module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDoma
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RderMemAutFormsCuspForms
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

namespace GlobalTheory.VBExt

section Algebra

variable {R A B C : Type} [CommRing R] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
  {ι κ : Type} [Fintype ι] [Fintype κ]

theorem bijective_sumElim (hfg : Function.Exact f g) (hf : Function.Injective f)
    (a : Module.Basis ι R A) (c : Module.Basis κ R C) (t : κ → B) (ht : ∀ k, g (t k) = c k) :
    Function.Bijective (Fintype.linearCombination R (Sum.elim (fun i => f (a i)) t)) := by
  have hg (x : ι ⊕ κ → R) : g (Fintype.linearCombination R (Sum.elim (fun i => f (a i)) t) x) =
      ∑ k, x (.inr k) • c k := by
    simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, hfg.apply_apply_eq_zero, ht]
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have h2 : ∀ k, x (.inr k) = 0 :=
      Fintype.linearIndependent_iff.1 c.linearIndependent _ (by rw [← hg, hx, map_zero])
    have h1 : ∀ i, x (.inl i) = 0 :=
      Fintype.linearIndependent_iff.1 a.linearIndependent _ (hf (by
        simpa [Fintype.linearCombination_apply, Fintype.sum_sum_type, h2] using hx))
    funext j
    rcases j with i | k
    exacts [h1 i, h2 k]
  · intro y
    obtain ⟨z, hz⟩ := (hfg (y - ∑ k, c.repr (g y) k • t k)).1 (by
      simp [ht])
    refine ⟨Sum.elim (a.repr z) (c.repr (g y)), ?_⟩
    have : ∑ i, a.repr z i • f (a i) = f z := by
      conv_rhs => rw [← a.sum_repr z]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, this, hz]

theorem det_sumElim [DecidableEq ι] [DecidableEq κ] (hfg : ∀ x, g (f x) = 0)
    (a : Module.Basis ι R A) (c : Module.Basis κ R C) (b : Module.Basis (ι ⊕ κ) R B)
    (hb : ∀ i, b (.inl i) = f (a i)) (hc : ∀ k, g (b (.inr k)) = c k) (a' : ι → A) (t' : κ → B) :
    b.det (Sum.elim (fun i => f (a' i)) t') = a.det a' * c.det fun k => g (t' k) := by
  have h1 (x : A) : ⇑(b.repr (f x)) = Sum.elim (a.repr x) 0 := by
    have : f x = ∑ j, Sum.elim (a.repr x) 0 j • b j := by
      conv_lhs => rw [← a.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Fintype.sum_sum_type, hb, map_sum, map_smul, Sum.elim_inl, Sum.elim_inr,
        Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
    rw [this, b.repr_sum_self]
  have h2 (y : B) (k : κ) : b.repr y (.inr k) = c.repr (g y) k := by
    have : g y = ∑ k, b.repr y (.inr k) • c k := by
      conv_lhs => rw [← b.sum_repr y]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Fintype.sum_sum_type, hb, hc, hfg, map_sum, map_smul, map_add (f := _), smul_zero,
        Finset.sum_const_zero, zero_add]
    rw [this, c.repr_sum_self]
  rw [Module.Basis.det_apply, Module.Basis.det_apply, Module.Basis.det_apply,
    ← Matrix.det_fromBlocks_zero₂₁ _ (Matrix.of fun i k => b.repr (t' k) (.inl i))]
  congr 1
  ext (i | i) (j | j) <;> simp [Module.Basis.toMatrix_apply, h1, h2, hfg]

end Algebra

variable {X : Scheme.{0}} {S : ShortComplex X.Modules} {U U' V : X.Opens} {r s : ℕ}

theorem isFrame_sumElim (hS : S.ShortExact) {ι κ : Type} [Fintype ι] [Fintype κ]
    {e : ι → Γ(S.X₁, U)} {t : κ → Γ(S.X₂, U)} (he : IsFrame e)
    (ht : IsFrame fun k => S.g.app U (t k)) :
    IsFrame (Sum.elim (fun i => S.f.app U (e i)) t) := fun V h => by
  have := hS.mono_f
  have key := bijective_sumElim (f := appLinear S.f V) (g := appLinear S.g V)
    (QCoh.exact_app_of_exact_of_mono hS.exact V) (QCoh.injective_app_of_mono S.f V)
    (he.basis h) (ht.basis h) (fun k => resM _ h (t k))
    (fun k => by rw [IsFrame.basis_apply, appLinear_apply, app_resM])
  convert key using 3
  funext j
  rcases j with i | k
  · simp only [Sum.elim_inl, IsFrame.basis_apply, appLinear_apply, app_resM]
  · rfl

theorem detUnit_sumElim (hS : S.ShortExact) {e : Fin r → Γ(S.X₁, U)} {t : Fin s → Γ(S.X₂, U)}
    (he : IsFrame e) (ht : IsFrame fun k => S.g.app U (t k)) {e' : Fin r → Γ(S.X₁, U')}
    {t' : Fin s → Γ(S.X₂, U')} (he' : IsFrame e') (ht' : IsFrame fun k => S.g.app U' (t' k))
    (h : V ≤ U) (h' : V ≤ U') :
    ((isFrame_sumElim hS he ht).comp_equiv finSumFinEquiv.symm).detUnit
      ((isFrame_sumElim hS he' ht').comp_equiv finSumFinEquiv.symm) h h' =
      he.detUnit he' h h' * ht.detUnit ht' h h' := by
  have := hS.mono_f
  refine Units.ext ?_
  have e₁ : ((isFrame_sumElim hS he ht).comp_equiv finSumFinEquiv.symm).basis h =
      ((isFrame_sumElim hS he ht).basis h).reindex finSumFinEquiv :=
    DFunLike.ext _ _ fun k => by simp
  have key := det_sumElim (f := appLinear S.f V) (g := appLinear S.g V)
    (QCoh.exact_app_of_exact_of_mono hS.exact V).apply_apply_eq_zero
    (he.basis h) (ht.basis h) ((isFrame_sumElim hS he ht).basis h)
    (fun i => by simp only [Sum.elim_inl, IsFrame.basis_apply, appLinear_apply, app_resM])
    (fun i => by simp only [Sum.elim_inr, IsFrame.basis_apply, appLinear_apply, app_resM])
    (fun i => resM _ h' (e' i)) (fun k => resM _ h' (t' k))
  simp only [appLinear_apply, app_resM] at key
  rw [Units.val_mul, IsFrame.val_detUnit, IsFrame.val_detUnit, IsFrame.val_detUnit, e₁,
    Module.Basis.det_reindex, ← key]
  congr 1
  funext j
  rcases j with i | k <;> simp

theorem exists_lifts {F G : X.Modules} (φ : F ⟶ G) [Epi φ] {κ : Type} [Fintype κ]
    (c : κ → Γ(G, U)) {x : X} (hx : x ∈ U) :
    ∃ (W : X.Opens) (h : W ≤ U), x ∈ W ∧ ∃ t : κ → Γ(F, W), ∀ k, φ.app W (t k) = resM G h (c k) := by
  choose W hW hxW t ht using fun k => exists_app_eq_of_epi φ (c k) hx
  have hV (k : κ) : U ⊓ Finset.univ.inf W ≤ W k :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ k))
  refine ⟨U ⊓ Finset.univ.inf W, inf_le_left, ⟨hx, by
    rw [Opens.coe_finset_inf]; simpa using hxW⟩, fun k => resM F (hV k) (t k), fun k => ?_⟩
  rw [app_resM, ht, resM_resM]


variable (S r s) in
structure AdaptedChart where

  U : X.Opens

  e : Fin r → Γ(S.X₁, U)

  t : Fin s → Γ(S.X₂, U)

  he : IsFrame e

  ht : IsFrame fun k => S.g.app U (t k)

theorem exists_adaptedChart (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (x : X) :
    ∃ c : AdaptedChart S r s, x ∈ c.U := by
  have := hS.epi_g
  obtain ⟨U, e, hx, he⟩ := h₁ x
  obtain ⟨U', c, -, hx', hle, hc⟩ := h₃.exists_affine hx
  obtain ⟨W, h, hxW, t, ht⟩ := exists_lifts S.g c hx'
  exact ⟨⟨W, _, t, he.res (h.trans hle), by rw [funext ht]; exact hc.res h⟩, hxW⟩

theorem isVB_and_cls_det_of_shortExact (X : Scheme.{0}) (S : ShortComplex X.Modules) (r s : ℕ)
    (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) :
    ∃ h₂ : IsVB S.X₂ (r + s),
      CechPic.cls _ h₂.isLB_det = CechPic.cls _ h₁.isLB_det + CechPic.cls _ h₃.isLB_det := by
  have hb (c : AdaptedChart S r s) := (isFrame_sumElim hS c.he c.ht).comp_equiv finSumFinEquiv.symm
  let L : LB X :=
    { ι := AdaptedChart S r s
      U := fun c => c.U
      g := fun c c' => (hb c).detUnit (hb c') inf_le_left inf_le_right }
  have hL : L.IsLB := by
    refine ⟨top_le_iff.1 fun x _ => ?_, fun c => ?_, fun c c' c'' => ?_⟩
    · exact Opens.mem_iSup.2 (exists_adaptedChart hS h₁ h₃ x)
    · exact (IsFrame.res_detUnit _ _ _ _ _).trans ((hb c).detUnit_self _ _)
    · exact (congrArg₂ (· * ·) (IsFrame.res_detUnit _ _ _ _ _)
        (IsFrame.res_detUnit _ _ _ _ _)).trans
        ((IsFrame.detUnit_mul _ _ _ _ _ _).trans (IsFrame.res_detUnit _ _ _ _ _).symm)
  obtain ⟨h₂, hi⟩ := lbIso_det_of_frames hL _ hb fun _ _ => rfl
  have hT := CechPic.isLB_tens h₁.isLB_det h₃.isLB_det
  have hj : LBIso L (CechPic.tens (det S.X₁ r) (det S.X₃ s)) := CechPic.iso_of_chart hT
    ⟨fun c => (⟨c.U, c.e, c.he⟩, ⟨c.U, _, c.ht⟩), fun _ _ h => ⟨h, h⟩, fun y c c' hc hc' =>
      ((congrArg _ (detUnit_sumElim hS c.he c.ht c'.he c'.ht _ _)).trans (map_mul _ _ _)).trans
        (CechPic.gm_tens (det S.X₁ r) (det S.X₃ s) (𝟙 X) y (⟨c.U, c.e, c.he⟩, ⟨c.U, _, c.ht⟩)
          (⟨c'.U, c'.e, c'.he⟩, ⟨c'.U, _, c'.ht⟩) ⟨hc, hc⟩ ⟨hc', hc'⟩).symm⟩
  exact ⟨h₂, ((CechPic.cls_eq_iff hL _).2 hi).symm.trans ((CechPic.cls_eq_iff hL hT).2 hj)⟩

end GlobalTheory.VBExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaHasInfExpOfIsEtaConj
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EtaConjType

open Formalism.L2.Host Formalism.L2.JoinChr

section General

variable {E : Type} [Field E] [NumberField E]

noncomputable def rt (P : HeightOneSpectrum (𝓞 E)) : ℝ := (Real.sqrt ((Ideal.absNorm P.asIdeal : ℕ) : ℝ))⁻¹

theorem rt_pos (P : HeightOneSpectrum (𝓞 E)) : 0 < rt P :=
  inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot))))

theorem rt_sq (P : HeightOneSpectrum (𝓞 E)) : rt P ^ 2 = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [rt, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem mk_eq (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) : FinitePlace.mk P (k : E) = (rt P ^ ordF P k) ^ 2 := by
  obtain ⟨u, hu, hk⟩ := GlobalTheory.EtaConjChar.exists_unit_part P k
  generalize ordF P k = n at hk ⊢
  rw [hk, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, GlobalTheory.EtaConjLocal.mk_unit P hu,
    GlobalTheory.EtaConjLocal.mk_unif, mul_one, ← rt_sq, sq, sq, mul_zpow]

theorem prod_rt [_root_.NumberField.IsTotallyComplex E] {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (k : Eˣ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ P, ordF P k ≠ 0 → P ∈ S) : (∏ i, ‖φ i k‖) * ∏ P ∈ S, rt P ^ ordF P k = 1 := by
  have h := prod_abs_eq_one k.ne_zero
  rw [← hφ.prod_comp, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm,
    finprod_eq_prod_of_mulSupport_subset (s := S)] at h
  · rw [← sq_eq_sq₀ (mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.prod_nonneg fun P _ => (zpow_pos (rt_pos P) _).le)) zero_le_one, one_pow, mul_pow, ← Finset.prod_pow,
      ← Finset.prod_pow, ← h]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => by rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
    · exact Finset.prod_congr rfl fun P _ => (mk_eq P k).symm
  · intro P hP
    refine hS P fun h0 => hP ?_
    exact (mk_eq P k).trans (by rw [h0]; simp)

theorem prod_val (χ : HChar E) (hu : ∀ P, χ.UnrAt P) (k : Eˣ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ P, ordF P k ≠ 0 → P ∈ S) :
    ((χ.inf k : ℂˣ) : ℂ) * ∏ P ∈ S, (((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ)) ^ ordF P k =
      ((∏ P ∈ S, rt P ^ ordF P k : ℝ) : ℂ) := by
  have h := GlobalTheory.HeckeProduct.productRule χ ∅ (fun v _ => hu v) k
  simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, not_false_eq_true, finprod_true] at h
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun P hP => hS P fun h0 => hP (by simp [h0]))] at h
  have h' := congrArg (Units.val : ℂˣ → ℂ) h
  simp only [Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_one] at h'
  simp only [mul_zpow, Finset.prod_mul_distrib]
  rw [← mul_assoc, h', one_mul]
  push_cast
  rfl

theorem unrAt_of_locK (χ : HChar E) (P : HeightOneSpectrum (𝓞 E))
    (h : ∀ u : Eˣ, P.valuation E (u : E) = 1 → χ.locK P u = 1) : χ.UnrAt P := by
  intro x
  have hc : IsClopen {x : (P.adicCompletion E)ˣ | IsUnitAt P x} := by
    have := (Valued.isClopen_sphere (P.adicCompletion E) (r := 1) one_ne_zero).preimage
      (Units.continuous_val (M := P.adicCompletion E))
    convert this using 1
    ext x
    simp [IsUnitAt]
  refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin P).induction_on (p := fun x => IsUnitAt P x → χ.loc P x = 1) x ?_
    fun k hk => h k ((P.valuedAdicCompletion_eq_valuation' _).symm.trans hk)
  exact isClosed_imp hc.2 (isClosed_eq (χ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele P)) continuous_const)

variable {L : Type} [Field L] (ι σ : L →+* ℂ) {χ χ' : HChar E} (hu : ∀ P, χ.UnrAt P) (hu' : ∀ P, χ'.UnrAt P)
  (y : HeightOneSpectrum (𝓞 E) → L) (hy : ∀ P, ι (y P) = ((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ))
  (hy' : ∀ P, σ (y P) = ((χ'.val P : ℂˣ) : ℂ) * (rt P : ℂ))

include hu hu' hy hy'

theorem inf_eq [_root_.NumberField.IsTotallyComplex E] {I : Type} [Fintype I] (φ : I → E →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (hi : χ.HasInf φ fun _ => 1)
    (ht : ∀ k : E, ∃ t : L, ι t = ∏ i, φ i k ∧ σ t = ∏ i, φ i k) (k : Eˣ) : χ'.inf k = χ.inf k := by
  obtain ⟨t, ht1, ht2⟩ := ht k
  let S := (GlobalTheory.HeckeProduct.finite_ordF k).toFinset
  have hS : ∀ P, ordF P k ≠ 0 → P ∈ S := fun P hP => (Set.Finite.mem_toFinset _).2 hP
  have h1 := prod_val χ hu k S hS
  have h2 := prod_val χ' hu' k S hS
  have h3 := congrArg (fun r : ℝ => (r : ℂ)) (prod_rt φ hφ k S hS)
  have h4 : ((χ.inf k : ℂˣ) : ℂ) * ((∏ i, ‖φ i k‖ : ℝ) : ℂ) = ∏ i, φ i k := by
    rw [hi k, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [zpow_one, div_mul_cancel₀ _ (by simp)]
  simp only [← hy, ← hy', ← map_zpow₀, ← map_prod] at h1 h2
  simp only [Complex.ofReal_mul, Complex.ofReal_one] at h3
  generalize ∏ P ∈ S, y P ^ ordF P k = Y at h1 h2
  generalize ((∏ P ∈ S, rt P ^ ordF P k : ℝ) : ℂ) = r at h1 h2 h3
  generalize ((∏ i, ‖φ i k‖ : ℝ) : ℂ) = s at h3 h4
  have h5 : Y * t = 1 := ι.injective (by
    rw [map_mul, map_one, ht1, ← h4, ← h3, ← h1]
    ring)
  have h6 : σ Y * (∏ i, φ i k) = 1 := by rw [← ht2, ← map_mul, h5, map_one]
  refine Units.ext ?_
  calc ((χ'.inf k : ℂˣ) : ℂ) = (χ'.inf k : ℂˣ) * (σ Y * (((χ.inf k : ℂˣ) : ℂ) * s)) := by rw [h4, h6, mul_one]
    _ = (χ.inf k : ℂˣ) * (s * (((χ'.inf k : ℂˣ) : ℂ) * σ Y)) := by ring
    _ = _ := by rw [h2, h3, mul_one]

theorem resFin_eq {F : Type} [Field F] [NumberField F] [Algebra F E] (h2 : Module.finrank F E = 2)
    (hF : ∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal) (hr : χ.ResEta F)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ'.resFin v k = χ.resFin v k := by
  have key : ∀ (ψ : HChar E), (∀ P, ψ.UnrAt P) →
      ∏ P ∈ aboveF (L := E) F v, (((ψ.val P : ℂˣ) : ℂ) * (rt P : ℂ)) ^ ordF v k =
        ((ψ.resFin v k : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ ^ ordF v k := by
    intro ψ hψ
    have h1 : ∏ P ∈ aboveF (L := E) F v, rt P = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
      rw [← sq_eq_sq₀ (Finset.prod_nonneg fun P _ => (rt_pos P).le) (by positivity), ← Finset.prod_pow]
      simp only [rt_sq]
      rw [Finset.prod_inv_distrib, ← Nat.cast_prod, GlobalTheory.ToricDistribution.prod_absNorm hF, h2, Nat.cast_pow, inv_pow]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    congr 1
    · rw [HChar.resFin_apply, Units.coe_prod]
      refine Finset.prod_congr rfl fun P hP => ?_
      rw [GlobalTheory.HeckeProduct.locK_unr ψ (hψ P), GlobalTheory.ToricDistribution.ordF_up hF, GlobalTheory.ToricDistribution.mem_aboveF.1 hP,
        Units.val_zpow_eq_zpow_val]
    · rw [Finset.prod_zpow, ← Complex.ofReal_prod, h1]
      simp
  have h1 := key χ hu
  have h3 := key χ' hu'
  simp only [← hy, ← hy', ← map_zpow₀, ← map_prod] at h1 h3
  obtain ⟨z, hz⟩ : ∃ z : L, ∀ f : L →+* ℂ, f z = ((χ.resFin v k : ℂˣ) : ℂ) := by
    rw [hr.1, etaFin]
    split_ifs
    · exact ⟨(-1) ^ ordF v k, fun f => by simp⟩
    · exact ⟨1, fun f => by simp⟩
  have h4 : ∏ P ∈ aboveF (L := E) F v, y P ^ ordF v k = z * ((Ideal.absNorm v.asIdeal : ℕ) : L)⁻¹ ^ ordF v k :=
    ι.injective (by rw [h1, map_mul, hz, map_zpow₀, map_inv₀, map_natCast])
  rw [h4, map_mul, hz, map_zpow₀, map_inv₀, map_natCast] at h3
  refine Units.ext (mul_right_cancel₀ (zpow_ne_zero _ (inv_ne_zero ?_)) h3.symm)
  exact Nat.cast_ne_zero.2 (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)

end General

theorem isEtaT_of_conj {D : D7} {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) {η η' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E}
    (hc : ChrEq η χ) (hc' : ChrEq η' χ') (hχ : IsEtaT D.host χ) (hη : IsEtaConj σ η η') : IsEtaT D.host χ' := by
  have hu' : ∀ P, χ'.UnrAt P := fun P => unrAt_of_locK χ' P (GlobalTheory.EtaConjChar.locK_eq_one hc' hη.2.1 P)
  have hy : ∀ P, ∃ y : D.what₂.LL, D.what₂.embLL y = ((χ.val P : ℂˣ) : ℂ) * (rt P : ℂ) ∧
      σ y = ((χ'.val P : ℂˣ) : ℂ) * (rt P : ℂ) := by
    intro P
    obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
    obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
    obtain ⟨y, hy1, hy2⟩ := hη.2.2 P e he (locU he.1 (unif P)) rfl
    rw [hc.2 P e he _ (locU he.1 (unif P)) rfl] at hy1
    rw [hc'.2 P e he _ (locU he.1 (unif P)) rfl] at hy2
    refine ⟨y, ?_, ?_⟩
    · simpa only [HChar.val, rt, Ideal.absNorm_eq_natCard] using hy1
    · simpa only [HChar.val, rt, Ideal.absNorm_eq_natCard] using hy2
  choose y hy hy' using hy
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  haveI := hcm.cplx
  obtain ⟨hb, hl⟩ := (labels_overK σ).1 hσ
  have hinf : ∀ k, (χ' * χ⁻¹).inf k = 1 := fun k => by
    rw [HChar.inf_mul, HChar.inf_inv, mul_inv_eq_one]
    refine inf_eq D.what₂.embLL σ hχ.unr hu' y hy hy' (embPsi D.host) hcm.bij hχ.inf (fun a => ?_) k
    refine ⟨∏ τ, labLL D τ a, ?_, ?_⟩
    · rw [map_prod, ← D.eTau.prod_comp]
      exact Finset.prod_congr rfl fun τ _ => embLL_embE D _
    · rw [map_prod, ← D.eTau.prod_comp, ← hb.prod_comp]
      exact Finset.prod_congr rfl fun ρ _ => RingHom.congr_fun (hl ρ) a
  obtain ⟨n, hn, ho⟩ := GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one _ _ hinf
  have hp : ∀ x, (χ' * χ⁻¹).1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar D.host.E => ξ.1 x) ho
  have hξ : IsClsF D.host (χ' * χ⁻¹) := by
    refine ⟨HChar.isUnitary_of_order hn ho, fun P => (hu' P).mul (hχ.unr P).inv, hinf, fun v k => ?_, fun w k => ?_⟩
    · rw [HChar.resFin_mul, HChar.resFin_inv, mul_inv_eq_one]
      exact resFin_eq D.what₂.embLL σ hχ.unr hu' y hy hy' hcm.rank
        (GlobalTheory.BaseChangeExistsCompare.unram_of_cm D D.sp.cm) hχ.res v k
    · rw [HChar.resInf_apply]
      exact Finset.prod_eq_one fun w' _ => GlobalTheory.ToricDistribution.locInf_of_pow hn.ne' hp w' _
  have := hχ.mul_cls hξ
  rwa [mul_comm χ', mul_inv_cancel_left] at this

end GlobalTheory.EtaConjType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientMeasureProductGroups
open MeasureTheory

namespace GlobalTheory.Cusp.SemidirectConst

theorem map_restrict_isMulRightInvariant : ∀ (N N₁ : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
    [Group N₁] [TopologicalSpace N₁] [IsTopologicalGroup N₁] [MeasurableSpace N₁] [BorelSpace N₁]
    (Δ : Subgroup N) [Countable Δ] (μ : Measure N) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (D : Set N),
    IsFundamentalDomain Δ D μ → ∀ (s : N₁ →* N) (π : N →* N₁), Continuous π → (∀ u, π (s u) = u) →
    (∀ δ ∈ Δ, π δ = 1) → ((μ.restrict D).map π).IsMulRightInvariant := by
  intro N N₁ _ _ _ _ _ _ _ _ _ _ Δ _ μ _ _ D hD s π hπ hπs hπΔ
  refine ⟨fun u₀ => ?_⟩
  ext B hB
  have hP : MeasurableSet (π ⁻¹' B) := hπ.measurable hB
  rw [Measure.map_apply (measurable_mul_const u₀) hB, Measure.map_apply hπ.measurable hB,
    Measure.map_apply hπ.measurable (measurable_mul_const u₀ hB), Measure.restrict_apply hP,
    Measure.restrict_apply (hπ.measurable (measurable_mul_const u₀ hB))]
  have e1 : π ⁻¹' ((· * u₀) ⁻¹' B) ∩ D = (· * s u₀) ⁻¹' (π ⁻¹' B ∩ (· * (s u₀)⁻¹) ⁻¹' D) := by
    ext v; simp [map_mul, hπs]
  have hD' : IsFundamentalDomain Δ ((· * (s u₀)⁻¹) ⁻¹' D) μ :=
    hD.preimage_of_equiv (measurePreserving_mul_right μ (s u₀)⁻¹).quasiMeasurePreserving Function.bijective_id
      fun γ x => mul_assoc _ _ _
  rw [e1, measure_preimage_mul_right]
  exact hD'.measure_set_eq hD hP fun δ => by
    ext v; simp [Subgroup.smul_def, map_mul, hπΔ δ δ.2]


open scoped Pointwise in
theorem map_restrict_isFiniteMeasureOnCompacts : ∀ (N N₁ : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [MeasurableSpace N] [BorelSpace N]
    [Group N₁] [TopologicalSpace N₁] [IsTopologicalGroup N₁] [T2Space N₁] [MeasurableSpace N₁] [BorelSpace N₁]
    (Δ : Subgroup N) [Countable Δ] (μ : Measure N) [μ.IsHaarMeasure] (D : Set N),
    IsFundamentalDomain Δ D μ → ∀ (s : N₁ →* N) (π : N →* N₁), Continuous s → Continuous π → (∀ u, π (s u) = u) →
    (∃ K : Set N, IsCompact K ∧ ∀ v, π v = 1 → ∃ δ ∈ Δ, δ * v ∈ K) →
    IsFiniteMeasureOnCompacts ((μ.restrict D).map π) := by
  intro N N₁ _ _ _ _ _ _ _ _ _ _ _ Δ _ μ _ D hD s π hs hπ hπs hK
  obtain ⟨K, hK, hKs⟩ := hK
  refine ⟨fun C hC => ?_⟩
  have hm : MeasurableSet (π ⁻¹' C) := hπ.measurable hC.measurableSet
  rw [Measure.map_apply hπ.measurable hC.measurableSet, Measure.restrict_apply hm]
  have hL : IsCompact ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) := (hK.prod hC).image (by fun_prop)
  have hsub : π ⁻¹' C ∩ D ⊆ ⋃ g : Δ, (g • ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) ∩ D) := by
    rintro v ⟨hv, hvD⟩
    obtain ⟨δ, hδ, hδK⟩ := hKs (v * (s (π v))⁻¹) (by rw [map_mul, map_inv, hπs, mul_inv_cancel])
    refine Set.mem_iUnion.2 ⟨⟨δ, hδ⟩⁻¹, Set.mem_smul_set.2 ⟨δ * v, ⟨(δ * (v * (s (π v))⁻¹), π v), ⟨hδK, hv⟩, ?_⟩, ?_⟩, hvD⟩
    · simp [mul_assoc]
    · simp [Subgroup.smul_def]
  calc μ (π ⁻¹' C ∩ D) ≤ μ (⋃ g : Δ, (g • ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) ∩ D)) := measure_mono hsub
    _ ≤ ∑' g : Δ, μ (g • ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) ∩ D) := measure_iUnion_le _
    _ = μ ((fun p : N × N₁ => p.1 * s p.2) '' (K ×ˢ C)) := (hD.measure_eq_tsum _).symm
    _ < ⊤ := hL.measure_lt_top

theorem existsUnique_inter_preimage : ∀ (G G₁ : Type) [Group G] [Group G₁] (Γ N N' : Subgroup G) (Γ₁ N₁ : Subgroup G₁) (s : N₁ →* N) (π : N →* N₁),
    (∀ u, π (s u) = u) → (∀ v, π v = 1 ↔ (v : G) ∈ N') →
    (∀ u : N₁, (u : G₁) ∈ Γ₁ → (s u : G) ∈ Γ) → (∀ v : N, (v : G) ∈ Γ → (π v : G₁) ∈ Γ₁) →
    ∀ (A : Set N) (B : Set N₁), (∀ v : N, ∃! δ : (Γ ⊓ N').subgroupOf N, (δ : N) * v ∈ A) →
    (∀ u : N₁, ∃! γ : Γ₁.subgroupOf N₁, (γ : N₁) * u ∈ B) →
    ∀ v : N, ∃! γ : Γ.subgroupOf N, (γ : N) * v ∈ A ∩ π ⁻¹' B := by
  intro G G₁ _ _ Γ N N' Γ₁ N₁ s π hπs hker hsΓ hπΓ A B hA hB v
  obtain ⟨γ₁, hγ₁, hγ₁u⟩ := hB (π v)
  obtain ⟨δ, hδ, hδu⟩ := hA (s γ₁ * v)
  have hδΓ : ((δ : N) : G) ∈ Γ := (Subgroup.mem_subgroupOf.1 δ.2).1
  have hδ1 : π δ = 1 := (hker _).2 (Subgroup.mem_subgroupOf.1 δ.2).2
  have hsγ : ((s γ₁ : N) : G) ∈ Γ := hsΓ _ (Subgroup.mem_subgroupOf.1 γ₁.2)
  refine ⟨⟨δ * s γ₁, Subgroup.mem_subgroupOf.2 (by simpa using mul_mem hδΓ hsγ)⟩, ⟨?_, ?_⟩, fun γ hγ => ?_⟩
  · simpa [mul_assoc] using hδ
  · change π (δ * s γ₁ * v) ∈ B
    rwa [map_mul, map_mul, hδ1, hπs, one_mul]
  · have hγΓ : (((γ : N)) : G) ∈ Γ := Subgroup.mem_subgroupOf.1 γ.2
    have hπγ : (⟨π γ, Subgroup.mem_subgroupOf.2 (hπΓ _ hγΓ)⟩ : Γ₁.subgroupOf N₁) = γ₁ :=
      hγ₁u _ (by simpa [map_mul] using hγ.2)
    have hπγ' : π γ = γ₁ := congrArg Subtype.val hπγ
    have hmem : (γ : N) * (s γ₁)⁻¹ ∈ (Γ ⊓ N').subgroupOf N := Subgroup.mem_subgroupOf.2
      ⟨by simpa using mul_mem hγΓ (inv_mem hsγ), (hker _).1 (by rw [map_mul, map_inv, hπs, hπγ', mul_inv_cancel])⟩
    have e : (⟨_, hmem⟩ : (Γ ⊓ N').subgroupOf N) = δ := hδu _ (by simpa [mul_assoc] using hγ.1)
    refine Subtype.ext ?_
    change (γ : N) = δ * s γ₁
    rw [← e]; simp

end GlobalTheory.Cusp.SemidirectConst

open GlobalTheory.Cusp.SemidirectConst


open GlobalTheory.AutomorphicL2Unitary in
theorem GlobalTheory.Cusp.constTermOn_eq_integral_semidirect : ∀ (G G₁ : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (Γ N N' : Subgroup G) (Γ₁ N₁ : Subgroup G₁) [DiscreteTopology Γ] [DiscreteTopology Γ₁] [LocallyCompactSpace N] [LocallyCompactSpace N₁],
    N' ≤ N → GlobalTheory.Cusp.Cocompact Γ N → GlobalTheory.Cusp.Cocompact Γ N' → GlobalTheory.Cusp.Cocompact Γ₁ N₁ →
    ∀ (s : N₁ →* N) (π : N →* N₁), Continuous s → Continuous π → (∀ u, π (s u) = u) → (∀ v, π v = 1 ↔ (v : G) ∈ N') →
    (∀ u : N₁, (u : G₁) ∈ Γ₁ → (s u : G) ∈ Γ) → (∀ v : N, (v : G) ∈ Γ → (π v : G₁) ∈ Γ₁) →
    ∀ ψ : G → ℂ, Continuous ψ → (∀ a ∈ N', ∀ y, ψ (a * y) = ψ y) → (∀ γ ∈ Γ, γ ∈ N → ∀ y, ψ (γ * y) = ψ y) →
    ∀ (μ₁ : Measure N₁) (𝓕₁ : Set N₁), μ₁.IsHaarMeasure → IsFundamentalDomain (Γ₁.subgroupOf N₁) 𝓕₁ μ₁ → μ₁ 𝓕₁ = 1 →
    ∀ x : G, GlobalTheory.Cusp.constTermOn Γ N ψ x = ∫ u in 𝓕₁, ψ ((s u : G) * x) ∂μ₁ := by
  intro G G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Γ N N' Γ₁ N₁ _ _ _ _ hle hc hc' hc₁ s π hs hπ hπs hker hsΓ hπΓ ψ hψc hψN' hψΓ
    μ₁ 𝓕₁ hμ₁ h𝓕₁ h1 x
  haveI := hμ₁
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : DiscreteTopology (Γ ⊓ N' : Subgroup G) :=
    .of_continuous_injective (f := Subgroup.inclusion (inf_le_left : Γ ⊓ N' ≤ Γ))
      (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective _)
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Subgroup N, Δ = (Γ ⊓ N').subgroupOf N := ⟨_, rfl⟩
  subst hΔ
  have : Countable ((Γ ⊓ N').subgroupOf N) := Function.Injective.countable
    (f := fun δ : (Γ ⊓ N').subgroupOf N => (⟨δ.1.1, (Subgroup.mem_subgroupOf.1 δ.2).1⟩ : Γ))
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => z.1) h))
  let μ : Measure N := Measure.haar
  have := hc.isMulRightInvariant μ
  have := hc₁.isMulRightInvariant μ₁
  have hD' := isFundamentalDomain_stdDom ((Γ ⊓ N').subgroupOf N) μ
  have hπΔ : ∀ δ ∈ (Γ ⊓ N').subgroupOf N, π δ = 1 := fun δ hδ => (hker δ).2 (Subgroup.mem_subgroupOf.1 hδ).2
  obtain ⟨ν, hν⟩ : ∃ ν, ν = (μ.restrict (stdDom ((Γ ⊓ N').subgroupOf N))).map π := ⟨_, rfl⟩
  have : ν.IsMulRightInvariant := hν ▸ map_restrict_isMulRightInvariant N N₁ _ μ _ hD' s π hπ hπs hπΔ
  have : IsFiniteMeasureOnCompacts ν := hν ▸ map_restrict_isFiniteMeasureOnCompacts N N₁ _ μ _ hD' s π hs hπ hπs (by
    obtain ⟨K, hK, hKs⟩ := hc'
    refine ⟨Subgroup.inclusion hle '' K, hK.image (continuous_subtype_val.subtype_mk _), fun v hv => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hKs ⟨v, (hker v).1 hv⟩
    refine ⟨Subgroup.inclusion hle γ, Subgroup.mem_subgroupOf.2 ⟨Subgroup.mem_subgroupOf.1 hγ, γ.2⟩, ⟨_, hγK, ?_⟩⟩
    exact Subtype.ext (by simp))
  obtain ⟨c, hνc⟩ : ∃ c : NNReal, ν = c • μ₁ := by
    obtain ⟨a, e1⟩ : ∃ a : NNReal, ν.inv = a • μ₁ := ⟨_, Measure.isMulLeftInvariant_eq_smul ν.inv μ₁⟩
    obtain ⟨b, e2⟩ : ∃ b : NNReal, μ₁.inv = b • μ₁ := ⟨_, Measure.isMulLeftInvariant_eq_smul μ₁.inv μ₁⟩
    refine ⟨a * b, ?_⟩
    rw [← Measure.inv_inv ν, e1, Measure.inv_def, Measure.map_smul, ← Measure.inv_def, e2, smul_smul]
    exact measurable_inv.aemeasurable
  have hD₁ := isFundamentalDomain_stdDom (Γ₁.subgroupOf N₁) μ₁
  have hmD₁ := measurableSet_stdDom (Γ₁.subgroupOf N₁)
  have hm𝓕 : MeasurableSet (stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁)) :=
    (measurableSet_stdDom _).inter (hπ.measurable hmD₁)
  have h𝓕 : IsFundamentalDomain (Γ.subgroupOf N) (stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁)) μ :=
    .mk' hm𝓕.nullMeasurableSet (existsUnique_inter_preimage G G₁ Γ N N' Γ₁ N₁ s π hπs hker hsΓ hπΓ _ _ (existsUnique_stdDom _) (existsUnique_stdDom _))
  have hg : ∀ v : N, ψ (v * x) = ψ (s (π v) * x) := fun v => by
    have hm : ((v * (s (π v))⁻¹ : N) : G) ∈ N' := (hker _).1 (by rw [map_mul, map_inv, hπs, mul_inv_cancel])
    have := hψN' _ hm ((s (π v) : G) * x)
    rw [← this, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left]
  have hgc : Continuous fun u : N₁ => ψ (s u * x) := by fun_prop
  have hint : ∫ v in stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁), ψ (v * x) ∂μ =
      ∫ u in stdDom (Γ₁.subgroupOf N₁), ψ (s u * x) ∂ν := by
    rw [hν, setIntegral_map hmD₁ hgc.aestronglyMeasurable hπ.aemeasurable, Measure.restrict_restrict (hπ.measurable hmD₁),
      Set.inter_comm (π ⁻¹' _)]
    exact integral_congr_ae (.of_forall hg)
  have hmeas : μ (stdDom ((Γ ⊓ N').subgroupOf N) ∩ π ⁻¹' stdDom (Γ₁.subgroupOf N₁)) = ν (stdDom (Γ₁.subgroupOf N₁)) := by
    rw [hν, Measure.map_apply hπ.measurable hmD₁, Measure.restrict_apply (hπ.measurable hmD₁), Set.inter_comm]
  have hinv1 : ∀ (γ : Γ₁.subgroupOf N₁) (u : N₁), ψ (s (γ • u) * x) = ψ (s u * x) := fun γ u => by
    rw [Subgroup.smul_def, smul_eq_mul, map_mul]
    simp only [Subgroup.coe_mul, mul_assoc]
    exact hψΓ _ (hsΓ _ (Subgroup.mem_subgroupOf.1 γ.2)) (s γ).2 _
  have hDe : μ₁ (stdDom (Γ₁.subgroupOf N₁)) = 1 := (hD₁.measure_eq h𝓕₁).trans h1
  rw [GlobalTheory.Cusp.Stages.constTermOn_eq' h𝓕 (fun γ hγ n => by
      simp only [Subgroup.coe_mul, mul_assoc]
      exact hψΓ _ (Subgroup.mem_subgroupOf.1 hγ) γ.2 _),
    hint, measureReal_def, hmeas, hνc, Measure.smul_apply, hDe, Measure.restrict_smul, integral_smul_nnreal_measure,
    hD₁.setIntegral_eq h𝓕₁ hinv1]
  have hc0 : c ≠ 0 := by
    have := h𝓕.measure_ne_zero (NeZero.ne μ)
    rw [hmeas, hνc, Measure.smul_apply, hDe] at this
    rintro rfl; simp at this
  first
  | (rw [ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_toReal, NNReal.smul_def, smul_smul,
      inv_mul_cancel₀ (NNReal.coe_ne_zero.2 hc0), one_smul]; done)
  | (simp [hc0, NNReal.smul_def, smul_smul]; done)
  | (field_simp; done)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SemilinTransport

open MvPolynomial

theorem map_mem {R : Type} [CommRing R] (σ : R →+* R) {r n : ℕ} {ν : Fin n → ℕ}
    {f : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν) :
    map σ f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_weightedHomogeneousSubmodule] at h1 ⊢
    intro d hd
    apply h1
    intro h0
    apply hd
    rw [coeff_map, h0, map_zero]
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at h2 ⊢
    intro l j hlj
    have e := h2 l j hlj
    simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero] at e ⊢
    have hc : ∀ g : MvPolynomial (Fin r × Fin n) R,
        map σ (Formalism.GradedWeylDivisibility.colAddGen R l j g) = Formalism.GradedWeylDivisibility.colAddGen R l j (map σ g) := by
      intro g
      unfold Formalism.GradedWeylDivisibility.colAddGen
      rw [aeval_eq_bind₁, map_bind₁]
      congr 2
      funext v
      split_ifs <;> simp
    rw [← hc, e, map_rename]

def onFactor {R : Type} [CommRing R] (σ : R →+* R) (r n : ℕ) (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.dualWeyl R r n ν →+ Formalism.GradedWeylDivisibility.dualWeyl R r n ν where
  toFun f := ⟨map σ (f : MvPolynomial (Fin r × Fin n) R), map_mem σ f.2⟩
  map_zero' := by ext1; simp
  map_add' f f' := by ext1; simp

theorem onFactor_smul {R : Type} [CommRing R] (σ : R →+* R) (r n : ℕ) (ν : Fin n → ℕ) (c : R)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R r n ν) : onFactor σ r n ν (c • f) = σ c • onFactor σ r n ν f := by
  ext1
  simp [onFactor, smul_eq_C_mul]

def Tw {R : Type} [CommRing R] (_σ : R →+* R) (M : Type) : Type := M

instance {R : Type} [CommRing R] (σ : R →+* R) (M : Type) [AddCommGroup M] : AddCommGroup (Tw σ M) :=
  inferInstanceAs (AddCommGroup M)

instance {R : Type} [CommRing R] (σ : R →+* R) (M : Type) [AddCommGroup M] [Module R M] :
    Module R (Tw σ M) :=
  Module.compHom M σ

variable {R : Type} [CommRing R] {ι : Type} (N : ℕ) (mu : ι → ℕ → ℕ)

def mlin (σ : R →+* R) :
    MultilinearMap (RingHom.id R) (fun τ : ι => Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ)))
      (Tw σ (NablaT R N mu)) where
  toFun x := (PiTensorProduct.tprod R (fun τ => onFactor σ N N _ (x τ)) : NablaT R N mu)
  map_update_add' := by
    intro _ x i a b
    have e : ∀ v, (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ)) (Function.update x i v τ)) =
        Function.update (fun τ => onFactor σ N N _ (x τ)) i (onFactor σ N N _ v) := fun v =>
      funext fun τ => Function.apply_update (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) x i v τ
    simp only [e, map_add (f := _)]
    exact (PiTensorProduct.tprod R).map_update_add _ i _ _
  map_update_smul' := by
    intro _ x i c a
    have e : ∀ v, (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ)) (Function.update x i v τ)) =
        Function.update (fun τ => onFactor σ N N _ (x τ)) i (onFactor σ N N _ v) := fun v =>
      funext fun τ => Function.apply_update (fun τ => onFactor σ N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) x i v τ
    simp only [e, onFactor_smul]
    exact (PiTensorProduct.tprod R).map_update_smul _ i _ _

def semi (σ : R →+* R) : NablaT R N mu →+ NablaT R N mu :=
  (PiTensorProduct.lift (mlin N mu σ)).toAddMonoidHom

theorem semi_tprod (σ : R →+* R) (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) :
    semi N mu σ (PiTensorProduct.tprod R x) = PiTensorProduct.tprod R (fun τ => onFactor σ N N _ (x τ)) :=
  by
    show (PiTensorProduct.lift (mlin N mu σ)) (PiTensorProduct.tprod R x) = _
    rw [PiTensorProduct.lift.tprod]; rfl

theorem semi_smul (σ : R →+* R) (c : R) (y : NablaT R N mu) :
    semi N mu σ (c • y) = σ c • semi N mu σ y :=
  (PiTensorProduct.lift (mlin N mu σ)).map_smul c y

end GlobalTheory.SemilinTransport

namespace GlobalTheory.SemilinTransport

open MvPolynomial

variable {R : Type} [CommRing R] {ι : Type} (N : ℕ) (mu : ι → ℕ → ℕ)

theorem semi_left_inv (g : R ≃+* R) (y : NablaT R N mu) :
    semi N mu (g.symm : R →+* R) (semi N mu (g : R →+* R) y) = y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [semi_smul, semi_smul, semi_tprod, semi_tprod]
    congr 1
    · simp
    · congr 1
      funext τ
      ext1
      simp [onFactor, map_map, MvPolynomial.map_id]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem fix_inv (g : R ≃+* R) (u : GL (Fin N) R)
    (hu : ∀ a b, g ((u : Matrix (Fin N) (Fin N) R) a b) = (u : Matrix (Fin N) (Fin N) R) a b) (a b : Fin N) :
    g (((u⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) a b) = ((u⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) a b := by
  have hU : Units.map ((g : R →+* R).mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R).toMonoidHom u = u :=
    Units.ext (by ext i j; simp [hu])
  have h2 : Units.map ((g : R →+* R).mapMatrix : Matrix (Fin N) (Fin N) R →+* Matrix (Fin N) (Fin N) R).toMonoidHom u⁻¹ = u⁻¹ := by
    rw [map_inv, hU]
  have := congrArg (fun w : GL (Fin N) R => (w : Matrix (Fin N) (Fin N) R) a b) h2
  simpa using this

theorem onFactor_rep (g : R ≃+* R) (u : GL (Fin N) R)
    (hu : ∀ a b, g ((u : Matrix (Fin N) (Fin N) R) a b) = (u : Matrix (Fin N) (Fin N) R) a b) (ν : Fin N → ℕ)
    (f : Formalism.GradedWeylDivisibility.dualWeyl R N N ν) :
    onFactor (g : R →+* R) N N ν (Formalism.UG.dualWeylRep R N N ν u f) =
      Formalism.UG.dualWeylRep R N N ν u (onFactor (g : R →+* R) N N ν f) := by
  ext1
  simp only [onFactor, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Formalism.UG.dualWeylRep_apply]
  unfold Formalism.UG.dwAct Formalism.GradedWeylDivisibility.rowAct
  rw [aeval_eq_bind₁, map_bind₁]
  congr 2
  simp only [map_sum, map_mul, map_C, map_X, RingHom.coe_coe, fix_inv N g u hu]

theorem grp_tprod [DecidableEq ι] (h : ι → GL (Fin N) R)
    (x : ∀ τ, Formalism.GradedWeylDivisibility.dualWeyl R N N (Formalism.CohomologicalDescent.LD.res N (mu τ))) :
    grp R N mu h (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun τ => Formalism.UG.dualWeylRep R N N _ (h τ) (x τ)) := by
  simp [grp, Formalism.CohomologicalDescent.RealLocalDeltaNabla.nablaRep, PiTensorProduct.mapMonoidHom, PiTensorProduct.map_tprod]

theorem semi_grp [DecidableEq ι] (g : R ≃+* R) (h : ι → GL (Fin N) R)
    (hh : ∀ τ a b, g ((h τ : Matrix (Fin N) (Fin N) R) a b) = (h τ : Matrix (Fin N) (Fin N) R) a b)
    (y : NablaT R N mu) :
    semi N mu (g : R →+* R) (grp R N mu h y) = grp R N mu h (semi N mu (g : R →+* R) y) := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    rw [map_smul, semi_smul, semi_smul, map_smul, grp_tprod, semi_tprod, semi_tprod, grp_tprod]
    congr 2
    funext τ
    exact onFactor_rep N g (h τ) (hh τ) _ (x τ)
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]

end GlobalTheory.SemilinTransport

namespace GlobalTheory

open GlobalTheory.SemilinTransport

theorem semilinear_transport : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (mu : ι → ℕ → ℕ)
    (g : R ≃+* R), ∃ Φ : NablaT R N mu →+ NablaT R N mu, Function.Injective Φ ∧ (∀ (c : R) x, Φ (c • x) = g c • Φ x) ∧
    ∀ (h : ι → GL (Fin N) R), (∀ τ a b, g ((h τ : Matrix (Fin N) (Fin N) R) a b) = (h τ : Matrix (Fin N) (Fin N) R) a b) →
      ∀ x, Φ (grp R N mu h x) = grp R N mu h (Φ x) := by
  intro R _ ι _ _ N mu g
  refine ⟨semi N mu (g : R →+* R), fun y y' e => ?_, fun c x => semi_smul N mu _ c x,
    fun h hh x => semi_grp N mu g h hh x⟩
  rw [← semi_left_inv N mu g y, ← semi_left_inv N mu g y', e]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensorStatement
open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semilinear_action_dualWeylTensor : ∀ (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (mu : ι → ℕ → ℕ) (g : R ≃+* R), ∃ Φ : NablaT R N mu →+ NablaT R N mu, Function.Injective Φ ∧ (∀ (c : R) x, Φ (c • x) = g c • Φ x) ∧ ∀ (h : ι → GL (Fin N) R), (∀ τ a b, g ((h τ : Matrix (Fin N) (Fin N) R) a b) = (h τ : Matrix (Fin N) (Fin N) R) a b) → ∀ x, Φ (grp R N mu h x) = grp R N mu h (Φ x) := by
  first | exact @GlobalTheory.semilinear_transport | exact GlobalTheory.semilinear_transport | (intros; apply GlobalTheory.semilinear_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsJacMapZero
noncomputable section

open Matrix GlobalTheory.SplitWeil GlobalTheory.KSplit

namespace GlobalTheory.JacLine

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def blk3 (a b : ℕ) : Fin 1 ⊕ Fin (a + b) ⊕ Fin 1 ≃ Fin (a + (b + 2)) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 1)) finSumFinEquiv).trans finSumFinEquiv).trans (finCongr (by omega))

def IsJacMap (a b : ℕ) (α β : kˣ →* ℂˣ) (χ₁ χ₂ : kˣ → ℂ) (φ : indSp a (b + 2) α β →ₗ[ℂ] indSp a b α β) : Prop :=
  (∀ (u : GL (Fin (a + (b + 2))) k) (X : Matrix (Fin 1) (Fin (a + b) ⊕ Fin 1) k) (Y : Matrix (Fin (a + b)) (Fin 1) k),
      u.val.submatrix (blk3 a b) (blk3 a b) = fromBlocks 1 X 0 (fromBlocks 1 Y 0 1) →
      ∀ f f₁ : indSp a (b + 2) α β, (∀ h, (f₁ : GL (Fin (a + (b + 2))) k → ℂ) h = (f : GL (Fin (a + (b + 2))) k → ℂ) (h * u)) →
        φ f₁ = φ f) ∧
  ∀ (m : GL (Fin (a + (b + 2))) k) (x y : kˣ) (g : GL (Fin (a + b)) k),
      m.val.submatrix (blk3 a b) (blk3 a b) =
        fromBlocks (of fun _ _ => (x : k)) 0 0 (fromBlocks g.val 0 0 (of fun _ _ => (y : k))) →
      ∀ f f₁ : indSp a (b + 2) α β, (∀ h, (f₁ : GL (Fin (a + (b + 2))) k → ℂ) h = (f : GL (Fin (a + (b + 2))) k → ℂ) (h * m)) →
        ∀ h, (φ f₁ : GL (Fin (a + b)) k → ℂ) h = χ₁ x * χ₂ y * (φ f : GL (Fin (a + b)) k → ℂ) (h * g)

end GlobalTheory.JacLine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedField
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory.CMConjInvol

theorem cm_conj_invol_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧ ∀ x, σ x = x → ∃ f : F, algebraMap F E f = x :=
  fun _ _ _ _ _ _ _ _ h => ⟨GlobalTheory.HermLineZeros.conj_invol h, GlobalTheory.HermLineZeros.exists_of_fixed h⟩

end GlobalTheory.CMConjInvol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedFieldStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmExtension_conjugation_involutive_fixedField : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → (∀ x, σ (σ x) = x) ∧ ∀ x, σ x = x → ∃ f : F, algebraMap F E f = x := by
  first | exact @GlobalTheory.CMConjInvol.cm_conj_invol_fixed | exact GlobalTheory.CMConjInvol.cm_conj_invol_fixed | (intros; apply GlobalTheory.CMConjInvol.cm_conj_invol_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LettersEqFockVarsCore
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh


set_option maxHeartbeats 1000000 in
theorem letters_eq_fockVars_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (X : Data D.host.E D.R.r) (g : ℕ) (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' (inC O.c') X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))) (vr : Harm.Var X.Ψ (T.Q.Dw ((i : ℕ) + 1)).p X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → IsVarOf (Vc D i) (Wc D i) X (T.Q.Dw ((i : ℕ) + 1)).p vr → (∀ ℓ : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank, (vr (Dc.eL ℓ)).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (vr (Dc.eL ℓ)).1 ∧ ((vr (Dc.eL ℓ)).2.1 : ℕ) = ℓ.2.1) ∨ (ℓ.1 = conjEmb (tauE D (vr (Dc.eL ℓ)).1) ∧ ((vr (Dc.eL ℓ)).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ hT i Tp tup O _ X g Dc vr hM hp hv ℓ
  have hP := hT.laws.pins
  have hm : ∀ τ, τ ∉ X.Ψ → (T.Q.Dw ((i : ℕ) + 1)).mult τ ≤ X.p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg fun h : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 => hτ ((hM.psi τ).2 (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ h)), hp]
  obtain ⟨h1, h2⟩ := Dic.letter Dc (fun τ => RingHom.ext fun _ => rfl) hm ℓ
  obtain ⟨g1, g2, g3⟩ := hv (Dc.eL ℓ)
  refine ⟨g2.trans h1, ?_⟩
  rcases h2 with ⟨k, e1, e2, e3⟩ | ⟨k, e1, e2, e3⟩
  · rw [e1, Sum.elim_inl] at g3
    exact Or.inl ⟨e2.trans g1, g3.trans e3⟩
  · rw [e1, Sum.elim_inr] at g3
    exact Or.inr ⟨by rw [← g1]; exact e2, by rw [g3, e3]⟩

end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapCompAlt
noncomputable section

namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : Datum F} {p N : ℕ}
  {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp (D.OEp p)} {s₂ : S₂ ⟶ Sp (D.OEp p)} {s₃ : S₃ ⟶ Sp (D.OEp p)}
  {o₁ : Obj D p N s₁} {o₂ : Obj D p N s₂} {o₃ : Obj D p N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}

def ObjMap.comp (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) : ObjMap o₁ o₃ (f ≫ g) where
  φ := m₁.φ ≫ m₂.φ
  cart := IsGrpPullback.comp m₁.cart m₂.cart
  act a := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o₁.PP.isLB (pull_isLB o₂.PP.isLB m₁.φ) (pull_isLB o₃.PP.isLB _) m₁.pol
    (LBIso.chartPull (chartPullPull o₂.PP.L m₁.φ)
      (chartPullSame o₃.PP.L (fun _ : PUnit => m₁.φ ≫ m₂.φ) (fun _ => m₂.φ) (fun _ => 1) m₁.φ (fun _ => rfl))
      m₂.pol)
  eta a := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

theorem objMap_comp : ∀ (F : Type) [Field F] [NumberField F] [IsCMField F] (D : GlobalTheory.UPel.Datum F) (p N : ℕ)
    (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp (D.OEp p)) (s₂ : S₂ ⟶ Sp (D.OEp p)) (s₃ : S₃ ⟶ Sp (D.OEp p))
    (o₁ : GlobalTheory.UPel.Obj D p N s₁) (o₂ : GlobalTheory.UPel.Obj D p N s₂) (o₃ : GlobalTheory.UPel.Obj D p N s₃) (f : S₁ ⟶ S₂)
    (g : S₂ ⟶ S₃), GlobalTheory.UPel.ObjMap o₁ o₂ f → GlobalTheory.UPel.ObjMap o₂ o₃ g → Nonempty (GlobalTheory.UPel.ObjMap o₁ o₃ (f ≫ g)) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m₁ m₂ => ⟨m₁.comp m₂⟩

end GlobalTheory.UPel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsQProjOverOfIsProper
namespace GlobalTheory.UPel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

theorem isProjOver_of_isQProjOver_of_isProper :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
      IsQProjOver s → IsProper s → IsProjOver s := by
  intro R _ _ X s hq hp
  exact GlobalTheory.SchemeWords.isProjOver_iff.mpr ⟨hq, hp⟩

end GlobalTheory.UPel
end
