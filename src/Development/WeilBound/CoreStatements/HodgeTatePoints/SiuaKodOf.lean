module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNull
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUnique
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GfForms
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuativeLiftExistsUnique
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.SiuaKodOf
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace PositivityTheory.HtPt.Siua

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel

theorem siu_kodaira_of
    (h : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (μ : K → ℤ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → GroundTheory.Heights₂.Heights.FieldNumbers.relDim (mIdealOver F y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) → IsNef F y μ → 0 < GroundTheory.Heights₂.Heights.NumbersDVR.intNum F (mIdealOver F y) (fun _ : Fin (d + 1) => μ) → ∃ a : ℕ, 1 ≤ a ∧ ∃ σ ∈ secOver F y (a • μ - 1), σ ≠ 0) :
    VeryAmpleNefPlusAmple.Statement → SectionCount.Statement →
      GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.Statement := by
  intro hA hC K _ ι _ Ω _ _ y D a hD hV _ hN hg
  let _ : DecidableEq K := fun x y => Classical.propDecidable (x = y)
  have : Nonempty K := hV.1
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  have hI : genIdeal y = mIdealOver ℚ y := LiftBirationalNef.genIdeal_eq y
  have hP := isProjVarF_map_of_isArithVar hV
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k =>
    (hV.2.1.2.2 k).imp fun i hi => LiftBirationalNef.coord_ne_zero_of_not_mem hi
  have hdim : FieldNumbers.relDim (mIdealOver ℚ y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    hI ▸ (FieldNumbers.CutRegular.relDim_eq_natCast_iff _ (d + 1)).2 hP.2
  have hnef : IsNef ℚ y a := fun W hW hle hW1 =>
    NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg hN W
      ⟨(Bridge.isMultiProjPrime_iff W).mp hW, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
      (hI.le.trans hle)
  have hpos : 0 < NumbersDVR.intNum ℚ (mIdealOver ℚ y) (fun _ : Fin (d + 1) => a) := by
    rw [← hI]; exact hg
  obtain ⟨k, hk, σ, hσ, hσ0⟩ := h hA hC ℚ K ι Ω y d a hnz hdim hnef hpos
  refine ⟨k, σ, hk, hσ0, fun c hc => ?_⟩
  have h1 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hσ c) hc
  have h2 : σ * ∏ j, y ⟨j, c j⟩ ^ (-(k • a - 1) j) ∈ chartRingOver ℚ y c := h1
  have h3 : ∀ j, -(((1 : ℕ) : ℤ) * ((k : ℤ) • a - 1) j) = -(k • a - 1) j := fun j => by simp
  simp only [h3]
  exact h2

end PositivityTheory.HtPt.Siua
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenGen
noncomputable section

namespace PositivityTheory.HtPt.Hcptgen

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open scoped TensorProduct

theorem eig_generic : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (E : Type) [AddCommGroup E] [Module Ω E] (F : Type) [Field F] [NumberField F] (ρ : NumberField.RingOfIntegers F →+* Module.End Ω E) (I : Type) [Fintype I] [DecidableEq I] (σ : I → (NumberField.RingOfIntegers F →+* Ω)), Function.Injective σ → Fintype.card I = Module.finrank ℚ F → DirectSum.IsInternal fun s => eigSp ρ (σ s) := by
  intro Ω _ _ E _ _ F _ _ ρ I _ _ σ hσ hcard
  classical
  let τ : I → (F →+* Ω) := fun s => IsFractionRing.lift (EigSplit.injective_of_charZero F (σ s))
  have hτ : ∀ s (a : 𝓞 F), τ s (a : F) = σ s a := fun s a =>
    IsFractionRing.lift_algebraMap (EigSplit.injective_of_charZero F (σ s)) a
  have hτinj : Function.Injective τ := by
    intro s t hst'
    apply hσ
    ext a
    rw [← hτ, ← hτ, hst']
  let j : (F →+* Ω) → (F →ₐ[ℚ] AlgebraicClosure Ω) := fun φ =>
    ((algebraMap Ω (AlgebraicClosure Ω)).comp φ).toRatAlgHom
  have hj : Function.Injective j := by
    intro φ ψ hφψ
    ext x
    apply (algebraMap Ω (AlgebraicClosure Ω)).injective
    have := DFunLike.congr_fun hφψ x
    simpa [j] using this
  haveI : Finite (F →+* Ω) := Finite.of_injective j hj
  letI : Fintype (F →+* Ω) := Fintype.ofFinite _
  have hle : Fintype.card (F →+* Ω) ≤ Module.finrank ℚ F := by
    rw [← AlgHom.card ℚ F (AlgebraicClosure Ω)]
    exact Fintype.card_le_of_injective j hj
  have hge : Module.finrank ℚ F ≤ Fintype.card (F →+* Ω) := hcard ▸ Fintype.card_le_of_injective τ hτinj
  have hc : Fintype.card (F →+* Ω) = Module.finrank ℚ F := le_antisymm hle hge
  have hbij : Function.Bijective τ :=
    (Fintype.bijective_iff_injective_and_card τ).2 ⟨hτinj, hcard.trans hc.symm⟩
  have hsum : ∑ s, HT.eigProj ρ (τ s) = 1 := by
    rw [← HT.sum_eigProj_eq_one Ω E F ρ hc]
    exact hbij.sum_comp fun φ => HT.eigProj ρ φ
  have heig : ∀ s, eigSp ρ (σ s) = HT.eigSp ρ (τ s) := by
    intro s
    ext v
    simp [GlobalTheory.CompanionTheory.Ar.eigSp, HT.eigSp, Submodule.mem_iInf, sub_eq_zero, hτ]
  have spec := fun s => HT.ProjEig.eigProj_spec Ω E F ρ (τ s)
  simp only [heig]
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (fun s => ?_) ?_
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    have h0 : ⨆ t, ⨆ (_ : t ≠ s), HT.eigSp ρ (τ t) ≤ LinearMap.ker (HT.eigProj ρ (τ s)) :=
      iSup₂_le fun t ht y hy => (spec s).2.2.1 (τ t) (hτinj.ne ht) y hy
    have := h0 hx'
    rwa [LinearMap.mem_ker, (spec s).2.1 x hx] at this
  · rw [eq_top_iff]
    intro x _
    have h : x = ∑ s, HT.eigProj ρ (τ s) x := by
      rw [← LinearMap.sum_apply, hsum, Module.End.one_apply]
    rw [h]
    exact Submodule.sum_mem _ fun s _ => Submodule.mem_iSup_of_mem s ((spec s).1 x)

theorem isIntegral_tensor {O Ω₀ F : Type} [CommRing O] [Field Ω₀] [CharZero Ω₀] [Field F] [Algebra O Ω₀]
    [Algebra O F] (hF : ∀ u : F, IsAlgebraic ℤ u) : Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := by
  have h1 : ∀ u : F, _root_.IsIntegral Ω₀ ((1 : Ω₀) ⊗ₜ[O] u) := by
    intro u
    obtain ⟨a, ha, hi⟩ := (hF u).exists_integral_multiple
    have h2 : _root_.IsIntegral ℤ ((1 : Ω₀) ⊗ₜ[O] (a • u)) :=
      hi.map_of_comp_eq (RingHom.id ℤ) (Algebra.TensorProduct.includeRight : F →ₐ[O] Ω₀ ⊗[O] F).toRingHom
        (Subsingleton.elim _ _)
    have h3 : _root_.IsIntegral Ω₀ ((1 : Ω₀) ⊗ₜ[O] (a • u)) :=
      h2.map_of_comp_eq (Int.castRingHom Ω₀) (RingHom.id _) (Subsingleton.elim _ _)
    have ha' : (a : Ω₀) ≠ 0 := Int.cast_ne_zero.2 ha
    have e : (1 : Ω₀) ⊗ₜ[O] u = (a : Ω₀)⁻¹ • ((1 : Ω₀) ⊗ₜ[O] (a • u)) := by
      rw [TensorProduct.tmul_smul, ← Int.cast_smul_eq_zsmul Ω₀, smul_smul, inv_mul_cancel₀ ha', one_smul]
    rw [e]
    exact h3.smul _
  refine ⟨fun x => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | tmul a u =>
    have e : a ⊗ₜ[O] u = a • ((1 : Ω₀) ⊗ₜ[O] u) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e]
    exact (h1 u).smul a
  | add x y hx hy => exact hx.add hy

theorem eq_of_specializes_of_fst {X : Scheme.{0}} {O F Ω₀ : Type} [CommRing O] [Field F] [Field Ω₀] [CharZero Ω₀]
    (s : X ⟶ Sp O) (β : O →+* F) (g₀ : O →+* Ω₀) (ξ₀ : Sp Ω₀ ⟶ X) (h₀ : IsCptGen ξ₀) (hs : ξ₀ ≫ s = spMap g₀)
    (hF : ∀ u : F, IsAlgebraic ℤ u)
    {y y' : ↥(pullback s (spMap β))} (hy : pullback.fst s (spMap β) y = genPt ξ₀) (hyy : y' ⤳ y) : y' = y := by
  letI := β.toAlgebra
  letI := g₀.toAlgebra
  have hy' : pullback.fst s (spMap β) y' = genPt ξ₀ :=
    GlobalTheory.CompanionTheory.Ar.CptInh.nogen ξ₀ h₀ _ (hy ▸ hyy.map (pullback.fst s (spMap β)).continuous)
  have hsurj : SurjectiveOnStalks ξ₀ := by
    have : IsIso (Scheme.stalkClosedPointTo ξ₀) := (ConcreteCategory.isIso_iff_bijective _).2 h₀.bij
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ₀]
    infer_instance
  have hemb := SurjectiveOnStalks.isEmbedding_pullback (pullback.fst s (spMap β)) ξ₀
  obtain ⟨z, hz, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y
    (IsLocalRing.closedPoint Ω₀) hy
  obtain ⟨z', hz', hz₂'⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.fst s (spMap β)) (g := ξ₀) y'
    (IsLocalRing.closedPoint Ω₀) hy'
  have hzz : z' ⤳ z := by
    rw [← hemb.isInducing.specializes_iff, specializes_prod]
    simp only [hz, hz', hz₂, hz₂']
    exact ⟨hyy, specializes_rfl⟩
  have sq : IsPullback (pullback.snd (pullback.fst s (spMap β)) ξ₀)
      (pullback.fst (pullback.fst s (spMap β)) ξ₀ ≫ pullback.snd s (spMap β)) (spMap g₀) (spMap β) := by
    rw [← hs]
    exact (IsPullback.of_hasPullback (pullback.fst s (spMap β)) ξ₀).flip.paste_vert
      (IsPullback.of_hasPullback s (spMap β))
  let e := sq.isoPullback ≪≫ pullbackSpecIso O Ω₀ F
  have hint : Algebra.IsIntegral Ω₀ (Ω₀ ⊗[O] F) := isIntegral_tensor hF
  let p' : PrimeSpectrum (Ω₀ ⊗[O] F) := e.hom z'
  let p : PrimeSpectrum (Ω₀ ⊗[O] F) := e.hom z
  have hle : p' ≤ p := (PrimeSpectrum.le_iff_specializes _ _).2 (hzz.map e.hom.continuous)
  have hcm : (Ideal.comap (algebraMap Ω₀ (Ω₀ ⊗[O] F)) p'.asIdeal).IsMaximal :=
    Ideal.IsPrime.isMaximal' (Ideal.comap_isPrime _ _)
  have hmax : p'.asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Ω₀) p'.asIdeal hcm
  have heq : p' = p := PrimeSpectrum.ext (hmax.eq_of_le p.isPrime.ne_top hle)
  have hzeq : z' = z := by
    have h := congrArg e.inv heq
    simpa [p, p'] using h
  rw [← hz, ← hz', hzeq]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem exists_lift : ∃ x : Sp Ω ⟶ Xo.XF c, 𝔐.ξ ≫ 𝔐.f = x ≫ Y.j := by
  have hchar : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  haveI : CharZero 𝔐.Ω₀ := 𝔐.fn.charZero
  let g₀ : O →+* 𝔐.Ω₀ := (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom
  have hs : 𝔐.ξ₀ ≫ Y.s = spMap g₀ := by
    show _ = Spec.map (CommRingCat.ofHom (Spec.preimage (𝔐.ξ₀ ≫ Y.s)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hfn : 𝔐.ξ ≫ 𝔐.f = spMap 𝔐.fn ≫ 𝔐.ξ₀ := 𝔐.fn_over
  have hw : (𝔐.ξ ≫ 𝔐.f) ≫ Y.s = spMap 𝔐.cst ≫ spMap β := by
    rw [Category.assoc, 𝔐.cst_over]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let g : Sp Ω ⟶ pullback Y.s (spMap β) := pullback.lift (𝔐.ξ ≫ 𝔐.f) (spMap 𝔐.cst) hw
  have hgf : g ≫ pullback.fst _ _ = 𝔐.ξ ≫ 𝔐.f := pullback.lift_fst _ _ _
  have hall : ∀ w : Sp Ω, pullback.fst Y.s (spMap β) (g w) = genPt 𝔐.ξ₀ := by
    intro w
    rw [← Scheme.Hom.comp_apply, hgf, hfn, Scheme.Hom.comp_apply]
    exact congrArg 𝔐.ξ₀ (Subsingleton.elim (α := PrimeSpectrum 𝔐.Ω₀) _ _)
  have := HodgeBasic.noetherianSpace_pullback Y.proj β
  have := Y.jQ_open
  have := c.fin
  have hF : ∀ u : c.F, IsAlgebraic ℤ u := fun u =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2 (Algebra.IsAlgebraic.isAlgebraic u)
  have hran : Set.range g ⊆ Set.range Y.jQ := by
    rintro _ ⟨w, rfl⟩
    exact HodgeBasic.mem_of_dense_of_maximal Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense fun y' h' =>
      eq_of_specializes_of_fst Y.s β g₀ 𝔐.ξ₀ 𝔐.gen₀ hs hF (hall w) h'
  refine ⟨IsOpenImmersion.lift Y.jQ g hran, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hgf]

theorem isProper_gen : IsProper (pullback.snd 𝔐.t.G.hom 𝔐.ξ) := by
  obtain ⟨x, hx⟩ := exists_lift 𝔐
  haveI := Y.oF.proper
  have sq : IsPullback (pullback.fst 𝔐.t.G.hom 𝔐.ξ ≫ 𝔐.m.φ) (pullback.snd 𝔐.t.G.hom 𝔐.ξ) Y.t.G.hom
      (𝔐.ξ ≫ 𝔐.f) := (IsPullback.of_hasPullback 𝔐.t.G.hom 𝔐.ξ).paste_horiz 𝔐.m.cart.1
  have sq' : IsPullback (pullback.fst Y.oF.t.G.hom x ≫ Y.m.φ) (pullback.snd Y.oF.t.G.hom x) Y.t.G.hom
      (x ≫ Y.j) := (IsPullback.of_hasPullback Y.oF.t.G.hom x).paste_horiz Y.m.cart.1
  rw [hx] at sq
  rw [← sq.isoIsPullback_hom_snd _ _ sq']
  infer_instance

theorem finrank_Vgen (s : CMType H ⊕ CMType H) : Module.Finite Ω (𝔐.Vgen s) ∧
    Module.finrank Ω (𝔐.Vgen s) = labelRk D s := by
  obtain ⟨U, hU, b, hb, hfr⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_rfl⟩ (Set.mem_univ _)
  have hli := (hfr ⟨genPt 𝔐.ξ, specializes_rfl⟩ (Set.mem_univ _) hU).1
  have e : 𝔐.Vgen s = Submodule.span Ω (Set.range b) := hb.symm
  rw [e]
  exact ⟨Module.Finite.span_of_finite Ω (Set.finite_range b), by rw [finrank_span_eq_card hli, Fintype.card_fin]⟩

theorem two_mul_finrank : 2 * Module.finrank Ω 𝔐.Li = Module.finrank ℤ D.La := by
  classical
  have hchar : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  have hinj : Function.Injective 𝔐.emb := by
    intro s s' h
    refine HodgeBasic.labelEmb_injective c (RingHom.ext fun a => 𝔐.cst.injective ?_)
    exact congrArg (fun m : 𝓞 E →+* Ω => m a) h
  letI : Fintype (CMType H) := Fintype.ofFinite _
  have hcard : Fintype.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
    rw [Fintype.card_of_bijective (HodgeBasic.labelHom_bijective H), Embeddings.card]
  have hint : DirectSum.IsInternal 𝔐.Vgen := eig_generic Ω 𝔐.Li E 𝔐.ρ (CMType H ⊕ CMType H) 𝔐.emb hinj hcard
  haveI := fun s => (finrank_Vgen 𝔐 s).1
  have h1 : Module.finrank Ω 𝔐.Li = ∑ s, labelRk D s := by
    rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap 𝔐.Vgen) hint).finrank_eq, Module.finrank_directSum]
    exact Finset.sum_congr rfl fun s _ => (finrank_Vgen 𝔐 s).2
  rw [h1, GlobalTheory.datum_finrank_int D, ← hcard, Fintype.sum_sum_type, Fintype.card_sum, ← two_mul,
    Nat.mul_div_cancel_left _ two_pos]
  simp [labelRk]
  ring

end PositivityTheory.HtPt.Hcptgen
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.ChIsDeg
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ch

theorem unitAt_div {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {Λ : Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) :
    unitAt ξ p (s / t) := by
  have key : ∀ {s t : Ω}, Λ.IsGenAt p s → Λ.IsGenAt p t → s / t ∈ regAt ξ p := by
    intro s t hs ht
    have : s ∈ Submodule.span (regAt ξ p) {t} := by
      rw [← ht.2, hs.2]; exact Submodule.mem_span_singleton_self s
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 this
    have ha' : (a : Ω) * t = s := ha
    rw [← ha', mul_div_cancel_right₀ _ ht.1]
    exact a.2
  exact ⟨div_ne_zero hs.1 ht.1, key hs ht, by rw [inv_div]; exact key ht hs⟩

theorem isdeg_unique : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (Λ : Lat ξ Ω) (n n' : ℤ), IsCptGen ξ → Y.IsDeg Λ n → Y.IsDeg Λ n' → n = n' := by
  intro X Ω _ ξ K _ C z Y Λ n n' hξ ⟨h₀, h, s₀, s, r, g₀, g, hr, hf, e⟩
    ⟨h₀', h', s₀', s', r', g₀', g', hr', hf', e'⟩
  obtain ⟨φ, hφ, hu⟩ := ValHom.exists_valAt_hom X Ω ξ K z h₀ hξ
  have u₀ := unitAt_div g₀' g₀
  let c : K := φ ⟨s₀' / s₀, u₀.2.1⟩
  have hc : c ≠ 0 := ((hu ⟨_, u₀.2.1⟩).2 u₀).ne_zero
  have key : ∀ i, C.v i (r i) = C.v i (r' i) * C.v i c := by
    intro i
    obtain ⟨ψ, hψ, hv⟩ := ValHom.exists_valAt_hom X Ω ξ _ (Y.x i) (h i) hξ
    have u := unitAt_div (g i) (g' i)
    have hun : IsUnit (ψ ⟨_, u.2.1⟩) := (hv ⟨_, u.2.1⟩).2 u
    have hval := GlobalTheory.T.valAt_comp_local_hom X Ω ξ _ K (C.v i).valuationSubring.subtype (Y.x i) _ _
      ((hψ _ _).2 ⟨u.2.1, rfl⟩) (by rw [Y.gen i]; exact h₀)
    rw [Y.gen i] at hval
    obtain ⟨m1, e1⟩ := (hφ _ _).1 hval
    obtain ⟨m2, e2⟩ := (hφ _ _).1 (hr i).2
    obtain ⟨m3, e3⟩ := (hφ _ _).1 (hr' i).2
    have hone : C.v i ((C.v i).valuationSubring.subtype (ψ ⟨_, u.2.1⟩)) = 1 := by
      obtain ⟨w, hw⟩ := hun.exists_right_inv
      have h1 : C.v i ((ψ ⟨_, u.2.1⟩ : (C.v i).valuationSubring) : K) * C.v i (w : K) = 1 := by
        rw [← map_mul, ← MulMemClass.coe_mul, hw]; simp
      exact le_antisymm (ψ ⟨_, u.2.1⟩).2 (h1 ▸ mul_le_of_le_one_right' w.2)
    have : r i = (C.v i).valuationSubring.subtype (ψ ⟨_, u.2.1⟩) * (r' i * c) := by
      rw [← e1, ← e2, ← e3, ← map_mul, ← map_mul]
      congr 1
      refine Subtype.ext ?_
      have := (g' i).1
      have := g₀'.1
      have := g₀.1
      simp only [MulMemClass.coe_mul]
      field_simp
    rw [this, map_mul, hone, one_mul, map_mul]
  have h2 : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i (r i)) =
      (C.w i : ℤ) * WithZero.log (C.v i (r' i)) + (C.w i : ℤ) * WithZero.log (C.v i c) := by
    intro i
    rw [key, WithZero.log_mul ((Valuation.ne_zero_iff _).2 (hr' i).1)
      ((Valuation.ne_zero_iff _).2 hc), mul_add]
  rw [e, e']
  simp only [h2]
  rw [finsum_add_distrib (hf'.subset fun i hi h1 => hi (by simp [h1]))
    ((C.fin c hc).subset fun i hi h1 => hi (by simp [h1])), C.prod c hc, add_zero]

end PositivityTheory.HtPt.Ch
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.CiField
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

open MvPolynomial PositivityTheory.HtPt.Gf

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)] {K : Type} [Field K]

theorem cone_homog (y : (Σ k, J k) → K) {g : MRing J} {d : B → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = C (aeval y g) * ∏ k, X k ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mConeMap, aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, mul_assoc]
  congr 1
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Finset.prod_pow_eq_pow_sum, hg m hm k]

theorem exists_homog_val {w : (Σ k, J k) → K} {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ = 1) (f : MRing J) :
    ∃ (N : ℕ) (g : MRing J), IsMultiHomog g (fun _ => N) ∧ aeval w g = aeval w f := by
  classical
  have hm : ∀ e, aeval w (mon c e) = 1 := fun e => by simp [aeval_mon, hc]
  induction f using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, C a, fun m hm k => ?_, rfl⟩
    have : m = 0 := by
      by_contra h
      exact mem_support_iff.1 hm (by rw [coeff_C, if_neg (Ne.symm h)])
    simp [this]
  | add f g hf hg =>
    obtain ⟨N, f', h1, h2⟩ := hf
    obtain ⟨M, g', h3, h4⟩ := hg
    refine ⟨N + M, f' * mon c (fun _ => M) + g' * mon c (fun _ => N), hom_add (hom_mul h1 (hom_mon _ _))
      (hom_of_eq (hom_mul h3 (hom_mon _ _)) fun k => add_comm _ _), ?_⟩
    simp only [map_add (f := _), map_mul, hm, h2, h4, mul_one]
  | mul_X f q hf =>
    obtain ⟨N, f', h1, h2⟩ := hf
    refine ⟨N + 1, f' * mon (Function.update c q.1 q.2) (fun _ => 1), hom_mul h1 (hom_mon _ _), ?_⟩
    rw [map_mul, map_mul, h2, aeval_mon, aeval_X, Finset.prod_eq_single q.1 (fun l _ hl => by
      rw [Function.update_of_ne hl, hc, one_pow]) (by simp), Function.update_self, pow_one]

theorem birational_of_frac {w : (Σ k, J k) → K} {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ = 1)
    (hfr : ∀ s : K, ∃ f g : MRing J, aeval w g ≠ 0 ∧ aeval w f = s * aeval w g) : Birational w := by
  intro s
  have hm : ∀ e, aeval w (mon c e) = 1 := fun e => by simp [aeval_mon, hc]
  obtain ⟨f, g, h0, h⟩ := hfr s
  obtain ⟨N, f', h1, h2⟩ := exists_homog_val hc f
  obtain ⟨M, g', h3, h4⟩ := exists_homog_val hc g
  refine ⟨fun _ => N + M, f' * mon c (fun _ => M), g' * mon c (fun _ => N), hom_mul h1 (hom_mon _ _),
    hom_of_eq (hom_mul h3 (hom_mon _ _)) fun k => add_comm _ _, ?_, ?_⟩
  · rwa [map_mul, hm, h4, mul_one]
  · rw [map_mul, map_mul, hm, hm, h2, h4, mul_one, mul_one, h]

theorem isFunctionField_of_dim {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) K] {w : (Σ k, J k) → K} {c : ∀ k, J k}
    (hc : ∀ k, w ⟨k, c k⟩ = 1) (hb : Birational w) {W : Ideal (MRing J)} (hW : mCoordIdeal w = W)
    (hp : (p : MRing J) ∈ W) (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card B : ℕ) : WithBot ℕ∞)) :
    GroundTheory.FunctionField.IsFunctionField (ZMod p) K := by
  refine GlobalTheory.CompanionTheory.Ar.Flat.isFunctionField_of_fg_trdeg ?_ ?_
  · refine IntermediateField.fg_def.2 ⟨Set.range w, Set.finite_range w, top_le_iff.1 fun s _ => ?_⟩
    have key : ∀ f : MRing J, aeval w f ∈ IntermediateField.adjoin (ZMod p) (Set.range w) := by
      intro f
      induction f using MvPolynomial.induction_on with
      | C a => simp
      | add f g hf hg => rw [map_add]; exact add_mem hf hg
      | mul_X f q hf => rw [map_mul, aeval_X]; exact mul_mem hf (IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩)
    obtain ⟨d, g, h, -, -, h0, h1⟩ := hb s
    rw [← div_eq_iff h0] at h1
    exact h1 ▸ div_mem (key g) (key h)
  · have hker : RingHom.ker (mConeMap w).toRingHom = W := hW
    have hprime : W.IsPrime := hker ▸ RingHom.ker_isPrime _
    have hchar : CharP (MRing J ⧸ W) p := (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
      rw [← map_natCast (Ideal.Quotient.mk W), Ideal.Quotient.eq_zero_iff_mem]; exact hp)
    let _ := ZMod.algebra (MRing J ⧸ W) p
    haveI : FaithfulSMul (ZMod p) (MRing J ⧸ W) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
    have : IsScalarTower ℤ (ZMod p) (MRing J ⧸ W) := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
    have : Algebra.FiniteType (ZMod p) (MRing J ⧸ W) :=
      Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) _
    obtain ⟨n, h1, h2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ZMod p) (A := MRing J ⧸ W)
    have hn : n = 1 + Fintype.card B := by
      rw [hdim] at h1
      exact_mod_cast h1.symm
    let μ : MRing J ⧸ W →+* MvPolynomial B K :=
      Ideal.Quotient.lift W (mConeMap w).toRingHom fun a ha => (hker.ge ha :)
    have hμ : Function.Injective μ := RingHom.lift_injective_of_ker_le_ideal W _ hker.le
    let _ := μ.toAlgebra
    have hμ' : ∀ f, algebraMap (MRing J ⧸ W) (MvPolynomial B K) (Ideal.Quotient.mk W f) = mConeMap w f :=
      fun f => rfl
    have : FaithfulSMul (MRing J ⧸ W) (MvPolynomial B K) := (faithfulSMul_iff_algebraMap_injective _ _).2 hμ
    have : IsScalarTower (ZMod p) (MRing J ⧸ W) (MvPolynomial B K) :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
    have hX : ∀ k, IsAlgebraic (MRing J ⧸ W) (X k : MvPolynomial B K) := fun k => by
      have := isAlgebraic_algebraMap (A := MvPolynomial B K) (Ideal.Quotient.mk W (X ⟨k, c k⟩))
      rw [hμ'] at this
      simpa [mConeMap, hc] using this
    have : Algebra.IsAlgebraic (MRing J ⧸ W) (MvPolynomial B K) := ⟨fun f => by
      induction f using MvPolynomial.induction_on with
      | C s =>
        obtain ⟨d, g, h, hg, hh, h0, h1⟩ := hb s
        refine IsAlgebraic.of_smul (y := Ideal.Quotient.mk W h) (mem_nonZeroDivisors_of_ne_zero fun e => ?_) ?_
        · have h3 := hμ' h
          rw [e, map_zero, cone_homog w hh] at h3
          exact mul_ne_zero (mt C_eq_zero.1 h0)
            (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)) h3.symm
        · have h3 := isAlgebraic_algebraMap (A := MvPolynomial B K) (Ideal.Quotient.mk W g)
          rw [hμ', cone_homog w hg, h1, map_mul, mul_assoc, mul_comm, ← cone_homog w hh] at h3
          rwa [Algebra.smul_def, hμ']
      | add f g hf hg => exact hf.add hg
      | mul_X f k hf => exact hf.mul (hX k)⟩
    have e1 := trdeg_add_eq (ZMod p) (MRing J ⧸ W) (A := MvPolynomial B K)
    have e2 := trdeg_add_eq (ZMod p) K (A := MvPolynomial B K)
    rw [h2, trdeg_eq_zero, add_zero, hn] at e1
    rw [MvPolynomial.trdeg_of_isDomain, ← e1, Cardinal.lift_id, Cardinal.mk_fintype, Nat.cast_add, Nat.cast_one] at e2
    exact (Cardinal.add_nat_inj _).1 e2

theorem curve_field : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (W : Ideal (MRing J)) (p : ℕ) [Fact p.Prime], IsMultiProjPrime W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card B : ℕ) : WithBot ℕ∞) → ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod p) K) (_ : GroundTheory.FunctionField.IsFunctionField (ZMod p) K) (w : (Σ k, J k) → K), mCoordIdeal w = W ∧ Birational w ∧ ∀ k, ∃ c, w ⟨k, c⟩ ≠ 0 := by
  intro B _ J _ W p _ ⟨hprime, ⟨S, hS, hWS⟩, hrel⟩ hchar hdim
  choose c hc using hrel
  have hp := natCast_mem_of_charOf hchar
  let F := FractionRing (MRing J ⧸ W)
  let π : MRing J →+* F := (algebraMap (MRing J ⧸ W) F).comp (Ideal.Quotient.mk W)
  have hπ : ∀ f, π f = 0 ↔ f ∈ W := fun f => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact map_eq_zero_iff _ (IsFractionRing.injective (MRing J ⧸ W) F)
  have ht : ∀ k, π (X ⟨k, c k⟩) ≠ 0 := fun k h => hc k ((hπ _).1 h)
  let w' : (Σ k, J k) → F := fun q => π (X q) / π (X ⟨q.1, c q.1⟩)
  let K := Subfield.closure (Set.range w')
  let w : (Σ k, J k) → K := fun q => ⟨w' q, Subfield.subset_closure ⟨q, rfl⟩⟩
  have hw : ∀ k, w ⟨k, c k⟩ = 1 := fun k => Subtype.ext (div_self (ht k))
  have hK : CharP K p := (CharP.charP_iff_prime_eq_zero Fact.out).2 (K.subtype.injective (by
    rw [map_natCast, map_zero, ← map_natCast π, hπ]; exact hp))
  let ε : MvPolynomial B K →+* F := eval₂Hom K.subtype fun k => π (X ⟨k, c k⟩)
  have hε : ε.comp (mConeMap w).toRingHom = π := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun q => ?_
    · simp
    · change ε (mConeMap w (X q)) = _
      rw [mConeMap, aeval_X, map_mul, eval₂Hom_C, eval₂Hom_X']
      exact div_mul_cancel₀ _ (ht _)
  have hε' : ∀ f, ε (mConeMap w f) = π f := fun f => RingHom.congr_fun hε f
  have hW : mCoordIdeal w = W := by
    refine le_antisymm (fun f hf => (hπ f).1 ?_) (hWS.le.trans (Ideal.span_le.2 fun f hf => ?_))
    · rw [← hε', show mConeMap w f = 0 from hf, map_zero]
    · obtain ⟨a, ha⟩ := hS f hf
      refine mem_mCoordIdeal ha ?_
      have h1 := (hε' f).trans ((hπ f).2 (hWS.ge (Ideal.subset_span hf)))
      rw [cone_homog w ha, map_mul, eval₂Hom_C, map_prod, mul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact (map_eq_zero_iff _ K.subtype.injective).1 h1
      · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h1
        rw [map_pow, eval₂Hom_X'] at hk
        exact absurd hk (pow_ne_zero _ (ht k))
  have hb : Birational w := birational_of_frac hw fun s => by
    have hr : Subring.closure (Set.range w') ≤ (K.subtype.comp (aeval w : MRing J →ₐ[ℤ] K).toRingHom).range := by
      refine Subring.closure_le.2 ?_
      rintro _ ⟨q, rfl⟩
      exact ⟨X q, congrArg K.subtype (aeval_X w q)⟩
    obtain ⟨y, hy, z, hz, e⟩ := Subfield.mem_closure_iff.1 s.2
    obtain ⟨f, rfl⟩ := hr hy
    obtain ⟨g, rfl⟩ := hr hz
    have e' : aeval w f / aeval w g = s := K.subtype.injective (by rw [map_div₀]; exact e)
    by_cases h0 : aeval w g = 0
    · exact ⟨0, 1, by simp, by simp [← e', h0]⟩
    · exact ⟨f, g, h0, (div_eq_iff h0).1 e'⟩
  let _ := ZMod.algebra K p
  exact ⟨K, inferInstance, inferInstance, isFunctionField_of_dim hw hb hW hp hdim, w, hW, hb,
    fun k => ⟨c k, hw k ▸ one_ne_zero⟩⟩

end PositivityTheory.HtPt.Ci
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.CiCurveIn
set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

section Alg

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]

def chartEval {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : (k : B) → J k) : MRing J →ₐ[ℤ] Ω :=
  MvPolynomial.aeval fun q => y q / y ⟨q.1, c q.1⟩

theorem cone_step [DecidableEq B] {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (c : (k : B) → J k)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (q : Σ k, J k) :
    mConeMap y (MvPolynomial.X q * ∏ l ∈ Finset.univ.erase q.1, MvPolynomial.X ⟨l, c l⟩) =
      MvPolynomial.C (y q / y ⟨q.1, c q.1⟩) * mConeMap y (∏ l, MvPolynomial.X ⟨l, c l⟩) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q.1), map_mul, map_mul, ← mul_assoc]
  congr 1
  simp only [mConeMap, MvPolynomial.aeval_X]
  rw [← mul_assoc, ← map_mul, div_mul_cancel₀ _ (hy _)]

theorem exists_homog {Ω K : Type} [Field Ω] [Field K] (y : (Σ k, J k) → Ω) (w : (Σ k, J k) → K)
    (c : (k : B) → J k) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) (f : MRing J) :
    ∃ (N : ℕ) (g : MRing J),
      mConeMap y g = MvPolynomial.C (chartEval y c f) * mConeMap y (∏ l, MvPolynomial.X ⟨l, c l⟩) ^ N ∧
      mConeMap w g = MvPolynomial.C (chartEval w c f) * mConeMap w (∏ l, MvPolynomial.X ⟨l, c l⟩) ^ N := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, MvPolynomial.C a, by simp, by simp⟩
  | add f g hf hg =>
    obtain ⟨N, f', h1, h2⟩ := hf
    obtain ⟨M, g', h3, h4⟩ := hg
    refine ⟨N + M, f' * (∏ l, MvPolynomial.X ⟨l, c l⟩) ^ M + g' * (∏ l, MvPolynomial.X ⟨l, c l⟩) ^ N, ?_, ?_⟩
    · rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, h1, h3, map_add (chartEval y c), MvPolynomial.C_add]; ring
    · rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, h2, h4, map_add (chartEval w c), MvPolynomial.C_add]; ring
  | mul_X f q hf =>
    obtain ⟨N, f', h1, h2⟩ := hf
    refine ⟨N + 1, f' * (MvPolynomial.X q * ∏ l ∈ Finset.univ.erase q.1, MvPolynomial.X ⟨l, c l⟩), ?_, ?_⟩
    · rw [map_mul, cone_step y c hy, h1, map_mul, map_mul, chartEval, MvPolynomial.aeval_X]; ring
    · rw [map_mul, cone_step w c hw, h2, map_mul, map_mul, chartEval, MvPolynomial.aeval_X]; ring

theorem cone_X_eq_zero {Ω : Type} [Field Ω] (y : (Σ k, J k) → Ω) (q : Σ k, J k) :
    mConeMap y (MvPolynomial.X q) = 0 ↔ y q = 0 := by
  simp [mConeMap]

theorem ne_zero_of_le {Ω K : Type} [Field Ω] [Field K] {y : (Σ k, J k) → Ω} {w : (Σ k, J k) → K}
    (h : mCoordIdeal y ≤ mCoordIdeal w) {q : Σ k, J k} (hq : w q ≠ 0) : y q ≠ 0 := fun h0 =>
  hq ((cone_X_eq_zero w q).1 (h ((cone_X_eq_zero y q).2 h0)))

theorem chartEval_ker {Ω K : Type} [Field Ω] [Field K] {y : (Σ k, J k) → Ω} {w : (Σ k, J k) → K}
    (h : mCoordIdeal y ≤ mCoordIdeal w) (c : (k : B) → J k) (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) (f : MRing J)
    (hf : chartEval y c f = 0) : chartEval w c f = 0 := by
  obtain ⟨N, g, h1, h2⟩ := exists_homog y w c (fun k => ne_zero_of_le h (hw k)) hw f
  rw [hf, map_zero, zero_mul] at h1
  have h3 : mConeMap w g = 0 := h h1
  rw [h2, mul_eq_zero] at h3
  rcases h3 with h3 | h3
  · exact MvPolynomial.C_eq_zero.1 h3
  · have h4 := pow_eq_zero_iff'.1 h3
    rw [map_prod, Finset.prod_eq_zero_iff] at h4
    obtain ⟨⟨k, -, hk⟩, -⟩ := h4
    exact absurd ((cone_X_eq_zero w _).1 hk) (hw k)

omit [∀ k, Fintype (J k)] in
theorem segre_update [DecidableEq B] {Ω : Type} [Field Ω] {y : (Σ k, J k) → Ω} {c : (k : B) → J k}
    (h0 : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : B) (j : J k) :
    segre y (Function.update c k j) / segre y c = y ⟨k, j⟩ / y ⟨k, c k⟩ := by
  rw [Conj.segre, Conj.segre, ← Finset.prod_div_distrib, Finset.prod_eq_single k (fun l _ hl => by
    rw [Function.update_of_ne hl, div_self (h0 l)]) (by simp), Function.update_self]

theorem exists_chart_hom {Ω K : Type} [Field Ω] [Field K] {y : (Σ k, J k) → Ω} {w : (Σ k, J k) → K}
    (h : mCoordIdeal y ≤ mCoordIdeal w) (c : (k : B) → J k) (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    ∃ ψ : Algebra.adjoin ℤ (Set.range fun j => segre y j / segre y c) →+* K,
      ∀ k j, ∃ hm, ψ ⟨y ⟨k, j⟩ / y ⟨k, c k⟩, hm⟩ = w ⟨k, j⟩ / w ⟨k, c k⟩ := by
  classical
  have hle : Algebra.adjoin ℤ (Set.range fun j => segre y j / segre y c) ≤ (chartEval y c).range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    refine ⟨∏ k, MvPolynomial.X ⟨k, j k⟩, ?_⟩
    simp [chartEval, Conj.segre]
  let π := (chartEval y c).rangeRestrict.toRingHom
  have hπ : Function.Surjective π := (chartEval y c).rangeRestrict_surjective
  let ψ' := π.liftOfSurjective hπ ⟨(chartEval w c).toRingHom, fun f hf =>
    chartEval_ker h c hw f (congrArg Subtype.val hf)⟩
  have hψ' : ∀ f, ψ' (π f) = chartEval w c f := fun f => RingHom.liftOfSurjective_comp_apply _ _ _ _
  refine ⟨ψ'.comp (Subalgebra.inclusion hle).toRingHom, fun k j => ⟨Algebra.subset_adjoin
    ⟨Function.update c k j, segre_update (fun k => ne_zero_of_le h (hw k)) k j⟩, ?_⟩⟩
  refine Eq.trans (congrArg ψ' (Subtype.ext ?_)) ((hψ' (MvPolynomial.X ⟨k, j⟩)).trans ?_)
  · exact (MvPolynomial.aeval_X (fun q : Σ k, J k => y q / y ⟨q.1, c q.1⟩) ⟨k, j⟩).symm
  · exact MvPolynomial.aeval_X _ _

end Alg

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isUnit_regAt {p : Cpt ξ} {a : regAt ξ p} (h : unitAt ξ p (a : Ω)) : IsUnit a :=
  IsUnit.of_mul_eq_one ⟨_, h.2.2⟩ (Subtype.ext (mul_inv_cancel₀ h.1))

theorem exists_point {κ : Type} {x : κ → Ω} (tie : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) {K : Type} [Field K]
    (ψ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* K) :
    ∃ z : Spec (CommRingCat.of K) ⟶ X,
      ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), ValAt ξ z (a : Ω) (ψ a) := by
  have hI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨p, ⟨hp, hu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x tie c hc _ hI
  have hle : ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), (a : Ω) ∈ regAt ξ p := fun a =>
    (tie.ring c hc a).1 a.2 p hp
  let ι : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* regAt ξ p :=
    (Algebra.adjoin ℤ (Set.range fun j => x j / x c)).val.toRingHom.codRestrict _ hle
  let _ := ι.toAlgebra
  have hsurj : ∀ a : regAt ξ p, ∃ s t, s ∉ RingHom.ker ψ ∧ a * ι s = ι t := by
    intro a
    obtain ⟨s, hs, h1, h2⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x tie c p hp a).1 a.2
    exact ⟨⟨s, hs⟩, ⟨_, h2⟩, (hu _).2 h1, Subtype.ext (mul_comm _ _)⟩
  have hloc : IsLocalization (RingHom.ker ψ).primeCompl (regAt ξ p) := by
    refine (isLocalization_iff _ _).2 ⟨fun s => isUnit_regAt ((hu s).1 s.2), fun a => ?_, fun {a b} hab => ?_⟩
    · obtain ⟨s, t, hs, h⟩ := hsurj a
      exact ⟨⟨t, s, hs⟩, h⟩
    · exact ⟨1, by rw [show a = b from Subtype.ext (congrArg (fun u : regAt ξ p => (u : Ω)) hab)]⟩
  let φ : regAt ξ p →+* K := IsLocalization.lift (M := (RingHom.ker ψ).primeCompl) (g := ψ)
    fun s => IsUnit.mk0 _ s.2
  have hφ : ∀ a, φ (ι a) = ψ a := fun a => IsLocalization.lift_eq _ a
  have hl : IsLocalHom φ := ⟨fun a ha => by
    obtain ⟨s, t, hs, h⟩ := hsurj a
    have h1 := congrArg φ h
    rw [map_mul, hφ, hφ] at h1
    have ht : t ∉ RingHom.ker ψ := fun h0 => mul_ne_zero ha.ne_zero hs (h1.trans h0)
    exact isUnit_of_mul_isUnit_left (h ▸ isUnit_regAt (a := ι t) ((hu t).1 ht))⟩
  obtain ⟨z, ⟨-, hz⟩, -⟩ := GlobalTheory.T.existsUnique_centre_local_hom X Ω ξ tie.gen p K φ hl
  exact ⟨z, fun a => hφ a ▸ hz (ι a)⟩

theorem unitAt_of_val (hξ : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (h : genPt ξ ⤳ centre z) {a : Ω} {r : R} (ha : ValAt ξ z a r) : IsUnit r ↔ unitAt ξ ⟨centre z, h⟩ a := by
  obtain ⟨φ, h1, h2⟩ := ValHom.exists_valAt_hom X Ω ξ R z h hξ
  obtain ⟨hm, rfl⟩ := (h1 a r).1 ha
  exact h2 _

theorem inFibre_of_zero (hξ : IsCptGen ξ) {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {p : ℕ} (hp : (p : R) = 0) :
    InFibre ξ p ⟨centre z, h⟩ := fun hu =>
  not_isUnit_zero (hp ▸ (unitAt_of_val hξ h ⟨h, (p : X.presheaf.stalk (centre z)), map_natCast _ _,
    map_natCast _ _⟩).2 hu)

theorem exists_chart_fun {κ : Type} {x : κ → Ω} (tie : CoordTie ℤ ξ x) {c : κ} {p : Cpt ξ} (hp : InChart ξ x c p)
    {U : X.Opens} (hU : p.1 ∈ U) : ∃ a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), unitAt ξ p a ∧
      ∀ q : Cpt ξ, InChart ξ x c q → unitAt ξ q a → q.1 ∈ U := by
  obtain ⟨W, hW, hm⟩ := tie.affine c hp.1
  have hmem : ∀ q : Cpt ξ, InChart ξ x c q → q.1 ∈ W := fun q hq => (hm q.1).2 ⟨q.2, hq⟩
  obtain ⟨f, hf1, hf2⟩ := hW.exists_basicOpen_le (V := U) ⟨p.1, hU⟩ (hmem p hp)
  have hg : genPt ξ ∈ W := p.2.mem_open W.2 (hmem p hp)
  have key : ∀ (q : Cpt ξ) (hq : q.1 ∈ W), genMap ξ q (X.presheaf.germ W q.1 hq f) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hg f) := fun q hq =>
    congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_stalkSpecializes_apply hq q.2 f)
  refine ⟨_, (tie.ring c hp.1 _).2 fun q hq => ⟨_, key q (hmem q hq)⟩, ?_, fun q hq hu => hf1 ?_⟩
  · rw [← key p (hmem p hp), ← ValHom.isUnit_iff_unitAt ξ tie.gen]
    exact (X.mem_basicOpen f p.1 (hmem p hp)).1 hf2
  · rw [← key q (hmem q hq), ← ValHom.isUnit_iff_unitAt ξ tie.gen] at hu
    exact (X.mem_basicOpen f q.1 (hmem q hq)).2 hu

theorem curve_in_cpt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (segre y) → ∀ (K : Type) [Field K] (C : ACurve K) (w : (Σ k, J k) → K), mCoordIdeal y ≤ mCoordIdeal w → (∀ k, ∃ c, w ⟨k, c⟩ ≠ 0) → ∃ (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)), CoordsAt ξ y z w ∧ ∀ p : ℕ, (p : K) = 0 → InFibre ξ p ⟨centre z, h₀⟩ ∧ ∀ i, InFibre ξ p ⟨centre (Y.x i), h i⟩ := by
  intro X Ω _ ξ B _ J _ y tie K _ C w hle hw
  classical
  have hξ := tie.gen
  choose c hc using hw
  have hy := fun k => ne_zero_of_le hle (hc k)
  have hsc : segre y c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  obtain ⟨ψ, hψ⟩ := exists_chart_hom hle c hc
  obtain ⟨z, hz⟩ := exists_point tie hsc ψ
  have h₀ : genPt ξ ⤳ centre z := (hz 0).1
  have hmem : ∀ j, segre y j / segre y c ∈ Algebra.adjoin ℤ (Set.range fun j => segre y j / segre y c) :=
    fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  have hch : InChart ξ (segre y) c ⟨centre z, h₀⟩ := ⟨hsc, fun j => Val.mem (hz ⟨_, hmem j⟩) h₀⟩
  choose x hx using fun i => (GlobalTheory.T.valuative_lift_existsUnique X Ω ξ _ _ tie K (C.v i).valuationSubring z h₀).exists
  have hgen : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ x i = z := fun i => (hx i).2
  have hunit : ∀ i (a : Ω) (r : K), a ∈ regAt ξ ⟨centre (x i), (hx i).1⟩ → ValAt ξ z a r → C.v i r = 1 →
      unitAt ξ ⟨centre (x i), (hx i).1⟩ a := by
    intro i a r ha hr hv
    obtain ⟨ρ, hρ⟩ := Val.of_mem ha
    have h1 := LieTangent.valAt_base hξ (C.v i).valuationSubring.subtype hρ
    rw [hgen i] at h1
    refine (unitAt_of_val hξ _ hρ).1 ?_
    have h2 : (ρ : K) = r := LieTangent.valAt_unique hξ h1 hr
    have h3 : r ≠ 0 := fun h0 => by simp [h0] at hv
    refine IsUnit.of_mul_eq_one ⟨r⁻¹, ?_⟩ (Subtype.ext ?_)
    · change C.v i r⁻¹ ≤ 1
      rw [map_inv₀, hv, inv_one]
    · change (ρ : K) * r⁻¹ = 1
      rw [h2, mul_inv_cancel₀ h3]
  have hF : (⋃ j : {j // ψ ⟨_, hmem j⟩ ≠ 0}, {i | C.v i (ψ ⟨_, hmem j.1⟩) ≠ 1}).Finite :=
    Set.finite_iUnion fun j => C.fin _ j.2
  have hgood : ∀ i, i ∉ (⋃ j : {j // ψ ⟨_, hmem j⟩ ≠ 0}, {i | C.v i (ψ ⟨_, hmem j.1⟩) ≠ 1}) →
      InChart ξ (segre y) c ⟨centre (x i), (hx i).1⟩ := by
    intro i hi
    obtain ⟨d, hd⟩ := tie.cover ⟨centre (x i), (hx i).1⟩
    obtain ⟨ρ, hρ⟩ := Val.of_mem (hd.2 c)
    have h1 := LieTangent.valAt_base hξ (C.v i).valuationSubring.subtype hρ
    rw [hgen i] at h1
    have h2 := Val.mul h1 (hz ⟨_, hmem d⟩)
    change ValAt ξ z (segre y c / segre y d * (segre y d / segre y c)) _ at h2
    rw [div_mul_div_cancel₀ hd.1, div_self hsc] at h2
    have h3 := LieTangent.valAt_unique hξ h2 (Val.one h₀)
    have h4 : C.v i (ψ ⟨_, hmem d⟩) = 1 := by
      by_contra hcon
      exact hi (Set.mem_iUnion.2 ⟨⟨d, right_ne_zero_of_mul_eq_one h3⟩, hcon⟩)
    have h5 := congrArg (C.v i) h3
    rw [map_mul, h4, mul_one, map_one] at h5
    have h6 := hunit i _ _ (hd.2 c) h1 h5
    refine ⟨hsc, fun j => ?_⟩
    have h7 := mul_mem (hd.2 j) h6.2.2
    rwa [inv_div, div_mul_div_cancel₀ hd.1] at h7
  refine ⟨z, ⟨x, hgen, fun U hU => ?_⟩, h₀, fun i => (hx i).1, ⟨fun k => ⟨c k, IsUnit.mk0 _ (hc k)⟩,
    fun k d hd => ⟨ne_zero_of_le hle hd.ne_zero, fun j => ?_⟩⟩, fun p hp => ⟨inFibre_of_zero hξ h₀ hp, fun i =>
      inFibre_of_zero hξ _ (Subtype.ext (by simpa using hp))⟩⟩
  · obtain ⟨a, ha, hu, hq⟩ := exists_chart_fun tie hch hU
    have ha0 : ψ ⟨a, ha⟩ ≠ 0 := ((unitAt_of_val hξ h₀ (hz ⟨a, ha⟩)).2 hu).ne_zero
    refine (hF.union (C.fin _ ha0)).subset fun i hi => ?_
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    have h1 := hgood i hcon.1
    exact hi (hq _ h1 (hunit i a _ ((tie.ring c hsc a).1 ha _ h1) (hz ⟨a, ha⟩) (not_not.1 hcon.2)))
  · obtain ⟨m1, e1⟩ := hψ k d
    obtain ⟨m2, e2⟩ := hψ k j
    have v1 : ValAt ξ z (y ⟨k, d⟩ / y ⟨k, c k⟩) (w ⟨k, d⟩ / w ⟨k, c k⟩) := e1 ▸ hz ⟨_, m1⟩
    have v2 : ValAt ξ z (y ⟨k, j⟩ / y ⟨k, c k⟩) (w ⟨k, j⟩ / w ⟨k, c k⟩) := e2 ▸ hz ⟨_, m2⟩
    have hu := (unitAt_of_val hξ h₀ v1).1 (IsUnit.mk0 _ (div_ne_zero hd.ne_zero (hc k)))
    have hr := mul_mem (Val.mem v2 h₀) hu.2.2
    rw [inv_div, div_mul_div_cancel₀ (hy k)] at hr
    obtain ⟨r, hr⟩ := Val.of_mem hr
    refine ⟨r, hr, ?_⟩
    have h1 := Val.mul hr v1
    rw [div_mul_div_cancel₀ (ne_zero_of_le hle hd.ne_zero)] at h1
    have h2 := LieTangent.valAt_unique hξ h1 v2
    rw [← mul_div_assoc, div_left_inj' (hc k)] at h2
    exact h2.symm

end PositivityTheory.HtPt.Ci
end
end
