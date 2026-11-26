module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePreconnected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnDens

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFactorisationConnectedFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFactorisationConnectedFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SteinFact

theorem finite_appTop_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}}
    (f : X ⟶ Sp R) [IsProper f] :
    ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom.Finite := by
  letI := GlobalTheory.algebraΓOfHom f
  have h0 := GlobalTheory.ProperFinite.finite_coh_of_isProper f (GlobalTheory.structureModule X) 0
  have h1 := Module.Finite.equiv (GlobalTheory.cohOn.zeroEquiv R (GlobalTheory.structureModule X) ⊤)
  let ρ : GlobalTheory.sectionsOn (GlobalTheory.structureModule X) ⊤ →ₗ[R] Γ(X, ⊤) :=
    { toFun := fun s => (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤ s : Γ(X, ⊤))
      map_add' := fun s t => map_add (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤) s t
      map_smul' := fun r s => by
        rw [GlobalTheory.sectionsOn.toΓ_smul]
        rw [GlobalTheory.restrictGlobal_top]
        rfl }
  have hρ : Function.Bijective ρ := (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤).bijective
  exact Module.Finite.equiv (LinearEquiv.ofBijective ρ hρ)

theorem finite_app_of_isProper {X Y : Scheme.{0}} (g : X ⟶ Y) [IsProper g] {V : Y.Opens}
    (hV : IsAffineOpen V) [IsNoetherianRing Γ(Y, V)] : (g.app V).hom.Finite := by
  let j := (g ⁻¹ᵁ V).ι
  let g' : (g ⁻¹ᵁ V).toScheme ⟶ Sp Γ(Y, V) := g ∣_ V ≫ hV.isoSpec.hom
  have : IsProper g' := inferInstanceAs (IsProper (g ∣_ V ≫ hV.isoSpec.hom))
  have h1 := finite_appTop_of_isProper g'
  have hle : j ''ᵁ ⊤ ≤ g ⁻¹ᵁ V := (g ⁻¹ᵁ V).ι_image_top.le
  have e : (Scheme.ΓSpecIso (.of Γ(Y, V))).inv ≫ g'.appTop = g.appLE V (j ''ᵁ ⊤) hle := by
    ext r
    change (g ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso Γ(Y, V)).inv r) = _
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, ← CommRingCat.comp_apply, Category.assoc,
      Iso.inv_hom_id_assoc, GlobalTheory.ProperFinite.topIso_inv_appTop]
  rw [e] at h1
  have hi : IsIso (X.presheaf.map (homOfLE hle).op) := by
    rw [show homOfLE hle = eqToHom (g ⁻¹ᵁ V).ι_image_top from Subsingleton.elim _ _]
    infer_instance
  exact (RingHom.finite_respectsIso.cancel_right_isIso _ (X.presheaf.map (homOfLE hle).op)).1 h1

theorem stein_factorisation : ∀ (X Y : Scheme.{0}) (g : X ⟶ Y), IsLocallyNoetherian Y → IsProper g → ∃ (Y' : Scheme.{0}) (a : X ⟶ Y') (b : Y' ⟶ Y), a ≫ b = g ∧ IsFinite b ∧ IsProper a ∧ Surjective a ∧ (∀ V : Y'.Opens, Function.Bijective (a.app V).hom) ∧ ∀ y : Y', _root_.IsPreconnected {x : X | a x = y} := by
  intro X Y g hY hg
  have hb : IsFinite g.fromNormalization := by
    refine { toIsAffineHom := inferInstance, finite_app := fun U hU => ?_ }
    have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI := (g.app U).hom.toAlgebra
    have : Module.Finite Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := finite_app_of_isProper g hU
    have : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, g ⁻¹ᵁ U)) :=
      Module.IsNoetherian.finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, g ⁻¹ᵁ U)).toSubmodule
    rw [g.fromNormalization_app hU]
    exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).2 (RingHom.finite_algebraMap.2 this)
  have hY' : IsLocallyNoetherian g.normalization := LocallyOfFiniteType.isLocallyNoetherian g.fromNormalization
  have ha : IsProper g.toNormalization := by
    have : IsProper (g.toNormalization ≫ g.fromNormalization) := by
      rw [g.toNormalization_fromNormalization]; exact hg
    exact IsProper.of_comp _ g.fromNormalization
  have hbij : ∀ V : g.normalization.Opens, Function.Bijective (g.toNormalization.app V).hom := by
    intro V
    refine ⟨g.toNormalization.app_injective V, fun t => ?_⟩
    obtain ⟨s, hs⟩ := GlobalTheory.mem_range_app_of_forall_isAffineOpen g.toNormalization V t fun W hW hWV => by
      have : IsNoetherianRing Γ(g.normalization, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
      exact GlobalTheory.mem_range_toNormalization_app g W _
        (RingHom.IsIntegral.of_finite (finite_app_of_isProper g.toNormalization hW) _)
    exact ⟨s, hs⟩
  have hs : Surjective g.toNormalization := by
    have h := g.toNormalization.denseRange.closure_range
    rw [g.toNormalization.isClosedMap.isClosed_range.closure_eq] at h
    exact ⟨Set.range_eq_univ.mp h⟩
  exact ⟨g.normalization, g.toNormalization, g.fromNormalization, g.toNormalization_fromNormalization, hb, ha, hs,
    hbij, fun y => GlobalTheory.T.zariski_connectedness_isPreconnected_fibre X _ g.toNormalization hY' ha hbij y⟩

end GlobalTheory.SteinFact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFactorisationConnectedFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stein_factorisation_connected_fibres : ∀ (X Y : Scheme.{0}) (g : X ⟶ Y), IsLocallyNoetherian Y → IsProper g → ∃ (Y' : Scheme.{0}) (a : X ⟶ Y') (b : Y' ⟶ Y), a ≫ b = g ∧ IsFinite b ∧ IsProper a ∧ Surjective a ∧ (∀ V : Y'.Opens, Function.Bijective (a.app V).hom) ∧ ∀ y : Y', _root_.IsPreconnected {x : X | a x = y} := by
  first | exact @GlobalTheory.SteinFact.stein_factorisation | exact GlobalTheory.SteinFact.stein_factorisation | (intros; apply GlobalTheory.SteinFact.stein_factorisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedInnerProductDataDefiniteBottomLargeGri
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.BottomIPData

theorem mem_bottomPairFinitePlacesBelow_of_mem_exceptional {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T)
    {v : FinPl D} (hv : v ∈ G.pl.S0) : v ∈ sfB G t := by
  classical
  have hw : G.pl.w v ∈ locPl G t := by
    unfold locPl GlobalTheory.ChiGrid.Places.W0
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
  unfold sfB
  simp only [Finset.mem_image]
  exact ⟨_, hw, G.pl.under_w hv⟩

theorem under_mem_sfB {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (t : T)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ locPl G t) : w.under (𝓞 D.host.F) ∈ sfB G t := by
  classical
  unfold sfB
  simp only [Finset.mem_image]
  exact ⟨w, hw, rfl⟩

theorem unrOff_betaB_div_alphaB {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc)
    {μ₀ : T} (hL : Lc.Is μ₀) (i j : Fin D.R.m) (t : T) :
    GlobalTheory.LFun.UnrOff (betaB G i j / alphaB Lc i j t) ((sfB G t : Finset (FinPl D)) : Set (FinPl D)) := by
  classical
  intro w hw
  have hw' : w.under (𝓞 D.host.F) ∉ sfB G t := hw
  have hv : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h => hw' (mem_bottomPairFinitePlacesBelow_of_mem_exceptional G t h)
  have hQ : ∀ P ∈ Lc.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F) := fun P hP e =>
    hw' (e ▸ under_mem_sfB G t (by unfold locPl; exact Finset.mem_union_right _ hP))
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hχ : GlobalTheory.LFun.UnrAt (G.ch.chi (D.R.m - i)) w :=
    (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq _ h1 h2) w).2 (G.ch.unr _ h1 h2 w hv)
  have hμ0 : GlobalTheory.LFun.UnrAt (Lc.mu0 ((j : ℕ) + 1)) w := by
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 j) w).2 ((Lc.C.isMu0 j).unr w fun k hk => hv ?_)
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]
      exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hk'
    · exact Or.inr (Or.inl hk')
  have hξ : GlobalTheory.LFun.UnrAt (Lc.xi t) w := by
    refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
    by_contra hn
    rcases (hL.Q_ram t w).1 hn with hq | ⟨P', hq, hc⟩
    · exact hQ w hq rfl
    · exact hQ P' hq (GlobalTheory.BotTripleUnr.under_eq_of_isConjPl hc)
  have e : betaB G i j / alphaB Lc i j t = G.ch.chi (D.R.m - i) * (Lc.mu0 ((j : ℕ) + 1) * Lc.xi t)⁻¹ := by
    unfold betaB alphaB
    rw [mul_div_mul_right_eq_div, div_eq_mul_inv]
    rfl
  rw [e]
  exact hχ.mul (hμ0.mul hξ).inv

theorem isSphOff_pureTensorO {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : HSp D) (sS : RealMat S) (sT : RealMat T)
    (BS : RealMat S) (BT : RealMat T) (LS : Lat S) (LT : Lat T) {f₀ Φ f : WO S T → ℂ}
    (hvac : IsVacO ψ θ S T sS sT LS LT f₀) {e : AE D} {Pset : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e Pset)
    (hth : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T LS LT fun _ => True) 1 f₀ Φ f)
    (Sf : Finset (FinPl D)) (hP : ∀ PP ∈ Pset, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ Sf)
    (hpt : ∀ φ, IsFockVec ψ θ S T sS sT (pureTensorO ψ θ S T sS sT BS BT f φ)) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsSphOff ψ S T LS LT Sf (pureTensorO ψ θ S T sS sT BS BT f φ) :=
  GlobalTheory.FockSph.isLatVac_pureTensorO_off hvac.2.inf BS BT hvac he hth Sf hP (fun φ => (hpt φ).1) φ

theorem unram_bottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ P : PolF D WW.rank A.rank, Unram W.ψ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) X.rA.Λ X.rW.Λ (GlobalTheory.BottomIPData.sfB G t) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W i j A A' WW X hX t P
  have h := isBottomTri_is hX
  have hψ : IsStdChar D W.ψ (-1) := h.isVac.1
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have cS : ∀ τ, IsCartanInv (gramAt D (GlobalTheory.Grid.neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (h.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (h.rigW.2.2 τ).1
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (h.fst t) h.isVac.2.theta
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem t)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst t)
      h.isVac.2.theta hf (h.isVac.2.fock τ)
  have hpt := GlobalTheory.FockSph.isFockVec_pureTensorO (S := GlobalTheory.Grid.neg A) (T := WW) (sS := fun τ => -X.rA.s τ) (sT := X.rW.s)
    hψ hθ cS cT X.rA.B X.rW.B hf hv
  have hs := isSphOff_pureTensorO (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.rA.Λ X.rW.Λ
    h.isVac (h.idem t) (h.fst t) (sfB G t) (fun PP hPP => under_mem_sfB G t hPP) hpt P
  exact ⟨GlobalTheory.RowTest.isSelfDualC_neg' h.rigA.1, h.rigW.1, fun v _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2,
    unrOff_betaB_div_alphaB G hL i j t, hs, hs⟩

end GlobalTheory.BottomIPData

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundOfHyp
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SumSize GlobalTheory.FunObj.AaCoef
open GlobalTheory.RowClaim GlobalTheory.ArchTens ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.ArchTens.VolSize

theorem abs_zpow_le {q : ℕ} (hq : q ≠ 0) {z : ℤ} {A : ℝ} (h : |(z : ℝ)| ≤ A) :
    |(((q : ℚ) ^ z : ℚ) : ℝ)| ≤ Real.exp (A * Real.log q) := by
  have h0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have e : (((q : ℚ) ^ z : ℚ) : ℝ) = Real.exp ((z : ℝ) * Real.log q) := by
    rw [← Real.log_zpow, Real.exp_log (zpow_pos h0 z)]
    push_cast
    rfl
  rw [e, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ((le_abs_self _).trans h) (Real.log_natCast_nonneg _))

theorem prod_zpow_sum {q : ℚ} (hq : q ≠ 0) {ι : Type} (s : Finset ι) (z : ι → ℤ) : ∏ i ∈ s, q ^ z i = q ^ ∑ i ∈ s, z i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem coef_le_of_chosen {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {P : Pl D.host.E} (hP : P ∈ G.pl.W0)
    (hl : P ∈ locPl G t) {β : CosFam G t} (hβ : β ∈ S.supp t Φ) :
    |((S.term t Φ β ⟨P, hl⟩).coef : ℝ)| ≤
      Real.exp ((D.R.m : ℝ) ^ 3 * bigN D * cosExp G P * Real.log (resCard (Kw P) : ℕ)) := by
  classical
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hkeep : keepAt G P = false := by simp [keepAt, hP]
  have hdep : depthAt G P = cosExp G P := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨h1, h2⟩ := depthAt_w G hv
    rw [h1, h2]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := ((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm
  haveI := (isUnitVol_unitVol P).1
  have hT := isTensor_Tflip hL W S.B t Φ hde hc hl
  rw [hdep] at hT
  have hO := oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even
    (isUnif_unifAt P) h00.cond hT (fun j hj _ => givenLevel_KO G t P hj)
  have hb := hβ ⟨P, hl⟩
  have hb' : β ⟨P, hl⟩ ∈ unfSupport (psiAt W P) (unitVol P) false
      (Reps.through hs (givenLevel G t P) (stair (locGrid G t P) (unifAt P) (cosExp G P))) (Tflip W S.B t Φ P) := by
    have : keepAt G (⟨P, hl⟩ : locPl G t).1 = false := hkeep
    rw [this] at hb
    exact hb
  have hβ' := funext (hO _ hb')
  have hz : ∀ i : Fin ((locGrid G t P).m - 2), ∃ z : ℤ,
      invVol (conjLevel hs (givenLevel G t P) ((repsAt G t P).elt (β ⟨P, hl⟩)) (j := i + 1) (by omega)) =
        (resCard (Kw P) : ℚ) ^ z ∧ |z| ≤ (bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ))) := fun i =>
    factor_stair G t P hs (cosExp G P) _ (Nat.succ_pos _) _ (by
      rw [hβ']
      exact through_elt _ (by omega))
  choose z hz hzb using hz
  have hq : resCard (Kw P) ≠ 0 := resCard_ne P
  have e : (S.term t Φ β ⟨P, hl⟩).coef = (resCard (Kw P) : ℚ) ^ (∑ i, z i) := by
    rw [← prod_zpow_sum (by exact_mod_cast hq)]
    refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => hz i)
    rfl
  rw [e]
  refine abs_zpow_le hq ?_
  have hm2 : (((locGrid G t P).m - 2 : ℕ) : ℤ) ≤ D.R.m := by
    have : (locGrid G t P).m - 2 ≤ D.R.m := by show D.R.m - 2 ≤ D.R.m; omega
    exact_mod_cast this
  have key : |∑ i, z i| ≤ (D.R.m : ℤ) ^ 3 * bigN D * cosExp G P :=
    calc |∑ i, z i| ≤ ∑ i, |z i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin ((locGrid G t P).m - 2), (bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ))) :=
        Finset.sum_le_sum fun i _ => hzb i
      _ = (((locGrid G t P).m - 2 : ℕ) : ℤ) * ((bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ)))) := by simp
      _ ≤ (D.R.m : ℤ) * ((bigN D : ℤ) * ((D.R.m : ℤ) * ((cosExp G P : ℤ) * (D.R.m : ℤ)))) :=
        mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ = _ := by ring
  exact_mod_cast key

theorem exponent_le (P : Pl D.host.E) {C : ℝ} (hC : 2 ≤ C) :
    (D.R.m : ℝ) ^ 3 * bigN D * cosExp G P * Real.log (resCard (Kw P) : ℕ) ≤
      C * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * placeSz G P := by
  have h1 := log_absNorm_le P
  have hS := placeSz_nonneg G P
  have hmN : (D.R.m : ℝ) ≤ bigN D := by exact_mod_cast m_le_bigN
  rw [ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
  have h2 : (cosExp G P : ℝ) * Real.log (Ideal.absNorm P.asIdeal : ℕ) ≤ C * placeSz G P :=
    calc (cosExp G P : ℝ) * Real.log (Ideal.absNorm P.asIdeal : ℕ)
        ≤ (cosExp G P : ℝ) * (2 * Real.log (Ideal.absNorm (P.under (𝓞 D.host.F)).asIdeal)) :=
          mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ = 2 * placeSz G P := by rw [placeSz]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC hS
  have h3 : (D.R.m : ℝ) ^ 3 * bigN D ≤ (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 :=
    calc (D.R.m : ℝ) ^ 3 * bigN D = (D.R.m : ℝ) ^ 2 * bigN D * D.R.m := by ring
      _ ≤ (D.R.m : ℝ) ^ 2 * bigN D * bigN D := mul_le_mul_of_nonneg_left hmN (by positivity)
      _ = _ := by ring
  calc _ = ((D.R.m : ℝ) ^ 3 * bigN D) * ((cosExp G P : ℝ) * Real.log (Ideal.absNorm P.asIdeal : ℕ)) := by ring
    _ ≤ ((D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2) * (C * placeSz G P) :=
      mul_le_mul h3 h2 (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)) (by positivity)
    _ = _ := by ring

end GlobalTheory.ArchTens.VolSize

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowClose
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

open Formalism.L2.Host (HChar)

namespace GlobalTheory.TopFlipNu

theorem exists_pow_close {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x c : w.adicCompletion E)
    (hx : Valued.v x = 1) (hc : c ≠ 0) : ∃ k : ℕ, 0 < k ∧ Valued.v (x ^ k - 1) ≤ Valued.v c := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hK : IsCompact {y : w.adicCompletion E | Valued.v y ≤ 1} := by
    have := IsNonarchimedeanLocalField.isCompact_closedBall (w.adicCompletion E) 1
    convert this using 1
    ext y
    exact e.le_one_iff_le_one.symm
  have hv0 : Valued.v c ≠ 0 := by simpa using hc
  obtain ⟨s, -, hs⟩ := hK.elim_nhds_subcover (fun y => {z | (z - y) * c⁻¹ ∈ w.adicCompletionIntegers E}) fun y _ =>
    ((Valued.isOpen_valuationSubring _).preimage ((continuous_id.sub continuous_const).mul continuous_const)).mem_nhds
      (by simp)
  have h1 : ∀ n : ℕ, ∃ y : s, Valued.v (x ^ n - y) ≤ Valued.v c := fun n => by
    have : x ^ n ∈ {y : w.adicCompletion E | Valued.v y ≤ 1} := by simp [hx]
    obtain ⟨y, hy, h⟩ := Set.mem_iUnion₂.1 (hs this)
    refine ⟨⟨y, hy⟩, ?_⟩
    have h2 : Valued.v ((x ^ n - y) * c⁻¹) ≤ 1 := h
    rwa [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 hv0), one_mul] at h2
  choose f hf using h1
  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ k : ℕ, 0 < k ∧ Valued.v (x ^ k - 1) ≤ Valued.v c := fun a b hab h => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
    refine ⟨k + 1, by omega, ?_⟩
    have h3 := Valuation.map_sub_le _ (hf (a + k + 1)) (h ▸ hf a)
    have h4 : x ^ (a + k + 1) - f (a + k + 1) - (x ^ a - f (a + k + 1)) = x ^ a * (x ^ (k + 1) - 1) := by ring
    rwa [h4, map_mul, map_pow, hx, one_pow, one_mul] at h3
  obtain ⟨a, b, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hne with h' | h'
  exacts [key a b h' h, key b a h' h.symm]

theorem exists_pow_eq_one {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (h : χ.LevelLe w n) (x : (w.adicCompletion E)ˣ) (hx : Valued.v (x : w.adicCompletion E) = 1) :
    ∃ k : ℕ, 0 < k ∧ χ.loc w x ^ k = 1 := by
  have hu := Formalism.L2.Host.unif_spec w
  unfold Formalism.L2.Host.IsUnifAt at hu
  obtain ⟨k, hk, h1⟩ := exists_pow_close w x
    (((Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ^ n) hx
    (pow_ne_zero _ (Units.ne_zero _))
  refine ⟨k, hk, ?_⟩
  rw [← map_pow]
  refine h _ ?_ ?_
  · show Valued.v _ = 1
    rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
  · rw [map_pow, hu, ← WithZero.exp_nsmul] at h1
    rw [Units.val_pow_eq_pow_val]
    simpa using h1

theorem awayIm_unit {D : D7} {χ : HChar D.host.E} (hχ : LocIn D.what₂.embLL χ) {w : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (h : χ.LevelLe w n) (x : (w.adicCompletion D.host.E)ˣ) (hx : Valued.v (x : w.adicCompletion D.host.E) = 1) (m : ℕ) :
    GlobalTheory.KappaArith.AwayIm D m (χ.loc w x : ℂ) := by
  obtain ⟨k, hk, h1⟩ := exists_pow_eq_one h x hx
  obtain ⟨ζ, hζ⟩ := hχ w x
  have h2 : ζ ^ k = 1 := D.what₂.embLL.injective (by rw [map_pow, hζ, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one])
  exact ⟨ζ, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one m hk h2, hζ⟩

theorem chi_levelLe {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) : (G.ch.chiH i).LevelLe w 2 := by
  by_cases h : w.under (𝓞 D.host.F) ∈ G.pl.S0
  · rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact fun x hx h3 => (G.ch.lev0 i h1 h2 w h).1 x hx (h3.trans (WithZero.exp_le_exp.2 (by omega)))
    · exact (G.ch.lev1 i h1 h2 w h).1
  · exact fun x hx _ => G.ch.unr i h1 h2 w h x hx

theorem nu_arith : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → CharsIn G D.what₂.embLL → ∀ (i j : Fin D.R.m) (x : ∀ w : Pl D.host.E, (Kw w)ˣ) (t : T),
      (∀ w ∈ locPl G t, ValuativeRel.valuation (Kw w) (x w : Kw w) = 1) →
      ∃ z : ℂ, GlobalTheory.KappaArith.AwayIm D (Qn G t) z ∧ ∏ w ∈ locPl G t, (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) =
        z * ∏ w ∈ locPl G μ₀, (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := by
  classical
  intro D T L sc G μ₀ hL hC i j x t hx
  have hQ : L.Q μ₀ = ∅ := Finset.eq_empty_of_forall_notMem fun w hw =>
    (hL.Q_ram μ₀ w).2 (Or.inl hw) (by rw [hL.xi_base]; intro x _; rfl)
  have h0 : locPl G μ₀ = G.pl.W0 := by rw [locPl, hQ]; simp
  have hsub : G.pl.W0 ⊆ locPl G t := fun w hw => by unfold locPl; simp [hw]
  have hf : ∀ w, (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) =
      ((L.xiH t).loc w (x w) : ℂ) * (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := fun w => by
    have loc_mul (a b : HChar D.host.E) : (a * b).loc w (x w) = a.loc w (x w) * b.loc w (x w) := rfl
    have loc_one : (1 : HChar D.host.E).loc w (x w) = 1 := rfl
    simp only [Grid.nu, locGrid, MonoidHom.div_apply, loc_mul, hL.xi_base, loc_one,
      Units.val_div_eq_div_val, Units.val_mul, Units.val_one]
    ring
  have hb : ∀ w ∈ locPl G t, GlobalTheory.KappaArith.AwayIm D (Qn G t) (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := fun w hw => by
    haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
    have e := ValuativeRel.isEquiv (ValuativeRel.valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
    have hv : Valued.v (x w : Kw w) = 1 := e.eq_one_iff_eq_one.1 (hx w hw)
    have hv' : Valued.v (((x w)⁻¹ : (Kw w)ˣ) : Kw w) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
    have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
    have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
    have a := awayIm_unit (hC.mu0 j) ((L.C.isMu0 j).tame w) (x w) hv (Qn G t)
    have b := awayIm_unit (hC.chi _ h1 h2) (chi_levelLe G h1 h2 w) (x w)⁻¹ hv' (Qn G t)
    have hm : muBase L (j + 1) = L.C.mu0 j := by rw [muBase, dite_eq_left j.2]
    convert a.mul b using 1
    simp only [Grid.nu, locGrid, MonoidHom.div_apply, hL.xi_base, mul_one, hm, map_inv,
      Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
    exact div_eq_mul_inv _ _
  refine ⟨(∏ w ∈ locPl G t, ((L.xiH t).loc w (x w) : ℂ)) *
    ∏ w ∈ locPl G t \ G.pl.W0, (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ), ?_, ?_⟩
  · exact (GlobalTheory.KappaArith.AwayIm.prod _ _ fun w _ => GlobalTheory.KappaArith.awayIm_val hL (hC.xi t) _ w (x w)).mul
      (GlobalTheory.KappaArith.AwayIm.prod _ _ fun w hw => hb w (Finset.mem_sdiff.1 hw).1)
  · rw [h0, mul_assoc, Finset.prod_sdiff hsub, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => hf w

end GlobalTheory.TopFlipNu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianModelFibreSpecializationChain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianModelFibreSpecializationChain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.SpecChain

theorem eqvGen_specializes {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    [PreconnectedSpace X] (x y : X) : Relation.EqvGen (· ⤳ ·) x y := by
  classical
  let C : Set X := {y | Relation.EqvGen (· ⤳ ·) x y}
  have hsub : ∀ K ∈ irreducibleComponents X, (K ∩ C).Nonempty → K ⊆ C := by
    rintro K hK ⟨w, hwK, hwC⟩ v hv
    have hI : IsIrreducible K := hK.1
    have hcl : IsClosed K := isClosed_of_mem_irreducibleComponents K hK
    have hg := hI.isGenericPoint_genericPoint hcl
    have h1 : hI.genericPoint ⤳ w := hg.specializes hwK
    have h2 : hI.genericPoint ⤳ v := hg.specializes hv
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hwC (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h1)))
      (Relation.EqvGen.rel _ _ h2)
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have hC : C = ⋃ K ∈ {K ∈ irreducibleComponents X | (K ∩ C).Nonempty}, K := by
    ext v
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hv
      exact ⟨irreducibleComponent v, ⟨irreducibleComponent_mem_irreducibleComponents v,
        ⟨v, mem_irreducibleComponent, hv⟩⟩, mem_irreducibleComponent⟩
    · rintro ⟨K, ⟨hK, hne⟩, hvK⟩
      exact hsub K hK hne hvK
  have hCc : Cᶜ = ⋃ K ∈ {K ∈ irreducibleComponents X | ¬ (K ∩ C).Nonempty}, K := by
    ext v
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hv
      refine ⟨irreducibleComponent v, ⟨irreducibleComponent_mem_irreducibleComponents v, ?_⟩, mem_irreducibleComponent⟩
      intro hne
      exact hv (hsub _ (irreducibleComponent_mem_irreducibleComponents v) hne mem_irreducibleComponent)
    · rintro ⟨K, ⟨hK, hne⟩, hvK⟩ hv
      exact hne ⟨v, hvK, hv⟩
  have hC1 : IsClosed C := by
    rw [hC]
    exact (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion fun K hK => isClosed_of_mem_irreducibleComponents K hK.1
  have hC2 : IsClosed Cᶜ := by
    rw [hCc]
    exact (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion fun K hK => isClosed_of_mem_irreducibleComponents K hK.1
  have hclo : IsClopen C := ⟨hC1, isClosed_compl_iff.mp hC2⟩
  have hx : x ∈ C := Relation.EqvGen.refl x
  have := hclo.eq_univ ⟨x, hx⟩
  have hy : y ∈ C := this ▸ Set.mem_univ y
  exact hy

theorem quasiSober_of_generalization {X : Type*} [TopologicalSpace X] [QuasiSober X] (S : Set X)
    (hS : ∀ x s, s ∈ S → x ⤳ s → x ∈ closure S → x ∈ S) : QuasiSober S := by
  constructor
  intro T hT hTc
  have hT' : IsIrreducible (((↑) : S → X) '' T) := hT.image _ continuous_subtype_val.continuousOn
  have hξ := hT'.isGenericPoint_genericPoint_closure
  obtain ⟨t, ht⟩ := hT.nonempty
  have hξt : hT'.genericPoint ⤳ (t : X) := hξ.specializes (subset_closure ⟨t, ht, rfl⟩)
  have hξS : hT'.genericPoint ∈ S :=
    hS _ t t.2 hξt (closure_mono (Subtype.coe_image_subset S T) hξ.mem)
  refine ⟨⟨hT'.genericPoint, hξS⟩, ?_⟩
  show closure {(⟨hT'.genericPoint, hξS⟩ : S)} = T
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.image_singleton]
  change ((↑) : S → X) ⁻¹' closure {hT'.genericPoint} = T
  rw [hξ.def, ← Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, hTc.closure_eq]

theorem eqvGen_of_isPreconnected {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    (S : Set X) (hc : IsPreconnected S) (hS : ∀ x s, s ∈ S → x ⤳ s → x ∈ closure S → x ∈ S) :
    ∀ a ∈ S, ∀ b ∈ S, Relation.EqvGen (fun u v : X => u ∈ S ∧ v ∈ S ∧ u ⤳ v) a b := by
  intro a ha b hb
  haveI := quasiSober_of_generalization S hS
  haveI : PreconnectedSpace S := Subtype.preconnectedSpace hc
  have h := eqvGen_specializes (⟨a, ha⟩ : S) ⟨b, hb⟩
  have key : ∀ u v : S, Relation.EqvGen (· ⤳ ·) u v →
      Relation.EqvGen (fun u v : X => u ∈ S ∧ v ∈ S ∧ u ⤳ v) u v := by
    intro u v huv
    induction huv with
    | rel p q hpq => exact Relation.EqvGen.rel _ _ ⟨p.2, q.2, hpq.map continuous_subtype_val⟩
    | refl p => exact Relation.EqvGen.refl _
    | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans p q r _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  exact key _ _ h

end GlobalTheory.SpecChain

namespace GlobalTheory.SpecChain

theorem fibre_chain : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ y y' : Y.Z, πY y = z₁ → πY y' = z₁ → Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' := by
  intro g n F W Z i X₁ z₁ Y πY hZH y y' hy hy'
  obtain ⟨U₀, EE, -, -, -, hHom, hProp⟩ := hZH
  obtain ⟨U, hU, hiso⟩ := GlobalTheory.T.exists_nonempty_isIso_morphismRestrict_of_isHom_id X₁.o₁ X₁.Ω₁ Y X₁.M πY hHom
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI : IsLocallyNoetherian (Sp X₁.o₁) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
  haveI := X₁.M.lft
  haveI := Y.lft
  haveI := Y.qc
  haveI : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : CompactSpace Y.Z := by
    constructor
    have := QuasiCompact.isCompact_preimage (f := Y.s) (U := Set.univ) isOpen_univ isCompact_univ
    simpa using this
  haveI : IsNoetherian Y.Z := {}
  haveI : IsProper πY := hProp
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X₁.M.Z := (GlobalTheory.isNormalScheme_iff_pred _).1 X₁.normal
  have hc := GlobalTheory.ZariskiConn.fibre_preconnected Y.Z X₁.M.Z πY hN U hU hiso z₁
  have hS : ∀ x s, s ∈ πY.base ⁻¹' {z₁} → x ⤳ s → x ∈ closure (πY.base ⁻¹' {z₁}) → x ∈ πY.base ⁻¹' {z₁} := by
    intro x s hs hxs hx
    have h1 : πY.base x ⤳ z₁ := by
      have := hxs.map πY.base.hom.continuous
      rwa [show πY.base s = z₁ from hs] at this
    have h2 : z₁ ⤳ πY.base x := by
      rw [specializes_iff_mem_closure]
      have hcont := πY.base.hom.continuous
      have : closure (πY.base ⁻¹' {z₁}) ⊆ πY.base ⁻¹' closure {z₁} :=
        closure_minimal (Set.preimage_mono subset_closure) (isClosed_closure.preimage hcont)
      exact this hx
    exact (h1.antisymm h2).eq
  exact eqvGen_of_isPreconnected _ hc hS y hy y' hy'

end GlobalTheory.SpecChain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianModelFibreSpecializationChainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelianModel_fibre_specialization_chain : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ y y' : Y.Z, πY y = z₁ → πY y' = z₁ → Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' := by
  first | exact @GlobalTheory.SpecChain.fibre_chain | exact GlobalTheory.SpecChain.fibre_chain | (intros; apply GlobalTheory.SpecChain.fibre_chain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeConjDirectSumTraceSelfDualStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeConjDirectSumTraceSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (skewGram)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped nonZeroDivisors
open GlobalTheory.TripleSpaceW (conjSub mem_conjSub conjO coe_conjO)
open GlobalTheory.SkewLat (scLat pairLat)
open GlobalTheory.SkewLat.DualPair

noncomputable section

namespace GlobalTheory.SkewLat.DualPairConj

variable {D : D7}

theorem mem_conj_scLat {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {y : Fin n → D.host.E} :
    y ∈ conjSub (scLat D.host.AA (conjSub Λ)) ↔ ∀ c ∈ D.host.AA⁻¹, star c • y ∈ Λ := by
  rw [mem_conjSub, GlobalTheory.SkewLat.mem_scLat]
  refine forall_congr' fun c => forall_congr' fun _ => ?_
  have e : star (c • star y) = star c • y := by
    ext i; simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', star_star]
  rw [mem_conjSub, e]

theorem star_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {a : D.host.E} (ha : a ∈ D.host.AA)
    {s : Fin n → D.host.E} (hs : s ∈ Λ) : star a • s ∈ conjSub (scLat D.host.AA (conjSub Λ)) := by
  refine mem_conj_scLat.2 fun c hc => ?_
  obtain ⟨b, hb⟩ := int_of_inv_mul hc ha
  rw [smul_smul, ← star_mul', ← hb, ← coe_conjO]
  exact Λ.smul_mem (conjO b) hs

theorem fwd' (hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar) (S : HSp D)
    {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    (hΛ : IsSelfDualC S Λ) {x y : Fin S.rank → D.host.E} (hx : x ∈ conjSub (scLat D.host.AA (conjSub Λ)))
    (hy : y ∈ conjSub (scLat D.host.AA (conjSub Λ))) :
    IntTr (D.host.xi0 * hS S x y) := by
  rw [mem_conj_scLat] at hx hy
  have key : ∀ u ∈ D.host.AA * D.host.AA⁻¹, ∀ v ∈ D.host.AA * D.host.AA⁻¹,
      IntTr (D.host.xi0 * u * star v * hS S x y) := by
    intro u hu
    refine FractionalIdeal.mul_induction_on hu
      (C := fun u => ∀ v ∈ D.host.AA * D.host.AA⁻¹, IntTr (D.host.xi0 * u * star v * hS S x y)) ?_ ?_
    · intro a ha c hc v hv
      refine FractionalIdeal.mul_induction_on hv
        (C := fun v => IntTr (D.host.xi0 * (a * c) * star v * hS S x y)) ?_ ?_
      · intro a' ha' c' hc'
        obtain ⟨b, hb⟩ := (hΛ.2 (star c' • y)).1 (hy c' hc') (star c • x) (hx c hc)
        have e1 : D.host.xi0 * (a * c) * star (a' * c') * hS S x y = D.host.xi0 * a * star a' * (b : D.host.E) := by
          rw [hb, show (∑ i, ∑ j, star ((star c • x) i) * S.gram i j * (star c' • y) j) =
            hS S (star c • x) (star c' • y) from rfl, hS_smul, star_mul', star_star]
          ring
        rw [e1]
        exact ((intTr_iff_mem_dual _).2 (xi_mem hs ha ha')).mul_int b
      · intro v1 v2 h1 h2
        rw [star_add, show D.host.xi0 * (a * c) * (star v1 + star v2) * hS S x y =
          D.host.xi0 * (a * c) * star v1 * hS S x y + D.host.xi0 * (a * c) * star v2 * hS S x y by ring]
        exact h1.add h2
    · intro u1 u2 h1 h2 v hv
      rw [show D.host.xi0 * (u1 + u2) * star v * hS S x y =
        D.host.xi0 * u1 * star v * hS S x y + D.host.xi0 * u2 * star v * hS S x y by ring]
      exact (h1 v hv).add (h2 v hv)
  have := key 1 one_mem_AA_mul 1 one_mem_AA_mul
  simpa using this

theorem bwd' (hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA) (S : HSp D)
    {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hΛ : IsSelfDualC S Λ) {y : Fin S.rank → D.host.E}
    (h : ∀ a ∈ D.host.AA, ∀ s ∈ Λ, IntTr (D.host.xi0 * hS S (star a • s) y)) :
    y ∈ conjSub (scLat D.host.AA (conjSub Λ)) := by
  refine mem_conj_scLat.2 fun c hcA => ?_
  refine (hΛ.2 (star c • y)).2 fun s hs => ?_
  have hmem : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) ≤ D.host.AAbar *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) := by
    rw [show D.host.AAbar * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) =
      FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA * D.host.AAbar by ring, hX,
      ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    have h1 := (intTr_iff_mem_dual _).1 (h j hj s hs)
    rw [hS_smul_left, star_star] at h1
    rw [smul_mul_assoc, show hS S s y * D.host.xi0 * j = D.host.xi0 * (j * hS S s y) by ring]
    exact Submodule.smul_mem _ z h1
  have hXne : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA ≠ 0 :=
    mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 xi_ne) AA_ne
  have hle : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) ≤ D.host.AAbar := by
    calc FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y)
        = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (hS S s y) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hXne, mul_one]
      _ ≤ D.host.AAbar * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA) *
          (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AA)⁻¹ := by gcongr
      _ = D.host.AAbar := by rw [mul_assoc, mul_inv_cancel₀ hXne, mul_one]
  obtain ⟨b, hb⟩ := int_of_inv_mul hcA (hc _ (hle (FractionalIdeal.mem_spanSingleton_self _ _)))
  refine ⟨conjO b, ?_⟩
  have e : ((conjO b : 𝓞 D.host.E) : D.host.E) = hS S s (star c • y) := by
    rw [coe_conjO, hb, star_mul', star_star, hS_smul_right]
  first | exact e | exact e.symm

end GlobalTheory.SkewLat.DualPairConj


open GlobalTheory.SkewLat.DualPairConj in
theorem GlobalTheory.SkewLat.pairLat_conj_trace_selfDual : ∀ {D : D7} (A B : HSp D)
    {ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)},
    IsSelfDualC A ΛA → IsSelfDualC B ΛB → ∀ {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (y : Fin d → D.host.E),
    y ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e ↔
      ∀ x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e,
      ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) y x)) := by
  intro D A B ΛA ΛB hA hB d e y
  have hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar := fun c h => by
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj]; exact Formalism.L2.Pj.conj_mem_AAbar D h
  have hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA := by
    first | exact GlobalTheory.star_mem_AA_of_mem_AAbar | exact GlobalTheory.star_mem_AA_of_mem_AAbar D | (intros; apply GlobalTheory.star_mem_AA_of_mem_AAbar; assumption)
  constructor
  · intro hy x hx o
    have hy' := GlobalTheory.SkewLat.mem_pairLat.1 hy
    have hx' := GlobalTheory.SkewLat.mem_pairLat.1 hx
    rw [form_skewGram, mul_add]
    exact ((fwd hs A hA hx'.1 hy'.1).add (fwd' hs B hB hx'.2 hy'.2)) o
  · intro h
    refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨bwd hc A hA fun a ha s hs' => ?_, bwd' hc B hB fun a ha s hs' => ?_⟩
    · let x : Fin d → D.host.E := fun i => Sum.elim (fun k => a * s k) (fun _ => 0) (e.symm i)
      have hxA : (fun k => x (e (.inl k))) = a • s := by ext k; simp [x]
      have hxB : (fun k => x (e (.inr k))) = 0 := by ext k; simp [x]
      have hx : x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e := by
        refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩
        · rw [hxA]; exact smul_mem_scLat ha hs'
        · rw [hxB]; exact zero_mem _
      intro o
      have := h x hx o
      rwa [form_skewGram, hxA, hxB, hS_zero_left, add_zero] at this
    · let x : Fin d → D.host.E := fun i => Sum.elim (fun _ => 0) (fun k => star a * s k) (e.symm i)
      have hxA : (fun k => x (e (.inl k))) = 0 := by ext k; simp [x]
      have hxB : (fun k => x (e (.inr k))) = star a • s := by ext k; simp [x]
      have hx : x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e := by
        refine GlobalTheory.SkewLat.mem_pairLat.2 ⟨?_, ?_⟩
        · rw [hxA]; exact zero_mem _
        · rw [hxB]; exact star_smul_mem ha hs'
      intro o
      have := h x hx o
      rwa [form_skewGram, hxA, hxB, hS_zero_left, zero_add] at this

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB alpha beta blk)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf HasExp SplitsFully)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.TripleSpaceW (conjSub)
open GlobalTheory.SkewLat (scLat pairLat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledLattice_conj_directSum_trace_selfDual : ∀ {D : D7} (A B : HSp D)
    {ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)},
    IsSelfDualC A ΛA → IsSelfDualC B ΛB → ∀ {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (y : Fin d → D.host.E),
    y ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e ↔
      ∀ x ∈ pairLat (scLat D.host.AA ΛA) (conjSub (scLat D.host.AA (conjSub ΛB))) e,
      ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) y x)) := by
  first | exact @GlobalTheory.SkewLat.pairLat_conj_trace_selfDual | exact GlobalTheory.SkewLat.pairLat_conj_trace_selfDual | (intros; apply GlobalTheory.SkewLat.pairLat_conj_trace_selfDual <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleFibreIntegralPullbackMulFibreClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnivEqOfLocalPreimageEq
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

theorem GlobalTheory.FlagCell2.univ_eq_of_local_preimage_eq : ∀ (M N : Type) [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] (π : N → M), Measurable π → ∀ (μ : Measure N) (ν : Measure M), (∀ x : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ T, MeasurableSet T → T ⊆ U → μ (π ⁻¹' T) = ν T) → μ Set.univ = ν Set.univ := by
  intro M N _ _ _ _ _ π hπ μ ν h
  choose U hUo hxU hU using h
  obtain ⟨S, hSc, hS⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  haveI : Countable S := hSc.to_subtype
  have hcov : ⋃ i : S, U i = Set.univ := by
    rw [← Set.biUnion_eq_iUnion S (fun i _ => U i), hS]
    exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨x, hxU x⟩
  have hmap : μ.map π = ν := by
    refine (Measure.ext_iff_of_iUnion_eq_univ hcov).2 fun i => ?_
    ext T hT
    have hm : MeasurableSet (T ∩ U i) := hT.inter (hUo i).measurableSet
    rw [Measure.restrict_apply hT, Measure.restrict_apply hT, Measure.map_apply hπ hm]
    exact hU i _ hm Set.inter_subset_right
  have : μ Set.univ = μ.map π Set.univ := by
    rw [Measure.map_apply hπ MeasurableSet.univ, Set.preimage_univ]
  rw [this, hmap]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleFibreIntegralPullbackMulFibreClass
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem fibre_integral : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ α : (atlas X σ).Fld, (atlas X σ).IsForm α → (atlas Y σ).integral ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) = (atlas X σ).integral α := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH α hα
  have hol := GlobalTheory.T.varietyComplexPointsMap_isHolomorphic F σ X Y f hf
  have hmet := GlobalTheory.T.isFlaggedBundleMetric_pullGram_refinement F σ X Y ι m E E' φ f hf hR H hH
  have hgr := GlobalTheory.T.fullFlagGradedLineChernForms_smooth_dbarClosed F σ Y ι m E' _ hmet
  have hpb := (((GlobalTheory.formCalculus _ _ (atlas X σ)).2.2.2.2 _ _ (atlas Y σ) _ hol).2 1 α α).2.2.2 hα
  have hev := ((GlobalTheory.formCalculus _ _ (atlas Y σ)).2.2.2.1 (Root m) (grF E' (pullGram E H φ f hf)) (fibrePoint m)
    fun x => (hgr x).1).1
  have hβ := (((GlobalTheory.formCalculus _ _ (atlas Y σ)).2.1 1 _ _ hpb.1 hev)).2.1
  have key : ∀ s : ℤˣ, (atlas Y σ).part ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α *
      evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) s Set.univ = (atlas X σ).part α s Set.univ := by
    intro s
    refine GlobalTheory.FlagCell2.univ_eq_of_local_preimage_eq _ _ (ptMap σ f hf) hol.1.measurable _ _ fun x => ?_
    have := X.smooth_str
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := X.dim) (σ := σ) x
    obtain ⟨A, hA⟩ := E.nonempty (under x)
    refine ⟨c.e.source ∩ interior {z | A ∈ E.S (under z)}, c.e.open_source.inter isOpen_interior,
      ⟨hc, mem_interior_iff_mem_nhds.2 (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m 0 E x A hA)⟩, fun T hT hTU => ?_⟩
    exact GlobalTheory.FlagCell2.LocFib.part_preimage F σ X Y ι m E E' φ f hf hR H hH α hα hβ s c A _ (c.e.open_source.inter isOpen_interior)
      Set.inter_subset_left (fun z hz => (interior_subset (s := {z | A ∈ E.S (under z)}) hz.2 :)) T hT hTU
  rw [HolAtlas.integral, HolAtlas.integral, measureReal_def, measureReal_def, measureReal_def, measureReal_def, key, key]

end GlobalTheory.ChernCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleFibreIntegralPullbackMulFibreClassStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagBundle_fibreIntegral_pullback_mul_fibreClass : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ α : (atlas X σ).Fld, (atlas X σ).IsForm α → (atlas Y σ).integral ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) = (atlas X σ).integral α := by
  first | exact @GlobalTheory.ChernCalc.fibre_integral | exact GlobalTheory.ChernCalc.fibre_integral | (intros; apply GlobalTheory.ChernCalc.fibre_integral <;> assumption)
end
end
