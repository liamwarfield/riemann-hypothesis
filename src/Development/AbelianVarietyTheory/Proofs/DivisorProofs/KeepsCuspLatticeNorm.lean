module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KeepsCuspOfIsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPart
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.OnlySecondOfFormLaws
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffPolynomialEqZeroOfVanishingOnGLFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpand
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.WeightEqZeroOfOneIsSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspNe
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GamAtOfLawsCore

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelIsometry

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp GlobalTheory.DictMove GlobalTheory.AllWt GlobalTheory.LevDesc GlobalTheory.LevelKeeps
open GlobalTheory.Dict (castFr)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.FormTies (levFull)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem val_transl_nonneg (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (γ : LevelAut Dw l) {e : Ix Dw → ℤ}
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (h : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) :
    ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v (transl Xo c γ f) := by
  rintro la _ ⟨⟨q, S, io, n, ho, y, hy, η, hη, rfl⟩, rfl⟩
  let := io.toAlgebra
  have hmv := levR_move hpq hA γ y.1
  let y' : IntFr Xo c S io :=
    ⟨_, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      GlobalTheory.FormTies.LevelMove.integral_of_levR _ _ _ _ _ _ (levFull Dw l γ) S io y.1 _ hmv y.2.2⟩
  have h0 : 0 ≤ nval S.V n (evI y' f) := h la _ ⟨PtV.mk la ho y' hy () trivial, rfl⟩
  have e1 : evI y (transl Xo c γ f) = evI y' f := evR_transl hpq hA γ hf y.1
  show 0 ≤ nval S.V n (evI y (transl Xo c γ f))
  rw [e1]
  exact h0

variable {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ}

theorem norm_rdU_transl (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hP : HasPeriods φ)
    (hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0) (γ : LevelAut Dw l) {k k' : U.Comp} {δ : GL (Fin r) E}
    (h : Carries φ (levFull Dw l γ).1 k k' δ) {w : Ix Dw → ℤ} (hw : Even (w none)) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c w) {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    ‖rdU U (transl Xo c γ f) k x‖ = ‖rdU U f k' (lact δ (castFr h.mt.psi x))‖ := by
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have hA' : l.A.Coprime l.M := by rw [hA]; exact Nat.coprime_one_left _
  obtain ⟨z, hz1, hz⟩ := exists_const_of_carries (w := 0) (n := 2) (s' := (levFull Dw l γ).2) hσ hU hpq hA hP hxi
    ⟨fun _ => antitone_const, even_two⟩ (transl Xo c γ)
    (fun f hf => by rw [← secZ_nat] at hf ⊢; exact transl_mem_secZ hpq hA' γ hf)
    (fun y => by
      obtain ⟨ρ, ν, -, hν, hm⟩ := levR_move hpq hA' γ y
      exact ⟨ρ, ν, _, hν, hm, fun f hf => by rw [← secZ_nat] at hf; exact evR_transl hpq hA' γ hf y⟩) h
  obtain ⟨m, hm⟩ := hw
  obtain ⟨ρ, ν, -, hν, hmv⟩ := levR_move hpq hA' γ (U.un k ⟨x, hx⟩)
  obtain ⟨a₁, b₁⟩ := move_eq hσ hpq hA hP h hν ⟨x, hx⟩ hmv
  obtain ⟨t₀, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen _ _ a₁ b₁
  have key : ∀ (w : Ix Dw → ℤ), ∀ f ∈ secZ Xo c w, rdU U (transl Xo c γ f) k x =
      toC (t₀ : CAt σ) ^ w none * rdU U f k' (lact δ (castFr h.mt.psi x)) := fun w f hf => by
    have v1 : rdU U (transl Xo c γ f) k x = toC (evR Xo c (transl Xo c γ f) (U.un k ⟨x, hx⟩)) := dif_pos hx
    have v2 : rdU U f k' (lact δ (castFr h.mt.psi x)) = toC (evR Xo c f (U.un k' ⟨_, h.mt.mem_dom hx⟩)) :=
      dif_pos (h.mt.mem_dom hx)
    rw [v1, v2, evR_transl hpq hA' γ hf, GlobalTheory.FlagTan.evR_frBor hf ht, Fintype.prod_option]
    simp only [Option.elim, one_zpow, Finset.prod_const_one, mul_one]
    exact congrArg (· * toC (evR Xo c f (U.un k' ⟨_, h.mt.mem_dom hx⟩))) (Units.val_zpow_eq_zpow_val (α := ℂ) t₀ _)
  obtain ⟨f₂, hf₂, h0⟩ := exists_sec_two hσ hU (hU.1 ▸ hpq) k' (h.mt.mem_dom hx)
  have h2 := hz f₂ hf₂ x hx
  rw [← secZ_nat] at hf₂
  rw [key _ f₂ hf₂] at h2
  have h3 : toC (t₀ : CAt σ) ^ (2 : ℤ) = z := mul_right_cancel₀ h0 h2
  rw [key w f hf, hm, ← two_mul, zpow_mul, h3, norm_mul, norm_zpow, hz1, one_zpow, one_mul]

end Free

section Adelic

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH _root_.Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.LevDesc GlobalTheory.DictMove
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.FormTies (levFull)
open scoped Matrix TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def rightEquiv (V : HSp D) (κ : GA D V) : AutQ V ≃ᵐ AutQ V :=
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have hrel : ∀ (k a b : GA D V), QuotientGroup.rightRel (GQ V) a b → QuotientGroup.rightRel (GQ V) (a * k) (b * k) :=
    fun k a b h => by
      rw [QuotientGroup.rightRel_apply] at h ⊢
      rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  have hm : ∀ k : GA D V, Measurable (Quotient.map' (· * k) (hrel k) : AutQ V → AutQ V) := fun k _ hs =>
    measurable_mul_const k (autMk_measurable V hs)
  { toFun := Quotient.map' (· * κ) (hrel κ)
    invFun := Quotient.map' (· * κ⁻¹) (hrel κ⁻¹)
    left_inv := fun q => Quotient.inductionOn q fun a => congrArg (autMk V) (mul_inv_cancel_right a κ)
    right_inv := fun q => Quotient.inductionOn q fun a => congrArg (autMk V) (inv_mul_cancel_right a κ)
    measurable_toFun := hm κ
    measurable_invFun := hm κ⁻¹ }

theorem eLpNorm_right (V : HSp D) (hs : V.SigOK) (κ : GA D V) (Φ : GA D V → ℝ)
    (hΦ : ∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) (p : ENNReal) :
    eLpNorm (fun q : AutQ V => Φ (q.out * κ)) p (muQ1 V) = eLpNorm (fun q : AutQ V => Φ q.out) p (muQ1 V) := by
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hR := ((GlobalTheory.CoreLawsCompare.invProb_iff V hP hV _).2 rfl).2
  have hmap : (muQ1 V).map (rightEquiv V κ) = muQ1 V := Measure.ext fun s hs => by
    rw [MeasurableEquiv.map_apply]
    exact hR κ _ (fun _ => rfl) s hs
  have hout : ∀ g, Φ (autMk V g).out = Φ g := fun g => by
    have e : (QuotientGroup.rightRel (GQ V)) g (autMk V g).out := Quotient.exact (Quotient.out_eq (autMk V g)).symm
    rw [QuotientGroup.rightRel_apply] at e
    rw [← hΦ _ e g, inv_mul_cancel_right]
  conv_rhs => rw [← hmap, (rightEquiv V κ).measurableEmbedding.eLpNorm_map_measure]
  congr 1
  funext q
  rw [← hout (q.out * κ)]
  exact congrArg (fun q' : AutQ V => Φ (rightEquiv V κ q').out) (Quotient.out_eq q)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem exists_induces (V : HSp D) {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι)
    (γ : LevelAut Dw l) : ∃ κ, Induces V l ι (levFull Dw l γ).1 κ := by
  obtain ⟨red, h1, -, h3⟩ := GlobalTheory.LevelReduction.exists_isReduction D H Dw l V ι hι
  obtain ⟨k, rfl⟩ := h1 γ
  refine ⟨k, k.2.1, ?_, fun a ha => ?_⟩
  · have e : Formalism.L2.Pj.gLat V k = Formalism.L2.Pj.gLat V 1 := by
      unfold Formalism.L2.Pj.gLat
      rw [map_one, Units.val_one]
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨_, (k.2.2 y).2 hy, Matrix.one_mulVec _⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨_, ((k⁻¹).2.2 y).2 hy, ?_⟩
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          map_one, Units.val_one]
    unfold latGHat
    rw [e]
  · obtain ⟨w, hw, e⟩ := h3 k a ha
    exact ⟨-w, neg_mem hw, by rw [neg_nsmul, ← e, neg_sub]; exact (add_sub_cancel _ _).symm⟩


set_option maxHeartbeats 4000000 in
theorem petE_transl {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {V : HSp D}
    (hs : V.SigOK) (hr : V.rank = r) {dict : GA D V → Σ k, Frame (U.X k).Ψ r}
    {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} {g : ℕ}
    {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th th' : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {Kf : Subgroup (GA D V)}
    (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hW : ∀ k, ModelW V hr (U.X k))
    (hι : LatEmb V ι) (hL : DictLat U V hr dict ι e F ik φ th x₀) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hD : DictIsUnif V dict Kf th' hr) (hu : ∀ g τ i, ‖dmin (U.X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    {G : WTZ D.host.E} (hG : Even G.2) (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (modelWt U G k) γ = 1)
    (γ : LevelAut Dw l) {f : Rul Xo c} (hf : f ∈ secZ Xo c (exZ Dw G)) (hfc : rdU U f ∈ holSub U.X (modelWt U G)) :
    petE V dict (muQ1 V) (modelWt U G) (rdU U (transl Xo c γ f)) = petE V dict (muQ1 V) (modelWt U G) (rdU U f) := by
  subst hr
  obtain ⟨κ, hκ⟩ := exists_induces V hι γ
  have hN : ∀ (P : FDSec U.X) g, ptN (modelWt U G) P (dict g) = ‖P (dict g).1 (dict g).2‖ := fun P g =>
    pnorm_eq_of_unit _ _ _ _ (hu g)
  unfold petE
  simp only [hN]
  have hΦ : ∀ a ∈ GQ V, ∀ h, ‖rdU U f (dict (a * h)).1 (dict (a * h)).2‖ =
      ‖rdU U f (dict h).1 (dict h).2‖ := fun a ha h => by
    obtain ⟨a', ha', e₁⟩ := hD.1 a ha h
    have := (GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ hfc (dict h).1).1.1.2.2 a' ha' _ (hD.2.2.2.1 h)
    rw [hχ _ _ ha', one_mul] at this
    rw [e₁]
    exact congrArg norm this
  have hright : eLpNorm' (fun q : AutQ V => ‖rdU U f (dict (q.out * κ)).1 (dict (q.out * κ)).2‖) 2 (muQ1 V) =
      eLpNorm' (fun q : AutQ V => ‖rdU U f (dict q.out).1 (dict q.out).2‖) 2 (muQ1 V) := by
    obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
    have hR := ((GlobalTheory.CoreLawsCompare.invProb_iff V hP hV _).2 rfl).2
    have hmap : (muQ1 V).map (rightEquiv V κ) = muQ1 V := Measure.ext fun s hs => by
      rw [MeasurableEquiv.map_apply]
      exact hR κ _ (fun _ => rfl) s hs
    have hout : ∀ g, ‖rdU U f (dict (autMk V g).out).1 (dict (autMk V g).out).2‖ =
        ‖rdU U f (dict g).1 (dict g).2‖ := fun g => by
      have e : (QuotientGroup.rightRel (GQ V)) g (autMk V g).out := Quotient.exact (Quotient.out_eq (autMk V g)).symm
      rw [QuotientGroup.rightRel_apply] at e
      rw [← hΦ _ e g, inv_mul_cancel_right]
    unfold eLpNorm'
    conv_rhs => rw [← hmap, lintegral_map_equiv]
    congr 1
    apply lintegral_congr
    intro q
    dsimp only
    have he : rightEquiv V κ q = autMk V (q.out * κ) := by
      exact (congrArg (rightEquiv V κ) (Quotient.out_eq q)).symm
    rw [he, hout]
  rw [← hright]
  congr 1
  funext q
  obtain ⟨hx, δ, hc, e₁⟩ := GlobalTheory.StabMove.exists_carries (V := V) (W := V) rfl rfl rfl (dict := dict) ι hU hW hL hth
    hD.2.2.2.1 hκ q.out
  change (dict (q.out * κ)).2 = _ at e₁
  rw [e₁]
  exact norm_rdU_transl hσ hU hpq hA hL.1.2 (fun k k' => (hW k).2.trans (hW k').2.symm) γ hc hG hf hx

end Adelic

end GlobalTheory.LevelIsometry

end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.LevDesc (transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open scoped TensorProduct
open GlobalTheory GlobalTheory.CovTop


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ G : WTZ D.host.E, Even G.2 → KeepsCusp Y.U G ∧ ∀ (γ : LevelAut (T.Q.Dw j) Y.d.l₂) (f g : Y.V G), (g : Rul Y.d.Xo₂ Y.d.c₂) = pull Y.d.Xo₂ Y.d.c₂ γ f → (f ∈ AllWt.latW Y.U G → g ∈ AllWt.latW Y.U G) ∧ ∀ σ, Y.nrm G σ g = Y.nrm G σ f := by
  intro D T hT j hp _ _ hj Y e o hY G hG
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := le_add_right hp
  have hA := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := by rw [hA]; exact Nat.coprime_one_left _
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hY.lev.1.2.1, hT.pins.2.1.1]
  have hχ := fun σ hσ => GlobalTheory.AllWt.Model.chi_modelWt (Y.U σ) (hY.chiTriv σ hσ) G hG
  obtain ⟨ι, hι, -, hpin⟩ := hY.adPin
  refine ⟨GlobalTheory.LevelKeeps.keepsCusp_of_isUnf hpq hA hG hY.unf (fun σ hσ k k' => ?_) (fun σ hσ => ?_) hχ,
    fun γ f g hg => ⟨fun hf => ?_, fun σ => ?_⟩⟩
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    exact ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    obtain ⟨th, _, hth, hD⟩ := hY.dictU σ hσ
    obtain ⟨x₀, h0, _, g, e, F, ik, φ, th', hth', hL⟩ := hpin σ hσ
    obtain rfl : th = th' := funext fun k => funext fun τ =>
      GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth k τ) (hth' k τ)
    exact GlobalTheory.LevelKeeps.mem_group (hY.unf σ hσ) hA ((hY.unf σ hσ).1 ▸ hpq) hr hW h0 (hM ▸ hY.levelK) hth hD fun h => by
      obtain ⟨γ, -, -, -, h3⟩ := hL.2 h
      exact ⟨_, h3⟩
  · intro la v hv
    show 0 ≤ v (g : Rul Y.d.Xo₂ Y.d.c₂)
    rw [hg]
    exact GlobalTheory.LevelIsometry.val_transl_nonneg hpq hA' γ⁻¹ (AllWt.mem_cuspW.1 f.2).1 hf la v hv
  · have hσ := goodEmb_goodOf (c := Y.d.c₂) σ
    obtain ⟨hr, hW⟩ := hY.modelW _ hσ
    obtain ⟨th, _, -, hD⟩ := hY.dictU _ hσ
    obtain ⟨x₀, -, _, g', e, F, ik, φ, th', hth', hL⟩ := hpin _ hσ
    have := GlobalTheory.LevelIsometry.petE_transl (D.sp.W_sig j) hr hσ (hY.unf _ hσ) hpq hA hW hι hL hth' hD (hY.unit _ hσ) hG
      (hχ _ hσ) γ⁻¹ (AllWt.mem_cuspW.1 f.2).1 ((AllWt.mem_cuspW.1 f.2).2 _ hσ)
    show _ * (AllWt.petE _ _ _ _ (rdU (Y.U (goodOf Y.d.c₂ σ)) (g : Rul Y.d.Xo₂ Y.d.c₂))).toReal = _
    rw [hg]
    exact congrArg (fun t : ENNReal => AllWt.lieFacZ (T.Q.Dw j) (xiR D) G * t.toReal) this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLift
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

theorem isKSValue_act : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (a' : OAct O A'), (∀ z, (a.act z).left ≫ i = i ≫ (a'.act z).left) → ∀ (z : O) {f : HdR A} {w : epsR R ⟶ A}, IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z) := by
  intro R _ A _ A' _ i h O _ a a' hi z f w hf
  haveI := a.hom z
  haveI := a'.hom z
  obtain ⟨k, ⟨d, hd, e⟩, l⟩ := hf
  rw [act_apply]
  have hm := push_mem_liftFil (epsDP R) h h (a.act z) (a'.act z) (e := (hi z).symm) hd
  have hl := l.push (a.act z)
  refine ⟨push (dp0 R) (𝟙 _) (a.act z) k, ⟨_, hm, fun c ↦ ?_⟩, hl⟩
  have kk : GrpMor (dp0 R) (𝟙 _) A (epsDP R) (DeRham.epsRed R) A
      (algebraMap R (DualNumber R)) (𝟙 _) (a.act z).left :=
    ⟨(constMor A).dp, (constMor A).base, by simpa using (Over.w (a.act z)),
      (homMor (dp0 R) (𝟙 _) (a.act z)).mul⟩
  have hM := homMor (epsDP R) (DeRham.epsRed R) (a.act z)
  have e1 := GrpMor.pull_pull (constMor A) hM kk (fun _ ↦ rfl) (by simp) c
  have e2 := GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) (a.act z)) (constMor A) kk (fun _ ↦ rfl) rfl c
  rw [push_apply]
  change d (hM.pull ((constMor A).pull c)) = _
  rw [e1, ← e2, e]
  rfl
end GlobalTheory.KSExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKodairaSpencerValueEndomorphismLiftStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (a' : OAct O A'), (∀ z, (a.act z).left ≫ i = i ≫ (a'.act z).left) → ∀ (z : O) {f : HdR A} {w : epsR R ⟶ A}, IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z) := by
  first | exact @GlobalTheory.KSExist.isKSValue_act | exact GlobalTheory.KSExist.isKSValue_act | (intros; apply GlobalTheory.KSExist.isKSValue_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAdd
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem interNumRed_of_cls_eq_nsmul_add : ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (L M M' : LB X) (hL : L.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (a b : ℕ) (C : Closeds X), IsCompleteCurve k C → cls L hL = a • cls M hM + b • cls M' hM' → interNumRed k C ![L] = a * interNumRed k C ![M] + b * interNumRed k C ![M'] := by
  intro k _ X q hq
  letI := algebraΓOfHom q
  intro L M M' hL hM hM' a b C hC e
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hq
  rw [hC.interNumRed_of_cls_eq_add hH hL (isLB_lbPow hM a) (isLB_lbPow hM' b)
    (by rw [cls_lbPow hM, cls_lbPow hM', e]),
    hC.interNumRed_lbPow hH hM, hC.interNumRed_lbPow hH hM']

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAddStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_curve_of_class_eq_smul_add : ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (L M M' : LB X) (hL : L.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (a b : ℕ) (C : Closeds X), IsCompleteCurve k C → cls L hL = a • cls M hM + b • cls M' hM' → interNumRed k C ![L] = a * interNumRed k C ![M] + b * interNumRed k C ![M'] := by
  first | exact @GlobalTheory.interNumRed_of_cls_eq_nsmul_add | exact GlobalTheory.interNumRed_of_cls_eq_nsmul_add | (intros; apply GlobalTheory.interNumRed_of_cls_eq_nsmul_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSmoothProjectiveVarietyProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSmoothProjectiveVarietyProperties
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.BaseChangeVariety

theorem baseChange_props : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y) (D : ℕ) [SmoothOfRelativeDimension D p], IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → GeometricallyConnected p → IsIntegral X ∧ IsLocallyNoetherian X ∧ SmoothOfRelativeDimension D q ∧ IsProjOver q ∧ Function.Surjective π := by
  intro k E _ _ _ Y X p q π D _ H hP _
  have hs : SmoothOfRelativeDimension D q :=
    (smoothOfRelativeDimension_isStableUnderBaseChange D).of_isPullback H ‹_›
  have : Smooth p := SmoothOfRelativeDimension.smooth D p
  have : Smooth q := SmoothOfRelativeDimension.smooth D q
  have hI : IsIntegral X := GlobalTheory.isIntegral_of_isPullback_of_smooth H
  have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  exact ⟨hI, hN, hs, GlobalTheory.PosBaseChange.isProjOver_of_isPullback H hP, GlobalTheory.PosBaseChange.surjective_proj H⟩

end GlobalTheory.BaseChangeVariety
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSmoothProjectiveVarietyPropertiesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_smooth_projective_variety_properties : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y) (D : ℕ) [SmoothOfRelativeDimension D p], IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → GeometricallyConnected p → IsIntegral X ∧ IsLocallyNoetherian X ∧ SmoothOfRelativeDimension D q ∧ IsProjOver q ∧ Function.Surjective π := by
  first | exact @GlobalTheory.BaseChangeVariety.baseChange_props | exact GlobalTheory.BaseChangeVariety.baseChange_props | (intros; apply GlobalTheory.BaseChangeVariety.baseChange_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleModuloEffectiveAwayFromPointPullAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleModuloEffectiveAwayFromPointPullAffine
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.AmplePull

theorem ampleAt_pull : ∀ (Y X : Scheme.{0}) (π : X ⟶ Y) [IsAffineHom π] (N : LB Y), N.IsLB → ∀ x : X,
    AmpleAt N (π x) → AmpleAt (N.pull π) x := by
  intro Y X π _ N hN x h
  obtain ⟨m, A, s, hm, hA, hAmp, hy⟩ := h
  have hNm : (lbPow N m).IsLB := isLB_lbPow hN m
  have hP : (LB.div (lbPow N m) A).IsLB := LB.isLB_div hNm hA
  have hN' : (N.pull π).IsLB := LB.isLB_pull hN π
  have hA' : (A.pull π).IsLB := LB.isLB_pull hA π
  have hNm' : (lbPow (N.pull π) m).IsLB := isLB_lbPow hN' m
  have hQ : (LB.div (lbPow (N.pull π) m) (A.pull π)).IsLB := LB.isLB_div hNm' hA'
  have iso : LBIso (LB.div (lbPow (N.pull π) m) (A.pull π)) ((LB.div (lbPow N m) A).pull π) := by
    rw [← cls_eq_iff hQ (LB.isLB_pull hP π), cls_div hNm' hA' hQ, cls_pull hP π, cls_div hNm hA hP,
      cls_lbPow hN' m hNm', cls_pull hN π hN', cls_pull hA π hA', cls_lbPow hN m hNm, map_sub, map_nsmul]
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hQ (LB.isLB_pull hP π) iso (ZM.RepBC.secPull _ π s)
  refine ⟨m, A.pull π, t, hm, hA', hAmp.pull_of_isAffineHom π, ?_⟩
  rw [ht, GlobalTheory.ZV.GraphSystem.nonzeroLocus_pull]
  exact hy

end GlobalTheory.AmplePull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleModuloEffectiveAwayFromPointPullAffineStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ampleModuloEffectiveAwayFromPoint_pull_affine : ∀ (Y X : Scheme.{0}) (π : X ⟶ Y) [IsAffineHom π] (N : LB Y), N.IsLB → ∀ x : X, AmpleAt N (π x) → AmpleAt (N.pull π) x := by
  first | exact @GlobalTheory.AmplePull.ampleAt_pull | exact GlobalTheory.AmplePull.ampleAt_pull | (intros; apply GlobalTheory.AmplePull.ampleAt_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientPolynomialGLFunctionNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientPolynomialGLFunctionNeZero
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoeffNonvanish

open MvPolynomial

theorem exists_coefFn_ne_zero : ∀ {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n),
    ∃ (F : VV D.what₂.LL lam) (x : GLR D n), coefFn D.what₂.embLL lam (F : Pol D.what₂.LL D.what₂.Tau n) x ≠ 0 := by
  intro D n lam
  refine ⟨⟨Formalism.L2.Col.extVV D.what₂.LL lam, Formalism.L2.Col.extVV_mem D.what₂.LL lam⟩, ?_⟩
  by_contra h
  push_neg at h
  have hmap : MvPolynomial.map D.what₂.embLL (Formalism.L2.Col.extVV D.what₂.LL lam) = 0 := by
    refine GlobalTheory.ExportSeries.eq_zero_of_coefFn_id_eq_zero D n lam _ ?_
    intro x
    have hx := h x
    simp only [coefFn] at hx ⊢
    rw [eval₂Hom_map_hom] at *
    simpa using hx
  exact Formalism.L2.Col.extVV_ne_zero D.what₂.LL lam
    ((map_eq_zero_iff _ (MvPolynomial.map_injective _ D.what₂.embLL.injective)).mp hmap)

end GlobalTheory.CoeffNonvanish
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientPolynomialGLFunctionNeZeroStatement
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientPolynomial_GLFunction_ne_zero : ∀ {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n),
    ∃ (F : VV D.what₂.LL lam) (x : GLR D n), coefFn D.what₂.embLL lam (F : Pol D.what₂.LL D.what₂.Tau n) x ≠ 0 := by
  first | exact @GlobalTheory.CoeffNonvanish.exists_coefFn_ne_zero | exact GlobalTheory.CoeffNonvanish.exists_coefFn_ne_zero | (intros; apply GlobalTheory.CoeffNonvanish.exists_coefFn_ne_zero <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundleOfSmulClassEqAmpleAtAddNef
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundleOfSmulClassEqAmpleAtAddNef
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem isBig_of_smul_cls_eq_add_ampleAt : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → IsBig k N := by
  intro hnum k _ X _ q hq
  letI := algebraΓOfHom q
  intro N N₁ N₂ hN h₁ h₂ a x _ ha e hx hn₂
  have hf : ∀ r, algebraMap k Γ(X, ⊤) r = q.appTop ((Scheme.ΓSpecIso (.of k)).inv r) :=
    algebraΓOfHom_algebraMap q
  have hp : IsProjOver (strHom k (X := X)) := (strHom_eq hf) ▸ hq
  obtain ⟨m, A, s, hm, hA, hAmp, hxs⟩ := hx
  have hD := Semi.LB.isLB_div (isLB_lbPow h₁ m) hA
  have hsec : HasNonzeroSec (LB.div (lbPow N₁ m) A) := ⟨s, sec_ne_zero_of_mem hxs⟩
  have hB : IsBig k (tens (lbPow N₂ m) A) := (hn₂.pow hAmp m).isBig_tens_ample hnum hp hAmp
  have hP := isLB_lbPow hN (a * m)
  have e₂ : (a * m) • cls N hN = m • (cls N₁ h₁ + cls N₂ h₂) := by
    rw [← e, smul_smul, mul_comm a m]
  have hbig : IsBig k (lbPow N (a * m)) := hB.of_cls_eq_add hf hq hD hsec hP (by
    rw [cls_tens (isLB_lbPow h₂ m) hA, cls_div (isLB_lbPow h₁ m) hA hD, cls_lbPow hN, cls_lbPow h₂,
      cls_lbPow h₁, e₂]
    module)
  exact hbig.of_pow hN (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero ha.ne' hm.ne'))
    fun n => finite_coh_zero_twist_of_isProjOver hf hq (isLB_lbPow hN n)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBigLineBundleOfSmulClassEqAmpleAtAddNefStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBigLineBundle_of_smul_class_eq_ampleAt_add_nef : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N₁ N₂ : LB X) (hN : N.IsLB) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB) (a : ℕ) (x : X), IsNef k N → 0 < a → a • cls N hN = cls N₁ h₁ + cls N₂ h₂ → AmpleAt N₁ x → IsNef k N₂ → IsBig k N := by
  first | exact @GlobalTheory.isBig_of_smul_cls_eq_add_ampleAt | exact GlobalTheory.isBig_of_smul_cls_eq_add_ampleAt | (intros; apply GlobalTheory.isBig_of_smul_cls_eq_add_ampleAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineMultipleLeFamilyThreshold
namespace GlobalTheory.HodgeMultNum

theorem nat_bound (r f T : ℕ) (hr : 100 ≤ r) (hf : 5 ≤ f) (hT : 11 * (f * r.choose 2) ^ 2 ≤ T) :
    2 * r + 50 * r ^ 2 * (f * (r * r / 4)) + 2 ≤ T := by
  have hq : 4 * (r * r / 4) ≤ r * r := Nat.mul_div_le (r * r) 4
  have hc : 2 * r.choose 2 = r * (r - 1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 100 := ⟨r - 100, by omega⟩
  have h1 : s + 100 - 1 = s + 99 := by omega
  rw [h1] at hc
  set q := (s + 100) * (s + 100) / 4
  set c := (s + 100).choose 2
  have key : 4 * (2 * (s + 100) + 50 * (s + 100) ^ 2 * (f * q) + 2) ≤ 4 * (11 * (f * c) ^ 2) := by
    have e1 : 4 * (11 * (f * c) ^ 2) = 11 * f ^ 2 * ((s + 100) * (s + 99)) ^ 2 := by rw [← hc]; ring
    rw [e1]
    have e2 : 4 * (2 * (s + 100) + 50 * (s + 100) ^ 2 * (f * q) + 2) = 8 * (s + 100) + 8 + 50 * (s+100)^2 * f * (4 * q) := by ring
    rw [e2]
    have h3 : 50 * (s+100)^2 * f * (4 * q) ≤ 50 * (s+100)^2 * f * ((s+100)*(s+100)) := Nat.mul_le_mul_left _ hq
    have h4 : 8 * (s + 100) + 8 + 50 * (s+100)^2 * f * ((s+100)*(s+100)) ≤ 11 * f ^ 2 * ((s + 100) * (s + 99)) ^ 2 := by
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 5 := ⟨f - 5, by omega⟩
      ring_nf
      nlinarith [Nat.zero_le (s * g), Nat.zero_le (s * g ^ 2), Nat.zero_le (s ^ 2 * g), Nat.zero_le (s ^ 2 * g ^ 2),
        Nat.zero_le (s ^ 3 * g), Nat.zero_le (s ^ 3 * g ^ 2), Nat.zero_le (s ^ 4 * g), Nat.zero_le (s ^ 4 * g ^ 2),
        Nat.zero_le (s ^ 2), Nat.zero_le (s ^ 3), Nat.zero_le (s ^ 4), Nat.zero_le (g ^ 2)]
    omega
  omega

theorem five_le_of_pow (r f : ℕ) (hr : 100 ≤ r) (h : (r : ℝ) / 2 * (7 / 8 : ℝ) ^ f ≤ 1 / 16) : 5 ≤ f := by
  by_contra hf
  push_neg at hf
  have h1 : (7 / 8 : ℝ) ^ 4 ≤ (7 / 8 : ℝ) ^ f := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h2 : (100 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith [pow_pos (show (0:ℝ) < 7/8 by norm_num) f]

end GlobalTheory.HodgeMultNum

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn

theorem GlobalTheory.HodgeMultNum.hodgeMult_le_TO : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x →
    ∀ ι : Fm.Ix x, 2 * (Fm.D x ι).R.r + 50 * (Fm.D x ι).R.r ^ 2 * ((Fm.D x ι).R.f * ((Fm.D x ι).R.r * (Fm.D x ι).R.r / 4)) + 2 ≤
      (Fm.parT x hx ι).TO := by
  refine Closed.imp GlobalTheory.T.badShareSize_bounds_along_family fun Fm _ _ H => ?_
  obtain ⟨x0, H⟩ := H
  refine ⟨x0, fun x hx h0 ι => ?_⟩
  obtain ⟨hr, -, hE, hk⟩ := H x hx h0 ι
  obtain ⟨hg, hsum⟩ := hk 0
  set D := Fm.D x ι
  set g : ℝ := (D.host.g 0 : ℝ)
  have hg1 : (4096 : ℝ) ≤ g := by simp only [g]; exact_mod_cast hg
  have hlogg : 0 ≤ Real.log g := Real.log_nonneg (by linarith)
  have hr' : (100 : ℝ) ≤ (D.R.r : ℝ) := by exact_mod_cast hr
  have hlogr : 0 ≤ Real.log (D.R.r : ℝ) := Real.log_nonneg (by linarith)
  have hfpos : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  have hmpos : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hA : 0 ≤ 3 * (D.R.f : ℝ) / g := by positivity
  have hB : 0 ≤ 23 * (D.R.f : ℝ) * Real.log g / Real.sqrt g := by positivity
  have hC : 0 ≤ 2 * (D.R.f : ℝ) * (D.R.m : ℝ) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) +
      (1 + Real.log (D.R.r : ℝ)) / (g - 1)) := by
    have : 0 ≤ g - 1 := by linarith
    positivity
  have hE' : 0 ≤ Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ))) := (Real.exp_pos _).le
  have hP : (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f ≤ 1 / 16 := by linarith
  have hf := GlobalTheory.HodgeMultNum.five_le_of_pow _ _ hr hP
  have hT := (Fm.parT x hx ι).TO_11D2
  rw [(Fm.parT x hx ι).Dp_eq] at hT
  exact GlobalTheory.HodgeMultNum.nat_bound _ _ _ hr hf hT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSatEqOfIsCT
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ResW.SatWordAt

open GlobalTheory.LFun Formalism.UG

theorem esymm_add (A B : Multiset ℂ) (j : ℕ) :
    (A + B).esymm j = ∑ i ∈ Finset.HasAntidiagonal.antidiagonal j, A.esymm i.1 * B.esymm i.2 := by
  induction A using Multiset.induction_on generalizing j with
  | empty =>
    rw [zero_add, Finset.sum_eq_single (0, j)]
    · simp [Multiset.esymm]
    · rintro ⟨a, b⟩ hab hne
      have hab' : a + b = j := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
      obtain _ | a := a
      · exact absurd (by simp [← hab']) hne
      · rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simp)]
        simp
    · simp
  | cons a A ih =>
    have hrec : ∀ (s : Multiset ℂ) (k : ℕ), (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := fun s k => by
      simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]
    have h0 : ∀ s : Multiset ℂ, s.esymm 0 = 1 := fun s => by simp [Multiset.esymm]
    obtain _ | j := j
    · simp [h0]
    · rw [Multiset.cons_add, hrec, ih, ih, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
      simp only [hrec, h0, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, add_assoc]

theorem satEig_add {q r s N : ℕ} (hq : q ≠ 0) (h : r + s = N) {C B : Multiset ℂˣ} (hC : C.card = r) (hB : B.card = s) (j : ℕ) :
    satEig q N (C + B) j = ∑ i ∈ (Finset.range (r + 1) ×ˢ Finset.range (s + 1)).filter (fun i : ℕ × ℕ => i.1 + i.2 = j),
      (q : ℂ) ^ (((j : ℂ) * (N - j) - i.1 * (r - i.1) - i.2 * (s - i.2)) / 2) * (satEig q r C i.1 * satEig q s B i.2) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hz : ∀ (A : Multiset ℂˣ) (k : ℕ), A.card < k → (A.map fun b : ℂˣ => (b : ℂ)).esymm k = 0 := fun A k hk => by
    rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by simpa using hk)]
    simp
  rw [satEig, Multiset.map_add (f := _), esymm_add, Finset.mul_sum]
  symm
  refine Finset.sum_subset_zero_on_sdiff (fun i hi => ?_) (fun i hi => ?_) fun i hi => ?_
  · exact Finset.HasAntidiagonal.mem_antidiagonal.2 (Finset.mem_filter.1 hi).2
  · obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
    have h3 := Finset.HasAntidiagonal.mem_antidiagonal.1 h1
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, h3, and_true, not_and_or, not_lt] at h2
    rcases h2 with h2 | h2
    · rw [hz C _ (by omega)]; simp
    · rw [hz B _ (by omega)]; simp
  · simp only [satEig]
    have e : ((j : ℂ) * (N - j)) / 2 = ((j : ℂ) * (N - j) - i.1 * (r - i.1) - i.2 * (s - i.2)) / 2 +
      (i.1 * (r - i.1)) / 2 + (i.2 * (s - i.2)) / 2 := by ring
    rw [e, Complex.cpow_add _ _ hq', Complex.cpow_add _ _ hq']
    ring

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {v : HeightOneSpectrum (𝓞 E)} {N r s : ℕ}

section Lin

variable {m : ℕ} {u : List (Letter E)} {f : Vec u} {h : wsize u + m = N}

end Lin

variable {ϖ : v.adicCompletion E}


end GlobalTheory.ResW.SatWordAt

namespace GlobalTheory.ResW

end GlobalTheory.ResW

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatPIffMulVec
section -- merged from Development.AbelianVarietyTheory.Counterexamples.ThetaValuation.UniformMultiplier
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB

namespace GlobalTheory.ModelLatExamples

theorem eq_latP {r : ℕ} (D : D7) (Λ L : Submodule (𝓞 D.host.E) (Fin r → D.host.E))
    (h : Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ L, v = a • u}) : L = lattice₂ D Λ := by
  have h2 := lat_eq_span Formalism.IndefR.Fin.factPrincipalDatum Λ
  apply le_antisymm
  · exact GlobalTheory.ModelLatticeCheck.le_of_span_le _ (GlobalTheory.ModelLatticeCheck.AA_ne_zero D) _ _ (by rw [← h, ← h2])
  · exact GlobalTheory.ModelLatticeCheck.le_of_span_le _ (GlobalTheory.ModelLatticeCheck.AA_ne_zero D) _ _ (by rw [← h, ← h2])

end GlobalTheory.ModelLatExamples
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev uAt {D : D7} {J : CoreJ D} {G : Type} (r : TwoRuns J G) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Fin D.R.m) :=
  (r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀

end GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Build

theorem mem_localLattice_iff_mulVec {r : ℕ} (D : D7) {Λ Λ' : Submodule (𝓞 D.host.E) (Fin r → D.host.E)}
    (A : Matrix (Fin r) (Fin r) D.host.E) (h : ∀ w, w ∈ Λ ↔ A.mulVec w ∈ Λ') (w : Fin r → D.host.E) :
    w ∈ lattice₂ D Λ ↔ A.mulVec w ∈ lattice₂ D Λ' := by
  simp only [mem_latP]
  refine forall₂_congr fun a _ => ?_
  rw [h, Matrix.mulVec_smul]

theorem chi_one_of_toData {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Xd : DataX E r) (X : Data E r)
    (e : Xd.toData = X) (h : ∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) : ∀ la, ∀ γ ∈ Xd.Γ, Xd.χ la γ = 1 := by
  subst e
  exact h

theorem nonempty_place (D : D7) : Nonempty (HeightOneSpectrum (𝓞 D.what₂.LL)) := by
  obtain ⟨I, hb, ht⟩ := (Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top).1 (NumberField.RingOfIntegers.not_isField D.what₂.LL)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I ht.ne
  exact ⟨⟨P, hP.isPrime, fun e => hb.ne' (le_bot_iff.1 (e ▸ hIP))⟩⟩

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem exists_dataX_latP (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (i : Fin D.R.m)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (k : (uAt r v i).Comp) :
    ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (uAt r v i).X k ∧ Xx.L' = lattice₂ D ((uAt r v i).X k).Λ := by
  obtain ⟨X, ⟨h1, -, h3⟩, -⟩ := GlobalTheory.ModelLatticeCheck.holds_by_value D (r.used v).full.toCore (h.laws v).p.toLawsCore
    ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ (r.used v).full.σ₀ (r.used v).full.toCore.good_σ₀ k
  refine ⟨X, h1, ?_⟩
  rw [GlobalTheory.ModelLatExamples.eq_latP D X.Λ X.L' h3]
  show lattice₂ D X.toData.Λ = _
  rw [h1]

end Build

end GlobalTheory.ShareOn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNefBigOfClassEqSmulAddSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNefBigOfClassEqSmulAddSmul
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem nef_big_of_cls_eq_smul_add_smul : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (a b : ℕ), IsNef k N → IsBig k N → IsNef k N' → 0 < a → ∃ (N₀ : LB X) (h₀ : N₀.IsLB), cls N₀ h₀ = a • cls N hN + b • cls N' hN' ∧ IsNef k N₀ ∧ IsBig k N₀ := by
  intro hNN k _ X _ q hq
  letI := algebraΓOfHom q
  intro N N' hN hN' a b hNn hNb hN'n ha
  have hp : IsProjOver (strHom k (X := X)) := by
    rwa [strHom_eq (f := q) fun _ => rfl]
  obtain ⟨_, hH⟩ := exists_isAmpleLB_of_isProjOver hq
  refine ⟨tens (lbPow N a) (lbPow N' b), isLB_tens (isLB_lbPow hN a) (isLB_lbPow hN' b), ?_, ?_, ?_⟩
  · rw [cls_tens (isLB_lbPow hN a) (isLB_lbPow hN' b), cls_lbPow hN, cls_lbPow hN']
  · exact (hNn.pow hH a).tens (hN'n.pow hH b) hH
  · exact (hNb.pow (fun _ => rfl) hq ha).tens_nef hNN hp (hNn.pow hH a) (hN'n.pow hH b)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNefBigOfClassEqSmulAddSmulStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nef_big_of_class_eq_smul_add_smul : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (a b : ℕ), IsNef k N → IsBig k N → IsNef k N' → 0 < a → ∃ (N₀ : LB X) (h₀ : N₀.IsLB), cls N₀ h₀ = a • cls N hN + b • cls N' hN' ∧ IsNef k N₀ ∧ IsBig k N₀ := by
  first | exact @GlobalTheory.nef_big_of_cls_eq_smul_add_smul | exact GlobalTheory.nef_big_of_cls_eq_smul_add_smul | (intros; apply GlobalTheory.nef_big_of_cls_eq_smul_add_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspSectionLargeEvenScalarWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspSectionLargeEvenScalarWeight
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

theorem GlobalTheory.ScalarPoin.exists_cusp_ne_some : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), ∃ y ∈ X.dom, P y ≠ 0 := by
  intro E _ _ _ r X hp0 hpr hχ N
  obtain ⟨y, hy⟩ := GlobalTheory.FlagSecProbe.dom_nonempty X
  obtain ⟨n, hN, -, hev, P, hP, hPy⟩ := GlobalTheory.ScalarPoin.exists_cusp_ne E r X hp0 hpr hχ y hy N
  exact ⟨n, hN, hev, P, hP, y, hy, hPy⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspSectionLargeEvenScalarWeightStatement
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_cuspSection_large_evenScalarWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), ∃ y ∈ X.dom, P y ≠ 0 := by
  first | exact @GlobalTheory.ScalarPoin.exists_cusp_ne_some | exact GlobalTheory.ScalarPoin.exists_cusp_ne_some | (intros; apply GlobalTheory.ScalarPoin.exists_cusp_ne_some <;> assumption)
end
end
