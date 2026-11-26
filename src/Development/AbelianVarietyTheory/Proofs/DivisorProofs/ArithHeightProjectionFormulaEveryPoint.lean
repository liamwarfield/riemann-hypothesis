module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteFreeNbhd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSurjectiveOfOmegaMapSurjectiveConnected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultPullbackRationalSectionPushforward

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantRestrictionPointClosures
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantRestrictionPointClosures
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem clo_restrict_dominant : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X) (y : Y), ∃ g : clo y ⟶ clo (π y), g ≫ cloι (π y) = cloι y ≫ π ∧ g (genericPoint _) = genericPoint _ ∧ ∀ w : clo y, g.residueDegree w = π.residueDegree (cloι y w) := by
  intro X Y π y
  set i := cloι (π y)
  set j := cloι y
  have hi : i (genericPoint (clo (π y))) = π y := cloι_genericPoint _
  have hj : j (genericPoint (clo y)) = y := cloι_genericPoint _
  have hr : Set.range i = closure {π y} := by
    have h₁ := (genericPoint_spec (clo (π y))).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  have : Surjective (Limits.pullback.snd i (j ≫ π)) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr]
    refine Set.eq_univ_of_forall fun w => ?_
    have := ((genericPoint_specializes w).map (j ≫ π).continuous)
    rw [Set.mem_preimage]
    have e : (j ≫ π) (genericPoint (clo y)) = π y := by
      rw [Scheme.Hom.comp_apply, hj]
    rw [e] at this
    exact this.mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd i (j ≫ π))
  refine ⟨inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π), ?_, ?_, ?_⟩
  · rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]
  · apply i.isClosedEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc,
      Scheme.Hom.comp_apply, hj, hi]
  · intro w
    have e₁ := GlobalTheory.CurveDegreesCompare.residueDegree_comp (inv (Limits.pullback.snd i (j ≫ π)) ≫ Limits.pullback.fst i (j ≫ π)) i w
    have e₂ := GlobalTheory.CurveDegreesCompare.residueDegree_comp j π w
    rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc,
      GlobalTheory.Published.residueDegree_of_isClosedImmersion i, one_mul] at e₁
    rw [GlobalTheory.Published.residueDegree_of_isClosedImmersion j, mul_one] at e₂
    rw [← e₁, e₂]

end GlobalTheory.MixHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantRestrictionPointClosuresStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_restriction_pointClosures : ∀ (X Y : Scheme.{0}) (π : Y ⟶ X) (y : Y), ∃ g : clo y ⟶ clo (π y), g ≫ cloι (π y) = cloι y ≫ π ∧ g (genericPoint _) = genericPoint _ ∧ ∀ w : clo y, g.residueDegree w = π.residueDegree (cloι y w) := by
  first | exact @GlobalTheory.MixHt.clo_restrict_dominant | exact GlobalTheory.MixHt.clo_restrict_dominant | (intros; apply GlobalTheory.MixHt.clo_restrict_dominant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaInductiveStep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTopPowerPullbackSmallerDimEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTopPowerPullbackSmallerDimEqZero
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernLowDim

open MeasureTheory Set GlobalTheory.ChartGlue GlobalTheory.Points

theorem det_mul_mul_eq_zero {m n : ℕ} (hmn : m < n) (P : Matrix (Fin n) (Fin m) ℂ)
    (K : Matrix (Fin m) (Fin m) ℂ) (Q : Matrix (Fin m) (Fin n) ℂ) : (P * K * Q).det = 0 := by
  by_contra h
  have hu : IsUnit (P * K * Q) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 : (P * K * Q).rank ≤ m :=
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)).trans
      ((Matrix.rank_le_card_width P).trans (by simp))
  simp only [Fintype.card_fin] at h1
  omega

theorem chernPart_pull_of_lt : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (e e' : ℕ), IsArithVar p e → IsArithVar q e' → e < e' → ∀ (g : Y ⟶ X) (hg : g ≫ p = q), g (genericPoint Y) = genericPoint X → ∀ (N : HermLB p) (σ : k →+* ℂ) (ε : ℤˣ), ((N.pull g hg).φ σ).chernPart e' ε = 0 := by
  intro k _ X Y _ _ p q e e' hX hY hlt g hg hgen N σ ε
  obtain ⟨T, hT, hTg, hc⟩ := GlobalTheory.GenericChart.exists_isClosed_chart k X p e hX
  set Z : Set Y := (⇑g) ⁻¹' T with hZdef
  have hZ : IsClosed Z := hT.preimage g.continuous
  have hZg : genericPoint Y ∉ Z := by
    simp only [hZdef, mem_preimage, hgen]
    exact hTg
  set φ := (N.pull g hg).φ σ
  set A : Set (CxPts q σ) := {y | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} with hAdef
  have h0 : φ.chernPart e' ε A = 0 := GlobalTheory.ChernNull.chernPart_over_closed hY Z hZ hZg σ φ ε
  have hA : MeasurableSet A := by
    have : A = (ptsIn q σ ⟨Zᶜ, hZ.isOpen_compl⟩)ᶜ := by
      ext y
      simp [hAdef, mem_ptsIn]
    rw [this]
    exact (isOpen_ptsIn _).measurableSet.compl

  have hdens : ∀ (c : AlgChart q σ e') (y : CxPts q σ), y ∈ c.e.source → y ∉ A →
      c.chernDens φ y = 0 := by
    intro c y hys hyA
    have hy' : (PtsOver.map g hg (spMap σ) y).1 (IsLocalRing.closedPoint ℂ) ∉ T := by
      intro hT'
      exact hyA (show g (y.1 (IsLocalRing.closedPoint ℂ)) ∈ T from hT')
    obtain ⟨c', hc'⟩ := hc σ _ hy'
    obtain ⟨P, Q, hPQ⟩ := GlobalTheory.HessPull.hess_pull_factor k X Y p q g hg σ e' e c c' y hys hc'
    obtain ⟨K, hK⟩ := hPQ N (pick φ.isLB y) (mem_pick _ y)
    rw [AlgChart.chernDens, hK, det_mul_mul_eq_zero hlt, Complex.zero_re, mul_zero]
  have key : φ.chernPart e' ε ≤ (φ.chernPart e' ε).restrict A := iSup_le fun c => by
    have e0 : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) Aᶜ = 0 := by
      rw [chartMeas_apply _ _ hA.compl]
      have hm := measurableSet_image c.e (c.e.open_source.measurableSet.inter hA.compl)
        inter_subset_left
      rw [setLIntegral_congr_fun hm (g := fun _ => 0) ?_, lintegral_zero]
      rintro _ ⟨y, hy, rfl⟩
      simp only [c.e.left_inv hy.1, hdens c y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero]
    rw [← Measure.restrict_eq_self_of_ae_mem (s := A) (mem_ae_iff.2 e0)]
    exact Measure.restrict_mono le_rfl (le_iSup (fun c : AlgChart q σ e' =>
      chartMeas c.e fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ y)) c)
  refine Measure.measure_univ_eq_zero.1 (le_antisymm ((key univ).trans_eq ?_) zero_le)
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, h0]

end GlobalTheory.ChernLowDim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTopPowerPullbackSmallerDimEqZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernForm_topPower_pullback_smaller_dim_eq_zero : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (e e' : ℕ), IsArithVar p e → IsArithVar q e' → e < e' → ∀ (g : Y ⟶ X) (hg : g ≫ p = q), g (genericPoint Y) = genericPoint X → ∀ (N : HermLB p) (σ : k →+* ℂ) (ε : ℤˣ), ((N.pull g hg).φ σ).chernPart e' ε = 0 := by
  first | exact @GlobalTheory.ChernLowDim.chernPart_pull_of_lt | exact GlobalTheory.ChernLowDim.chernPart_pull_of_lt | (intros; apply GlobalTheory.ChernLowDim.chernPart_pull_of_lt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaInductiveStep
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

open GlobalTheory.TwistTop

namespace GlobalTheory.ProjStep

theorem archInt_refines {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {N L : HermLB p} {ρ : N.B.ι → L.B.ι} (h : Refines N L ρ 0) {r : L.B.ι → X.functionFieldˣ}
    (hr : IsRatSec L.B r) (e : ℕ) :
    N.archInt N e (h.isRatSec hr) = L.archInt L e hr := by
  unfold HermLB.archInt
  rw [h.div hr]
  refine finsum_congr fun σ => ?_
  rw [h.chernInt]
  exact Weight.chernInt_congr (isOpen_offSupp _).measurableSet fun y hy => h.logNorm hr hy

end GlobalTheory.ProjStep

namespace GlobalTheory.ProjStep

theorem main : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ (y : Y) (e : ℕ), CharZero Γ(clo y, ⊤) → HasDim y (e + 1 + 1) → (∀ w : Y, HasDim w (e + 1) → h' w = (π.residueDegree w : ℝ) * h (π w)) → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' H H' y e hc hy hrec
  have hAX : IsAmb p := isAmb_of_isArithVar hX
  have hAY : IsAmb q := isAmb_of_isArithVar hY
  have := hX.isNoetherian
  have := hY.isNoetherian
  obtain ⟨hbdX, -, -, -, hsubX, hgenX⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hAX
  obtain ⟨-, -, -, -, hsubY, hgenY⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hAY
  obtain ⟨g, hgc, hgη, hgdeg⟩ := GlobalTheory.T.exists_dominant_restriction_pointClosures X Y π y

  have hdW : topologicalKrullDim (clo y) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    refine (hgenY (clo y) (e + 1 + 1)).1 ((hsubY (clo y) (cloι y) _ _).1 ?_)
    rw [cloι_genericPoint]; exact hy
  have hcZ : CharZero Γ(clo (π y), ⊤) := g.appTop.hom.charZero
  have hg1 : g ≫ cloι (π y) ≫ p = cloι y ≫ q := by
    rw [← Category.assoc, hgc, Category.assoc, hπ]
  have hC : (g ≫ cloι (π y)) ≫ p = cloι y ≫ q := by rw [Category.assoc]; exact hg1
  have hη' : g (genericPoint (clo y)) ⤳ genericPoint (clo (π y)) := hgη ▸ specializes_rfl
  have happ (w : clo y) : π (cloι y w) = cloι (π y) (g w) := by
    have := congrArg (fun f : clo y ⟶ X => f w) hgc
    simpa using this.symm
  have hδ : g.residueDegree (genericPoint (clo y)) = π.residueDegree y := by
    rw [hgdeg, cloι_genericPoint]

  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr (cloι (π y))).isLB
  have hr1 := MultPull.isRatSec_pull_map g hη' hr
  have ref1 : Refines (L.pull (g ≫ cloι (π y)) hC)
      ((L.restr (cloι (π y))).pull g hg1) (fun c _ => c) 0 := by
    refine { le := ?_, g := ?_, φ := ?_ }
    · intro c z hz
      exact Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hz a
    · intro W s z c c' hc hc'
      have h₁ : (s ≫ g) z ∈ (L.B.pull (cloι (π y))).U c := Set.mem_iInter.2 fun a => Set.mem_iInter.1 hc a
      have h₂ : (s ≫ g) z ∈ (L.B.pull (cloι (π y))).U c' := Set.mem_iInter.2 fun a => Set.mem_iInter.1 hc' a
      have h₃ : s z ∈ ((L.B.pull (cloι (π y))).pull g).U (fun _ => c) := Set.mem_iInter.2 fun _ => h₁
      have h₄ : s z ∈ ((L.B.pull (cloι (π y))).pull g).U (fun _ => c') := Set.mem_iInter.2 fun _ => h₂
      have e₁ := gm_pull_g (L.B.pull (cloι (π y))) g s z (fun _ => c) (fun _ => c') h₃ h₄
      have e₂ := gm_pull_g L.B (cloι (π y)) (s ≫ g) z c c' h₁ h₂
      have e₃ := gm_pull_g L.B (g ≫ cloι (π y)) s z c c' hc hc'
      rw [← Category.assoc] at e₃
      exact e₃.trans (e₁.trans e₂).symm
    · intro σ c z hz
      refine ((L.φ σ).pull_φ (g ≫ cloι (π y)) hC c z).trans (Eq.symm ((add_zero _).trans ?_))
      refine (((L.restr (cloι (π y))).φ σ).pull_φ g hg1 (fun _ => c) z).trans (((L.φ σ).pull_φ (cloι (π y)) rfl _ _).trans ?_)
      exact congrArg _ (Subtype.ext (Category.assoc _ _ _))
  have hrC := ref1.isRatSec hr1
  obtain ⟨ρ, ref2⟩ : ∃ ρ, Refines ((L.pull π hπ).restr (cloι y)) (L.pull (g ≫ cloι (π y)) hC) ρ 0 := by
    have key : ∀ (f : clo y ⟶ X) (hf : f ≫ p = cloι y ≫ q), f = cloι y ≫ π →
        ∃ ρ, Refines ((L.pull π hπ).restr (cloι y)) (L.pull f hf) ρ 0 := by
      rintro f hf rfl
      refine ⟨fun c => c PUnit.unit, { le := ?_, g := ?_, φ := ?_ }⟩
      · intro c z hz
        exact Set.mem_iInter.2 fun a => Set.mem_iInter.1 (Set.mem_iInter.1 hz PUnit.unit) a
      · intro W s z c c' hc hc'
        have h₁ := Set.mem_iInter.1 hc PUnit.unit
        have h₂ := Set.mem_iInter.1 hc' PUnit.unit
        refine (gm_pull_g _ (cloι y) s z c c' hc hc').trans ((gm_pull_g _ π (s ≫ cloι y) z _ _ h₁ h₂).trans ?_)
        refine Eq.trans ?_ (gm_pull_g _ (cloι y ≫ π) s z (c PUnit.unit) (c' PUnit.unit)
          (Set.mem_iInter.2 fun a => Set.mem_iInter.1 h₁ a) (Set.mem_iInter.2 fun a => Set.mem_iInter.1 h₂ a)).symm
        rw [Category.assoc]
      · intro σ c z hz
        refine (((L.pull π hπ).φ σ).pull_φ (cloι y) rfl c z).trans (((L.φ σ).pull_φ π hπ _ _).trans ?_)
        refine Eq.trans ?_ (((L.φ σ).pull_φ (cloι y ≫ π) hf (c PUnit.unit) z).symm.trans (add_zero _).symm)
        exact congrArg _ (Subtype.ext (Category.assoc _ _ _))
    exact key _ hC hgc
  have hrA := ref2.isRatSec hrC
  obtain ⟨-, hrecW⟩ := H'.recursion_one (cloι y) hc (by omega : 1 ≤ e + 1) hdW hrA
  rw [cloι_genericPoint] at hrecW
  have ediv : ((L.pull π hπ).restr (cloι y)).div hrA = (((L.restr (cloι (π y))).pull g hg1)).div hr1 :=
    (ref2.div hrC).trans (ref1.div hr1)
  have earch : ((L.pull π hπ).restr (cloι y)).archInt ((L.pull π hπ).restr (cloι y)) (e + 1) hrA =
      ((L.restr (cloι (π y))).pull g hg1).archInt ((L.restr (cloι (π y))).pull g hg1) (e + 1) hr1 :=
    (archInt_refines ref2 hrC (e + 1)).trans (archInt_refines ref1 hr1 (e + 1))
  have hsum : ∑ᶠ w, ((((L.pull π hπ).restr (cloι y)).div hrA).mult w : ℝ) * h' (cloι y w) =
      (π.residueDegree y : ℝ) * ∑ᶠ z, (((L.restr (cloι (π y))).div hr).mult z : ℝ) * h (cloι (π y) z) := by
    rw [ediv, ← hδ]
    refine Eq.trans (finsum_congr fun w => ?_) (GlobalTheory.T.finsum_mult_pullback_rationalSection_pushforward k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q)
      (hAX.sub _) (hAY.sub _) g hg1 hgη (L.restr (cloι (π y))).B (L.restr (cloι (π y))).isLB r hr
      (fun z => h (cloι (π y) z)))
    by_cases hm : ((((L.restr (cloι (π y))).pull g hg1)).div hr1).mult w = 0
    · have hm' : ((((L.restr (cloι (π y))).pull g hg1)).div hr1).mult w = 0 := hm
      rw [hm, Int.cast_zero, zero_mul]
      exact (mul_eq_zero_of_left (Int.cast_eq_zero.2 hm) _).symm
    · have hco := CartierDiv.coheight_eq_one_of_mult_ne_zero hm
      have hd1 := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k (clo y) (cloι y ≫ q) (hAY.sub _) (e + 1) hdW).1 w).1 hco
      have hd2 := (hsubY (clo y) (cloι y) w (e + 1)).2 hd1
      rw [hrec _ hd2, happ, hgdeg]
      rfl

  obtain ⟨m, hm⟩ := hbdX
  obtain ⟨d', -, hd'⟩ := hm (π y)
  obtain ⟨hle, hiff⟩ := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hAX hAY π hπ y (e + 1 + 1) d' hy hd'
  have hdZ : topologicalKrullDim (clo (π y)) = (d' : WithBot ℕ∞) := by
    refine (hgenX (clo (π y)) d').1 ((hsubX (clo (π y)) (cloι (π y)) _ _).1 ?_)
    rw [cloι_genericPoint]; exact hd'
  have hWv := hY.of_isClosedImmersion (cloι y) hc hdW
  rw [hsum, earch] at hrecW
  by_cases h0 : π.residueDegree y = 0
  ·
    have hlt : d' < e + 1 + 1 := lt_of_le_of_ne hle fun h1 => hiff.2 h1.symm h0
    have hd0 : d' ≠ 0 := fun h2 => hX.dim_ne_zero (cloι (π y)) hcZ (by rw [hdZ, h2]; rfl)
    obtain ⟨e0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd0
    have hZv0 := hX.of_isClosedImmersion (cloι (π y)) hcZ (e := e0) hdZ
    have hzero (σ : k →+* ℂ) (ε : ℤˣ) :
        (((L.restr (cloι (π y))).pull g hg1).φ σ).chernPart (e + 1) ε = 0 :=
      GlobalTheory.T.chernForm_topPower_pullback_smaller_dim_eq_zero k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) e0 (e + 1) hZv0 hWv (by omega) g hg1 hgη
        (L.restr (cloι (π y))) σ ε
    have harch0 : ((L.restr (cloι (π y))).pull g hg1).archInt ((L.restr (cloι (π y))).pull g hg1) (e + 1) hr1 = 0 := by
      unfold HermLB.archInt Weight.chernInt
      simp [hzero]
    rw [harch0, h0] at hrecW
    rw [hrecW, h0]
    simp
  ·
    have hde : d' = e + 1 + 1 := (hiff.1 h0).symm
    subst hde
    have hZv := hX.of_isClosedImmersion (cloι (π y)) hcZ hdZ
    obtain ⟨-, hrecZ⟩ := H.recursion_one (cloι (π y)) hcZ (by omega : 1 ≤ e + 1) hdZ hr
    rw [cloι_genericPoint] at hrecZ
    have hpa := GlobalTheory.T.archimedeanIntegral_pull_mul_degree k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) (e + 1) hZv hWv g hg1 hgη
      (hδ ▸ h0) (L.restr (cloι (π y))) (L.restr (cloι (π y))) r hr
    rw [hδ] at hpa
    rw [hrecW, hpa, hrecZ]
    ring

end GlobalTheory.ProjStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaInductiveStepStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHeight_projectionFormula_inductiveStep : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ (y : Y) (e : ℕ), CharZero Γ(clo y, ⊤) → HasDim y (e + 1 + 1) → (∀ w : Y, HasDim w (e + 1) → h' w = (π.residueDegree w : ℝ) * h (π w)) → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  first | exact @GlobalTheory.ProjStep.main | exact GlobalTheory.ProjStep.main | (intros; apply GlobalTheory.ProjStep.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaPointCurve
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaPointCurve
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.ProjCurve

section SlopeTestRemainingChoices

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}


open GlobalTheory.TwistTop in
theorem refines_trans {N L M : HermLB p} {π : N.B.ι → L.B.ι} {π' : L.B.ι → M.B.ι}
    (h : Refines N L π 0) (h' : Refines L M π' 0) : Refines N M (fun c => π' (π c)) 0 := by
  refine ⟨fun c => (h.le c).trans (h'.le _), ?_, ?_⟩
  · intro Z r z c c' hc hc'
    exact (h.g Z r z c c' hc hc').trans (h'.g Z r z _ _ (h.le _ hc) (h.le _ hc'))
  · intro σ c y hy
    rw [h.φ σ c y hy, h'.φ σ _ y (ptsIn_mono (h.le _) hy)]
    simp


open GlobalTheory.TwistTop in
theorem exists_refines_of_eq {N L L' : HermLB p} {π : N.B.ι → L.B.ι} (h : Refines N L π 0) (e : L = L') :
    ∃ π' : N.B.ι → L'.B.ι, Refines N L' π' 0 := by
  subst e
  exact ⟨π, h⟩

theorem pull_congr (L : HermLB p) {q : Y ⟶ Sp k} {f f' : Y ⟶ X} (e : f = f') (hf : f ≫ p = q)
    (hf' : f' ≫ p = q) : L.pull f hf = L.pull f' hf' := by
  subst e
  rfl

theorem isClosed_of_ne_generic {Z : Scheme.{0}} [IsIntegral Z] (hd : topologicalKrullDim Z = 1) {z : Z}
    (hz : z ≠ genericPoint Z) : IsClosed ({z} : Set Z) := by
  rcases Order.krullDim_le_one_iff.1 (show Order.krullDim (IrreducibleCloseds Z) ≤ 1 from hd.le)
    ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ with h | h
  · refine isClosed_of_closure_subset fun w hw => ?_
    have h₁ : (⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds Z) ≤
        ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
      closure_minimal (Set.singleton_subset_iff.2 hw) isClosed_closure
    have h₂ : z ∈ closure {w} := h h₁ (subset_closure rfl)
    exact ((specializes_iff_mem_closure.2 h₂).antisymm (specializes_iff_mem_closure.2 hw)).eq
  · exact absurd (IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@h
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩ (Set.subset_univ _)))
      (genericPoint_spec Z)) hz

theorem log_card_residueField {W Z : Scheme.{0}} (g : W ⟶ Z) (w : W) [Finite (W.residueField w)] :
    Real.log (Nat.card (W.residueField w)) =
      (g.residueDegree w : ℝ) * Real.log (Nat.card (Z.residueField (g w))) := by
  letI := (g.residueFieldMap w).hom.toAlgebra
  have : Finite (Z.residueField (g w)) := Finite.of_injective _ (g.residueFieldMap w).hom.injective
  have : Module.Finite (Z.residueField (g w)) (W.residueField w) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := Z.residueField (g w)) (V := W.residueField w), Nat.cast_pow,
    Real.log_pow]
  rfl

end SlopeTestRemainingChoices


open GlobalTheory.TwistTop in
theorem main : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ),
    IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, CharZero Γ(clo y, ⊤) → HasDim y 1 →
    h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' H H' y hc hy
  have hAX := isAmb_of_isArithVar hX
  have hAY := isAmb_of_isArithVar hY
  have := hAX.isNoetherian
  have := hAY.isNoetherian
  obtain ⟨g, hgc, hgη, hgdeg⟩ := GlobalTheory.T.exists_dominant_restriction_pointClosures X Y π y
  have D₁ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hAY
  have D₂ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hAX

  have hdW : topologicalKrullDim (clo y) = 1 := by
    have h₁ := (D₁.2.2.2.2.1 (clo y) (cloι y) (genericPoint (clo y)) 1).1 (by rw [cloι_genericPoint]; exact hy)
    have h₂ := (D₁.2.2.2.2.2 (clo y) 1).1 h₁
    rw [h₂]
    rfl

  have hcZ : CharZero Γ(clo (π y), ⊤) := g.appTop.hom.charZero

  obtain ⟨m, hm⟩ := D₂.1
  obtain ⟨d', -, hd'⟩ := hm (π y)
  have hdZ' : topologicalKrullDim (clo (π y)) = d' :=
    (D₂.2.2.2.2.2 (clo (π y)) d').1 ((D₂.2.2.2.2.1 (clo (π y)) (cloι (π y)) _ d').1
      (by rw [cloι_genericPoint]; exact hd'))
  obtain ⟨hle, hiff⟩ := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q hAX hAY π hπ y 1 d' hy hd'
  have hd1 : d' = 1 := by
    have h0 : d' ≠ 0 := by
      rintro rfl
      exact hX.dim_ne_zero (cloι (π y)) hcZ (hdZ'.trans (by rfl))
    omega
  subst hd1
  have hdZ : topologicalKrullDim (clo (π y)) = 1 := hdZ'.trans (by rfl)
  have hdeg : π.residueDegree y ≠ 0 := hiff.2 rfl
  have hdegη : g.residueDegree (genericPoint (clo y)) = π.residueDegree y := by
    rw [hgdeg, cloι_genericPoint]
  have hW : IsArithVar (cloι y ≫ q) 0 := hY.of_isClosedImmersion (cloι y) hc hdW
  have hZ : IsArithVar (cloι (π y) ≫ p) 0 := hX.of_isClosedImmersion (cloι (π y)) hcZ hdZ

  obtain ⟨r, hr⟩ := exists_isRatSec (L.restr (cloι (π y))).isLB
  have hg' : g ≫ cloι (π y) ≫ p = cloι y ≫ q := by
    rw [← Category.assoc, hgc, Category.assoc, hπ]
  have hr' := MultPull.isRatSec_pull_map g (hgη ▸ specializes_rfl : g (genericPoint (clo y)) ⤳ genericPoint _) hr

  have h₁ : (cloι y ≫ π) ≫ p = cloι y ≫ q := by rw [Category.assoc, hπ]
  have h₂ : (g ≫ cloι (π y)) ≫ p = cloι y ≫ q := by rw [hgc, h₁]
  obtain ⟨ρ, hρ⟩ := exists_refines_of_eq (L.refines_pull_pull π hπ (cloι y) rfl h₁)
    (pull_congr L hgc.symm h₁ h₂)
  have hρ' := refines_trans hρ (L.refines_pull_comp (cloι (π y)) rfl g hg' h₂)

  have e₁ := H'.point (clo y) (cloι y) hc hdW _ (hρ'.isRatSec hr')
  rw [cloι_genericPoint] at e₁
  have e₂ : ((L.pull π hπ).restr (cloι y)).curveDeg (hρ'.isRatSec hr') =
      ((L.restr (cloι (π y))).pull g hg').curveDeg hr' := by
    unfold HermLB.curveDeg
    rw [hρ'.div hr']
    refine congrArg _ (finsum_congr fun σ => finsum_congr fun z => hρ'.logNorm hr' (mem_offSupp.2 ?_))
    rw [under_eq_genericPoint hW z]
    exact CartierDiv.genericPoint_notMem_supp _

  have e₃ := H.point (clo (π y)) (cloι (π y)) hcZ hdZ r hr
  rw [cloι_genericPoint] at e₃

  have a₁ := GlobalTheory.ArchDimZero.main k (clo y) (cloι y ≫ q) hW ((L.restr (cloι (π y))).pull g hg')
    ((L.restr (cloι (π y))).pull g hg') _ hr'
  have a₂ := GlobalTheory.T.archimedeanIntegral_pull_mul_degree k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) 0 hZ hW g hg' hgη
    (hdegη ▸ hdeg) (L.restr (cloι (π y))) (L.restr (cloι (π y))) r hr
  have a₃ := GlobalTheory.ArchDimZero.main k (clo (π y)) (cloι (π y) ≫ p) hZ (L.restr (cloι (π y)))
    (L.restr (cloι (π y))) r hr

  have f₁ := GlobalTheory.T.finsum_mult_pullback_rationalSection_pushforward k (clo (π y)) (clo y) (cloι (π y) ≫ p) (cloι y ≫ q) (hAX.sub _) (hAY.sub _) g hg' hgη
    (L.restr (cloι (π y))).B (L.restr (cloι (π y))).isLB r hr (fun z => Real.log (Nat.card ((clo (π y)).residueField z)))
  have f₂ : ∑ᶠ w, ((((L.restr (cloι (π y))).pull g hg').div hr').mult w : ℝ) *
      Real.log (Nat.card ((clo y).residueField w)) =
      ∑ᶠ w, ((((L.restr (cloι (π y))).pull g hg').div hr').mult w : ℝ) *
      ((g.residueDegree w : ℝ) * Real.log (Nat.card ((clo (π y)).residueField (g w)))) := by
    refine finsum_congr fun w => ?_
    by_cases hw : (((L.restr (cloι (π y))).pull g hg').div hr').mult w = 0
    · rw [hw, Int.cast_zero, zero_mul, zero_mul]
    have hne : w ≠ genericPoint (clo y) := fun e =>
      CartierDiv.genericPoint_notMem_supp _ (e ▸ CartierDiv.mem_supp_of_mult_ne_zero hw)
    have := hW.finite_residueField (isClosed_of_ne_generic hdW hne)
    rw [log_card_residueField g w]
  rw [e₁, e₂, e₃]
  unfold HermLB.curveDeg
  rw [← a₁, ← a₃, f₂]
  rw [hdegη] at f₁ a₂
  rw [a₂]
  erw [f₁]
  ring

end GlobalTheory.ProjCurve
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaPointCurveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHeight_projectionFormula_pointCurve : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, CharZero Γ(clo y, ⊤) → HasDim y 1 → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  first | exact @GlobalTheory.ProjCurve.main | exact GlobalTheory.ProjCurve.main | (intros; apply GlobalTheory.ProjCurve.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightPullbackResidueDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightPullbackResidueDegree
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjFormulaVert


set_option maxHeartbeats 1000000 in
theorem exists_affine_finite_free (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (hX : IsProjOver p) (hY : IsProjOver q) (π : Y ⟶ X) (hπ : π ≫ p = q)
    (hg : π (genericPoint Y) = genericPoint X) (hδ : π.residueDegree (genericPoint Y) ≠ 0) :
    ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧
      (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧
        Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  have hqP : IsProper q := by
    obtain ⟨N, j, _, hj⟩ := hY
    have := isProper_str k N
    exact hj ▸ inferInstance
  have : IsSeparated (π ≫ p) := hπ ▸ (inferInstance : IsSeparated q)
  have hsep : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType (π ≫ p) := hπ ▸ (inferInstance : LocallyOfFiniteType q)
  have hlft : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  have : IsLocallyNoetherian X := by
    obtain ⟨N, j, _, hj⟩ := hX
    have : LocallyOfFiniteType p := hj ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U₀, hU₀, hxU₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X))
  have hyU₀ : genericPoint Y ∈ π ⁻¹ᵁ U₀ := by
    show π (genericPoint Y) ∈ U₀
    rw [hg]; exact hxU₀
  obtain ⟨V₀, hV₀, hyV₀, hVle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hyU₀
  haveI : Nonempty U₀ := ⟨⟨_, hxU₀⟩⟩
  haveI : Nonempty V₀ := ⟨⟨_, hyV₀⟩⟩
  letI : Algebra Γ(X, U₀) Γ(Y, V₀) := (π.appLE U₀ V₀ hVle).hom.toAlgebra
  haveI : IsNoetherianRing Γ(X, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  haveI : FaithfulSMul Γ(X, U₀) Γ(Y, V₀) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (GlobalTheory.appLE_injective_of_genericPoint_map π hg ⟨_, hyV₀⟩ hVle)
  haveI : Algebra.FiniteType Γ(X, U₀) Γ(Y, V₀) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType π hlft ⟨U₀, hU₀⟩ ⟨V₀, hV₀⟩ hVle
  haveI : Algebra.IsAlgebraic Γ(X, U₀) Γ(Y, V₀) := GlobalTheory.GenDegAlg.isAlgebraic_appLE π hg hδ hU₀ ⟨_, hyV₀⟩ hVle
  obtain ⟨a₁, ha₁, H₁⟩ := GlobalTheory.finite_away_of_isAlgebraic_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  obtain ⟨a₂, ha₂, H₂⟩ := GlobalTheory.free_away_mul_of_finiteType (A := Γ(X, U₀)) (B := Γ(Y, V₀))
  have ha : a₁ * a₂ ≠ 0 := mul_ne_zero ha₁ ha₂
  have hUU₀ : X.basicOpen (a₁ * a₂) ≤ U₀ := X.basicOpen_le _
  have hUa : IsAffineOpen (X.basicOpen (a₁ * a₂)) := hU₀.basicOpen _
  have hxU : genericPoint X ∈ X.basicOpen (a₁ * a₂) := by
    have hne : X.basicOpen (a₁ * a₂) ≠ ⊥ := fun h => ha ((basicOpen_eq_bot_iff _).1 h)
    obtain ⟨z, hz⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
    exact ((genericPoint_spec X).mem_open_set_iff (X.basicOpen (a₁ * a₂)).isOpen).2
      ⟨z, trivial, hz⟩
  set U : X.Opens := X.basicOpen (a₁ * a₂) with hU_def
  set V : Y.Opens := Y.basicOpen (π.appLE U₀ V₀ hVle (a₁ * a₂)) with hV_def
  have hVV₀ : V ≤ V₀ := Y.basicOpen_le _
  have hVe : V = V₀ ⊓ π ⁻¹ᵁ U := Scheme.basicOpen_appLE π V₀ U₀ hVle _
  have hVU : V ≤ π ⁻¹ᵁ U := by rw [hVe]; exact inf_le_right
  have hVa : IsAffineOpen V := hV₀.basicOpen _
  have hyV : genericPoint Y ∈ V := by
    rw [hVe]; exact ⟨hyV₀, show π (genericPoint Y) ∈ U from hg ▸ hxU⟩
  letI iA : Algebra Γ(X, U₀) Γ(X, U) := (X.presheaf.map (homOfLE hUU₀).op).hom.toAlgebra
  letI iB : Algebra Γ(Y, V₀) Γ(Y, V) := (Y.presheaf.map (homOfLE hVV₀).op).hom.toAlgebra
  letI iAB : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V hVU).hom.toAlgebra
  letI iAB' : Algebra Γ(X, U₀) Γ(Y, V) := (π.appLE U₀ V (hVV₀.trans hVle)).hom.toAlgebra
  haveI : IsScalarTower Γ(X, U₀) Γ(X, U) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.map_appLE hVU (homOfLE hUU₀).op).symm)
  haveI : IsScalarTower Γ(X, U₀) Γ(Y, V₀) Γ(Y, V) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (π.appLE_map hVle (homOfLE hVV₀).op).symm)
  haveI hlA : IsLocalization.Away (a₁ * a₂) Γ(X, U) :=
    hU₀.isLocalization_of_eq_basicOpen _ (homOfLE hUU₀) rfl
  haveI hlB : IsLocalization.Away (algebraMap Γ(X, U₀) Γ(Y, V₀) (a₁ * a₂)) Γ(Y, V) :=
    hV₀.isLocalization_of_eq_basicOpen _ (homOfLE hVV₀) rfl
  have e2 : a₂ * a₁ = a₁ * a₂ := mul_comm _ _
  have hfin : Module.Finite Γ(X, U) Γ(Y, V) := H₁ a₂ Γ(X, U) Γ(Y, V) hlA hlB
  have hfree : Module.Free Γ(X, U) Γ(Y, V) :=
    H₂ a₁ Γ(X, U) Γ(Y, V) (by rw [e2]; exact hlA) (by rw [e2]; exact hlB)
  have hpre : π ⁻¹ᵁ U = V := GlobalTheory.preimage_eq_of_finite_appLE π hUa hVa ⟨_, hyV⟩ hVU hfin
  have key : ∀ (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ U), W = π ⁻¹ᵁ U →
      (letI := (π.appLE U W hW).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, W) ∧ Module.Finite Γ(X, U) Γ(Y, W)) →
      (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.Finite Γ(X, U) Γ(Y, π ⁻¹ᵁ U)) := by
    rintro W hW rfl h
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  obtain ⟨h1, h2⟩ := key V hVU hpre.symm ⟨hfree, hfin⟩
  exact ⟨U, hUa, hxU, hpre ▸ hVa, h1, h2,
    GlobalTheory.GenFinEtField.finrank_app_eq_residueDegree π hg hUa (hpre ▸ hVa) hxU⟩

end GlobalTheory.ProjFormulaVert

namespace GlobalTheory.ProjFormulaVert

theorem algebra_zmod_eq {l : ℕ} {R : Type} [CommRing R] (a b : Algebra (ZMod l) R) : a = b :=
  Algebra.algebra_ext a b fun r => congrFun (congrArg DFunLike.coe
    (RingHom.ext_zmod (@algebraMap _ _ _ _ a) (@algebraMap _ _ _ _ b))) r

theorem height_pull_vertical : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ),
    IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ (y : Y) (l : ℕ) [Fact l.Prime],
    Nonempty (Algebra (ZMod l) Γ(clo y, ⊤)) → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' hh hh' y l _ ⟨instW⟩
  obtain ⟨g, hgc, hgen, hgdeg⟩ := GlobalTheory.T.exists_dominant_restriction_pointClosures X Y π y
  have hδ : g.residueDegree (genericPoint (clo y)) = π.residueDegree y := by
    rw [hgdeg, cloι_genericPoint]

  have hinj : Function.Injective g.appTop.hom := by
    have := GlobalTheory.appLE_injective_of_genericPoint_map g hgen (U := ⊤) (V := g ⁻¹ᵁ ⊤)
      ⟨genericPoint (clo y), trivial⟩ le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at this
  haveI : Nonempty (⊤ : (clo y).Opens) := ⟨⟨genericPoint (clo y), trivial⟩⟩
  haveI : CharP Γ(clo y, ⊤) l :=
    charP_of_injective_algebraMap (algebraMap (ZMod l) Γ(clo y, ⊤)).injective l
  haveI : CharP Γ(clo (π y), ⊤) l := ⟨fun n => by
    rw [← CharP.cast_eq_zero_iff Γ(clo y, ⊤) l n, ← map_natCast g.appTop.hom n,
      map_eq_zero_iff _ hinj]⟩
  letI instZ : Algebra (ZMod l) Γ(clo (π y), ⊤) := ZMod.algebra _ l
  have hWp : IsProjOver (strHom (ZMod l) (X := (clo y))) :=
    GlobalTheory.FibreProj.isProjOver_closed_fibre k Y q E hY (clo y) (cloι y) l
  have hZp : IsProjOver (strHom (ZMod l) (X := (clo (π y)))) :=
    GlobalTheory.FibreProj.isProjOver_closed_fibre k X p D hX (clo (π y)) (cloι (π y)) l
  have hgs : g ≫ strHom (ZMod l) (clo (π y)) = strHom (ZMod l) (clo y) :=
    comp_strHom fun r => congrFun (congrArg DFunLike.coe
      (RingHom.ext_zmod (g.appTop.hom.comp (algebraMap (ZMod l) _)) (algebraMap (ZMod l) _))) r

  obtain ⟨⟨m, hm⟩, -, -, -, hcl, hgd⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q (isAmb_of_isArithVar hY)
  obtain ⟨⟨m', hm'⟩, -, -, -, hcl', hgd'⟩ := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p (isAmb_of_isArithVar hX)
  obtain ⟨d, -, hd⟩ := hm y
  obtain ⟨d', -, hd'⟩ := hm' (π y)
  have hWd : topologicalKrullDim (clo y) = d :=
    (hgd (clo y) d).1 ((hcl (clo y) (cloι y) _ d).1 (by rw [cloι_genericPoint]; exact hd))
  have hZd : topologicalKrullDim (clo (π y)) = d' :=
    (hgd' (clo (π y)) d').1 ((hcl' (clo (π y)) (cloι (π y)) _ d').1 (by rw [cloι_genericPoint]; exact hd'))
  obtain ⟨hle, hiff⟩ := GlobalTheory.T.pointClosureDim_le_and_residueDegree_ne_zero_iff k X Y p q (isAmb_of_isArithVar hX) (isAmb_of_isArithVar hY) π hπ y d d' hd hd'

  have e1 := hh'.vertical (clo y) (cloι y) (ZMod l) d hWd
  have e2 := hh.vertical (clo (π y)) (cloι (π y)) (ZMod l) d' hZd
  rw [cloι_genericPoint] at e1 e2
  have ej : (cloι y ≫ π) ≫ p = cloι y ≫ q := by rw [Category.assoc, hπ]
  have ei : (g ≫ cloι (π y)) ≫ p = g ≫ cloι (π y) ≫ p := Category.assoc _ _ _
  have t1 : topSelfIntersection (ZMod l) ((L.pull π hπ).B.pull (cloι y)) d = topSelfIntersection (ZMod l) (L.B.pull (cloι y ≫ π)) d :=
    topSelf_congr (ZMod l) ((L.pull π hπ).pull (cloι y) rfl).isLB (L.pull (cloι y ≫ π) ej).isLB
      (LBIso.chartPull (chartPullLinComb L.B π (fun _ : PUnit => cloι y)
        (fun _ => cloι y ≫ π) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
        (chartPullId _) (PolBaseChange.lbIso_refl (LB.isLB_pull L.isLB _))) d
  have t2 : topSelfIntersection (ZMod l) (L.B.pull (g ≫ cloι (π y))) d =
      topSelfIntersection (ZMod l) ((L.B.pull (cloι (π y))).pull g) d :=
    topSelf_congr (ZMod l) (L.pull (g ≫ cloι (π y)) ei).isLB ((L.pull (cloι (π y)) rfl).pull g rfl).isLB
      (LBIso.symm (LBIso.chartPull (chartPullLinComb L.B (cloι (π y)) (fun _ : PUnit => g)
        (fun _ => g ≫ cloι (π y)) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
        (chartPullId _) (PolBaseChange.lbIso_refl (LB.isLB_pull L.isLB _)))) d
  rw [t1, ← hgc, t2] at e1
  rw [e1, e2]
  suffices key : topSelfIntersection (ZMod l) ((L.B.pull (cloι (π y))).pull g) d =
      (π.residueDegree y : ℤ) * topSelfIntersection (ZMod l) (L.B.pull (cloι (π y))) d' by
    rw [key]; push_cast; ring
  have hB : (L.B.pull (cloι (π y))).IsLB := (L.pull (cloι (π y)) rfl).isLB
  have hBg : ((L.B.pull (cloι (π y))).pull g).IsLB := ((L.pull (cloι (π y)) rfl).pull g rfl).isLB
  have hclo : topologicalKrullDim (closure ({g (genericPoint (clo y))} : Set (clo (π y)))) = d' := by
    rw [hgen, (genericPoint_spec (clo (π y))).def]
    exact (Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq.trans hZd
  by_cases h0 : π.residueDegree y = 0
  · have hne : d ≠ d' := fun e => (hiff.2 e) h0
    have hlt : d' < d := lt_of_le_of_ne hle (Ne.symm hne)
    have hz := GlobalTheory.PullVanish.interNum_pull_eq_zero (ZMod l) 0 d (clo y) (clo (π y)) hWp
      (by rw [Nat.zero_add, hWd]) g (by rw [hclo]; exact_mod_cast hlt)
      (fun i => i.elim0) (fun i => i.elim0) (fun _ => L.B.pull (cloι (π y))) (fun _ => hB)
    rw [h0, Nat.cast_zero, zero_mul, topSelf_def, ← interNum_comp_equiv (ZMod l) _ (fun _ => hBg)
      (Equiv.emptySum (Fin 0) (Fin d)), ← hz]
    congr 1
    funext x
    rcases x with i | a
    · exact i.elim0
    · rfl
  · have hdd : d = d' := hiff.1 h0
    subst hdd
    obtain ⟨U, hU, hgU, hU', hfree, hfin, hrank⟩ := exists_affine_finite_free (ZMod l) (clo (π y)) (clo y)
      (strHom (ZMod l) (clo (π y))) (strHom (ZMod l) (clo y)) hZp hWp g hgs hgen (hδ ▸ h0)
    have key := GlobalTheory.FieldProj.interNum_pull_eq_mul (ZMod l) (clo y) (clo (π y)) (strHom (ZMod l) (clo (π y))) g
      (hgs ▸ hWp) hZp U _ hgU hU hU' ⟨hfree, hfin, hrank⟩ d hZd.le (fun _ => L.B.pull (cloι (π y))) (fun _ => hB)
    rw [hδ] at key
    rw [topSelf_def, topSelf_def]
    convert key using 3
    · exact algebra_zmod_eq _ _
    · exact algebra_zmod_eq _ _

end GlobalTheory.ProjFormulaVert
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightPullbackResidueDegreeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_height_pullback_residue_degree : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ (y : Y) (l : ℕ) [Fact l.Prime], Nonempty (Algebra (ZMod l) Γ(clo y, ⊤)) → h' y = (π.residueDegree y : ℝ) * h (π y) := by
  first | exact @GlobalTheory.ProjFormulaVert.height_pull_vertical | exact GlobalTheory.ProjFormulaVert.height_pull_vertical | (intros; apply GlobalTheory.ProjFormulaVert.height_pull_vertical <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaEveryPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem hasDim_iff_clo {Y : Scheme.{0}} (y : Y) (e : ℕ) : HasDim y e ↔ topologicalKrullDim (clo y) = (e : ℕ) := by
  have hemb := (cloι y).isClosedEmbedding
  have hr : Set.range (cloι y) = closure ({y} : Set Y) := by
    rw [← Set.image_univ, ← (genericPoint_spec (clo y)).def, ← hemb.isClosedMap.closure_image_eq_of_continuous
      hemb.continuous, Set.image_singleton, cloι_genericPoint]
  have h := (hemb.toIsEmbedding.toHomeomorph).isHomeomorph.topologicalKrullDim_eq
  unfold HasDim
  rw [h, hr]

theorem heightProj : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ),
    IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' H H'
  have key : ∀ (n : ℕ) (w : Y), HasDim w (n + 1) → h' w = (π.residueDegree w : ℝ) * h (π w) := by
    intro n
    induction n with
    | zero =>
      intro w hw
      rcases hY.vertical_or_horizontal (cloι w) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
      · exact GlobalTheory.T.arith_height_pullback_residue_degree k X Y p q D E hX hY π hπ L h h' H H' w l hl
      · exact GlobalTheory.T.arithHeight_projectionFormula_pointCurve k X Y p q D E hX hY π hπ L h h' H H' w hc hw
    | succ m ih =>
      intro w hw
      rcases hY.vertical_or_horizontal (cloι w) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
      · exact GlobalTheory.T.arith_height_pullback_residue_degree k X Y p q D E hX hY π hπ L h h' H H' w l hl
      · exact GlobalTheory.T.arithHeight_projectionFormula_inductiveStep k X Y p q D E hX hY π hπ L h h' H H' w m hc hw ih
  intro y
  rcases hY.vertical_or_horizontal (cloι y) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
  · exact GlobalTheory.T.arith_height_pullback_residue_degree k X Y p q D E hX hY π hπ L h h' H H' y l hl
  · exact key e y ((hasDim_iff_clo y (e + 1)).2 he)

end GlobalTheory.MixHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaEveryPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHeight_projectionFormula_every_point : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, h' y = (π.residueDegree y : ℝ) * h (π y) := by
  first | exact @GlobalTheory.MixHt.heightProj | exact GlobalTheory.MixHt.heightProj | (intros; apply GlobalTheory.MixHt.heightProj <;> assumption)
end
