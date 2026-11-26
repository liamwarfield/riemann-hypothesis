module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArCalcOfPrincipalisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullOfGenericallySmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullOfGenericallySmooth
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermLB

open Set GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic
open ReciprocityTheory.L2DbarEstimates (V leviV)

theorem semiPos_pull_of_genSmooth : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k)
    (q : Y ⟶ Sp k) (D E : ℕ), GenSmooth p D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p),
    L.SemiPos D → (L.pull π hπ).SemiPos E := by
  intro k _ X Y p q D E hX π hπ L hL σ
  obtain ⟨R⟩ := hX σ
  intro i c y hy ξ
  set φ := L.φ σ
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  obtain ⟨a, h0⟩ := R.cover (m y)
  set c0 := R.chart a
  have him : m y ∈ ptsIn p σ (L.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hy.2 PUnit.unit
  set F : V E → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U := GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy.1 h0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn E _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy.1]
  set g : V D → ℂ := fun v => (φ.φ (i PUnit.unit) (c0.e.symm v) : ℂ) with hgdef
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((L.cInf σ).contDiffAt c0 h0 him)
  have e : (fun v => ((L.pull π hπ).φ σ |>.φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ φ π hπ i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  show 0 ≤ (leviV E (fun v => ((L.pull π hπ).φ σ |>.φ i (c.e.symm v) : ℂ)) (c.e y) ξ).re
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp E D g F U hU _ hyU hF hg ξ, hFy]
  exact hL σ (i PUnit.unit) c0 (m y) ⟨h0, him⟩ _

end GlobalTheory.HermLB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullOfGenericallySmoothStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPos_pull_of_genericallySmooth : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), GenSmooth p D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), L.SemiPos D → (L.pull π hπ).SemiPos E := by
  first | exact @GlobalTheory.HermLB.semiPos_pull_of_genSmooth | exact GlobalTheory.HermLB.semiPos_pull_of_genSmooth | (intros; apply GlobalTheory.HermLB.semiPos_pull_of_genSmooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithmeticCoverOverModification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithmeticCoverOverModification
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLift

open Limits GlobalTheory.MixHt

theorem exists_cover_over_modification : ∀ (k : Type) [CommRing k] (X X' Y : Scheme.{0}) [IsIntegral X] [IsIntegral X']
    [IsIntegral Y] (p : X ⟶ Sp k) (D E : ℕ) (ρ : X' ⟶ X) (π : Y ⟶ X), IsArithVar p D → IsArithVar (ρ ≫ p) D →
    IsArithVar (π ≫ p) E → ρ (genericPoint X') = genericPoint X →
    ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (g : Y' ⟶ Y) (π' : Y' ⟶ X'), π' ≫ ρ = g ≫ π ∧
      IsArithVar (g ≫ π ≫ p) E ∧ g (genericPoint Y') = genericPoint Y ∧
      g.residueDegree (genericPoint Y') ≠ 0 := by
  intro k _ X X' Y _ _ _ p D E ρ π hX hX' hY hρ

  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  obtain ⟨N', j', _, hj'⟩ := hX'.isProjOver
  have : IsProper (ρ ≫ p) := hj' ▸ inferInstance
  have : IsProper ρ := IsProper.of_comp ρ p
  have hs : Function.Surjective ρ := by
    rw [← Set.range_eq_univ]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec X).def, ← ρ.isClosedMap.isClosed_range.closure_eq]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hρ⟩)
  have : Surjective ρ := ⟨hs⟩

  obtain ⟨z, hz, hdeg⟩ := exists_residueDegree_pos_of_mem_range _ _ (pullback.fst π ρ) (genericPoint Y)
    ((inferInstance : Surjective (pullback.fst π ρ)).surj _)
  set g := cloι z ≫ pullback.fst π ρ with hgdef
  have hg : g (genericPoint (clo z)) = genericPoint Y := by
    rw [hgdef, Scheme.Hom.comp_apply, cloι_genericPoint, hz]
  have hdeg' : g.residueDegree (genericPoint (clo z)) ≠ 0 := by
    rw [hgdef, CurveDegreesCompare.residueDegree_comp, Published.residueDegree_of_isClosedImmersion (cloι z), mul_one,
      cloι_genericPoint]
    exact hdeg.ne'

  have hP : IsProjOver (pullback.fst π ρ ≫ π ≫ p) :=
    FlagFamily.isProjOver_pullback_over hX.isProjOver hY.isProjOver hX'.isProjOver
  have hA : IsAmb (g ≫ π ≫ p) := by
    have := (IsAmb.mk hX.1 hX.2 hP).sub (cloι z)
    rwa [← Category.assoc] at this
  have hAY : IsAmb (π ≫ p) := isAmb_of_isArithVar hY

  obtain ⟨⟨m, hm⟩, -, -, -, -, hgen⟩ := hasDim_basic k (clo z) (g ≫ π ≫ p) hA
  obtain ⟨d, -, hd⟩ := hm (genericPoint (clo z))
  have hdY : HasDim (g (genericPoint (clo z))) (E + 1) := by
    rw [hg]
    exact (DimBasic.hasDim_genericPoint_iff Y (E + 1)).2 hY.dim_eq
  have hcmp := DimDeg.dim_le_and_residueDegree_ne_zero_iff k Y (clo z) (π ≫ p) (g ≫ π ≫ p) hAY hA g rfl
    (genericPoint (clo z)) d (E + 1) hd hdY
  have hdim : topologicalKrullDim (clo z) = (E + 1 : ℕ) := (hgen (clo z) (E + 1)).1 (hcmp.2.1 hdeg' ▸ hd)

  have hcY : CharZero Γ(Y, ⊤) := hY.charZero
  have h₁ : CharZero Y.functionField :=
    charZero_of_injective_ringHom (fnOf_injective (⊤ : Y.Opens) (Opens.mem_top _))
  have h₂ : CharZero (Y.residueField (genericPoint Y)) := by
    let f : Y.functionField →+* Y.residueField (genericPoint Y) := (Y.residue _).hom
    exact charZero_of_injective_ringHom f.injective
  have h₃ : CharZero (Y.residueField (g (genericPoint (clo z)))) := hg ▸ h₂
  have h₄ : CharZero ((clo z).residueField (genericPoint (clo z))) :=
    charZero_of_injective_ringHom (g.residueFieldMap _).hom.injective
  have h₅ : CharZero (clo z).functionField := by
    let f : (clo z).functionField →+* (clo z).residueField (genericPoint (clo z)) := ((clo z).residue _).hom
    exact (RingHom.charZero_iff f.injective).2 h₄
  have h₆ : CharZero Γ(clo z, ⊤) :=
    (RingHom.charZero_iff (fnOf_injective (⊤ : (clo z).Opens) (Opens.mem_top _))).2 h₅
  refine ⟨clo z, inferInstance, g, cloι z ≫ pullback.snd π ρ, ?_,
    ⟨hX.1, hX.2, inferInstance, hA.isProjOver, (flat_int_iff_charZero _).2 h₆, hdim⟩, hg, hdeg'⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]

end GlobalTheory.CoverLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithmeticCoverOverModificationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arithmeticCover_over_modification : ∀ (k : Type) [CommRing k] (X X' Y : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsIntegral Y] (p : X ⟶ Sp k) (D E : ℕ) (ρ : X' ⟶ X) (π : Y ⟶ X), IsArithVar p D → IsArithVar (ρ ≫ p) D → IsArithVar (π ≫ p) E → ρ (genericPoint X') = genericPoint X → ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (g : Y' ⟶ Y) (π' : Y' ⟶ X'), π' ≫ ρ = g ≫ π ∧ IsArithVar (g ≫ π ≫ p) E ∧ g (genericPoint Y') = genericPoint Y ∧ g.residueDegree (genericPoint Y') ≠ 0 := by
  first | exact @GlobalTheory.CoverLift.exists_cover_over_modification | exact GlobalTheory.CoverLift.exists_cover_over_modification | (intros; apply GlobalTheory.CoverLift.exists_cover_over_modification <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPositivePullbackGenericallyEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPositivePullbackGenericallyEtale
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
open GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory.SemiPosUp

open ReciprocityTheory.L2DbarEstimates (V leviV)

theorem levi_pull_nonneg {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k}
    {q : Y ⟶ Sp k} {σ : k →+* ℂ} (π : Y ⟶ X) (hπ : π ≫ p = q) {D D' : ℕ} {B : LB X}
    (φ : Weight p σ B) (hC : φ.IsCInf) (hSP : φ.SemiPosReg D) (i : (B.pull π).ι)
    (c : AlgChart q σ D') {y : CxPts q σ} (hy : y ∈ c.e.source ∩ ptsIn q σ ((B.pull π).U i))
    (c0 : AlgChart p σ D) (h0 : PtsOver.map π hπ (spMap σ) y ∈ c0.e.source) (ξ : Fin D' → ℂ) :
    0 ≤ (leviV D' (fun v => ((φ.pull π hπ).φ i (c.e.symm v) : ℂ)) (c.e y) ξ).re := by
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  have him : m y ∈ ptsIn p σ (B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hy.2 PUnit.unit
  set F : V D' → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U :=
    GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy.1 h0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D' _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy.1]
  set g : V D → ℂ := fun v => (φ.φ (i PUnit.unit) (c0.e.symm v) : ℂ) with hgdef
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hC.contDiffAt c0 h0 him)
  have e : (fun v => ((φ.pull π hπ).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ φ π hπ i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp D' D g F U hU _ hyU hF hg ξ, hFy]
  exact hSP (i PUnit.unit) c0 (m y) ⟨h0, him⟩ _

theorem semiPos_pull_of_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  intro k _ X Y _ _ p q D hp hq π hπ V hV he L hL
  have := hq.isDomain
  have := hq.finite
  obtain ⟨T, hT, hηT, hch⟩ := GlobalTheory.GenericChart.exists_isClosed_chart k X p D hp
  let U : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  obtain ⟨v, hv⟩ := hV
  obtain ⟨v', -, hv'⟩ := Flat.generalizingMap (V.ι ≫ π)
    (genericPoint_specializes ((V.ι ≫ π) ⟨v, hv⟩))
  have hW : ((π ⁻¹ᵁ U : Y.Opens) : Set Y).Nonempty := by
    refine ⟨V.ι v', ?_⟩
    show π (V.ι v') ∈ Tᶜ
    rw [← Scheme.Hom.comp_apply, hv']
    exact hηT
  intro σ
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    change Ideal.comap (algebraMap ℤ k) (RingHom.ker σ) = ⊥
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  intro i
  refine GlobalTheory.SemiPosBir.PosOn.of_inter hσ (isOpen_ptsIn _) ((L.cInf σ).pull π hπ i) hW ?_
  rintro c y ⟨hyc, hyS, hyW⟩ ξ
  obtain ⟨c0, h0⟩ := hch σ (PtsOver.map π hπ (spMap σ) y) (mem_ptsIn.1 hyW)
  exact levi_pull_nonneg π hπ (L.φ σ) (L.cInf σ) (hL σ) i c ⟨hyc, hyS⟩ c0 h0 ξ

end GlobalTheory.SemiPosUp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPositivePullbackGenericallyEtaleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPositive_pullback_generically_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  first | exact @GlobalTheory.SemiPosUp.semiPos_pull_of_etale | exact GlobalTheory.SemiPosUp.semiPos_pull_of_etale | (intros; apply GlobalTheory.SemiPosUp.semiPos_pull_of_etale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensEtaleGenericallyFiniteDominant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensEtaleGenericallyFiniteDominant
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.GenEtale

theorem exists_opens_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ Etale (V.ι ≫ π) := by
  intro k _ X Y _ _ p q D hp hq π hπ hη hd
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp.isProjOver
  have : IsProper (π ≫ p) := hπ ▸ GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver
  have : IsProper π := IsProper.of_comp π p
  have := hp.isLocallyNoetherian
  have := hp.charZero
  obtain ⟨U, -, hU, hxU, hW, -, hE, -⟩ :=
    GlobalTheory.GenFiniteEtale.exists_finite_etale_of_isProper π hη hd ⊤ (Opens.mem_top _)
  refine ⟨π ⁻¹ᵁ U, ⟨genericPoint Y, show π _ ∈ U from hη ▸ hxU⟩, ?_⟩
  have : IsAffine U := hU
  have : IsAffine (π ⁻¹ᵁ U) := hW
  have hE' : ∀ U' : X.Opens, U' = U → (π.app U').hom.Etale := by
    rintro _ rfl
    exact hE
  have e : U.ι ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have h1 : Etale (π ∣_ U) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale), morphismRestrict_appTop]
    exact (RingHom.Etale.respectsIso).cancel_right_isIso _ _ |>.2 (hE' _ e)
  rw [← morphismRestrict_ι]
  infer_instance

end GlobalTheory.GenEtale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpensEtaleGenericallyFiniteDominantStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_opens_etale_generically_finite_dominant : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ Etale (V.ι ≫ π) := by
  first | exact @GlobalTheory.GenEtale.exists_opens_etale | exact GlobalTheory.GenEtale.exists_opens_etale | (intros; apply GlobalTheory.GenEtale.exists_opens_etale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosOfPullbackGenericallyEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosOfPullbackGenericallyEtale
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.Points GlobalTheory.SemiPosBir

namespace GlobalTheory.SemiPosEtale

variable {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Z ⟶ Sp k} {σ : k →+* ℂ}
  {D : ℕ}

theorem exists_map_eq_of_etale (j : Z ⟶ X) [Etale j] (hj : j ≫ p = q) {y : CxPts p σ}
    (hy : y.1 (IsLocalRing.closedPoint ℂ) ∈ Set.range j) :
    ∃ z : CxPts q σ, PtsOver.map j hj _ z = y := by
  obtain ⟨v, hv⟩ := hy
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := y.1) v _ hv
  have : JacobsonSpace ↥(pullback j y.1) := LocallyOfFiniteType.jacobsonSpace (pullback.snd j y.1)
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback j y.1)))
    ⟨w, trivial⟩ isOpen_univ.isLocallyClosed
  replace hc : IsClosed {c} := hc
  refine ⟨⟨pointOfClosedPoint (pullback.snd j y.1) c hc ≫ pullback.fst j y.1, ?_⟩, Subtype.ext ?_⟩
  · rw [← hj, Category.assoc, pullback.condition_assoc, pointOfClosedPoint_comp_assoc]
    exact y.2
  · change (pointOfClosedPoint (pullback.snd j y.1) c hc ≫ pullback.fst j y.1) ≫ j = y.1
    rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

def img (j : Z ⟶ X) [Etale j] : X.Opens := ⟨Set.range j, j.isOpenMap.isOpen_range⟩

theorem PosOn.of_etale (j : Z ⟶ X) [Etale j] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)}
    (h : PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S)) :
    PosOn D f (S ∩ ptsIn p σ (img j)) := fun c y hy ξ => by
  obtain ⟨z, rfl⟩ := exists_map_eq_of_etale j hj (mem_ptsIn.1 hy.2.2)
  obtain ⟨W, hW, hzW, e⟩ := exists_isAffineOpen_le z.1 (V := j ⁻¹ᵁ c.U) (c.source_subset hy.1)
  have h₂ : (MvPolynomial.eval₂Hom (algX q W) fun a => (j.appLE _ W e).hom (c.x a)).Etale := by
    rw [← appLE_comp_eval hj e]
    exact RingHom.Etale.stableUnderComposition _ _ c.etale
      (HasRingHomProperty.appLE @Etale j inferInstance ⟨c.U, c.affine⟩ ⟨W, hW⟩ e)
  obtain ⟨c', hc, rfl, hcx⟩ := AlgChart.exists_of_etale (y := z) hW _ h₂ hzW
  rw [← levi_pull hj f c c' e (congrFun hcx) hc hy.1]
  exact h c' _ ⟨hc, hy.2.1⟩ ξ

end GlobalTheory.SemiPosEtale

namespace GlobalTheory.SemiPosEtale

theorem semiPos_of_pull_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, (L.pull π hπ).SemiPos D → L.SemiPos D := by
  intro k _ X Y _ _ p q D hp _ π hπ V hV hE L hL σ i
  have := hp.isDomain
  have := hp.finite
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have : Etale (V.ι ≫ π) := hE
  have hj : (V.ι ≫ π) ≫ p = V.ι ≫ q := by rw [Category.assoc, hπ]
  have hU : ((img (V.ι ≫ π) : X.Opens) : Set X).Nonempty := by
    obtain ⟨v, hv⟩ := hV
    exact ⟨_, ⟨v, hv⟩, rfl⟩
  change PosOn D ((L.φ σ).φ i) (ptsIn p σ (L.B.U i))
  refine PosOn.of_inter hσ (isOpen_ptsIn _) (L.cInf σ i) hU (PosOn.of_etale (V.ι ≫ π) hj ?_)
  let J : (L.B.pull π).ι := fun _ => i
  have h₀ : PosOn D (((L.φ σ).pull π hπ).φ J) (ptsIn q σ ((L.B.pull π).U J)) := hL σ J
  have e₁ : ptsIn q σ ((L.B.pull π).U J) =
      PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ (L.B.U i) := Set.ext fun z => by
    rw [Set.mem_preimage, mem_ptsIn, mem_ptsIn]
    exact ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩
  have e₂ : ((L.φ σ).pull π hπ).φ J = fun w => (L.φ σ).φ i (PtsOver.map π hπ _ w) :=
    funext ((L.φ σ).pull_φ π hπ J)
  rw [e₁, e₂] at h₀
  have h₁ := h₀.pull V.ι (q := V.ι ≫ q) rfl
  have e₃ (w : CxPts (V.ι ≫ q) σ) : PtsOver.map π hπ _ (PtsOver.map V.ι rfl _ w) =
      PtsOver.map (V.ι ≫ π) hj _ w := Subtype.ext (Category.assoc _ _ _)
  simp only [e₃] at h₁
  exact h₁

end GlobalTheory.SemiPosEtale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosOfPullbackGenericallyEtaleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPos_of_pullback_generically_etale : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (V : Y.Opens), (V : Set Y).Nonempty → Etale (V.ι ≫ π) → ∀ L : HermLB p, (L.pull π hπ).SemiPos D → L.SemiPos D := by
  first | exact @GlobalTheory.SemiPosEtale.semiPos_of_pull_etale | exact GlobalTheory.SemiPosEtale.semiPos_of_pull_etale | (intros; apply GlobalTheory.SemiPosEtale.semiPos_of_pull_etale <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.SemiPullAll

theorem isometric_pull_pull {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {s : Z ⟶ Sp k} (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = s) (c : Z ⟶ X)
    (hc : c ≫ p = s) (e : g ≫ f = c) : ((L.pull f hf).pull g hg).Isometric (L.pull c hc) := by
  subst e
  have R : GlobalTheory.TwistTop.Refines ((L.pull f hf).pull g hg) (L.pull (g ≫ f) hc)
      (fun c => c PUnit.unit) 0 := by
    refine ⟨fun c y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) a, ?_, ?_⟩
    · intro W r z c c' hc₁ hc₂
      have h₁ := Set.mem_iInter.1 hc₁ PUnit.unit
      have h₂ := Set.mem_iInter.1 hc₂ PUnit.unit
      refine (gm_pull_g _ g r z c c' hc₁ hc₂).trans ((gm_pull_g _ f (r ≫ g) z _ _ h₁ h₂).trans ?_)
      refine Eq.trans ?_ (gm_pull_g _ (g ≫ f) r z (c PUnit.unit) (c' PUnit.unit)
        (Set.mem_iInter.2 fun a => Set.mem_iInter.1 h₁ a) (Set.mem_iInter.2 fun a => Set.mem_iInter.1 h₂ a)).symm
      rw [Category.assoc]
    · intro σ c y hy
      refine (((L.pull f hf).φ σ).pull_φ g hg c y).trans (((L.φ σ).pull_φ f hf _ _).trans ?_)
      refine Eq.trans ?_ (((L.φ σ).pull_φ (g ≫ f) hc (c PUnit.unit) y).symm.trans (add_zero _).symm)
      exact congrArg _ (Subtype.ext (Category.assoc _ _ _))
  exact HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy =>
    ((R.φ σ c y hy).trans (add_zero _)).symm

theorem semiPull_of_principalisation : GlobalTheory.Published.Principalisation → SemiPull := by
  intro hP k _ X Y p q D E hp hq π hπ L hL
  have := hp.isIntegral
  have := hq.isIntegral
  obtain ⟨X', _, ρ, hρ, hsm, hgen, hdeg⟩ := GlobalTheory.GenRes.exists_birational_genSmooth hP k X p D hp
  obtain ⟨V, hV, het⟩ := GlobalTheory.T.exists_opens_etale_generically_finite_dominant k X X' p (ρ ≫ p) D hp hρ ρ rfl hgen (by rw [hdeg]; exact one_ne_zero)
  have h₁ : (L.pull ρ rfl).SemiPos D := GlobalTheory.T.semiPositive_pullback_generically_etale k X X' p (ρ ≫ p) D hp hρ ρ rfl V hV het L hL
  have hπp : IsArithVar (π ≫ p) E := by rw [hπ]; exact hq
  obtain ⟨Y', _, g, π', hcomm, hY', hggen, hgdeg⟩ := GlobalTheory.T.exists_arithmeticCover_over_modification k X X' Y p D E ρ π hp hρ hπp hgen
  have hY'q : IsArithVar (g ≫ q) E := by rw [← hπ]; exact hY'
  have e₁ : π' ≫ ρ ≫ p = g ≫ q := by rw [← Category.assoc, hcomm, Category.assoc, hπ]
  have e₂ : (g ≫ π) ≫ p = g ≫ q := by rw [Category.assoc, hπ]
  have h₂ : ((L.pull ρ rfl).pull π' e₁).SemiPos E :=
    GlobalTheory.T.semiPos_pull_of_genericallySmooth k X' Y' (ρ ≫ p) (g ≫ q) D E hsm π' e₁ (L.pull ρ rfl) h₁
  have iso : ((L.pull ρ rfl).pull π' e₁).Isometric ((L.pull π hπ).pull g rfl) :=
    (isometric_pull_pull L ρ rfl π' e₁ (g ≫ π) e₂ hcomm).trans
      (isometric_pull_pull L π hπ g rfl (g ≫ π) e₂ rfl).symm
  have h₃ : ((L.pull π hπ).pull g rfl).SemiPos E :=
    HermLB.Isometric.semiPos _ _ E iso h₂
  obtain ⟨W, hW, hWet⟩ := GlobalTheory.T.exists_opens_etale_generically_finite_dominant k Y Y' q (g ≫ q) E hq hY'q g rfl hggen hgdeg
  exact GlobalTheory.T.semiPos_of_pullback_generically_etale k Y Y' q (g ≫ q) E hq hY'q g rfl W hW hWet (L.pull π hπ) h₃

end GlobalTheory.SemiPullAll
