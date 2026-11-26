module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifference
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveDegreeIndependentOfSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductiveRhsSymmIsometryInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchLogNormIntegralIsometrySymmCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchLogNormIntegralIsometrySymmCongr
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem pol_comp_equiv {ι : Type} [Fintype ι] (τ : ι ≃ ι) (φ : (ι → ℤ) → ℝ) :
    FibreProj.pol (fun n => φ (n ∘ τ.symm)) = FibreProj.pol φ := by
  classical
  unfold FibreProj.pol
  refine Fintype.sum_equiv (Equiv.finsetCongr τ) _ _ fun S => ?_
  simp only [Equiv.finsetCongr_apply, Finset.card_map]
  congr 2
  funext i
  simp

theorem mixArch_iso_symm_congr : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → mixArch L M hr = mixArch L' M hr) ∧ (∀ τ : Equiv.Perm (Fin e), mixArch (fun a => L (τ a)) M hr = mixArch L M hr) ∧ ∀ (M' : HermLB q) (r' : M'.B.ι → Y.functionFieldˣ) (hr' : IsRatSec M'.B r'), M'.div hr' = M.div hr → (∀ σ, Set.EqOn (logNorm (M'.φ σ) r') (logNorm (M.φ σ) r) (offSupp q σ (M.div hr))) → mixArch L M' hr' = mixArch L M hr := by
  intro k _ Y _ q e L M r hr
  refine ⟨fun L' hL => ?_, fun τ => ?_, fun M' r' hr' hd hn => ?_⟩
  · have h : ∀ n, (comb L n).archInt M e hr = (comb L' n).archInt M e hr := fun n =>
      by simp only [HermLB.archInt, (isometric_comb_congr hL n).chernInt_eq]
    simp only [mixArch, h]
  · have h : ∀ n, (comb (fun a => L (τ a)) (n ∘ τ)).archInt M e hr = (comb L n).archInt M e hr := fun n => by
      have iso : (comb (fun a => L (τ a)) (n ∘ τ)).Isometric (comb L n) := by
        refine HermLB.icls_eq_iff.1 ?_
        rw [icls_comb, icls_comb]
        exact Fintype.sum_equiv τ _ _ fun a => by simp
      simp only [HermLB.archInt, iso.chernInt_eq]
    simp only [mixArch]
    rw [← pol_comp_equiv τ.symm (fun n => (comb (fun a => L (τ a)) n).archInt M e hr)]
    simp only [Equiv.symm_symm, h]
  · have h : ∀ n, (comb L n).archInt M' e hr' = (comb L n).archInt M e hr := fun n => by
      simp only [HermLB.archInt, hd]
      exact finsum_congr fun σ => Weight.chernInt_congr (isOpen_offSupp _).measurableSet (hn σ)
    simp only [mixArch, h]

end GlobalTheory.MixHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchLogNormIntegralIsometrySymmCongrStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedArchLogNormIntegral_isometry_symm_congr : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → mixArch L M hr = mixArch L' M hr) ∧ (∀ τ : Equiv.Perm (Fin e), mixArch (fun a => L (τ a)) M hr = mixArch L M hr) ∧ ∀ (M' : HermLB q) (r' : M'.B.ι → Y.functionFieldˣ) (hr' : IsRatSec M'.B r'), M'.div hr' = M.div hr → (∀ σ, Set.EqOn (logNorm (M'.φ σ) r') (logNorm (M.φ σ) r) (offSupp q σ (M.div hr))) → mixArch L M' hr' = mixArch L M hr := by
  first | exact @GlobalTheory.MixHt.mixArch_iso_symm_congr | exact GlobalTheory.MixHt.mixArch_iso_symm_congr | (intros; apply GlobalTheory.MixHt.mixArch_iso_symm_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductiveRhsSymmIsometryInvariant
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem recVal_iso_symm : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ T, IsMix q e T →
    ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r),
    (∀ L L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → recVal (T e L) L M hr = recVal (T e L') L' M hr) ∧
    (∀ (L : Fin e → HermLB q) (τ : Equiv.Perm (Fin e)),
      recVal (T e fun a => L (τ a)) (fun a => L (τ a)) M hr = recVal (T e L) L M hr) ∧
    (∀ (L : Fin e → HermLB q) (M' : HermLB q), M.Isometric M' → ∃ (r' : M'.B.ι → Y.functionFieldˣ)
      (hr' : IsRatSec M'.B r'), recVal (T e L) L M' hr' = recVal (T e L) L M hr) := by
  intro _ k _ Y _ _ q hq e hY T hT M r hr
  have hd : ∀ z : Y, ((M.div hr).mult z : ℝ) ≠ 0 → HasDim z e := fun z hz =>
    ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq e hY).1 z).1
      (CartierDiv.coheight_eq_one_of_mult_ne_zero fun h => hz (by rw [h]; simp))
  refine ⟨fun L L' h => ?_, fun L τ => ?_, fun L M' h => ?_⟩
  · unfold recVal
    rw [(GlobalTheory.T.mixedArchLogNormIntegral_isometry_symm_congr k Y q e L M r hr).1 L' h]
    congr 1
    refine finsum_congr fun z => ?_
    by_cases hz : ((M.div hr).mult z : ℝ) = 0
    · simp [hz]
    · rw [hT.iso e L L' z le_rfl (hd z hz) h]
  · unfold recVal
    rw [(GlobalTheory.T.mixedArchLogNormIntegral_isometry_symm_congr k Y q e L M r hr).2.1 τ]
    congr 1
    refine finsum_congr fun z => ?_
    by_cases hz : ((M.div hr).mult z : ℝ) = 0
    · simp [hz]
    · rw [hT.symm e L τ z le_rfl (hd z hz)]
  · obtain ⟨r', hr', hdiv, hlog⟩ := h.exists_isRatSec hr
    refine ⟨r', hr', ?_⟩
    unfold recVal
    rw [(GlobalTheory.T.mixedArchLogNormIntegral_isometry_symm_congr k Y q e L M r hr).2.2 M' r' hr' hdiv hlog, hdiv]

end GlobalTheory.MixHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductiveRhsSymmIsometryInvariantStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedHeight_inductive_rhs_symm_isometry_invariant : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ T, IsMix q e T → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ L L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → recVal (T e L) L M hr = recVal (T e L') L' M hr) ∧ (∀ (L : Fin e → HermLB q) (τ : Equiv.Perm (Fin e)), recVal (T e fun a => L (τ a)) (fun a => L (τ a)) M hr = recVal (T e L) L M hr) ∧ (∀ (L : Fin e → HermLB q) (M' : HermLB q), M.Isometric M' → ∃ (r' : M'.B.ι → Y.functionFieldˣ) (hr' : IsRatSec M'.B r'), recVal (T e L) L M' hr' = recVal (T e L) L M hr) := by
  first | exact @GlobalTheory.MixHt.recVal_iso_symm | exact GlobalTheory.MixHt.recVal_iso_symm | (intros; apply GlobalTheory.MixHt.recVal_iso_symm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixedHeightByInductionSucc
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightRecursiveValueWellDefined
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveHeightFormulaRhsTransportIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveHeightFormulaRhsTransportIso
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.MixHt
open GlobalTheory.TrueGeo.SmallSec GlobalTheory.FrameGlue.Pull GlobalTheory.MultPull GlobalTheory.Points

variable {k : Type} [CommRing k]

theorem isEmpty_cxPts_of_map {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (g : Y ⟶ X) (hg : g ≫ p = q)
    (h : ∀ σ : k →+* ℂ, IsEmpty (CxPts p σ)) (σ : k →+* ℂ) : IsEmpty (CxPts q σ) :=

  isEmpty_iff.2 fun y => isEmpty_iff.1 (h σ) (PtsOver.map g hg (spMap σ) y)

theorem mixArch_pull_iso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
    (hp : IsAmb p) (hq : IsAmb q) (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X) [IsIso g]
    (e : ℕ) (hX : topologicalKrullDim X = (e + 1 : ℕ)) (L : Fin e → HermLB p) (M : HermLB p)
    (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r) :
    mixArch (fun a => (L a).pull g hg) (M.pull g hg)
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) =
      mixArch L M hr := by
  have hY : topologicalKrullDim Y = (e + 1 : ℕ) :=
    (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso g)).isHomeomorph).trans hX
  have hg' : inv g ≫ q = p := by rw [← hg, IsIso.inv_hom_id_assoc]
  by_cases hp0 : ∀ σ : k →+* ℂ, IsEmpty (CxPts p σ)
  · rw [(GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints k X p hp0 e L M).1 r hr]
    exact (GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints k Y q (isEmpty_cxPts_of_map g hg hp0) e _ _).1 _ _
  by_cases hq0 : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)
  · exact absurd (isEmpty_cxPts_of_map (inv g) hg' hq0) hp0
  obtain ⟨e₁, he₁, hXa⟩ := (GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k X p hp (e + 1) hX).resolve_left fun ⟨_, _, _, h⟩ => hp0 h
  obtain ⟨e₂, he₂, hYa⟩ := (GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k Y q hq (e + 1) hY).resolve_left fun ⟨_, _, _, h⟩ => hq0 h
  obtain rfl : e₁ = e := by omega
  obtain rfl : e₂ = e₁ := by omega
  unfold mixArch
  congr 2
  funext n
  have h₁ : (comb (fun a => (L a).pull g hg) n).archInt (M.pull g hg) e₂
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) =
      ((comb L n).pull g hg).archInt (M.pull g hg) e₂
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) := by
    simp only [HermLB.archInt, (isometric_comb_pull L n g hg).chernInt_eq]
  rw [h₁, GlobalTheory.T.archimedeanIntegral_pull_mul_degree k X Y p q e₂ hXa hYa g hg hη (by rw [Published.residueDegree_of_isClosedImmersion]; exact one_ne_zero),
    Published.residueDegree_of_isClosedImmersion, Nat.cast_one, one_mul]

theorem mult_pull_iso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) ⤳ genericPoint X) [IsIso g]
    (M : HermLB p) {r : M.B.ι → X.functionFieldˣ} (hr : IsRatSec M.B r) (y : Y) :
    ((M.pull g hg).div (MultPull.isRatSec_pull_map g hη hr)).mult y = (M.div hr).mult (g y) := by
  change (divOfRatSec (LB.isLB_pull M.isLB g) (MultPull.isRatSec_pull_map g hη hr)).mult y =
    (divOfRatSec M.isLB hr).mult (g y)
  obtain ⟨c, hc⟩ := exists_chart (LB.isLB_pull M.isLB g) y
  have hc' : g y ∈ M.B.U (c PUnit.unit) := Set.mem_iInter.1 hc PUnit.unit
  rw [((presents_divOfRatSec _ _).isEqn c y hc).mult_eq,
    ((presents_divOfRatSec M.isLB hr).isEqn _ _ hc').mult_eq]
  exact ord_fnMap g hη y _

theorem transport : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), IsIso g → ∀ e : ℕ, topologicalKrullDim X = (e + 1 : ℕ) → ∀ (h : X → ℝ) (L : Fin e → HermLB p) (M : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), recVal (fun w => h (g w)) (fun a => (L a).pull g hg) (M.pull g hg) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = recVal h L M hr := by
  intro k _ X Y _ _ _ _ p q hp hq g hg hη _ e hX h L M r hr
  unfold recVal
  rw [mixArch_pull_iso p q hp hq g hg hη e hX L M r hr]
  congr 1
  refine (finsum_congr fun z => ?_).trans
    (finsum_comp_equiv (Scheme.homeoOfIso (asIso g)).toEquiv (f := fun x => ((M.div hr).mult x : ℝ) * h x))
  exact congrArg (fun n : ℤ => (n : ℝ) * h (g z)) (mult_pull_iso g hg _ M hr z)

end GlobalTheory.MixHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveHeightFormulaRhsTransportIsoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inductive_height_formula_rhs_transport_iso : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), IsIso g → ∀ e : ℕ, topologicalKrullDim X = (e + 1 : ℕ) → ∀ (h : X → ℝ) (L : Fin e → HermLB p) (M : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), recVal (fun w => h (g w)) (fun a => (L a).pull g hg) (M.pull g hg) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = recVal h L M hr := by
  exact @GlobalTheory.MixHt.transport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoClosedImmersionsSameGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoClosedImmersionsSameGenericPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
open Limits

namespace GlobalTheory

theorem range_closedImmersion_eq_closure_genericPoint {X Y : Scheme.{0}} [IsIntegral Y] (i : Y ⟶ X)
    [IsClosedImmersion i] : Set.range i = closure {i (genericPoint Y)} := by
  have hc : IsClosedMap i := i.isClosedEmbedding.isClosedMap
  have h1 : Set.range i = i '' closure {genericPoint Y} := by
    rw [(genericPoint_spec Y).def, Set.image_univ]
  rw [h1]
  apply le_antisymm
  · exact image_closure_subset_closure_image i.continuous |>.trans (by rw [Set.image_singleton])
  · rw [← Set.image_singleton]
    exact closure_minimal (Set.image_mono subset_closure) (hc _ isClosed_closure)

theorem iso_of_closedImmersion_genericPoint_eq :
    ∀ (X Y Y' : Scheme.{0}) [IsIntegral Y] [IsIntegral Y'] (i : Y ⟶ X) (i' : Y' ⟶ X)
      [IsClosedImmersion i] [IsClosedImmersion i'], i (genericPoint Y) = i' (genericPoint Y') →
      ∃ g : Y' ⟶ Y, IsIso g ∧ g ≫ i = i' ∧ g (genericPoint Y') = genericPoint Y := by
  intro X Y Y' _ _ i i' _ _ h
  have hr : Set.range i = Set.range i' := by
    rw [range_closedImmersion_eq_closure_genericPoint, range_closedImmersion_eq_closure_genericPoint, h]
  have hs : Function.Surjective (pullback.snd i i') := by
    intro y'
    obtain ⟨y, hy⟩ : i' y' ∈ Set.range i := hr ▸ ⟨y', rfl⟩
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := i') y y' hy
    exact ⟨z, hz⟩
  have hf : Function.Surjective (pullback.fst i i') := by
    intro y
    obtain ⟨y', hy⟩ : i y ∈ Set.range i' := hr ▸ ⟨y, rfl⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := i') y y' hy.symm
    exact ⟨z, hz⟩
  haveI : Surjective (pullback.snd i i') := ⟨hs⟩
  haveI : Surjective (pullback.fst i i') := ⟨hf⟩
  haveI : IsIso (pullback.snd i i') := isIso_of_isClosedImmersion_of_surjective _
  haveI : IsIso (pullback.fst i i') := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨inv (pullback.snd i i') ≫ pullback.fst i i', inferInstance, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  · apply i.isClosedEmbedding.injective
    have e := congrArg (fun f : Y' ⟶ X => f (genericPoint Y')) (show (inv (pullback.snd i i') ≫ pullback.fst i i') ≫ i = i' by
      rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc])
    rw [Scheme.Hom.comp_apply] at e
    rw [e, h]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoClosedImmersionsSameGenericPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_closedImmersions_same_genericPoint : ∀ (X Y Y' : Scheme.{0}) [IsIntegral Y] [IsIntegral Y'] (i : Y ⟶ X) (i' : Y' ⟶ X) [IsClosedImmersion i] [IsClosedImmersion i'], i (genericPoint Y) = i' (genericPoint Y') → ∃ g : Y' ⟶ Y, IsIso g ∧ g ≫ i = i' ∧ g (genericPoint Y') = genericPoint Y := by
  first | exact @GlobalTheory.iso_of_closedImmersion_genericPoint_eq | exact GlobalTheory.iso_of_closedImmersion_genericPoint_eq | (intros; apply GlobalTheory.iso_of_closedImmersion_genericPoint_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightRecursiveValueWellDefined
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.StepVal

variable {k : Type} [CommRing k]

theorem isometric_pull_pull' {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {s : Z ⟶ Sp k} (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = s) (c : Z ⟶ X)
    (hc : c ≫ p = s) (e : g ≫ f = c) : ((L.pull f hf).pull g hg).Isometric (L.pull c hc) := by
  subst e
  have R := L.refines_pull_pull f hf g hg hc
  exact HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy =>
    ((R.φ σ c y hy).trans (add_zero _)).symm

theorem recVal_congr {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {e : ℕ}
    {h h' : Y → ℝ} (H : ∀ z : Y, Order.coheight z = 1 → h z = h' z) (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : recVal h L M hr = recVal h' L M hr := by
  unfold recVal
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  · rw [H z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)]

theorem dim_of_genericPoint {X Y : Scheme.{0}} [IsIntegral Y] {p : X ⟶ Sp k} (hp : IsAmb p) (i : Y ⟶ X)
    [IsClosedImmersion i] {x : X} {d : ℕ} (hx : HasDim x d) (hg : i (genericPoint Y) = x) :
    topologicalKrullDim Y = d := by
  have H := (GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp).2.2.2.2
  rw [← H.2 Y d, ← H.1 Y i (genericPoint Y) d, hg]
  exact hx

theorem recVal_indep_section (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ) {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) (hY : topologicalKrullDim Y = (m + 1 : ℕ)) {T}
    (hT : IsMix q m T) (L : Fin m → HermLB q) (N : HermLB q) {r r' : N.B.ι → Y.functionFieldˣ} (hr : IsRatSec N.B r)
    (hr' : IsRatSec N.B r') : recVal (T m L) L N hr = recVal (T m L) L N hr' := by
  cases m with
  | zero =>
    have H : ∀ z : Y, Order.coheight z = 1 → T 0 L z = Real.log (Nat.card (Y.residueField z)) := fun z hz =>
      hT.zero L z (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq 0 hY).1 z).1 hz)
    rw [recVal_congr H, recVal_congr H]
    exact GlobalTheory.T.arithmetic_curve_degree_independent_of_section k Y q hq hY N L r hr r' hr'
  | succ e => exact GlobalTheory.T.mixedHeightInduction_independent_of_section hInt hRec k Y q hq e hY T hT N L r hr r' hr'

theorem recVal_indep (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ) {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) (hY : topologicalKrullDim Y = (m + 1 : ℕ)) {T}
    (hT : IsMix q m T) (L L' : Fin m → HermLB q) (hL : ∀ a, (L a).Isometric (L' a)) (M M' : HermLB q)
    (hM : M.Isometric M') {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) {r' : M'.B.ι → Y.functionFieldˣ}
    (hr' : IsRatSec M'.B r') : recVal (T m L) L M hr = recVal (T m L') L' M' hr' := by
  have H := GlobalTheory.T.mixedHeight_inductive_rhs_symm_isometry_invariant hInt k Y q hq m hY T hT M r hr
  obtain ⟨r₃, hr₃, e₃⟩ := H.2.2 L' M' hM
  rw [H.1 L L' hL, ← e₃]
  exact recVal_indep_section hInt hRec m hq hY hT L' M' hr₃ hr'

end GlobalTheory.MixHt.StepVal

namespace GlobalTheory.MixHt.StepVal

variable {k : Type} [CommRing k]

theorem recVal_eq_of_same (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ)
    (hall : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T)
    {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsAmb p) {T} (hT : IsMix p m T) {x : X} (hx : HasDim x (m + 1))
    (M : HermLB p) (L : Fin m → HermLB p) {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k}
    (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q) (hg : i (genericPoint Y) = x)
    (M' M'' : HermLB q) (L' L'' : Fin m → HermLB q) (hM' : (M.pull i hi).Isometric M')
    (hM'' : (M.pull i hi).Isometric M'') (hL' : ∀ a, ((L a).pull i hi).Isometric (L' a))
    (hL'' : ∀ a, ((L a).pull i hi).Isometric (L'' a)) {r' : M'.B.ι → Y.functionFieldˣ} (hr' : IsRatSec M'.B r')
    {r'' : M''.B.ι → Y.functionFieldˣ} (hr'' : IsRatSec M''.B r'') :
    recVal (fun z => T m L (i z)) L' M' hr' = recVal (fun z => T m L (i z)) L'' M'' hr'' := by
  have hq : IsAmb q := by subst hi; exact hp.sub i
  have hY := dim_of_genericPoint hp i hx hg
  obtain ⟨T', hT'⟩ := hall k Y q hq
  have E : ∀ N : Fin m → HermLB q, (∀ a, ((L a).pull i hi).Isometric (N a)) → ∀ z : Y, Order.coheight z = 1 →
      T m L (i z) = T' m N z := fun N hN z hz =>
    GlobalTheory.T.mixedHeight_unique_restrict_closedSubscheme k X Y p q hp i hi m m T T' hT hT' m le_rfl le_rfl L N hN z
      (((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq m hY).1 z).1 hz)
  rw [recVal_congr (E L' hL'), recVal_congr (E L'' hL'')]
  exact recVal_indep hInt hRec m hq hY hT' L' L'' (fun a => (hL' a).symm.trans (hL'' a)) M' M''
    (hM'.symm.trans hM'') hr' hr''

theorem recVal_eq_of_two (hInt : ArchInteg) (hRec : ArchRecip) (m : ℕ)
    (hall : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T)
    {X : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsAmb p) {T} (hT : IsMix p m T) {x : X} (hx : HasDim x (m + 1))
    (M : HermLB p) (L : Fin m → HermLB p)
    {Y₁ : Scheme.{0}} [IsIntegral Y₁] [IsLocallyNoetherian Y₁] {q₁ : Y₁ ⟶ Sp k}
    (i₁ : Y₁ ⟶ X) [IsClosedImmersion i₁] (hi₁ : i₁ ≫ p = q₁) (hg₁ : i₁ (genericPoint Y₁) = x)
    (M₁ : HermLB q₁) (L₁ : Fin m → HermLB q₁) (hM₁ : (M.pull i₁ hi₁).Isometric M₁)
    (hL₁ : ∀ a, ((L a).pull i₁ hi₁).Isometric (L₁ a)) {r₁ : M₁.B.ι → Y₁.functionFieldˣ} (hr₁ : IsRatSec M₁.B r₁)
    {Y₂ : Scheme.{0}} [IsIntegral Y₂] [IsLocallyNoetherian Y₂] {q₂ : Y₂ ⟶ Sp k}
    (i₂ : Y₂ ⟶ X) [IsClosedImmersion i₂] (hi₂ : i₂ ≫ p = q₂) (hg₂ : i₂ (genericPoint Y₂) = x)
    (M₂ : HermLB q₂) (L₂ : Fin m → HermLB q₂) (hM₂ : (M.pull i₂ hi₂).Isometric M₂)
    (hL₂ : ∀ a, ((L a).pull i₂ hi₂).Isometric (L₂ a)) {r₂ : M₂.B.ι → Y₂.functionFieldˣ} (hr₂ : IsRatSec M₂.B r₂) :
    recVal (fun z => T m L (i₁ z)) L₁ M₁ hr₁ = recVal (fun z => T m L (i₂ z)) L₂ M₂ hr₂ := by
  obtain ⟨g, hiso, hgi, hη⟩ := GlobalTheory.T.exists_iso_closedImmersions_same_genericPoint X Y₁ Y₂ i₁ i₂ (hg₁.trans hg₂.symm)
  have hgq : g ≫ q₁ = q₂ := by rw [← hi₁, ← hi₂, ← Category.assoc, hgi]
  have hq₁ : IsAmb q₁ := by subst hi₁; exact hp.sub i₁
  have hq₂ : IsAmb q₂ := by subst hi₂; exact hp.sub i₂
  have hY₁ := dim_of_genericPoint hp i₁ hx hg₁
  have tr := GlobalTheory.T.inductive_height_formula_rhs_transport_iso k Y₁ Y₂ q₁ q₂ hq₁ hq₂ g hgq hη hiso m hY₁ (fun z => T m L (i₁ z)) L₁ M₁ r₁ hr₁
  rw [← tr]
  have hfun : (fun w => T m L (i₁ (g w))) = fun w => T m L (i₂ w) := by
    funext w
    rw [← hgi]
    simp
  rw [hfun]
  refine recVal_eq_of_same hInt hRec m hall hp hT hx M L i₂ hi₂ hg₂ _ _ _ _ ?_ hM₂ (fun a => ?_) hL₂ _ hr₂
  · exact (isometric_pull_pull' M i₁ hi₁ g hgq i₂ hi₂ hgi).symm.trans (hM₁.pull g hgq)
  · exact (isometric_pull_pull' (L a) i₁ hi₁ g hgq i₂ hi₂ hgi).symm.trans ((hL₁ a).pull g hgq)

theorem step_val : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k),
    IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ T,
    IsMix p m T → ∀ (x : X), HasDim x (m + 1) → ∀ (M : HermLB p) (L : Fin m → HermLB p), ∃ v : ℝ,
    ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = q), i (genericPoint Y) = x → ∀ (M' : HermLB q) (L' : Fin m → HermLB q),
    (M.pull i hi).Isometric M' → (∀ a, ((L a).pull i hi).Isometric (L' a)) →
    ∀ (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr := by
  intro hInt hRec m hall k _ X p hp T hT x hx M L
  classical
  by_cases H : ∃ v : ℝ, ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (q : Y ⟶ Sp k)
      (i : Y ⟶ X) (_ : IsClosedImmersion i) (hi : i ≫ p = q) (_ : i (genericPoint Y) = x) (M' : HermLB q)
      (L' : Fin m → HermLB q) (_ : (M.pull i hi).Isometric M') (_ : ∀ a, ((L a).pull i hi).Isometric (L' a))
      (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr
  · obtain ⟨v, Y₁, _, _, q₁, i₁, _, hi₁, hg₁, M₁, L₁, hM₁, hL₁, r₁, hr₁, rfl⟩ := H
    exact ⟨_, fun Y _ _ q i _ hi hg M' L' hM hL r hr =>
      recVal_eq_of_two hInt hRec m hall hp hT hx M L i₁ hi₁ hg₁ M₁ L₁ hM₁ hL₁ hr₁ i hi hg M' L' hM hL hr⟩
  · exact ⟨0, fun Y _ _ q i _ hi hg M' L' hM hL r hr =>
      absurd ⟨_, Y, ‹_›, ‹_›, q, i, ‹_›, hi, hg, M', L', hM, hL, r, hr, rfl⟩ H⟩

end GlobalTheory.MixHt.StepVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightRecursiveValueWellDefinedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedHeightRecursiveValue_well_defined : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ T, IsMix p m T → ∀ (x : X), HasDim x (m + 1) → ∀ (M : HermLB p) (L : Fin m → HermLB p), ∃ v : ℝ, ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q), i (genericPoint Y) = x → ∀ (M' : HermLB q) (L' : Fin m → HermLB q), (M.pull i hi).Isometric M' → (∀ a, ((L a).pull i hi).Isometric (L' a)) → ∀ (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr := by
  first | exact @GlobalTheory.MixHt.StepVal.step_val | exact GlobalTheory.MixHt.StepVal.step_val | (intros; apply GlobalTheory.MixHt.StepVal.step_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionSymmetricFirstTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionSymmetricFirstTwo
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.VSwap

theorem finite_coheight_one_mem_supp {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [CompactSpace Z]
    (D : CartierDiv Z) : {z : Z | Order.coheight z = 1 ∧ z ∈ D.supp}.Finite := by
  classical
  have : IsNoetherian Z := {}
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible D.supp.isClosed
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint Z).subset
    fun z hz => ?_
  obtain ⟨T, hT, hzT⟩ := Set.mem_sUnion.1 (hU.le hz.2)
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have h₁ : z ≤ (hi T hT).genericPoint := hg.specializes hzT
  have h₂ : (hi T hT).genericPoint < genericPoint Z := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint Z := (Specializes.antisymm e (genericPoint_specializes _)).eq
    exact D.genericPoint_notMem_supp (e' ▸ hU.ge (Set.mem_sUnion.2 ⟨T, hT, hg.mem⟩))
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e => hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz.1] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

section

variable (hI : ArchInteg) (hR : ArchRecip) {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
  [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) {e : ℕ} (hd : topologicalKrullDim Y = (e + 1 + 1 : ℕ))
  {T : ∀ d : ℕ, (Fin d → HermLB q) → Y → ℝ} (hT : IsMix q (e + 1) T) (L : Fin e → HermLB q)


include hI hR hq hd hT in
theorem add_first (N M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    {u : A.B.ι → Y.functionFieldˣ} (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ}
    (ht : IsRatSec (M.tens A).B t) :
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) (M.tens A) ht =
      recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr +
        recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) A hu := by
  have hp : IsRatSec (M.tens A).B (fun c : M.B.ι × A.B.ι => r c.1 * u c.2) := PtHtComb.isRatSec_tens hr hu
  rw [GlobalTheory.T.mixedHeightInduction_independent_of_section hI hR k Y q hq e hd T hT (M.tens A) (Fin.cons N L) t ht _ hp]
  exact GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k Y q hq (e + 1) hd (T (e + 1) (Fin.cons N L)) (Fin.cons N L) M A r hr u hu _ hp
    fun _ _ _ _ => rfl


include hI hR hq hd hT in
theorem swap_of_sec (M N : HermLB q) (t : N.B.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) {r' : N.B.ι → Y.functionFieldˣ} (hr' : IsRatSec N.B r') :
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr =
      recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  have : IsNoetherian Y := hq.isNoetherian
  set S : Set Y := {genericPoint Y} ∪ {z | Order.coheight z = 1 ∧ z ∈ (divOfSec N.isLB t ht).supp} with hS
  have hfin : S.Finite := (Set.finite_singleton _).union (finite_coheight_one_mem_supp _)
  obtain ⟨B, s, v, hsS, hvS⟩ := GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set k Y q hq M S hfin
  have hs : genericPoint Y ∈ nonzeroLocus s := hsS (Set.mem_union_left _ rfl)
  have hv : genericPoint Y ∈ nonzeroLocus v := hvS (Set.mem_union_left _ rfl)
  have hcov : ∀ z : Y, Order.coheight z = 1 → z ∉ nonzeroLocus t → z ∈ S := fun z hz hzt =>
    Set.mem_union_right _ ⟨hz, by_contra fun h => hzt ((notMem_supp_divOfSec (hL := N.isLB) (s := t) (hs := ht)).1 h)⟩
  have R1 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT (M.tens B) N L s t hs ht fun z hz =>
    (em (z ∈ nonzeroLocus t)).elim Or.inr fun h => Or.inl (hsS (hcov z hz h))
  have R2 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT B N L v t hv ht fun z hz =>
    (em (z ∈ nonzeroLocus t)).elim Or.inr fun h => Or.inl (hvS (hcov z hz h))
  have A1 := add_first hI hR hq hd hT L N M B hr (isRatSec_ratOfSec v hv) (isRatSec_ratOfSec s hs)
  have A2 := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT N (ratOfSec t ht) (isRatSec_ratOfSec t ht) M B L
  rw [GlobalTheory.T.mixedHeightInduction_independent_of_section hI hR k Y q hq e hd T hT N (Fin.cons M L) r' hr' _ (isRatSec_ratOfSec t ht)]
  linarith

end

theorem main : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T →
    ∀ (M N : HermLB q) (L : Fin e → HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r)
    (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'),
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr =
      recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  intro hI hR k _ Y _ _ q hq e hd T hT M N L r hr r' hr'
  obtain ⟨A, s, u, hsS, huS⟩ := GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set k Y q hq N {genericPoint Y} (Set.finite_singleton _)
  have hs : genericPoint Y ∈ nonzeroLocus s := hsS rfl
  have hu : genericPoint Y ∈ nonzeroLocus u := huS rfl
  have hp := PtHtComb.isRatSec_tens hr' (isRatSec_ratOfSec u hu)
  have K1 := swap_of_sec hI hR hq hd hT L M (N.tens A) s hs hr hp
  have K2 := swap_of_sec hI hR hq hd hT L M A u hu hr (isRatSec_ratOfSec u hu)
  have A3 := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT M r hr N A L
  have A4 := add_first hI hR hq hd hT L M N A hr' (isRatSec_ratOfSec u hu) hp
  linarith

end GlobalTheory.MixHt.VSwap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionSymmetricFirstTwoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedHeightInduction_symmetric_firstTwo : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr = recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  first | exact @GlobalTheory.MixHt.VSwap.main | exact GlobalTheory.MixHt.VSwap.main | (intros; apply GlobalTheory.MixHt.VSwap.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermInvariantOfConsSwapAndTail
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermInvariantOfConsSwapAndTail
open Equiv

theorem GlobalTheory.perm_invariant_of_cons_swap :
  ∀ (α : Type 1) (n : ℕ) (F : (Fin (n + 2) → α) → ℝ), (∀ (a : α) (L : Fin (n + 1) → α) (e : Equiv.Perm (Fin (n + 1))), F (Fin.cons a fun i => L (e i)) = F (Fin.cons a L)) → (∀ (a b : α) (L : Fin n → α), F (Fin.cons a (Fin.cons b L : Fin (n + 1) → α)) = F (Fin.cons b (Fin.cons a L : Fin (n + 1) → α))) → ∀ (L : Fin (n + 2) → α) (e : Equiv.Perm (Fin (n + 2))), F (fun i => L (e i)) = F L := by
  intro α n F h1 h2
  let S : Subgroup (Equiv.Perm (Fin (n+2))) :=
    { carrier := {σ | ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L}
      mul_mem' := by
        intro σ τ hσ hτ
        have hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := hσ
        have hτ' : ∀ L : Fin (n+2) → α, F (fun i => L (τ i)) = F L := hτ
        show ∀ L : Fin (n+2) → α, F (fun i => L ((σ * τ) i)) = F L
        intro L
        calc F (fun i => L ((σ * τ) i)) = F (fun i => L (σ (τ i))) := rfl
          _ = F (fun j => L (σ j)) := hτ' (fun j => L (σ j))
          _ = F L := hσ' L
      one_mem' := by
        show ∀ L : Fin (n+2) → α, F (fun i => L ((1 : Equiv.Perm (Fin (n+2))) i)) = F L
        intro L; rfl
      inv_mem' := by
        intro σ hσ
        have hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := hσ
        show ∀ L : Fin (n+2) → α, F (fun i => L (σ⁻¹ i)) = F L
        intro L
        calc F (fun i => L (σ⁻¹ i)) = F (fun i => L (σ⁻¹ (σ i))) := (hσ' (fun j => L (σ⁻¹ j))).symm
          _ = F L := by simp }
  have memS : ∀ σ, σ ∈ S ↔ ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := fun σ => Iff.rfl
  have hfix : ∀ e : Equiv.Perm (Fin (n+1)), Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) ∈ S := by
    intro e
    rw [memS]
    intro L
    have hc : (fun i => L (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) i)) = Fin.cons (L 0) (fun i => Fin.tail L (e i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Equiv.Perm.decomposeFin_symm_apply_succ, Fin.tail]
    rw [hc, h1 (L 0) (Fin.tail L) e, Fin.cons_self_tail]
  have hswap : Equiv.swap (0 : Fin (n+2)) 1 ∈ S := by
    rw [memS]
    intro L
    have e1 : L = Fin.cons (L 0) (Fin.cons (L 1) (fun i => L i.succ.succ) : Fin (n+1) → α) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun k => ?_) j
        · rfl
        · rfl
    have e2 : (fun i => L (Equiv.swap (0 : Fin (n+2)) 1 i)) = Fin.cons (L 1) (Fin.cons (L 0) (fun i => L i.succ.succ) : Fin (n+1) → α) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · refine Fin.cases ?_ (fun k => ?_) j
        · simp
        · have a1 : (k.succ.succ : Fin (n+2)) ≠ 0 := Fin.succ_ne_zero _
          have a2 : (k.succ.succ : Fin (n+2)) ≠ 1 := by
            intro h
            rw [← Fin.succ_zero_eq_one] at h
            exact Fin.succ_ne_zero _ (Fin.succ_injective _ h)
          simp [Equiv.swap_apply_of_ne_of_ne a1 a2]
    rw [e2, ← h2 (L 0) (L 1)]
    exact congrArg F e1.symm
  have hp : ∀ p : Fin (n+2), Equiv.swap (0 : Fin (n+2)) p ∈ S := by
    intro p
    refine Fin.cases ?_ (fun k => ?_) p
    · rw [Equiv.swap_self]; exact S.one_mem
    · have h0 : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 0 = 0 := by simp
      have h1' : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 1 = k.succ := by
        rw [← Fin.succ_zero_eq_one, Equiv.Perm.decomposeFin_symm_apply_succ]
        simp
      have hc := Equiv.swap_apply_apply (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k)) 0 1
      rw [h0, h1'] at hc
      rw [hc]
      exact S.mul_mem (S.mul_mem (hfix _) hswap) (S.inv_mem (hfix _))
  have hdec : ∀ (p : Fin (n+2)) (e : Equiv.Perm (Fin (n+1))),
      Equiv.Perm.decomposeFin.symm (p, e) = Equiv.swap 0 p * Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) := by
    intro p e
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
  intro L e
  have he : e ∈ S := by
    rw [← Equiv.Perm.decomposeFin.symm_apply_apply e]
    rcases Equiv.Perm.decomposeFin e with ⟨p, e'⟩
    rw [hdec]
    exact S.mul_mem (hp p) (hfix e')
  exact (memS e).1 he L
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermInvariantOfConsSwapAndTailStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perm_invariant_of_cons_swap_and_tail : ∀ (α : Type 1) (n : ℕ) (F : (Fin (n + 2) → α) → ℝ), (∀ (a : α) (L : Fin (n + 1) → α) (e : Equiv.Perm (Fin (n + 1))), F (Fin.cons a fun i => L (e i)) = F (Fin.cons a L)) → (∀ (a b : α) (L : Fin n → α), F (Fin.cons a (Fin.cons b L : Fin (n + 1) → α)) = F (Fin.cons b (Fin.cons a L : Fin (n + 1) → α))) → ∀ (L : Fin (n + 2) → α) (e : Equiv.Perm (Fin (n + 2))), F (fun i => L (e i)) = F L := by
  first | exact @GlobalTheory.perm_invariant_of_cons_swap | exact GlobalTheory.perm_invariant_of_cons_swap | (intros; apply GlobalTheory.perm_invariant_of_cons_swap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixedHeightByInductionSucc
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.Step

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def extend (m : ℕ) (T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ) (V : (Fin (m + 1) → HermLB p) → X → ℝ) :
    ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ :=
  fun d L x => if h : d = m + 1 then V (fun a => L (Fin.cast h.symm a)) x else T d L x

theorem extend_of_ne {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} {V : (Fin (m + 1) → HermLB p) → X → ℝ}
    {d : ℕ} (h : d ≠ m + 1) (L : Fin d → HermLB p) (x : X) : extend m T V d L x = T d L x := dif_neg h

theorem extend_self {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} {V : (Fin (m + 1) → HermLB p) → X → ℝ}
    (L : Fin (m + 1) → HermLB p) (x : X) : extend m T V (m + 1) L x = V L x := by
  simp [extend]

theorem recVal_congr {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {e : ℕ} {h h' : Y → ℝ}
    (H : ∀ z, Order.coheight z = 1 → h z = h' z) (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : recVal h L M hr = recVal h' L M hr := by
  unfold recVal
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  · rw [H z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)]

theorem isRatSec_tens_mul {Z : Scheme.{0}} [IsIntegral Z] {A B : LB Z} {r : A.ι → Z.functionFieldˣ}
    {s : B.ι → Z.functionFieldˣ} (hr : IsRatSec A r) (hs : IsRatSec B s) :
    IsRatSec (CechPic.tens A B) fun c : A.ι × B.ι => r c.1 * s c.2 := fun (c c' : A.ι × B.ι) h => by
  have h₁ : genericPoint Z ∈ A.U c.1 ⊓ A.U c'.1 := ⟨h.1.1, h.2.1⟩
  have h₂ : genericPoint Z ∈ B.U c.2 ⊓ B.U c'.2 := ⟨h.1.2, h.2.2⟩
  have e : fnOf _ h ((CechPic.tens A B).g c c' : Γ(Z, _)) =
      fnOf _ h₁ (A.g c.1 c'.1 : Γ(Z, _)) * fnOf _ h₂ (B.g c.2 c'.2 : Γ(Z, _)) := by
    change fnOf _ h ((res _ (A.g c.1 c'.1)).val * (res _ (B.g c.2 c'.2)).val) = _
    exact (map_mul (fnOf _ h) _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ h _) (fnOf_resG _ h _))
  rw [Units.val_mul, Units.val_mul, hr c.1 c'.1 h₁, hs c.2 c'.2 h₂, e]
  ring

theorem isMix_succ : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∃ T, IsMix p (m + 1) T := by
  intro hI hR m hm k _ X p hp
  classical
  haveI : IsNoetherian X := hp.isNoetherian
  obtain ⟨T, hT⟩ := hm k X p hp
  choose v hv using GlobalTheory.T.mixedHeightRecursiveValue_well_defined hI hR m hm k X p hp T hT
  have hD := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp
  have hdimi : ∀ (Y : Scheme.{0}) [IsIntegral Y] (i : Y ⟶ X) [IsClosedImmersion i] (d : ℕ),
      topologicalKrullDim Y = (d : ℕ) → HasDim (i (genericPoint Y)) d := fun Y _ i _ d h =>
    (hD.2.2.2.2.1 Y i (genericPoint Y) d).2 ((hD.2.2.2.2.2 Y d).2 h)
  have hcd : ∀ x : X, HasDim x (m + 1) → topologicalKrullDim (clo x) = ((m + 1 : ℕ) : WithBot ℕ∞) := fun x hx =>
    (hD.2.2.2.2.2 (clo x) (m + 1)).1
      ((hD.2.2.2.2.1 (clo x) (cloι x) (genericPoint (clo x)) (m + 1)).1 (by rw [cloι_genericPoint]; exact hx))
  have E : ∀ (x : X) (hx : HasDim x (m + 1)) (M : HermLB p) (L : Fin m → HermLB p)
      (M' : HermLB (cloι x ≫ p)) (L' : Fin m → HermLB (cloι x ≫ p)),
      (M.pull (cloι x) rfl).Isometric M' → (∀ a, ((L a).pull (cloι x) rfl).Isometric (L' a)) →
      ∀ (r : M'.B.ι → (clo x).functionFieldˣ) (hr : IsRatSec M'.B r)
        (TY : ∀ d : ℕ, (Fin d → HermLB (cloι x ≫ p)) → clo x → ℝ), IsMix (cloι x ≫ p) m TY →
      v x hx M L = recVal (TY m L') L' M' hr := by
    intro x hx M L M' L' hM hL r hr TY hTY
    rw [hv x hx M L (clo x) (cloι x ≫ p) (cloι x) rfl (cloι_genericPoint x) M' L' hM hL r hr]
    refine recVal_congr (fun z hz => ?_) L' M' hr
    have hz' : HasDim z m := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k (clo x) (cloι x ≫ p) (hp.sub _) m (hcd x hx)).1 z).1 hz
    exact GlobalTheory.T.mixedHeight_unique_restrict_closedSubscheme k X (clo x) p (cloι x ≫ p) hp (cloι x) rfl m m T TY hT hTY m le_rfl le_rfl L L' hL z hz'
  let V : (Fin (m + 1) → HermLB p) → X → ℝ := fun L x =>
    if hx : HasDim x (m + 1) then v x hx (L 0) (Fin.tail L) else 0
  have hV : ∀ (L : Fin (m + 1) → HermLB p) (x : X) (hx : HasDim x (m + 1)),
      extend m T V (m + 1) L x = v x hx (L 0) (Fin.tail L) := fun L x hx => by
    rw [extend_self]
    exact dif_pos hx
  have hsym : ∀ (x : X) (hx : HasDim x (m + 1)) (L : Fin (m + 1) → HermLB p) (e : Equiv.Perm (Fin (m + 1))),
      v x hx (L (e 0)) (Fin.tail fun a => L (e a)) = v x hx (L 0) (Fin.tail L) := by
    intro x hx L e
    obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
    have hq : IsAmb (cloι x ≫ p) := hp.sub (cloι x)
    have hdx := hcd x hx
    let F : (Fin (m + 1) → HermLB p) → ℝ := fun L => v x hx (L 0) (Fin.tail L)
    change F (fun a => L (e a)) = F L
    rcases m with _ | n
    · have : (fun a => L (e a)) = L := funext fun a => congrArg L (@Subsingleton.elim (Fin 1) _ _ _)
      rw [this]
    · refine GlobalTheory.T.perm_invariant_of_cons_swap_and_tail (HermLB p) n F (fun a L τ => ?_) (fun a b L => ?_) L e
      · simp only [F, Fin.cons_zero, Fin.tail_cons]
        obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (a.pull (cloι x) rfl).isLB
        rw [E x hx a (fun i => L (τ i)) (a.pull (cloι x) rfl) (fun i => (L (τ i)).pull (cloι x) rfl)
            (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY,
          E x hx a L (a.pull (cloι x) rfl) (fun i => (L i).pull (cloι x) rfl)
            (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY]
        exact (GlobalTheory.T.mixedHeight_inductive_rhs_symm_isometry_invariant hI k (clo x) (cloι x ≫ p) hq (n + 1) hdx TY hTY _ ra hra).2.1
          (fun i => (L i).pull (cloι x) rfl) τ
      · simp only [F, Fin.cons_zero, Fin.tail_cons]
        obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (a.pull (cloι x) rfl).isLB
        obtain ⟨rb, hrb⟩ := Cartier.exists_isRatSec (b.pull (cloι x) rfl).isLB
        have iso : ∀ (c : HermLB p) (j : Fin (n + 1)), ((Fin.cons c L : Fin (n + 1) → HermLB p) j).pull (cloι x) rfl |>.Isometric
            ((Fin.cons (c.pull (cloι x) rfl) (fun i => (L i).pull (cloι x) rfl) : Fin (n + 1) → HermLB (cloι x ≫ p)) j) := by
          intro c j
          refine Fin.cases ?_ (fun i => ?_) j <;> simp only [Fin.cons_zero, Fin.cons_succ] <;> exact HermLB.Isometric.refl _
        rw [E x hx a _ (a.pull (cloι x) rfl) _ (HermLB.Isometric.refl _) (iso b) ra hra TY hTY,
          E x hx b _ (b.pull (cloι x) rfl) _ (HermLB.Isometric.refl _) (iso a) rb hrb TY hTY]
        exact GlobalTheory.T.mixedHeightInduction_symmetric_firstTwo hI hR k (clo x) (cloι x ≫ p) hq n hdx TY hTY _ _ _ ra hra rb hrb
  refine ⟨extend m T V, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro d L M x hd hx hLM
    by_cases h : d = m + 1
    · subst h
      rw [hV _ _ hx, hV _ _ hx]
      obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
      obtain ⟨r, hr⟩ := Cartier.exists_isRatSec ((L 0).pull (cloι x) rfl).isLB
      rw [E x hx (L 0) (Fin.tail L) ((L 0).pull (cloι x) rfl) (fun a => (Fin.tail L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr TY hTY,
        E x hx (M 0) (Fin.tail M) ((L 0).pull (cloι x) rfl) (fun a => (Fin.tail L a).pull (cloι x) rfl)
          ((hLM 0).symm.pull _ _) (fun a => (hLM a.succ).symm.pull _ _) r hr TY hTY]
    · rw [extend_of_ne h, extend_of_ne h]
      exact hT.iso d L M x (by omega) hx hLM
  · intro d L e x hd hx
    by_cases h : d = m + 1
    · subst h
      rw [hV _ _ hx, hV _ _ hx]
      exact hsym x hx L e
    · rw [extend_of_ne h, extend_of_ne h]
      exact hT.symm d L e x (by omega) hx
  · intro d A B L x hd hx
    by_cases h : d + 1 = m + 1
    · obtain rfl : d = m := by omega
      rw [hV _ _ hx, hV _ _ hx, hV _ _ hx]
      simp only [Fin.cons_zero, Fin.tail_cons]
      obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
      obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (A.pull (cloι x) rfl).isLB
      obtain ⟨rb, hrb⟩ := Cartier.exists_isRatSec (B.pull (cloι x) rfl).isLB
      have ht := isRatSec_tens_mul hra hrb
      rw [E x hx (A.tens B) L ((A.pull (cloι x) rfl).tens (B.pull (cloι x) rfl)) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.isometric_pull_tens A B _ _) (fun _ => HermLB.Isometric.refl _) _ ht TY hTY,
        E x hx A L (A.pull (cloι x) rfl) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY,
        E x hx B L (B.pull (cloι x) rfl) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) rb hrb TY hTY]
      exact GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k (clo x) (cloι x ≫ p) (hp.sub _) d (hcd x hx) _ _ _ _ ra hra rb hrb _ ht
        fun _ _ _ _ => rfl
    · rw [extend_of_ne h, extend_of_ne h, extend_of_ne h]
      exact hT.add d A B L x (by omega) hx
  · intro L x hx
    rw [extend_of_ne (by omega)]
    exact hT.zero L x hx
  · intro Y _ _ q i _ hi e he hdim M L M' L' hM hL r hr
    have hfun : (fun z => extend m T V e L (i z)) = fun z => T e L (i z) :=
      funext fun z => extend_of_ne (by omega) L (i z)
    rw [hfun]
    by_cases h : e + 1 = m + 1
    · obtain rfl : e = m := by omega
      have hx := hdimi Y i (e + 1) hdim
      rw [hV _ _ hx]
      simp only [Fin.cons_zero, Fin.tail_cons]
      exact hv _ hx M L Y q i hi rfl M' L' hM hL r hr
    · rw [extend_of_ne h]
      exact hT.recur Y q i hi e (by omega) hdim M L M' L' hM hL r hr

end GlobalTheory.MixHt.Step
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixedHeightByInductionSuccStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMixedHeightByInduction_succ : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∃ T, IsMix p (m + 1) T := by
  first | exact @GlobalTheory.MixHt.Step.isMix_succ | exact GlobalTheory.MixHt.Step.isMix_succ | (intros; apply GlobalTheory.MixHt.Step.isMix_succ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedHeightOfArchimedeanIntegrals
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem exists_isMix_of_arch : ArchInteg → ArchRecip →
    (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) := by
  intro hI hR
  have key : ∀ m : ℕ, ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T := by
    intro m
    induction m with
    | zero => intro k _ Y q _; exact ⟨_, isMix_zero q⟩
    | succ m ih => exact GlobalTheory.T.isMixedHeightByInduction_succ hI hR m ih
  intro k _ Y q h m
  exact key m k Y q h

end GlobalTheory.MixHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedHeightOfArchimedeanIntegralsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixedHeight_of_archimedean_integrals : ArchInteg → ArchRecip → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) := by
  first | exact @GlobalTheory.MixHt.exists_isMix_of_arch | exact GlobalTheory.MixHt.exists_isMix_of_arch | (intros; apply GlobalTheory.MixHt.exists_isMix_of_arch <;> assumption)
end
