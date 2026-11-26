module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelAffineCoverRadical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupAbelianWhereTrivialisationsUnits

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVariety
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem isEmpty_cxPts_of_algebra_zmod {k : Type} [CommRing k] {Y : Scheme.{0}} (q : Y ⟶ Sp k)
    (l : ℕ) [Fact l.Prime] (_ : Algebra (ZMod l) Γ(Y, ⊤)) (σ : k →+* ℂ) : IsEmpty (CxPts q σ) := by
  refine ⟨fun y => ?_⟩
  let f : ZMod l →+* ℂ := (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp
    (y.1.appTop.hom.comp (algebraMap (ZMod l) Γ(Y, ⊤)))
  have h := map_natCast f l
  rw [ZMod.natCast_self, map_zero] at h
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h.symm

theorem amb_vertical_or_arithVar : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ d : ℕ, topologicalKrullDim Y = d → (∃ (l : ℕ) (_ : Fact l.Prime), Nonempty (Algebra (ZMod l) Γ(Y, ⊤)) ∧ ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) ∨ ∃ e : ℕ, d = e + 1 ∧ IsArithVar q e := by
  intro k _ Y _ q hq d hd
  obtain ⟨ℓ, _⟩ := CharP.exists Γ(Y, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Y, ⊤) ℓ with hℓ | rfl
  · have : Fact ℓ.Prime := ⟨hℓ⟩
    exact .inl ⟨ℓ, this, ⟨ZMod.algebra _ ℓ⟩, fun σ => isEmpty_cxPts_of_algebra_zmod q ℓ (ZMod.algebra _ ℓ) σ⟩
  · have hc := CharP.charP_to_charZero Γ(Y, ⊤)
    obtain _ | e := d
    · exact absurd (by simpa using hd) (dim_ne_zero_of_isProjOver q hq.isProjOver hq.finite hc)
    · exact .inr ⟨e, rfl, hq.isDomain, hq.finite, ‹_›, hq.isProjOver,
        (flat_int_iff_charZero _).2 hc, hd⟩

end GlobalTheory.MixHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVarietyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ d : ℕ, topologicalKrullDim Y = d → (∃ (l : ℕ) (_ : Fact l.Prime), Nonempty (Algebra (ZMod l) Γ(Y, ⊤)) ∧ ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) ∨ ∃ e : ℕ, d = e + 1 ∧ IsArithVar q e := by
  first | exact @GlobalTheory.MixHt.amb_vertical_or_arithVar | exact GlobalTheory.MixHt.amb_vertical_or_arithVar | (intros; apply GlobalTheory.MixHt.amb_vertical_or_arithVar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackSectionZerosNormMultiplicities
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackSectionZerosNormMultiplicities
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mix

theorem exists_secPull_props : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q) (M : MLine p σ) (s : M.B.Sec), ∃ s' : (M.pull π hπ).B.Sec, nonzeroLocus s' = π ⁻¹ᵁ nonzeroLocus s ∧ (∀ y, (M.pull π hπ).φ.nsq (secVal q σ s') y = M.φ.nsq (secVal p σ s) (ptMap π hπ σ y)) ∧ ∀ [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] (hη : π (genericPoint Y) ⤳ genericPoint X) (hs : genericPoint X ∈ nonzeroLocus s) (hs' : genericPoint Y ∈ nonzeroLocus s') (w : Y) (i : M.B.ι), π w ∈ M.B.U i → (divOfSec (M.pull π hπ).φ.isLB s' hs').mult w = Scheme.ord (TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField)) w := by
  intro k _ X Y p q σ π hπ M s
  refine ⟨GlobalTheory.Cartier.secPull s π, GlobalTheory.Cartier.nonzeroLocus_secPull s π, fun y =>
    Weight.nsq_pull_secPull M.φ π hπ s y, ?_⟩
  intro _ _ _ hη hs hs' w i hw
  have hc : w ∈ (M.B.pull π).U (fun _ => i) := by
    rw [GlobalTheory.Cartier.pull_U]; exact hw
  have hg : genericPoint Y ∈ (M.B.pull π).U (fun _ => i) := gen_mem hc
  have hg' : genericPoint Y ∈ π ⁻¹ᵁ M.B.U i := by
    have h := hg
    rw [GlobalTheory.Cartier.pull_U] at h
    exact h
  have h0 : genericPoint X ∈ M.B.U i := gen_mem hw
  have e : ((ratOfSec (L := (M.pull π hπ).B) (GlobalTheory.Cartier.secPull s π) hs' fun _ => i : Y.functionFieldˣ) :
      Y.functionField) = TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField) := by
    rw [val_ratOfSec h0, TrueGeo.SmallSec.fnMap_fnOf π hη h0 hg']
    exact (val_ratOfSec (L := M.B.pull π) (s := GlobalTheory.Cartier.secPull s π) (hs := hs') hg).trans
      (fnOf_resG (GlobalTheory.Cartier.pull_U M.B π fun _ => i).le hg _)
  exact ((presents_divOfRatSec _ _).isEqn (fun _ => i) w hc).mult_eq.trans (congrArg (Scheme.ord · w) e)

end GlobalTheory.Mix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackSectionZerosNormMultiplicitiesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_section_zeros_norm_multiplicities : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q) (M : MLine p σ) (s : M.B.Sec), ∃ s' : (M.pull π hπ).B.Sec, nonzeroLocus s' = π ⁻¹ᵁ nonzeroLocus s ∧ (∀ y, (M.pull π hπ).φ.nsq (secVal q σ s') y = M.φ.nsq (secVal p σ s) (ptMap π hπ σ y)) ∧ ∀ [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] (hη : π (genericPoint Y) ⤳ genericPoint X) (hs : genericPoint X ∈ nonzeroLocus s) (hs' : genericPoint Y ∈ nonzeroLocus s') (w : Y) (i : M.B.ι), π w ∈ M.B.U i → (divOfSec (M.pull π hπ).φ.isLB s' hs').mult w = Scheme.ord (TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField)) w := by
  first | exact @GlobalTheory.Mix.exists_secPull_props | exact GlobalTheory.Mix.exists_secPull_props | (intros; apply GlobalTheory.Mix.exists_secPull_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecAppLETopEq
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.CechKSSmul

theorem valR_mul_of_le {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : valR x O (a * b) = valR x O a * valR x O b := by
  simp only [valR, dif_pos h, map_mul]

theorem valR_sub_of_le {A : Type} [CommRing A] {Z : Scheme.{0}} (x : Sp A ⟶ Z) (O : Z.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ O) (a b : Γ(Z, O)) : valR x O (a - b) = valR x O a - valR x O b := by
  simp only [valR, dif_pos h, map_sub]

theorem valR_appLE_comp {A : Type} [CommRing A] {Y Z : Scheme.{0}} (x : Sp A ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens)
    (W : Y.Opens) (e : W ≤ g ⁻¹ᵁ U) (h : ⊤ ≤ x ⁻¹ᵁ W) (a : Γ(Z, U)) :
    valR x W ((g.appLE U W e).hom a) = valR (x ≫ g) U a := by
  have h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := fun y hy => e (h hy)
  simp only [valR, dif_pos h, dif_pos h']
  exact congrArg (fun q => (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (q.hom a))
    (Scheme.Hom.appLE_comp_appLE x g U W ⊤ e h)

theorem fromSpec_appLE_top_eq {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  exact (Spec Γ(X, U)).presheaf.map_id _

theorem valR_spMap_chart {X : Scheme.{0}} (U : X.affineOpens) {S : Type} [CommRing S] (φ : Γ(X, U.1) →+* S)
    (r : Γ(X, U.1)) : valR (spMap φ ≫ chart U) U.1 r = φ r := by
  have h1 : ⊤ ≤ (chart U) ⁻¹ᵁ U.1 := by
    show ⊤ ≤ U.2.fromSpec ⁻¹ᵁ U.1
    rw [U.2.fromSpec_preimage_self]
  rw [← valR_appLE_comp (spMap φ) (chart U) U.1 ⊤ h1 (fun _ _ => trivial)]
  have e : (chart U).appLE U.1 ⊤ h1 = (Scheme.ΓSpecIso Γ(X, U.1)).inv := by
    exact fromSpec_appLE_top_eq U.2 h1
  rw [e]
  simp only [valR, dif_pos (show ⊤ ≤ spMap φ ⁻¹ᵁ ⊤ from fun _ _ => trivial)]
  have e2 : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop :=
    Scheme.Hom.appLE_eq_app (f := spMap φ) (U := ⊤)
  rw [e2]
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso Γ(X, U.1)).inv.hom r)) n
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [this]
  congr 1
  exact (Scheme.ΓSpecIso Γ(X, U.1)).inv_hom_id_apply r

theorem resG_appLE' {Y Z : Scheme.{0}} (f : Y ⟶ Z) {W : Z.Opens} {O O' : Y.Opens} (h : O' ≤ O) (e : O ≤ f ⁻¹ᵁ W)
    (a : Γ(Z, W)) : resG Y h ((f.appLE W O e).hom a) = (f.appLE W O' (h.trans e)).hom a := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

end GlobalTheory.CechKSSmul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorGradedLengthSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorGradedLengthSmooth
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem leadMinor_re_pos_of_posDef {s : ℕ} {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (j : ℕ) :
    0 < (leadMinor G j).re := by
  have hsub : (G.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val).PosDef :=
    hG.submatrix Subtype.val_injective
  have h := hsub.det_pos
  unfold leadMinor
  exact (Complex.pos_iff.mp h).1

theorem contDiffAt_leadMinor {n s : ℕ} {G : V n → Matrix (Fin s) (Fin s) ℂ} {v : V n}
    (h : MContDiffAt ∞ G v) (j : ℕ) : ContDiffAt ℝ ∞ (fun x => leadMinor (G x) j) v :=
  (h.submatrix _ _).det

theorem ldPart_grD_smooth : ∀ (n s : ℕ) (G : V n → Matrix (Fin s) (Fin s) ℂ) (v : V n), MContDiffAt ∞ G v → (G v).PosDef →
    MContDiffAt ∞ (fun x => ldPart (G x)) v ∧ ∀ i, ContDiffAt ℝ ∞ (fun x => grD (G x) i) v := by
  intro n s G v hG hp
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · have hnum : ContDiffAt ℝ ∞ (fun x => ((G x).submatrix
        (fun a : {a : Fin s // (a : ℕ) < j + 1} => if a.1 = j then i else a.1) Subtype.val).det) v :=
      (hG.submatrix _ _).det
    have hden := contDiffAt_leadMinor hG (j : ℕ)
    have hne : leadMinor (G v) j ≠ 0 := fun h0 => by
      have := leadMinor_re_pos_of_posDef hp j
      rw [h0] at this; simp at this
    simp only [ldPart, Matrix.of_apply]
    exact hnum.mul (hden.inv hne)
  · have hnum : ContDiffAt ℝ ∞ (fun x => (leadMinor (G x) (i + 1)).re) v :=
      Complex.reCLM.contDiff.contDiffAt.comp v (contDiffAt_leadMinor hG _)
    have hden : ContDiffAt ℝ ∞ (fun x => (leadMinor (G x) i).re) v :=
      Complex.reCLM.contDiff.contDiffAt.comp v (contDiffAt_leadMinor hG _)
    exact hnum.div hden (leadMinor_re_pos_of_posDef hp i).ne'

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorGradedLengthSmoothStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth : ∀ (n s : ℕ) (G : V n → Matrix (Fin s) (Fin s) ℂ) (v : V n), MContDiffAt ∞ G v → (G v).PosDef → MContDiffAt ∞ (fun x => ldPart (G x)) v ∧ ∀ i, ContDiffAt ℝ ∞ (fun x => grD (G x) i) v := by
  first | exact @GlobalTheory.ChernCalc.ldPart_grD_smooth | exact GlobalTheory.ChernCalc.ldPart_grD_smooth | (intros; apply GlobalTheory.ChernCalc.ldPart_grD_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMumfordClassEqZeroAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMumfordClassEqZeroAmple
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem memKL_of_lam_geom_eq_zero {K : Type} [Field K] (A : AbVar K) {L : LB A.X.left} (hL : L.IsLB)
    (x : A.Pt) (h : AbVar.lam (cls L hL) (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0) :
    MemKL A.X L x := by
  set P := ptOver K (AlgebraicClosure K)
  have h1 := congrArg (CechPic.pull (lift (snd P A.X) (fst P A.X)).left) h
  rw [lam_eq, pull_lam, map_zero, lift_fst, lift_snd_assoc, lam_comm, ← lam_eq] at h1
  have h0 : CechPic.pull (fst P A.X ≫ x).left (cls L hL) = 0 := by
    rw [Over.comp_left, pull_comp, GlobalTheory.PrimitiveOverField.pic_field (K := AlgebraicClosure K) (CechPic.pull x.left (cls L hL)), map_zero]
  rw [AbVar.lam, h0, sub_zero] at h1
  intro p
  refine ⟨⊤, trivial, ?_⟩
  have hD : (Out.translDiff A.X L x).IsLB := LB.isLB_linComb hL _ _
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  refine (congrArg _ ?_).trans (map_zero _)
  refine (cls_linComb hL _ _ hD).trans (Eq.trans ?_ h1)
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

end GlobalTheory.AV.AbVar

theorem GlobalTheory.AV.AbVar.finite_lam_eq_zero : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c → Finite {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0} := by
  intro K _ A c ⟨L, hL, ha, hc⟩
  subst hc
  obtain ⟨H, _, i, -, hmono, hfin, -, hH⟩ := GlobalTheory.kernel_finiteFlat_subgroup K A.X A.ab L hL ha
  have hF := GlobalTheory.FlagCovQF.finite_points H.hom (AlgebraicClosure K) (spMap (algebraMap K (AlgebraicClosure K)))
  haveI := hF.to_subtype
  have hz : ∀ x : {x : A.Pt // AbVar.lam (cls L hL) (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0},
      ∃ z : ptOver K (AlgebraicClosure K) ⟶ H, z ≫ i = x.1 := fun x =>
    (hH _ x.1).1 (memKL_of_lam_geom_eq_zero A hL x.1 x.2)
  choose z hz using hz
  refine Finite.of_injective (fun x => (⟨(z x).left, Over.w (z x)⟩ :
    {y : Sp (AlgebraicClosure K) ⟶ H.left | y ≫ H.hom = spMap (algebraMap K (AlgebraicClosure K))})) ?_
  intro a b hab
  have e : z a = z b := Over.OverMorphism.ext (congrArg Subtype.val hab)
  exact Subtype.ext ((hz a).symm.trans (e ▸ hz b))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMumfordClassEqZeroAmpleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_mumfordClass_eq_zero_ample : ∀ (K : Type) [Field K] (A : AbVar K) (c : Pic A.X.left), IsAmpleCls c → Finite {x : A.Pt // AbVar.lam c (fst A.X (ptOver K (AlgebraicClosure K))) (snd A.X _ ≫ x) = 0} := by
  first | (exact @GlobalTheory.AV.AbVar.finite_lam_eq_zero) | (exact GlobalTheory.AV.AbVar.finite_lam_eq_zero) | (intros; apply GlobalTheory.AV.AbVar.finite_lam_eq_zero  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiadditiveClassEqPoincarePullbackUniqueHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiadditiveClassEqPoincarePullbackUniqueHom
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.FamHom

theorem main : ∀ (K : Type) [Field K] (A A' T : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P)
    (β : Pic (A.X ⊗ T.X).left), (∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ T.X),
      CechPic.pull (lift (a * a') t).left β = CechPic.pull (lift a t).left β + CechPic.pull (lift a' t).left β) →
    CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ T.X)).left β = 0 →
    ∃! ψ : T ⟶ A', β = AbDual.evc hP.isLB (fst A.X T.X) (snd A.X T.X ≫ ψ.hom) := by
  intro K _ A A' T P hP β hadd h0
  obtain ⟨M, hM, rfl⟩ := cls_surj β
  have hMa : AbDual.IsAdditive M := (AbDual.isAdditive_iff hM).2 fun Y a a' t => hadd Y a a' t
  obtain ⟨x, hx, hu⟩ := hP.univ T.X M hM hMa
  have hE : (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ x)).IsLB := pull_isLB hP.isLB _
  have c : cls M hM = AbDual.evc hP.isLB (fst A.X T.X) (snd A.X T.X ≫ x) := (cls_eq_iff hM hE).2 hx
  have Kx : ∀ (Y : Over (Sp K)) (a : Y ⟶ A.X) (t : Y ⟶ T.X),
      AbDual.evc hP.isLB a (t ≫ x) = AbDual.evc hM a t := by
    intro Y a t
    have k := AbDual.evc_ev hP.isLB (fst A.X T.X) (snd A.X T.X ≫ x) hE a t
    rw [lift_fst, lift_snd_assoc] at k
    rw [← k]
    unfold AbDual.evc
    rw [c]
    rfl
  have h1 := (AbDual.triv_ev_iff hM (𝟙 A.X) (1 : A.X ⟶ T.X)).2 h0
  have u : snd A.X (𝟙_ (Over (Sp K))) ≫ (η[T.X] : 𝟙_ (Over (Sp K)) ⟶ T.X) = 1 := by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A.X (𝟙_ (Over (Sp K)))) (toUnit _)]
  have e1 : η[T.X] ≫ x = 1 := by
    apply hP.eq_one
    rw [AbDual.triv_ev_iff hP.isLB, ← Category.assoc, Kx, u, AbDual.evc_one_right hM h1]
  have hpt : η[T.X] ≫ x = η[A'.X] := by
    rw [e1]
    show toUnit _ ≫ η = η
    rw [toUnit_unique (toUnit (𝟙_ (Over (Sp K)))) (𝟙 _), Category.id_comp]
  have hmon : IsMonHom x := rigidity_holds (Sp K) T.X A'.X T.ab A'.ab x hpt
  refine ⟨Hom.mk x, c, fun ψ hψ => ?_⟩
  have hE' : (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ ψ.hom)).IsLB := pull_isLB hP.isLB _
  have hψ' : LBIso M (AbDual.ev P (fst A.X T.X) (snd A.X T.X ≫ ψ.hom)) := (cls_eq_iff hM hE').1 hψ
  exact Subtype.ext (hu ψ.hom hψ')

end GlobalTheory.AV.FamHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiadditiveClassEqPoincarePullbackUniqueHomStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biadditiveClass_eq_poincarePullback_unique_hom : ∀ (K : Type) [Field K] (A A' T : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P) (β : Pic (A.X ⊗ T.X).left), (∀ (Y : Over (Sp K)) (a a' : Y ⟶ A.X) (t : Y ⟶ T.X), CechPic.pull (lift (a * a') t).left β = CechPic.pull (lift a t).left β + CechPic.pull (lift a' t).left β) → CechPic.pull (lift (𝟙 A.X) (1 : A.X ⟶ T.X)).left β = 0 → ∃! ψ : T ⟶ A', β = AbDual.evc hP.isLB (fst A.X T.X) (snd A.X T.X ≫ ψ.hom) := by
  first | (exact @GlobalTheory.AV.FamHom.main) | (exact GlobalTheory.AV.FamHom.main) | (intros; apply GlobalTheory.AV.FamHom.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesOfCompatibleSystem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesOfCompatibleSystem
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

theorem existsUnique_evA_eq_of_presents (k : Type) [CommRing k] (σ : Type) [Finite σ]
    (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, Algebra k (B n)] (y : ∀ n, σ → B n)
    (hy : ∀ n i, IsNilpotent (y n i)) (r : ∀ n, B (n + 1) →ₐ[k] B n)
    (hr : ∀ n i, r n (y (n + 1) i) = y n i) (hP : Presents k y hy) (b : ∀ n, B n)
    (hb : ∀ n, r n (b (n + 1)) = b n) :
    ∃! f : MvPowerSeries σ k, ∀ n, evA k (y n) (hy n) f = b n := by
  classical
  have hX : ∀ n i, evA k (y n) (hy n) (X i) = y n i := by
    intro n i
    change constantCoeff (substAlgHom (R := k) (a := fun i => (C (y n i) : MvPowerSeries Empty (B n)))
      (hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hy n i) (X i)) = _
    rw [substAlgHom_X, constantCoeff_C]
  have hres : ∀ n f, r n (evA k (y (n + 1)) (hy (n + 1)) f) = evA k (y n) (hy n) f := fun n f =>
    (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k σ (B (n + 1))).2 (B n) (r n) _ _ _ _ (hr n) f
  have hdown : ∀ n m, n ≤ m → ∀ f, evA k (y m) (hy m) f = b m → evA k (y n) (hy n) f = b n := by
    intro n m h
    induction m, h using Nat.le_induction with
    | base => exact fun _ h => h
    | succ m _ ih =>
      intro f hf
      exact ih f (by rw [← hres, hf, hb])
  choose F hF using fun n => hP.1 n (b n)
  choose ν hν using hP.2
  have hcoef : ∀ (α : σ →₀ ℕ) (g g' : MvPowerSeries σ k),
      evA k (y _) (hy (ν (α.degree + 1))) g = b _ → evA k (y _) (hy (ν (α.degree + 1))) g' = b _ →
      coeff α g = coeff α g' := by
    intro α g g' h h'
    have := hν (α.degree + 1) (g - g') (by rw [map_sub, h, h', sub_self]) α (Nat.lt_succ_self _)
    rwa [map_sub, sub_eq_zero] at this
  let f : MvPowerSeries σ k := fun α => coeff α (F (ν (α.degree + 1)))
  have hf : ∀ α, coeff α f = coeff α (F (ν (α.degree + 1))) := fun _ => rfl
  refine ⟨f, fun n => ?_, fun g hg => ?_⟩
  · obtain ⟨N, hN⟩ := GlobalTheory.mvPowerSeries_algHom_kill_high_order k σ (B n) (evA k (y n) (hy n)) fun i => by
      rw [hX]; exact hy n i
    let m := max n ((Finset.range (N + 1)).sup ν)
    have h0 := hN (f - F m) fun α hα => by
      rw [map_sub, hf, sub_eq_zero]
      refine hcoef α _ _ (hF _) (hdown _ m ?_ _ (hF m))
      exact le_max_of_le_right (Finset.le_sup (f := ν) (Finset.mem_range.2 (by omega)))
    rw [map_sub, sub_eq_zero] at h0
    rw [h0]
    exact hdown n m (le_max_left _ _) _ (hF m)
  · ext α
    rw [hf]
    exact hcoef α _ _ (hg _) (hF _)

end Katz

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesOfCompatibleSystemStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_powerSeries_of_compatible_system : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, Algebra k (B n)] (y : ∀ n, σ → B n) (hy : ∀ n i, IsNilpotent (y n i)) (r : ∀ n, B (n + 1) →ₐ[k] B n), (∀ n i, r n (y (n + 1) i) = y n i) → Presents k y hy → ∀ b : ∀ n, B n, (∀ n, r n (b (n + 1)) = b n) → ∃! f : MvPowerSeries σ k, ∀ n, evA k (y n) (hy n) f = b n := by
  first | exact @GlobalTheory.Katz.existsUnique_evA_eq_of_presents | exact GlobalTheory.Katz.existsUnique_evA_eq_of_presents | (intros; apply GlobalTheory.Katz.existsUnique_evA_eq_of_presents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem genericFibre_facts : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (D : ℕ), IsArithVar p D → ∃ (_ : IsIntegral G) (_ : IsLocallyNoetherian G), IsProjOver q ∧ topologicalKrullDim G = D ∧ j (genericPoint G) = genericPoint X ∧ Function.Injective j ∧ (∀ x, IsIso (j.stalkMap x)) ∧ (∀ x, Order.coheight (j x) = Order.coheight x) ∧ ∀ z : X, z ∉ Set.range j → ∀ σ : k →+* ℂ, IsEmpty (CxPts (closι z ≫ p) σ) := by
  intro k K _ _ _ _ X G _ p q j hp D h
  obtain ⟨hG, hd, hη⟩ := GenSmoothCover.genericFibre h hp
  have hq : IsProjOver q := ProjSpace.isProjOver_of_isPullback_spMap _ hp h.isProjOver
  have : IsProper q := CommonModel.isProper_of_isProjOver hq
  have := h.isDomain
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion j := MorphismProperty.of_isPullback hp.flip this
  have := flat_specMap_localization (nonZeroDivisors k) K
  have : Flat j := MorphismProperty.of_isPullback hp.flip this
  have hs (x : G) : IsIso (j.stalkMap x) := GenSpread.isIso_stalkMap_of_flat j x
  refine ⟨hG, LocallyOfFiniteType.isLocallyNoetherian q, hq, hd, hη, j.isEmbedding.injective, hs,
    fun x => ?_, fun z hz σ => ⟨fun y => hz ?_⟩⟩
  · have := hs x
    have e := ringKrullDim_eq_of_ringEquiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at e
    exact_mod_cast e
  · have hr : Set.range j = p ⁻¹' Set.range (spMap (algebraMap k K)) := by
      rw [← Scheme.Pullback.range_fst, ← hp.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
        Function.Surjective.range_comp hp.isoPullback.hom.surjective]
    let c : Sp ℂ := IsLocalRing.closedPoint ℂ
    have hw : closι z (y.1 c) ∈ closure {z} := by
      have : closι z (y.1 c) ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι :=
        ⟨_, rfl⟩
      rw [Scheme.IdealSheafData.range_subschemeι] at this
      simpa using this
    have h₁ : p z ⤳ p (closι z (y.1 c)) := (specializes_iff_mem_closure.2 hw).map p.continuous
    have h₂ : p (closι z (y.1 c)) = spMap σ c := by
      have := y.2
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun f : Sp ℂ ⟶ Sp k => f c) this
    have h₃ : (spMap σ c).asIdeal = ⊥ := by
      change Ideal.comap σ (IsLocalRing.maximalIdeal ℂ) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ (ChernNull.injective_of_arithVar h σ)
    rw [h₂] at h₁
    have h₄ : (p z).asIdeal ≤ (spMap σ c).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h₁
    rw [h₃, le_bot_iff] at h₄
    rw [hr]
    refine ⟨(⟨⊥, inferInstance⟩ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [h₄]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective k K)

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (D : ℕ), IsArithVar p D → ∃ (_ : IsIntegral G) (_ : IsLocallyNoetherian G), IsProjOver q ∧ topologicalKrullDim G = D ∧ j (genericPoint G) = genericPoint X ∧ Function.Injective j ∧ (∀ x, IsIso (j.stalkMap x)) ∧ (∀ x, Order.coheight (j x) = Order.coheight x) ∧ ∀ z : X, z ∉ Set.range j → ∀ σ : k →+* ℂ, IsEmpty (CxPts (closι z ≫ p) σ) := by
  first | exact @GlobalTheory.Mix.genericFibre_facts | exact GlobalTheory.Mix.genericFibre_facts | (intros; apply GlobalTheory.Mix.genericFibre_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationExpUniqueFullLevelMarking
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationExpUniqueFullLevelMarking
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem unifAt_exp_unique : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) P (y : Sp ℂ ⟶ F.X) e e', 3 ≤ N → FullMark N D' t → UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D' t P y e' → e = e' := by
  intro O _ bar g ρ R _ σ Λ F N D' t P y e e' hN hfull hu hu'
  obtain ⟨w, h, ⟨hiso, hmark⟩, hPw, he⟩ :=
    GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry O bar g ρ R σ Λ F N D' D' t t P P y e e' (by omega) hu hu'
  obtain ⟨-, hinj, hd, hspan, Hm, -, hpos, hIm⟩ := hu.2.1
  let σw : Module.End ℤ D'.La := (w.toLinearMap.toAddMonoidHom).toIntLinearMap
  have hσ : ∀ a, σw a = w a := fun _ => rfl
  let hR : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := h.toLinearMap.restrictScalars ℝ
  let B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun u v => (hermForm Hm u v).im)
    (fun a b c => by simp [hermForm]) (fun r a b => by simp [hermForm])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add]) (fun r a b => by simp [hermForm, Matrix.mulVec_smul])
  have hB : B.compl₁₂ hR hR = B := by
    refine LinearMap.ext_on_range hspan fun a => LinearMap.ext_on_range hspan fun b => ?_
    show (hermForm Hm (h (P a)) (h (P b))).im = (hermForm Hm (P a) (P b)).im
    rw [← hPw, ← hPw, hIm, hIm, hiso]
  have hq : ∀ u, (hermForm Hm u u).re = B (Complex.I • u) u := fun u => by
    show _ = (hermForm Hm (Complex.I • u) u).im
    simp [hermForm]
  have hbd := GlobalTheory.ExpUnique.isBounded_sublevel (q := fun u => (hermForm Hm u u).re)
    (by unfold hermForm; fun_prop) (fun r u => by
      simp only [hq]
      rw [smul_comm, map_smul, map_smul, LinearMap.smul_apply, smul_smul, sq, smul_eq_mul]) hpos
  have key : σw = 1 := by
    refine GlobalTheory.ExpUnique.end_eq_one_of_invariant D'.La σw (fun a b hab => w.injective hab)
      (fun a => (hermForm Hm (P a) (P a)).re) (fun c => ?_) (fun a => ?_) N hN fun a => ?_
    · refine Set.Finite.of_finite_image (f := P) ((Metric.finite_isBounded_inter_isClosed
        (s := P.range) DiscreteTopology.isDiscrete (hbd c) AddSubgroup.isClosed_of_discrete).subset ?_) hinj.injOn
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨ha, a, rfl⟩
    · have h1 : h (Complex.I • P a) = Complex.I • h (P a) := map_smul h _ _
      simp only [hq, hσ, hPw]
      rw [← h1]
      have h2 := LinearMap.congr_fun₂ hB (Complex.I • P a) (P a)
      rw [LinearMap.compl₁₂_apply] at h2
      exact h2
    · obtain ⟨i, f, rfl⟩ := hfull a
      obtain ⟨e₀, he₀⟩ := hmark i
      refine ⟨e₀ + w f - f, ?_⟩
      have h3 : w (t i + N • f) = w (t i) + N • w f := by rw [map_add (f := _), map_nsmul]
      rw [hσ, h3, he₀, smul_sub, smul_add]
      abel
  have hid : hR = LinearMap.id := LinearMap.ext_on_range hspan fun a => by
    show h (P a) = P a
    rw [← hPw, ← hσ, key]
    rfl
  funext z
  have hz : h z = z := LinearMap.congr_fun hid z
  rw [← he z, hz]

end GlobalTheory.PELU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationExpUniqueFullLevelMarkingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexUniformisation_exp_unique_full_level_marking : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) P (y : Sp ℂ ⟶ F.X) e e', 3 ≤ N → FullMark N D' t → UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D' t P y e' → e = e' := by
  first | exact @GlobalTheory.PELU.unifAt_exp_unique | exact GlobalTheory.PELU.unifAt_exp_unique | (intros; apply GlobalTheory.PELU.unifAt_exp_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnMixedChernFormDensityInChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnMixedChernFormDensityInChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace GlobalTheory.Mix

theorem continuousOn_dens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (D : ℕ) (L : Fin D → MLine p σ) (c : AlgChart p σ D), ContinuousOn (dens L c) c.e.source := by
  intro k _ X p σ D L c y₀ hy₀
  let i : ∀ a, (L a).B.ι := fun a => pick (L a).φ.isLB y₀
  let S : Set (CxPts p σ) := c.e.source ∩ ⋂ a, ptsIn p σ ((L a).B.U (i a))
  have hSo : IsOpen S := c.e.open_source.inter (isOpen_iInter_of_finite fun a => isOpen_ptsIn _)
  have hy₀S : y₀ ∈ S := ⟨hy₀, mem_iInter.2 fun a => mem_pick _ y₀⟩
  have hH : ∀ (a : Fin D) (j l : Fin D),
      ContinuousOn (fun y => c.hess (L a).φ (i a) y j l) S := by
    intro a j l
    have hO : IsOpen (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ ((L a).B.U (i a))) :=
      isOpen_over c.e (isOpen_ptsIn _)
    have hg : ContDiffOn ℝ ∞ (fun v => ((L a).φ.φ (i a) (c.e.symm v) : ℂ))
        (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ ((L a).B.U (i a))) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_chart ((L a).cInf (i a)) c)
    have hw := ReciprocityTheory.L2DbarEstimates.Y.continuousOn_wd_wdb hO hg j l
    exact hw.comp (c.e.continuousOn.mono inter_subset_left) fun y hy =>
      ⟨c.e.map_source hy.1, by
        simpa only [mem_preimage, c.e.left_inv hy.1] using mem_iInter.1 hy.2 a⟩
  let F : CxPts p σ → ℝ := fun y => (Real.pi ^ D)⁻¹ * (∑ τ : Equiv.Perm (Fin D),
    (Matrix.of fun j l => c.hess (L (τ l)).φ (i (τ l)) y j l).det).re
  have hF : ContinuousOn F S := by
    refine continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      (continuousOn_finsetSum _ fun τ _ => ?_))
    refine (continuous_id.matrix_det).comp_continuousOn ?_
    exact continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hH (τ l) j l
  have he : ∀ y ∈ S, dens L c y = F y := by
    intro y hy
    have hm : ∀ τ : Equiv.Perm (Fin D),
        (Matrix.of fun j l => c.hess (L (τ l)).φ (pick (L (τ l)).φ.isLB y) y j l) =
          Matrix.of fun j l => c.hess (L (τ l)).φ (i (τ l)) y j l := fun τ => by
      ext j l
      simp only [Matrix.of_apply]
      rw [c.hess_eq (L (τ l)).cInf hy.1 (mem_iInter.1 hy.2 (τ l)) (mem_pick _ y)]
    simp only [dens, F, hm]
  refine ContinuousAt.continuousWithinAt ?_
  refine (hF.continuousAt (hSo.mem_nhds hy₀S)).congr ?_
  filter_upwards [hSo.mem_nhds hy₀S] with y hy
  exact (he y hy).symm

end GlobalTheory.Mix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnMixedChernFormDensityInChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_mixedChernFormDensityInChart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (c : AlgChart p σ D), ContinuousOn (dens L c) c.e.source := by
  first | exact @GlobalTheory.Mix.continuousOn_dens | exact GlobalTheory.Mix.continuousOn_dens | (intros; apply GlobalTheory.Mix.continuousOn_dens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveIffPtMapSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveIffPtMapSurjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem surjective_iff_ptMap_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B),
    Surjective p.hom.left ↔ Function.Surjective (ptMap p) := by
  intro K _ A B p
  have hAs : Smooth A.X.hom := A.ab.smooth
  have hBs : Smooth B.X.hom := B.ab.smooth
  have hBp : IsProper B.X.hom := B.ab.proper
  have hw : p.hom.left ≫ B.X.hom = A.X.hom := Over.w p.hom
  have hlft : LocallyOfFiniteType p.hom.left := by
    have : LocallyOfFiniteType (p.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
    exact locallyOfFiniteType_of_comp p.hom.left B.X.hom
  constructor
  · intro hs y
    obtain ⟨u, hu⟩ := hs.surj (y.left (IsLocalRing.closedPoint (AlgebraicClosure K)))
    obtain ⟨w, hw'⟩ := GlobalTheory.CovLift.exists_lift_of_locallyOfFiniteType _ _ p.hom.left hlft
      (AlgebraicClosure K) y.left u hu
    refine ⟨Over.homMk w ?_, ?_⟩
    · change w ≫ A.X.hom = spMap (algebraMap K (AlgebraicClosure K))
      rw [← hw, ← Category.assoc, hw']
      exact Over.w y
    · apply Over.OverMorphism.ext
      simpa using hw'
  · intro hs
    have : IsProper (p.hom.left ≫ B.X.hom) := by rw [hw]; exact A.ab.proper
    have hp : IsProper p.hom.left := IsProper.of_comp p.hom.left B.X.hom
    have hcl : IsClosed (Set.range p.hom.left) := p.hom.left.isClosedMap.isClosed_range
    have hJ : JacobsonSpace B.X.left := LocallyOfFiniteType.jacobsonSpace B.X.hom
    have hsub : closedPoints B.X.left ⊆ Set.range p.hom.left := by
      intro b hb
      let t : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K (AlgebraicClosure K))
      haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.X.hom) (g := t) b
        (IsLocalRing.closedPoint (AlgebraicClosure K)) (Subsingleton.elim _ _)
      have : JacobsonSpace ↥(pullback B.X.hom t : Scheme.{0}) :=
        LocallyOfFiniteType.jacobsonSpace (pullback.snd B.X.hom t)
      have hF : IsClosed ((pullback.fst B.X.hom t) ⁻¹' {b}) :=
        (show IsClosed {b} from hb).preimage (pullback.fst B.X.hom t).continuous
      obtain ⟨c, hcF, hc'⟩ := nonempty_inter_closedPoints (X := ↥(pullback B.X.hom t : Scheme.{0}))
        (Z := (pullback.fst B.X.hom t) ⁻¹' {b}) ⟨z, hz⟩ hF.isLocallyClosed
      have hc : IsClosed {c} := hc'
      let x0 : Sp (AlgebraicClosure K) ⟶ B.X.left :=
        pointOfClosedPoint (pullback.snd B.X.hom t) c hc ≫ pullback.fst B.X.hom t
      have hx0 : x0 ≫ B.X.hom = t := by
        simp only [x0, Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
      obtain ⟨x, hx⟩ := hs (Over.homMk x0 hx0 : ptOver K (AlgebraicClosure K) ⟶ B.X)
      refine ⟨x.left (IsLocalRing.closedPoint (AlgebraicClosure K)), ?_⟩
      have e : x.left ≫ p.hom.left = x0 := congrArg CommaMorphism.left hx
      have e3 : p.hom.left (x.left (IsLocalRing.closedPoint (AlgebraicClosure K))) =
          x0 (IsLocalRing.closedPoint (AlgebraicClosure K)) := by
        rw [← e]; rfl
      have e4 : x0 (IsLocalRing.closedPoint (AlgebraicClosure K)) = pullback.fst B.X.hom t c := by
        change pullback.fst B.X.hom t (pointOfClosedPoint (pullback.snd B.X.hom t) c hc
          (IsLocalRing.closedPoint (AlgebraicClosure K))) = _
        exact congrArg (pullback.fst B.X.hom t) (pointOfClosedPoint_apply (pullback.snd B.X.hom t) c hc _)
      rw [e3, e4]
      exact hcF
    have huniv : Set.univ ⊆ Set.range p.hom.left := by
      rw [← closure_closedPoints]
      exact closure_minimal hsub hcl
    exact ⟨fun b => huniv (Set.mem_univ b)⟩

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveIffPtMapSurjectiveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abVar_surjective_iff_ptMap_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B), Surjective p.hom.left ↔ Function.Surjective (ptMap p) := by
  first | exact @GlobalTheory.AV.AbVar.surjective_iff_ptMap_surjective | exact GlobalTheory.AV.AbVar.surjective_iff_ptMap_surjective | (intros; apply GlobalTheory.AV.AbVar.surjective_iff_ptMap_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativePolynomialFunctionEqNormForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativePolynomialFunctionEqNormForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulPolyNorm

open Polynomial GlobalTheory.PolyNorm

theorem eq_prod_aroots : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (d : ℕ) (δ : Polynomial ℤ → ℚ) (P : Polynomial ℚ), (∀ F G, δ (F * G) = δ F * δ G) → (∀ (n : ℕ) (u : Fin n → Polynomial ℤ), ∃ Φ : MvPolynomial (Fin n) ℚ, Φ.IsHomogeneous (2 * d) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) Φ = δ (∑ i, m i • u i)) → P.Monic → P.natDegree = 2 * d → (∀ n : ℤ, P.eval (n : ℚ) = δ (Polynomial.C n - Polynomial.X)) → ∀ F : Polynomial ℤ, algebraMap ℚ Ω (δ F) = ((P.aroots Ω).map (fun a => Polynomial.aeval a F)).prod := by
  intro Ω _ _ _ d δ P hm hΦ0 hP hPd hPe
  choose Φ hh hΦ using fun r : ℕ => hΦ0 r (fun i : Fin r => (X : ℤ[X]) ^ (i : ℕ))
  have hN : ∀ r (F : ℤ[X]), F.natDegree < r → δ F = ev (Φ r) (F.map (Int.castRingHom ℚ)) := by
    intro r F hF
    have := hΦ r fun i => F.coeff i
    have e : ∑ i : Fin r, F.coeff i • (X : ℤ[X]) ^ (i : ℕ) = F := by
      conv_rhs => rw [← gen_coeff F hF]
      unfold gen
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_C_mul, C_mul_X_pow_eq_monomial]
    rw [e] at this
    rw [← this]
    simp [ev, MvPolynomial.aeval_eq_eval]
  have h11 : δ 1 = δ 1 * δ 1 := by rw [← hm, _root_.one_mul]
  have h1 : δ 1 = 1 := by
    by_contra hne
    have h0 : δ 1 = 0 := by
      have : δ 1 * (δ 1 - 1) = 0 := by rw [mul_sub, ← h11]; ring
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hne
    have hP0 : P = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono (s := Set.range (Int.cast : ℤ → ℚ)) ?_
        (Set.infinite_range_of_injective Int.cast_injective)
      rintro _ ⟨n, rfl⟩
      simp only [Set.mem_setOf_eq, IsRoot.def]
      rw [hPe, ← _root_.one_mul (C n - Polynomial.X : ℤ[X]), hm, h0, zero_mul]
    exact hP.ne_zero hP0
  obtain ⟨M, hM⟩ := exists_ext δ Φ hN h1 hm Ω
  have hPP : ev (Φ 2) (C Polynomial.X - Polynomial.X : ℚ[X][X]) = P := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := Set.range (Int.cast : ℤ → ℚ)) ?_
      (Set.infinite_range_of_injective Int.cast_injective)
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [hPe, hN 2 _ (lt_of_le_of_lt (natDegree_sub_le _ _) (by simp)), ← coe_evalRingHom, ev_map]
    congr 1
    simp
  have ha : P.map (algebraMap ℚ Ω) = ((P.aroots Ω).map fun x => Polynomial.X - C x).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hP.map _)
      IsAlgClosed.card_roots_eq_natDegree).symm
  have hac : Multiset.card (P.aroots Ω) = 2 * d := by
    rw [aroots_def, IsAlgClosed.card_roots_eq_natDegree, hP.natDegree_map, hPd]
  have hMa : ∀ F, M F = ((P.aroots Ω).map fun x => F.eval x).prod := by
    refine eq_prod_of_mul M (P.aroots Ω) (fun c => ?_) (fun β => ?_)
    · rw [hM 1 _ (by simp), ← _root_.mul_one (C c), ev_homog (hh 1), ev_one δ Φ hN h1, _root_.mul_one, hac]
    · have := congrArg (eval β) ha
      rw [Polynomial.eval_multiset_prod, Multiset.map_map, Polynomial.eval_map, ← coe_eval₂RingHom, ← hPP,
        ev_map, hPP] at this
      rw [hM 2]
      · simpa using this
      · exact lt_of_le_of_lt (natDegree_sub_le _ _) (by simp)
  intro F
  have := hMa (F.map (algebraMap ℤ Ω))
  simp only [eval_map_algebraMap] at this
  rw [← this, hM (F.natDegree + 1) _ (Nat.lt_succ_of_le natDegree_map_le),
    hN _ F (Nat.lt_succ_self _), ev_map, Polynomial.map_map]
  congr 2
  exact RingHom.ext_int _ _

end GlobalTheory.MulPolyNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativePolynomialFunctionEqNormFormStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (d : ℕ) (δ : Polynomial ℤ → ℚ) (P : Polynomial ℚ), (∀ F G, δ (F * G) = δ F * δ G) → (∀ (n : ℕ) (u : Fin n → Polynomial ℤ), ∃ Φ : MvPolynomial (Fin n) ℚ, Φ.IsHomogeneous (2 * d) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) Φ = δ (∑ i, m i • u i)) → P.Monic → P.natDegree = 2 * d → (∀ n : ℤ, P.eval (n : ℚ) = δ (Polynomial.C n - Polynomial.X)) → ∀ F : Polynomial ℤ, algebraMap ℚ Ω (δ F) = ((P.aroots Ω).map (fun a => Polynomial.aeval a F)).prod := by
  first | (exact @GlobalTheory.MulPolyNorm.eq_prod_aroots) | (exact GlobalTheory.MulPolyNorm.eq_prod_aroots) | (intros; apply GlobalTheory.MulPolyNorm.eq_prod_aroots  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianProperUniformisedWhereTrivialisationsGene
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianProperUniformisedWhereTrivialisationsGene
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem abelian_and_proper_of_psiUnitOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → (W : Set (Sp R)) ⊆ abLocus G ∧ IsProper (G.hom ∣_ W) := by
  intro R _ _ _ hB D A G _ _ hG U W hW
  exact ⟨GlobalTheory.T.uniformised_group_abelian_where_trivialisations_units R hB D A G hG U W hW, GlobalTheory.T.isProper_uniformisedSemiAbelian_over_open_in_abLocus R hB D A G hG U W (GlobalTheory.T.uniformised_group_abelian_where_trivialisations_units R hB D A G hG U W hW)⟩

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianProperUniformisedWhereTrivialisationsGeneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_proper_uniformised_where_trivialisations_generate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, (∀ y, PsiUnitOn D.toPre y W) → (W : Set (Sp R)) ⊆ abLocus G ∧ IsProper (G.hom ∣_ W) := by
  first | exact @GlobalTheory.Mum.abelian_and_proper_of_psiUnitOn | exact GlobalTheory.Mum.abelian_and_proper_of_psiUnitOn | (intros; apply GlobalTheory.Mum.abelian_and_proper_of_psiUnitOn <;> assumption)
end
end
