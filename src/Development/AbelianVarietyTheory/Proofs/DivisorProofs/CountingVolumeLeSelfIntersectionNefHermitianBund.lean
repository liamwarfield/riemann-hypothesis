module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingVolumeLeSelfIntersectionNefHermitianBund
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingVolumeLeSelfIntersectionNefHermitianBund
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory

open Filter Topology

theorem countVol_le_selfInter : ∀ (k : Type) [CommRing k] (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp k) (D d a : ℕ) (L : GlobalTheory.HermLB p) (A : ℝ) (m : ℕ → ℕ∞), GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.IsArithVar p D → L.IsNef D → L.IsSelfInter A → 0 < d → 0 < a → (∀ i : ℕ, 1 ≤ i → m (a * i) ≤ (L.pow (a * i)).smallSec.encard) → countVol D d a m ≤ ENNReal.ofReal (A / ((d : ℝ) * ((D : ℝ) + 1))) := by
  intro k _ X _ p D d a L A m hAHS hX hL hA hd ha hm
  have hmul : Tendsto (fun j : ℕ => a * j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j ha) tendsto_id
  have h1 := ((hAHS.tendsto_of_triv hX hL hA).comp hmul).div_const ((d : ℝ) * ((D : ℝ) + 1))
  have h2 := ENNReal.tendsto_ofReal h1
  refine (limsup_le_limsup ?_).trans_eq h2.limsup_eq
  filter_upwards [hmul.eventually (hAHS.of_triv hX hL hA).1, eventually_ge_atTop 1] with j hfin hj
  have hx : 0 ≤ Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hN : (0 : ℝ) < ((a * j : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.mul_pos ha hj)
  have hd' : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.2 hd
  have hlog : logCard (m (a * j)) ≤ ENNReal.ofReal (Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ)) := by
    rw [← logCard_coe, hfin.cast_ncard_eq]
    exact EReal.toENNReal_le_toENNReal (ENNReal.log_monotone (ENat.toENNReal_le.2 (hm j hj)))
  have hden : (d : ℝ≥0∞) * ((a * j : ℕ) : ℝ≥0∞) ^ (D + 1) =
      ENNReal.ofReal ((d : ℝ) * ((a * j : ℕ) : ℝ) ^ (D + 1)) := by
    rw [ENNReal.ofReal_mul hd'.le, ENNReal.ofReal_pow hN.le, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  calc _ ≤ (D.factorial : ℝ≥0∞) * ENNReal.ofReal (Real.log (((L.pow (a * j)).smallSec.ncard : ℕ) : ℝ)) /
        ((d : ℝ≥0∞) * ((a * j : ℕ) : ℝ≥0∞) ^ (D + 1)) := by gcongr
    _ = _ := by
      rw [hden, ← ENNReal.ofReal_natCast (D.factorial), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_div_of_pos (by positivity)]
      simp only [Function.comp]
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountingVolumeLeSelfIntersectionNefHermitianBundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.countingVolume_le_selfIntersection_nefHermitianBundle : ∀ (k : Type) [CommRing k] (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp k) (D d a : ℕ) (L : GlobalTheory.HermLB p) (A : ℝ) (m : ℕ → ℕ∞), GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.IsArithVar p D → L.IsNef D → L.IsSelfInter A → 0 < d → 0 < a → (∀ i : ℕ, 1 ≤ i → m (a * i) ≤ (L.pow (a * i)).smallSec.encard) → countVol D d a m ≤ ENNReal.ofReal (A / ((d : ℝ) * ((D : ℝ) + 1))) := by
  first | exact @GlobalTheory.countVol_le_selfInter | exact GlobalTheory.countVol_le_selfInter | (intros; apply GlobalTheory.countVol_le_selfInter <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionMemBallExpOfProjArithVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionMemBallExpOfProjArithVariety
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem sec_nsq_le {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (M : HermLB p) (u : M.B.Sec) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ C := by
  have := hX.finite_emb
  have hb : ∀ σ : k →+* ℂ, ∃ K : ℝ, ∀ y, (M.φ σ).nsq (CxPts.secVal p σ u) y ≤ K := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨K, hK⟩ := (isCompact_range ((M.cInf σ).continuous_nsq u)).bddAbove
    exact ⟨K, fun y => hK ⟨y, rfl⟩⟩
  choose K hK using hb
  have := Fintype.ofFinite (k →+* ℂ)
  refine ⟨∑ τ, |K τ| + 1, ?_, fun σ y => (hK σ y).trans ?_⟩
  · linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)]
  · have := Finset.single_le_sum (fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)) (Finset.mem_univ σ)
    linarith [le_abs_self (K σ)]

theorem bounded_norm : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∃ u : ℝ, 0 ≤ u ∧ f ∈ P.Bl a b (Real.exp u) := by
  intro k _ X _ p D hX P a b f hf
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a b
  obtain ⟨e, -, hrng, hnu, -⟩ := GlobalTheory.VolBr.RepDict.rep_dict k X p P a b M hM
  obtain ⟨u, rfl⟩ : f ∈ Set.range e := by rw [hrng]; exact hf
  obtain ⟨C, hC1, hC⟩ := sec_nsq_le hX M u
  refine ⟨Real.log C, Real.log_nonneg hC1, hf, fun σ y => ?_⟩
  rw [Real.exp_log (by linarith)]
  have h1 := hnu u σ y
  have h2 := hC σ y
  have h3 : 0 ≤ P.nu a b σ y (e u) := by unfold Pair.nu; positivity
  nlinarith

end GlobalTheory.HSNef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionMemBallExpOfProjArithVarietyStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∃ u : ℝ, 0 ≤ u ∧ f ∈ P.Bl a b (Real.exp u) := by
  first | exact @GlobalTheory.HSNef.bounded_norm | exact GlobalTheory.HSNef.bounded_norm | (intros; apply GlobalTheory.HSNef.bounded_norm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtIffForallSpecializes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtIffForallSpecializes
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.RegCodimOne

theorem regAt_iff_ord_nonneg {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] {z : X} (hz : Order.coheight z = 1) {g : X.functionField} (hg : g ≠ 0) :
    RegAt z g ↔ 0 ≤ Scheme.ord g z := by
  haveI := IsNormalScheme.isDiscreteValuationRing_stalk hz
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk z)
  have h := le_ordTop_vw_iff (F := X.functionField) ht 0 g
  rw [ordTop_vw_of_ne_zero _ hg, WithTop.coe_le_coe] at h
  have e : Scheme.ord g z = WithZero.log (Ring.ordFrac (X.presheaf.stalk z) g) :=
    (Scheme.ord_eq_iff hz hg).2 (WithZero.exp_log ((map_ne_zero _).2 hg)).symm
  rw [e]
  refine Iff.trans ⟨fun ⟨a, ha⟩ => ⟨a, by simp [ha]⟩, fun ⟨a, ha⟩ => ⟨a, by simp [ha]⟩⟩ h.symm

theorem regularAt_iff_forall_specializes : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (D : CartierDiv X) (x : X) (f : X.functionFieldˣ), D.RegularAt x (f : X.functionField) ↔ ∀ z, z ⤳ x → 0 ≤ Scheme.ord (f : X.functionField) z + D.mult z := by
  intro X _ _ _ D x f
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
  have hne : (f : X.functionField) * (g : X.functionField) ≠ 0 := mul_ne_zero f.ne_zero g.ne_zero
  have key : ∀ z, z ⤳ x → Scheme.ord (f : X.functionField) z + D.mult z =
      Scheme.ord ((f : X.functionField) * (g : X.functionField)) z := fun z hz => by
    rw [(hgU z (hz.mem_open U.isOpen hU)).mult_eq, Scheme.ord_mul f.ne_zero g.ne_zero]
  rw [hg.regularAt_iff]
  refine ⟨fun h z hz => ?_, fun h => regAt_of_forall_coheight_eq_one fun z hz h1 => ?_⟩
  · rw [key z hz]
    by_cases h1 : Order.coheight z = 1
    · exact (regAt_iff_ord_nonneg h1 hne).1 (GlobalTheory.Discrepancy.regAt_of_specializes hz h)
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one h1]
  · exact (regAt_iff_ord_nonneg h1 hne).2 (key z hz ▸ h z hz)

end GlobalTheory.RegCodimOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtIffForallSpecializesStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (D : CartierDiv X) (x : X) (f : X.functionFieldˣ), D.RegularAt x (f : X.functionField) ↔ ∀ z, z ⤳ x → 0 ≤ Scheme.ord (f : X.functionField) z + D.mult z := by
  first | exact @GlobalTheory.RegCodimOne.regularAt_iff_forall_specializes | exact GlobalTheory.RegCodimOne.regularAt_iff_forall_specializes | (intros; apply GlobalTheory.RegCodimOne.regularAt_iff_forall_specializes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSpecBaseChangeMapEqOfFieldExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSpecBaseChangeMapEqOfFieldExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory

theorem baseChange_map_eq_of_fieldExtension : ∀ (R k Ω : Type) [CommRing R] [Field k] [Field Ω] [Algebra R k] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] (V W : Over (Spec (CommRingCat.of R))) (f g : V ⟶ W), (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map g → (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map g := by
  intro R k Ω _ _ _ _ _ _ _ V W f g h
  have hu : Spec.map (CommRingCat.ofHom (algebraMap R Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h1 : pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ f.left =
      pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ g.left := by
    have := congrArg (fun φ => φ.left ≫ pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) h
    simp only [Over.pullback_map_left, pullback.lift_fst] at this
    exact this
  set s := Spec.map (CommRingCat.ofHom (algebraMap R k)) with hs
  set t := Spec.map (CommRingCat.ofHom (algebraMap k Ω)) with ht
  rw [hu] at h1
  have f₁ : Flat t := by
    rw [ht, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField k) _
  have f₂ : Surjective t :=
    ⟨fun y => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have : Epi (pullback.fst (pullback.snd V.hom s) t) := Flat.epi_of_flat_of_surjective _
  have key : pullback.fst V.hom s ≫ f.left = pullback.fst V.hom s ≫ g.left := by
    rw [← cancel_epi (pullback.fst (pullback.snd V.hom s) t)]
    have hc : (pullback.fst (pullback.snd V.hom s) t ≫ pullback.fst V.hom s) ≫ V.hom =
        pullback.snd (pullback.snd V.hom s) t ≫ t ≫ s := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
    have he := pullback.lift_fst _ _ hc
    rw [← Category.assoc, ← Category.assoc, ← he, Category.assoc, Category.assoc, h1]
  apply Over.OverMorphism.ext
  simp only [Over.pullback_map_left]
  apply pullback.hom_ext
  · erw [pullback.lift_fst, pullback.lift_fst]
    exact key
  · erw [pullback.lift_snd, pullback.lift_snd]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverSpecBaseChangeMapEqOfFieldExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.overSpecBaseChange_map_eq_of_fieldExtension : ∀ (R k Ω : Type) [CommRing R] [Field k] [Field Ω] [Algebra R k] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] (V W : Over (Spec (CommRingCat.of R))) (f g : V ⟶ W), (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map g → (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map g := by
  first | exact @GlobalTheory.baseChange_map_eq_of_fieldExtension | exact GlobalTheory.baseChange_map_eq_of_fieldExtension | (intros; apply GlobalTheory.baseChange_map_eq_of_fieldExtension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmEqMapGm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def IsFrameOver {X : Scheme.{0}} (L : LB X) (W : X.Opens) (T : ∀ k, Γ(X, W ⊓ L.U k)ˣ) : Prop :=
  ∀ k k', res (inf_le_left : W ⊓ L.U k ⊓ (W ⊓ L.U k') ≤ W ⊓ L.U k) (T k) =
    res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      W ⊓ L.U k ⊓ (W ⊓ L.U k') ≤ L.U k ⊓ L.U k') (L.g k k') *
    res (inf_le_right : W ⊓ L.U k ⊓ (W ⊓ L.U k') ≤ W ⊓ L.U k') (T k')

def FrameCarried {X : Scheme.{0}} (L : LB X) (W : X.Opens) (T : ∀ k, Γ(X, W ⊓ L.U k)ˣ) (f : X ⟶ X)
    (w : LB.Iso L (L.pull f)) : Prop :=
  ∀ (z : X) (j k : L.ι), z ∈ W → f z ∈ W → z ∈ L.U k → f z ∈ L.U j →
    gm f z (W ⊓ L.U j) (T j) = gw w (𝟙 X) z j k * gm (𝟙 X) z (W ⊓ L.U k) (T k)

theorem gm_eq_map_gm {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [gm_val f y U h, Units.coe_map, gm_val (𝟙 X) (f y) U h]
  have := congrArg (fun q => q.hom a.val) (f.germ_stalkMap U y h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this.symm

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem FrameCarried.ratio_fixed {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {W W' O : X.Opens}
    {T : ∀ k, Γ(X, W ⊓ L.U k)ˣ} {T' : ∀ k, Γ(X, W' ⊓ L.U k)ˣ} {f : X ⟶ X} {w : LB.Iso L (L.pull f)}
    (hT : FrameCarried L W T f w) (hT' : FrameCarried L W' T' f w) (hOW : O ≤ W) (hOW' : O ≤ W') (r : Γ(X, O)ˣ)
    (hr : ∀ (z : X) (k : L.ι), z ∈ O → z ∈ L.U k →
      gm (𝟙 X) z O r = gm (𝟙 X) z _ (T' k) * (gm (𝟙 X) z _ (T k))⁻¹)
    (h : O ≤ f ⁻¹ᵁ O) : (f.appLE O O h).hom r.val = r.val := by
  apply TopCat.Presheaf.section_ext X.sheaf O
  intro x hx
  obtain ⟨k, hk⟩ := exists_chart hL x
  have hfx : f x ∈ O := h hx
  obtain ⟨j, hj⟩ := exists_chart hL (f x)
  have key : gm f x O r = gm (𝟙 X) x O r := by
    rw [gm_eq_map_gm f x O hfx, hr (f x) j hfx hj, map_mul, map_inv,
      ← gm_eq_map_gm f x (W' ⊓ L.U j) (show f x ∈ W' ⊓ L.U j from ⟨hOW' hfx, hj⟩),
      ← gm_eq_map_gm f x (W ⊓ L.U j) (show f x ∈ W ⊓ L.U j from ⟨hOW hfx, hj⟩),
      hT' x j k (hOW' hx) (hOW' hfx) hk hj, hT x j k (hOW hx) (hOW hfx) hk hj, hr x k hx hk, _root_.mul_inv,
      _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
  have e1 := congrArg Units.val key
  rw [gm_val f x O hfx, gm_val (𝟙 X) x O hx] at e1
  refine Eq.trans ?_ (e1.trans ?_)
  · simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    exact TopCat.Presheaf.germ_res_apply X.presheaf _ x hx _
  · rfl

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEndomorphismPlaceIntegral
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.BirigidLift
open scoped nonZeroDivisors
open scoped CategoryTheory.Obj

namespace GlobalTheory.PlaceModel


set_option autoImplicit false in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
attribute [local instance] Over.cartesianMonoidalCategory in
open scoped nonZeroDivisors in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.PlaceModel.exists_factor_pullback {S S' S'' : Scheme.{0}} {G : Over S}
    {G' : Over S'} {G'' : Over S''} [GrpObj G]
    [GrpObj G'] [GrpObj G''] {f : S' ⟶ S} {c : S'' ⟶ S} {φ : G'.left ⟶ G.left}
    {ψ : G''.left ⟶ G.left}
    (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f φ) (n : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G c ψ) (g : S'' ⟶ S') (e : g ≫ f = c) :
    ∃ φ' : G''.left ⟶ G'.left, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G'' G' g φ' ∧ φ' ≫ φ = ψ := by
  subst e
  obtain ⟨hφ, hφm⟩ := h
  obtain ⟨hψ, hψm⟩ := n
  refine ⟨hφ.lift ψ (G''.hom ≫ g) (by rw [hψ.w, Category.assoc]), ⟨?_, ?_⟩, hφ.lift_fst _ _ _⟩
  · refine IsPullback.of_right ?_ (hφ.lift_snd _ _ _) hφ
    rwa [hφ.lift_fst]
  · intro T x y x₀ y₀ hx hy
    apply hφ.hom_ext
    · rw [Category.assoc, hφ.lift_fst]
      let u : Over.mk ((T.hom ≫ g) ≫ f) ⟶ Over.mk (T.hom ≫ g ≫ f) :=
        Over.homMk (𝟙 T.left) (by simp)
      let x₁ : Over.mk (T.hom ≫ g ≫ f) ⟶ G := Over.homMk (x.left ≫ ψ) (by
        simp only [Over.mk_hom, Category.assoc, hψ.w]; simp only [← Category.assoc, Over.w])
      let y₁ : Over.mk (T.hom ≫ g ≫ f) ⟶ G := Over.homMk (y.left ≫ ψ) (by
        simp only [Over.mk_hom, Category.assoc, hψ.w]; simp only [← Category.assoc, Over.w])
      have hψxy := hψm T x y x₁ y₁ rfl rfl
      have hφxy := hφm (Over.mk (T.hom ≫ g)) x₀ y₀ (u ≫ x₁) (u ≫ y₁)
        (by simp [u, x₁, hx, hφ.lift_fst]) (by simp [u, y₁, hy, hφ.lift_fst])
      rw [← hφxy, ← hψxy, ← comp_mul]
      simp [u]
    · rw [Category.assoc, hφ.lift_snd, ← Category.assoc, Over.w, Over.w]
      rfl

end GlobalTheory.PlaceModel

namespace GlobalTheory.PlaceModel

end GlobalTheory.PlaceModel

namespace GlobalTheory.PlaceModel

end GlobalTheory.PlaceModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidSerreAmple
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid


open GlobalTheory.SerreField in
theorem serreAmple_of_finiteOrder_of_separated :
    FiniteOrderSt → SeparatedSt → SerreAmpleSt := by
  intro hfin hsep K _ _ A _ _ hA L hL hamp N hN3 hNK σ hσ hpull hfix
  haveI := hσ
  obtain ⟨m, hm0, hord⟩ := hfin K A hA L hL hamp σ hσ hpull
  have hFS : ∀ n : ℕ, 1 ≤ n → Flat (Out.mulA A n).left ∧ Surjective (Out.mulA A n).left :=
    fun n hn => flat_and_surjective_of_isFinite_abelianEnd
      forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K A hA _
      (GlobalTheory.AbLaw.MulN.isMonHom_mulA A n) (GlobalTheory.MulFiniteAny.isFinite_mulA K A hA n hn)
  have hu : IsMonHom (σ.hom * (𝟙 A)⁻¹) := by
    rw [Hom.mul_def, Hom.inv_def]; infer_instance
  obtain ⟨-, hdiv⟩ := GlobalTheory.TorsionDivisible.finite_torsion_and_divisible K A hA N hNK
  obtain ⟨φ, hφ, e⟩ := hdiv (σ.hom * (𝟙 A)⁻¹) hu (fun x hx => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hfix K (𝟙 _) x hx, Category.comp_id, mul_inv_cancel])
  haveI := hφ
  have key : toRing σ.hom = 1 := by
    refine GlobalTheory.eq_one_of_pow_eq_one_of_congr_one (homRing A) N hN3 ?_ ?_ (toRing σ.hom) (toRing φ) m
      hm0 ?_ ?_
    · rintro k ⟨f, u, hu, hf⟩ hk h
      have h1 := congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) h
      simp only [natCast_mul_apply, hf, Category.id_comp] at h1
      have h2 : u ^ k = 1 := h1
      have h3 : u = 1 := by
        obtain ⟨_, _⟩ := hFS k (by omega)
        haveI : Epi (Out.mulA A k).left := Flat.epi_of_flat_of_surjective _
        refine Over.OverMorphism.ext ((cancel_epi (Out.mulA A k).left).1 ?_)
        rw [← Over.comp_left, ← Over.comp_left, MonObj.comp_one, Out.mulA, MonObj.pow_comp,
          Category.id_comp, h2]
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · rintro q ⟨f, u, hu, hf⟩ hq h
      have h3 : u = 1 := hsep K A hA L hL hamp q hq u fun k => by
        obtain ⟨⟨g, v, hv, hg⟩, e⟩ := h k
        refine ⟨v, hv, ?_⟩
        have h1 := congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) e
        simp only [← Nat.cast_pow, natCast_mul_apply, hf, hg, Category.id_comp] at h1
        exact h1
      exact homRing_ext (by rw [hf, h3, Category.id_comp]; rfl)
    · refine homRing_ext ?_
      change _ = Additive.ofMul (𝟙 A) + ((N : homRing A) * toRing φ).1 _
      rw [natCast_mul_apply, toRing_apply, toRing_apply, Category.id_comp, Category.id_comp,
        ← ofMul_pow, ← e, ← ofMul_mul, mul_comm, inv_mul_cancel_right]
    · rw [toRing_pow]
      exact homRing_ext (by rw [toRing_apply, hord, Category.id_comp]; rfl)
  have h1 := congrArg (fun g : homRing A => g.1 (Additive.ofMul (𝟙 A))) key
  simp only [toRing_apply, Category.id_comp] at h1
  exact h1

end GlobalTheory.AmpleRigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorPullbackSupportAndEffective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorPullbackSupportAndEffective
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

set_option autoImplicit false in
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter in
private theorem unitAt_functionFieldMap_of_unitAt {X Y : Scheme} [IsIntegral X]
    [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] {y : Y} {f : X.functionField}
    (hf : _root_.GlobalTheory.Cartier.UnitAt (s y) f) :
    _root_.GlobalTheory.Cartier.UnitAt y (_root_.GlobalTheory.functionFieldMap s f) := by
  obtain ⟨a, hunit, ha⟩ := hf
  exact ⟨ConcreteCategory.hom (s.stalkMap y) a, hunit.map _, by
    rw [← _root_.GlobalTheory.functionFieldMap_algebraMap, ha]⟩

set_option autoImplicit false in
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter in
private theorem regAt_functionFieldMap_of_regAt {X Y : Scheme} [IsIntegral X]
    [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] {y : Y} {f : X.functionField}
    (hf : _root_.GlobalTheory.Cartier.RegAt (s y) f) :
    _root_.GlobalTheory.Cartier.RegAt y (_root_.GlobalTheory.functionFieldMap s f) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨ConcreteCategory.hom (s.stalkMap y) a, by
    rw [← _root_.GlobalTheory.functionFieldMap_algebraMap, ha]⟩


set_option autoImplicit false in
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter in
theorem _root_.GlobalTheory.Discrepancy.pullCart_supp_and_eff : ∀ (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (D : _root_.GlobalTheory.Cartier.CartierDiv X),
    (∀ y : Y, y ∈ (_root_.GlobalTheory.Discrepancy.pullCart s D).supp →
      s y ∈ D.supp) ∧
    (D.Eff → (_root_.GlobalTheory.Discrepancy.pullCart s D).Eff) := by
  intro X Y _ _ s _ D
  refine ⟨fun y hy => ?_, fun hD => ?_⟩
  · obtain ⟨g, hg⟩ := D.exists_isEqn (s y)
    have hg' := _root_.GlobalTheory.Discrepancy.isEqn_pullCart s hg
    rw [hg'.mem_supp_iff] at hy
    rw [hg.mem_supp_iff]
    intro hunit
    exact hy (unitAt_functionFieldMap_of_unitAt s hunit)
  · rw [_root_.GlobalTheory.Cartier.CartierDiv.eff_iff] at hD ⊢
    intro y g' hg'
    obtain ⟨g, hg⟩ := D.exists_isEqn (s y)
    have hpull := _root_.GlobalTheory.Discrepancy.isEqn_pullCart s hg
    have hquot := (hpull.iff_unitAt).1 hg'
    have hreg : _root_.GlobalTheory.Cartier.RegAt y
        ((_root_.GlobalTheory.Discrepancy.fnPull s g : (Y.functionField)ˣ) : Y.functionField) :=
      regAt_functionFieldMap_of_regAt s (hD (s y) g hg)
    have hprod := hquot.regAt.mul hreg
    rwa [div_mul_cancel₀ _ (Units.ne_zero _)] at hprod

end GlobalTheory.Discrepancy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorPullbackSupportAndEffectiveStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierDivisorPullback_support_and_effective : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (D : CartierDiv X), (∀ y : Y, y ∈ (pullCart s D).supp → s y ∈ D.supp) ∧ (D.Eff → (pullCart s D).Eff) := by
  first | exact @GlobalTheory.Discrepancy.pullCart_supp_and_eff | exact GlobalTheory.Discrepancy.pullCart_supp_and_eff | (intros; apply GlobalTheory.Discrepancy.pullCart_supp_and_eff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorialInvLe
noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD)

namespace GlobalTheory.JetExp

variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem sz_mul {r r' : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r' y) : Sz l lam (r + r') (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have e : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [e, map_mul, norm_mul, Real.rpow_add hl]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r r' : ℝ} {x : ℂ} (h : r ≤ r') (hx : Sz l lam r x) : Sz l lam r' x :=
  ⟨hx.1, hx.2.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Fact.out : l.Prime).one_lt.le) h)⟩

theorem sz_one : Sz l lam 0 1 := ⟨one_mem _, by
  have e : (⟨1, one_mem _⟩ : algebraicClosure ℚ ℂ) = 1 := rfl
  rw [e, map_one, norm_one, Real.rpow_zero]⟩

theorem sz_prod {ι : Type} (t : Finset ι) (r : ι → ℝ) (f : ι → ℂ) (h : ∀ i ∈ t, Sz l lam (r i) (f i)) :
    Sz l lam (∑ i ∈ t, r i) (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (sz_one (l := l) (lam := lam))
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact sz_mul (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem norm_factorial_inv_le (n : ℕ) : ‖((n.factorial : ℂ_[l]))‖⁻¹ ≤ (l : ℝ) ^ (n : ℝ) := by
  have hp : l.Prime := Fact.out
  have e1 : ((n.factorial : ℂ_[l])) = (((n.factorial : ℚ) : ℚ_[l]) : ℂ_[l]) := by simp
  rw [e1, PadicComplex.norm_extends', Padic.eq_padicNorm,
    padicNorm.eq_zpow_of_nonzero (by exact_mod_cast Nat.factorial_ne_zero n), padicValRat.of_nat]
  have hv : multiplicity l n.factorial ≤ n := multiplicity_factorial_le l n
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hp.one_lt.le
  rw [Rat.cast_zpow, Rat.cast_natCast, zpow_neg, inv_inv, zpow_natCast, Real.rpow_natCast]
  exact pow_le_pow_right₀ hl1 hv

theorem sz_factorial_inv (n : ℕ) : Sz l lam (n : ℝ) ((n.factorial : ℂ)⁻¹) := by
  have hm : ((n.factorial : ℂ)⁻¹) ∈ algebraicClosure ℚ ℂ := inv_mem (natCast_mem _ _)
  refine ⟨hm, ?_⟩
  have e : (⟨(n.factorial : ℂ)⁻¹, hm⟩ : algebraicClosure ℚ ℂ) = ((n.factorial : algebraicClosure ℚ ℂ))⁻¹ := by
    ext; simp
  rw [e, map_inv₀, map_natCast, norm_inv]
  exact norm_factorial_inv_le n

theorem expansion_of_jetInt : JetInt → Expansion := by
  classical
  intro hJ E _ _ _ _ I _ d φ s hφ hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy _ _ lam Ω hΩ
  obtain ⟨a, b, hab, hX⟩ := hJ E I d φ s hφ hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy lam Ω hΩ
  refine ⟨a, b, hab, fun g κ u hg hu => ?_⟩
  have h1 := hX g κ u hg hu
  have h2 : Sz l lam ((∑ i, κ i : ℕ) : ℝ) (∏ i, ((κ i).factorial : ℂ)⁻¹) := by
    rw [Nat.cast_sum]
    exact sz_prod _ _ _ fun i _ => sz_factorial_inv (κ i)
  have e : iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ))) =
      (iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / a i ^ (2 * s))) * ∏ i, ((κ i).factorial : ℂ)⁻¹ := by
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_mul_eq_div_div, div_eq_mul_inv (_ / _)]
  rw [e]
  refine sz_mono ?_ (sz_mul h1 h2)
  have hK : (0 : ℝ) ≤ ((∑ i, κ i : ℕ) : ℝ) := Nat.cast_nonneg _
  split_ifs <;> nlinarith

end GlobalTheory.JetExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidCube
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AmpleRigid
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AmpleCube

open GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.CubeThm

section
attribute [local instance] CategoryTheory.Hom.group

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

theorem cube_pic_of_gen (L : LB B.left) (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (x y z : B ⟶ B) :
    GlobalTheory.CechPic.pull (x * y * z).left (GlobalTheory.CechPic.cls L hL) +
                 GlobalTheory.CechPic.pull x.left (GlobalTheory.CechPic.cls L hL) +
                 GlobalTheory.CechPic.pull y.left (GlobalTheory.CechPic.cls L hL) +
                 GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls L hL) =
      GlobalTheory.CechPic.pull (x * y).left (GlobalTheory.CechPic.cls L hL) +
        GlobalTheory.CechPic.pull (x * z).left (GlobalTheory.CechPic.cls L hL) +
        GlobalTheory.CechPic.pull (y * z).left (GlobalTheory.CechPic.cls L hL) +
        GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls L hL) := by
  set c := GlobalTheory.CechPic.cls L hL
  have hT : (Theta B L).IsLB := LB.isLB_linComb hL _ _
  have h0 : GlobalTheory.CechPic.cls (Theta B L) hT = 0 := (GlobalTheory.CechPic.cls_eq_zero_iff hT).2 hΘ
  have h1 : (∑ I : ULift.{0} (Finset (Fin 3)),
      ((-1 : ℤ) ^ (3 - I.down.card)) • GlobalTheory.CechPic.pull (psum B (x3 B) I.down).left c) = 0 :=
    (GlobalTheory.CechPic.cls_linComb hL (fun I : ULift.{0} (Finset (Fin 3)) => (psum B (x3 B) I.down).left)
      (fun I => (-1 : ℤ) ^ (3 - I.down.card)) hT).symm.trans h0
  have h2 := congrArg (GlobalTheory.CechPic.pull (lift x (lift y z)).left) h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at h2
  simp only [map_zsmul, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, CubeThm.comp_psum, lift_comp_cubeCoordinates] at h2
  rw [← Equiv.ulift.symm.sum_comp] at h2
  simp only [Equiv.ulift_symm_down] at h2
  rw [show (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide] at h2
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at h2
  have e0 : psum B ![x, y, z] ∅ = 1 := rfl
  have e1 : psum B ![x, y, z] {0} = x := (show _ = x * 1 from rfl).trans (mul_one x)
  have e2 : psum B ![x, y, z] {1} = y := (show _ = y * 1 from rfl).trans (mul_one y)
  have e3 : psum B ![x, y, z] {2} = z := (show _ = z * 1 from rfl).trans (mul_one z)
  have e4 : psum B ![x, y, z] {0, 1} = x * y :=
    (show _ = x * (y * 1) from rfl).trans (congrArg (x * ·) (mul_one y))
  have e5 : psum B ![x, y, z] {0, 2} = x * z :=
    (show _ = x * (z * 1) from rfl).trans (congrArg (x * ·) (mul_one z))
  have e6 : psum B ![x, y, z] {1, 2} = y * z :=
    (show _ = y * (z * 1) from rfl).trans (congrArg (y * ·) (mul_one z))
  have e7 : psum B ![x, y, z] {0, 1, 2} = x * y * z :=
    (show _ = x * (y * (z * 1)) from rfl).trans
      ((congrArg (x * ·) (congrArg (y * ·) (mul_one z))).trans (mul_assoc x y z).symm)
  rw [e0, e1, e2, e3, e4, e5, e6, e7] at h2
  have c0 : (∅ : Finset (Fin 3)).card = 0 := rfl
  have c1 : ({0} : Finset (Fin 3)).card = 1 := rfl
  have c2 : ({1} : Finset (Fin 3)).card = 1 := rfl
  have c3 : ({2} : Finset (Fin 3)).card = 1 := rfl
  have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := rfl
  have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := rfl
  have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := rfl
  have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := rfl
  rw [c0, c1, c2, c3, c4, c5, c6, c7] at h2
  norm_num at h2
  rw [← sub_eq_zero]
  rw [← h2]
  abel

end

theorem cubeSt : CubeSt := by
  intro K _ _ A _ _ hA L hL hamp c x y z
  obtain ⟨M, hM, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  exact cube_pic_of_gen A M hM (GlobalTheory.exists_gen_theta_of_isAbelianScheme K A hA M hM) x y z

end GlobalTheory.AmpleCube
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomTrivialModPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomTrivialModPow
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory

namespace TorusThicken

theorem pullback_map_eq_of_comp {S S' S'' : Scheme.{0}} (s : S'' ⟶ S') (p : S' ⟶ S) {V W : Over S}
    {a b : V ⟶ W} (h : (Over.pullback p).map a = (Over.pullback p).map b) :
    (Over.pullback (s ≫ p)).map a = (Over.pullback (s ≫ p)).map b := by
  have ha := (Over.pullbackComp s p).hom.naturality a
  have hb := (Over.pullbackComp s p).hom.naturality b
  simp only [Functor.comp_map] at ha hb
  rw [← cancel_mono ((Over.pullbackComp s p).hom.app W), ha, hb, h]

theorem pullback_pullback_map_eq_of_comp {S S' S'' : Scheme.{0}} (s : S'' ⟶ S') (p : S' ⟶ S)
    {V W : Over S} {a b : V ⟶ W} (h : (Over.pullback (s ≫ p)).map a = (Over.pullback (s ≫ p)).map b) :
    (Over.pullback s).map ((Over.pullback p).map a) = (Over.pullback s).map ((Over.pullback p).map b) := by
  have ha := (Over.pullbackComp s p).hom.naturality a
  have hb := (Over.pullbackComp s p).hom.naturality b
  simp only [Functor.comp_map] at ha hb
  rw [← cancel_epi ((Over.pullbackComp s p).hom.app V), ← ha, ← hb, h]

end TorusThicken


open TorusThicken in
theorem splitTorus_hom_trivial_mod_pow (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (A : Type) [AddCommGroup A] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (f : splitTorus (Spec (CommRingCat.of R)) A ⟶ G) (hf : IsMonHom f)
    (h : (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map f =
      (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map 1) (n : ℕ) :
    (Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map 1 := by
  set I := IsLocalRing.maximalIdeal R ^ (n + 1) with hI
  set p := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) with hp
  have hIt : I ≠ ⊤ := fun e => (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.1 (e ▸ Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hIt
  have : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  set J : Ideal (R ⧸ I) := (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I) with hJ
  have hJn : IsNilpotent J := ⟨n + 1, by
    rw [hJ, ← Ideal.map_pow, ← hI, Ideal.map_quotient_self]; rfl⟩
  set q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) with hq
  let ℓ : IsLocalRing.ResidueField R →+* (R ⧸ I) ⧸ J :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) ((Ideal.Quotient.mk J).comp (Ideal.Quotient.mk I))
      (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem _ ha)
  have hsq : q ≫ p = Spec.map (CommRingCat.ofHom ℓ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))) := by
    rw [hq, hp, ← Spec.map_comp, ← Spec.map_comp]; rfl

  have h1 : (Over.pullback q).map ((Over.pullback p).map f) =
      (Over.pullback q).map ((Over.pullback p).map 1) := by
    apply pullback_pullback_map_eq_of_comp
    rw [hsq]
    exact pullback_map_eq_of_comp _ _ h
  obtain ⟨e, he, -⟩ := splitTorus_baseChange _ _ p A
  have hg : IsMonHom (e.hom ≫ (Over.pullback p).map f) := inferInstance
  have hp1 : (Over.pullback p).map (1 : splitTorus (Spec (CommRingCat.of R)) A ⟶ G) = 1 :=
    Functor.map_one _
  have key := splitTorus_hom_eq_one_of_nilpotent (R ⧸ I) J hJn A _ (e.hom ≫ (Over.pullback p).map f) hg
    (by rw [Functor.map_comp, h1, hp1, ← Functor.map_comp, ← Hom.one_def, MonObj.comp_one])
  rw [← cancel_epi e.hom, key, ← Hom.one_def, hp1, MonObj.comp_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomTrivialModPowStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorus_hom_pullback_quotient_pow_eq_one : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A : Type) [AddCommGroup A] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (f : splitTorus (Spec (CommRingCat.of R)) A ⟶ G), IsMonHom f → (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map f = (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R (IsLocalRing.ResidueField R)).map 1 → ∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f = (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map 1 := by
  first | exact @GlobalTheory.splitTorus_hom_trivial_mod_pow | exact GlobalTheory.splitTorus_hom_trivial_mod_pow | (intros; apply GlobalTheory.splitTorus_hom_trivial_mod_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumNatCastEq
set_option autoImplicit false

noncomputable section

open NumberField
open scoped nonZeroDivisors
open GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.PairFourier

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem tsum_natCast_eq {ι : Type} (n : ι → ℕ) (h : Summable (fun i ↦ (n i : ℂ))) :
    ∃ m : ℕ, ∑' i, (n i : ℂ) = m := by
  have hfin : (Function.support n).Finite := by
    have ht := h.tendsto_cofinite_zero
    have hev : ∀ᶠ i in Filter.cofinite, ‖(n i : ℂ)‖ < 1 := by
      have := ht.norm
      simp only [norm_zero] at this
      exact this.eventually (gt_mem_nhds (by norm_num))
    refine (Filter.eventually_cofinite.1 hev).subset ?_
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Set.mem_setOf_eq, not_lt]
    have : (1 : ℝ) ≤ n i := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi
    simpa [Complex.norm_natCast] using this
  refine ⟨∑ i ∈ hfin.toFinset, n i, ?_⟩
  rw [tsum_eq_sum (s := hfin.toFinset)]
  · push_cast; rfl
  · intro i hi
    simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hi
    simp [hi]

variable {F : Type} [Field F] [NumberField F]

theorem norm_div_eq_nat (𝔞 : Frac F) {ν : F} (hν : ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ m : ℕ, |((Algebra.norm ℚ ν : ℚ) : ℝ)| / nrm 𝔞 = m := by
  set J : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.spanSingleton (𝓞 F)⁰ ν * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) with hJdef
  have hle : J ≤ 1 := by
    have h1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ ν ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) :=
      FractionalIdeal.spanSingleton_le_iff_mem.2 hν
    calc J ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
          mul_le_mul_left h1 _
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hJa : J * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ ν := by
    rw [hJdef, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hn := congrArg FractionalIdeal.absNorm hJa
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, ← hI, FractionalIdeal.coeIdeal_absNorm] at hn
  have h0 : (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℚ) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact Units.ne_zero 𝔞
  refine ⟨Ideal.absNorm I, ?_⟩
  unfold nrm
  rw [div_eq_iff (by exact_mod_cast h0)]
  have := congrArg (fun q : ℚ ↦ (q : ℝ)) hn
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs] at this
  rw [← this]

variable [IsTotallyReal F]

def pairPt (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) : GlobalTheory.RealMult.FracId.elt (𝔞 * 𝔟) :=
  ⟨c.out.1.1 * c.out.1.2, by
    show _ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F)
    rw [Units.val_mul]
    exact FractionalIdeal.mul_mem_mul c.out.2.1 c.out.2.2.1⟩

def pairCoef (𝔞 𝔟 : Frac F) (k : ℕ) (c : Quotient (qRel 𝔞 𝔟)) : ℕ :=
  (norm_div_eq_nat 𝔞 c.out.2.1).choose ^ (k - 1)

theorem qClass_eq (𝔞 𝔟 : Frac F) (k : ℕ) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) :
    qClass 𝔞 𝔟 k z c = (pairCoef 𝔞 𝔟 k c : ℂ) * GlobalTheory.RealMult.qPower ((pairPt 𝔞 𝔟 c : F)) z := by
  unfold qClass qTerm pairCoef pairPt
  have hs := (norm_div_eq_nat 𝔞 c.out.2.1).choose_spec
  generalize (norm_div_eq_nat 𝔞 c.out.2.1).choose = m at hs ⊢
  rw [hs]
  push_cast
  rfl

theorem pairPt_ne_zero (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) : pairPt 𝔞 𝔟 c ≠ 0 := by
  intro h
  have h' : c.out.1.1 * c.out.1.2 = 0 := congrArg Subtype.val h
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
  have := c.out.2.2.2 hr.embedding
  rw [h', map_zero] at this
  exact lt_irrefl _ this

end GlobalTheory.PairFourier
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicPointLiftsFiniteType
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.CovTop GlobalTheory.CovHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CovLift

theorem exists_lift_of_locallyOfFiniteType : ∀ (V Y : Scheme.{0}) (π : V ⟶ Y), LocallyOfFiniteType π → ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ Y) (u : V), π u = y (IsLocalRing.closedPoint K) → ∃ w : Sp K ⟶ V, w ≫ π = y := by
  intro V Y π hπ K _ _ y u hu
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := y) u (IsLocalRing.closedPoint K) hu
  have : JacobsonSpace ↥(pullback π y : Scheme.{0}) := LocallyOfFiniteType.jacobsonSpace (pullback.snd π y)
  obtain ⟨c, -, hc'⟩ := nonempty_inter_closedPoints (X := ↥(pullback π y : Scheme.{0})) (Z := Set.univ) ⟨z, trivial⟩
    isOpen_univ.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π y) c hc ≫ pullback.fst π y, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

end GlobalTheory.CovLift
end
