module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRestrIsoTens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivLeSubMulDiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeParametersBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RankGrowthBoundSmallScale

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HermitianGeometricHypothesisHolds
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GeneratedWeightsMulStableAndBounded
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CuspidalSectionsMulMem
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem cusp_form_section_mul : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (a b : AllWt.Weight (T.Q.Dw j)) (w : Cusp Z Y.U a) (f : Cusp Z Y.U b), _root_.GlobalTheory.CovTop.Hypotheses'' → ∃ g : Cusp Z Y.U (a + b), g.1 = w.1 * f.1 ∧ (w ∈ latOn Y.U Z _ → f ∈ latOn Y.U Z _ → g ∈ latOn Y.U Z _) := by
  intro D T j Y e o _ _ Z a b w f _
  have hm : w.1 * f.1 ∈ Cusp Z Y.U (a + b) := by
    show w.1 * f.1 ∈ cuspOn Y.U Z (wtOf _ (a + b) 0)
    have h := GlobalTheory.AllWt.wtOf_add (Dw := T.Q.Dw j) a b 0 0
    rw [add_zero] at h
    rw [h]
    refine ⟨GlobalTheory.SlopeRec.mul_mem_cuspW ⟨0, by simp [GlobalTheory.AllWt.wtOf_snd]⟩ ⟨0, by simp [GlobalTheory.AllWt.wtOf_snd]⟩ w.2.1 f.2.1,
      GlobalTheory.AllWt.mul_mem_suppOn _ f.2.2⟩
  exact ⟨⟨_, hm⟩, rfl, fun hw hf => GlobalTheory.AllWt.mul_mem_supLat hw hf hm⟩
end GlobalTheory.HSApp
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_sections_mul_mem : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (a b : AllWt.Weight (T.Q.Dw j)) (w : Cusp Z Y.U a) (f : Cusp Z Y.U b), _root_.GlobalTheory.CovTop.Hypotheses'' → ∃ g : Cusp Z Y.U (a + b), g.1 = w.1 * f.1 ∧ (w ∈ latOn Y.U Z _ → f ∈ latOn Y.U Z _ → g ∈ latOn Y.U Z _) := by
  first | exact @_root_.GlobalTheory.HSApp.cusp_form_section_mul | exact _root_.GlobalTheory.HSApp.cusp_form_section_mul | (intros; apply _root_.GlobalTheory.HSApp.cusp_form_section_mul <;> assumption)
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem generated_weights_mul_stable_and_bounded : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif) (h : Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict) (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂) (th : R.L.Sec) (k : Consts), BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ k.beta → (h.data f₁ f₂ th k).MulStable ∧ (h.data f₁ f₂ th k).MulBound fun _ => k.beta := by
  intro hPr D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k hB
  have tr : ∀ (a b : AllWt.Weight (T.Q.Dw j)) (_ : a = b) (g : Cusp Z Y.U a), ∃ g' : Cusp Z Y.U b, g'.1 = g.1 ∧
      (g ∈ latOn Y.U Z (wtOf _ a 0) → g' ∈ latOn Y.U Z (wtOf _ b 0)) := by
    rintro a b rfl g
    exact ⟨g, rfl, id⟩
  have key : ∀ (i : ℕ) (hi : i < P.T) (w' : Cusp Z Y.U P.u₁) (f' : Cusp Z Y.U (P.wt i)),
      ∃ g' : Cusp Z Y.U (P.wt (i + 1)), g'.1 = w'.1 * f'.1 ∧
        (w' ∈ latOn Y.U Z (wtOf _ P.u₁ 0) → f' ∈ latOn Y.U Z (wtOf _ (P.wt i) 0) →
          g' ∈ latOn Y.U Z (wtOf _ (P.wt (i + 1)) 0)) ∧
        ((h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g' : (h.data f₁ f₂ th k).V (i + 1)) :
            (h.data f₁ f₂ th k).Sec (i + 1)) =
          (h.data f₁ f₂ th k).mulW i (f₁.b.equivFun w') (h.equivV f₁ f₂ th k hi.le f') := by
    intro i hi w' f'
    have hx := _root_.GlobalTheory.T.cuspidal_sections_mul_mem D T j Y e o hG hE Z P.u₁ (P.wt i) w' f' hPr
    obtain ⟨g, hg, hgl⟩ := hx
    have hy := tr _ _ (P.u₁_add_wt i) g
    obtain ⟨g', hg', hgl'⟩ := hy
    refine ⟨g', hg'.trans hg, fun a b => hgl' (hgl a b), ?_⟩
    exact (h.coe_equivV f₁ f₂ th k _ g').trans ((h.mulW_adjSec f₁ f₂ th k i w' f' g' (hg'.trans hg)).symm.trans
      (congrArg _ (h.coe_equivV f₁ f₂ th k hi.le f').symm))
  refine ⟨?_, ?_⟩
  · intro i hi w hw f hf
    have hk := key i hi (f₁.b.equivFun.symm w) ((h.equivV f₁ f₂ th k hi.le).symm f)
    obtain ⟨g', -, hl, he⟩ := hk
    have hw' : f₁.b.equivFun.symm w ∈ latOn Y.U Z (wtOf _ P.u₁ 0) :=
      (h.mem_lattice f₁ f₂ th k _).1
        (Eq.mpr (congrArg (· ∈ (h.data f₁ f₂ th k).lattice) (f₁.b.equivFun.apply_symm_apply w)) hw)
    have hf' : (h.equivV f₁ f₂ th k hi.le).symm f ∈ latOn Y.U Z (wtOf _ (P.wt i) 0) :=
      (h.equivV_mem f₁ f₂ th k hi.le _).1
        (Eq.mpr (congrArg (· ∈ (h.data f₁ f₂ th k).M i) (LinearEquiv.apply_symm_apply _ f)) hf)
    refine ⟨h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g', (h.equivV_mem f₁ f₂ th k _ g').2 (hl hw' hf'), ?_⟩
    exact he.trans (congrArg₂ (fun a b => (h.data f₁ f₂ th k).mulW i a b) (f₁.b.equivFun.apply_symm_apply w)
      (congrArg Subtype.val (LinearEquiv.apply_symm_apply _ f)))
  · intro i hi σ w hw f hf g hg
    have pe : ∀ (a b : AllWt.Weight (T.Q.Dw j)), a = b → ∀ σ x,
        petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ a 0) σ x =
          petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ b 0) σ x := by
      rintro a b rfl σ x
      rfl
    have hk := key i hi (f₁.b.equivFun.symm w) ((h.equivV f₁ f₂ th k hi.le).symm f)
    obtain ⟨g', hgp, -, he⟩ := hk
    have hgg : g = h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g' :=
      Subtype.ext (hg.trans ((congrArg₂ (fun a b => (h.data f₁ f₂ th k).mulW i a b) (f₁.b.equivFun.apply_symm_apply w)
        (congrArg Subtype.val (LinearEquiv.apply_symm_apply _ f))).symm.trans he.symm))
    have hb := GlobalTheory.T.petersson_norm_mul_le_sqrt_bergman_mul_component D T j Y e o hG hE Z P.u₁ (P.wt i) (f₁.b.equivFun.symm w)
      ((h.equivV f₁ f₂ th k hi.le).symm f) k.beta (zero_le_one.trans k.one_le_beta) hB σ
    have e0 : petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.wt (i + 1)) 0) σ g'.1 =
        petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.u₁ + P.wt i) 0) σ
          ((f₁.b.equivFun.symm w).1 * ((h.equivV f₁ f₂ th k hi.le).symm f).1) :=
      (congrArg (petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.wt (i + 1)) 0) σ) hgp).trans
        (pe _ _ (P.u₁_add_wt i).symm σ _)
    have e1 := h.nrm_equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) σ g'
    have e2 := h.normAt_eq f₁ f₂ th k σ (f₁.b.equivFun.symm w)
    have e3 := h.nrm_equivV f₁ f₂ th k hi.le σ ((h.equivV f₁ f₂ th k hi.le).symm f)
    have e2' := (congrArg ((h.data f₁ f₂ th k).normAt σ) (f₁.b.equivFun.apply_symm_apply w).symm).trans e2
    have e3' := (congrArg (((h.data f₁ f₂ th k).nm i).nrm σ) (LinearEquiv.apply_symm_apply _ f).symm).trans e3
    calc _ = _ := congrArg (((h.data f₁ f₂ th k).nm (i + 1)).nrm σ) hgg
      _ = _ := e1
      _ = _ := e0
      _ ≤ _ := hb
      _ = _ := congrArg₂ (fun a b => Real.sqrt k.beta * a * b) e2'.symm e3'.symm
end GlobalTheory.HSApp
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.HSApp.geometric_hypothesis_of_components : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif) (h : Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict) (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ Λ₀ : ℝ, WtBig P → RatGen TF.X Z Y.U P.u₁ → RatGen TF.X Z Y.U P.u₂ → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ k.beta → 1 ≤ k.abelian₂ → (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ k.abelian₂) → 1 ≤ Λ₀ → (h.data f₁ f₂ th k).ShortFamily 0 Λ₀ → (h.data f₁ f₂ th k).ShortFamily (dimFlag (T.Q.Dw j)) k.LamD → (h.data f₁ f₂ th k).ShortFamily P.T k.LamT → GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ := by
  intro hPr hGD hQ hNad hPrin hSi hFa hLie D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k Λ₀ hW hR₁ hR₂ hB hL hLe h1 hS0 hSD hST
  have hNN := hQ.nef
  have hF := hG.geo
  have hA : IsNef Y.d.c₂.F (h.geo f₁ f₂ th k).LA ∧ IsBig Y.d.c₂.F (h.geo f₁ f₂ th k).LA := by
    apply _root_.GlobalTheory.T.hodge_bundle_isNef_isBig_of_weight <;> assumption
  obtain ⟨hnef, hbig⟩ := hA
  have hbir := GlobalTheory.HSApp.birational_of_ratGen TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k hR₁
  have hbir₂ := GlobalTheory.HSApp.geo_second_birational TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k hR₂
  obtain ⟨hms, hmb⟩ := _root_.GlobalTheory.HSApp.generated_weights_mul_stable_and_bounded hPr D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k hB
  have hnb₂ : IsNef Y.d.c₂.F (h.data f₁ f₂ th k).L₂ ∧ IsBig Y.d.c₂.F (h.data f₁ f₂ th k).L₂ :=
    GlobalTheory.BirationalBig.isNef_and_isBig hQ _ (h.geo f₁ f₂ th k).second.toLinSys
    (h.geo f₁ f₂ th k).alg₂.variety (h.geo f₁ f₂ th k).alg₂.bpf hbir₂
  have hTC : IsTotallyComplex Y.d.c₂.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := Y.d.c₂) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  obtain ⟨hD, hT, -, -, hLam, -, hLD, hLT, -⟩ := Ready.data_numbers h f₁ f₂ th k
  refine ⟨hTC, ?_, ?_, ?_, ?_, ?_, hms, hmb, ?_, ?_, h1, hS0, ?_, ?_⟩
  · exact hbir
  · exact hnef
  · exact hbig
  · exact hnb₂.1
  · exact hnb₂.2
  · intro q σ
    rw [hLam]
    exact hLe q σ
  · rw [hLam]; exact hL
  · rw [hD, hLD]; exact hSD
  · rw [hT, hLT]; exact hST
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_geometric_hypothesis_holds : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif) (h : Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict) (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ Λ₀ : ℝ, WtBig P → RatGen TF.X Z Y.U P.u₁ → RatGen TF.X Z Y.U P.u₂ → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ k.beta → 1 ≤ k.abelian₂ → (∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ k.abelian₂) → 1 ≤ Λ₀ → (h.data f₁ f₂ th k).ShortFamily 0 Λ₀ → (h.data f₁ f₂ th k).ShortFamily (dimFlag (T.Q.Dw j)) k.LamD → (h.data f₁ f₂ th k).ShortFamily P.T k.LamT → GlobalTheory.HSShort.GeoHyp (h.data f₁ f₂ th k) Λ₀ := by
  first | exact @_root_.GlobalTheory.HSApp.geometric_hypothesis_of_components | exact _root_.GlobalTheory.HSApp.geometric_hypothesis_of_components | (intros; apply _root_.GlobalTheory.HSApp.geometric_hypothesis_of_components <;> assumption)
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
namespace GlobalTheory.HSShortRun
open GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
variable {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j}
theorem hilbertSamuel_estimate_at_level (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : Quoted)
    (hN : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hPr : GlobalTheory.Published.Principalisation)
    (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hC : GlobalTheory.Published.ToroidalChartsForFan)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    (hE : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) {P : WtPar (T.Q.Dw j)} (hW : WtBig P)
    (hA : ∀ i ≤ P.T, Y.GoodAt (wtOf _ (P.wt i) 0)) {PP κ : ℝ} (hPP : 0 ≤ PP) (hκ : 0 ≤ κ)
    (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂)
    (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) {Λ β : ℝ} (hΛ : 1 ≤ Λ) (hβ : 1 ≤ β)
    (hfr : ∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ)
    (hberg : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ β)
    (hBir : BirOn Y.U Z (wtOf _ P.u₁ 0) ∧ BirOn Y.U Z (wtOf _ P.u₂ 0))
    (h0 : ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U (P.wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧
      Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z
        (wtOf _ (P.wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)))
    (hsh : ∀ i ≤ P.T, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U (P.wt i)), (∀ q, v q ∈ latOn Y.U Z _) ∧
      Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z
        (wtOf _ (P.wt i) 0) σ (v q).1 ≤ Real.exp (PP * κ)) :
    1 ≤ (f₁.n : ℝ) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 P.T (CompHt.dimFlag (T.Q.Dw j)) f₁.n 1 Λ β (Real.exp (PP * κ))
      (Real.exp (PP * κ)) (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)) (Y.dg P.u₁ Z) (Y.ht P.u₁ Z)
      (Y.rkC (P.wt P.T) Z) (Y.degC (P.wt P.T) Z) := by
  obtain ⟨TF, R, ω, h⟩ := _root_.GlobalTheory.T.exists_weight_hodge_bundle_generated hP hG hQ hN hPr hS hC hL D T j Y e o hY hE Z P hW hA
  have hPk : 0 ≤ PP * κ := mul_nonneg hPP hκ
  let k : Consts := ⟨Λ, β, Real.exp (PP * κ), Real.exp (PP * κ), 0, hβ, Real.one_le_exp hPk, Real.one_le_exp hPk⟩
  let th : R.L.Sec := 0
  have r₁ := GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₁ ⟨R.toModif⟩ hBir.1
  have r₂ := GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₂ ⟨R.toModif⟩ hBir.2
  have hΛ₀ : 1 ≤ Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)) := Real.one_le_exp (by positivity)
  have sh : ∀ i ≤ P.T, (h.data f₁ f₂ th k).ShortFamily i (Real.exp (PP * κ)) := fun i hi => by
    obtain ⟨m, v, l, s, n⟩ := hsh i hi
    exact GlobalTheory.HSApp.shortFamily_of_spanning _ _ _ _ _ _ TF Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k i hi _ m v l s n
  have s0 : (h.data f₁ f₂ th k).ShortFamily 0 (Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1))) := by
    obtain ⟨m, v, l, s, n⟩ := h0
    exact GlobalTheory.HSApp.shortFamily_of_spanning _ _ _ _ _ _ TF Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k 0 P.T.zero_le _ m v l s n
  have hDT : FlagTan.dimFlag (T.Q.Dw j) ≤ P.T := (Nat.le_succ _).trans h.le_T
  have hyp := _root_.GlobalTheory.T.hermitian_geometric_hypothesis_holds hP hG hQ hN hPr hS hC hL D T j Y e o hY hE Z TF P R ω h f₁ f₂ th k _ hW r₁ r₂ hberg hΛ hfr hΛ₀ s0
    (sh _ hDT) (sh _ le_rfl)
  have hC := GlobalTheory.T.hilbertSamuel_component_short_basis_bound hQ _ _ _ _ _ _ _ TF.X Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k _ hyp
  have hrk : Y.rkC (P.wt P.T) Z = Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf _ (P.wt P.T) 0)) := by
    show ((Formalism.HN.rkK _ : ℕ) : ℝ) = _
    rw [Formalism.HN.rkK, (h.good _ le_rfl).2.2, finrank_top]
  rw [Real.log_exp] at hC
  refine ⟨by exact_mod_cast (h.geo f₁ f₂ th k).one_le_n, ?_⟩
  rw [hrk]
  exact hC
end GlobalTheory.HSShortRun
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
end
