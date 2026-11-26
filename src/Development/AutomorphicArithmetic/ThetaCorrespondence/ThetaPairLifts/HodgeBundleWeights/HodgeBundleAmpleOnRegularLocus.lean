module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleDominatesOfLargeWeight
section
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
namespace GlobalTheory.HodgeDominates
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
theorem exists_weight_hodgeBundle_dominates : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : AllWt.Weight Dw, ∀ y ∈ U₀ TF.X Z, ∀ A : LB TF.Y.X, A.IsLB → ∃ (m : ℕ) (s : (LB.div (lbPow (L₀ TF.X Z χ) m) (A.pull (inc₀ TF.X Z ≫ TF.X.π))).Sec), 0 < m ∧ y ∈ nonzeroLocus s := by
  intro hP _ hS hF E _ _ _ H Dw l Xo c TF Z _
  obtain ⟨ω, hω, e, h⟩ := exists_lb_dominates (E := E) (H := H) (Dw := Dw) (l := l) (Xo := Xo) (c := c) hP.p22 hS hF TF
  refine ⟨FlagMod.mu0 Dw, fun y hy A hA => ?_⟩
  obtain ⟨w, hw⟩ : ∃ w, TF.Y.j w = (inc₀ TF.X Z ≫ TF.X.π) y := hy
  obtain ⟨m, hm, s, hs⟩ := h w A hA
  have hD := LB.isLB_div (isLB_lbPow hω m) hA
  have hL := isLB_L₀ TF.X Z (FlagMod.mu0 Dw)
  have hT := LB.isLB_div (isLB_lbPow hL m) (pull_isLB hA (inc₀ TF.X Z ≫ TF.X.π))
  have e' : cls _ hL = CechPic.pull (inc₀ TF.X Z ≫ TF.X.π) (cls ω hω) := by
    rw [CechPic.pull_comp, ← e]
    exact cls_pull (TF.X.isLB_Llam _) _ _
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hT (pull_isLB hD (inc₀ TF.X Z ≫ TF.X.π))
    ((cls_eq_iff hT (pull_isLB hD _)).1 (by
      rw [cls_div (isLB_lbPow hL m) (pull_isLB hA _), cls_lbPow hL, cls_pull hA, cls_pull hD,
        cls_div (isLB_lbPow hω m) hA, cls_lbPow hω, map_sub, map_nsmul, e'])) (lbSecPull _ s _)
  refine ⟨m, t, hm, ?_⟩
  rw [ht, nonzeroLocus_lbSecPull]
  exact (hw ▸ hs : (inc₀ TF.X Z ≫ TF.X.π) y ∈ nonzeroLocus s)
end GlobalTheory.HodgeDominates
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeBundle_dominates_of_large_weight : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∃ χ : AllWt.Weight Dw, ∀ y ∈ U₀ TF.X Z, ∀ A : LB TF.Y.X, A.IsLB → ∃ (m : ℕ) (s : (LB.div (lbPow (L₀ TF.X Z χ) m) (A.pull (inc₀ TF.X Z ≫ TF.X.π))).Sec), 0 < m ∧ y ∈ nonzeroLocus s := by
  first | exact @_root_.GlobalTheory.HodgeDominates.exists_weight_hodgeBundle_dominates | exact _root_.GlobalTheory.HodgeDominates.exists_weight_hodgeBundle_dominates | (intros; apply _root_.GlobalTheory.HodgeDominates.exists_weight_hodgeBundle_dominates <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsWeightIsAmpleLineBundleComp
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RelAmpleComp
open GlobalTheory.FlagMod (FlagCover FlagModel)
private def commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) : LB Y where
  ι := C.J
  U j := (B s).U (C.idx s j)
  g j j' := (B s).g (C.idx s j) (C.idx s j')
private theorem isLB_commonRestr {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    (commonRestr C s).IsLB := {
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨j, hj⟩ := C.cover y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (C.mem s j y).2 hj⟩
  g_self j := (C.isLB s).g_self (C.idx s j)
  cocycle i j k := (C.isLB s).cocycle (C.idx s i) (C.idx s j) (C.idx s k) }
private theorem commonRestr_iso {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (s : Λ) :
    LBIso (commonRestr C s) (B s) :=
  iso_of_chart (C.isLB s)
    { idx := C.idx s
      le := fun _ _ h => h
      g := fun _ _ _ _ _ => rfl }
private theorem commonRestr_iso_tens {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    LBIso (commonRestr C (a + b)) (tens (B a) (B b)) :=
  iso_of_chart (isLB_tens (C.isLB a) (C.isLB b))
    { idx := fun j => (C.idx a j, C.idx b j)
      le := fun j y h => by
        have h' : y ∈ C.U j := (C.mem (a + b) j y).1 h
        exact ⟨(C.mem a j y).2 h', (C.mem b j y).2 h'⟩
      g := fun y j j' hj hj' => by
        have h₁ : y ∈ C.U j := (C.mem (a + b) j y).1 hj
        have h₂ : y ∈ C.U j' := (C.mem (a + b) j' y).1 hj'
        refine (C.add a b y j j' h₁ h₂).trans ?_
        exact (tr_tens (B a) (B b) y (a := (C.idx a j, C.idx b j)) (b := (C.idx a j', C.idx b j'))
          ⟨(C.mem a j y).2 h₁, (C.mem b j y).2 h₁⟩ ⟨(C.mem a j' y).2 h₂, (C.mem b j' y).2 h₂⟩).symm }
private theorem cls_common_add {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (a b : Λ) :
    cls (B (a + b)) (C.isLB (a + b)) = cls (B a) (C.isLB a) + cls (B b) (C.isLB b) := by
  have e₁ := (cls_eq_iff (isLB_commonRestr C (a + b)) (C.isLB (a + b))).2 (commonRestr_iso C (a + b))
  have e₂ := (cls_eq_iff (isLB_commonRestr C (a + b)) (isLB_tens (C.isLB a) (C.isLB b))).2
    (commonRestr_iso_tens C a b)
  rw [← e₁, e₂, cls_tens (C.isLB a) (C.isLB b)]
theorem exists_weight_isAmple_lineBundle_comp : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∃ ρ : AllWt.Weight Dw, ∀ A : LB TF.Y.X, A.IsLB → IsAmpleLB A → ∃ n : ℕ, IsAmpleLB (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)) := by
  intro _ _ E _ _ _ H Dw l Xo c TF Z hF
  refine ⟨fun _ k => if (k : ℕ) < Dw.p then ((k : ℕ) : ℤ) - Dw.p else ((k : ℕ) : ℤ) - Dw.p + 1, ?_⟩
  intro A hA hAmp
  set ρ : AllWt.Weight Dw := fun _ k => if (k : ℕ) < Dw.p then ((k : ℕ) : ℤ) - Dw.p else ((k : ℕ) : ℤ) - Dw.p + 1 with hρ
  let e : Ix Dw → ℤ := fun ix => ix.elim 0 fun p => (Dw.mult p.1 : ℤ) - ((p.2 : ℕ) : ℤ)
  have hex : AllWt.exOf Dw ρ 0 = -e := by
    refine GlobalTheory.FlagMod.exOf_ext rfl (fun τ i hi => ?_) (fun τ i hi => ?_)
    · have hm := GlobalTheory.FlagMod.mult_of_mem (Dw := Dw) τ
      have h2 := i.2
      simp only [hρ, e, Pi.neg_apply, Option.elim]
      rw [if_pos (by omega)]
      omega
    · have hm := GlobalTheory.FlagMod.mult_conj (Dw := Dw) τ
      have h2 := i.2
      simp only [hρ, e, Pi.neg_apply, Option.elim]
      rw [if_neg (by omega)]
      push_cast
      omega
  have : IsProper TF.Y.s := projProper _ _ _ TF.Y.proj
  have : CompactSpace TF.Y.X := QuasiCompact.compactSpace_of_compactSpace TF.Y.s
  have : IsProper TF.X.π := TF.X.proper
  have : CompactSpace TF.X.YY := QuasiCompact.compactSpace_of_compactSpace TF.X.π
  have : QuasiSeparatedSpace TF.X.YY := quasiSeparatedSpace_of_quasiSeparated (TF.X.π ≫ TF.Y.s)
  obtain ⟨-, hPj, -⟩ := GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF
  have : IsProper (str₀ TF.X Z) := GlobalTheory.CommonModel.isProper_of_isProjOver hPj
  have : CompactSpace (Y₀ TF.X Z) := QuasiCompact.compactSpace_of_compactSpace (str₀ TF.X Z)
  have hN : (TF.X.F.LL (AllWt.exOf Dw ρ 0)).IsLB := TF.X.F.isLB_LL _
  have hM : (TF.X.F.LL e).IsLB := TF.X.F.isLB_LL _
  have hsum := cls_common_add (commonLL TF.X) e (AllWt.exOf Dw ρ 0)
  have h0 := cls_common_add (commonLL TF.X) (0 : Ix Dw → ℤ) 0
  simp only [add_zero] at h0
  have h3 : e + AllWt.exOf Dw ρ 0 = 0 := by rw [hex]; exact add_neg_cancel e
  rw [h3] at hsum
  have hcls : GlobalTheory.CechPic.cls (TF.X.F.LL e) hM = -GlobalTheory.CechPic.cls (TF.X.F.LL (AllWt.exOf Dw ρ 0)) hN := by
    refine eq_neg_of_add_eq_zero_left ?_
    have h4 : GlobalTheory.CechPic.cls (TF.X.F.LL 0) ((commonLL TF.X).isLB 0) = 0 := by
      have := congrArg (· - GlobalTheory.CechPic.cls (TF.X.F.LL 0) ((commonLL TF.X).isLB 0)) h0
      simpa using this.symm
    exact hsum.symm.trans h4
  obtain ⟨n₀, hn⟩ := GlobalTheory.T.isAmple_pullbackPower_div_of_locally_ample TF.X.π A hAmp (TF.X.F.LL (AllWt.exOf Dw ρ 0)) (TF.X.F.LL e) hN hM hcls
    (fun z => GlobalTheory.T.borelWeil_flagModel_detInverse_isAmple_local TF.flag z)
  have h := (hn n₀ le_rfl).pull_of_isOpenImmersion (inc₀ TF.X Z)
  have hAπ := LB.isLB_pull hA TF.X.π
  have hAg := LB.isLB_pull hA (inc₀ TF.X Z ≫ TF.X.π)
  have hP1 := isLB_lbPow hAπ n₀
  have hP2 := isLB_lbPow hAg n₀
  have hD1 := LB.isLB_div hP1 hN
  have hL0 : (L₀ TF.X Z ρ).IsLB := LB.isLB_pull hN _
  have hD2 := LB.isLB_div hP2 hL0
  refine ⟨n₀, IsAmpleLB.of_lbIso h hD2 ((GlobalTheory.CechPic.cls_eq_iff hD2 (LB.isLB_pull hD1 _)).1 ?_)⟩
  rw [GlobalTheory.CechPic.cls_div hP2 hL0, GlobalTheory.CechPic.cls_lbPow hAg, GlobalTheory.CechPic.cls_pull hA _ hAg,
    GlobalTheory.CechPic.cls_pull hD1 _ _, GlobalTheory.CechPic.cls_div hP1 hN hD1, GlobalTheory.CechPic.cls_lbPow hAπ,
    GlobalTheory.CechPic.cls_pull hA _ hAπ, GlobalTheory.CechPic.pull_comp, map_sub, map_nsmul]
  congr 1
end GlobalTheory.RelAmpleComp
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativelyAmple_comp_of_exists_weight : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∃ ρ : AllWt.Weight Dw, ∀ A : LB TF.Y.X, A.IsLB → IsAmpleLB A → ∃ n : ℕ, IsAmpleLB (LB.div (lbPow (A.pull (inc₀ TF.X Z ≫ TF.X.π)) n) (L₀ TF.X Z ρ)) := by
  first | exact @_root_.GlobalTheory.RelAmpleComp.exists_weight_isAmple_lineBundle_comp | exact _root_.GlobalTheory.RelAmpleComp.exists_weight_isAmple_lineBundle_comp | (intros; apply _root_.GlobalTheory.RelAmpleComp.exists_weight_isAmple_lineBundle_comp <;> assumption)
end
end

section
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
namespace GlobalTheory.HSApp
theorem hodge_bundle_ample_at_regular_point : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ la : AllWt.Weight Dw, GapGe 1 la → ∀ y ∈ U₀ TF.X Z, ∃ mu : AllWt.Weight Dw, GapGe 0 mu ∧ ∃ m : ℕ, 0 < m ∧ AmpleAt (L₀ TF.X Z (m • la - mu)) y := by
  intro hP hN hS hC E _ _ _ H Dw l Xo c TF Z hF la hla y hy
  obtain ⟨A, hA⟩ := GlobalTheory.exists_isAmpleLB_of_isProjOver TF.Y.proj
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.T.relativelyAmple_comp_of_exists_weight hP hN E H Dw l Xo c TF Z hF
  obtain ⟨n, hn⟩ := hρ A hA.isLB hA
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.T.hodgeBundle_dominates_of_large_weight hP hN hS hC E H Dw l Xo c TF Z hF
  obtain ⟨m, s, -, hs⟩ := hχ y hy (lbPow A n) (isLB_lbPow hA.isLB n)
  obtain ⟨mu, hmu, M, hM, e⟩ := exists_dominant_sub la (m • χ - ρ) hla
  exact ⟨mu, hmu, M, hM, e ▸ AmpleTwist.ampleAt_of_sec E H Dw l Xo c TF Z A hA.isLB ρ χ n m hn y s hs⟩
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_bundle_ample_on_regular_locus : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ la : AllWt.Weight Dw, GapGe 1 la → ∀ y ∈ U₀ TF.X Z, ∃ mu : AllWt.Weight Dw, GapGe 0 mu ∧ ∃ m : ℕ, 0 < m ∧ AmpleAt (L₀ TF.X Z (m • la - mu)) y := by
  first | exact @_root_.GlobalTheory.HSApp.hodge_bundle_ample_at_regular_point | exact _root_.GlobalTheory.HSApp.hodge_bundle_ample_at_regular_point | (intros; apply _root_.GlobalTheory.HSApp.hodge_bundle_ample_at_regular_point <;> assumption)
end
