module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedSectionChartCoords

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSectionsZeroSchemeRegularSequenceLineB
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSectionsZeroSchemeRegularSequenceLineB
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.RegSeqGlue

open GlobalTheory.Twist

variable {Y : Scheme.{0}} {L : LB Y}

def LocSpan (F : Y.Modules) {d : ℕ} (t : Fin d → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (x : Γ(twistZ F L m, O)) : Prop :=
  ∀ y ∈ O, ∃ (V : Y.Opens) (hV : V ≤ O), y ∈ V ∧ ∃ c : Fin d → Γ(twistZ F L l, V),
    (twistZ F L m).presheaf.map (homOfLE hV).op x = ∑ i, (mulSecOfEq F (zofSec (t i)) h).app V (c i)

theorem res_res (G : Y.Modules) {U V W : Y.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (x : Γ(G, U)) :
    G.presheaf.map (homOfLE h₁).op (G.presheaf.map (homOfLE h₂).op x) =
      G.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem eq_zero_of_locSpan (F : Y.Modules) (t : Fin 0 → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (x : Γ(twistZ F L m, O)) (hx : LocSpan F t h x) : x = 0 :=
  section_eq_zero_of_germ x fun y hy => by
    obtain ⟨V, hV, hyV, c, e⟩ := hx y hy
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hV) y hyV, e, Finset.univ_eq_empty, Finset.sum_empty, map_zero]

variable (hL : L.IsLB)

theorem π_mul (F : Y.Modules) (s a : L.Sec) {l m : ℤ} (h : l + 1 = m) (V : Y.Opens) (u : Γ(twistZ F L l, V)) :
    (Twist.map (lbZPow L m) (cutπ F hL s)).app V ((mulSecOfEq F (zofSec a) h).app V u) =
      (mulSecOfEq (cut F hL s) (zofSec a) h).app V ((Twist.map (lbZPow L l) (cutπ F hL s)).app V u) := by
  rw [app_app, app_app, mulSecOfEq_naturality]

theorem map_locSpan (F : Y.Modules) {d : ℕ} (t : Fin (d + 1) → L.Sec) [Mono (cutHom F hL (t 0))] {l m : ℤ}
    (h : l + 1 = m) {O : Y.Opens} {x : Γ(twistZ F L m, O)} (hx : LocSpan F t h x) :
    LocSpan (cut F hL (t 0)) (fun i => t i.succ) h ((Twist.map (lbZPow L m) (cutπ F hL (t 0))).app O x) :=
  fun y hy => by
    obtain ⟨V, hV, hyV, c, e⟩ := hx y hy
    refine ⟨V, hV, hyV, fun i => (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app V (c i.succ), ?_⟩
    have := (RegSeqKer.shortExact_twistComplex hL F (t 0) h).mono_f
    have hex : Function.Exact ((mulSecOfEq F (zofSec (t 0)) h).app V)
        ((Twist.map (lbZPow L m) (cutπ F hL (t 0))).app V) :=
      exact_app_of_exact_of_mono (RegSeqKer.shortExact_twistComplex hL F (t 0) h).exact V
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← app_res, e, Fin.sum_univ_succ, map_add (f := _), hex.apply_apply_eq_zero, zero_add, map_sum]
    exact Finset.sum_congr rfl fun i _ => π_mul hL F _ _ h V _

theorem exists_glue (d : ℕ) : ∀ (t : Fin d → L.Sec) (F : Y.Modules) [F.IsQuasicoherent] (j₀ l m : ℤ)
    (h : l + 1 = m), RegSeq hL F (List.ofFn t) → VanishFrom L F j₀ → j₀ + d ≤ m →
    ∀ (W : Y → Y.Opens) (b : ∀ y, Γ(twistZ F L m, W y)), (∀ y, y ∈ W y) →
    (∀ y z, LocSpan F t h ((twistZ F L m).presheaf.map (homOfLE (inf_le_left : W y ⊓ W z ≤ W y)).op (b y) -
      (twistZ F L m).presheaf.map (homOfLE (inf_le_right : W y ⊓ W z ≤ W z)).op (b z))) →
    ∃ σ : Γ(twistZ F L m, ⊤), ∀ y, LocSpan F t h ((twistZ F L m).presheaf.map (homOfLE le_top).op σ - b y) := by
  induction d with
  | zero =>
    intro t F _ j₀ l m h _ _ _ W b hW hb
    have hc : ∀ y z, (twistZ F L m).presheaf.map (homOfLE (inf_le_left : W y ⊓ W z ≤ W y)).op (b y) =
        (twistZ F L m).presheaf.map (homOfLE (inf_le_right : W y ⊓ W z ≤ W z)).op (b z) := fun y z =>
      sub_eq_zero.1 (eq_zero_of_locSpan F t h _ (hb y z))
    obtain ⟨σ, hσ, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨(twistZ F L m).presheaf, (twistZ F L m).isSheaf⟩ W ⊤
      (fun y => homOfLE le_top) (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) b (fun y z => hc y z)
    refine ⟨σ, fun y z hz => ⟨W y, le_rfl, hz, fun i => i.elim0, ?_⟩⟩
    rw [hσ y, sub_self, map_zero, Finset.univ_eq_empty, Finset.sum_empty]
  | succ d ih =>
    intro t F _ j₀ l m h hr hv hj W b hW hb
    rw [List.ofFn_succ, regSeq_cons] at hr
    obtain ⟨hm0, hr⟩ := hr
    have hS := RegSeqKer.shortExact_twistComplex hL F (t 0) h
    have := hS.mono_f
    have hex : ∀ V : Y.Opens, Function.Exact ((mulSecOfEq F (zofSec (t 0)) h).app V)
        ((Twist.map (lbZPow L m) (cutπ F hL (t 0))).app V) := fun V =>
      exact_app_of_exact_of_mono hS.exact V
    obtain ⟨σ', hσ'⟩ := ih (fun i => t i.succ) (cut F hL (t 0)) (j₀ + 1) l m h hr
      (RegSeqKer.vanishFrom_cut hL F (t 0) hv) (by push_cast at hj; omega) W
      (fun y => (Twist.map (lbZPow L m) (cutπ F hL (t 0))).app (W y) (b y)) hW fun y z => by
        have := map_locSpan hL F t h (hb y z)
        rwa [map_sub, app_res, app_res] at this
    obtain ⟨σ, hσ⟩ := cohOn.app_surjective hS ⊤ (hv l (by push_cast at hj; omega) 1 one_pos) σ'
    change (Twist.map (lbZPow L m) (cutπ F hL (t 0))).app ⊤ σ = σ' at hσ
    have hEpi : Epi (Twist.map (lbZPow L l) (cutπ F hL (t 0))) :=
      (RegSeqKer.shortExact_twistComplex hL F (t 0) (l := l - 1) (m := l) (by omega)).epi_g
    have := isQuasicoherent_twist (F := F) (isLB_lbZPow hL l)
    have := isQuasicoherent_twist (F := cut F hL (t 0)) (isLB_lbZPow hL l)
    refine ⟨σ, fun y z hz => ?_⟩
    obtain ⟨V, hV, hzV, c', e⟩ := hσ' y z hz
    obtain ⟨A, hzA, hAV⟩ := exists_affine hzV
    have hlift : ∀ i, ∃ u : Γ(twistZ F L l, A.1), (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app A.1 u =
        (twistZ (cut F hL (t 0)) L l).presheaf.map (homOfLE hAV).op (c' i) := fun i =>
      surjective_app_of_epi _ A.2 _
    choose u hu using hlift
    obtain ⟨v, hv'⟩ := (hex A.1 ((twistZ F L m).presheaf.map (homOfLE (hAV.trans hV)).op
        ((twistZ F L m).presheaf.map (homOfLE le_top).op σ - b y) -
        ∑ i, (mulSecOfEq F (zofSec (t i.succ)) h).app A.1 (u i))).1 (by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, sub_eq_zero]
      erw [app_res, map_sub, app_res, hσ]
      rw [← res_res _ hAV hV]
      erw [e]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [π_mul, hu]
      exact (app_res _ _ _).symm)
    refine ⟨A.1, hAV.trans hV, hzA, Fin.cons v u, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hv', sub_add_cancel]

end GlobalTheory.HSCore.RegSeqGlue

namespace GlobalTheory.HSCore.RegSeqGlue

open GlobalTheory.Twist GlobalTheory.HSKerRes

variable {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) {M L : LB Y} (hM : M.IsLB) (hL : L.IsLB)


include hM hL in
theorem toH0_res {n : ℤ} {O O' : Y.Opens} (h : O' ≤ O) (s : Γ(twistZ (LB.toMod M) L n, O)) :
    toH0 p ((twistZ (LB.toMod M) L n).presheaf.map (homOfLE h).op s) = H0.restr h (toH0 p s) :=
  tw_ext hM hL fun i j y hy hi hj => by
    rw [H0.germ_restr, germ_of_global_section p _ i j y _ hi hj, germ_of_global_section p _ i j y _ hi hj]
    erw [Twist.zcoord_resM]
    rw [HSKerRes.coord_resM, ger_resG]


include hM in
theorem vanishesTo_mulSec {d : ℕ} (t : Fin d → L.Sec) (a : Fin d) {n l : ℤ} (h : n + 1 = l) {O : Y.Opens}
    (f : Vanishing.H0 p (tw M L n) O) : VanishesTo (cutIdeal hL t) 1 (mulSec hM hL (t a) h f) :=
  vanishesTo_of_exists fun y _ hy => by
    obtain ⟨i, hi⟩ := exists_chart hM y
    obtain ⟨j, hj⟩ := exists_chart hL y
    refine ⟨twIdx l i j, mem_tw_U.2 ⟨hi, hj⟩, ?_⟩
    rw [germ_mulSec _ _ _ _ _ _ _ _ _ hi hj, pow_one, stalkId_cutIdeal hL t j y hj]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, rfl⟩)


include hM in
theorem vanishesTo_of_locSpan {d : ℕ} (t : Fin d → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (x : Γ(twistZ (LB.toMod M) L m, O)) (hx : LocSpan (LB.toMod M) t h x) :
    VanishesTo (cutIdeal hL t) 1 (toH0 p x) := fun y hs hy i hi => by
  obtain ⟨V, hV, hyV, c, e⟩ := hx y hy
  have hv : VanishesTo (cutIdeal hL t) 1 (H0.restr hV (toH0 p x)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← toH0_res p hM hL, e, map_sum]
    show _ ∈ filTop p _ V (cutIdeal hL t) 1
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [mem_filTop, global_section_mul p hM hL (t a) h]
    exact vanishesTo_mulSec p hM hL t a h _
  have := hv y hs hyV i hi
  rwa [H0.germ_restr] at this


include hM in
theorem locSpan_of_vanishesTo {d : ℕ} (t : Fin d → L.Sec) {l m : ℤ} (h : l + 1 = m) {O : Y.Opens}
    (s : Γ(twistZ (LB.toMod M) L m, O)) (hs : VanishesTo (cutIdeal hL t) 1 (toH0 p s)) :
    LocSpan (LB.toMod M) t h s := fun y hy => by
  obtain ⟨i, hi⟩ := exists_chart hM y
  obtain ⟨j, hj⟩ := exists_chart hL y
  obtain ⟨V, hV, e⟩ := exists_affine (memInf (memInf hy hi) hj)
  have hVO : V.1 ≤ O := e.trans (inf_le_left.trans inf_le_left)
  have hVi : V.1 ≤ M.U i := e.trans (inf_le_left.trans inf_le_right)
  have hVj : V.1 ≤ L.U j := e.trans inf_le_right
  have h₁ : V.1 ≤ O ⊓ (tw M L m).U (twIdx m i j) := fun _ hz => ⟨hVO hz, mem_tw_U.2 ⟨hVi hz, hVj hz⟩⟩
  have h₂ := vanishesTo_iff_affine.1 hs V _ h₁
  rw [pow_one, ideal_cutIdeal hL t V j hVj, restricted_section_chart_coords p s i j h₁ (le_inf (le_inf hVO hVj) hVi)] at h₂
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h₂
  refine ⟨V.1, hVO, hV, fun a => (Twist.zchartEquiv hL l j hVj).symm ((LB.chartEquiv hM i hVi).symm (c a)), ?_⟩
  refine (Twist.zchartEquiv hL m j hVj).injective ((LB.chartEquiv hM i hVi).injective ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Twist.zchartEquiv_mulSecOfEq_app, map_smul, LinearEquiv.apply_symm_apply, Twist.zfun_zofSec,
    smul_eq_mul]
  rw [LB.chartEquiv_apply, Twist.zchartEquiv_apply]
  refine Eq.trans ?_ (hc.symm.trans (Finset.sum_congr rfl fun a _ => mul_comm _ _))
  rw [HSKerRes.coord_resM]
  erw [Twist.zcoord_resM]
  rw [HSKerRes.coord_resM, LB.resG_resG, LB.resG_resG]

end GlobalTheory.HSCore.RegSeqGlue

theorem GlobalTheory.HSCore.exists_glue_mod_regSeq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (p : Y ⟶ Sp k) (M L : LB Y), M.IsLB → ∀ (hL : L.IsLB) (d : ℕ) (t : Fin d → L.Sec) (l : ℤ), RegSeq hL (GlobalTheory.LB.toMod M) (List.ofFn t) → VanishFrom L (GlobalTheory.LB.toMod M) 0 → (d : ℤ) ≤ l → ∀ (W : Y → Y.Opens) (b : ∀ y, Vanishing.H0 p (tw M L l) (W y)), (∀ y, y ∈ W y) → (∀ y z, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr inf_le_left (b y) - Vanishing.H0.restr inf_le_right (b z) : Vanishing.H0 p (tw M L l) (W y ⊓ W z))) → ∃ σ : Vanishing.H0 p (tw M L l) ⊤, ∀ y, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr le_top σ - b y) := by
  intro k _ Y _ _ p M L hM hL d t l hreg hvan hd W b hW hb
  have hl : l - 1 + 1 = l := by omega
  have := (VB.isVB_toMod hM).isFiniteQC
  have hs : ∀ y, ∃ β : Γ(twistZ (LB.toMod M) L l, W y), HSKerRes.toH0 p β = b y := fun y =>
    HSKerRes.surjective_ofTwist hM (Twist.isLB_lbZPow hL _) (b y)
  choose β hβ using hs
  obtain ⟨σ, hσ⟩ := RegSeqGlue.exists_glue hL d t (LB.toMod M) 0 (l - 1) l hl hreg hvan (by omega) W β hW
    fun y z => RegSeqGlue.locSpan_of_vanishesTo p hM hL t hl _ (by
      rw [map_sub, RegSeqGlue.toH0_res p hM hL, RegSeqGlue.toH0_res p hM hL, hβ, hβ]
      exact hb y z)
  refine ⟨HSKerRes.toH0 p σ, fun y => ?_⟩
  have := RegSeqGlue.vanishesTo_of_locSpan p hM hL t hl _ (hσ y)
  rwa [map_sub, RegSeqGlue.toH0_res p hM hL, hβ] at this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftSectionsZeroSchemeRegularSequenceLineBStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_sections_zeroScheme_regularSequence_lineBundle : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (p : Y ⟶ Sp k) (M L : LB Y), M.IsLB → ∀ (hL : L.IsLB) (d : ℕ) (t : Fin d → L.Sec) (l : ℤ), RegSeq hL (GlobalTheory.LB.toMod M) (List.ofFn t) → VanishFrom L (GlobalTheory.LB.toMod M) 0 → (d : ℤ) ≤ l → ∀ (W : Y → Y.Opens) (b : ∀ y, Vanishing.H0 p (tw M L l) (W y)), (∀ y, y ∈ W y) → (∀ y z, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr inf_le_left (b y) - Vanishing.H0.restr inf_le_right (b z) : Vanishing.H0 p (tw M L l) (W y ⊓ W z))) → ∃ σ : Vanishing.H0 p (tw M L l) ⊤, ∀ y, VanishesTo (cutIdeal hL t) 1 (Vanishing.H0.restr le_top σ - b y) := by
  first | exact @GlobalTheory.HSCore.exists_glue_mod_regSeq | exact GlobalTheory.HSCore.exists_glue_mod_regSeq | (intros; apply GlobalTheory.HSCore.exists_glue_mod_regSeq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalLiftSectionsOnClosedSubscheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalLiftSectionsOnClosedSubscheme
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open TopologicalSpace Opposite H0

theorem exists_local_lift_H0On : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (B : LB Y), B.IsLB → ∀ (I : Y.IdealSheafData) (g : sectionsOnClosedSubscheme p B I) (y : Y), ∃ (W : Y.Opens) (_ : y ∈ W) (b : Vanishing.H0 p B W), ∀ (z : I.subscheme) (hz : I.subschemeι z ∈ W) (j : (B.pull I.subschemeι).ι) (hj : z ∈ (B.pull I.subschemeι).U j), Vanishing.H0.germ j z (TopologicalSpace.Opens.mem_top z) hj g = (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ (j PUnit.unit) (I.subschemeι z) hz (mem_pull.1 hj) b) := by
  intro k _ Y p B hB I g y
  obtain ⟨i, hi⟩ := exists_chart hB y
  obtain ⟨W, hyW, hWi⟩ := exists_affine hi
  obtain ⟨J, rfl⟩ : ∃ J : (B.pull I.subschemeι).ι, J PUnit.unit = i := ⟨fun _ => i, rfl⟩
  have hJ (z : I.subscheme) (hz : I.subschemeι z ∈ W.1) : z ∈ (B.pull I.subschemeι).U J :=
    mem_pull.2 (hWi hz)
  have hle : I.subschemeι ⁻¹ᵁ W.1 ≤ ⊤ ⊓ (B.pull I.subschemeι).U J :=
    fun z hz => ⟨trivial, hJ z hz⟩
  obtain ⟨a, ha⟩ := I.subschemeι_app_surjective W (resG I.subscheme hle (g.loc J))
  let b : H0 p B W.1 := (LB.chartEquiv hB (J PUnit.unit) hWi).symm a
  have hb (x : Y) (hx : x ∈ W.1) : germ (J PUnit.unit) x hx (hWi hx) b = ger x hx a := by
    conv_rhs =>
      rw [← (LB.chartEquiv hB (J PUnit.unit) hWi).apply_symm_apply a, LB.chartEquiv_apply,
        ger_resG]
    rfl
  refine ⟨W.1, hyW, b, fun z hz j hj => ?_⟩
  have h0 : germ J z (Opens.mem_top z) (hJ z hz) g =
      (I.subschemeι.stalkMap z).hom (germ (J PUnit.unit) (I.subschemeι z) hz (hWi hz) b) := by
    rw [hb, germ_apply, ← ger_resG hle z hz, ← ha]
    exact (Scheme.Hom.germ_stalkMap_apply _ _ z hz a).symm
  rw [germ_change j J z _ hj (hJ z hz), h0,
    germ_change (j PUnit.unit) (J PUnit.unit) _ hz (mem_pull.1 hj) (hWi hz), map_mul,
    tr_pull B I.subschemeι z hj (hJ z hz), Units.coe_map]
  rfl

end GlobalTheory.Vanishing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalLiftSectionsOnClosedSubschemeStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_lift_sectionsOnClosedSubscheme : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (B : LB Y), B.IsLB → ∀ (I : Y.IdealSheafData) (g : sectionsOnClosedSubscheme p B I) (y : Y), ∃ (W : Y.Opens) (_ : y ∈ W) (b : Vanishing.H0 p B W), ∀ (z : I.subscheme) (hz : I.subschemeι z ∈ W) (j : (B.pull I.subschemeι).ι) (hj : z ∈ (B.pull I.subschemeι).U j), Vanishing.H0.germ j z (TopologicalSpace.Opens.mem_top z) hj g = (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ (j PUnit.unit) (I.subschemeι z) hz (mem_pull.1 hj) b) := by
  first | exact @GlobalTheory.Vanishing.exists_local_lift_H0On | exact GlobalTheory.Vanishing.exists_local_lift_H0On | (intros; apply GlobalTheory.Vanishing.exists_local_lift_H0On <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSResOnto

open GlobalTheory.HSCore.VanishNumberField

theorem vanishFrom_adj_of_nef_big : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K) (B₀ : LB G.Y), B₀.IsLB →
    IsNef K B₀ → IsBig K B₀ → VanishFrom G.L (GlobalTheory.LB.toMod (tens G.K.bundle B₀)) 0 := by
  intro Q K _ _ G B₀ hB₀ hnef hbig j hj q hq
  lift j to ℕ using hj
  let Ω := AlgebraicClosure K
  let S := G.toLinSys
  have hV : S.IsVariety := G.geom.alg.variety
  have hV' := hV.baseChange Ω
  have hH := S.isPullback_baseChange Ω
  haveI : IsIntegral (S.baseChange Ω).Y := hV'.isIntegral
  haveI : SmoothOfRelativeDimension G.D (S.baseChange Ω).str := hV'.smooth
  obtain ⟨hprop, A₀, hA₀⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hV.proj
  haveI := hprop
  have hstr : strHom K G.Y = G.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom K (X := G.Y)) := hstr ▸ hV.proj
  haveI : IsProper (strHom K (X := G.Y)) := hstr ▸ hprop

  have hLnef : IsNef K G.L := IsGenerated.isNef_of_isProjOver (L := G.L) ⟨G.N, G.b, G.geom.alg.bpf⟩ hV.proj
  have hLj : IsNef K (lbPow G.L j) := hLnef.pow hA₀ j
  have hNnef : IsNef K (tens B₀ (lbPow G.L j)) := hnef.tens_of_isProjOver hLj hV.proj
  have hNbig : IsBig K (tens B₀ (lbPow G.L j)) := hbig.tens_nef Q.nef hproj hnef hLj

  haveI : IsIntegralHom (spMap (algebraMap K Ω)) :=
    IsIntegralHom.SpecMap_iff.2 fun x => Algebra.IsIntegral.isIntegral x
  haveI : IsIntegralHom (S.bcFst Ω) := MorphismProperty.of_isPullback (P := @IsIntegralHom) hH.flip ‹_›
  let π := S.bcFst Ω

  have hN'nef : IsNef Ω ((tens B₀ (lbPow G.L j)).pull π) :=
    PosBaseChange.isNef_pull hNnef hA₀ (hA₀.pull_of_isAffineHom π) π π.isClosedMap
  have hN'big : IsBig Ω ((tens B₀ (lbPow G.L j)).pull π) := by
    obtain ⟨D₀, hD₀, c, hc, hm⟩ := hNbig.3
    have hD : topologicalKrullDim G.Y = G.D := topologicalKrullDim_eq_of_smooth G.str G.D hV.smooth
    obtain rfl : D₀ = G.D := by exact_mod_cast hD₀.symm.trans hD
    have hL := LB.isLB_pull hNbig.1 π
    refine (isBig_iff (f := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj
      (topologicalKrullDim_eq_of_smooth _ G.D hV'.smooth)).2 ⟨hL, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ ?_)⟩
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL m) (LB.isLB_pull (isLB_lbPow hNbig.1 m) π)
      (by rw [cls_lbPow hL, cls_pull hNbig.1, cls_pull (isLB_lbPow hNbig.1 m), cls_lbPow hNbig.1, map_nsmul])]
    exact (FieldChangeInter.hdim_pull hH (isLB_lbPow hNbig.1 m) 0).symm

  have hM' := LB.isLB_pull (isLB_tw (isLB_tens G.K.isLB hB₀) G.isLB j) π
  have hKV : Subsingleton (coh (twist (structureModule (S.baseChange Ω).Y) ((tw (tens G.K.bundle B₀) G.L j).pull π)) q) :=
    Q.kv.twist (k := Ω) (p := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj (G.K.baseChange hH) hN'nef hN'big hM'
      (by
        rw [cls_pull (isLB_tw (isLB_tens G.K.isLB hB₀) G.isLB j) π]
        erw [cls_pull G.K.isLB π, cls_pull hNnef.isLB π]
        rw [← map_add (f := _)]
        congr 1
        erw [cls_tens (isLB_tens G.K.isLB hB₀) (Twist.isLB_lbZPow G.isLB j), cls_tens G.K.isLB hB₀,
          cls_tens hB₀ (isLB_lbPow G.isLB j)]
        exact add_assoc _ _ _) hq

  have hY : Subsingleton (coh (twist (structureModule G.Y) (tw (tens G.K.bundle B₀) G.L j)) q) :=
    subsingleton_coh_of_pull (f := G.str) (f' := (S.baseChange Ω).str) hH (isLB_tw (isLB_tens G.K.isLB hB₀) G.isLB j) q hKV
  have hB : (tens G.K.bundle B₀).IsLB := isLB_tens G.K.isLB hB₀
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule G.Y) hB (Twist.isLB_lbZPow G.isLB j)
    (isLB_tw (isLB_tens G.K.isLB hB₀) G.isLB j) rfl
  exact (cohOn.mapIso Γ(G.Y, ⊤) ⊤ q
    ((twistFunctor (lbZPow G.L j)).mapIso (Twist.unitTwistIso (tens G.K.bundle B₀)).symm ≪≫ i)).toEquiv.subsingleton_congr.2 hY

section Comb

variable {K : Type} [Field K] [NumberField K] (G : Geo K)

theorem ger_comb_sum {ι : Type} [Fintype ι] (a : ι → K) (u : ι → Fin G.N → K) (j : G.L.ι) (y : G.Y) (hj : y ∈ G.L.U j) :
    ger y hj ((G.comb (∑ i, a i • u i)).f j) = ∑ i, H0.const G.str y (a i) * ger y hj ((G.comb (u i)).f j) := by
  have key (v : Fin G.N → K) : H0.ofSec G.str ⊤ (G.comb v) =
      Fintype.linearCombination K (fun c => H0.ofSec G.str ⊤ (G.b c)) v := G.ofSec_comb ⊤ v
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← H0.germ_ofSec (p := G.str) j y (TopologicalSpace.Opens.mem_top y) hj, key, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, H0.germ_smul, ← key, H0.germ_ofSec]

theorem vanishesTo_of_isUnit (s : Fin G.D → Fin G.N → K) (g : Matrix (Fin G.D) (Fin G.D) K) (hg : IsUnit g.det)
    {B : LB G.Y} {O : G.Y.Opens} {f : Vanishing.H0 G.str B O} (hf : VanishesTo (G.ideal s) 1 f) :
    VanishesTo (G.ideal fun i => ∑ j, g i j • s j) 1 f := fun y _ hy c hc => by
  have h := vanishesTo_iff_forall.1 hf y hy c hc
  obtain ⟨j, hj⟩ := exists_chart G.isLB y
  rw [pow_one, stalkId_cutIdeal G.isLB _ j y hj] at h ⊢
  refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_) h
  have e : s a = ∑ i, g⁻¹ a i • ∑ j, g i j • s j := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul g hg, Matrix.one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change ger y hj ((G.comb (s a)).f j) ∈ Ideal.span _
  rw [e, ger_comb_sum]
  exact sum_mem fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end Comb

section Germs
variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} {I : Y.IdealSheafData}

theorem vanishesTo_one_of_stalkMap {f : Vanishing.H0 p B O}
    (h : ∀ (z : I.subscheme) (hz : I.subschemeι z ∈ O) (j : (B.pull I.subschemeι).ι)
      (hj : z ∈ (B.pull I.subschemeι).U j),
      (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ (j PUnit.unit) (I.subschemeι z) hz (mem_pull.1 hj) f) = 0) :
    VanishesTo I 1 f := by
  intro y hs hy i hi
  obtain ⟨z, rfl⟩ := exists_ι_eq hs
  rw [pow_one, ← ker_stalkMap]
  exact RingHom.mem_ker.2 (h z hy (fun _ => i) (mem_pull.2 hi))

theorem stalkMap_germ_eq_zero {f : Vanishing.H0 p B O} (hf : VanishesTo I 1 f) (z : I.subscheme)
    (hz : I.subschemeι z ∈ O) (i : B.ι) (hi : I.subschemeι z ∈ B.U i) :
    (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ i (I.subschemeι z) hz hi f) = 0 := by
  have := hf _ (ι_mem_support I z) hz i hi
  rw [pow_one, ← ker_stalkMap] at this
  exact RingHom.mem_ker.1 this

end Germs

theorem res_onto : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.L₂ → IsBig K G.L₂ →
    ∀ (s : Fin G.D → Fin G.N → K) (hs : G.IsGood s), Function.Surjective fun f => hs.res 0 (G.mulE 0 f) := by
  intro Q K _ _ G hnef hbig s hs
  have hB : (tens G.K.bundle G.L₂).IsLB := isLB_tens G.K.isLB G.isLB₂
  have hB' : (G.adj₂ 0).IsLB := isLB_tw hB G.isLB _
  obtain ⟨g, hg, hreg⟩ := GlobalTheory.T.exists_basis_regular_sequence_of_common_zeros K G s hs _ hB
  have hproj : IsProjOver (GlobalTheory.strHom K (X := G.Y)) := by
    rw [GlobalTheory.strHom_eq (f := G.str) fun _ => rfl]
    exact G.geom.alg.variety.proj
  have hinv : ∀ {O : G.Y.Opens} {f : Vanishing.H0 G.str (G.adj₂ 0) O},
      VanishesTo (G.ideal fun i => ∑ j, g i j • s j) 1 f → VanishesTo (G.ideal s) 1 f := by
    intro O f hf
    have e : (fun a => ∑ i, g⁻¹ a i • ∑ j, g i j • s j) = s := funext fun a => by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, ← Matrix.mul_apply, Matrix.nonsing_inv_mul g hg, Matrix.one_apply, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have h := vanishesTo_of_isUnit G (fun i => ∑ j, g i j • s j) g⁻¹ (Matrix.isUnit_nonsing_inv_det g hg) hf
    rwa [e] at h
  have key : ∀ y₀ : sectionsOnClosedSubscheme G.str (G.adj₂ 0) (G.ideal s), ∃ f, resTo suppIn_top f = y₀ := by
    intro y₀
    choose W hW b hb using fun y => GlobalTheory.T.exists_local_lift_sectionsOnClosedSubscheme K G.Y G.str (G.adj₂ 0) hB' (G.ideal s) y₀ y
    have hcomp : ∀ y z, VanishesTo (G.ideal s) 1 (Vanishing.H0.restr inf_le_left (b y) -
        Vanishing.H0.restr inf_le_right (b z) : Vanishing.H0 G.str (G.adj₂ 0) (W y ⊓ W z)) := by
      intro y z
      refine vanishesTo_one_of_stalkMap fun z' hz' j hj => ?_
      rw [map_sub, Vanishing.H0.germ_restr, Vanishing.H0.germ_restr, map_sub, ← hb y z' hz'.1 j hj,
        ← hb z z' hz'.2 j hj, sub_self]
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_lift_sections_zeroScheme_regularSequence_lineBundle K G.Y hproj G.str _ G.L hB G.isLB G.D _ _ hreg
      (vanishFrom_adj_of_nef_big Q K G G.L₂ G.isLB₂ hnef hbig) (by simp) W b hW
      fun y z => vanishesTo_of_isUnit G s g hg (hcomp y z)
    refine ⟨σ, Vanishing.H0.ext_germ fun z _ => ?_⟩
    obtain ⟨c, hc⟩ := exists_chart hB' ((G.ideal s).subschemeι z)
    refine ⟨fun _ => c, mem_pull.2 hc, ?_⟩
    have h₁ := stalkMap_germ_eq_zero (hinv (hσ ((G.ideal s).subschemeι z))) z (hW _) c hc
    rw [map_sub, Vanishing.H0.germ_restr, map_sub, sub_eq_zero] at h₁
    refine (germ_resTo suppIn_top (fun _ => c) z (mem_pull.2 hc) σ).trans ?_
    rw [hb _ z (hW _) (fun _ => c) (mem_pull.2 hc)]
    exact h₁
  intro y₀
  obtain ⟨f, hf⟩ := key (Vanishing.mulDs G.K G.isLB G.isLB₂ (G.sec s) hs.etale rfl y₀)
  refine ⟨f, ?_⟩
  change hs.res 0 (G.mulE 0 f) = y₀
  rw [hs.res_mulE]
  exact (Vanishing.resDs_eq_iff G.K G.isLB G.isLB₂ (G.sec s) hs.etale suppIn_top rfl f y₀).2 hf

end GlobalTheory.HSResOnto
