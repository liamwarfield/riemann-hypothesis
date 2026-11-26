module

public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsRoundedDownDivisor
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLogResolution
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.MultiplierVanishingNefTwistAmple

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionLocalVanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionLocalVanishing
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.Discrepancy

theorem exists_logRes_subsingleton_cohOn_one : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Z : Closeds X), η ≠ 0 → 0 < m → Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y) (N : CartierDiv X), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) ∧ (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) := by
  intro hPr X _ _ p n hp hn η m G Z hη hm hZ
  letI := algebraΓOfHom p
  obtain ⟨-, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have hpS : IsProjOver (strHom ℂ (X := X)) := by rwa [strHom_eq (f := p) fun _ => rfl]
  have hbig : IsBig ℂ H := IsAmpleLB.isBig ℂ X hpS H hH
  obtain ⟨Y, _, s, _, K, B, hlog, hZB, a, Fd, A, hA, hFd⟩ :=
    GlobalTheory.T.exists_log_resolution_big_bundle hPr ℂ X p n hp hn η m G hη Z hZ H hH.isLB hbig
  haveI : SmoothOfRelativeDimension n (s ≫ p) := hlog.smooth
  haveI : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hlog.proj
  obtain ⟨F, hF, -⟩ := GlobalTheory.T.exists_rounded_down_divisor ℂ Y (s ≫ p) n hlog.proj (pullCart s G - m • K) m

  obtain ⟨J, hJ⟩ := eventually_atTop.1
    (hH.eventually_isAmpleLB_tens_lbPow_succ (isLB_toLB (-G)))
  have hj : J ≤ m * (J + 1) - 1 := by
    have : J + 1 ≤ m * (J + 1) := Nat.le_mul_of_pos_left _ hm
    omega
  have hTa := hJ _ hj
  have hsucc : m * (J + 1) - 1 + 1 = m * (J + 1) := by
    have : 1 ≤ m * (J + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm.ne' (Nat.succ_ne_zero J))
    omega
  rw [hsucc] at hTa
  obtain ⟨N, hNc⟩ := toPic_surjective ((J + 2) • cls H hH.isLB)
  have hTn : IsNef ℂ (tens (toLB (-G)) (lbPow H (m * (J + 1)))) := hTa.isNef
  have hcls : cls _ hTn.isLB = (m * 1) • cls (toLB N) (isLB_toLB N) - 1 • toPic G - m • cls H hH.isLB := by
    rw [cls_tens (isLB_toLB (-G)) (isLB_lbPow hH.isLB _), cls_lbPow hH.isLB, ← toPic_apply,
      ← toPic_apply, hNc, map_neg]
    simp only [mul_one, one_smul, smul_smul]
    rw [show m * (J + 2) = m * (J + 1) + m by ring, add_smul]
    abel
  obtain ⟨-, hloc⟩ := GlobalTheory.T.multiplier_vanishing_nef_twist_ample ℂ X p n hp η m G Y s K B F hη hm hlog hF (toLB N) H _
    (isLB_toLB N) hH.isLB 1 hTn one_pos hcls hH.isNef a Fd A hA hFd
  refine ⟨Y, inferInstance, inferInstance, s, inferInstance, K, B, F, N, hlog, hZB, hF,
    fun U hU => ?_⟩
  have hP := pull_isLB (isLB_toLB N) s
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq (GlobalTheory.structureModule Y) (isLB_toLB (-F)) hP
    (isLB_toLB (pullCart s N - F)) (by
      rw [← toPic_apply, ← toPic_apply, cls_pull (isLB_toLB N) s hP, ← toPic_apply,
        ← toPic_pullCart, map_sub, map_neg]
      abel)
  exact (cohOn.mapIso Γ(Y, ⊤) (s ⁻¹ᵁ U) 1 e).toEquiv.subsingleton_congr.1 (hloc U hU 1 one_pos)

end GlobalTheory.Discrepancy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionLocalVanishingStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logResolution_localVanishing : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Z : Closeds X), η ≠ 0 → 0 < m → Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y) (N : CartierDiv X), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) ∧ (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) := by
  first | exact @GlobalTheory.Discrepancy.exists_logRes_subsingleton_cohOn_one | exact GlobalTheory.Discrepancy.exists_logRes_subsingleton_cohOn_one | (intros; apply GlobalTheory.Discrepancy.exists_logRes_subsingleton_cohOn_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResolutionMultLtOfConnectedness
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftedFunctionOnLogResolution
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionSplitRegularDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFunctionMapsOfCartierTwistSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFunctionMapsOfCartierTwistSections
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Cartier

variable {Y : Scheme.{0}} [IsIntegral Y]

def chartEqn {D : CartierDiv Y} (i : (toLB D).ι) : Y.functionFieldˣ := (show EqnChart D from i).1.2

theorem gen_mem_chart {D : CartierDiv Y} (i : (toLB D).ι) : genericPoint Y ∈ (toLB D).U i :=
  (show EqnChart D from i).2.1

theorem isEqn_chartEqn {D : CartierDiv Y} (i : (toLB D).ι) {x : Y} (hx : x ∈ (toLB D).U i) :
    D.IsEqn x (chartEqn i) :=
  (show EqnChart D from i).2.2 x hx

theorem fnOf_g_chart {D : CartierDiv Y} (i j : (toLB D).ι) (h) :
    fnOf _ h ((toLB D).g i j).val = (chartEqn i : Y.functionField) / (chartEqn j : Y.functionField) :=
  fnOf_toLB_g i j h

def genChart (D : CartierDiv Y) : (toLB D).ι :=
  (exists_chart (isLB_toLB D) (genericPoint Y)).choose

def coordFn {D : CartierDiv Y} {W : Y.Opens}
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    Γ(Y, W ⊓ (toLB D).U i) :=
  Twist.coord (sectionsOn.toΓ _ _ a) i

theorem coordFn_zero {D : CartierDiv Y} {W : Y.Opens} (i : (toLB D).ι) :
    coordFn (0 : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) i = 0 := rfl

theorem coordFn_add {D : CartierDiv Y} {W : Y.Opens}
    (a b : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    coordFn (a + b) i = coordFn a i + coordFn b i := rfl


open Classical in
def ratOn (D : CartierDiv Y) (W : Y.Opens) :
    sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField where
  toFun a := if h : genericPoint Y ∈ W then
      fnOf _ (memInf h (gen_mem_chart (genChart D))) (coordFn a (genChart D)) /
        (chartEqn (genChart D) : Y.functionField)
    else 0
  map_zero' := by
    split_ifs with h
    · rw [coordFn_zero, map_zero, zero_div]
    · rfl
  map_add' a b := by
    split_ifs with h
    · rw [coordFn_add, map_add (f := _), add_div]
    · rw [add_zero]

theorem ratOn_apply (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) :
    ratOn D W a = fnOf _ (memInf h (gen_mem_chart (genChart D))) (coordFn a (genChart D)) /
      (chartEqn (genChart D) : Y.functionField) :=
  dif_pos h

theorem ratOn_mul (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (i : (toLB D).ι) :
    ratOn D W a * chartEqn i = fnOf _ (memInf h (gen_mem_chart i)) (coordFn a i) := by
  set j := genChart D
  have hij : genericPoint Y ∈ W ⊓ (toLB D).U i ⊓ (toLB D).U j :=
    memInf (memInf h (gen_mem_chart i)) (gen_mem_chart j)
  have e0 : resG Y (inf_le_left : W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U i) (coordFn a i) =
      resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ (toLB D).U i ⊓ (toLB D).U j) ((toLB D).g i j).val *
        resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U j) (coordFn a j) :=
    Twist.coord_rel (sectionsOn.toΓ _ _ a) i j _ _ _
  have e := congrArg (fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij) e0
  rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, fnOf_g_chart] at e
  rw [ratOn_apply D h, e]
  have := (chartEqn j).ne_zero
  field_simp
  exact mul_comm _ _

end GlobalTheory.Cartier

namespace GlobalTheory.Cartier

variable {Y : Scheme.{0}} [IsIntegral Y]

theorem ratOn_regularAt (D : CartierDiv Y) {W : Y.Opens}
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) {y : Y} (hy : y ∈ W) :
    D.RegularAt y (ratOn D W a) := by
  obtain ⟨i, hi⟩ : ∃ i, y ∈ (toLB D).U i := exists_chart (isLB_toLB D) y
  refine ⟨chartEqn i, isEqn_chartEqn i hi, ?_⟩
  rw [ratOn_mul D (gen_mem hy) a i]
  exact regAt_fnOf (memInf hy hi) _ _

theorem exists_ratOn_eq (D : CartierDiv Y) {W : Y.Opens} (h : genericPoint Y ∈ W)
    {f : Y.functionField} (hf : ∀ y ∈ W, D.RegularAt y f) :
    ∃ a, ratOn D W a = f := by
  have key (i : (toLB D).ι) : ∃ b : Γ(Y, W ⊓ (toLB D).U i),
      fnOf _ (memInf h (gen_mem_chart i)) b = f * chartEqn i :=
    exists_fnOf_eq _ fun x hx => (isEqn_chartEqn i hx.2).regularAt_iff.1 (hf x hx.1)
  choose b hb using key
  have hmem : b ∈ Twist.secGroup (GlobalTheory.structureModule Y) (toLB D) W := fun i j =>
    fn_ext (U := W ⊓ (toLB D).U i ⊓ (toLB D).U j) fun hij => by
      show fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij
          (resG Y (inf_le_left : W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U i) (b i)) =
        fnOf (W ⊓ (toLB D).U i ⊓ (toLB D).U j) hij
          (resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
              W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ (toLB D).U i ⊓ (toLB D).U j) ((toLB D).g i j).val *
            resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
              W ⊓ (toLB D).U i ⊓ (toLB D).U j ≤ W ⊓ (toLB D).U j) (b j))
      rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hb, hb, fnOf_g_chart]
      have := (chartEqn j).ne_zero
      field_simp
  refine ⟨(sectionsOn.toΓ _ _).symm (Twist.mkSec b hmem), ?_⟩
  have e := ratOn_mul D h ((sectionsOn.toΓ _ _).symm (Twist.mkSec b hmem)) (genChart D)
  exact mul_right_cancel₀ (chartEqn (genChart D)).ne_zero (e.trans (hb _))

theorem ratOn_res (D : CartierDiv Y) {W W' : Y.Opens} (hle : W' ≤ W)
    (a : sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W) (h : genericPoint Y ∈ W') :
    ratOn D W' (sectionsOn.res Γ(Y, ⊤) _ hle a) = ratOn D W a := by
  rw [ratOn_apply D h, ratOn_apply D (hle h)]
  have e : coordFn (sectionsOn.res Γ(Y, ⊤) _ hle a) (genChart D) =
      resG Y (inf_le_inf_right _ hle) (coordFn a (genChart D)) := rfl
  rw [e, fnOf_resG]

theorem exists_ratOn_twist : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y), ∃ ρ : ∀ W : Y.Opens, sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField, (∀ (W : Y.Opens) (a), ∀ y ∈ W, D.RegularAt y (ρ W a)) ∧ (∀ (W : Y.Opens) (f : Y.functionField), genericPoint Y ∈ W → (∀ y ∈ W, D.RegularAt y f) → ∃ a, ρ W a = f) ∧ ∀ (W W' : Y.Opens) (h : W' ≤ W) (a), genericPoint Y ∈ W' → ρ W' (sectionsOn.res Γ(Y, ⊤) _ h a) = ρ W a :=
  fun Y _ D => ⟨ratOn D, fun _ a _ hy => ratOn_regularAt D a hy,
    fun _ _ h hf => exists_ratOn_eq D h hf, fun _ _ hle a h => ratOn_res D hle a h⟩

end GlobalTheory.Cartier
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFunctionMapsOfCartierTwistSectionsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalFunction_maps_of_cartierTwistSections : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y), ∃ ρ : ∀ W : Y.Opens, sectionsOn (twist (GlobalTheory.structureModule Y) (toLB D)) W →+ Y.functionField, (∀ (W : Y.Opens) (a), ∀ y ∈ W, D.RegularAt y (ρ W a)) ∧ (∀ (W : Y.Opens) (f : Y.functionField), genericPoint Y ∈ W → (∀ y ∈ W, D.RegularAt y f) → ∃ a, ρ W a = f) ∧ ∀ (W W' : Y.Opens) (h : W' ≤ W) (a), genericPoint Y ∈ W' → ρ W' (sectionsOn.res Γ(Y, ⊤) _ h a) = ρ W a := by
  first | exact @GlobalTheory.Cartier.exists_ratOn_twist | exact GlobalTheory.Cartier.exists_ratOn_twist | (intros; apply GlobalTheory.Cartier.exists_ratOn_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisSectionsSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisSectionsSplit
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open Opposite

namespace GlobalTheory.TwoOpens

theorem sections_inter_eq_sub_of_subsingleton_cohOn : ∀ (Y : Scheme.{0}) (F : Y.Modules) (W₁ W₂ : Y.Opens), Subsingleton (cohOn F (W₁ ⊔ W₂) 1) → ∀ t : sectionsOn F (W₁ ⊓ W₂), ∃ (a : sectionsOn F W₁) (b : sectionsOn F W₂), t = sectionsOn.res Γ(Y, ⊤) F inf_le_right b - sectionsOn.res Γ(Y, ⊤) F inf_le_left a := by
  intro Y F W₁ W₂ h t
  let A := (GlobalTheory.toAbSheaf Y).obj F
  let S := Flasque.injectiveShortComplex A
  have hS : S.ShortExact := Flasque.injectiveShortComplex_shortExact A
  have hfl : TopCat.Sheaf.IsFlasque S.X₂ := Flasque.isFlasque_injectiveShortComplex_X₂ A
  have hinj : ∀ W : Y.Opens, Function.Injective (S.f.hom.app (op W)) := by
    intro W x y hxy
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective x
    obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
    rw [← SheafLES.equivZero_map, ← SheafLES.equivZero_map] at hxy
    rw [SheafLES.injective_zero hS W ((SheafLES.equivZero.{0} S.X₂ W).injective hxy)]
  have hex : ∀ W : Y.Opens, Function.Exact (S.f.hom.app (op W)) (S.g.hom.app (op W)) := by
    intro W x
    obtain ⟨x, rfl⟩ := (SheafLES.equivZero.{0} S.X₂ W).surjective x
    rw [← SheafLES.equivZero_map, AddEquiv.map_eq_zero_iff, SheafLES.exact₂ hS 0 W x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, (SheafLES.equivZero_map S.f W y).symm⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (SheafLES.equivZero.{0} S.X₁ W).surjective y
      exact ⟨y, (SheafLES.equivZero.{0} S.X₂ W).injective
        ((SheafLES.equivZero_map S.f W y).trans hy)⟩

  have natf : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.f.hom.app (op V) (S.X₁.obj.map (homOfLE hUV).op x) =
        S.X₂.obj.map (homOfLE hUV).op (S.f.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.f.hom (homOfLE hUV).op x
  have natg : ∀ {U V : Y.Opens} (hUV : V ≤ U) x,
      S.g.hom.app (op V) (S.X₂.obj.map (homOfLE hUV).op x) =
        S.X₃.obj.map (homOfLE hUV).op (S.g.hom.app (op U) x) := fun hUV x =>
    NatTrans.naturality_apply S.g.hom (homOfLE hUV).op x
  have resres : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₂.obj.map (homOfLE h₂).op (S.X₂.obj.map (homOfLE h₁).op x) =
        S.X₂.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  have resres3 : ∀ {U V V' : Y.Opens} (h₁ : V ≤ U) (h₂ : V' ≤ V) x,
      S.X₃.obj.map (homOfLE h₂).op (S.X₃.obj.map (homOfLE h₁).op x) =
        S.X₃.obj.map (homOfLE (h₂.trans h₁)).op x := fun h₁ h₂ x => by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl

  obtain ⟨b', hb'⟩ := (AddCommGrpCat.epi_iff_surjective
    (S.X₂.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op)).1 (hfl.epi _)
    (S.f.hom.app (op (W₁ ⊓ W₂)) (sectionsOn.toΓ F _ t))

  let U : Bool → Y.Opens := fun b => cond b W₂ W₁
  let sf : ∀ b : Bool, ToType (S.X₃.obj.obj (op (U b))) := fun b =>
    match b with
    | true => S.g.hom.app (op W₂) b'
    | false => 0
  have h0 : S.X₃.obj.map (homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    rw [← natg, hb']
    exact (hex _).apply_apply_eq_zero _
  have h0' : S.X₃.obj.map (homOfLE (inf_le_left : W₂ ⊓ W₁ ≤ W₂)).op (S.g.hom.app (op W₂) b') = 0 := by
    have e := resres3 (inf_le_right : W₁ ⊓ W₂ ≤ W₂) (inf_comm W₂ W₁).le (S.g.hom.app (op W₂) b')
    rw [h0, map_zero] at e
    exact e.symm
  have hcomp : TopCat.Presheaf.IsCompatible S.X₃.obj U sf := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact (map_zero _).trans h0.symm
    · exact h0'.trans (map_zero _).symm
    · rfl
  obtain ⟨q, hq, -⟩ := TopCat.Sheaf.existsUnique_gluing' (X := Y.toPresheafedSpace.carrier) S.X₃ U (W₁ ⊔ W₂)
    (fun b => homOfLE (by cases b; exacts [le_sup_left, le_sup_right]))
    (sup_le (le_iSup U false) (le_iSup U true)) sf hcomp

  obtain ⟨i, hi⟩ := SheafLES.sections_surjective_of_subsingleton.{0} hS (W₁ ⊔ W₂) h q
  obtain ⟨bb, hbb⟩ := (hex W₂ (b' - S.X₂.obj.map (homOfLE (le_sup_right : W₂ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_sub, natg, hi]
    exact sub_eq_zero.2 (hq true).symm)
  obtain ⟨aa, haa⟩ := (hex W₁ (- S.X₂.obj.map (homOfLE (le_sup_left : W₁ ≤ W₁ ⊔ W₂)).op i)).1 (by
    rw [map_neg, natg, hi]
    exact neg_eq_zero.2 (hq false))
  refine ⟨(sectionsOn.toΓ F W₁).symm aa, (sectionsOn.toΓ F W₂).symm bb, ?_⟩
  apply (sectionsOn.toΓ F _).injective
  rw [map_sub, sectionsOn.toΓ_res, sectionsOn.toΓ_res]
  simp only [AddEquiv.apply_symm_apply]
  apply hinj
  change _ = S.f.hom.app _ (S.X₁.obj.map _ bb - S.X₁.obj.map _ aa)
  erw [map_sub]
  rw [natf, natf, hbb, haa, map_sub, map_neg, resres, resres, hb']
  abel

end GlobalTheory.TwoOpens
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisSectionsSplitStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mayer_vietoris_sections_split : ∀ (Y : Scheme.{0}) (F : Y.Modules) (W₁ W₂ : Y.Opens), Subsingleton (cohOn F (W₁ ⊔ W₂) 1) → ∀ t : sectionsOn F (W₁ ⊓ W₂), ∃ (a : sectionsOn F W₁) (b : sectionsOn F W₂), t = sectionsOn.res Γ(Y, ⊤) F inf_le_right b - sectionsOn.res Γ(Y, ⊤) F inf_le_left a := by
  first | exact @GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn | exact GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn | (intros; apply GlobalTheory.TwoOpens.sections_inter_eq_sub_of_subsingleton_cohOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionSplitRegularDivisor
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem genericPoint_mem_of_mem_opens (Y : Scheme.{0}) [IsIntegral Y] (W : Y.Opens) {y : Y}
    (hy : y ∈ W) : genericPoint Y ∈ W :=
  ((genericPoint_spec Y).mem_open_set_iff W.isOpen).mpr ⟨y, trivial, hy⟩

theorem ratsec_split_of_H1 : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (W₁ W₂ : Y.Opens),
    Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB D)) (W₁ ⊔ W₂) 1) →
    ∀ f : Y.functionField, (∀ y ∈ W₁ ⊓ W₂, D.RegularAt y f) →
    ∃ h₁ h₂ : Y.functionField, f = h₂ - h₁ ∧ (∀ y ∈ W₁, D.RegularAt y h₁) ∧
      ∀ y ∈ W₂, D.RegularAt y h₂ := by
  intro Y _ D W₁ W₂ hH f hf
  obtain ⟨ρ, hreg, hsurj, hres⟩ := GlobalTheory.T.exists_rationalFunction_maps_of_cartierTwistSections Y D
  by_cases g1 : genericPoint Y ∈ W₁
  · by_cases g2 : genericPoint Y ∈ W₂
    · have g12 : genericPoint Y ∈ W₁ ⊓ W₂ := ⟨g1, g2⟩
      obtain ⟨t, ht⟩ := hsurj (W₁ ⊓ W₂) f g12 hf
      obtain ⟨a, b, hab⟩ := GlobalTheory.T.mayer_vietoris_sections_split Y _ W₁ W₂ hH t
      refine ⟨ρ W₁ a, ρ W₂ b, ?_, fun y hy => hreg W₁ a y hy, fun y hy => hreg W₂ b y hy⟩
      rw [← ht, hab, map_sub, hres W₂ (W₁ ⊓ W₂) inf_le_right b g12,
        hres W₁ (W₁ ⊓ W₂) inf_le_left a g12]
    · refine ⟨ρ W₁ 0, f, by simp, fun y hy => hreg W₁ 0 y hy, fun y hy => ?_⟩
      exact absurd (genericPoint_mem_of_mem_opens Y W₂ hy) g2
  · refine ⟨-f, ρ W₂ 0, by simp, fun y hy => ?_, fun y hy => hreg W₂ 0 y hy⟩
    exact absurd (genericPoint_mem_of_mem_opens Y W₁ hy) g1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFunctionSplitRegularDivisorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_function_split_regular_divisor : ∀ (Y : Scheme.{0}) [IsIntegral Y] (D : CartierDiv Y) (W₁ W₂ : Y.Opens), Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB D)) (W₁ ⊔ W₂) 1) → ∀ f : Y.functionField, (∀ y ∈ W₁ ⊓ W₂, D.RegularAt y f) → ∃ h₁ h₂ : Y.functionField, f = h₂ - h₁ ∧ (∀ y ∈ W₁, D.RegularAt y h₁) ∧ ∀ y ∈ W₂, D.RegularAt y h₂ := by
  first | exact @GlobalTheory.ratsec_split_of_H1 | exact GlobalTheory.ratsec_split_of_H1 | (intros; apply GlobalTheory.ratsec_split_of_H1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNhdsAvoidingImagesOfSpecializations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNhdsAvoidingImagesOfSpecializations
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.BadOpen

theorem exists_affine_nhds_avoid : ∀ (X Y : Scheme.{0}) [IsIntegral X] (s : Y ⟶ X) [IsProper s] (T : Set Y) (σ : Y) (y : X) (N : CartierDiv X), T.Finite → (∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → ¬ s w ⤳ y) → ∃ (U : X.Opens) (e : X.functionFieldˣ), IsAffineOpen U ∧ y ∈ U ∧ (∀ x ∈ U, N.IsEqn x e) ∧ ∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → s w ∉ U := by
  intro X Y _ s _ T σ y N hT hbad
  obtain ⟨g, hg⟩ := N.exists_isEqn y
  obtain ⟨U₁, hyU₁, hU₁⟩ := hg.exists_nhds
  set C : Set X := ⋃ v ∈ T, s.base '' (closure {v} ∩ closure {σ}) with hC
  have hCc : IsClosed C := by
    refine hT.isClosed_biUnion fun v _ => ?_
    exact s.isClosedMap _ (isClosed_closure.inter isClosed_closure)
  have hyC : y ∉ C := by
    simp only [hC, Set.mem_iUnion, Set.mem_image, not_exists, not_and]
    intro v hv w hw hwy
    exact hbad v hv w (specializes_iff_mem_closure.2 hw.1) (specializes_iff_mem_closure.2 hw.2)
      (hwy ▸ specializes_rfl)
  let V : X.Opens := U₁ ⊓ ⟨Cᶜ, hCc.isOpen_compl⟩
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset (U := V) (x := y) ⟨hyU₁, hyC⟩
  refine ⟨W, g, hW, hyW, fun x hx => hU₁ x (hWV hx).1, fun v hv w hvw hσw hw => ?_⟩
  have := (hWV hw).2
  apply this
  simp only [hC, Set.mem_iUnion, Set.mem_image]
  exact ⟨v, hv, w, ⟨specializes_iff_mem_closure.1 hvw, specializes_iff_mem_closure.1 hσw⟩, rfl⟩

end GlobalTheory.BadOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNhdsAvoidingImagesOfSpecializationsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nhds_avoiding_images_of_specializations : ∀ (X Y : Scheme.{0}) [IsIntegral X] (s : Y ⟶ X) [IsProper s] (T : Set Y) (σ : Y) (y : X) (N : CartierDiv X), T.Finite → (∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → ¬ s w ⤳ y) → ∃ (U : X.Opens) (e : X.functionFieldˣ), IsAffineOpen U ∧ y ∈ U ∧ (∀ x ∈ U, N.IsEqn x e) ∧ ∀ v ∈ T, ∀ w : Y, v ⤳ w → σ ⤳ w → s w ∉ U := by
  first | exact @GlobalTheory.BadOpen.exists_affine_nhds_avoid | exact GlobalTheory.BadOpen.exists_affine_nhds_avoid | (intros; apply GlobalTheory.BadOpen.exists_affine_nhds_avoid <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftedFunctionOnLogResolution
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep.LiftFn

variable {Y : Scheme.{0}}

theorem eq_of_specializes_of_coheight {v w : Y} (h : v ⤳ w) (hv : Order.coheight v = 1)
    (hw : Order.coheight w = 1) : v = w := by
  by_contra hne
  have hlt : w < v := lt_of_le_not_ge h fun e => hne (Specializes.antisymm h e).eq
  have h₃ := Order.coheight_add_one_le hlt
  rw [hv, hw] at h₃
  exact absurd h₃ (by decide)

variable [IsIntegral Y] [IsLocallyNoetherian Y]

theorem mult_neg (F : CartierDiv Y) (z : Y) : (-F).mult z = -F.mult z := by
  have e := CartierDiv.mult_add F (-F) z
  rw [add_neg_cancel, (CartierDiv.isEqn_zero (X := Y) z).mult_eq, Units.val_one, (unitAt_one z).ord_eq_zero] at e
  omega

end GlobalTheory.PairStep.LiftFn

namespace GlobalTheory.PairStep


open LiftFn in
theorem exists_lifted_fn : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), IsLogRes p n η m G s K B → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → F.mult v ≤ 0) → s σ ⤳ y → Order.coheight σ = 1 → ∃ h : Y.functionField, (-F).RegularAt σ (h - 1) ∧ ∀ v : Y, v ≠ σ → Order.coheight v = 1 → s v ⤳ y → (-F).RegularAt v h := by
  intro X _ _ p n hp _ η m G N Y _ _ s _ K B F hres hcoh y σ hF hσy hσ
  have hpr : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have hspr : IsProper (s ≫ p) :=
    ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hres.proj).1
  haveI : IsProper s := IsProper.of_comp s p
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (s ≫ p)
  haveI := hres.smooth
  haveI := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth (s ≫ p)

  set T : Set Y := {v | v ≠ σ ∧ 0 < F.mult v} with hTdef
  have hT : T.Finite := F.finite_support_mult.subset fun v hv => hv.2.ne'
  obtain ⟨U, e, hUa, hyU, hNe, hav⟩ := GlobalTheory.T.exists_affine_nhds_avoiding_images_of_specializations X Y s T σ y N hT
    fun v hv w hvw hσw hwy => not_le.2 hv.2 (hF v w hv.1 hvw hσw hwy)
  have hTc : IsClosed (⋃ v ∈ T, closure ({v} : Set Y)) :=
    hT.isClosed_biUnion fun _ _ => isClosed_closure
  set W₁ : Y.Opens := s ⁻¹ᵁ U ⊓ ⟨_, hTc.isOpen_compl⟩ with hW₁
  set W₂ : Y.Opens := s ⁻¹ᵁ U ⊓ ⟨_, (isClosed_closure (s := ({σ} : Set Y))).isOpen_compl⟩ with hW₂
  have hW : W₁ ⊔ W₂ = s ⁻¹ᵁ U := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun w hw => ?_
    by_cases hwσ : w ∈ closure ({σ} : Set Y)
    · refine Or.inl ⟨hw, fun hwT => ?_⟩
      obtain ⟨v, hv, hwv⟩ := Set.mem_iUnion₂.1 hwT
      exact hav v hv w (specializes_iff_mem_closure.2 hwv) (specializes_iff_mem_closure.2 hwσ) hw
    · exact Or.inr ⟨hw, hwσ⟩
  have hc := hcoh U hUa
  rw [← hW] at hc
  set e' : Y.functionFieldˣ := fnPull s e with he'
  have key : ∀ w ∈ s ⁻¹ᵁ U, ∀ f : Y.functionField,
      (pullCart s N - F).RegularAt w f ↔ (-F).RegularAt w (f * e') := by
    intro w hw f
    obtain ⟨g, hg⟩ := F.exists_isEqn w
    rw [((isEqn_pullCart s (hNe _ hw)).sub hg).regularAt_iff, hg.neg.regularAt_iff]
    have : f * ((fnPull s e / g : Y.functionFieldˣ) : Y.functionField) =
        f * (e' : Y.functionField) * ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
      rw [Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, he']
      ring
    rw [this]
  have hinv : ∀ x ∈ W₁ ⊓ W₂, (pullCart s N - F).RegularAt x (e' : Y.functionField)⁻¹ := by
    intro x hx
    rw [key x hx.1.1, inv_mul_cancel₀ e'.ne_zero]
    have h1 := (GlobalTheory.T.regularAt_iff_forall_specializes_ord_add_mult_nonneg Y (-F) x 1).2
    rw [Units.val_one] at h1
    refine h1 fun z hzx => ?_
    rw [(unitAt_one z).ord_eq_zero, zero_add, mult_neg]
    refine neg_nonneg.2 (not_lt.1 fun hz => ?_)
    by_cases hzσ : z = σ
    · subst hzσ
      exact hx.2.2 (specializes_iff_mem_closure.1 hzx)
    · exact hx.1.2 (Set.mem_iUnion₂.2 ⟨z, ⟨hzσ, hz⟩, specializes_iff_mem_closure.1 hzx⟩)
  obtain ⟨h₁, h₂, hsplit, hh₁, hh₂⟩ :=
    GlobalTheory.T.rational_function_split_regular_divisor Y (pullCart s N - F) W₁ W₂ hc (e' : Y.functionField)⁻¹ hinv
  have hσU : σ ∈ s ⁻¹ᵁ U := hσy.mem_open U.isOpen hyU
  refine ⟨h₂ * e', ?_, fun v hvσ hv hvy => ?_⟩
  · have hσW : σ ∈ W₁ := ⟨hσU, fun hσT => by
      obtain ⟨v, hv, hσv⟩ := Set.mem_iUnion₂.1 hσT
      exact hv.1 (eq_of_specializes_of_coheight (specializes_iff_mem_closure.2 hσv)
        (CartierDiv.coheight_eq_one_of_mult_ne_zero hv.2.ne') hσ)⟩
    have e₁ : h₂ * (e' : Y.functionField) - 1 = h₁ * e' := by
      rw [show h₂ = (e' : Y.functionField)⁻¹ + h₁ by rw [hsplit]; ring, add_mul,
        inv_mul_cancel₀ e'.ne_zero]
      ring
    rw [e₁]
    exact (key σ hσU h₁).1 (hh₁ σ hσW)
  · have hvU : v ∈ s ⁻¹ᵁ U := hvy.mem_open U.isOpen hyU
    have hvW : v ∈ W₂ := ⟨hvU, fun hvσ' =>
      hvσ (eq_of_specializes_of_coheight (specializes_iff_mem_closure.2 hvσ') hσ hv).symm⟩
    exact (key v hvU h₂).1 (hh₂ v hvW)

end GlobalTheory.PairStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftedFunctionOnLogResolutionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lifted_function_on_logResolution : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), IsLogRes p n η m G s K B → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → F.mult v ≤ 0) → s σ ⤳ y → Order.coheight σ = 1 → ∃ h : Y.functionField, (-F).RegularAt σ (h - 1) ∧ ∀ v : Y, v ≠ σ → Order.coheight v = 1 → s v ⤳ y → (-F).RegularAt v h := by
  first | exact @GlobalTheory.PairStep.exists_lifted_fn | exact GlobalTheory.PairStep.exists_lifted_fn | (intros; apply GlobalTheory.PairStep.exists_lifted_fn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtNormalPointOfDivisors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtNormalPointOfDivisors
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem regAt_of_isIntegrallyClosed_stalk : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y) → ∀ f : X.functionField, (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → f ∈ E.ring) → RegAt y f := by
  intro X _ _ p hp y hy f hf
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨y, hx⟩⟩
  letI := X.presheaf.algebra_section_stalk (⟨y, hx⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hx⟩
  refine (mem_range_algebraMap_iff_forall_height_eq_one (A := X.presheaf.stalk y) f).2
    fun q hq h1 => ?_
  let P : PrimeSpectrum Γ(X, U) := ⟨q.comap (algebraMap _ (X.presheaf.stalk y)), inferInstance⟩
  have hP1 : P.asIdeal.height = 1 :=
    (IsLocalization.height_under (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl q).trans h1
  have hPQ : P ≤ hU.primeIdealOf ⟨y, hx⟩ := fun s hs => by_contra fun hs' =>
    hq.ne_top (q.eq_top_of_isUnit_mem hs (IsLocalization.map_units (X.presheaf.stalk y)
      (⟨s, hs'⟩ : (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl)))
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  have hzx : (z : X) ⤳ y := by
    have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨y, hx⟩)).mp hPQ).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨y, hx⟩] at h
  clear_value z
  haveI := hU.isLocalization_stalk z
  have hc : Order.coheight (z : X) = 1 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf z).asIdeal
      (X.presheaf.stalk (z : X))
    rw [ringKrullDim_stalk_eq_coheight, hP, hP1] at this
    exact_mod_cast this

  haveI hT : IsLocalization.AtPrime (Localization.AtPrime q) P.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (hU.primeIdealOf ⟨y, hx⟩).asIdeal.primeCompl (Localization.AtPrime q) q
  haveI : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hs : (hU.primeIdealOf z).asIdeal.primeCompl = P.asIdeal.primeCompl := by
    ext s; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hP]
  haveI hZ : IsLocalization P.asIdeal.primeCompl (X.presheaf.stalk (z : X)) := by
    rw [← hs]; exact hU.isLocalization_stalk z
  let e : X.presheaf.stalk (z : X) ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv P.asIdeal.primeCompl (X.presheaf.stalk (z : X))
      (Localization.AtPrime q)).toRingEquiv
  haveI : IsIntegrallyClosed (X.presheaf.stalk (z : X)) :=
    ((IsNormalScheme.isDomain_and_isIntegrallyClosed_iff_of_ringEquiv e).2
      ⟨inferInstance, inferInstance⟩).2
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) := by
    have h1 : Ring.KrullDimLE 1 (X.presheaf.stalk (z : X)) := krullDimLE_of_coheight_le hc.le
    have hf : ¬ IsField (X.presheaf.stalk (z : X)) := fun h => by
      have := ringKrullDim_eq_zero_of_isField h
      rw [ringKrullDim_stalk_eq_coheight, hc] at this
      simp at this
    have hm := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hf
    have h3 : IsIntegrallyClosed (X.presheaf.stalk (z : X)) ∧
        ∃! P : Ideal (X.presheaf.stalk (z : X)), P ≠ ⊥ ∧ P.IsPrime :=
      ⟨inferInstance, _, ⟨hm, inferInstance⟩, fun P hP => IsLocalRing.eq_maximalIdeal
        (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp h1 P hP.1 hP.2)⟩
    exact ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk (z : X)) hf).out 1 4).mpr h3
  obtain ⟨E, hE⟩ := DivOver.exists_isAt (p := p) (z : X)
  obtain ⟨a, rfl⟩ := (hE f).1 (hf z hzx E hE)
  obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf z).asIdeal.primeCompl a
  refine (mem_primeLocalSubalgebra_iff q _).2 ⟨algebraMap _ _ s.1, ?_, algebraMap _ _ c, ?_⟩
  · have := s.2
    rw [Ideal.mem_primeCompl_iff] at this
    have h' : s.1 ∉ P.asIdeal := by simpa only [hP] using this
    exact h'
  · have e' := congrArg (algebraMap _ X.functionField) e
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at e'
    rw [Algebra.smul_def, mul_comm]
    exact ((algebraMap_germ hx c).trans e'.symm).trans (congrArg _ (algebraMap_germ hx s.1).symm)

end GlobalTheory.Discrepancy
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtNormalPointOfDivisorsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_at_normal_point_of_divisors : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y) → ∀ f : X.functionField, (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → f ∈ E.ring) → RegAt y f := by
  first | exact @GlobalTheory.Discrepancy.regAt_of_isIntegrallyClosed_stalk | exact GlobalTheory.Discrepancy.regAt_of_isIntegrallyClosed_stalk | (intros; apply GlobalTheory.Discrepancy.regAt_of_isIntegrallyClosed_stalk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResolutionMultLtOfConnectedness
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.LogResConn

theorem mult_le_ord_of_regularAt {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {F : CartierDiv Y} {v : Y} {f : Y.functionField} (h : (-F).RegularAt v f) (hf : f ≠ 0)
    (hv : Order.coheight v = 1) : F.mult v ≤ Scheme.ord f v := by
  obtain ⟨g, hg⟩ := F.exists_isEqn v
  obtain ⟨a, ha⟩ := hg.neg.regularAt_iff.1 h
  have hg0 : ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) ≠ 0 := Units.ne_zero _
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact mul_ne_zero hf hg0 ha.symm
  have h2 := ord_algebraMap hv ha0
  rw [ha, Scheme.ord_mul hf hg0] at h2
  have h3 := Scheme.ord_mul (x := v) (Units.ne_zero g) hg0
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, (unitAt_one v).ord_eq_zero] at h3
  rw [hg.mult_eq]
  have : (0 : ℤ) ≤ ((Module.length (Y.presheaf.stalk v) (Y.presheaf.stalk v ⧸ Ideal.span {a})).toNat : ℤ) :=
    Int.natCast_nonneg _
  omega

theorem mem_ring_of_regularAt {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {E : DivOver q} {F : CartierDiv Y} {w : Y}
    {f : Y.functionField} (hE : E.IsAt w) (h : (-F).RegularAt w f) (hF : 0 ≤ F.mult w) :
    f ∈ E.ring := by
  by_cases hf : f = 0
  · rw [hf]; exact zero_mem _
  have h1 := mult_le_ord_of_regularAt h hf hE.coheight_eq_one
  have h2 := hE.ord_eq (Units.mk0 f hf)
  have h3 := (E.ord_nonneg_iff (Units.mk0 f hf)).1 (by rw [h2]; simpa using hF.trans h1)
  simpa using h3

variable {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian Y] [GlobalTheory.IsNormalScheme Y]

theorem regAt_pull {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] [LocallyOfFiniteType (s ≫ p)]
    (hbir : Function.Bijective (functionFieldMap s)) {v : Y} {y : X} (hv : Order.coheight v = 1)
    (hsv : s v ⤳ y) {f : X.functionField} (hf : RegAt y f) : RegAt v (functionFieldMap s f) := by
  obtain ⟨E', hE'⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) hv
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_primeDivisor_over_target_birational k X Y p s hbir E'
  have ht := GlobalTheory.T.primeDivisorCentre_through_image k X Y p s E' E hE v (hE'.through specializes_rfl)
  exact (hE' _).1 ((hE f).1 ((ht.of_specializes hsv) f hf))

theorem unitAt_pull {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] [LocallyOfFiniteType (s ≫ p)]
    (hbir : Function.Bijective (functionFieldMap s)) {v : Y} {y : X} (hv : Order.coheight v = 1)
    (hsv : s v ⤳ y) {f : X.functionField} (hf : UnitAt y f) : UnitAt v (functionFieldMap s f) := by
  have hf0 := hf.ne_zero
  obtain ⟨h1, h2⟩ := (unitAt_iff hf0).1 hf
  refine (unitAt_iff ((map_ne_zero _).2 hf0)).2 ⟨regAt_pull (p := p) s hbir hv hsv h1, ?_⟩
  rw [← map_inv₀]
  exact regAt_pull (p := p) s hbir hv hsv h2

end GlobalTheory.LogResConn

namespace GlobalTheory.LogResConn

theorem mult_lt_of_connected : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), IsIntegrallyClosed (X.presheaf.stalk y) → (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → ∀ g, G.IsEqn z g → discrep E η m g ≤ 0) → (pullCart s G - m • K).mult σ = m → s σ ⤳ y → (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s G - m • K).mult v < m) → ∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s G - m • K).mult v < m := by
  intro X _ _ p n hp hn η m G N Y _ _ s _ K B F hη hm hres hF hcoh y σ hyint hdisc hσ hsσ hnear
    v hvσ hsv
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hFσ : F.mult σ = 1 := by rw [hF, hσ]; exact Int.ediv_self hm'.ne'
  have hFle : ∀ z, F.mult z ≤ 0 ↔ (pullCart s G - m • K).mult z < m := fun z => by
    rw [hF, ← Int.lt_add_one_iff, zero_add, Int.ediv_lt_iff_lt_mul hm', one_mul]
  have hFnn : ∀ z, 0 ≤ (pullCart s G - m • K).mult z → 0 ≤ F.mult z := fun z hz => by
    rw [hF]; exact Int.ediv_nonneg hz hm'.le
  by_cases hvc : Order.coheight v ≠ 1
  · have : (pullCart s G - m • K).mult v = 0 := by
      by_contra h0
      exact hvc (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)
    rw [this]; exact hm'
  push_neg at hvc
  haveI := hres.smooth
  haveI : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth n _
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.ModifSections.isNormalScheme_of_smooth (s ≫ p)
  haveI : IsProper (s ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB (s ≫ p)).1 hres.proj).1
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  haveI : IsProper s := IsProper.of_comp s p
  have hbir := hres.bir
  have hσc : Order.coheight σ = 1 :=
    CartierDiv.coheight_eq_one_of_mult_ne_zero (by rw [hσ]; exact_mod_cast hm.ne')
  obtain ⟨h, hσreg, hreg⟩ := GlobalTheory.T.exists_lifted_function_on_logResolution X p n hp hn η m G N Y s K B F hres hcoh y σ
    (fun v w h1 h2 h3 h4 => (hFle v).2 (hnear v w h1 h2 h3 h4)) hsσ hσc
  obtain ⟨h₀, rfl⟩ := hbir.2 h

  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hη ((EtaleKlt.ratPull_bijective_of_birational ℂ X Y p s hbir n).1 (h0.trans (map_zero _).symm))

  have hDnn : ∀ (z : X), z ⤳ y → ∀ (E : DivOver p) (E' : DivOver (s ≫ p)), E.IsAt z →
      DivOver.Over s E' E → ∀ w, s w = z → E'.IsAt w → 0 ≤ F.mult w := by
    intro z hz E E' hE hE'E w hwz hw
    subst hwz
    obtain ⟨g, hg⟩ := G.exists_isEqn (s w)
    have hd := hdisc (s w) hz E hE g hg
    have h1 := GlobalTheory.T.discrepancy_formula_divisor ℂ Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (pullCart s G) m hm
      hres.div E' w (fnPull s g) hw (isEqn_pullCart s hg)
    have h2 : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g) = discrep E η m g := by
      have hform : E'.formOrd (EtaleKlt.ratPull p s n η) = E.formOrd η := by
        simpa only [DivOver.formOrd] using
          (GlobalTheory.T.form_order_birational_pullback ℂ X Y p s hbir E' E hE'E n η hη)
      unfold discrep
      rw [hform, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hbir E' E hE'E g]
    rw [h2] at h1
    rw [h1] at hd
    have hmq : (0 : ℚ) < m := by exact_mod_cast hm
    have : (0 : ℚ) ≤ ((pullCart s G - m • K).mult w : ℚ) := by
      rw [neg_div, neg_nonpos] at hd
      exact (div_nonneg_iff.1 hd).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hmq))
    exact hFnn w (by exact_mod_cast this)

  have hreg0 : RegAt y h₀ := by
    refine GlobalTheory.T.regular_at_normal_point_of_divisors X p hp y hyint h₀ fun z hz E hE => ?_
    obtain ⟨E', hE'E⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p s hbir E
    obtain ⟨w, hwz, hw⟩ := GlobalTheory.T.divisor_point_proper_lift ℂ X Y p s hbir inferInstance E' E hE'E z hE
    have hFw := hDnn z hz E E' hE hE'E w hwz hw
    have hsw : s w ⤳ y := hwz ▸ hz
    rw [hE'E h₀]
    by_cases hwσ : w = σ
    · subst hwσ
      have := mem_ring_of_regularAt hw hσreg hFw
      simpa using add_mem this (one_mem E'.ring)
    · exact mem_ring_of_regularAt hw (hreg w hwσ hw.coheight_eq_one hsw) hFw

  have hunit0 : UnitAt y h₀ := by
    by_cases hh1 : functionFieldMap s h₀ - 1 = 0
    · have : h₀ = 1 := hbir.1 (by rw [map_one]; exact sub_eq_zero.1 hh1)
      rw [this]; exact unitAt_one y
    have hnu : ¬ UnitAt y (h₀ - 1) := fun hu => by
      have hu' := unitAt_pull (p := p) s hbir hσc hsσ hu
      rw [map_sub, map_one] at hu'
      have := mult_le_ord_of_regularAt hσreg hh1 hσc
      rw [hu'.ord_eq_zero, hFσ] at this
      omega
    obtain ⟨a, ha, e⟩ := zeroAt_iff.2 ⟨hreg0.add ⟨-1, by rw [map_neg, map_one]⟩, by
      rwa [sub_eq_add_neg] at hnu⟩
    have h1a : (1 + a) ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := fun h' => by
      have h1 : (1 : X.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
        simpa using sub_mem h' ha
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    exact ⟨1 + a, IsLocalRing.notMem_maximalIdeal.1 h1a, by rw [map_add (f := _), map_one, e]; ring⟩
  have hu := unitAt_pull (p := p) s hbir hvc hsv hunit0
  have := mult_le_ord_of_regularAt (hreg v hvσ hvc hsv) hu.ne_zero hvc
  rw [hu.ord_eq_zero] at this
  exact (hFle v).1 this

end GlobalTheory.LogResConn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResolutionMultLtOfConnectednessStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logResolution_mult_lt_of_connectedness : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), IsIntegrallyClosed (X.presheaf.stalk y) → (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → ∀ g, G.IsEqn z g → discrep E η m g ≤ 0) → (pullCart s G - m • K).mult σ = m → s σ ⤳ y → (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s G - m • K).mult v < m) → ∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s G - m • K).mult v < m := by
  first | exact @GlobalTheory.LogResConn.mult_lt_of_connected | exact GlobalTheory.LogResConn.mult_lt_of_connected | (intros; apply GlobalTheory.LogResConn.mult_lt_of_connected <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectednessLemmaAtNormalPointLogResolution
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem connectedness_at_normal_point :
    GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Z : Closeds X), η ≠ 0 → 0 < m → Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ ∀ (y : X) (σ : Y), IsIntegrallyClosed (X.presheaf.stalk y) → (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → ∀ g, G.IsEqn z g → discrep E η m g ≤ 0) → (pullCart s G - m • K).mult σ = m → s σ ⤳ y → (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s G - m • K).mult v < m) → ∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s G - m • K).mult v < m := by
  intro hP X _ _ p n hp hdim η m G Z hη hm hZ
  obtain ⟨Y, hYi, hYn, s, hs, K, B, F, N, hres, hB, hF, hvan⟩ :=
    GlobalTheory.T.exists_logResolution_localVanishing hP X p n hp hdim η m G Z hη hm hZ
  refine ⟨Y, hYi, hYn, s, hs, K, B, hres, hB, ?_⟩
  intro y σ hy hdisc hσ hσy hloc
  exact GlobalTheory.T.logResolution_mult_lt_of_connectedness X p n hp hdim η m G N Y s K B F hη hm hres hF hvan y σ hy hdisc hσ hσy hloc

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectednessLemmaAtNormalPointLogResolutionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedness_lemma_at_normal_point_logResolution : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Z : Closeds X), η ≠ 0 → 0 < m → Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ ∀ (y : X) (σ : Y), IsIntegrallyClosed (X.presheaf.stalk y) → (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → ∀ g, G.IsEqn z g → discrep E η m g ≤ 0) → (pullCart s G - m • K).mult σ = m → s σ ⤳ y → (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s G - m • K).mult v < m) → ∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s G - m • K).mult v < m := by
  first | exact @GlobalTheory.connectedness_at_normal_point | exact GlobalTheory.connectedness_at_normal_point | (intros; apply GlobalTheory.connectedness_at_normal_point <;> assumption)
end
