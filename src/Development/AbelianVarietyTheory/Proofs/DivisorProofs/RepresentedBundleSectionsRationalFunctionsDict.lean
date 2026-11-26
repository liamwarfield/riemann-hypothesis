module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.VolBr.RepDict

theorem exists_quot {X : Scheme.{0}} [IsIntegral X] {B : LB X} (hB : B.IsLB) {ρ : B.ι → X.functionFieldˣ}
    (hρ : IsRatSec B ρ) : ∃ e : B.Sec → X.functionField,
      ∀ u c (hc : genericPoint X ∈ B.U c), e u * (ρ c : X.functionField) = fnOf _ hc (u.f c) := by
  obtain ⟨c₀, h₀⟩ : ∃ c, genericPoint X ∈ B.U c := Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  refine ⟨fun u => fnOf _ h₀ (u.f c₀) / ρ c₀, fun u c hc => ?_⟩
  have e : fnOf _ hc (u.f c) = fnOf _ (memInf hc h₀) (B.g c c₀ : Γ(X, B.U c ⊓ B.U c₀)) * fnOf _ h₀ (u.f c₀) := by
    rw [← fnOf_resG inf_le_left (memInf hc h₀), ← fnOf_resG inf_le_right (memInf hc h₀), ← map_mul]
    exact congrArg _ (u.compat c c₀)
  rw [e, hρ c c₀ (memInf hc h₀)]
  have := (ρ c₀).ne_zero
  field_simp

theorem exists_sec {X : Scheme.{0}} [IsIntegral X] {B : LB X} {ρ : B.ι → X.functionFieldˣ}
    (hρ : IsRatSec B ρ) {f : X.functionField} (hf : ∀ c, ∀ x ∈ B.U c, RegAt x (f * ρ c)) :
    ∃ u : B.Sec, ∀ c (hc : genericPoint X ∈ B.U c), fnOf _ hc (u.f c) = f * ρ c := by
  have h : ∀ c, ∃ a : Γ(X, B.U c), ∀ hc, fnOf _ hc a = f * ρ c := fun c => by
    by_cases hc : genericPoint X ∈ B.U c
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hc (hf c)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => (hc h).elim⟩
  choose a ha using h
  refine ⟨⟨a, fun i j => Cartier.fn_ext fun h => ?_⟩, ha⟩
  rw [map_mul]
  refine (fnOf_resG _ h _).trans (Eq.trans ?_ (congrArg (_ * ·) (fnOf_resG _ h _).symm))
  rw [ha, ha, hρ i j h]
  ring

theorem rep_dict : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → ∃ e : M.B.Sec → X.functionField, Function.Injective e ∧ Set.range e = (P.H a b : Set X.functionField) ∧ (∀ u (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y (e u) ^ 2 = (M.φ σ).nsq (secVal p σ u) y) ∧ ∀ u (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → (x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u ↔ UnitAt x (P.loc a b (e u) i j)) := by
  intro k _ X _ p P a b M ⟨ρ, hρ, hu, hn⟩
  obtain ⟨e, he⟩ := exists_quot M.isLB hρ
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  have hl (f : X.functionField) c i j :
      P.loc a b f i j * ((ρ c : X.functionField) / P.loc a b 1 i j) = f * ρ c := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    simp only [Pair.loc]
    field_simp
  have hl' (f : X.functionField) c i j :
      P.loc a b f i j = f * ρ c * ((ρ c : X.functionField) / P.loc a b 1 i j)⁻¹ := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    have := (ρ c).ne_zero
    simp only [Pair.loc]
    field_simp
  have hmem u : e u ∈ P.H a b := fun x i j hi hj => by
    obtain ⟨c, hc⟩ := hcov M.isLB x
    rw [hl' _ c, he u c (gen_mem hc)]
    exact (regAt_fnOf hc _ _).mul (hu x c i j hc hi hj).inv.regAt
  refine ⟨e, fun u v huv => ?_, ?_, fun u σ y => ?_, fun u x i j hi hj => ?_⟩
  · refine ReciprocityTheory.ChartRestriction.G.DVR.SecOps.sec_ext fun c => Cartier.fn_ext fun hc => ?_
    rw [← he, ← he, huv]
  · refine Set.Subset.antisymm (Set.range_subset_iff.2 hmem) fun f hf => ?_
    obtain ⟨u, hu'⟩ := exists_sec hρ (f := f) fun c x hc => by
      obtain ⟨i, hi⟩ := hcov P.L.isLB x
      obtain ⟨j, hj⟩ := hcov P.A.isLB x
      rw [← hl f c i j]
      exact (hf x i j hi hj).mul (hu x c i j hc hi hj).regAt
    obtain ⟨c, hc⟩ := hcov M.isLB (genericPoint X)
    exact ⟨u, mul_right_cancel₀ (ρ c).ne_zero ((he u c hc).trans (hu' c hc))⟩
  · have hi := mem_pick (P.L.φ σ).isLB y
    have hj := mem_pick (P.A.φ σ).isLB y
    have hc := mem_pick (M.φ σ).isLB y
    have hU := hu _ _ _ _ (mem_ptsIn.1 hc) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have h1 := hn σ y _ _ _ hc hi hj
    have h2 := ratVal_mul (y := y) (hmem u _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)) hU.regAt
    rw [hl, he u _ (gen_mem (mem_ptsIn.1 hc)), ratVal_fnOf hc] at h2
    have h3 := norm_pos_iff.2 (ratVal_ne_zero hU)
    rw [Pair.nu, Weight.nsq, secVal_apply, h2, ← h1, Real.exp_sub, Real.exp_log h3, norm_mul, Real.exp_neg]
    have h4 : Real.exp ((M.φ σ).φ (pick (M.φ σ).isLB y) y) =
        Real.exp ((M.φ σ).φ (pick (M.φ σ).isLB y) y / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h4]
    field_simp
  · obtain ⟨c, hc⟩ := hcov M.isLB x
    have hU := hu x c i j hc hi hj
    rw [mem_nonzeroLocus_iff u c hc, ← unitAt_fnOf_iff hc (gen_mem hc), ← he]
    exact ⟨fun h => hl' (e u) c i j ▸ h.mul hU.inv, fun h => hl (e u) c i j ▸ h.mul hU⟩

end GlobalTheory.VolBr.RepDict
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDictStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representedBundle_sections_rationalFunctions_dict : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → ∃ e : M.B.Sec → X.functionField, Function.Injective e ∧ Set.range e = (P.H a b : Set X.functionField) ∧ (∀ u (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y (e u) ^ 2 = (M.φ σ).nsq (secVal p σ u) y) ∧ ∀ u (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → (x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u ↔ UnitAt x (P.loc a b (e u) i j)) := by
  first | exact @GlobalTheory.VolBr.RepDict.rep_dict | exact GlobalTheory.VolBr.RepDict.rep_dict | (intros; apply GlobalTheory.VolBr.RepDict.rep_dict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
noncomputable section

namespace GlobalTheory.FlagMod

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem eq_of_field_maps {S : Type} [CommRing S] [_root_.IsReduced S] {a b : S}
    (h : ∀ (L : Type) [Field L] (ψ : S →+* L), ψ a = ψ b) : a = b := by
  rw [← sub_eq_zero]
  refine IsNilpotent.eq_zero (mem_nilradical.1 ?_)
  rw [nilradical_eq_sInf, Ideal.mem_sInf]
  intro p hp
  haveI : p.IsPrime := hp
  rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, h _ (algebraMap S p.ResidueField), sub_self]

theorem eq_of_field_algHoms {K S : Type} [CommRing K] [CommRing S] [Algebra K S] [_root_.IsReduced S] {a b : S}
    (h : ∀ (L : Type) [Field L] [Algebra K L] (ψ : S →ₐ[K] L), ψ a = ψ b) : a = b :=
  eq_of_field_maps fun L _ ψ =>
    letI : Algebra K L := (ψ.comp (algebraMap K S)).toAlgebra
    h L { ψ with commutes' := fun _ => rfl }

theorem ext_ev_field {Z : Scheme.{0}} [IsReduced Z] {V : Z.Opens} {a b : Γ(Z, V)}
    (h : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), ev z V hz a = ev z V hz b) : a = b := by
  apply TopCat.Presheaf.section_ext Z.sheaf V
  intro p hp
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hp V.isOpen
  have hWV : W ≤ V := hWV
  have e0 : ev (tau hW) V (tau_le hW hWV) a = ev (tau hW) V (tau_le hW hWV) b :=
    eq_of_field_maps fun L _ ψ => by
      have := h L (spMap ψ ≫ tau hW) (le_preimage_comp _ (tau_le hW hWV))
      rwa [ev_spMap ψ _ V (tau_le hW hWV)] at this
  rw [ev_tau hW hWV, ev_tau hW hWV] at e0
  have e1 := Z.presheaf.germ_res_apply (homOfLE hWV) p hpW a
  have e2 := Z.presheaf.germ_res_apply (homOfLE hWV) p hpW b
  exact e1.symm.trans ((congrArg _ e0).trans e2)

theorem glue_field {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (uniq : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ V → ∀ x y, R L z x → R L z y → x = y)
    (loc : ∀ W : Z.Opens, IsAffineOpen W → W ≤ V → ∃ a : Γ(Z, W),
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a)) :
    ∃ a : Γ(Z, V), ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a) := by
  let I := {W : Z.Opens // IsAffineOpen W ∧ W ≤ V}
  choose a ha using fun i : I => loc i.1 i.2.1 i.2.2
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ i.1 := fun p hp => by
    obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hp V.isOpen
    exact ⟨⟨W, hW, hWV⟩, hpW⟩
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2)
    (fun p hp => TopologicalSpace.Opens.mem_iSup.2 (hc p hp)) a (fun i j => by
      refine ext_ev_field (a := resG Z inf_le_left (a i)) (b := resG Z inf_le_right (a j)) fun L _ z hz => ?_
      have hi := le_preimage_mono inf_le_left hz
      have hj := le_preimage_mono inf_le_right hz
      rw [ev_res z _ hz hi, ev_res z _ hz hj]
      exact uniq L z (le_preimage_mono i.2.2 hi) _ _ (ha i L z hi) (ha j L z hj))
  refine ⟨s, fun L _ z hz => ?_⟩
  obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
  have hi' : ⊤ ≤ z ⁻¹ᵁ i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ i.1)).1 hi).ge
  have e : ev z V hz s = ev z i.1 hi' (a i) := (ev_res z i.2.2 hi' hz s).symm.trans (congrArg _ (hs i))
  exact e ▸ ha i L z hi'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

namespace FlagCover

theorem isReduced_Yo (hi : Function.Injective β) (hs : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (X : FlagCover Y) : IsReduced X.Yo := by
  letI := β.toAlgebra
  haveI : IsDomain O := hi.isDomain β
  haveI : FaithfulSMul O c.F := (faithfulSMul_iff_algebraMap_injective O c.F).2 hi
  haveI : IsFractionRing O c.F := IsFractionRing.of_field O c.F fun x => by
    obtain ⟨a, b, hb, h⟩ := hs x
    exact ⟨a, b, (eq_div_iff hb).2 h⟩
  have h1 : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (R := O) (S := c.F) (nonZeroDivisors O)
  have h2 : Flat (spMap β) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact IsLocalization.flat c.F (nonZeroDivisors O)
  have := Y.jQ_open
  have h3 : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have h4 : Flat Y.j := by unfold Model.j; infer_instance
  have h5 : IsPreimmersion X.inc :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip h3
  have : ∀ x : X.Yo, _root_.IsReduced (X.Yo.presheaf.stalk x) := fun x => by
    have := (X.normal (X.inc x)).1
    let _ := (X.inc.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x) := Flat.stalkMap X.inc x
    have : IsLocalHom (algebraMap (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (X.inc.stalkMap x).hom)
    have : Module.FaithfullyFlat (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    let e := RingEquiv.ofBijective (X.inc.stalkMap x).hom
      ⟨FaithfulSMul.algebraMap_injective (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x),
        X.inc.stalkMap_surjective x⟩
    exact isReduced_of_injective e.symm e.symm.injective
  exact isReduced_of_isReduced_stalk _

theorem evR_frMap_of_isReduced {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    [_root_.IsReduced S] {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  obtain ⟨p, a, u, hu⟩ := (evLaws_genFr_atlas E H Dw l Xo c).1.test S y
  rw [FlagTan.evR_eq hf hu, FlagTan.evR_eq hf (PullbackSections.frMap_trans a φ hu h)]
  rfl

variable {X : FlagCover Y} {e : Ix Dw → ℤ}

theorem exists_alg_chartFr {S : Type} [CommRing S] (w : Sp S ⟶ X.Yo) :
    ∃ _ : Algebra c.F S, ∀ (k : X.F.J) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k),
      ∃ Q : FrPt Xo c S, X.F.ChartFr k (w ≫ X.inc) hz Q ∧ X.pt Q = w :=
  letI : Algebra c.F S :=
    ((ev (w ≫ pullback.snd X.π Y.j ≫ pullback.snd _ _) ⊤ le_top).comp (toΓ c.F)).toAlgebra
  ⟨this, fun k hz => X.exists_chartFr w (spMap_ev_top _).symm k hz⟩

theorem exists_coef [IsReduced X.Yo] {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) (k : X.F.J) :
    ∃ a : Γ(X.Yo, ((X.F.LL e).pull X.inc).U (fun _ => k)), ∀ (L : Type) [Field L] (z : Sp L ⟶ X.Yo)
      (hz' : ⊤ ≤ z ⁻¹ᵁ ((X.F.LL e).pull X.inc).U (fun _ => k)) [Algebra c.F L]
      (hz : ⊤ ≤ (z ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c L), X.F.ChartFr k (z ≫ X.inc) hz Q → X.pt Q = z →
      ev z _ hz' a = evR Xo c f Q := by
  refine glue_field _ (fun L _ z x => ∀ [Algebra c.F L] (hz : ⊤ ≤ (z ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c L),
    X.F.ChartFr k (z ≫ X.inc) hz Q → X.pt Q = z → x = evR Xo c f Q) (fun L _ z hz' x y hx hy => ?_)
    fun W hW hle => ?_
  · obtain ⟨_, h⟩ := exists_alg_chartFr z
    obtain ⟨Q, hQ, ez⟩ := h k fun p hp => mem_pull.1 (hz' hp)
    exact (hx _ Q hQ ez).trans (hy _ Q hQ ez).symm
  · obtain ⟨_, h⟩ := exists_alg_chartFr (tau hW)
    obtain ⟨Q₀, hQ₀, e₀⟩ := h k fun p hp => mem_pull.1 (tau_le hW hle hp)
    refine ⟨evR Xo c f Q₀, fun L _ z hzW _ hz Q hQ ez => ?_⟩
    have e1 : spMap (ev z W hzW) ≫ tau hW = z := spMap_ev z hW hzW
    have e2 : spMap ((ev z W hzW).comp (algebraMap c.F Γ(X.Yo, W))) = spMap (algebraMap c.F L) := by
      rw [← spMap_comp', ← frX_snd Q₀, ← frX_snd Q, ← X.pt_snd Q₀, ← X.pt_snd Q, e₀, ez]
      simp only [← Category.assoc, e1]
    have e3 : (ev z W hzW).comp (algebraMap c.F Γ(X.Yo, W)) = algebraMap c.F L :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
    let φ : Γ(X.Yo, W) →ₐ[c.F] L := { ev z W hzW with commutes' := fun r => DFunLike.congr_fun e3 r }
    obtain ⟨Q', hQ'⟩ := exists_frMap φ Q₀
    have e4 : spMap φ.toRingHom ≫ tau hW ≫ X.inc = z ≫ X.inc := by
      rw [← Category.assoc]; exact congrArg (· ≫ X.inc) e1
    rw [hQ.unique (hQ₀.frMap hQ' e4 hz)]
    exact (evR_frMap_of_isReduced hf hQ').symm

theorem exists_toRule_eq [IsReduced X.Yo] {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c e) :
    ∃ s : X.SecO e, toRule s = f := by
  classical
  choose a ha using exists_coef (X := X) (e := e) hf.1
  let s : X.SecO e := ⟨fun j => a (j PUnit.unit), fun j j' => ext_ev_field fun L _ z hw => by
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j PUnit.unit, rfl⟩
    obtain ⟨k', rfl⟩ : ∃ k, j' = fun _ => k := ⟨j' PUnit.unit, rfl⟩
    have hh : ⊤ ≤ (z ≫ X.inc) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k') :=
      fun p hp => ⟨(mem_pull (F := X.inc)).1 (hw hp).1, (mem_pull (F := X.inc)).1 (hw hp).2⟩
    have hz := le_preimage_mono inf_le_left hh
    have hz' := le_preimage_mono inf_le_right hh
    obtain ⟨_, h⟩ := exists_alg_chartFr z
    obtain ⟨Q, hQ, ez⟩ := h k hz
    obtain ⟨Q', hQ', ez'⟩ := h k' hz'
    have hwt := FlagTan.evR_frBor hf (hQ.frBor hQ' hh)
    rw [map_mul]
    refine (ev_res z _ hw (le_pull hz) _).trans ((ha k L z _ hz Q hQ ez).trans (Eq.trans ?_
      (congrArg₂ (· * ·) ((ev_pull_g (X.F.LL e) X.inc (fun _ => k) (fun _ => k') z hw hh).trans
        (X.F.ev_LL_g e k k' _ hh)).symm
        ((ev_res z _ hw (le_pull hz') _).trans (ha k' L z _ hz' Q' hQ' ez')).symm)))
    rw [hwt, ← mul_assoc, ← Units.val_mul]
    have : (∏ ix, X.F.TAt k k' (z ≫ X.inc) hh ix ^ (-e ix)) * ∏ ix, X.F.TAt k k' (z ≫ X.inc) hh ix ^ e ix = 1 := by
      rw [← Finset.prod_mul_distrib]; simp
    rw [this, Units.val_one, one_mul]⟩
  refine ⟨s, funext fun p => funext fun P => ?_⟩
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  refine eq_of_field_algHoms (K := c.F) fun L _ _ ψ => ?_
  obtain ⟨P', hP⟩ := exists_frMap ψ P
  obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing X.F.cover (X.pt P' ≫ X.inc)
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor P' k hz
  have hc : coef s k (X.pt P') hz = evR Xo c f Q := ha k L _ _ hz Q hQ (X.pt_frBor ht)
  rw [← FlagTan.evR_eq hf.1 hP, FlagTan.evR_frBor hf ht, ← hc]
  refine (val_frMap s hP).symm.trans ?_
  convert val_eq s hQ ht

theorem toRule_injective [IsReduced X.Yo] {s s' : X.SecO e} (h : toRule s = toRule s') : s = s' := by
  refine TieUniq.sec_ext fun j => ext_ev_field fun S _ w hw => ?_
  obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j PUnit.unit, rfl⟩
  have hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k := fun p hp => mem_pull.1 (hw hp)
  obtain ⟨_, h'⟩ := exists_alg_chartFr w
  obtain ⟨Q, hQ, rfl⟩ := h' k hz
  exact (val_chartFr s hQ).symm.trans (((evR_toRule_of_isReduced s Q).symm.trans
    ((congrArg (evR Xo c · Q) h).trans (evR_toRule_of_isReduced s' Q))).trans (val_chartFr s' hQ))

end FlagCover

end GlobalTheory.FlagMod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.NuEq

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {y : CxPts p σ}

theorem ratVal_one' : ratVal (1 : X.functionField) y = 1 := by
  have h1 := unitAt_one (under y)
  have e := ratVal_mul (y := y) h1.regAt h1.regAt
  rw [mul_one] at e
  exact (mul_eq_left₀ (ratVal_ne_zero h1)).1 e.symm

theorem ratVal_inv' {f : X.functionField} (hf : UnitAt (under y) f) :
    ratVal f⁻¹ y = (ratVal f y)⁻¹ := by
  have e := ratVal_mul hf.regAt hf.inv.regAt
  rw [mul_inv_cancel₀ hf.ne_zero, ratVal_one'] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem unitAt_pow {x : X} {u : X.functionField} (h : UnitAt x u) (m : ℕ) : UnitAt x (u ^ m) := by
  induction m with
  | zero => simpa using unitAt_one x
  | succ m ih => rw [pow_succ]; exact ih.mul h

theorem unitAt_zpow {x : X} {u : X.functionField} (h : UnitAt x u) (n : ℤ) : UnitAt x (u ^ n) := by
  cases n with
  | ofNat m => simpa using unitAt_pow h m
  | negSucc m => rw [zpow_negSucc]; exact (unitAt_pow h _).inv

theorem ratVal_pow' {u : X.functionField} (h : UnitAt (under y) u) (m : ℕ) :
    ratVal (u ^ m) y = ratVal u y ^ m := by
  induction m with
  | zero => simpa using ratVal_one'
  | succ m ih => rw [pow_succ, ratVal_mul (unitAt_pow h m).regAt h.regAt, ih, pow_succ]

theorem ratVal_zpow' {u : X.functionField} (h : UnitAt (under y) u) (n : ℤ) :
    ratVal (u ^ n) y = ratVal u y ^ n := by
  cases n with
  | ofNat m => simpa using ratVal_pow' h m
  | negSucc m => rw [zpow_negSucc, zpow_negSucc, ratVal_inv' (unitAt_pow h _), ratVal_pow' h]

end GlobalTheory.VolBr.NuEq

namespace GlobalTheory.VolBr


open NuEq in
theorem nu_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → P.nu a b σ y f = ‖ratVal (P.loc a b f i j) y‖ * Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) := by
  intro k _ X _ p P a b f hf σ y i j hi hj
  have hi₀ : y ∈ ptsIn p σ (P.L.B.U (pick (P.L.φ σ).isLB y)) := mem_pick _ y
  have hj₀ : y ∈ ptsIn p σ (P.A.B.U (pick (P.A.φ σ).isLB y)) := mem_pick _ y
  have hii := mem_ptsIn_inf.2 ⟨hi, hi₀⟩
  have hjj := mem_ptsIn_inf.2 ⟨hj, hj₀⟩
  have gi := gen_mem (mem_ptsIn.1 hii)
  have gj := gen_mem (mem_ptsIn.1 hjj)
  have uG := unitAt_fnOf (mem_ptsIn.1 hii) gi (P.L.B.g i (pick (P.L.φ σ).isLB y))
  have uG' := unitAt_fnOf (mem_ptsIn.1 hjj) gj (P.A.B.g j (pick (P.A.φ σ).isLB y))
  have uGa := unitAt_zpow uG a
  have uGb := unitAt_zpow uG' b
  have hreg : RegAt (under y) (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) :=
    hf _ _ _ (mem_ptsIn.1 hi₀) (mem_ptsIn.1 hj₀)
  have hloc : P.loc a b f i j =
      ((fnOf _ gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))) ^ a *
        (fnOf _ gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))) ^ b) *
        P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y) := by
    simp only [Pair.loc]
    rw [P.hr i _ gi, P.hr' j _ gj, mul_zpow, mul_zpow]
    ring
  have eG := ratVal_fnOf hii gi (P.L.B.g i (pick (P.L.φ σ).isLB y) : Γ(X, _))
  have eG' := ratVal_fnOf hjj gj (P.A.B.g j (pick (P.A.φ σ).isLB y) : Γ(X, _))
  have c0 : 0 < ‖CxPts.gv p σ P.L.B i (pick (P.L.φ σ).isLB y) y‖ :=
    norm_pos_iff.2 (by rw [CxPts.gv, ← eG]; exact ratVal_ne_zero uG)
  have c0' : 0 < ‖CxPts.gv p σ P.A.B j (pick (P.A.φ σ).isLB y) y‖ :=
    norm_pos_iff.2 (by rw [CxPts.gv, ← eG']; exact ratVal_ne_zero uG')
  rw [Pair.nu, hloc, ratVal_mul (uGa.mul uGb).regAt hreg, ratVal_mul uGa.regAt uGb.regAt,
    ratVal_zpow' uG, ratVal_zpow' uG', eG, eG', (P.L.φ σ).trans i _ y hi hi₀,
    (P.A.φ σ).trans j _ y hj hj₀, norm_mul, norm_mul, norm_zpow, norm_zpow]
  change _ = ‖CxPts.gv p σ P.L.B i _ y‖ ^ a * ‖CxPts.gv p σ P.A.B j _ y‖ ^ b * _ * _
  rw [← Real.rpow_intCast, ← Real.rpow_intCast, Real.rpow_def_of_pos c0, Real.rpow_def_of_pos c0',
    Real.log_pow, Real.log_pow]
  have key : ∀ (N u v s t : ℝ), N * Real.exp (-(a * (s - 2 * u) + b * (t - 2 * v)) / 2) =
      Real.exp (u * a) * Real.exp (v * b) * N * Real.exp (-(a * s + b * t) / 2) := by
    intro N u v s t
    rw [mul_comm (Real.exp (u * a) * Real.exp (v * b)) N, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  push_cast
  exact key _ _ _ _ _

end GlobalTheory.VolBr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFramesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLineBundlePairNorm_independent_of_frames : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ (σ : k →+* ℂ) (y : CxPts p σ) i j, y ∈ ptsIn p σ (P.L.B.U i) → y ∈ ptsIn p σ (P.A.B.U j) → P.nu a b σ y f = ‖ratVal (P.loc a b f i j) y‖ * Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) := by
  first | exact @GlobalTheory.VolBr.nu_eq | exact GlobalTheory.VolBr.nu_eq | (intros; apply GlobalTheory.VolBr.nu_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E)

def IsIdTorusElt (l : Fin r → (AF F ⊗[F] E)ˣ) (a : GAd σ J) : Prop :=
  (matHom _ σ J a).1 * adMat F X = adMat F X * diagonal (fun k => ((l k : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) ∧
  (matHom _ σ J a).1 * adMat F Y = adMat F Y * diagonal (fun k => (((conjUnit σ (l k))⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) ∧
  ∀ z ∈ colPerp σ J X Set.univ ⊓ colPerp σ J Y Set.univ, (matHom _ σ J a).1 *ᵥ z = z



end GlobalTheory.IdTorus
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosed
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SepClosedTorsion

def ptOverHomEquiv {K L : Type} [Field K] [Field L] [Algebra K L] (X : Over (Sp K)) :
    (ptOver K L ⟶ X) ≃ {x : Sp L ⟶ X.left // x ≫ X.hom = spMap (algebraMap K L)} where
  toFun y := ⟨y.left, Over.w y⟩
  invFun x := Over.homMk x.1 x.2
  left_inv y := Over.OverMorphism.ext rfl
  right_inv x := rfl

theorem isUnit_natCast_top {K : Type} [Field K] {m : ℕ} (hm : (m : K) ≠ 0) : IsUnit (m : Γ(Sp K, ⊤)) := by
  simpa using (isUnit_iff_ne_zero.2 hm).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem card_torsion_eq {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω']
    [IsSepClosed Ω] [IsSepClosed Ω'] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) {m : ℕ}
    (hm : (m : K) ≠ 0) :
    Nat.card {x : ptOver K Ω ⟶ A // x ^ m = 1} = Nat.card {x : ptOver K Ω' ⟶ A // x ^ m = 1} := by
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion A (hG := hA) (isUnit_natCast_top hm)
  rw [← Nat.card_congr (GlobalTheory.TorsionUnram.torsionEquiv A m _), ← Nat.card_congr (GlobalTheory.TorsionUnram.torsionEquiv A m _),
    Nat.card_congr (ptOverHomEquiv _), Nat.card_congr (ptOverHomEquiv _)]
  obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨z'⟩ : Nonempty (Sp Ω') := inferInstance
  rw [(FinEt.card_points_eq_finrank (torsion A m).hom (spMap (algebraMap K Ω)) z).2,
    (FinEt.card_points_eq_finrank (torsion A m).hom (spMap (algebraMap K Ω')) z').2]
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  rw [Subsingleton.elim (spMap (algebraMap K Ω) z) (spMap (algebraMap K Ω') z')]

theorem card_torsion_algClosed {K L : Type} [Field K] [Field L] [IsAlgClosed L] [Algebra K L]
    (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) {g : ℕ} (hg : SmoothOfRelativeDimension g A.hom)
    {m : ℕ} (hm : (m : K) ≠ 0) :
    Nat.card {x : ptOver K L ⟶ A // x ^ m = 1} = m ^ (2 * g) := by
  let t : Sp L ⟶ Sp K := spMap (algebraMap K L)
  letI : GrpObj ((Over.pullback t).obj A) := Functor.grpObjObj
  have hgp : IsGrpPullback ((Over.pullback t).obj A) A t (pullback.fst A.hom t) := isGrpPullback_pullback A t
  have hab : IsAbelianScheme ((Over.pullback t).obj A) := GlobalTheory.isAbelianScheme_pullback_obj t A hA
  have hdim : SmoothOfRelativeDimension g ((Over.pullback t).obj A).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hgp.1 hg
  obtain ⟨e, -⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hgp (𝟙 (Sp L)) t (Category.id_comp t).symm
  have hmL : (m : L) ≠ 0 := by
    intro h
    apply hm
    apply (algebraMap K L).injective
    simpa using h
  rw [← GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional L _ g m hab hdim hmL]
  exact Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => by
      change x ^ m = 1 ↔ e x ^ m = 1
      rw [← map_pow, map_eq_one_iff e e.injective]).symm

theorem card_torsion_sepClosed : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → ∀ m : ℕ, (m : K) ≠ 0 → Nat.card {x : ptOver K Ω ⟶ A // x ^ m = 1} = m ^ (2 * g) := by
  intro K Ω _ _ _ _ A _ hA g hg m hm
  rw [card_torsion_eq (Ω' := AlgebraicClosure Ω) A hA hm]
  exact card_torsion_algClosed A hA hg hm

end GlobalTheory.SepClosedTorsion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_abelianVariety_torsion_sepClosed : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → ∀ m : ℕ, (m : K) ≠ 0 → Nat.card {x : ptOver K Ω ⟶ A // x ^ m = 1} = m ^ (2 * g) := by
  first | exact @GlobalTheory.SepClosedTorsion.card_torsion_sepClosed | exact GlobalTheory.SepClosedTorsion.card_torsion_sepClosed | (intros; apply GlobalTheory.SepClosedTorsion.card_torsion_sepClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.VacConj
variable {D : D7}
theorem inv_neg' {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem star_char' {R : Type} [CommRing R] (ψ : AddChar R ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : R) :
    star (ψ (-x)) = ψ x := by
  have h1 : ψ (-x) * ψ x = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 : star (ψ (-x)) * ψ (-x) = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  calc star (ψ (-x)) = star (ψ (-x)) * (ψ (-x) * ψ x) := by rw [h1, mul_one]
    _ = ψ x := by rw [← mul_assoc, h2, one_mul]

theorem hO_neg (S T : HSp D) (x y : WO S T) : hO (negSp S) T x y = -hO S T x y := by
  unfold hO
  rw [negSp_gram, inv_neg']
  simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem symplOH_neg (S T : HSp D) (x y : WO S T) : symplOH (negSp S) T x y = -symplOH S T x y := by
  unfold symplOH symplO
  rw [hO_neg, mul_neg, map_neg, mul_neg]

theorem heisO_conj (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (u : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T u (fun w => starRingEnd ℂ (f w)) = fun w => starRingEnd ℂ (heisO ψ (negSp S) T u f w) := by
  funext w
  simp only [heisO, symplOH_neg, map_mul]
  rw [← Complex.star_def, star_char' ψ hψ]

theorem lineAt_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ (-z) t = lineAt θ τ z (-t) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) := Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ z)
  have hL0 : IsLineAt θ τ (-z) (lineAt θ τ (-z)) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ m n τ (-z))
  have hN : IsLineAt θ τ (-z) (-lineAt θ τ z) := by
    refine ⟨continuous_neg.comp hL.1, fun t => ?_, fun t τ' => ?_⟩
    · rw [AddMonoidHom.neg_apply, Matrix.map_neg _ (fun a => RingHom.map_neg (finPart D) a), hL.2.1 t, neg_zero]
    · have := hL.2.2 t τ'
      have e : compAt θ τ' ((-lineAt θ τ z) t) = -compAt θ τ' (lineAt θ τ z t) := by
        unfold compAt
        rw [AddMonoidHom.neg_apply, Matrix.map_neg _ (fun a => by rw [RingHom.map_neg, RingHom.map_neg])]
      rw [e, this]
      split_ifs <;> simp
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ m n τ (-z) _ _ hL0 hN]
  simp

theorem dRho_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) (f : Mx D m n → ℂ) (x : Mx D m n) :
    Formalism.IndefR.Datum.dRho hs θ τ (-z) f x = -Formalism.IndefR.Datum.dRho hs θ τ z f x := by
  unfold Formalism.IndefR.Datum.dRho
  simp_rw [lineAt_neg hθ]
  rw [deriv_comp_neg (f := fun t => hs (lineAt θ τ z t) f x), neg_zero]

theorem dRho_conj (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (x : WO S T) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (fun w => starRingEnd ℂ (f w)) x =
      starRingEnd ℂ (Formalism.IndefR.Datum.dRho (heisO ψ (negSp S) T) θ τ z f x) := by
  unfold Formalism.IndefR.Datum.dRho
  simp_rw [heisO_conj ψ hψ]
  exact deriv.star

theorem cplxO_neg {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    cplxO (-sS) sT z = -cplxO sS sT z := by
  unfold cplxO
  rw [Matrix.mul_neg, smul_neg]

theorem latO_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

end GlobalTheory.VacConj

namespace GlobalTheory.VacConj

theorem isVacO_conj_negSp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO (negSp S) T → ℂ) :
    IsVacO ψ θ (negSp S) T (fun τ => -sS τ) sT LS LT f → IsVacO ψ θ S T sS sT LS LT (fun w => starRingEnd ℂ (f w)) := by
  rintro ⟨hψ, hv⟩
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hθ : IsInfFam θ := hv.inf
  refine ⟨hψ, ⟨hθ, ⟨fun γ w => ?_, ?_, ?_, ?_⟩, ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun τ z => ?_, ?_⟩⟩
  · have h := hv.theta.quasi γ w
    show starRingEnd ℂ (f (ratW T S γ + w)) = _
    rw [show f (ratW T S γ + w) = _ from h, map_mul, symplOH_neg, ← Complex.star_def, star_char' ψ hn]
    rfl
  · obtain ⟨U, hU, hUf⟩ := hv.theta.level
    exact ⟨U, hU, fun u hu hu' => by rw [heisO_conj ψ hn, hUf u hu hu']⟩
  · exact Complex.continuous_conj.comp hv.theta.cont
  · intro k L hL hL' w
    exact (Complex.conjCLE.contDiff.comp (hv.theta.smooth k L hL hL' w) :)
  · rw [heisO_conj ψ hn, hv.lat.1 u (latO_le S T LS LT _ hu)]
  · rw [heisO_conj ψ hn, hv.lat.2 e he u (latO_le S T LS LT _ hu) hh]
  · funext x
    have h := congrFun (hv.fock τ z) x
    simp only [annih, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
    rw [cplxO_neg, dRho_neg hθ] at h
    rw [dRho_conj ψ hn, dRho_conj ψ hn]
    have h' := congrArg (starRingEnd ℂ) h
    simp only [map_add (f := _), map_mul, map_neg, Complex.conj_I, map_zero] at h'
    linear_combination h'
  · obtain ⟨h1, h2⟩ := hv.norm
    refine ⟨h1, fun p hp => ?_⟩
    have := h2 p hp
    unfold nrm2 at this ⊢
    simp only [Complex.norm_conj]
    exact this

end GlobalTheory.VacConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isVacuum_conj_of_negHermitianSpace : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO (negSp S) T → ℂ), IsVacO ψ θ (negSp S) T (fun τ => -sS τ) sT LS LT f → IsVacO ψ θ S T sS sT LS LT (fun w => starRingEnd ℂ (f w)) := by
  first | exact @GlobalTheory.VacConj.isVacO_conj_negSp | exact GlobalTheory.VacConj.isVacO_conj_negSp | (intros; apply GlobalTheory.VacConj.isVacO_conj_negSp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisor
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem divOver_ord_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (f : X.functionFieldˣ) (r : ℤ) : E.ord (f ^ r) = r * E.ord f := by
  rcases Int.eq_nat_or_neg r with ⟨s, rfl | rfl⟩
  · rw [zpow_natCast, E.ord_pow]
  · rw [zpow_neg, zpow_natCast, E.ord_inv, E.ord_pow]
    ring

theorem isLogEqn_add_smul : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Γ D : X → ℚ) (η : RatForms p n) (x : X) (m m' : ℕ) (g f : X.functionFieldˣ) (c : ℚ), 0 < m → 0 < m' → IsLogEqn p Γ η x m g → (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord f : ℚ) / m') → ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧ IsLogEqn p (Γ + c • D) η x m'' g'' ∧ ∀ E : DivOver p, discrep E η m'' g'' = discrep E η m g - c * ((E.ord f : ℚ) / m') := by
  intro X _ _ p n Γ D η x m m' g f c hm hm' hg hD
  have hb : 0 < c.den := c.den_pos
  have hc : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
  have h₁ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have h₂ : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have h₃ : (c.den : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  refine ⟨m * m' * c.den, g ^ (m' * c.den) * f ^ (c.num * m), Nat.mul_pos (Nat.mul_pos hm hm') hb,
    fun z hz E hE => ?_, fun E => ?_⟩
  · have e₁ := hg z hz E hE
    have e₂ := hD z hz E hE
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [E.ord_mul, E.ord_pow, divOver_ord_zpow, e₂]
    push_cast
    rw [← e₁]
    field_simp
    linear_combination (E.ord f : ℚ) * hc
  · simp only [discrep]
    rw [E.ord_mul, E.ord_pow, divOver_ord_zpow]
    push_cast
    field_simp
    linear_combination ((m : ℚ) * (E.ord f : ℚ)) * hc

end GlobalTheory.PairStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Γ D : X → ℚ) (η : RatForms p n) (x : X) (m m' : ℕ) (g f : X.functionFieldˣ) (c : ℚ), 0 < m → 0 < m' → IsLogEqn p Γ η x m g → (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord f : ℚ) / m') → ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧ IsLogEqn p (Γ + c • D) η x m'' g'' ∧ ∀ E : DivOver p, discrep E η m'' g'' = discrep E η m g - c * ((E.ord f : ℚ) / m') := by
  first | exact @GlobalTheory.PairStep.isLogEqn_add_smul | exact GlobalTheory.PairStep.isLogEqn_add_smul | (intros; apply GlobalTheory.PairStep.isLogEqn_add_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BzfinHolds
namespace GlobalTheory.Laid

theorem bzfin_holds : GlobalTheory.Published.BernsteinZelevinskyFiniteness := by
  intro k _ _ _ _

  exact ⟨CompanionTheory.SmGLBridge.irreducibleAdmissible k, CompanionTheory.JacquetBridge.jacquetFiniteLength k,
    CompanionTheory.BZInd.inductionFiniteLength k, SmGL.IndDual.inductionContragredient k⟩

end GlobalTheory.Laid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection
noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SectionLattice

def IntegralAtSection {W K' : Type} [CommRing W] [Field K'] [Algebra W K'] {G : Scheme.{0}}
    (p : G ⟶ Sp W) {P M : LB G} {N : LB (pullback p (spMap (algebraMap W K')))}
    (w : LB.Iso (M.pull (pullback.fst p (spMap (algebraMap W K')))) N)
    (w₁ : LB.Iso (P.pull (pullback.fst p (spMap (algebraMap W K')))) N) : Prop :=
  ∃ (e₀ : Sp W ⟶ G) (_ : e₀ ≫ p = 𝟙 _) (x : Sp K' ⟶ pullback p (spMap (algebraMap W K')))
    (_ : x ≫ pullback.fst p (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀)
    (_ : x ≫ pullback.snd p (spMap (algebraMap W K')) = 𝟙 _)
    (i : P.ι) (m : M.ι) (n : N.ι) (_ : ⊤ ≤ e₀ ⁻¹ᵁ P.U i) (_ : ⊤ ≤ e₀ ⁻¹ᵁ M.U m)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (P.pull (pullback.fst p (spMap (algebraMap W K')))).U (fun _ => i)))
    (h₂ : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst p (spMap (algebraMap W K')))).U (fun _ => m)))
    (a : W),
    (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h₁).hom (w₁.s (n, fun _ => i)).val) =
      algebraMap W K' a * (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
        ((x.appLE _ ⊤ h₂).hom (w.s (n, fun _ => m)).val)

end GlobalTheory.SectionLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

noncomputable section

namespace GlobalTheory.NefShift

theorem isNef_shift_nonneg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (M : HermLB p) (t : ℝ), 0 ≤ t → M.IsNef D →
      (M.shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro k _ X _ p D hX M t ht hM
  refine ⟨hM.semiPos.shift _ _, fun Z i _ _ κ _ _ _ hd => hM.vertical Z i κ hd, ?_⟩
  intro Z i _ _ _ hc hd
  obtain ⟨r, hr, h0⟩ := hM.horizontal Z i hc hd
  refine ⟨r, hr, ?_⟩
  rw [GlobalTheory.HtSelfInter.curveDeg_shift hX M t i hc hd hr]
  have : (0 : ℝ) ≤ t * Nat.card (X.residueField (i (genericPoint Z)) →+* ℂ) := by positivity
  linarith

end GlobalTheory.NefShift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonnegStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLineBundle_isNef_shift_of_nonneg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (t : ℝ), 0 ≤ t → M.IsNef D → (M.shift (fun _ => t) fun _ => rfl).IsNef D := by
  first | exact @GlobalTheory.NefShift.isNef_shift_nonneg | exact GlobalTheory.NefShift.isNef_shift_nonneg | (intros; apply GlobalTheory.NefShift.isNef_shift_nonneg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDual
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.VolBr.Pair

theorem isRatSec_dual_of_inv {X : Scheme.{0}} [IsIntegral X] {L : LB X} {r : L.ι → X.functionFieldˣ}
    (hr : IsRatSec L r) : IsRatSec (CechPic.dual L) fun i => (r i)⁻¹ := fun i j hij => by
  have e : fnOf _ hij ((CechPic.dual L).g i j : Γ(X, L.U i ⊓ L.U j)ˣ).val =
      (fnOf _ hij (L.g i j : Γ(X, L.U i ⊓ L.U j)))⁻¹ := map_units_inv _ _
  rw [e, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hr i j hij, mul_inv]
  rfl

theorem dual_quot_eq {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    (a b : ℤ) (u : X.functionField) (i : P.L.B.ι) (j : P.A.B.ι) :
    u⁻¹ / P.loc (-a) (-b) 1 i j = (u / P.loc a b 1 i j)⁻¹ := by
  simp only [loc, one_mul, zpow_neg, div_eq_mul_inv, mul_inv, inv_inv]

theorem ratVal_inv_unit {k : Type} [CommRing k] {σ : k →+* ℂ} {Z : Scheme.{0}} [IsIntegral Z]
    {q : Z ⟶ Sp k} {y : CxPts q σ} {f : Z.functionField} (hf : UnitAt (under y) f) :
    ratVal f⁻¹ y = (ratVal f y)⁻¹ := by
  have e := ratVal_mul (y := y) hf.regAt hf.inv.regAt
  have e1 := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
  rw [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e1
  rw [mul_inv_cancel₀ hf.ne_zero, e1] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem rep_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p),
    ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → P.Rep (-a) (-b) M.dual := by
  intro k _ X _ p P a b M ⟨ρ, hρ, hu, hn⟩
  refine ⟨fun c => (ρ c)⁻¹, isRatSec_dual_of_inv hρ, ?_, ?_⟩
  · intro x c i j hc hi hj
    rw [Units.val_inv_eq_inv_val, dual_quot_eq]
    exact (hu x c i j hc hi hj).inv
  · intro σ y c i j hc hi hj
    have hU := hu _ c i j (mem_ptsIn.1 hc) (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
    have e := hn σ y c i j hc hi hj
    rw [Units.val_inv_eq_inv_val, dual_quot_eq, ratVal_inv_unit hU, norm_inv, Real.log_inv]
    change _ - (-(M.φ σ).φ c y) / 2 = _
    push_cast
    linarith

end GlobalTheory.VolBr.Pair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundleDualStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.represents_hermitianLineBundle_dual : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → P.Rep (-a) (-b) M.dual := by
  first | exact @GlobalTheory.VolBr.Pair.rep_dual | exact GlobalTheory.VolBr.Pair.rep_dual | (intros; apply GlobalTheory.VolBr.Pair.rep_dual <;> assumption)
end
end
