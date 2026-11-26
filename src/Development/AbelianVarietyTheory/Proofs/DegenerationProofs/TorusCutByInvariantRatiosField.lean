module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitChartsTorusExtensionOverField
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KfBijective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCutByInvariantRatiosField
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCutByInvariantRatiosField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ.KerCut

theorem hom_ext_of_appLE {X Y : Scheme.{0}} (V : X.Opens) (hV : IsAffineOpen V) (f g : Y ⟶ X)
    (hf : ⊤ ≤ f ⁻¹ᵁ V) (hg : ⊤ ≤ g ⁻¹ᵁ V) (e : f.appLE V ⊤ hf = g.appLE V ⊤ hg) : f = g := by
  have : IsAffine V.toScheme := hV
  have r : ∀ (f : Y ⟶ X), ⊤ ≤ f ⁻¹ᵁ V → ∃ f' : Y ⟶ V.toScheme, f = f' ≫ V.ι := by
    intro f hf
    refine ⟨IsOpenImmersion.lift V.ι f ?_, (IsOpenImmersion.lift_fac _ _ _).symm⟩
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hf (show y ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨f', ef⟩ := r f hf
  obtain ⟨g', eg⟩ := r g hg
  rw [← GlobalTheory.FunDescent.res_comp_appTop V f' f ef, ← GlobalTheory.FunDescent.res_comp_appTop V g' g eg] at e
  have : f' = g' := by
    apply ext_of_isAffine
    ext x
    obtain ⟨y, rfl⟩ := (GlobalTheory.FunDescent.res_bijective V).2 x
    exact congrArg (fun ψ => ψ.hom y) e
  rw [ef, eg, this]

theorem appLE_appLE_apply {X Y Z : Scheme.{0}} (k : Z ⟶ Y) (q : Y ⟶ X) (V : X.Opens) (W : Y.Opens)
    (h : W ≤ q ⁻¹ᵁ V) (h' : ⊤ ≤ k ⁻¹ᵁ W) (p : Z ⟶ X) (e : k ≫ q = p) (h'' : ⊤ ≤ p ⁻¹ᵁ V) (v : Γ(X, V)) :
    (k.appLE W ⊤ h').hom ((q.appLE V W h).hom v) = (p.appLE V ⊤ h'').hom v := by
  subst e
  rw [← Scheme.Hom.appLE_comp_appLE k q V W ⊤ h h']
  rfl

end GlobalTheory.ZJ.KerCut

namespace GlobalTheory.ZJ

theorem Charts.kerIs_of_torus : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H) (a) (j : Fin d → C.I), GeometricallyConnected H.hom → C.Torus c i → C.Based c a j → C.KerIs a j i := by
  intro K _ H _ _ _ _ _ C d c i a j hc hT hB
  obtain ⟨B, _, q, -, hq, -, -, -, hP, hV⟩ := GlobalTheory.T.splitCharts_torus_extension_over_field K H C d c i hc hT
  obtain ⟨V, hW, hVa, hu⟩ := hV a
  have one_mem : ∀ Y : Over (Sp K), ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a := by
    intro Y y _
    exact hB.1 (show (toUnit Y).left y ∈ (⊤ : (Sp K).Opens) from trivial)
  refine ⟨⟨fun {Y} s t e => hP.hom_ext e (toUnit_unique _ _)⟩, fun Y k => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨h, h₁, hr⟩
    have key : k ≫ q = (1 : Y ⟶ H) ≫ q := by
      apply Over.OverMorphism.ext
      have m : ∀ g : Y ⟶ H, ⊤ ≤ g.left ⁻¹ᵁ C.W a → ⊤ ≤ (g ≫ q).left ⁻¹ᵁ V := by
        intro g hg
        rw [hW] at hg
        exact hg
      refine KerCut.hom_ext_of_appLE V hVa _ _ (m k h) (m 1 h₁) ?_
      ext v
      have hv := hT.gen a _ ((hu _).2 ⟨v, rfl⟩)
      have eq := RingHom.eqOn_set_closure (f := (k.left.appLE _ ⊤ h).hom)
        (g := ((1 : Y ⟶ H).left.appLE _ ⊤ h₁).hom) (by
          rintro u (⟨w, rfl⟩ | ⟨j', hj', rfl⟩)
          · exact (KerCut.appLE_appLE_apply _ _ _ _ _ _ Y.hom (Over.w k) le_rfl w).trans
              (KerCut.appLE_appLE_apply _ _ _ _ _ _ Y.hom (Over.w _) le_rfl w).symm
          · exact hr j' hj') hv
      exact (KerCut.appLE_appLE_apply _ _ _ _ _ _ _ rfl (m k h) v).symm.trans
        (eq.trans (KerCut.appLE_appLE_apply _ _ _ _ _ _ _ rfl (m 1 h₁) v))
    have w : k ≫ q = toUnit Y ≫ η[B] := by
      rw [key, MonObj.one_comp]
      rfl
    exact ⟨hP.lift _ _ w, (hP.lift_fst _ _ w).symm⟩
  · rintro ⟨t, rfl⟩
    have h' := hT.stable a Y t 1 (one_mem Y)
    have hr := fun j' hj' => hT.inv a j' hj' Y t 1 (one_mem Y) h'
    revert h' hr
    rw [_root_.mul_one]
    intro h' hr
    refine ⟨h', one_mem Y, fun j' hj' => ?_⟩
    rw [hr j' hj', charUnit_zero_val, map_one, _root_.one_mul]
  · intro Y t n h h₁
    have := hT.wt a (j n) n (hB.2 n).1 Y t 1 h₁
    rw [_root_.mul_one] at this
    exact this h

end GlobalTheory.ZJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCutByInvariantRatiosFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_cut_by_invariantRatios_field : ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H) (a) (j : Fin d → C.I), GeometricallyConnected H.hom → C.Torus c i → C.Based c a j → C.KerIs a j i := by
  first | exact @GlobalTheory.ZJ.Charts.kerIs_of_torus | exact GlobalTheory.ZJ.Charts.kerIs_of_torus | (intros; apply GlobalTheory.ZJ.Charts.kerIs_of_torus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionOfCoordinateDivisibility
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionOfCoordinateDivisibility
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {H : LB M.Z} {d : H.ι → Ω}
  {J : Type} {σ : J → H.Sec} {t : J → Ω}

theorem mem_nonzeroLocus_iff_div (hH : H.IsLB) (hd : M.GenTriv H d) (hv : ∀ j, M.HasVal d (σ j) (t j))
    (hg : ∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) (i : J) (z : M.Z) :
    z ∈ Out.nonzeroLocus (σ i) ↔ M.Div t i z := by
  constructor
  · intro hz
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    have hzl : z ∈ H.U l := M.Z.basicOpen_le _ hl
    obtain ⟨h0, h1⟩ := (isUnit_O_iff _).1 ((isUnit_valF_iff hzl _).2 hl)
    have e := hv i l ⟨z, hzl⟩
    dsimp only at h0 h1
    rw [e] at h0 h1
    have hi : t i ≠ 0 := fun h => h0 (by rw [h, zero_div])
    refine ⟨hi, fun j => ?_⟩
    have h2 := valF_mem_O hzl ((σ j).f l)
    rw [hv j l ⟨z, hzl⟩] at h2
    have h3 := mul_mem h2 h1
    have hdl := hd.ne l
    have e' : t j / d l * (t i / d l)⁻¹ = t j / t i := by field_simp
    rwa [e'] at h3
  · intro hz
    have hc : z ∈ ⨆ l, H.U l := by rw [hH.cover]; trivial
    obtain ⟨l, hzl⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    obtain ⟨i', hi', h1⟩ := hg l z hzl
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨l, (isUnit_valF_iff hzl _).1 ((isUnit_O_iff _).2 ?_)⟩
    dsimp only
    rw [hv i l ⟨z, hzl⟩]
    refine ⟨div_ne_zero hz.1 (hd.ne l), ?_⟩
    have h3 := mul_mem h1 (hz.2 i')
    have hi := hz.1
    have e' : d l / t i' * (t i' / t i) = (t i / d l)⁻¹ := by field_simp
    rwa [e'] at h3

theorem immBy_of_div : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω) (J : Type) (σ : J → H.Sec) (t : J → Ω) (k : Type) [CommRing k] (p : M.Z ⟶ Sp k) (ψ : k →+* Ω), H.IsLB → M.GenTriv H d → (∀ j, M.HasVal d (σ j) (t j)) → (∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) → M.pt ≫ p = spMap ψ → (∀ i, t i ≠ 0 → ∃ U : M.Z.Opens, IsAffineOpen U ∧ (U : Set M.Z) = {z | M.Div t i z} ∧ ∀ x ∈ M.ringOn U, x ∈ Subring.closure (Set.range ψ ∪ Set.range fun j => t j / t i)) → ImmBy p H σ Set.univ := by
  intro o Ω _ _ _ M H d J σ t k _ p ψ hH hd hv hg hp hU
  have key := mem_nonzeroLocus_iff_div hH hd hv hg
  refine ⟨top_unique fun z _ => ?_, fun i _ => ?_⟩
  · have hc : z ∈ ⨆ l, H.U l := by rw [hH.cover]; trivial
    obtain ⟨l, hzl⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    obtain ⟨i, hi, h1⟩ := hg l z hzl
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨trivial, (key i z).2 ⟨hi, fun j => ?_⟩⟩⟩
    have h2 := valF_mem_O hzl ((σ j).f l)
    rw [hv j l ⟨z, hzl⟩] at h2
    have h3 := mul_mem h2 h1
    have hdl := hd.ne l
    have e' : t j / d l * (d l / t i) = t j / t i := by field_simp
    rwa [e'] at h3
  · have hempty : ∀ V : M.Z.Opens, ¬ (V : Set M.Z).Nonempty → Subsingleton Γ(M.Z, V) := fun V hV => by
      have : V = ⊥ := SetLike.coe_injective (Set.not_nonempty_iff_eq_empty.1 hV)
      subst this
      infer_instance
    have key' := key i
    generalize Out.nonzeroLocus (σ i) = W at key' ⊢
    by_cases hi : t i = 0
    · have hW : W = ⊥ := eq_bot_iff.2 fun z hz => (((key' z).1 hz).1 hi).elim
      subst hW
      refine ⟨isAffineOpen_bot _, fun _ => 0, fun j l => ?_,
        top_unique fun f _ => Subsingleton.elim 0 f ▸ zero_mem _⟩
      have := hempty (⊥ ⊓ H.U l) (fun ⟨z, hz⟩ => hz.1)
      exact Subsingleton.elim _ _
    · obtain ⟨U, hUa, hUe, hR⟩ := hU i hi
      have hWU : W = U := SetLike.ext fun z => (key' z).trans (Set.ext_iff.1 hUe z).symm
      subst hWU
      have hne : (W : Set M.Z).Nonempty := ⟨_, (key' _).2 (div_genericPoint hi)⟩
      have hr : ∀ j, ∃ f : Γ(M.Z, W), valF M.pt W f = t j / t i := fun j =>
        (mem_ringOn_iff_exists hne).1 (mem_ringOn.2 fun z hz => ((key' z).1 hz).2 j)
      choose r hr using hr
      refine ⟨hUa, r, fun j l => ?_, ?_⟩
      · by_cases hl : ((W ⊓ H.U l : M.Z.Opens) : Set M.Z).Nonempty
        · have hl' : (H.U l : Set M.Z).Nonempty :=
            Set.Nonempty.mono (show (W ⊓ H.U l : M.Z.Opens) ≤ H.U l from inf_le_right) hl
          apply M.res_injective _ hl
          rw [map_mul, res_apply, res_apply, res_apply, M.valF_resG _ hl, M.valF_resG _ hl, M.valF_resG _ hl,
            hv j l hl', hv i l hl', hr]
          have hdl := hd.ne l
          field_simp
        · have := hempty _ hl
          exact Subsingleton.elim _ _
      · refine top_unique fun f _ => ?_
        have h1 := hR _ ((mem_ringOn_iff_exists hne).2 ⟨f, rfl⟩)
        have e : (Set.range ψ ∪ Set.range fun j => t j / t i) =
            M.res W hne '' (Set.range (constFn p W) ∪ Set.range r) := by
          rw [Set.image_union, ← Set.range_comp, ← Set.range_comp]
          congr 2
          · funext a
            exact ((M.res_apply W hne _).trans
              (valR_constFn_of_over p ψ M.pt hp W (M.top_le_preimage_pt hne) a)).symm
          · funext j
            exact ((M.res_apply W hne _).trans (hr j)).symm
        rw [e, ← RingHom.map_closure] at h1
        obtain ⟨g, hg1, hg2⟩ := h1
        have : g = f := M.res_injective W hne (hg2.trans (M.res_apply W hne f).symm)
        exact this ▸ hg1

end GlobalTheory.ZH.RatModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionOfCoordinateDivisibilityStatement
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_of_coordinate_divisibility : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω) (J : Type) (σ : J → H.Sec) (t : J → Ω) (k : Type) [CommRing k] (p : M.Z ⟶ Sp k) (ψ : k →+* Ω), H.IsLB → M.GenTriv H d → (∀ j, M.HasVal d (σ j) (t j)) → (∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) → M.pt ≫ p = spMap ψ → (∀ i, t i ≠ 0 → ∃ U : M.Z.Opens, IsAffineOpen U ∧ (U : Set M.Z) = {z | M.Div t i z} ∧ ∀ x ∈ M.ringOn U, x ∈ Subring.closure (Set.range ψ ∪ Set.range fun j => t j / t i)) → ImmBy p H σ Set.univ := by
  first | exact @GlobalTheory.ZH.RatModel.immBy_of_div | exact GlobalTheory.ZH.RatModel.immBy_of_div | (intros; apply GlobalTheory.ZH.RatModel.immBy_of_div <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.LocThetaConv

variable {X Y : Scheme.{0}}

theorem bijective_appLE (f : Y ⟶ X) [IsOpenImmersion f] (W : X.Opens) (hW : W ≤ f.opensRange)
    (U : Y.Opens) (e : U ≤ f ⁻¹ᵁ W) (e' : f ⁻¹ᵁ W ≤ U) : Function.Bijective (f.appLE W U e).hom := by
  obtain rfl : U = f ⁻¹ᵁ W := le_antisymm e e'
  rw [Scheme.Hom.appLE_eq_app]
  have := f.isIso_app W hW
  exact ConcreteCategory.bijective_of_isIso (f.app W)

theorem appLE_resG (f : Y ⟶ X) {W W' : X.Opens} (h : W' ≤ W) {U : Y.Opens} (e : U ≤ f ⁻¹ᵁ W')
    (a : Γ(X, W)) : (f.appLE W' U e).hom (resG X h a) =
      (f.appLE W U (e.trans fun _ hy => h hy)).hom a := by
  rw [← Scheme.Hom.map_appLE f e (homOfLE h).op]
  rfl

theorem resG_appLE (f : Y ⟶ X) {W : X.Opens} {U U' : Y.Opens} (h : U' ≤ U) (e : U ≤ f ⁻¹ᵁ W)
    (a : Γ(X, W)) : resG Y h ((f.appLE W U e).hom a) = (f.appLE W U' (h.trans e)).hom a := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

theorem g_val (L : LB X) {K : Type} [Fintype K] [Subsingleton K] (φ : K → (Y ⟶ X)) (k : K)
    (i j : K → L.ι) : ((LB.LinComb L φ (fun _ => 1)).g i j).val =
      ((φ k).appLE (L.U (i k) ⊓ L.U (j k)) (LB.wchart L φ i ⊓ LB.wchart L φ j)
        (le_inf (inf_le_left.trans (LB.wchart_le L φ i k)) (inf_le_right.trans (LB.wchart_le L φ j k)))).hom
        (L.g (i k) (j k)).val := by
  simp only [LB.LinComb, zpow_one]
  erw [Fintype.prod_subsingleton _ k]
  rfl

theorem mem_one {L : LB X} {j : Fin 1 → L.ι} {x : X} :
    x ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).U j ↔ x ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem mem_pull' {L : LB X} (f : Y ⟶ X) {j : L.ι} {y : Y} :
    y ∈ (L.pull f).U (fun _ => j) ↔ f y ∈ L.U j :=
  ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem exists_secOn (L : LB X) (V : X.Opens) (σ : LB.Sec (L.pull V.ι)) :
    ∃ τ ∈ secOn (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)) V,
      ∀ y ∈ nonzeroLocus σ, ∃ j, V.ι y ∈ X.basicOpen (τ j) := by
  set L₁ := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1) with hL₁
  have e : ∀ j : Fin 1 → L.ι, (L.pull V.ι).U (fun _ => j 0) ≤ V.ι ⁻¹ᵁ (V ⊓ L₁.U j) :=
    fun j y hy => ⟨y.2, mem_one.2 ((mem_pull' _).1 hy)⟩
  have e' : ∀ j : Fin 1 → L.ι, V.ι ⁻¹ᵁ (V ⊓ L₁.U j) ≤ (L.pull V.ι).U (fun _ => j 0) :=
    fun j y hy => (mem_pull' _).2 (mem_one.1 hy.2)
  have hV : V ≤ V.ι.opensRange := V.opensRange_ι.ge
  choose τ hτ using fun j : Fin 1 → L.ι =>
    (bijective_appLE V.ι _ (inf_le_left.trans hV) _ (e j) (e' j)).2 (σ.f fun _ => j 0)
  refine ⟨τ, fun i j => ?_, fun y hy => ?_⟩
  · apply (bijective_appLE V.ι (V ⊓ L₁.U i ⊓ L₁.U j) ((inf_le_left.trans inf_le_left).trans hV)
      ((L.pull V.ι).U (fun _ => i 0) ⊓ (L.pull V.ι).U (fun _ => j 0))
      (fun y hy => ⟨e i hy.1, (e j hy.2).2⟩) (fun y hy => ⟨e' i hy.1, e' j ⟨hy.1.1, hy.2⟩⟩)).1
    have h := σ.compat (fun _ => i 0) (fun _ => j 0)
    rw [← hτ i, ← hτ j] at h
    rw [map_mul]
    refine ((appLE_resG _ _ _ _).trans (resG_appLE _ _ _ _).symm).trans (h.trans ?_)
    congr 1
    · have h1 : ((L.pull V.ι).g (fun _ => i 0) (fun _ => j 0)).val =
          (V.ι.appLE (L.U (i 0) ⊓ L.U (j 0)) ((L.pull V.ι).U (fun _ => i 0) ⊓ (L.pull V.ι).U (fun _ => j 0))
            (fun y hy => ⟨(mem_pull' _).1 hy.1, (mem_pull' _).1 hy.2⟩)).hom
            (L.g (i 0) (j 0)).val :=
        (g_val L (fun _ : PUnit => V.ι) PUnit.unit _ _).trans (by rfl)
      have h2 : (L₁.g i j).val = resG X (fun y hy => ⟨mem_one.1 hy.1, mem_one.1 hy.2⟩ :
          L₁.U i ⊓ L₁.U j ≤ L.U (i 0) ⊓ L.U (j 0)) (L.g (i 0) (j 0)).val :=
        (g_val L (fun _ : Fin 1 => 𝟙 X) 0 _ _).trans (by rfl)
      rw [h1, h2]
      exact ((appLE_resG _ _ _ _).trans (appLE_resG _ _ _ _)).symm
    · exact (resG_appLE _ _ _ _).trans (appLE_resG _ _ _ _).symm
  · obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨fun _ => k PUnit.unit, ?_⟩
    have h := Scheme.basicOpen_appLE V.ι _ _ (e fun _ => k PUnit.unit) (τ fun _ => k PUnit.unit)
    have h' := hτ fun _ => k PUnit.unit
    have hk' : y ∈ V.toScheme.basicOpen (σ.f fun _ => k PUnit.unit) := hk
    rw [← h'] at hk'
    exact (h.le hk').2

theorem exists_point {K : Type} [Field K] [IsAlgClosed K] (π : X ⟶ Y) [LocallyOfFiniteType π]
    (x : Sp K ⟶ Y) (O : X.Opens) (p : X) (hp : p ∈ O) (hx : π p = x (IsLocalRing.closedPoint K)) :
    ∃ g : Sp K ⟶ X, g ≫ π = x ∧ ⊤ ≤ g ⁻¹ᵁ O := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (IsLocalRing.closedPoint K) hx
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints (Z := (pullback.fst π x ⁻¹ᵁ O : Set _))
    ⟨z, show pullback.fst π x z ∈ O from hz ▸ hp⟩ (pullback.fst π x ⁻¹ᵁ O).isOpen.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun a _ => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc a) ∈ O
    rw [pointOfClosedPoint_apply]
    exact hcO

theorem exists_secFam_fibNe : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), Q.LocTheta → ∀ z : M.Z, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.FibNe N σ := by
  intro o Ω _ _ _ _ S ρ M U₀ Q H z
  obtain ⟨N, σ, hz, hσ⟩ := H z
  obtain ⟨τ, hτ, hne⟩ := exists_secOn Q.L.L _ σ
  refine ⟨N, τ, hz, hτ, fun K _ _ x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hσ _ (hx ⟨IsLocalRing.closedPoint K, rfl⟩)
  obtain ⟨j, hj⟩ := hne y hy
  have := Q.dim
  have : Smooth Q.G.hom := SmoothOfRelativeDimension.smooth S.g _
  obtain ⟨g, hg, hO⟩ := exists_point Q.G.hom x _ _ hj hyx
  exact ⟨g, j, hg, ((GlobalTheory.Points.le_preimage_basicOpen_iff g
    (GlobalTheory.Points.le_preimage_mono g (Scheme.basicOpen_le _ _) hO) (τ j)).1 hO).ne_zero⟩

end GlobalTheory.ZH.LocThetaConv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localThetaSection_fibreNonzero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), Q.LocTheta → ∀ z : M.Z, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.FibNe N σ := by
  first | exact @GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe | exact GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe | (intros; apply GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalHomOfTest
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.ZHPre
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}

theorem isLocalHom_of_test {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)
    (jV : u.V →+* OO p)
    (hj : ∀ x, (jV x : PadicAlgCl p) = algebraMap (FractionRing u.V) _ (algebraMap u.V (FractionRing u.V) x)) :
    IsLocalHom jV := by
  refine ⟨fun x hx => ?_⟩
  have h1 : ‖(jV x : PadicAlgCl p)‖ = 1 :=
    le_antisymm ((mem_OO_iff _).1 (jV x).2) (not_lt.1 fun h => (not_isUnit_OO_iff _).2 h hx)
  have h0 : algebraMap u.V (FractionRing u.V) x ≠ 0 := fun h => by
    rw [hj, h, map_zero, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨v, hv⟩ := (u.norm_le (algebraMap u.V (FractionRing u.V) x)⁻¹).1 (by
    rw [map_inv₀, ← hj, norm_inv, h1, inv_one])
  refine IsUnit.of_mul_eq_one v (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, hv, mul_inv_cancel₀ h0, map_one]

end GlobalTheory.ZH.ZHPre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFunctionFieldOfIsDominant
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_functionField_point (X : Scheme.{0}) [IsIntegral X] :
    ∃ (K : Type) (_ : Field K) (pt : Sp K ⟶ X), (∀ w, pt w = genericPoint X) ∧
      ∀ x : K, ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x := by
  let pt : Sp X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)
  refine ⟨X.functionField, inferInstance, pt, fun w => ?_, fun x => ?_⟩
  · rw [Subsingleton.elim w (IsLocalRing.closedPoint X.functionField)]
    exact Scheme.fromSpecStalk_closedPoint
  · obtain ⟨W, hW, g, rfl⟩ := X.presheaf.germ_exist (x := genericPoint X) x
    obtain ⟨V, hV, hz, hle⟩ := exists_isAffineOpen_mem_and_subset hW
    have hle' : V ≤ W := hle
    let φ : Γ(X, V) ⟶ CommRingCat.of X.functionField := X.presheaf.germ V (genericPoint X) hz
    have e : pt = Spec.map φ ≫ hV.fromSpec := (hV.fromSpecStalk_eq_fromSpecStalk hz).symm
    refine ⟨V, (X.presheaf.map (homOfLE hle').op).hom g, ⟨_, hz⟩, ?_⟩
    rw [e, valF_eq_valR, valR_eq _ V (le_preimage_specMap_fromSpec hV φ), valMap_specMap_fromSpec]
    exact X.presheaf.germ_res_apply (homOfLE hle') _ hz g

theorem RatModel.exists_functionField_of_isDominant (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (M : RatModel o Ω) (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ M.Z) [IsDominant q] :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra o Ω') (φ : Ω →ₐ[o] Ω') (pt : Sp Ω' ⟶ X),
      Set.range pt = {genericPoint X} ∧
      (∀ x : Ω', ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x) ∧
      pt ≫ q = spMap φ.toRingHom ≫ M.pt := by
  obtain ⟨K, _, pt, hpt, honto⟩ := exists_functionField_point X
  have hq : q (genericPoint X) = genericPoint M.Z := by
    have h := (genericPoint_spec X).image q.continuous
    rw [Set.image_univ, q.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec M.Z)
  have hy : ∀ w, (pt ≫ q) w = genericPoint M.Z := fun w => by
    rw [Scheme.Hom.comp_apply, hpt, hq]
  have hs : ∀ w, (pt ≫ q) w ⤳ genericPoint M.Z := fun w => (hy w) ▸ specializes_rfl
  have hm : ∀ x : Ω, x ∈ M.O (genericPoint M.Z) := fun x => by rw [RatModel.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf (pt ≫ q) _ hs).comp
    ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)).toSubring hm)
  letI : Algebra o K := (β.comp (algebraMap o Ω)).toAlgebra
  refine ⟨K, inferInstance, inferInstance, { β with commutes' := fun _ => rfl }, pt, ?_, honto, ?_⟩
  · exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, hpt (IsLocalRing.closedPoint K)⟩, by
      rintro _ ⟨w, rfl⟩
      exact hpt w⟩
  · obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := genericPoint M.Z) (U := ⊤) trivial
    have h1 := top_le_preimage_of_specializes hs hz
    have h2 : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt ⟨_, hz⟩
    refine ext_of_valR hU h1 (le_preimage_comp _ _ h2 (le_preimage_top _)) fun f => ?_
    exact ((valR_spMap_comp β M.pt U h2 f).trans (RatModel.val_valF ((top_le_preimage_iff _ _).1 h1) f)).symm

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricLiftActionGeometricFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricLiftActionGeometricFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.ClassWeight

section General
open ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.ThetaPtMove
variable {B B' : Scheme.{0}} {G : Over B} [GrpObj G] {A : Over B'} [GrpObj A]
  {f : B' ⟶ B} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over B'} {T₀ : Over B} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem sv_sum_smul {L : LB A.left} {k : ℤ} {I : Type} (F : Finset I) (c : I → Γ(T.left, ⊤))
    (v : I → SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    ThetaAct.sv (∑ l ∈ F, c l • v l) r z J =
      ∑ l ∈ F, gs (r ≫ (fst T A).left) z ⊤ (c l) * ThetaAct.sv (v l) r z J := by
  induction F using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have h := ThetaAct.sv_add (0 : SecM A L k T) 0 r z hJ
    rw [add_zero] at h
    exact left_eq_add.1 h
  | insert a F ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ThetaAct.sv_add _ _ _ _ hJ, ThetaAct.sv_smul _ _ _ _ hJ, ih]

theorem secRel_sum {k : ℤ} {I : Type} [Fintype I] (c : I → Γ(T₀.left, ⊤))
    {t : I → LB.Sec (LPow A L₁ k T)} {s : I → LB.Sec (LPow G L₀ k T₀)} (h : ∀ l, SecRel hp τ hτ w (t l) (s l)) :
    SecRel hp τ hτ w (SecM.toSec A (∑ l, τ.appTop.hom (c l) • SecM.ofSec A (t l)))
      (SecM.toSec G (∑ l, c l • SecM.ofSec G (s l))) := by
  intro Z r z J J' hJ hJ'
  refine (sv_sum_smul Finset.univ c (fun l => SecM.ofSec G (s l)) (r ≫ psi hp τ hτ) z hJ).trans (Eq.trans ?_
    (congrArg (_ * ·) (sv_sum_smul Finset.univ (fun l => τ.appTop.hom (c l)) (fun l => SecM.ofSec A (t l))
      r z hJ').symm))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, Category.assoc, psi_fst', ← Category.assoc]
  exact congrArg₂ (· * ·) (gs_pull _ τ z ⊤ trivial (c l)).symm (h l Z r z J J' hJ hJ')

theorem isActOf_unique {L : LB A.left} (hL : L.IsLB) {k : ℤ} {θ : ThetaGrp A L k T}
    {s s₁ s₂ : LB.Sec (LPow A L k T)} (h₁ : IsActOf A L k θ s s₁) (h₂ : IsActOf A L k θ s s₂) :
    SecM.ofSec A s₁ = SecM.ofSec A s₂ :=
  ThetaAct.sv_ext hL fun y J hJ =>
    ((ThetaAct.isActOf_iff hL θ s s₁).1 h₁ y J hJ).trans ((ThetaAct.isActOf_iff hL θ s s₂).1 h₂ y J hJ).symm

theorem exists_isActOf' {L : LB A.left} (hL : L.IsLB) {k : ℤ} (θ : ThetaGrp A L k T)
    (s : LB.Sec (LPow A L k T)) : ∃ s', IsActOf A L k θ s s' := by
  obtain ⟨v, hv⟩ := ThetaAct.exists_act hL θ (SecM.ofSec A s)
  exact ⟨SecM.toSec A v, (ThetaAct.isActOf_iff hL θ _ _).2 fun y J hJ => hv _ _ y J hJ⟩

theorem ofSec_eq_sum {L : LB A.left} {k : ℤ} {I : Type} [Fintype I] (c : I → Γ(T.left, ⊤))
    (s : I → LB.Sec (LPow A L k T)) (σ : LB.Sec (LPow A L k T))
    (h : ∀ j, σ.f j = ∑ l, liftFun A _ (c l) * (s l).f j) : σ = SecM.toSec A (∑ l, c l • SecM.ofSec A (s l)) := by
  have e : SecM.ofSec A σ = ∑ l, c l • SecM.ofSec A (s l) := by
    refine Subtype.ext (funext fun j => (h j).trans ?_)
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [← e]
  rfl

theorem symLift_act_move [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {k : ℤ} {n : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ n = 1) {θ₀ : ThetaGrp G L₀ k T₀}
    (H₀ : SymLift G L₀ k n x₀ θ₀) {I : Type} [Fintype I] (c : I → I → Γ(T₀.left, ⊤)) (c' : I → I → Γ(T.left, ⊤))
    (hc : ∀ l i, τ.appTop.hom (c l i) = c' l i)
    {t : I → LB.Sec (LPow A L₁ k T)} {s : I → LB.Sec (LPow G L₀ k T₀)} (h : ∀ l, SecRel hp τ hτ w (t l) (s l))
    (hs : ∀ i σ, IsActOf G L₀ k θ₀ (s i) σ → ∀ j, σ.f j = ∑ l, liftFun G _ (c l i) * (s l).f j) :
    ∃ θ : ThetaGrp A L₁ k T, SymLift A L₁ k n x θ ∧ ∀ i t', IsActOf A L₁ k θ (t i) t' →
      SecM.ofSec A t' = ∑ l, c' l i • SecM.ofSec A (t l) := by
  obtain ⟨θ, hθ, H⟩ := symLift_move hp τ hτ hw hL₀ hL₁ hx hn H₀
  refine ⟨θ, hθ, fun i t' ht' => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_isActOf' hL₀ θ₀ (s i)
  have e := ofSec_eq_sum _ _ σ (hs i σ hσ)
  have hr := secRel_sum hp τ hτ (fun l => c l i) h
  rw [← e] at hr
  refine (isActOf_unique hL₁ ht' (H _ _ _ _ (h i) hr hσ)).trans ?_
  simp only [hc]
  rfl

end General

theorem appTop_fn {R : Type} [CommRing R] (V : Type) [CommRing V] [IsDomain V] (F : Type) [Field F]
    [Algebra (FractionRing V) F] (y : R →+* F) (c : R) :
    (show (TFK (R := V) F).left ⟶ (baseOver (Sp R)).left from spMap y).appTop.hom (fn c) = kf V F (y c) :=
  (congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))).symm

theorem exists_symLift_act : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt (S.r • a)).left → x ^ S.N = 1 → ∃ θ : ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p)), SymLift u.A.A u.A.L S.N S.N x θ ∧ ∀ i t', IsActOf u.A.A u.A.L S.N θ (t i) t' → SecM.ofSec u.A.A t' = ∑ l, kf u.V (PadicAlgCl p) (y₀ (algebraMap o S.R (S.ρ a l i))) • SecM.ofSec u.A.A (t l) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u w hw t ht a x hx hn
  have := u.A.isAb.comm
  exact symLift_act_move u.cart (T := TFK (R := u.V) (PadicAlgCl p))
    (T₀ := baseOver (Sp S.R)) (spMap y₀) (base_eq u) hw ρ.P.isLB u.A.isLB hx.symm hn (ρ.U_sym a)
    (fun l i => fn (algebraMap o S.R (S.ρ a l i))) _ (fun l i => appTop_fn u.V (PadicAlgCl p) y₀ _) ht (ρ.U_act a)

end GlobalTheory.ZH.ClassWeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricLiftActionGeometricFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetricLift_action_geometricFibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt (S.r • a)).left → x ^ S.N = 1 → ∃ θ : ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p)), SymLift u.A.A u.A.L S.N S.N x θ ∧ ∀ i t', IsActOf u.A.A u.A.L S.N θ (t i) t' → SecM.ofSec u.A.A t' = ∑ l, kf u.V (PadicAlgCl p) (y₀ (algebraMap o S.R (S.ρ a l i))) • SecM.ofSec u.A.A (t l) := by
  first | exact @GlobalTheory.ZH.ClassWeight.exists_symLift_act | exact GlobalTheory.ZH.ClassWeight.exists_symLift_act | (intros; apply GlobalTheory.ZH.ClassWeight.exists_symLift_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCarries
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ParTranslate
open GlobalTheory.UT GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar GlobalTheory.ThetaTranslate ReciprocityTheory.ChartRestriction.G.DVR

theorem toStk_onto {F : Type} [Field F] (z : Sp F) : Function.Surjective (toStk z) := fun a => by
  obtain ⟨U, hU, f, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => (Subsingleton.elim (α := PrimeSpectrum F) z y) ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 f
  exact ⟨x, rfl⟩

theorem isAdd_comm {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {g g' g'' : GtPtF D F} (h : g.IsAdd g' g'') : g'.IsAdd g g'' := by
  rw [isAdd_iff] at h ⊢
  refine ⟨h.1.trans (mul_comm _ _), fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  rw [C.s12, h.2 χ y J hJ, mul_comm]

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
  (w : W0 U)

abbrev Carries (t : SecA A F k) (σ : U.SecGF F k) : Prop :=
  GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w
    (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k
    (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) σ

theorem exists_carries (hw : w.IsGen) (σ : U.SecGF F k) : ∃ t, Carries U F k w t σ := by
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  obtain ⟨-, i₂⟩ := isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')
  exact (i₂ σ).exists

theorem exists_unit_carries (a : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (l : U.LG.L.ι)
    (hl : ⊤ ≤ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l) (y : Sp F)
    (J : (Sp F ⟶ A.A.left) → A.L.ι) (hJ : Good A.L y J) :
    ∃ c : ((Sp F).presheaf.stalk y)ˣ, ∀ t σ, Carries U F k w t σ →
      toStk y (valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a).left) _ (σ.f (fun _ => l))) =
        c.val * secVal t (show Sp F ⟶ _ from (ptSecT A.A (a ≫ U.gen.hom)).left) y J := by
  let r : Sp F ⟶ (UnifPre.GF (G := G) F).left := (lift (𝟙 (TFK (R := R) F)) a).left
  let r' : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e₀ : r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = a.left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) a)
  have e₁ : r ≫ (U.genF F).left = r' := by
    have : lift (𝟙 (TFK (R := R) F)) a ≫ U.genF F = ptSecT A.A (a ≫ U.gen.hom) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
    exact congrArg (fun q => q.left) this
  have e₂ : r' ≫ (snd (TFK (R := R) F) A.A).left =
      (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ U.gen.hom.left := by
    rw [e₀]
    exact congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) (a ≫ U.gen.hom))
  have m₂ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R)) y ∈
      U.LG.L.U l := by
    rw [e₀]
    exact (top_le_iff_mem _ _ y).1 hl
  have m₁ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ U.gen.hom.left) y ∈
      A.L.U (J (r' ≫ (snd (TFK (R := R) F) A.A).left)) := by
    rw [← e₂]
    exact hJ _
  refine ⟨isoVal w (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) y l
    (J (r' ≫ (snd (TFK (R := R) F) A.A).left)) ^ (k : ℤ), fun t σ h => ?_⟩
  have H := (isoRelM_iff w _ k _ h.1 _ h.2.1 t σ).1 h (Sp F) r y l _ m₂ m₁
  rw [Category.comp_id, e₁] at H
  exact (toStk_valF_gs r _ y (mem_wchart.2 fun _ => m₂) _).trans H

theorem exists_const_actVal (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F))
    (a a' : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (h : a' ≫ U.gen.hom = θ.pt * (a ≫ U.gen.hom))
    (l l' : U.LG.L.ι)
    (hl : ⊤ ≤ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l)
    (hl' : ⊤ ≤ (show Sp F ⟶ G.left from a'.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l') :
    ∃ c : F, c ≠ 0 ∧ ∀ t t' σ σ', Carries U F k w t σ → Carries U F k w t' σ' → ActVal θ t t' →
      valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a).left) _ (σ'.f (fun _ => l)) =
        c * valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a').left) _ (σ.f (fun _ => l')) := by
  let y : Sp F := IsLocalRing.closedPoint F
  obtain ⟨J, hJ⟩ := GlobalTheory.UT.CoefBasic.exists_good' A.isLB y
  obtain ⟨c, hc⟩ := exists_unit_carries U F k w a l hl y J hJ
  obtain ⟨c', hc'⟩ := exists_unit_carries U F k w a' l' hl' y J hJ
  let r : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e : r ≫ (translT A.A θ.pt).left = (ptSecT A.A (a' ≫ U.gen.hom)).left := by
    rw [h]
    exact congrArg (fun q => q.left) (ptSecT_translT (a ≫ U.gen.hom) θ.pt)
  obtain ⟨d, hd⟩ := toStk_onto y (c * thetaVal θ r y J * c'⁻¹).val
  refine ⟨d, fun h0 => ?_, fun t t' σ σ' h₁ h₂ h₃ => (toStk y).injective ?_⟩
  · have : Nontrivial ((Sp F).presheaf.stalk y) := inferInstance
    rw [h0, map_zero] at hd
    exact Units.ne_zero _ hd.symm
  · have a₁ := h₃ (Sp F) r y J hJ
    rw [e] at a₁
    rw [map_mul, hd, hc t' σ' h₂, hc' t σ h₁, Units.val_mul, Units.val_mul, _root_.mul_assoc,
      Units.inv_mul_cancel_left, _root_.mul_assoc]
    exact congrArg _ a₁

end

theorem parAt_translate : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) k) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (a a' : u.PtC) (g g' : GtPtF u.D.toPre (PadicAlgCl p)), 1 ≤ k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → a' ≫ u.U.gen.hom = x * (a ≫ u.U.gen.hom) → GtPtF.IsAdd pk.g g g' → u.ParAt k a g → u.ParAt k a' g' := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k pk x a a' g g' hk hx ha hg hpar w' hw' l' hl'
  have hG := hL.1.globalFns
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  obtain ⟨w₀, hw₀⟩ := u.U.toUnifPre.ext
  obtain ⟨v, hv⟩ := exists_normalisation (D := u.D.toPre) (F := PadicAlgCl p) k pk.g.b
  obtain ⟨ω₀, h₀⟩ := exists_normalisation (D := u.D.toPre) (F := PadicAlgCl p) k g.b
  obtain ⟨ω₁, h₁, -, hco⟩ := CoefPhi.coef_phi hL u.V _ hA u.D (PadicAlgCl p) k hk pk v hv g g' (isAdd_comm hg) ω₀ h₀
  replace hco := hco 1 k le_rfl (mul_one k).symm pk (one_smul _ _).symm rfl v ω₀ ω₁
    ⟨hv, fun _ _ _ => (pow_one _).symm⟩ ⟨h₀, fun _ _ _ => (pow_one _).symm⟩ ⟨h₁, fun _ _ _ => (pow_one _).symm⟩
  obtain ⟨c₁, hc₁, -, hfr⟩ := ((CoefBasic.coef_basic u.V u.D.toPre (PadicAlgCl p) k g').2.2 ω₁ h₁).2.2.1 w' hw'
  obtain ⟨θ, rfl, hθ⟩ := exists_theta_actVal u.U (PadicAlgCl p) hG hL.1.kerPow hk pk x hx w₀ hw₀ v hv
  obtain ⟨l, hl⟩ := exists_chart u.U.LG.isLB (u.toG a (IsLocalRing.closedPoint (PadicAlgCl p)))
  replace hl := (top_le_iff_mem _ _ _).2 hl
  obtain ⟨κ, hκ, hsum⟩ := hpar ω₀ h₀ l hl
  obtain ⟨c₂, hc₂, hval⟩ := exists_const_actVal u.U.toUnifPre (PadicAlgCl p) k w₀ θ a a' ha l l' hl hl'
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG u.U (PadicAlgCl p) hk w₀ hw₀
  refine ⟨c₁ * (κ * c₂), mul_ne_zero hc₁ (mul_ne_zero hκ hc₂), fun σ s hs => ?_⟩
  obtain ⟨t, ht⟩ := exists_carries u.U.toUnifPre (PadicAlgCl p) k w₀ hw₀ σ
  obtain ⟨t', ht'⟩ := exists_actVal u.A.isLB θ t
  have hE : u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ t' (e t') := (he _ _).2 rfl
  have hΦ := (hθ t t' s (e t') ⟨σ, ht, hs⟩ hE).2 ht'
  obtain ⟨σ', hσ', hs'⟩ := hE
  have H := hsum σ' _ hs'
  rw [hval t t' σ σ' ht hσ' ht', ← (Equiv.addRight pk.y).hasSum_iff] at H
  have H' := H.mul_left c₁
  rw [_root_.mul_assoc, _root_.mul_assoc]
  refine (congrArg (HasSum · _) (funext fun χ => ?_)).mp H'
  exact (congrArg (c₁ * ·) (hco s _ hΦ χ)).trans (hfr s χ).symm

end GlobalTheory.ZH.ParTranslate
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSectionsProportionalOfCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSectionsProportionalOfCoordinates
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.SecProp
open GlobalTheory.ZH.CrdCalc

section
variable {F : Type} [Field F] [IsAlgClosed F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) [LocallyOfFiniteType p]

theorem exists_point {Z : Set Y} (hZ : IsLocallyClosed Z) (hn : Z.Nonempty) :
    ∃ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ ∧ ∀ z, r z ∈ Z := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hn hZ
  exact ⟨pointOfClosedPoint p c hc, pointOfClosedPoint_comp p c hc,
    fun z => (congrArg (· ∈ Z) (pointOfClosedPoint_apply p c hc z)).mpr hcW⟩

theorem fn_ext_valR [IsReduced Y] {U : Y.Opens} {a b : Γ(Y, U)}
    (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ⊤ ≤ r ⁻¹ᵁ U → valR r U a = valR r U b) : a = b := by
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hn : ((Y.basicOpen (a - b) : Y.Opens) : Set Y).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e)
  obtain ⟨r, hr, hz⟩ := exists_point p (Y.basicOpen (a - b)).isOpen.isLocallyClosed hn
  have hU : ⊤ ≤ r ⁻¹ᵁ U := fun z _ => Y.basicOpen_le _ (hz z)
  have hu := (isUnit_valR_iff r U hU (a - b)).2 fun z _ => hz z
  have e := h r hr hU
  rw [valR_eq r U hU, valR_eq r U hU, ← sub_eq_zero, ← map_sub] at e
  rw [valR_eq r U hU, e] at hu
  exact not_isUnit_zero hu

variable {H : LB Y} {I : Type} {a b : I → H.Sec}

theorem exists_mem_basicOpen (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ∃ w, w ≠ 0 ∧ Crd H b r w) (l : H.ι) (y : Y)
    (hy : y ∈ H.U l) : ∃ i, y ∈ Y.basicOpen ((b i).f l) := by
  by_contra hne
  let V : Y.Opens := ⨆ i, Y.basicOpen ((b i).f l)
  have hyV : y ∉ V := fun e => hne (TopologicalSpace.Opens.mem_iSup.1 e)
  obtain ⟨r, hr, hz⟩ := exists_point p
    ((H.U l).isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨y, hy, hyV⟩
  obtain ⟨w, hw, hc⟩ := h r hr
  have hU : ⊤ ≤ r ⁻¹ᵁ H.U l := fun z _ => (hz z).1
  obtain ⟨c, hc'⟩ := crd_unique hc
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H b r (fun i => valR r (H.U l) ((b i).f l)))
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  have hu : IsUnit (valR r (H.U l) ((b i).f l)) := by
    rw [hc' i]
    exact c.isUnit.mul (Ne.isUnit hi)
  have z : Sp F := IsLocalRing.closedPoint F
  exact (hz z).2 (TopologicalSpace.Opens.mem_iSup.2 ⟨i, (isUnit_valR_iff r _ hU _).1 hu (Set.mem_univ z)⟩)

theorem cross_eq [IsReduced Y] (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ∃ w, Crd H a r w ∧ Crd H b r w) (l : H.ι)
    (i i' : I) : (a i).f l * (b i').f l = (a i').f l * (b i).f l := by
  refine fn_ext_valR p fun r hr hU => ?_
  obtain ⟨w, ha, hb⟩ := h r hr
  obtain ⟨c, hc⟩ := crd_unique ha
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H a r (fun i => valR r (H.U l) ((a i).f l)))
  obtain ⟨d, hd⟩ := crd_unique hb
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H b r (fun i => valR r (H.U l) ((b i).f l)))
  rw [valR_mul r _ hU, valR_mul r _ hU, hc i, hc i', hd i, hd i']
  ring

end

theorem valR_const {F : Type} [Field F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) (r : Sp F ⟶ Y) (hr : r ≫ p = 𝟙 _)
    (U : Y.Opens) (hU : ⊤ ≤ r ⁻¹ᵁ U) (a : F) :
    valR r U (resG Y le_top (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a))) = a := by
  rw [valR_res r le_top hU, valR_eq r ⊤ le_rfl]
  have e : r.appLE ⊤ ⊤ le_rfl = r.appTop := (Scheme.Hom.app_eq_appLE r).symm
  have e₂ : p.appTop ≫ r.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hr, Scheme.Hom.id_appTop]
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((p.appTop ≫ r.appLE ⊤ ⊤ le_rfl).hom _) = a
  rw [e, e₂]
  exact (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply a

theorem proportional_of_crd : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ) (I J : Type) [Fintype J] (t : I → SecA A F k) (s : J → SecA A F k) (b : Matrix I J F), (∀ x : TFK (R := R) F ⟶ A.A, ∃ v : J → F, b.mulVec v ≠ 0 ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) s (show Sp F ⟶ _ from (ptSecT A.A x).left) v ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) t (show Sp F ⟶ _ from (ptSecT A.A x).left) (b.mulVec v)) → ∃ c : F, ∀ i, ∑ j, kf R F (b i j) • SecM.ofSec A.A (s j) = kf R F c • SecM.ofSec A.A (t i) := by
  intro hG R _ _ A F _ _ _ k I J _ t s b H
  have hsm := A.isAb.smooth
  let T : Over (Spec (CommRingCat.of (FractionRing R))) := TFK (R := R) F
  let p : (T ⊗ A.A).left ⟶ Sp F := (fst T A.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst T.hom A.A.hom))
  have : IsReduced (T ⊗ A.A).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  let m : I → SecM A.A A.L (k : ℤ) T := fun i => ∑ j, kf R F (b i j) • SecM.ofSec A.A (s j)
  let t' : I → SecA A F k := fun i => SecM.toSec A.A (m i)
  have key : ∀ r : Sp F ⟶ (T ⊗ A.A).left, r ≫ p = 𝟙 _ →
      ∃ w, w ≠ 0 ∧ Crd (LPow A.A A.L (k : ℤ) T) t' r w ∧ Crd (LPow A.A A.L (k : ℤ) T) t r w := by
    intro r hr
    let r' : T ⟶ T ⊗ A.A := Over.homMk r (by
      rw [← Over.w (fst T A.A), ← Category.assoc]
      exact (congrArg (· ≫ T.hom) hr).trans (Category.id_comp _))
    have er : ptSecT A.A (r' ≫ snd _ _) = r' := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
      rw [ptSecT, lift_fst]
      exact Over.OverMorphism.ext hr.symm
    obtain ⟨v, hv, hs, ht⟩ := H (r' ≫ snd _ _)
    have er' : (ptSecT A.A (r' ≫ snd _ _)).left = r := congrArg (·.left) er
    replace hs : Crd (LPow A.A A.L (k : ℤ) T) s r v := er' ▸ hs
    replace ht : Crd (LPow A.A A.L (k : ℤ) T) t r (b.mulVec v) := er' ▸ ht
    refine ⟨_, hv, ?_, ht⟩
    obtain ⟨l, c, hl, hc⟩ := hs
    refine ⟨l, c, hl, fun i => ?_⟩
    have e : (t' i).f l = ∑ j, resG _ le_top (p.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (b i j))) * (s j).f l := by
      change (m i).1 l = _
      simp only [m, Submodule.coe_sum, Finset.sum_apply]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, valR_eq r _ hl, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← valR_eq r _ hl, valR_mul r _ hl, valR_const p r hr _ hl, hc j, mul_left_comm]
  obtain ⟨c₀, hc₀⟩ := SectionRatio.exists_ratio A.isLB (φ := fun _ : Fin 1 => (snd T A.A).left)
    (ε := fun _ => (k : ℤ)) t' t
    (fun y J hJ => by
      have hm := hJ.mem (fun _ : Fin 1 => (snd T A.A).left) (𝟙 _)
      obtain ⟨i, hi⟩ := exists_mem_basicOpen p (H := LPow A.A A.L (k : ℤ) T) (b := t)
        (fun r hr => (key r hr).imp fun w hw => ⟨hw.1, hw.2.2⟩) _ y hm
      exact ⟨i, (SectionRatio.mem_basicOpen_iff_gs _ y hm).1 hi⟩)
    (fun i i' y J hJ => by
      have hm := hJ.mem (fun _ : Fin 1 => (snd T A.A).left) (𝟙 _)
      have e := cross_eq p (H := LPow A.A A.L (k : ℤ) T) (a := t') (b := t)
        (fun r hr => (key r hr).imp fun w hw => hw.2) (fun _ => J (𝟙 _ ≫ (snd T A.A).left)) i i'
      exact (gs_mul _ y _ hm _ _).symm.trans ((congrArg (gs (𝟙 _) y _) e).trans (gs_mul _ y _ hm _ _)))
  obtain ⟨d, hd⟩ := CommPairing.surj_fst hG A.isAb T c₀
  obtain ⟨c, rfl⟩ := (kf_bijective R F).2 d
  refine ⟨c, fun i => ThetaAct.sv_ext A.isLB fun y J hJ => ?_⟩
  refine (hc₀ i y J hJ).trans (Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm)
  exact congrArg (· * _) ((congrArg (gs (𝟙 _) y ⊤) hd.symm).trans (gs_pull (𝟙 _) _ y ⊤ trivial _))

end GlobalTheory.ZH.SecProp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSectionsProportionalOfCoordinatesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSections_proportional_of_coordinates : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ) (I J : Type) [Fintype J] (t : I → SecA A F k) (s : J → SecA A F k) (b : Matrix I J F), (∀ x : TFK (R := R) F ⟶ A.A, ∃ v : J → F, b.mulVec v ≠ 0 ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) s (show Sp F ⟶ _ from (ptSecT A.A x).left) v ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) t (show Sp F ⟶ _ from (ptSecT A.A x).left) (b.mulVec v)) → ∃ c : F, ∀ i, ∑ j, kf R F (b i j) • SecM.ofSec A.A (s j) = kf R F c • SecM.ofSec A.A (t i) := by
  first | exact @GlobalTheory.ZH.SecProp.proportional_of_crd | exact GlobalTheory.ZH.SecProp.proportional_of_crd | (intros; apply GlobalTheory.ZH.SecProp.proportional_of_crd <;> assumption)
end
end
