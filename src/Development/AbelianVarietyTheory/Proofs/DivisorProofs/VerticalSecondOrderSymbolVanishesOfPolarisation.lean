module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRelationZeroDerivationOfShifted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolEntriesRegularAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativesCoboundaryCoeffsMemMaximalIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatSymbolRegularOnSectionNonvanishingLocus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueEqQuotientSectionByPowerAtField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueEqQuotientSectionByPowerAtField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecQuot

open TopologicalSpace

variable {X : Scheme.{0}} {L : LB X}

abbrev ch1 (L : LB X) (j : Fin 1 → L.ι) : X.Opens := LB.wchart L (fun _ : Fin 1 => 𝟙 X) j

theorem mem_finOnePowerChartOpen_iff {j : Fin 1 → L.ι} {x : X} : x ∈ ch1 L j ↔ x ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun i => by rw [Fin.fin_one_eq_zero i]; exact h⟩

theorem gm_secM_g {Z : Scheme.{0}} (k : ℕ) (r : Z ⟶ X) (z : Z) (j j' : Fin 1 → L.ι) (hj : r z ∈ ch1 L j)
    (hj' : r z ∈ ch1 L j') :
    gm r z (ch1 L j ⊓ ch1 L j') ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))).g j j') =
      gm r z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ k := by
  refine (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) r z j j' hj hj').trans ?_
  rw [Fin.prod_univ_one, Category.comp_id, zpow_natCast]

abbrev M1 (L : LB X) (k : ℕ) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (k : ℤ))

theorem germ_finOnePowerLineBundle_transition_eq_pow {Z : Scheme.{0}} (k : ℕ) (r : Z ⟶ X) (z : Z) (j j' : Fin 1 → L.ι) (hj : r z ∈ ch1 L j)
    (hj' : r z ∈ ch1 L j') :
    gm r z ((M1 L k).U j ⊓ (M1 L k).U j') ((M1 L k).g j j') =
      gm r z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ k := gm_secM_g k r z j j' hj hj'

theorem lineBundlePowChartOpen_le_finOnePowerChartOpen (J : PUnit → L.ι) : powChart L J ≤ ch1 L (fun _ => J PUnit.unit) :=
  fun _ h => mem_finOnePowerChartOpen_iff.2 (mem_powChart.1 h)

def toPow {k : ℕ} (s : SecM (𝟙 X) L k) : (lbPow L k).Sec :=
  powSecOfGerm k (fun J => resG X (lineBundlePowChartOpen_le_finOnePowerChartOpen J) (s.f fun _ => J PUnit.unit)) fun y J J' hJ hJ' => by
    have e := gs_compat s (𝟙 X) y (j := fun _ => J PUnit.unit) (j' := fun _ => J' PUnit.unit)
      (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ) (lineBundlePowChartOpen_le_finOnePowerChartOpen J' hJ')
    have e2 := germ_finOnePowerLineBundle_transition_eq_pow k (𝟙 X) y (fun _ => J PUnit.unit) (fun _ => J' PUnit.unit) (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ) (lineBundlePowChartOpen_le_finOnePowerChartOpen J' hJ')
    refine (gs_res _ y (lineBundlePowChartOpen_le_finOnePowerChartOpen J) hJ _).trans (e.trans ?_)
    refine (congrArg₂ (· * ·) (congrArg Units.val e2) (gs_res _ y (lineBundlePowChartOpen_le_finOnePowerChartOpen J') hJ' _).symm).trans ?_
    rw [Units.val_pow_eq_pow_val]

theorem gs_toPow {k : ℕ} (s : SecM (𝟙 X) L k) {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (J : PUnit → L.ι)
    (hJ : r z ∈ powChart L J) : gs r z _ (powFn (toPow s) J) = gs r z _ (s.f fun _ => J PUnit.unit) :=
  gs_res r z (lineBundlePowChartOpen_le_finOnePowerChartOpen J) hJ _

theorem exists_secM_of_pow {n N : ℕ} (hn : n = N) (u : (lbPow L n).Sec) :
    ∃ c : SecM (𝟙 X) L N, ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j : Fin 1 → L.ι), r z ∈ ch1 L j →
      gs r z _ (c.f j) = gs r z _ (powFn u (fun _ => j 0)) := by
  subst hn
  have le : ∀ j : Fin 1 → L.ι, ch1 L j ≤ powChart L (fun _ => j 0) := fun j _ h => mem_powChart.2 (mem_finOnePowerChartOpen_iff.1 h)
  refine ⟨GlobalTheory.LBGerm.secOfGerm (M := M1 L n) (fun j => resG X (le j) (powFn u (fun _ => j 0)))
    fun y (j j' : Fin 1 → L.ι) hj hj' => ?_, fun r z j hj => gs_res r z (le j) hj _⟩
  have e := gs_powFn_compat u (𝟙 X) y _ _ (le j hj) (le j' hj')
  have e2 := germ_finOnePowerLineBundle_transition_eq_pow n (𝟙 X) y j j' hj hj'
  refine (gs_res (𝟙 X) y (le j) hj _).trans (e.trans ?_)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val e2) (gs_res (𝟙 X) y (le j') hj' _)).symm
  rw [Units.val_pow_eq_pow_val]

theorem gs_appLE₁ {Y Z : Scheme.{0}} (F : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ F ⁻¹ᵁ U) (r : Z ⟶ Y)
    (z : Z) (hz : r z ∈ V) (a : Γ(X, U)) : gs r z V ((F.appLE U V h).hom a) = gs (r ≫ F) z U a :=
  (gs_res r z h hz _).trans (gs_pull r F z U (h hz) a)

theorem valR_congr₁ {A : Type} [CommRing A] (x : Sp A ⟶ X) {U U' : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hU' : ⊤ ≤ x ⁻¹ᵁ U') (a : Γ(X, U)) (a' : Γ(X, U')) (h : ∀ z, gs x z U a = gs x z U' a') :
    valR x U a = valR x U' a' := by
  rw [valR, valR, dite_eq_left hU, dite_eq_left hU']
  refine congrArg _ (fn_ext fun z hz => ?_)
  rw [gs_appLE₁ _ _ _ _ _ _ hz, gs_appLE₁ _ _ _ _ _ _ hz]
  simp only [Category.id_comp]
  exact h z

theorem mem_of_top_le {A : Type} [CommRing A] {x : Sp A ⟶ X} {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (z : Sp A) :
    x z ∈ U := h (show z ∈ (⊤ : (Sp A).Opens) from trivial)

theorem valR_mul_pow_of_gs {A : Type} [CommRing A] (x : Sp A ⟶ X) {U V W : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (hW : ⊤ ≤ x ⁻¹ᵁ W) (c : Γ(X, U)) (f : Γ(X, V)) (s : Γ(X, W)) (m : ℕ)
    (h : ∀ z, gs x z U c = gs x z V f * gs x z W s ^ m) : valR x U c = valR x V f * valR x W s ^ m := by
  have hO : ⊤ ≤ x ⁻¹ᵁ (V ⊓ W) := fun z hz => ⟨hV hz, hW hz⟩
  have e1 : valR x V f = valR x (V ⊓ W) (resG X inf_le_left f) :=
    valR_congr₁ x hV hO _ _ fun z => (gs_res x z inf_le_left (mem_of_top_le hO z) f).symm
  have e2 : valR x W s = valR x (V ⊓ W) (resG X inf_le_right s) :=
    valR_congr₁ x hW hO _ _ fun z => (gs_res x z inf_le_right (mem_of_top_le hO z) s).symm
  have e3 : valR x U c = valR x (V ⊓ W) (resG X inf_le_left f * resG X inf_le_right s ^ m) :=
    valR_congr₁ x hU hO _ _ fun z => by
      rw [h z, gs_mul _ z _ (mem_of_top_le hO z), GlobalTheory.LBGerm.gs_pow _ z _ (mem_of_top_le hO z),
        gs_res x z inf_le_left (mem_of_top_le hO z), gs_res x z inf_le_right (mem_of_top_le hO z)]
  rw [e1, e2, e3, valR, valR, valR, dite_eq_left hO, dite_eq_left hO, dite_eq_left hO, map_mul, map_mul, map_pow, map_pow]

theorem nonzeroLocus_toPow {k : ℕ} (s : SecM (𝟙 X) L k) : nonzeroLocus (toPow s) = nonzeroLocus s := by
  refine nonzeroLocus_eq_of (toPow s) _ (fun y hy => ?_) fun y J hJ => ?_
  · have ⟨j, hj⟩ : ∃ j : Fin 1 → L.ι, y ∈ ch1 L j := exists_chart_of_mem_nonzeroLocus hy
    exact ⟨fun _ => j 0, mem_powChart.2 (mem_finOnePowerChartOpen_iff.1 hj)⟩
  · have e : gs (𝟙 X) y _ ((toPow s).f J) = gs (𝟙 X) y _ (s.f fun _ => J PUnit.unit) := gs_toPow s (𝟙 X) y J hJ
    rw [e]
    exact (mem_nonzeroLocus_iff_isUnit s (k := fun _ => J PUnit.unit) (lineBundlePowChartOpen_le_finOnePowerChartOpen J hJ)).symm

theorem extend_part [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) {k : ℕ} (s : SecM (𝟙 X) L k)
    (f : Γ(X, nonzeroLocus s)) : ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m → N = k * m → ∃ c : SecM (𝟙 X) L N,
      ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (i : L.ι), r z ∈ L.U i → r z ∈ nonzeroLocus s →
        gs r z _ (c.f fun _ => i) = gs r z _ f * gs r z _ (s.f fun _ => i) ^ m := by
  have hs' := nonzeroLocus_toPow s
  have le : ∀ J : PUnit → L.ι, nonzeroLocus (toPow s) ⊓ powChart L J ≤ nonzeroLocus s :=
    fun J => inf_le_left.trans hs'.le
  obtain ⟨N₀, hN₀⟩ := exists_sec_eq_pow_mul (m := 0) hL (toPow s) (fun J => resG X (le J) f)
    (GlobalTheory.LBGerm.mem_secOn_of_germ (M := lbPow L 0) _ fun y J J' hy hJ hJ' => by
      rw [gm_lbPow_g 0 (𝟙 X) y J J' hJ hJ', pow_zero, Units.val_one, _root_.one_mul]
      exact (gs_res (𝟙 X) y (le J) ⟨hy, hJ⟩ f).trans (gs_res (𝟙 X) y (le J') ⟨hy, hJ'⟩ f).symm)
  refine ⟨N₀, fun m N hm hN => ?_⟩
  obtain ⟨u, hu⟩ := hN₀ m hm
  obtain ⟨c, hc⟩ := exists_secM_of_pow (show 0 + k * m = N by omega) u
  refine ⟨c, fun r z i hi hz => ?_⟩
  have hJ : r z ∈ powChart L (fun _ => i) := mem_powChart.2 hi
  have hy : r z ∈ nonzeroLocus (toPow s) ⊓ powChart L (fun _ => i) := ⟨by rw [hs']; exact hz, hJ⟩
  have e := congrArg (gs r z _) (hu (fun _ => i))
  rw [gs_res r z _ hy, gs_mul r z _ hy, GlobalTheory.LBGerm.gs_pow r z _ hy, gs_res r z _ hy, gs_res r z _ hy] at e
  rw [hc r z (fun _ => i) (mem_finOnePowerChartOpen_iff.2 hi), e, gs_toPow s r z _ hJ, _root_.mul_comm]

theorem quot_part {k : ℕ} (s : SecM (𝟙 X) L k) (m N : ℕ) (hN : N = k * m) (ρ : SecM (𝟙 X) L N) :
    ∃ f : Γ(X, nonzeroLocus s), ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (i : L.ι), r z ∈ L.U i →
      r z ∈ nonzeroLocus s →
      gs r z _ (ρ.f fun _ => i) = gs r z _ f * gs r z _ (s.f fun _ => i) ^ m := by
  subst hN
  have loc : ∀ j : Fin 1 → L.ι, ∃ a : Γ(X, X.basicOpen (s.f j)),
      resG X (X.basicOpen_le _) (ρ.f j) = a * resG X (X.basicOpen_le _) (s.f j) ^ m := fun j => by
    obtain ⟨b, hb⟩ := (show IsUnit (resG X (X.basicOpen_le (s.f j)) (s.f j)) from
      X.toRingedSpace.isUnit_res_basicOpen (s.f j)).exists_left_inv
    refine ⟨resG X (X.basicOpen_le _) (ρ.f j) * b ^ m, ?_⟩
    have key : ∀ {R : Type} [CommRing R] (x y c : R), c * y = 1 → x = x * c ^ m * y ^ m := fun x y c h => by
      rw [_root_.mul_assoc, ← _root_.mul_pow, h, _root_.one_pow, _root_.mul_one]
    exact key _ _ _ hb
  choose a ha using loc
  have hga : ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (j : Fin 1 → L.ι), r z ∈ X.basicOpen (s.f j) →
      gs r z _ (ρ.f j) = gs r z _ (a j) * gs r z _ (s.f j) ^ m := fun r z j hz => by
    have e := congrArg (gs r z _) (ha j)
    have e1 := gs_res r z (X.basicOpen_le (s.f j)) hz (ρ.f j)
    have e2 := gs_res r z (X.basicOpen_le (s.f j)) hz (s.f j)
    have e3 := gs_mul r z _ hz (a j) (resG X (X.basicOpen_le (s.f j)) (s.f j) ^ m)
    have e4 := GlobalTheory.LBGerm.gs_pow r z _ hz (resG X (X.basicOpen_le (s.f j)) (s.f j)) m
    exact e1.symm.trans (e.trans (e3.trans (congrArg _ (e4.trans (congrArg (· ^ m) e2)))))
  obtain ⟨f, hf, -⟩ := X.sheaf.existsUnique_gluing' (fun j => X.basicOpen (s.f j)) (nonzeroLocus s)
    (fun j => homOfLE (GlobalTheory.basicOpen_le_nonzeroLocus s j)) le_rfl a (fun i j => fn_ext fun y hy => by
      have hi : y ∈ ch1 L i := X.basicOpen_le _ hy.1
      have hj : y ∈ ch1 L j := X.basicOpen_le _ hy.2
      refine (gs_res (𝟙 X) y inf_le_left hy (a i)).trans
        (Eq.trans ?_ (gs_res (𝟙 X) y inf_le_right hy (a j)).symm)
      have u : IsUnit (gs (𝟙 X) y _ (s.f i) ^ m) :=
        ((GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y _ hi _).2 hy.1).pow m
      refine u.mul_right_cancel ?_
      rw [← hga (𝟙 X) y i hy.1, gs_compat ρ (𝟙 X) y hi hj, gs_compat s (𝟙 X) y hi hj, hga (𝟙 X) y j hy.2,
        germ_finOnePowerLineBundle_transition_eq_pow (k * m) (𝟙 X) y i j hi hj, germ_finOnePowerLineBundle_transition_eq_pow k (𝟙 X) y i j hi hj, Units.val_pow_eq_pow_val,
        Units.val_pow_eq_pow_val]
      ring)
  refine ⟨f, fun r z i hi hz => ?_⟩
  have hz' : r z ∈ X.basicOpen (s.f fun _ => i) := (mem_nonzeroLocus_iff_basicOpen s (k := fun _ => i) (mem_finOnePowerChartOpen_iff.2 hi)).1 hz
  rw [hga r z _ hz', ← hf (fun _ => i)]
  exact congrArg (· * _) (gs_res r z (GlobalTheory.basicOpen_le_nonzeroLocus s _) hz' f)

theorem valR_secM_eq_mul_pow : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X) (j₀ : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j₀ → ∀ (k : ℕ) (s : SecM (𝟙 X) L k), ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus s → (∀ f : Γ(X, Out.nonzeroLocus s), ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m → N = k * m → ∃ c : SecM (𝟙 X) L N, valR ξ _ (c.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m) ∧ ∀ m N : ℕ, N = k * m → ∀ ρ : SecM (𝟙 X) L N, ∃ f : Γ(X, Out.nonzeroLocus s), valR ξ _ (ρ.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m := by
  intro X _ _ L hL F _ ξ j₀ hj₀ k s hs
  have hc : ⊤ ≤ ξ ⁻¹ᵁ ch1 L (fun _ => j₀) := fun z hz => mem_finOnePowerChartOpen_iff.2 (hj₀ hz)
  refine ⟨fun f => ?_, fun m N hN ρ => ?_⟩
  · obtain ⟨m₀, hm₀⟩ := extend_part hL s f
    refine ⟨m₀, fun m N hm hN => ?_⟩
    obtain ⟨c, hc'⟩ := hm₀ m N hm hN
    exact ⟨c, valR_mul_pow_of_gs ξ hc hs hc _ _ _ m fun z =>
      hc' ξ z j₀ (mem_of_top_le hj₀ z) (mem_of_top_le hs z)⟩
  · obtain ⟨f, hf⟩ := quot_part s m N hN ρ
    exact ⟨f, valR_mul_pow_of_gs ξ hc hs hc _ _ _ m fun z =>
      hf ξ z j₀ (mem_of_top_le hj₀ z) (mem_of_top_le hs z)⟩

end GlobalTheory.SecQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueEqQuotientSectionByPowerAtFieldStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointValue_eq_quotient_section_by_power_at_field : ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X] (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X) (j₀ : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j₀ → ∀ (k : ℕ) (s : SecM (𝟙 X) L k), ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus s → (∀ f : Γ(X, Out.nonzeroLocus s), ∃ m₀ : ℕ, ∀ m N : ℕ, m₀ ≤ m → N = k * m → ∃ c : SecM (𝟙 X) L N, valR ξ _ (c.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m) ∧ ∀ m N : ℕ, N = k * m → ∀ ρ : SecM (𝟙 X) L N, ∃ f : Γ(X, Out.nonzeroLocus s), valR ξ _ (ρ.f fun _ => j₀) = valR ξ _ f * valR ξ _ (s.f fun _ => j₀) ^ m := by
  first | exact @GlobalTheory.SecQuot.valR_secM_eq_mul_pow | exact GlobalTheory.SecQuot.valR_secM_eq_mul_pow | (intros; apply GlobalTheory.SecQuot.valR_secM_eq_mul_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatSymbolRegularOnSectionNonvanishingLocus
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatLoc

variable {F : Type} [Field F]

theorem der_bracket (d : Derivation ℤ F F) (x y β : F) (M : ℕ) :
    x * β ^ M * d (y * β ^ M) - y * β ^ M * d (x * β ^ M) = β ^ (2 * M) * (x * d y - y * d x) := by
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

theorem der_mul_pow (d : Derivation ℤ F F) (x β : F) (hβ : β ≠ 0) (m : ℕ) :
    d (x * β ^ (m + 1)) = β ^ (m + 1) * (d x + ((m + 1 : ℕ) : F) * x * (d β / β)) := by
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  field_simp
  ring

theorem symb_eq {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (x y β : F) (hβ : β ≠ 0) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * (x * β ^ (m + 1)) * (x * β ^ (m + 1) * δ₀ (y * β ^ (m + 1)) - y * β ^ (m + 1) * δ₀ (x * β ^ (m + 1))) -
      ∑ a, ∑ e, Λ a e * δ a (x * β ^ (m + 1)) *
        (x * β ^ (m + 1) * δ e (y * β ^ (m + 1)) - y * β ^ (m + 1) * δ e (x * β ^ (m + 1))) =
    β ^ (3 * (m + 1)) * (((k * (m + 1) : ℕ) : F) * x * (x * δ₀ y - y * δ₀ x) -
      ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x)) := by
  rw [mul_sub (β ^ (3 * (m + 1))), Finset.mul_sum]
  simp only [Finset.mul_sum]
  congr 1
  · rw [der_bracket]; ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [der_bracket, der_mul_pow _ _ _ hβ]; ring

theorem symb_one {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (y β : F) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * 1 * (1 * δ₀ y - y * δ₀ 1) -
      ∑ a, ∑ e, Λ a e * (δ a 1 + ((m + 1 : ℕ) : F) * 1 * (δ a β / β)) * (1 * δ e y - y * δ e 1) =
    ((m + 1 : ℕ) : F) * ((k : F) * δ₀ y - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y) := by
  simp only [Derivation.map_one_eq_zero, mul_zero, sub_zero, zero_add, one_mul, mul_one]
  rw [mul_sub, Finset.mul_sum]
  simp only [Finset.mul_sum]
  congr 1
  · push_cast; ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring

def derivationBracketSum {n : ℕ} (δ : Fin n → Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F) (x y : F) : F :=
  ∑ a, ∑ e, Λ a e * δ a x * (x * δ e y - y * δ e x)

theorem symb_two {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (x y β : F) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * x * (x * δ₀ y - y * δ₀ x) -
      ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x) =
    ((m + 1 : ℕ) : F) * x * (x * ((k : F) * δ₀ y - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y) -
      y * ((k : F) * δ₀ x - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e x)) - derivationBracketSum δ Λ x y := by
  have hs : ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x) =
      derivationBracketSum δ Λ x y + ((m + 1 : ℕ) : F) * x * (x * ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y -
        y * ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e x) := by
    unfold derivationBracketSum
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hs]; push_cast; ring

theorem tsum_add_one {n : ℕ} (δ : Fin n → Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F) (x y : F) :
    derivationBracketSum δ Λ (x + 1) y - derivationBracketSum δ Λ x y = ∑ a, ∑ e, Λ a e * δ a x * δ e y := by
  unfold derivationBracketSum
  simp only [map_add (f := _), Derivation.map_one_eq_zero, add_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
  ring

end GlobalTheory.HeatLoc

namespace GlobalTheory.HeatLoc

theorem valR_ne_zero_sec {X : Scheme.{0}} (L : LB X) {F : Type} [Field F] (ξ : Sp F ⟶ X) (j₀ : L.ι)
    (h : ⊤ ≤ ξ ⁻¹ᵁ L.U j₀) (k : ℕ) (s : SecM (𝟙 X) L k) (hs : ⊤ ≤ ξ ⁻¹ᵁ nonzeroLocus s) :
    valR ξ _ (s.f fun _ => j₀) ≠ 0 := by
  have hk : ⊤ ≤ ξ ⁻¹ᵁ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) fun _ => (k : ℤ)).U (fun _ => j₀) :=
    fun p hp => Set.mem_iInter.2 fun _ => h hp
  have h₁ := (GlobalTheory.AmpleSpan.isUnit_gs_iff ξ (IsLocalRing.closedPoint F) _ (hk trivial) _).1
    ((GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs s ξ _ (hk trivial)).1 (hs trivial))
  exact ((GlobalTheory.Points.le_preimage_basicOpen_iff ξ hk _).1
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of F) ξ h₁).ge).ne_zero

theorem symb_regular : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → ∀ (k : ℕ), 1 ≤ k → ∀ s : SecM (𝟙 P₀.A.left) P₀.L k, ⊤ ≤ ξ ⁻¹ᵁ (Out.nonzeroLocus s) → (∀ f f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ h : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ h = ∑ a, ∑ e, Λ a e * δ a (valR ξ _ f) * δ e (valR ξ _ f')) ∧ (∀ f : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, Λ a e * (δ a (valR ξ _ (s.f fun _ => j₀)) / valR ξ _ (s.f fun _ => j₀)) * δ e (valR ξ _ f)) := by
  intro K _ _ P₀ n v dd hdd F _ ψ ξ hξ hinj δ hδ j₀ hj₀ δ₀ Λ hyp k hk s hs
  haveI := P₀.isAb.proper
  haveI : CompactSpace P₀.A.left := QuasiCompact.compactSpace_of_compactSpace P₀.A.hom
  haveI : QuasiSeparatedSpace P₀.A.left := quasiSeparatedSpace_of_quasiSeparated P₀.A.hom
  obtain ⟨G₁, G₂⟩ := GlobalTheory.T.pointValue_eq_quotient_section_by_power_at_field P₀.A.left P₀.L P₀.isLB F ξ j₀ hj₀ k s hs
  have hβ := valR_ne_zero_sec P₀.L ξ j₀ hj₀ k s hs
  set β := valR ξ _ (s.f fun _ => j₀) with hβdef
  have v1 : valR ξ (nonzeroLocus s) 1 = 1 := by rw [WtAlg.valR_eq' ξ _ hs, map_one, map_one]
  have hM : ∀ m : ℕ, ((m + 1 : ℕ) : F) ≠ 0 := fun m h => by
    have : ψ ((m + 1 : ℕ) : K) = 0 := by rw [map_natCast]; exact h
    exact (Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)) ((map_eq_zero ψ).1 this)

  have partD : ∀ f : Γ(P₀.A.left, nonzeroLocus s), ∃ f' : Γ(P₀.A.left, nonzeroLocus s),
      valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e (valR ξ _ f) := by
    intro f
    obtain ⟨m₁, h₁⟩ := G₁ 1
    obtain ⟨m₂, h₂⟩ := G₁ f
    set m := max m₁ m₂
    obtain ⟨σ, hσ⟩ := h₁ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨τ, hτ⟩ := h₂ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨ρ, hρ⟩ := hyp (k * (m + 1)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) σ τ
    obtain ⟨g, hg⟩ := G₂ (3 * (m + 1)) (3 * (k * (m + 1))) (by ring) ρ
    have e := hρ _ _ rfl rfl
    rw [hσ, hτ, hg, v1, symb_eq δ δ₀ Λ _ _ β hβ k m, symb_one] at e
    have e' : valR ξ _ g = ((m + 1 : ℕ) : F) * ((k : F) * δ₀ (valR ξ _ f) -
        ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e (valR ξ _ f)) := by
      have h3 : β ^ (3 * (m + 1)) ≠ 0 := pow_ne_zero _ hβ
      rw [mul_comm (valR ξ _ g)] at e
      exact (mul_left_cancel₀ h3 e).symm
    refine ⟨constFn P₀.A.hom _ (((m + 1 : ℕ) : K)⁻¹) * g, ?_⟩
    rw [WtAlg.valR_mul'' ξ _ hs, GlobalTheory.LogKSBal.valR_constFn P₀.A.hom ξ hs hξ, e', map_inv₀, map_natCast,
      ← _root_.mul_assoc, inv_mul_cancel₀ (hM m), _root_.one_mul]

  have partT : ∀ f f' : Γ(P₀.A.left, nonzeroLocus s), ∃ h : Γ(P₀.A.left, nonzeroLocus s),
      valR ξ _ h = derivationBracketSum δ Λ (valR ξ _ f) (valR ξ _ f') := by
    intro f f'
    obtain ⟨m₁, h₁⟩ := G₁ f
    obtain ⟨m₂, h₂⟩ := G₁ f'
    obtain ⟨d, hd⟩ := partD f
    obtain ⟨d', hd'⟩ := partD f'
    set m := max m₁ m₂
    obtain ⟨σ, hσ⟩ := h₁ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨τ, hτ⟩ := h₂ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨ρ, hρ⟩ := hyp (k * (m + 1)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) σ τ
    obtain ⟨g, hg⟩ := G₂ (3 * (m + 1)) (3 * (k * (m + 1))) (by ring) ρ
    have e := hρ _ _ rfl rfl
    rw [hσ, hτ, hg, symb_eq δ δ₀ Λ _ _ β hβ k m, symb_two, ← hd, ← hd'] at e
    have e' : valR ξ _ g = ((m + 1 : ℕ) : F) * valR ξ _ f * (valR ξ _ f * valR ξ _ d' - valR ξ _ f' * valR ξ _ d) -
        derivationBracketSum δ Λ (valR ξ _ f) (valR ξ _ f') := by
      have h3 : β ^ (3 * (m + 1)) ≠ 0 := pow_ne_zero _ hβ
      rw [mul_comm (valR ξ _ g)] at e
      exact (mul_left_cancel₀ h3 e).symm
    refine ⟨((m + 1 : ℕ) : Γ(P₀.A.left, nonzeroLocus s)) * f * (f * d' - f' * d) - g, ?_⟩
    rw [WtAlg.valR_sub' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_sub' ξ _ hs,
      WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_natCast' ξ _ hs, e']
    ring
  refine ⟨fun f f' => ?_, partD⟩
  obtain ⟨h₁, e₁⟩ := partT (f + 1) f'
  obtain ⟨h₂, e₂⟩ := partT f f'
  refine ⟨h₁ - h₂, ?_⟩
  rw [WtAlg.valR_sub' ξ _ hs, e₁, e₂, WtAlg.valR_add' ξ _ hs, v1, tsum_add_one]

end GlobalTheory.HeatLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatSymbolRegularOnSectionNonvanishingLocusStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heat_symbol_regular_on_section_nonvanishing_locus : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → ∀ (k : ℕ), 1 ≤ k → ∀ s : SecM (𝟙 P₀.A.left) P₀.L k, ⊤ ≤ ξ ⁻¹ᵁ (Out.nonzeroLocus s) → (∀ f f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ h : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ h = ∑ a, ∑ e, Λ a e * δ a (valR ξ _ f) * δ e (valR ξ _ f')) ∧ (∀ f : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, Λ a e * (δ a (valR ξ _ (s.f fun _ => j₀)) / valR ξ _ (s.f fun _ => j₀)) * δ e (valR ξ _ f)) := by
  first | exact @GlobalTheory.HeatLoc.symb_regular | exact GlobalTheory.HeatLoc.symb_regular | (intros; apply GlobalTheory.HeatLoc.symb_regular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixZeroDerivationEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvariantFieldDualNumberOfIsInvariantTangentVe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvariantFieldDualNumberOfIsInvariantTangentVe
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvDerBridge

theorem valR_add_of {B : Type} [CommRing B] {Z : Scheme.{0}} (a : Sp B ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O)
    (f g : Γ(Z, O)) : valR a O (f + g) = valR a O f + valR a O g := by
  simp only [valR, dif_pos ha, map_add (f := _)]

theorem valR_mul_of {B : Type} [CommRing B] {Z : Scheme.{0}} (a : Sp B ⟶ Z) {O : Z.Opens} (ha : ⊤ ≤ a ⁻¹ᵁ O)
    (f g : Γ(Z, O)) : valR a O (f * g) = valR a O f * valR a O g := by
  simp only [valR, dif_pos ha, map_mul]

theorem isInvDer_of_isInv : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (v : TanM (𝟙 (Sp K)) A) (u : epsR K ⟶ A) (dd : Fld A.left), u.left = (tv v).left → IsTangent u → IsInv A v dd → GlobalTheory.KS.IsInvDer u dd := by
  intro K _ A _ _ v u dd hu ht hd W f
  have hpre : ((fst (epsR K) A ≫ u) * snd (epsR K) A).left ⁻¹ᵁ W = (snd (epsR K) A).left ⁻¹ᵁ W :=
    GlobalTheory.InvFieldBasis.preimage_translate ht W
  refine GlobalTheory.LogKSBal.ext_valR _ _ fun B _ x hx => ?_
  obtain ⟨β, hβ⟩ : ∃ β : DualNumber K →+* B, x ≫ (fst (epsR K) A).left = spMap β :=
    ⟨(Spec.preimage (x ≫ (fst (epsR K) A).left)).hom, (Spec.map_preimage _).symm⟩
  letI : Algebra K B := (β.comp (algebraMap K (DualNumber K))).toAlgebra
  set e : B := β DualNumber.eps with he_def
  have he : e * e = 0 := by rw [he_def, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  let βa : DualNumber K →ₐ[K] B := { β with commutes' := fun _ => rfl }
  have hβe : βa = GlobalTheory.SqZero.epsTo K e he := DualNumber.algHom_ext (by simp [βa, e])
  have hxw : x ≫ (epsR K ⊗ A).hom = (Chart.sp (R₀ := K) B).hom := by
    rw [← Over.w (fst (epsR K) A), ← Category.assoc, hβ]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl
  let xt : Chart.sp (R₀ := K) B ⟶ epsR K ⊗ A := Over.homMk x hxw
  let z : Chart.sp (R₀ := K) B ⟶ A := xt ≫ snd (epsR K) A
  have hfst : xt ≫ fst (epsR K) A = Chart.spMap (GlobalTheory.SqZero.epsTo K e he) := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Chart.spMap_left, ← hβe]
    exact hβ
  have hmu : x ≫ ((fst (epsR K) A ≫ u) * snd (epsR K) A).left =
      ((Chart.spMap (GlobalTheory.SqZero.epsTo K e he) ≫ u : Chart.sp (R₀ := K) B ⟶ A) * z).left := by
    rw [← hfst, Category.assoc, ← MonObj.comp_mul]
    rfl
  have hz : ⊤ ≤ z.left ⁻¹ᵁ W := fun p hp => hx hp
  obtain ⟨-, H⟩ := GlobalTheory.Heat.DlogIndep.valR_translate hu ht hd e he z W hz
  rw [GlobalTheory.LogKSBal.valR_pbT x _ hpre.ge hx, hmu, H, valR_add_of x hx, valR_mul_of x hx,
    GlobalTheory.LogKSBal.valR_pbT x _ le_rfl hx, GlobalTheory.LogKSBal.valR_pbT x _ le_rfl hx,
    GlobalTheory.LogKSBal.valR_constFn _ x hx hβ]
  rfl

end GlobalTheory.InvDerBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvariantFieldDualNumberOfIsInvariantTangentVeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInvariantField_dualNumber_of_isInvariant_tangentVector : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (v : TanM (𝟙 (Sp K)) A) (u : epsR K ⟶ A) (dd : Fld A.left), u.left = (tv v).left → IsTangent u → IsInv A v dd → GlobalTheory.KS.IsInvDer u dd := by
  first | exact @GlobalTheory.InvDerBridge.isInvDer_of_isInv | exact GlobalTheory.InvDerBridge.isInvDer_of_isInv | (intros; apply GlobalTheory.InvDerBridge.isInvDer_of_isInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixZeroDerivationEqZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSZeroDer

theorem isInvDer_of_isInv {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]
    {v : TanM (𝟙 (Sp K)) A} {u : epsR K ⟶ A} (hu : u.left = (tv v).left) (ht : IsTangent u)
    {dd : Fld A.left} (hd : IsInv A v dd) : GlobalTheory.KS.IsInvDer u dd :=
  GlobalTheory.T.isInvariantField_dualNumber_of_isInvariant_tangentVector K A v u dd hu ht hd

theorem pbT_id_le {X : Scheme.{0}} {O₀ O : X.Opens} (h : O ≤ O₀) (s : Γ(X, O₀)) : pbT (𝟙 X) s O = rsT s O := by
  rw [pbT, rsT, dite_eq_left (show O ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ O₀ from h), dite_eq_left h]
  rfl

theorem constFn_zero_fn {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (O : X.Opens) :
    constFn q O 0 = 0 := by
  rw [constFn, map_zero, map_zero]

theorem id_app_apply {X : Scheme.{0}} (O : X.Opens) (s : Γ(X, O)) : ((𝟙 X : X ⟶ X).app O).hom s = s := by
  simp only [Scheme.Hom.id_app]
  rfl

theorem rsT_mul_le {X : Scheme.{0}} {O₀ O : X.Opens} (h : O ≤ O₀) (s t : Γ(X, O₀)) : rsT (s * t) O = rsT s O * rsT t O := by
  rw [rsT, rsT, rsT, dite_eq_left h, dite_eq_left h, dite_eq_left h, map_mul]

theorem dlg_eq {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (L : LB A.left)
    (δ : Fld A.left) (hf : IsField ⊤ δ) (i i' : L.ι) (ψ : Γ(A.left, L.U i ⊓ L.U i'))
    (hψ : (L.g i i').val * ψ = δ (L.U i ⊓ L.U i') (L.g i i').val) (O : A.left.Opens) (hO : O ≤ L.U i ⊓ L.U i') :
    dlg A (𝟙 _) L δ i i' O = rsT ψ O := by
  rw [dlg, pbT_id_le hO, pbT_id_le hO]
  have e2 := congrArg (fun s => rsT s O) hψ
  have e3 : rsT (δ (L.U i ⊓ L.U i') (L.g i i').val) O = δ O (rsT (L.g i i').val O) := by
    rw [rsT, rsT, dite_eq_left hO, dite_eq_left hO]
    exact (hf.2.2 _ O hO le_top _).symm
  rw [rsT_mul_le hO, e3] at e2
  rw [← e2, mul_comm (rsT (L.g i i').val O), _root_.mul_assoc, ← rsT_mul_le hO, Units.mul_inv]
  have e4 : rsT (1 : Γ(A.left, L.U i ⊓ L.U i')) O = 1 := by rw [rsT, dite_eq_left hO, map_one]
  rw [e4, _root_.mul_one]

theorem main : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ M : Matrix (Fin n) (Fin n) K, KSRel P₀.A (𝟙 P₀.A.left) P₀.L dd (fun _ => 0) M → M = 0 := by
  intro K _ _ P₀ n v dd hdd M hM
  haveI : IsCommMonObj P₀.A := P₀.isAb.comm
  obtain ⟨u, hu, hul⟩ := GlobalTheory.Heat.DlogIndep.exists_isLieBasis v
  have hinv : ∀ a, GlobalTheory.KS.IsInvDer (u a) (dd a) := fun a => isInvDer_of_isInv (hul a) (hu.1 a) (hdd a)
  have hiso := GlobalTheory.SiegLower.lbIso_pull_id P₀.isLB
  obtain ⟨⟨φ, hφ⟩, -⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hu hinv _ (𝟙 _) P₀.L P₀.isLB hiso
  obtain ⟨J, W, j, d, hcov, hWj, hl, hdiff⟩ := hM
  have hcv : ∀ z : P₀.A.left, ∃ i, (𝟙 P₀.A.left : P₀.A.left ⟶ P₀.A.left) z ∈ W i := fun z => by
    have h2 : z ∈ ⨆ i, W i := by rw [hcov]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 h2
  have hpb : IsPullback (𝟙 P₀.A.left) P₀.A.hom P₀.A.hom (𝟙 (Sp K)) := IsPullback.of_horiz_isIso ⟨by simp⟩
  refine GlobalTheory.KSUniq.theta_eq_fibre P₀ u hu dd hinv P₀.A.hom (𝟙 _) (𝟙 _) hpb (U := ⊤) (isAffineOpen_top _) P₀.L
    P₀.isLB hiso (fun _ => 0) M 0 W W j j d (fun _ _ _ => 0) (fun _ => le_top) (fun _ => le_top) hWj hWj hcv hcv
    (fun i => (hl i).1) (fun _ => isField_zero _) ?_ ?_ φ hφ ?_ ?_
  · intro i h r
    have e : r = (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r) := by
      simp
    have := (hl i).2 (W i) le_rfl ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r)
    show _ = (P₀.A.hom.appLE ⊤ (W i) h).hom 0
    rw [map_zero]
    conv_lhs => rw [e]
    exact this.trans (by simp [constFn])
  · intro k h r
    show (0 : Γ(P₀.A.left, W k)) = (P₀.A.hom.appLE ⊤ (W k) h).hom 0
    rw [map_zero]
  · intro i i' O hO f
    rw [id_app_apply, id_app_apply, hdiff i i' O hO f]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have p : pbT (𝟙 P₀.A.left) (P₀.L.g (j i) (j i')).val
        ((𝟙 P₀.A.left) ⁻¹ᵁ P₀.L.U (j i) ⊓ (𝟙 P₀.A.left) ⁻¹ᵁ P₀.L.U (j i')) = (P₀.L.g (j i) (j i')).val :=
      GlobalTheory.Heat.DlogIndep.pbT_id (X := P₀.A.left) (P₀.L.U (j i) ⊓ P₀.L.U (j i')) _
    have hψ := hφ b (j i) (j i')
    rw [p] at hψ
    rw [dlg_eq P₀.L (dd b) (hdd b).1 (j i) (j i') (φ b (j i) (j i')) hψ O
      (fun z hz => ⟨hWj i (hO hz).1, hWj i' (hO hz).2⟩)]
    rfl
  · intro k k' O hO f
    rw [id_app_apply]
    simp only [Matrix.zero_apply, constFn_zero_fn, zero_mul, Finset.sum_const_zero, sub_self]
    rfl

end GlobalTheory.KSZeroDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixZeroDerivationEqZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_matrix_zero_derivation_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ M : Matrix (Fin n) (Fin n) K, KSRel P₀.A (𝟙 P₀.A.left) P₀.L dd (fun _ => 0) M → M = 0 := by
  first | exact @GlobalTheory.KSZeroDer.main | exact GlobalTheory.KSZeroDer.main | (intros; apply GlobalTheory.KSZeroDer.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstOfRegularOnCoverAbelianVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstOfRegularOnCoverAbelianVariety
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.HeatConst

theorem const_of_regular_on_cover : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (I : Type) (W : I → P₀.A.left.Opens), ⨆ i, W i = ⊤ → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ W i) → ∀ y : F, (∀ i, ∃ h : Γ(P₀.A.left, W i), valR ξ (W i) h = y) → ∃ r : K, ψ r = y := by
  intro K _ P₀ F _ ψ ξ hξ hinj I W hW hWξ y hy
  choose h hh using hy
  have hagree : ∀ i j, rsT (h i) (W i ⊓ W j) = rsT (h j) (W i ⊓ W j) := by
    intro i j
    have hij : ⊤ ≤ ξ ⁻¹ᵁ (W i ⊓ W j) := fun p hp => ⟨hWξ i hp, hWξ j hp⟩
    refine sub_eq_zero.1 (hinj _ _ hij ?_)
    rw [GlobalTheory.LogKSBal.valR_eq ξ hij, map_sub, ← GlobalTheory.LogKSBal.valR_eq ξ hij, ← GlobalTheory.LogKSBal.valR_eq ξ hij,
      GlobalTheory.LogKSBal.valR_rsT ξ inf_le_left hij, GlobalTheory.LogKSBal.valR_rsT ξ inf_le_right hij, hh, hh, sub_self]
  obtain ⟨t, ht⟩ := GlobalTheory.KS.exists_rsT_eq W (O := ⊤) (fun _ => le_top) hW.ge h hagree
  obtain ⟨u, hu⟩ := (GlobalTheory.globalFns_holds (Sp K) P₀.A P₀.isAb).2 t
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom u, ?_⟩
  obtain ⟨i, -⟩ : ∃ i, ξ.base (IsLocalRing.closedPoint F) ∈ W i := by
    have : ξ.base (IsLocalRing.closedPoint F) ∈ (⨆ i, W i) := by rw [hW]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  have htop : ⊤ ≤ ξ ⁻¹ᵁ (⊤ : P₀.A.left.Opens) := fun _ _ => trivial
  have hc : t = constFn P₀.A.hom ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom u) := by
    rw [← hu]
    simp [constFn, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rw [← hh i, ← ht i, GlobalTheory.LogKSBal.valR_rsT ξ le_top (hWξ i), hc, GlobalTheory.LogKSBal.valR_constFn P₀.A.hom ξ htop hξ]

end GlobalTheory.HeatConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstOfRegularOnCoverAbelianVarietyStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_of_regular_on_cover_abelianVariety : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (I : Type) (W : I → P₀.A.left.Opens), ⨆ i, W i = ⊤ → (∀ i, ⊤ ≤ ξ ⁻¹ᵁ W i) → ∀ y : F, (∀ i, ∃ h : Γ(P₀.A.left, W i), valR ξ (W i) h = y) → ∃ r : K, ψ r = y := by
  first | exact @GlobalTheory.HeatConst.const_of_regular_on_cover | exact GlobalTheory.HeatConst.const_of_regular_on_cover | (intros; apply GlobalTheory.HeatConst.const_of_regular_on_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverByPolarizationPowerSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverByPolarizationPowerSections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleCover

variable {X : Scheme.{0}} (U : X.Opens) (hU : U = ⊤)

noncomputable def backTop : X ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (𝟙 X) (by
    rw [Scheme.Opens.range_ι, hU]; exact Set.subset_univ _)

theorem backTop_ι : backTop U hU ≫ U.ι = 𝟙 X := IsOpenImmersion.lift_fac _ _ _

theorem backTop_apply (y : X) : U.ι (backTop U hU y) = y :=
  congrArg (fun g : X ⟶ X => g y) (backTop_ι U hU)

instance : IsIso (backTop U hU) :=
  ⟨⟨U.ι, backTop_ι U hU, by rw [← cancel_mono U.ι, Category.assoc, backTop_ι, Category.comp_id, Category.id_comp]⟩⟩

end GlobalTheory.AmpleCover

namespace GlobalTheory.AmpleCover

variable {S : Scheme.{0}} (A : Over S) (L : LB A.left) (N : ℕ)

theorem gm_pow_congr {y : A.left} {r : A.left ⟶ A.left} (hr : r = 𝟙 A.left) (a b : L.ι) :
    gm (𝟙 A.left) y (L.U a ⊓ L.U b) (L.g a b) ^ N = gm r y (L.U a ⊓ L.U b) (L.g a b) ^ N := by
  subst hr; rfl

def chartPullPowTop :
    ChartPull (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 A.left) fun _ => (N : ℤ)) (powOver A L ⊤ N)
      (backTop (A.hom ⁻¹ᵁ ⊤) (by simp)) where
  idx j := fun _ => (j : Fin 1 → L.ι) 0
  le j y hy := Set.mem_iInter.2 fun _ => by
    have e := backTop_apply (A.hom ⁻¹ᵁ ⊤) (by simp) y
    have hy' : y ∈ L.U ((j : Fin 1 → L.ι) 0) := Set.mem_iInter.1 hy 0
    show (A.hom ⁻¹ᵁ ⊤).ι (backTop (A.hom ⁻¹ᵁ ⊤) (by simp) y) ∈ L.U ((j : Fin 1 → L.ι) 0)
    rw [e]; exact hy'
  g y j j' hj hj' := by
    have hb : ∀ (i : Fin 1 → L.ι), y ∈ L.U (i 0) →
        backTop (A.hom ⁻¹ᵁ ⊤) (by simp) y ∈ (powOver A L ⊤ N).U (fun _ => i 0) := fun i hi =>
      Set.mem_iInter.2 fun _ => by
        have e := backTop_apply (A.hom ⁻¹ᵁ ⊤) (by simp) y
        show (A.hom ⁻¹ᵁ ⊤).ι (backTop (A.hom ⁻¹ᵁ ⊤) (by simp) y) ∈ L.U (i 0)
        rw [e]; exact hi
    refine (gm_linComb L _ _ (𝟙 _) y j j' hj hj').trans (Eq.trans ?_
      (gm_linComb L (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ ⊤).ι) (fun _ => 1) _ y _ _
        (hb j (Set.mem_iInter.1 hj 0)) (hb j' (Set.mem_iInter.1 hj' 0))).symm)
    rw [Fintype.prod_unique]
    simp only [backTop_ι, Category.id_comp, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      zpow_natCast]
    exact gm_pow_congr A L N (backTop_ι _ _) _ _

end GlobalTheory.AmpleCover


open GlobalTheory.AmpleCover in
theorem GlobalTheory.AmpleCover.exists_affine_cover_secM : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∃ (k : ℕ) (I : Type) (s : I → SecM (𝟙 P₀.A.left) P₀.L k), 1 ≤ k ∧ ⨆ i, Out.nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧ ((Out.nonzeroLocus (s i) : P₀.A.left.Opens) : Set P₀.A.left).Nonempty := by
  intro K _ P₀
  obtain ⟨N, hN, M, s, hcov, hs⟩ := P₀.ample ⊤ (isAffineOpen_top _)
  have hT : P₀.A.hom ⁻¹ᵁ ⊤ = ⊤ := by simp
  let a := chartPullPowTop P₀.A P₀.L N
  have loc : ∀ i, Out.nonzeroLocus (GlobalTheory.chartSec a (s i)) = backTop _ hT ⁻¹ᵁ Out.nonzeroLocus (s i) := fun i =>
    GlobalTheory.nonzeroLocus_chartSec a (s i) fun y j hj => by
      have h0 : (P₀.A.hom ⁻¹ᵁ ⊤).ι (backTop _ hT y) ∈ P₀.L.U ((j : Fin N → P₀.L.ι) ⟨0, hN⟩) :=
        Set.mem_iInter.1 hj ⟨0, hN⟩
      rw [backTop_apply] at h0
      exact ⟨fun _ => (j : Fin N → P₀.L.ι) ⟨0, hN⟩, Set.mem_iInter.2 fun _ => h0⟩
  refine ⟨N, {i : Fin (M + 1) // ((Out.nonzeroLocus (GlobalTheory.chartSec a (s i)) : P₀.A.left.Opens) : Set P₀.A.left).Nonempty},
    fun i => GlobalTheory.chartSec a (s i.1), hN, ?_, fun i => ⟨?_, i.2⟩⟩
  · refine eq_top_iff.2 fun y _ => ?_
    have hy : backTop _ hT y ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    have hy' : y ∈ Out.nonzeroLocus (GlobalTheory.chartSec a (s i)) := by rw [loc]; exact hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, y, hy'⟩, hy'⟩
  · show IsAffineOpen (Out.nonzeroLocus (GlobalTheory.chartSec a (s i.1)))
    rw [loc]
    exact (hs i.1).1.preimage _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverByPolarizationPowerSectionsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_cover_by_polarization_power_sections : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∃ (k : ℕ) (I : Type) (s : I → SecM (𝟙 P₀.A.left) P₀.L k), 1 ≤ k ∧ ⨆ i, Out.nonzeroLocus (s i) = ⊤ ∧ ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧ ((Out.nonzeroLocus (s i) : P₀.A.left.Opens) : Set P₀.A.left).Nonempty := by
  first | exact @GlobalTheory.AmpleCover.exists_affine_cover_secM | exact GlobalTheory.AmpleCover.exists_affine_cover_secM | (intros; apply GlobalTheory.AmpleCover.exists_affine_cover_secM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalSecondOrderSymbolVanishesOfPolarisation
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Heat.gc_symbol_vanishes : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), Λᵀ = Λ → (∀ r, δ₀ (ψ r) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → Λ = 0 := by
  intro K _ _ P₀ n v dd hv F _ ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ Λ hΛ hδ₀ hbr
  obtain ⟨k, I, s, hk, hcov, hai⟩ := GlobalTheory.T.exists_affine_cover_by_polarization_power_sections K P₀
  have haff : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) := fun i => (hai i).1
  have hne := fun i => (hai i).2
  have hloc : ∀ i, ⊤ ≤ ξ ⁻¹ᵁ Out.nonzeroLocus (s i) := fun i =>
    GlobalTheory.T.top_le_preimage_nonempty_open_of_pointValue_injective K P₀ F ψ ξ hξ hval _ (hne i)
  have hL := fun i => GlobalTheory.T.heat_symbol_regular_on_section_nonvanishing_locus K P₀ n v dd hv F ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ Λ hbr k hk (s i) (hloc i)
  have hreg : ∀ i a e, ∃ h : Γ(P₀.A.left, Out.nonzeroLocus (s i)), valR ξ _ h = Λ a e := fun i =>
    GlobalTheory.T.symbol_entries_regular_affineOpen K P₀ n v dd hv F ψ ξ hξ hval δ hδ Λ _ (haff i) (hloc i) (hL i).1
  have hc : ∀ a e, ∃ r : K, ψ r = Λ a e := fun a e =>
    GlobalTheory.T.exists_const_of_regular_on_cover_abelianVariety K P₀ F ψ ξ hξ hval I (fun i => Out.nonzeroLocus (s i)) hcov hloc (Λ a e) (fun i => hreg i a e)
  choose lam hlam using hc
  have hsym : lamᵀ = lam := by
    ext a e
    apply ψ.injective
    show ψ (lam e a) = ψ (lam a e)
    rw [hlam, hlam]
    exact congrFun (congrFun hΛ a) e
  have hks := GlobalTheory.T.kodairaSpencer_relation_zero_derivation_of_shifted K P₀ n v dd hv F ψ ξ hξ hval δ hδ j₀ hj₀ δ₀ lam hsym hδ₀ k hk I s hcov haff hloc
    (fun i f => by
      obtain ⟨f', hf'⟩ := (hL i).2 f
      exact ⟨f', by rw [hf']; simp only [hlam]⟩)
  have h0 := GlobalTheory.T.kodairaSpencer_matrix_zero_derivation_eq_zero K P₀ n v dd hv lam hks
  ext a e
  rw [← hlam a e, h0]
  simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalSecondOrderSymbolVanishesOfPolarisationStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.verticalSecondOrderSymbol_vanishes_of_polarisation : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), Λᵀ = Λ → (∀ r, δ₀ (ψ r) = 0) → (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → Λ = 0 := by
  first | exact @GlobalTheory.Heat.gc_symbol_vanishes | exact GlobalTheory.Heat.gc_symbol_vanishes | (intros; apply GlobalTheory.Heat.gc_symbol_vanishes <;> assumption)
end
