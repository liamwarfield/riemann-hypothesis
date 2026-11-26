module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddExtension
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteValues
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology

theorem exists_lift_valR {O T : Type} [CommRing O] [IsLocalRing O] [CommRing T] [IsLocalRing T] (π : O →+* T)
    [IsLocalHom π] {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i] (c : Sp O ⟶ X) (ce : Sp T ⟶ Y)
    (h : ce ≫ i = spMap π ≫ c) (U : Y.Opens) (hU : ⊤ ≤ ce ⁻¹ᵁ U) (f : Γ(Y, U)) :
    ∃ (U' : X.Opens) (f' : Γ(X, U')), ⊤ ≤ c ⁻¹ᵁ U' ∧ π (valR c U' f') = valR ce U f := by
  have hy : ce (cpt T) ∈ U := hU trivial
  obtain ⟨a, ha⟩ := i.stalkMap_surjective (ce (cpt T)) ((Y.presheaf.germ U _ hy).hom f)
  obtain ⟨U', hU', f', rfl⟩ := X.presheaf.germ_exist a
  have hcl : spMap π (cpt T) = cpt O := IsLocalRing.comap_closedPoint π
  have h1 : (spMap π ≫ c) (cpt T) ∈ U' := by rw [← h]; exact hU'
  have h2 : ⊤ ≤ c ⁻¹ᵁ U' := (top_le_iff_cpt c U').2 (by rw [← hcl]; exact h1)
  refine ⟨U', f', h2, toStkA_injective ?_⟩
  rw [toStkA_map_valR π c U' _ h2, toStkA_valR_eq_gs ce U _ hU, ← h, ← gs_pull ce i _ U' hU',
    gs_eq ce _ U hy, gs_eq ce _ (i ⁻¹ᵁ U') hU', ← Scheme.Hom.germ_stalkMap_apply ce U _ hy,
    ← Scheme.Hom.germ_stalkMap_apply ce (i ⁻¹ᵁ U') _ hU', ← ha]
  exact congrArg _ (Scheme.Hom.germ_stalkMap_apply i U' _ hU' f').symm

variable {p : ℕ} [Fact p.Prime]

theorem exists_finite_values {V : Type} [CommRing V] (j : V →+* OO p) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K₀] (hj : ∀ x, (j x : PadicAlgCl p) ∈ K₀) {X : Scheme.{0}} (s : X ⟶ Sp V)
    [LocallyOfFiniteType s] (c : Sp (OO p) ⟶ X) (hc : c ≫ s = spMap j) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
      ∀ (U : X.Opens), ⊤ ≤ c ⁻¹ᵁ U → ∀ f, ((valR c U f : OO p) : PadicAlgCl p) ∈ K := by
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (x := c (cpt _)) (U := ⊤) trivial
  have hWt : ⊤ ≤ c ⁻¹ᵁ W := (top_le_iff_cpt c W).2 hyW
  have hft : (s.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  letI := (s.appLE ⊤ W le_top).hom.toAlgebra
  obtain ⟨t, ht⟩ := hft.1
  let φ : Γ(X, W) →+* PadicAlgCl p := (OO p).subtype.comp (CrdCalc.valHom c W hWt)
  have hφ : ∀ f, φ f = ((valR c W f : OO p) : PadicAlgCl p) := fun f => by
    rw [CrdCalc.valR_eq c W hWt]; rfl
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (φ '' (t : Set Γ(X, W)))) :=
    haveI : Finite (φ '' (t : Set Γ(X, W))) := ((t.finite_toSet).image φ).to_subtype
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨K₀ ⊔ IntermediateField.adjoin ℚ_[p] (φ '' (t : Set Γ(X, W))), inferInstance, ?_⟩
  set K := K₀ ⊔ IntermediateField.adjoin ℚ_[p] (φ '' (t : Set Γ(X, W)))
  have hall : ∀ f, φ f ∈ K := fun f => by
    have hf : f ∈ Algebra.adjoin Γ(Sp V, ⊤) (t : Set Γ(X, W)) := ht ▸ trivial
    induction hf using Algebra.adjoin_induction with
    | mem x hx => exact (le_sup_right : _ ≤ K) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
    | algebraMap r =>
      refine (le_sup_left : _ ≤ K) ?_
      have e : (s.appLE ⊤ W le_top ≫ c.appLE W ⊤ hWt ≫ (Scheme.ΓSpecIso (CommRingCat.of (OO p))).hom) =
          (Scheme.ΓSpecIso (CommRingCat.of V)).hom ≫ CommRingCat.ofHom j := by
        rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality]
        refine congrArg (· ≫ _) ((Scheme.Hom.appLE_comp_appLE c s ⊤ W ⊤ le_top hWt).trans ?_)
        simp only [hc]
        rfl
      have e' : CrdCalc.valHom c W hWt (algebraMap Γ(Sp V, ⊤) Γ(X, W) r) =
        j ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r) := congrArg (fun q => q.hom r) e
      have := hj ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom r)
      rw [← e'] at this
      exact this
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  intro U hU f
  obtain ⟨g, hgU, hyg⟩ := hW.exists_basicOpen_le ⟨c (cpt _), hU trivial⟩ hyW
  have hgt : ⊤ ≤ c ⁻¹ᵁ X.basicOpen g := (top_le_iff_cpt c _).2 hyg
  have := hW.isLocalization_basicOpen g
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (Submonoid.powers g) (resG X hgU f)
  have e2 := congrArg (valR c (X.basicOpen g)) e
  rw [CrdCalc.valR_mul c _ hgt, CrdCalc.valR_res c hgU hgt] at e2
  have r1 : ∀ b : Γ(X, W), valR c (X.basicOpen g) (algebraMap Γ(X, W) Γ(X, X.basicOpen g) b) = valR c W b :=
    fun b => CrdCalc.valR_res c (X.basicOpen_le g) hgt b
  rw [r1, r1] at e2
  have hu : IsUnit (valR c W g) := (CrdCalc.isUnit_valR_iff c W hWt g).2 hgt
  have hg0 : φ (g ^ n) ≠ 0 := by
    rw [map_pow, hφ]
    exact pow_ne_zero _ (hu.map (OO p).subtype).ne_zero
  have e3 : ((valR c U f : OO p) : PadicAlgCl p) = φ a / φ (g ^ n) := by
    rw [eq_div_iff hg0, hφ, hφ]
    exact congrArg Subtype.val e2
  rw [e3]
  exact div_mem (hall _) (hall _)

theorem exists_tendsto (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] {r : ℝ}
    (hr : r < 1) (ω : ℕ → PadicAlgCl p) (hK : ∀ e, ω e ∈ K) (h : ∀ e, ‖ω (e + 1) - ω e‖ ≤ r ^ (e + 1)) :
    ∃ a, Tendsto ω atTop (𝓝 a) := by
  have hc : CauchySeq ω := cauchySeq_of_le_geometric r r hr fun e => by
    rw [dist_comm, dist_eq_norm, ← pow_succ']; exact h e
  haveI : FiniteDimensional ℚ_[p] K.toSubmodule := inferInstanceAs (FiniteDimensional ℚ_[p] K)
  obtain ⟨a, -, ha⟩ := cauchySeq_tendsto_of_isComplete K.toSubmodule.complete_of_finiteDimensional hK hc
  exact ⟨a, ha⟩

theorem hasSum_of_levels {Ix : Type} {r : ℝ} (hr₀ : 0 ≤ r) (hr : r < 1) (x : Ix → PadicAlgCl p)
    (s : ℕ → PadicAlgCl p) (a : PadicAlgCl p) (hs : Tendsto s atTop (𝓝 a))
    (h : ∀ e, ∃ S : Finset Ix, ∀ T, S ⊆ T → ‖s e - ∑ i ∈ T, x i‖ ≤ r ^ (e + 1)) : HasSum x a := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have h1 := (Metric.tendsto_nhds.1 hs) (ε / 2) (half_pos hε)
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr).comp (tendsto_add_atTop_nat 1)
  have h3 := h2.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨e, he1, he2⟩ := (h1.and h3).exists
  obtain ⟨S, hS⟩ := h e
  refine ⟨S, fun T hT => ?_⟩
  have := hS T hT
  rw [← dist_eq_norm, dist_comm] at this
  have h4 := dist_triangle (∑ i ∈ T, x i) (s e) a
  simp only [Function.comp] at he2
  linarith

end GlobalTheory.ZH.IntegralSum
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology ReciprocityTheory.ChartRestriction.G.DVR
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}
variable {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem exists_lev_norm : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ e, ∀ x ∈ u.lev e, ‖(x : PadicAlgCl p)‖ ≤ r ^ (e + 1) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  refine ⟨‖(u.j π : PadicAlgCl p)‖, norm_nonneg _, ?_, fun e x hx => ?_⟩
  · by_contra h
    have h0 : algebraMap u.V (FractionRing u.V) π ≠ 0 := fun h₀ =>
      hπ.ne_zero (IsFractionRing.injective u.V (FractionRing u.V) (h₀.trans (map_zero _).symm))
    obtain ⟨z, hz⟩ := (u.norm_le (algebraMap u.V _ π)⁻¹).1 (by
      rw [map_inv₀, norm_inv]; exact inv_le_one_of_one_le₀ (not_lt.1 h))
    refine hπ.not_isUnit (IsUnit.of_mul_eq_one z (IsFractionRing.injective u.V (FractionRing u.V) ?_))
    rw [map_mul, hz, map_one, mul_inv_cancel₀ h0]
  · rw [ThetaSys.Real.UTest.lev, hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [map_pow]
    show ‖(a : PadicAlgCl p) * (u.j π : PadicAlgCl p) ^ (e + 1)‖ ≤ _
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) ((mem_OO_iff _).1 a.2)

theorem lev_ne_top (e : ℕ) : u.lev e ≠ ⊤ := fun h => by
  obtain ⟨r, h0, h1, h2⟩ := exists_lev_norm u
  have := h2 e 1 (h ▸ trivial)
  have h3 : r ^ (e + 1) < 1 := pow_lt_one₀ h0 h1 (Nat.succ_ne_zero e)
  simp only [OneMemClass.coe_one, norm_one] at this
  linarith

instance nontrivial_lev (e : ℕ) : Nontrivial (OO p ⧸ u.lev e) := Ideal.Quotient.nontrivial_iff.2 (lev_ne_top u e)

instance isLocalRing_lev (e : ℕ) : IsLocalRing (OO p ⧸ u.lev e) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

instance isLocalHom_lev (e : ℕ) : IsLocalHom (Ideal.Quotient.mk (u.lev e)) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

theorem norm_eq_one_of_isUnit {e : ℕ} {x : OO p} (h : IsUnit (Ideal.Quotient.mk (u.lev e) x)) :
    ‖(x : PadicAlgCl p)‖ = 1 := by
  obtain ⟨y, hy⟩ := (isUnit_of_map_unit _ x h).exists_right_inv
  have h1 : ‖(x : PadicAlgCl p)‖ * ‖(y : PadicAlgCl p)‖ = 1 := by
    rw [← norm_mul, show (x : PadicAlgCl p) * y = 1 from congrArg Subtype.val hy, norm_one]
  have hx := (mem_OO_iff _).1 x.2
  have hy := (mem_OO_iff _).1 y.2
  have := norm_nonneg (x : PadicAlgCl p)
  nlinarith

theorem mk_cpt (e : ℕ) : spMap (Ideal.Quotient.mk (u.lev e)) (cpt _) = cpt (OO p) :=
  IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (u.lev e))

theorem exists_level_point (c : Sp (OO p) ⟶ u.G.left) (hc : c ≫ u.G.hom = spMap u.j) (e : ℕ) :
    ∃ ce : Sp (OO p ⧸ u.lev e) ⟶ (thickObj u.V (IsLocalRing.maximalIdeal u.V) e u.G).left,
      ce ≫ (fstG (IsLocalRing.maximalIdeal u.V) e u.G).left = spMap (Ideal.Quotient.mk (u.lev e)) ≫ c := by
  refine ⟨pullback.lift (spMap (Ideal.Quotient.mk (u.lev e)) ≫ c)
    (spMap (Ideal.quotientMap (u.lev e) u.j Ideal.le_comap_map)) ?_, pullback.lift_fst _ _ _⟩
  rw [Category.assoc, hc]
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem lev_succ_le (e : ℕ) : u.lev (e + 1) ≤ u.lev e :=
  Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))

section
variable (c : Sp (OO p) ⟶ u.G.left) (b₀ : Sp (OO p) ⟶ u.D.toPre.P.A.left)
  (ce : ∀ e, Sp (OO p ⧸ u.lev e) ⟶ (thickObj u.V (IsLocalRing.maximalIdeal u.V) e u.G).left)
  (hce : ∀ e, ce e ≫ fGl (IsLocalRing.maximalIdeal u.V) u.G e = spMap (Ideal.Quotient.mk (u.lev e)) ≫ c)
  (hbe : ∀ e, ce e ≫ pGl u.U.toUnifPre e = spMap (Ideal.Quotient.mk (u.lev e)) ≫ b₀)
  {jL : u.U.LG.L.ι} {jM : u.D.toPre.P.L.ι} (hL : ⊤ ≤ c ⁻¹ᵁ u.U.LG.L.U jL) (hM : ⊤ ≤ b₀ ⁻¹ᵁ u.D.toPre.P.L.U jM)
include hce hbe hL hM

theorem top_le_wchart (e : ℕ) {T : Type} [CommRing T] (r : Sp T ⟶ Sp (OO p ⧸ u.lev e)) :
    ⊤ ≤ (r ≫ ce e) ⁻¹ᵁ ((u.D.toPre.P.L.pull (u.U.gt e).pG.left).U (fun _ => jM) ⊓
      (u.U.LG.L.pull (fstG (IsLocalRing.maximalIdeal u.V) e u.G).left).U (fun _ => jL)) := fun z _ =>
  ⟨mem_pull.2 ((congrArg (fun q => q (r z) ∈ u.D.toPre.P.L.U jM) (hbe e)).mpr (top_le_comp hM _ trivial)),
    mem_pull.2 ((congrArg (fun q => q (r z) ∈ u.U.LG.L.U jL) (hce e)).mpr (top_le_comp hL _ trivial))⟩

theorem top_le_wchart' (e : ℕ) :
    ⊤ ≤ (ce e) ⁻¹ᵁ ((u.D.toPre.P.L.pull (u.U.gt e).pG.left).U (fun _ => jM) ⊓
      (u.U.LG.L.pull (fstG (IsLocalRing.maximalIdeal u.V) e u.G).left).U (fun _ => jL)) :=
  top_le_wchart u c b₀ ce hce hbe hL hM e (𝟙 _)

theorem factor_wVal (e : ℕ) :
    Ideal.Quotient.factor (lev_succ_le u e) (wVal u.U.toUnifPre (e + 1) (ce (e + 1)) jL jM) =
      wVal u.U.toUnifPre e (ce e) jL jM := by
  have toStkA_valR {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X)
      (U : X.Opens) (z : Sp A) (ht : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
      toStkA z (valR x U a.val) = (gm x z U a).val := by
    have hz : x z ∈ U := ht (show z ∈ (⊤ : (Sp A).Opens) from trivial)
    have e1 : ∀ c, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c) = c :=
      fun c => congrArg (fun f => CommRingCat.Hom.hom f c) (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of A)))
    rw [valR, dif_pos ht, gm, dif_pos hz]
    show ((Sp A).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ ht).hom a.val))) =
      ((Sp A).presheaf.germ (x ⁻¹ᵁ U) z hz).hom ((x.app U).hom a.val)
    rw [e1]
    exact TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE ht) z trivial ((x.app U).hom a.val)
  have := fstG_mono (I := IsLocalRing.maximalIdeal u.V) (G := u.G) (e + 1)
  have ht := top_le_wchart' u c b₀ ce hce hbe hL hM e
  have e₁ : spMap (Ideal.Quotient.factor (lev_succ_le u e)) ≫ ce (e + 1) =
      ce e ≫ thickMap u.V (IsLocalRing.maximalIdeal u.V) e u.G := by
    rw [← cancel_mono (fstG (IsLocalRing.maximalIdeal u.V) (e + 1) u.G).left, Category.assoc, Category.assoc]
    refine (congrArg (_ ≫ ·) (hce (e + 1))).trans (Eq.trans ?_ ((hce e).symm.trans
      (congrArg (_ ≫ ·) (thickMap_comp_fGl _ e u.G).symm)))
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]
  have e₂ : Ideal.Quotient.factor (lev_succ_le u e) (wVal u.U.toUnifPre (e + 1) (ce (e + 1)) jL jM) =
      wVal u.U.toUnifPre (e + 1) (spMap (Ideal.Quotient.factor (lev_succ_le u e)) ≫ ce (e + 1)) jL jM :=
    (valR_spMap _ _ _ (top_le_wchart' u c b₀ ce hce hbe hL hM (e + 1)) _).symm
  apply toStkA_injective
  rw [e₂]
  refine (toStkA_valR _ _ _ (top_le_wchart u c b₀ ce hce hbe hL hM (e + 1) _) _).trans
    (Eq.trans ?_ (toStkA_valR _ _ _ ht _).symm)
  have h := wv_comp_thickMap (U := u.U.toUnifPre) e (ce e) (cpt _) jM jL (mem_pull.1 (ht trivial).1) (mem_pull.1 (ht trivial).2)
  rw [← e₁] at h
  exact congrArg Units.val h

theorem exists_omega [ArithBase o Ω] (hc : c ≫ u.G.hom = spMap u.j) : ∃ (ω : PadicAlgCl p) (ωe : ℕ → OO p), ω ≠ 0 ∧
    Tendsto (fun e => (ωe e : PadicAlgCl p)) atTop (𝓝 ω) ∧
    ∀ e, Ideal.Quotient.mk (u.lev e) (ωe e) = wVal u.U.toUnifPre e (ce e) jL jM := by
  obtain ⟨-, -, -, K₀, hK₀, hK₀'⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  have := u.U.smooth
  obtain ⟨K, hK, hval⟩ := exists_finite_values u.j K₀ (fun x => by
    show _ ∈ (K₀ : Set (PadicAlgCl p))
    rw [hK₀']; exact ⟨_, rfl⟩) u.G.hom c hc
  have hcl : ∀ e, IsClosedImmersion (fGl (IsLocalRing.maximalIdeal u.V) u.G e) := fun e =>
    haveI : IsClosedImmersion (thick u.V (IsLocalRing.maximalIdeal u.V) e) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    inferInstanceAs (IsClosedImmersion (pullback.fst u.G.hom (thick u.V (IsLocalRing.maximalIdeal u.V) e)))
  choose U' f' hU' hf' using fun e => exists_lift_valR (Ideal.Quotient.mk (u.lev e)) _ c (ce e) (hce e) _
    (top_le_wchart' u c b₀ ce hce hbe hL hM e) ((u.U.w e).s (fun _ => jM, fun _ => jL)).val
  have hw : ∀ e, Ideal.Quotient.mk (u.lev e) (valR c (U' e) (f' e)) = wVal u.U.toUnifPre e (ce e) jL jM := hf'
  obtain ⟨r, h0, h1, h2⟩ := exists_lev_norm u
  obtain ⟨ω, hω⟩ := exists_tendsto K h1 (fun e => (valR c (U' e) (f' e) : OO p)) (fun e => hval _ (hU' e) _)
    fun e => h2 e (valR c (U' (e + 1)) (f' (e + 1)) - valR c (U' e) (f' e)) (by
      rw [← Ideal.Quotient.eq, hw e, ← factor_wVal u c b₀ ce hce hbe hL hM e, ← hw (e + 1),
        Ideal.Quotient.factor_mk])
  refine ⟨ω, _, fun h => ?_, hω, hw⟩
  have h3 := hω.norm
  have h4 : ∀ e, ‖((valR c (U' e) (f' e) : OO p) : PadicAlgCl p)‖ = 1 := fun e =>
    norm_eq_one_of_isUnit u (e := e) (by
      rw [hw]; exact isUnit_valR _ _ (top_le_wchart' u c b₀ ce hce hbe hL hM e) _)
  simp only [h4, h, norm_zero] at h3
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h3)

end

theorem comp_Oφ_id {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
    (x : T ⟶ D.P.A) (χ : D.X) (k : Fin 4) : x.left ≫ D.Oφ (𝟙 D.P.A) χ k = D.Oφ x χ k :=
  (WeightPf.Oφ_comp x (𝟙 _) χ k).trans (by rw [Category.comp_id])

theorem level_Oφ (b₀ : Sp (OO p) ⟶ u.D.toPre.P.A.left) {e : ℕ}
    (ce : Sp (OO p ⧸ u.lev e) ⟶ (thickObj u.V (IsLocalRing.maximalIdeal u.V) e u.G).left)
    (hbe : ce ≫ pGl u.U.toUnifPre e = spMap (Ideal.Quotient.mk (u.lev e)) ≫ b₀) (χ : u.D.toPre.X) (i : Fin 4) :
    ce ≫ Oφl u.U.toUnifPre e χ i = spMap (Ideal.Quotient.mk (u.lev e)) ≫ b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i := by
  rw [← Category.assoc, ← hbe, Category.assoc]
  exact congrArg (ce ≫ ·) (comp_Oφ_id u.D.toPre (u.U.gt e).pG χ i).symm

theorem hasSum_integral (c : Sp (OO p) ⟶ u.G.left) (b₀ : Sp (OO p) ⟶ u.D.toPre.P.A.left)
    (ce : ∀ e, Sp (OO p ⧸ u.lev e) ⟶ (thickObj u.V (IsLocalRing.maximalIdeal u.V) e u.G).left)
    (hce : ∀ e, ce e ≫ fGl (IsLocalRing.maximalIdeal u.V) u.G e = spMap (Ideal.Quotient.mk (u.lev e)) ≫ c)
    (hbe : ∀ e, ce e ≫ pGl u.U.toUnifPre e = spMap (Ideal.Quotient.mk (u.lev e)) ≫ b₀)
    {jL : u.U.LG.L.ι} (hL : ⊤ ≤ c ⁻¹ᵁ u.U.LG.L.U jL) (d : u.D.toPre.P.A.left → u.D.toPre.P.L.ι)
    (hd : ∀ y, y ∈ u.D.toPre.P.L.U (d y)) (x : u.D.toPre.X → OO p)
    (hx : ∀ e χ, Ideal.Quotient.mk (u.lev e) (x χ) = valR (ce e) _
      (((u.U.gt e).t χ).s (fun i => d ((b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (cpt _)))).val)
    (ω : PadicAlgCl p) (ωe : ℕ → OO p) (hω : Tendsto (fun e => (ωe e : PadicAlgCl p)) atTop (𝓝 ω))
    (hωe : ∀ e, Ideal.Quotient.mk (u.lev e) (ωe e) = wVal u.U.toUnifPre e (ce e) jL (d (b₀ (cpt _))))
    {k : ℕ} (σ : H0 u.U.LG.L k) (f : ∀ α, u.D.toPre.SecB k α) (hE : ∀ e, u.U.toUnifPre.ExpandsAt e k σ f) :
    HasSum (fun α => ((valR b₀ _ ((f α).f (fun i => d ((b₀ ≫ u.D.toPre.famφB α i) (cpt _)))) * x α : OO p) :
      PadicAlgCl p)) (ω ^ k * (secVal u.U.toUnifPre σ c jL : OO p)) := by
  have toStkA_valR {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X)
      (U : X.Opens) (z : Sp A) (ht : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
      toStkA z (valR x U a.val) = (gm x z U a).val := by
    have hz : x z ∈ U := ht (show z ∈ (⊤ : (Sp A).Opens) from trivial)
    have e1 : ∀ c, (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c) = c :=
      fun c => congrArg (fun f => CommRingCat.Hom.hom f c) (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of A)))
    rw [valR, dif_pos ht, gm, dif_pos hz]
    show ((Sp A).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ ht).hom a.val))) =
      ((Sp A).presheaf.germ (x ⁻¹ᵁ U) z hz).hom ((x.app U).hom a.val)
    rw [e1]
    exact TopCat.Presheaf.germ_res_apply (Sp A).presheaf (homOfLE ht) z trivial ((x.app U).hom a.val)
  obtain ⟨r, h0, h1, h2⟩ := exists_lev_norm u
  refine hasSum_of_levels h0 h1 _ (fun e => ((ωe e ^ k * secVal u.U.toUnifPre σ c jL : OO p) : PadicAlgCl p)) _
    ((hω.pow k).mul_const _) fun e => ?_
  obtain ⟨F, hF⟩ := expandsAt_val u.U.toUnifPre e k σ f (hE e)
  refine ⟨F, fun T hT => ?_⟩
  let J : (Sp (OO p ⧸ u.lev e) ⟶ u.D.toPre.P.A.left) → u.D.toPre.P.L.ι := fun ψ => d (ψ (cpt _))
  have hJ : Good u.D.toPre.P.L (cpt (OO p ⧸ u.lev e)) J := fun ψ => hd _
  have eJ : ∀ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left, J (spMap (Ideal.Quotient.mk (u.lev e)) ≫ ψ) = d (ψ (cpt _)) :=
    fun ψ => congrArg (fun y => d (ψ y)) (mk_cpt u e)
  have hM : ⊤ ≤ b₀ ⁻¹ᵁ u.D.toPre.P.L.U (d (b₀ (cpt _))) := (top_le_iff_cpt _ _).2 (hd _)
  obtain ⟨H₀, H₁⟩ := hF _ (ce e) (cpt _) J hJ
  have H := H₁ jL ((congrArg (fun q => q (cpt _) ∈ u.U.LG.L.U jL) (hce e)).mpr (top_le_comp hL _ trivial))
  rw [hbe e] at H₀
  rw [hbe e, hce e, eJ, Finset.sum_subset hT (fun α _ hα => by rw [H₀ α hα, zero_mul])] at H
  rw [← AddSubmonoidClass.coe_finsetSum, ← AddSubgroupClass.coe_sub]
  refine h2 e _ (Ideal.Quotient.eq.1 (toStkA_injective ?_))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_pow, hωe, map_mul, map_pow, map_sum, map_sum]
  refine (congrArg₂ (· * ·) ?_ (toStkA_map_valR _ c _ _ (top_le_secChart hL) _)).trans
    (H.trans (Finset.sum_congr rfl fun α _ => ?_))
  · rw [Units.val_pow_eq_pow_val]
    exact congrArg (· ^ k) (toStkA_valR _ _ _ (top_le_wchart' u c b₀ ce hce hbe hL hM e) _)
  · rw [map_mul, map_mul, hx e α,
      sval_of (f α) _ _ J (fun i => d ((b₀ ≫ u.D.toPre.famφB α i) (cpt _))) (fun i => by rw [Category.assoc, eJ]),
      val_of (tG u.U.toUnifPre e α) _ _ J (fun i => d ((b₀ ≫ u.D.toPre.Oφ (𝟙 _) α i) (cpt _)))
        (fun i => by rw [level_Oφ u b₀ _ (hbe e), eJ])]
    refine (congrArg₂ (· * ·) (toStkA_map_valR _ b₀ _ _ ((top_le_iff_cpt _ _).2
      (Set.mem_iInter.2 fun i => hd ((b₀ ≫ u.D.toPre.famφB α i) (cpt _)))) _) (toStkA_valR _ _ _ ((top_le_iff_cpt _ _).2
      (Set.mem_iInter.2 fun i => ?_)) _)).symm
    have := hJ (ce e ≫ Oφl u.U.toUnifPre e α i)
    rw [show J (ce e ≫ Oφl u.U.toUnifPre e α i) = _ by rw [level_Oφ u b₀ _ (hbe e), eJ]] at this
    exact this

end GlobalTheory.ZH.IntegralSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsToStkAUnit
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT

theorem gtφ_eq {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (b : TF (R := R) F ⟶ D.P.A) (χ : D.X) (k : Fin 4) : DegPre.gtφ D F b χ k = b.left ≫ D.Oφ (𝟙 D.P.A) χ k := by
  rw [comp_Oφ_id]
  have h : padd D.P.A (DegPre.cF D F χ) b = padd D.P.A b (DegPre.cF D F χ) := _root_.mul_comm (DegPre.cF D F χ) b
  have h' : DegPre.gtφ D F b χ = D.Oφ b χ := by
    unfold DegPre.gtφ DegPre.Oφ
    rw [h]
  rw [h']

theorem Oφ_over {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (k : Fin 4) :
    D.Oφ (𝟙 D.P.A) χ k ≫ D.P.A.hom = D.P.A.hom := by
  fin_cases k <;> exact Over.w _

theorem gs_scal {F : Type} [CommRing F] {Y : Scheme.{0}} (q : Y ⟶ Sp F) (r : Sp F ⟶ Y) (h : r ≫ q = 𝟙 _) (z : Sp F)
    (a : F) : gs r z ⊤ (scal q a) = toStkA z a :=
  (gs_pull r q z ⊤ trivial _).trans ((congrArg (fun t => gs t z ⊤ _) h).trans (gs_eq (𝟙 _) z ⊤ trivial _))

theorem toStkA_surj {F : Type} [Field F] (z : Sp F) : Function.Surjective (toStkA z) := by
  intro a
  obtain ⟨U, hU, s, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => Subsingleton.elim (α := PrimeSpectrum F) z y ▸ hU
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 s
  exact ⟨x, congrArg ((Sp F).presheaf.germ ⊤ z trivial).hom hx⟩

theorem exists_toStkA_unit {F : Type} [Field F] (z : Sp F) (v : ((Sp F).presheaf.stalk z)ˣ) :
    ∃ t : F, t ≠ 0 ∧ toStkA z t = v.val := by
  obtain ⟨t, e⟩ := toStkA_surj z v.val
  exact ⟨t, fun e0 => v.ne_zero (by rw [← e, e0, map_zero]), e⟩

theorem top_le_of_mem {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U) :
    ⊤ ≤ x ⁻¹ᵁ U := fun y _ => Subsingleton.elim (α := PrimeSpectrum F) z y ▸ h

theorem exists_valF_secLin {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (h : Y ⟶ X)
    (q : Y ⟶ Sp F) (r : Sp F ⟶ Y) (hq : r ≫ q = 𝟙 _) (x : Sp F ⟶ X) (hr : r ≫ h = x) (k : ℕ) {l l' : L.ι}
    (hl : ⊤ ≤ x ⁻¹ᵁ L.U l) (hl' : ⊤ ≤ x ⁻¹ᵁ L.U l') : ∃ τ : F, τ ≠ 0 ∧
      ∀ (σ' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => (k : ℤ)))) (n : ℕ) (cc : Fin n → F)
        (σ : Fin n → H0 L k), GeneratorPullback.SecLin L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) σ'
          (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ)) σ h (fun i => scal q (cc i)) →
        valF r _ (σ'.f (fun _ => l)) = τ * ∑ i, cc i *
          valR x (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => l')) ((σ i).f (fun _ => l')) := by
  subst hr
  let z : Sp F := cpt F
  obtain ⟨J, hJ, eJ⟩ := exists_good L hL z (fun _ : PUnit.{1} => r ≫ h) (fun _ => l')
    (fun _ _ _ => rfl) (fun _ => hl' trivial)
  replace eJ : J (r ≫ h) = l' := eJ PUnit.unit
  have hl₁ : ⊤ ≤ r ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => h) (fun _ => l) :=
    fun y hy => Set.mem_iInter.2 fun _ => hl hy
  have hl₂ : r z ∈ LB.wchart L (fun _ : Fin 1 => h) (fun _ => l') := Set.mem_iInter.2 fun _ => hl' trivial
  obtain ⟨τ, τ0, hτ⟩ := exists_toStkA_unit z (trF (L := L) (fun _ : Fin 1 => h)
    (fun _ => (k : ℤ)) r z (fun _ => l) (fun _ => l'))
  refine ⟨τ, τ0, fun σ' n cc σ hσ => (toStkA z).injective ?_⟩
  refine (toStkA_valR_eq_gs r _ z hl₁ _).trans ((sec_trans σ' r z (hl₁ trivial) hl₂).trans ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, hτ, map_sum, ← sval_of σ' r z J (fun _ => l') (fun _ => eJ), ExpGTrans.secLin_val hσ r z hJ]
  refine congrArg (_ * ·) (Finset.sum_congr rfl fun i _ => ?_)
  rw [map_mul, sval_of (σ i) _ z J (fun _ => l') (fun _ => by rw [Category.comp_id, eJ])]
  exact congrArg₂ (· * ·) (gs_scal _ r hq z _)
    (toStkA_valR_eq_gs (r ≫ h) (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => l')) z
      (fun y hy => Set.mem_iInter.2 fun _ => hl' hy) _).symm

theorem exists_coef_secLin {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (g : GtPtF D F) (w : Frm D F k g.b) (hw : w.IsGen) (z : Sp F)
    (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) : ∃ κ : F, κ ≠ 0 ∧
      ∀ (s : Fam D F k) (χ : D.X) (n : ℕ) (cc : Fin n → F) (f : Fin n → D.SecB k χ),
        GeneratorPullback.SecLin D.P.L (DegPre.famφ D F χ) (DegPre.famε k) (s.s χ) (D.famφB χ) (DegPre.famε k) f
          (DegPre.prB D F).left (fun i => scal (fst (TF (R := R) F) D.P.A).left (cc i)) →
        ∀ (b : Sp F ⟶ D.P.A.left) (jf jt : Fin 4 → D.P.L.ι), b = g.b.left → (∀ i, J (b ≫ D.famφB χ i) = jf i) →
          (∀ i, J (b ≫ D.Oφ (𝟙 _) χ i) = jt i) →
          coef s g w χ = κ * ∑ i, cc i * (valR b _ ((f i).f jf) * valF (𝟙 (Sp F)) _ ((g.s χ).s jt).val) := by
  obtain ⟨Rg, R0, hR⟩ := exists_toStkA_unit z (rigV D (TF (R := R) F).hom z J)
  obtain ⟨W, W0, hW⟩ := exists_toStkA_unit z (val w (𝟙 _) z J)
  refine ⟨W * (Rg ^ k)⁻¹, by simp [R0, W0], fun s χ n cc f hs b jf jt hb hjf hjt => ?_⟩
  let rb : Sp F ⟶ (DegPre.BF D F).left := (lift (𝟙 (TF (R := R) F)) g.b).left
  have hrb : rb ≫ (DegPre.prB D F).left = b :=
    (congrArg (fun t => t.left) (lift_snd (𝟙 (TF (R := R) F)) g.b)).trans hb.symm
  have hrb' : rb ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun t => t.left) (lift_fst (𝟙 (TF (R := R) F)) g.b)
  have hcf : IsCoef k g w χ (s.s χ) (coef s g w χ) := Classical.epsilon_spec
    (((CoefBasic.coef_basic R D F k g).2.2 w hw).1 χ (s.s χ)).exists
  have e := hcf z J hJ
  have a₁ : sval (s.s χ) rb z J = toStkA z (∑ i, cc i * valR b _ ((f i).f jf)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ExpGTrans.secLin_val hs rb z hJ, hrb, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, sval_of (f i) _ z J jf hjf]
    refine congrArg₂ (· * ·) (gs_scal _ rb hrb' z _) (toStkA_valR_eq_gs b _ z (top_le_of_mem _ _ z ?_) _).symm
    have := hJ.mem (D.famφB χ) b
    rwa [funext hjf] at this
  have a₂ : (val (g.s χ) (𝟙 _) z J).val = toStkA z (valF (𝟙 (Sp F)) _ ((g.s χ).s jt).val) := by
    have c : ∀ i, J (𝟙 (Sp F) ≫ DegPre.gtφ D F g.b χ i) = jt i := fun i =>
      (congrArg J ((Category.id_comp _).trans ((gtφ_eq D F g.b χ i).trans
        (congrArg (· ≫ D.Oφ (𝟙 _) χ i) hb.symm)))).trans (hjt i)
    refine (congrArg Units.val (val_of (g.s χ) (𝟙 _) z J jt c)).trans ?_
    have toStkA_valR {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F)
        (ht : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
        toStkA z (valF x U a.val) = (gm x z U a).val := by
      have hz : x z ∈ U := ht trivial
      rw [valF, dif_pos ht, gm, dif_pos hz]
      show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
      rw [Iso.hom_inv_id_apply]
      exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ht) z trivial _
    refine (toStkA_valR (𝟙 (Sp F)) _ z (top_le_of_mem _ _ z ?_) _).symm
    have := hJ.mem (DegPre.gtφ D F g.b χ) (𝟙 (Sp F))
    rwa [funext c] at this
  have e' : toStkA z (coef s g w χ) * toStkA z Rg ^ k = toStkA z (∑ i, cc i * valR b _ ((f i).f jf)) *
      toStkA z (valF (𝟙 (Sp F)) _ ((g.s χ).s jt).val) * toStkA z W := by
    have a₃ : toStkA z (coef s g w χ) = GlobalTheory.UT.cst (R := R) F z (coef s g w χ) := (CoefBasic.cst_eq (R := R) z _).symm
    rw [hR, hW, ← a₁, ← a₂, a₃]
    exact e
  rw [← map_pow, ← map_mul, ← map_mul, ← map_mul] at e'
  rw [(eq_mul_inv_iff_mul_eq₀ (pow_ne_zero k R0)).2 ((toStkA z).injective e'), Finset.sum_mul]
  simp only [_root_.mul_assoc]
  ring

end GlobalTheory.ZH.IntegralSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCoordUnitAndSectionEqExpansion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}
variable {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem gPt_cancel {ψ ψ' : Sp (OO p) ⟶ u.D.toPre.P.A.left} (h : gPt p ≫ ψ = gPt p ≫ ψ') : ψ = ψ' := by
  have : IsProper u.D.toPre.P.A.hom := u.D.toPre.P.isAb.proper
  have := GlobalTheory.ZJ.AddExt.isDominant_gPt p
  exact ext_of_isDominant_of_isSeparated u.D.toPre.P.A.hom
    (ext_of_isDominant (gPt p) (by rw [← Category.assoc, h, Category.assoc])) (gPt p) h

theorem gtN_zero (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (hc : c ≫ u.G.hom = spMap u.j)
    (h : u.Lev c g) : u.GtN g 0 := by
  obtain ⟨b₀, hb, H⟩ := h
  intro J hJ χ
  obtain ⟨ce, hce⟩ := exists_level_point u c hc 0
  obtain ⟨hbe, H⟩ := H 0 ce hce
  have := GlobalTheory.ZJ.AddExt.isDominant_gPt p
  have hb₀ : b₀ ≫ u.D.toPre.P.A.hom = spMap u.j := by
    refine ext_of_isDominant (gPt p) ?_
    rw [← Category.assoc, hb]
    refine (Over.w g.b).trans ?_
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have ht : ⊤ ≤ ce ⁻¹ᵁ LB.wchart u.D.toPre.P.L (u.D.toPre.Oφ (u.U.gt 0).pG χ)
      (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k)) := fun y _ => Set.mem_iInter.2 fun i => by
    have h1 := hJ (b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (by rw [Category.assoc, Oφ_over, hb₀])
    rw [← Category.assoc, hb, ← gtφ_eq] at h1
    exact (congrArg (fun q => q y ∈ u.D.toPre.P.L.U _) (level_Oφ u b₀ ce hbe χ i)).mpr (top_le_comp h1 _ trivial)
  obtain ⟨x, hx, hx'⟩ := H χ _ ht
  rw [← hx, norm_eq_one_of_isUnit u (e := 0) (by rw [hx']; exact isUnit_valR _ _ ht _)]
  simp

theorem parAt [ArithBase o Ω] (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (a : u.PtC)
    (hc : c ≫ u.G.hom = spMap u.j) (ha : gPt p ≫ c = u.toG a) (h : u.Lev c g) (k : ℕ) : u.ParAt k a g := by
  obtain ⟨b₀, hb, H⟩ := h
  intro w hw l hl
  choose ce hce using exists_level_point u c hc
  have hbe := fun e => (H e (ce e) (hce e)).1
  choose d hd using fun y => exists_chart u.D.toPre.P.isLB y
  obtain ⟨jL, hjL⟩ := exists_chart u.U.LG.isLB (c (cpt _))
  have hL : ⊤ ≤ c ⁻¹ᵁ u.U.LG.L.U jL := (top_le_iff_cpt _ _).2 hjL
  have hM : ⊤ ≤ b₀ ⁻¹ᵁ u.D.toPre.P.L.U (d (b₀ (cpt _))) := (top_le_iff_cpt _ _).2 (hd _)
  obtain ⟨ω, ωe, hω0, hω, hωe⟩ := exists_omega u c b₀ ce hce hbe hL hM hc
  have hθ : ∀ θ : u.D.toPre.P.A.left ⟶ u.D.toPre.P.A.left,
      ⊤ ≤ (b₀ ≫ θ) ⁻¹ᵁ u.D.toPre.P.L.U (d ((b₀ ≫ θ) (cpt _))) := fun θ => (top_le_iff_cpt _ _).2 (hd _)
  choose x hx hx' using fun e χ => (H e (ce e) (hce e)).2 χ (fun i => d ((b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (cpt _)))
    (fun y _ => Set.mem_iInter.2 fun i => (congrArg (fun q => q y ∈ u.D.toPre.P.L.U _)
      (level_Oφ u b₀ (ce e) (hbe e) χ i)).mpr (top_le_comp (hθ _) _ trivial))
  have hx0 : ∀ e χ, x 0 χ = x e χ := fun e χ => Subtype.ext ((hx 0 χ).trans (hx e χ).symm)
  have HS := fun σ f hE => hasSum_integral u c b₀ ce hce hbe hL d hd (x 0) (fun e χ => by rw [hx0 e, hx']) ω ωe hω hωe
    (k := k) σ f hE
  let z : Sp (PadicAlgCl p) := cpt _
  obtain ⟨J, hJ, eJ⟩ := exists_good u.D.toPre.P.L u.D.toPre.P.isLB z
    (fun θ : u.D.toPre.P.A.left ⟶ u.D.toPre.P.A.left => gPt p ≫ b₀ ≫ θ) (fun θ => d ((b₀ ≫ θ) (cpt _)))
    (fun θ θ' e => by rw [gPt_cancel u e]) (fun θ => top_le_comp (hθ θ) _ trivial)
  let r : Sp (PadicAlgCl p) ⟶ (UnifPre.GF (G := u.G) (PadicAlgCl p)).left :=
    (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left
  have hr : r ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p) = gPt p ≫ c := by
    rw [ha, ← Category.assoc]
    exact congrArg (fun t : u.PtC => t.left ≫ _) (lift_snd _ _)
  have hr' : r ≫ (fst (TFK (R := u.V) (PadicAlgCl p)) ((Over.pullback (jK u.V)).obj u.G)).left = 𝟙 _ :=
    congrArg (fun t => t.left) (lift_fst (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a)
  obtain ⟨τ, τ0, hτ⟩ := exists_valF_secLin u.U.LG.isLB _ _ r hr' (gPt p ≫ c) hr k (l := l) (l' := jL)
    (by rw [ha]; exact hl) (top_le_comp hL _)
  obtain ⟨κ, κ0, hκ⟩ := exists_coef_secLin u.D.toPre (PadicAlgCl p) k g w hw z J hJ
  refine ⟨κ * ω ^ k * τ⁻¹, by simp [τ0, κ0, hω0], ?_⟩
  rintro σ' s ⟨n, cc, σ, f, hE, hσ, hs⟩
  have e₁ : valF r _ (σ'.f (fun _ => l)) =
      τ * ∑ i, cc i * ((secVal u.U.toUnifPre (σ i) c jL : OO p) : PadicAlgCl p) :=
    (hτ σ' n cc σ hσ).trans (congrArg (τ * ·) (Finset.sum_congr rfl fun i _ => congrArg (cc i * ·)
      (valR_spMap (OO p).subtype c _ (top_le_secChart hL) _)))
  have e₂ : ∀ χ, coef s g w χ = κ * ∑ i, cc i *
      ((valR b₀ _ ((f i χ).f (fun j => d ((b₀ ≫ u.D.toPre.famφB χ j) (cpt _)))) * x 0 χ : OO p) : PadicAlgCl p) := by
    intro χ
    refine (hκ s χ n cc (fun i => f i χ) (hs χ) (gPt p ≫ b₀) (fun j => d ((b₀ ≫ u.D.toPre.famφB χ j) (cpt _)))
      (fun i => d ((b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (cpt _))) hb (fun i => by rw [Category.assoc, eJ])
      (fun i => by rw [Category.assoc, eJ])).trans (congrArg (κ * ·) (Finset.sum_congr rfl fun i _ =>
        congrArg (cc i * ·) ?_))
    rw [MulMemClass.coe_mul]
    exact congrArg₂ (· * ·) (valR_spMap (OO p).subtype b₀ _
      ((top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun j => hd ((b₀ ≫ u.D.toPre.famφB χ j) (cpt _)))) _) (hx 0 χ).symm
  have hs' := (hasSum_sum (s := Finset.univ) fun i _ => (HS (σ i) (f i) (hE i)).mul_left (cc i)).mul_left κ
  show HasSum _ (_ * valF r _ (σ'.f (fun _ => l)))
  rw [e₁, funext e₂]
  refine (congrArg (HasSum _ ·) ?_).mp hs'
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

theorem gtN_zero_and_parAt : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (a : u.PtC), c ≫ u.G.hom = spMap u.j → gPt p ≫ c = u.toG a → u.Lev c g → u.GtN g 0 ∧ ∀ k, 1 ≤ k → u.ParAt k a g :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ u c g a hc ha h => ⟨gtN_zero u c g hc h, fun k _ => parAt u c g a hc ha h k⟩

end GlobalTheory.ZH.IntegralSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCoordUnitAndSectionEqExpansionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCoord_unit_and_section_eq_expansion : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (a : u.PtC), c ≫ u.G.hom = spMap u.j → gPt p ≫ c = u.toG a → u.Lev c g → u.GtN g 0 ∧ ∀ k, 1 ≤ k → u.ParAt k a g := by
  first | exact @GlobalTheory.ZH.IntegralSum.gtN_zero_and_parAt | exact GlobalTheory.ZH.IntegralSum.gtN_zero_and_parAt | (intros; apply GlobalTheory.ZH.IntegralSum.gtN_zero_and_parAt <;> assumption)
end
