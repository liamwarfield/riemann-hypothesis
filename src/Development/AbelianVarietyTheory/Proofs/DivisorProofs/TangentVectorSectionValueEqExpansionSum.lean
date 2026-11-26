module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstJetTermsGaugeUnitMulBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDualNumberCoordsOfAdicSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDualNumberCoordsOfAdicSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AdicDual

theorem hasSum_of_sumI {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R} {C : Type} [NormedField C]
    [IsUltrametricDist C] (φ : R →+* C) (h1 : ∀ a, ‖φ a‖ ≤ 1) (h2 : ∀ a ∈ I, ‖φ a‖ < 1)
    {M : Type} [AddCommGroup M] [Module R M] (g : M →+ C) (hg : ∀ (a : R) y, g (a • y) = φ a * g y)
    {Ix : Type} {x : Ix → M} {s : M} (h : GlobalTheory.UT.SumI I x s) : HasSum (fun i => g (x i)) (g s) := by
  have bd : ∀ {E : Type} [AddCommGroup E] [Module R E] (f : E →+ C), (∀ (a : R) y, f (a • y) = φ a * f y) →
      ∀ (t : Set E) (c : ℝ), 0 ≤ c → (∀ y ∈ t, ‖f y‖ ≤ c) → ∀ y ∈ Submodule.span R t, ‖f y‖ ≤ c := by
    intro E _ _ f hf t c h0 hc y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hc y hy
    | zero => simpa using h0
    | add y z _ _ k1 k2 => rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le k1 k2)
    | smul a y _ k1 => rw [hf, norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (h1 a)).trans k1
  obtain ⟨N, ⟨t, rfl⟩, -, -, h⟩ := h
  obtain ⟨u, rfl⟩ := IsNoetherian.noetherian I
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ y ∈ t, ‖g y‖ ≤ c :=
    ⟨∑ y ∈ t, ‖g y‖, Finset.sum_nonneg fun _ _ => norm_nonneg _,
      fun y hy => Finset.single_le_sum (f := fun y : M => ‖g y‖) (fun _ _ => norm_nonneg _) hy⟩
  obtain ⟨r, hr0, hr1, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ a ∈ u, ‖φ a‖ ≤ r :=
    ⟨(u.sup fun a => ‖φ a‖₊ : NNReal), NNReal.coe_nonneg _,
      by exact_mod_cast (Finset.sup_lt_iff (f := fun a => ‖φ a‖₊) (zero_lt_one' NNReal)).2 fun a ha =>
        show ‖φ a‖₊ < 1 from h2 a (Submodule.subset_span ha),
      fun a ha => by exact_mod_cast Finset.le_sup (f := fun a => ‖φ a‖₊) ha⟩
  have hI := bd φ.toAddMonoidHom (fun a y => map_mul φ a y) u r hr0 hr
  have hP : ∀ n : ℕ, ∀ y ∈ (Submodule.span R (u : Set R)) ^ n • Submodule.span R (t : Set M), ‖g y‖ ≤ r ^ n * c := by
    intro n
    induction n with
    | zero => simpa using bd g hg t c hc0 hc
    | succ n ih =>
      intro y hy
      rw [pow_succ', Submodule.mul_smul] at hy
      refine Submodule.smul_induction_on hy (fun a ha z hz => ?_)
        (fun y z k1 k2 => by rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le k1 k2))
      rw [hg, norm_mul, pow_succ', _root_.mul_assoc]
      exact mul_le_mul (hI a ha) (ih z hz) (norm_nonneg _) hr0
  refine Metric.tendsto_nhds.2 fun e he => ?_
  have lim := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const c
  rw [zero_mul] at lim
  obtain ⟨n, hn⟩ := (lim.eventually (gt_mem_nhds he)).exists
  obtain ⟨S, hS⟩ := h n
  refine Filter.mem_of_superset (Filter.mem_atTop S) fun T hT => ?_
  show dist _ _ < e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [dist_comm, dist_eq_norm, ← map_sum, ← map_sub]
  exact (hP n _ (hS T hT)).trans_lt hn

theorem hasSum_fst_snd : ∀ (V : Type) [CommRing V] [IsDomain V] [IsNoetherianRing V] (I : Ideal V) (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V I C → ∀ {Ix : Type} (x : Ix → DualNumber V) (s : DualNumber V), GlobalTheory.UT.SumI I x s → HasSum (fun i => toF V C (x i).fst) (toF V C s.fst) ∧ HasSum (fun i => toF V C (x i).snd) (toF V C s.snd) := by
  intro V _ _ _ I C _ _ _ hC Ix x s h
  let φ : V →+* C := (algebraMap (FractionRing V) C).comp (algebraMap V _)
  constructor
  · exact hasSum_of_sumI φ hC.1 hC.2 (φ.toAddMonoidHom.comp (TrivSqZeroExt.fstHom V V V).toLinearMap.toAddMonoidHom)
      (fun a y => by simp) h
  · exact hasSum_of_sumI φ hC.1 hC.2 (φ.toAddMonoidHom.comp (TrivSqZeroExt.sndHom V V).toAddMonoidHom)
      (fun a y => by simp) h

end GlobalTheory.AdicDual

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDualNumberCoordsOfAdicSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_dualNumber_coords_of_adicSum : ∀ (V : Type) [CommRing V] [IsDomain V] [IsNoetherianRing V] (I : Ideal V) (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V I C → ∀ {Ix : Type} (x : Ix → DualNumber V) (s : DualNumber V), GlobalTheory.UT.SumI I x s → HasSum (fun i => toF V C (x i).fst) (toF V C s.fst) ∧ HasSum (fun i => toF V C (x i).snd) (toF V C s.snd) := by
  first | exact @GlobalTheory.AdicDual.hasSum_fst_snd | exact GlobalTheory.AdicDual.hasSum_fst_snd | (intros; apply GlobalTheory.AdicDual.hasSum_fst_snd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionValueTangentEqAdicExpansionSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionValueTangentEqAdicExpansionSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanExp

open IsLocalRing GlobalTheory.FormalValue

theorem isLocalRing_dualNumber (V : Type) [CommRing V] [IsLocalRing V] : IsLocalRing (DualNumber V) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact isUnit_or_isUnit_one_sub_self _

theorem thick_closedPoint (V : Type) [CommRing V] [IsLocalRing V] [IsLocalRing (V ⧸ maximalIdeal V ^ (0 + 1))] :
    thick V (maximalIdeal V) 0 (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1))) = closedPoint V := by
  show PrimeSpectrum.comap (Ideal.Quotient.mk (maximalIdeal V ^ (0 + 1))) (closedPoint _) = closedPoint V
  refine PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ?_)
  haveI : (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1))).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

theorem pow_map_le_ker (V : Type) [CommRing V] (m : Ideal V) (e : ℕ) :
    (m.map (algebraMap V (DualNumber V))) ^ (e + 1) ≤
      RingHom.ker ((Ideal.Quotient.mk (m ^ (e + 1))).comp (TrivSqZeroExt.fstHom V V V).toRingHom) := by
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro a ha
  simp only [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl,
    Ideal.Quotient.eq_zero_iff_mem]
  exact ha

theorem ker_dualMap_le (V : Type) [CommRing V] (m : Ideal V) (e : ℕ) :
    RingHom.ker (dualMap (Ideal.Quotient.mk (m ^ (e + 1)))) ≤ (m.map (algebraMap V (DualNumber V))) ^ (e + 1) := by
  intro z hz
  rw [RingHom.mem_ker] at hz
  have h₁ : Ideal.Quotient.mk (m ^ (e + 1)) z.fst = 0 := by
    have := congrArg TrivSqZeroExt.fst hz
    simpa [dualMap] using this
  have h₂ : Ideal.Quotient.mk (m ^ (e + 1)) z.snd = 0 := by
    have := congrArg TrivSqZeroExt.snd hz
    simpa [dualMap] using this
  rw [Ideal.Quotient.eq_zero_iff_mem] at h₁ h₂
  rw [← Ideal.map_pow]
  have hz' : z = algebraMap V (DualNumber V) z.fst + algebraMap V (DualNumber V) z.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hz']
  exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ h₁) (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h₂))

theorem dualMap_surjective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (dualMap f) := by
  intro w
  obtain ⟨a, ha⟩ := hf w.fst
  obtain ⟨b, hb⟩ := hf w.snd
  refine ⟨(TrivSqZeroExt.inl a + TrivSqZeroExt.inr b : DualNumber A), ?_⟩
  ext <;> simp [dualMap, ha, hb]

theorem value_mul_sumI : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)), IsTangent y → TanRel U.toUnifPre y gm₀ → ∀ (k : ℕ) (jG : U.LG.L.ι) (J : (Sp (DualNumber V) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J ψ)) → ∃ W : (DualNumber V)ˣ, (W : DualNumber V).fst * GlobalTheory.MBLow.TanExp.rigVal U.LG jG = GlobalTheory.MBLow.TanExp.rigValD D.toPre (J gm₀.b.left) ∧ ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.toUnifPre.ExpandsAt e k σ f) → GlobalTheory.UT.SumI (IsLocalRing.maximalIdeal V) (fun α => GlobalTheory.MBLow.TanExp.termV J gm₀ (f α)) ((W : DualNumber V) ^ k * valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) (σ.f fun _ => jG)) := by
  intro V _ _ _ _ hV D A G _ _ _ U y gm₀ hy hT k jG J hjG hJ
  haveI : IsLocalRing (DualNumber V) := isLocalRing_dualNumber V
  haveI : Module.Finite V (DualNumber V) := inferInstanceAs (Module.Finite V (V × V))
  haveI : IsAdicComplete (maximalIdeal V) V := hV
  haveI hJd : IsAdicComplete ((maximalIdeal V).map (algebraMap V (DualNumber V))) (DualNumber V) :=
    InertNorm.isAdicComplete_map_of_finite (maximalIdeal V) (DualNumber V)
  have hx : IsFormalPt U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) gm₀ y.left :=
    isFormalPt_of_surjective _ fun e => by
      obtain ⟨ye, h₁, h₂, h₃⟩ := hT e
      exact ⟨DualNumber (V ⧸ maximalIdeal V ^ (e + 1)), inferInstance, dualMap (Ideal.Quotient.mk _), ye,
        dualMap_surjective _ Ideal.Quotient.mk_surjective, ker_dualMap_le V _ e, h₁, h₂, h₃⟩
  have hL : ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG := hjG
  have hM : ⊤ ≤ basePt gm₀ ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := hJ _
  refine ⟨(tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG (J gm₀.b.left))⁻¹,
    ?_, fun σ f hE => ?_⟩
  · obtain ⟨g₀, hg₀⟩ := exists_isZero D.toPre (Over.mk (spMap (RingHom.id V)))
    haveI : IsAdicComplete ((maximalIdeal V).map (RingHom.id V)) V := by rw [Ideal.map_id]; exact hV
    have h₀ := isFormalPt_zero U.toUnifPre (RingHom.id V) hg₀
    have hid : spMap (RingHom.id V) = 𝟙 (Sp V) := by
      show Spec.map (CommRingCat.ofHom (RingHom.id V)) = _
      rw [CommRingCat.ofHom_id, Spec.map_id]
    have hb₀ : basePt g₀ = spMap (RingHom.id V) ≫ eSec D.toPre.P.A := by
      refine (congrArg Over.Hom.left hg₀.1).trans ?_
      exact congrArg (· ≫ eSec D.toPre.P.A)
        ((Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk (spMap (RingHom.id V))))))
    have hyE : spMap (TrivSqZeroExt.fstHom V V V).toRingHom ≫ y.left = eSec G := hy
    have hL₀ : ⊤ ≤ (spMap (RingHom.id V) ≫ eSec G) ⁻¹ᵁ U.LG.L.U jG := by
      rw [← hyE, ← Category.assoc]; exact top_le_comp hL _
    have hxe : ∀ e, eSec (thickObj V (maximalIdeal V) e G) ≫ (fstG (maximalIdeal V) e G).left =
        spMap ((Ideal.Quotient.mk (maximalIdeal V ^ (e + 1))).comp (TrivSqZeroExt.fstHom V V V).toRingHom) ≫
          y.left := fun e => by
      rw [ExpansionValueZero.eSec_fstG, ← hyE]
      show _ = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (maximalIdeal V ^ (e + 1))).comp
        (TrivSqZeroExt.fstHom V V V).toRingHom)) ≫ _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have hM₀ : ⊤ ≤ basePt g₀ ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := by
      haveI : IsLocalRing (V ⧸ maximalIdeal V ^ (0 + 1)) :=
        isLocalRing_quotient_pow (IsLocalRing.maximalIdeal.isMaximal V).ne_top 0
      have HC := hx.hasCoords (e := 0) _ (pow_map_le_ker V _ 0) (hxe 0)
      have h₂ : thick V (maximalIdeal V) 0 ≫ eSec D.toPre.P.A = spMap _ ≫ gm₀.b.left :=
        (ExpansionValueZero.eSec_pG _ (U.gt 0)).symm.trans HC.2.1
      have h₃ : ⊤ ≤ (thick V (maximalIdeal V) 0 ≫ eSec D.toPre.P.A) ⁻¹ᵁ D.toPre.P.L.U (J gm₀.b.left) := by
        rw [h₂]; exact top_le_comp hM _
      have h₄ : eSec D.toPre.P.A (thick V (maximalIdeal V) 0 (closedPoint (V ⧸ maximalIdeal V ^ (0 + 1)))) ∈
          D.toPre.P.L.U (J gm₀.b.left) := h₃ (Set.mem_univ _)
      rw [thick_closedPoint] at h₄
      rw [hb₀]
      exact top_le_comp (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of V) _ h₄).ge _
    have hfst : (tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
        (J gm₀.b.left) : DualNumber V).fst =
        (tau U.toUnifPre ((maximalIdeal V).map (RingHom.id V)) (spMap (RingHom.id V) ≫ eSec G) jG
          (J gm₀.b.left) : V) := by
      refine eq_of_forall_mk_eq (maximalIdeal V) fun e => ?_
      have a₁ := map_tau_mul_wVal hx hL hM _ (pow_map_le_ker V _ e) (hxe e)
      have a₂ := map_tau_mul_wVal h₀ hL₀ hM₀ (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)))
        (by rw [Ideal.map_id, Ideal.mk_ker]) (xe := eSec (thickObj V (maximalIdeal V) e G))
        (by rw [hid, Category.id_comp]; exact ExpansionValueZero.eSec_fstG _ e G)
      exact (IsUnit.of_mul_eq_one_right _ a₂).mul_right_cancel (a₁.trans a₂.symm)
    have r₀ := tau_rig h₀ hb₀ hL₀ hM₀
    have hv : ∀ (U' : (Sp V).Opens) (f : Γ(Sp V, U')),
        valR (spMap (RingHom.id V)) U' f = valR (𝟙 (Sp V)) U' f := fun _ _ => by rw [hid]
    rw [hv, hv] at r₀
    have hW : (((tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
        (J gm₀.b.left))⁻¹ : (DualNumber V)ˣ) : DualNumber V).fst *
        (tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG
          (J gm₀.b.left) : DualNumber V).fst = 1 := by
      rw [← TrivSqZeroExt.fst_mul, Units.inv_mul, TrivSqZeroExt.fst_one]
    unfold rigVal rigValD
    rw [← r₀, ← _root_.mul_assoc, ← hfst, hW, _root_.one_mul]
    rfl
  · refine ⟨⊤, Module.Finite.fg_top, Submodule.mem_top, fun _ => Submodule.mem_top, fun n => ?_⟩
    haveI : IsLocalRing (DualNumber V ⧸ ((maximalIdeal V).map (algebraMap V (DualNumber V))) ^ (n + 1)) :=
      isLocalRing_quotient_pow (ne_top_of_isHausdorff _) n
    obtain ⟨F, hF⟩ := map_secVal_eq U.toUnifPre (hE n)
    obtain ⟨-, h₁⟩ := hF (DualNumber V) ((maximalIdeal V).map (algebraMap V (DualNumber V))) _ gm₀ y.left hx _
      (Ideal.Quotient.mk (((maximalIdeal V).map (algebraMap V (DualNumber V))) ^ (n + 1))) (by rw [Ideal.mk_ker])
    refine ⟨F, fun T hT => ?_⟩
    have hc : ∀ α ∈ T, CohCharts gm₀ α (J gm₀.b.left) (fun i => J (gm₀.b.left ≫ D.toPre.famφB α i))
        (fun i => J (D.toPre.gtφT (epsR V) gm₀.b α i)) := fun α _ => by
      refine ⟨fun p _ => Set.mem_iInter.2 fun i => hJ (gm₀.b.left ≫ D.toPre.famφB α i) (Set.mem_univ p),
        fun p _ => Set.mem_iInter.2 fun i => hJ (D.toPre.gtφT (epsR V) gm₀.b α i) (Set.mem_univ p), ?_⟩
      have c : ∀ a, Sum.elim (fun _ : PUnit.{1} => J gm₀.b.left) (Sum.elim (fun i => J (gm₀.b.left ≫ D.toPre.famφB α i))
          (fun i => J (D.toPre.gtφT (epsR V) gm₀.b α i))) a = J (Sum.elim (fun _ : PUnit.{1} => basePt gm₀)
            (Sum.elim (fun a => basePt gm₀ ≫ D.toPre.famφB α a) (coordφ gm₀ α)) a) := by
        rintro (a | a | a) <;> rfl
      exact fun a b hab => (c a).trans ((congrArg J hab).trans (c b).symm)
    have e := h₁ T jG (J gm₀.b.left) (fun α i => J (gm₀.b.left ≫ D.toPre.famφB α i))
      (fun α i => J (D.toPre.gtφT (epsR V) gm₀.b α i)) hT hL hM hc
    rw [Ideal.Quotient.eq] at e
    have key := Ideal.mul_mem_left _
      (((tau U.toUnifPre ((maximalIdeal V).map (algebraMap V (DualNumber V))) y.left jG (J gm₀.b.left))⁻¹ :
        (DualNumber V)ˣ) ^ k : DualNumber V) e
    rw [mul_sub, ← _root_.mul_assoc, ← mul_pow, Units.inv_mul, one_pow, _root_.one_mul] at key
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
    exact Ideal.pow_le_pow_right (Nat.le_succ n) key

end GlobalTheory.MBLow.TanExp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSectionValueTangentEqAdicExpansionSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralSectionValue_tangent_eq_adicExpansionSum : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)), IsTangent y → TanRel U.toUnifPre y gm₀ → ∀ (k : ℕ) (jG : U.LG.L.ι) (J : (Sp (DualNumber V) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J ψ)) → ∃ W : (DualNumber V)ˣ, (W : DualNumber V).fst * GlobalTheory.MBLow.TanExp.rigVal U.LG jG = GlobalTheory.MBLow.TanExp.rigValD D.toPre (J gm₀.b.left) ∧ ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.toUnifPre.ExpandsAt e k σ f) → GlobalTheory.UT.SumI (IsLocalRing.maximalIdeal V) (fun α => GlobalTheory.MBLow.TanExp.termV J gm₀ (f α)) ((W : DualNumber V) ^ k * valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) (σ.f fun _ => jG)) := by
  first | exact @GlobalTheory.MBLow.TanExp.value_mul_sumI | exact GlobalTheory.MBLow.TanExp.value_mul_sumI | (intros; apply GlobalTheory.MBLow.TanExp.value_mul_sumI <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericTangentEqUnitMulCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericTangentEqUnitMulCombination
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow.TanVal

theorem subsingleton_dual (K : Type) [Field K] : Subsingleton (PrimeSpectrum (DualNumber K)) := by
  have key : ∀ P : PrimeSpectrum (DualNumber K), P.asIdeal = Ideal.span {DualNumber.eps} := by
    intro P
    have hm : (DualNumber.eps : DualNumber K) ∈ P.asIdeal :=
      P.isPrime.mem_of_pow_mem 2 (by rw [pow_two, DualNumber.eps_mul_eps]; exact zero_mem _)
    rcases DualNumber.ideal_trichotomy P.asIdeal with h | h | h
    · rw [h, Ideal.mem_bot] at hm
      have := congrArg TrivSqZeroExt.snd hm
      simp at this
    · exact h
    · exact absurd h P.isPrime.ne_top
  exact ⟨fun P Q ↦ PrimeSpectrum.ext ((key P).trans (key Q).symm)⟩

theorem sp_comp {A B B' : Type} [CommRing A] [CommRing B] [CommRing B'] (a : A →+* B) (b : B' →+* A) :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem fst_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (TrivSqZeroExt.fstHom B B B).toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom A A A).toRingHom :=
  RingHom.ext fun z => by simp [dualMap]

theorem fst_alg (C : Type) [Field C] :
    (TrivSqZeroExt.fstHom C C C).toRingHom.comp (algebraMap C (DualNumber C)) = RingHom.id C :=
  RingHom.ext fun z => by simp

theorem resTop_top {Y : Scheme.{0}} (a : Γ(Y, ⊤)) : resTop ⊤ a = a := by
  simp [resTop]

end GlobalTheory.MBLow.TanVal

noncomputable section
namespace GlobalTheory.MBLow.TanVal

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem exists_ptG (U : UnifPre I D A G) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (yA : Sp (DualNumber C) ⟶ (TFK (R := R) C ⊗ A.A).left) :
    ∃ yG : Sp (DualNumber C) ⟶ (UnifPre.GF (G := G) C).left, yG ≫ (U.genF C).left = yA := by
  refine ⟨yA ≫ (lift (fst (TFK (R := R) C) A.A) (snd _ _ ≫ U.gen.inv)).left, ?_⟩
  have h : lift (fst (TFK (R := R) C) A.A) (snd _ _ ≫ U.gen.inv) ≫ U.genF C = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [UnifPre.genF]
    · simp [UnifPre.genF]
  rw [Category.assoc, ← Over.comp_left, h, Over.id_left, Category.comp_id]

theorem genF_snd (U : UnifPre I D A G) (C : Type) [Field C] [Algebra (FractionRing R) C] :
    (U.genF C).left ≫ (snd (TFK (R := R) C) A.A).left =
      (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
  rw [← Over.comp_left, ← Over.comp_left, UnifPre.genF, lift_snd]

theorem genF_fst (U : UnifPre I D A G) (C : Type) [Field C] [Algebra (FractionRing R) C] :
    (U.genF C).left ≫ (fst (TFK (R := R) C) A.A).left =
      (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left := by
  rw [← Over.comp_left, UnifPre.genF, lift_fst]

theorem gs_to_valR {B : Type} [CommRing B] [IsLocalRing B] {X : Scheme.{0}} (x : Sp B ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, V)) :
    (stalkClosedPointIso (CommRingCat.of B)).hom.hom (gs x (IsLocalRing.closedPoint B) V f) = valR x V f :=
  (GlobalTheory.ZH.ThetaData.valR_eq_gs x V (h trivial) f).symm


set_option maxHeartbeats 1000000 in
theorem value_tangent : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (C : Type) [Field C] [Algebra (FractionRing R) C] (w₀ : GlobalTheory.UT.W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U w₀ ρ → ∀ (y : epsR R ⟶ G) (yA : Sp (DualNumber C) ⟶ (TFK (R := R) C ⊗ A.A).left), IsTangent y → VecAt U C y yA → ∀ (k : ℕ) (i₀ : A.L.ι) (jG : U.LG.L.ι), ⊤ ≤ (jFK (R := R) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → ∃ Θ : (DualNumber C)ˣ, (Θ : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigVal U.LG jG) ^ k = valR (jFK (R := R) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k ∧ ∀ (t : GlobalTheory.UT.SecA A C k) (σ' : U.SecGF C k), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) C) A.A).left (U.genF C).left t (UnifPre.gFK (G := G) C) (𝟙 _) σ' → ∀ (n : ℕ) (c : Fin n → C) (σ : Fin n → H0 U.LG.L k), GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) C) (fun _ => (k : ℤ)) σ' (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) C) (fun i => scal (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left (c i)) → valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := R) C)).U fun _ => i₀) (t.f fun _ => i₀) = (Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) ((σ i).f fun _ => jG)) := by
  intro R _ _ I D A G _ _ U C _ _ w₀ ρ hN y yA hy hV k i₀ jG hi hj
  haveI := subsingleton_dual C
  obtain ⟨yG, e₁⟩ := exists_ptG U C yA
  have e₂ : yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left =
      yA ≫ (snd (TFK (R := R) C) A.A).left := by
    rw [← genF_snd, ← Category.assoc, e₁]
  have e₃ : yG ≫ (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left = spMap (algebraMap C (DualNumber C)) := by
    rw [← genF_fst, ← Category.assoc, e₁, hV.1]
  have e₂' : yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left =
      yA ≫ (snd (TFK (R := R) C) A.A).left ≫ U.gen.inv.left := by
    rw [← reassoc_of% e₂, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.comp_id]
  have e₄ : yG ≫ UnifPre.gFK (G := G) C = spMap (dualMap (toF R C)) ≫ y.left := by
    rw [UnifPre.gFK, ← Category.assoc, e₂']
    simp only [Category.assoc]
    exact hV.2
  have hfR : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ y.left = eSec G := hy
  have hjj : jFK (R := R) C ≫ jK R = spMap (toF R C) := sp_comp _ _
  have hη : eSec ((Over.pullback (jK R)).obj G) ≫ pullback.snd G.hom (jK R) = 𝟙 _ := Over.w η[(Over.pullback (jK R)).obj G]
  have e₅ : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yG ≫
      (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left = jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G) := by
    apply pullback.hom_ext
    · have l : (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yG ≫
          (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R) =
          spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap (dualMap (toF R C)) ≫ y.left := by
        rw [← e₄]; simp only [UnifPre.gFK, Category.assoc]
      rw [l, ← Category.assoc, sp_comp, fst_dualMap, ← sp_comp, Category.assoc, hfR, Category.assoc,
        GlobalTheory.UT.EvalZero.eK_fst, ← Category.assoc, hjj]
    · have l : (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left ≫ pullback.snd G.hom (jK R) =
          (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left ≫ jFK (R := R) C :=
        (Over.w (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G))).trans
          (Over.w (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G))).symm
      simp only [Category.assoc]
      rw [l, ← Category.assoc yG, e₃, ← Category.assoc, sp_comp, fst_alg, hη]
      simp [spMap]

  have hx₁ : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yA ≫ (snd (TFK (R := R) C) A.A).left =
      jFK (R := R) C ≫ eSec A.A := by
    rw [← e₂, reassoc_of% e₅, GlobalTheory.UT.EvalZero.eK_gen U]
  have m₁ : ⊤ ≤ (yA ≫ (snd (TFK (R := R) C) A.A).left) ⁻¹ᵁ A.L.U i₀ := by
    intro z' _
    obtain rfl : z' = spMap (TrivSqZeroExt.fstHom C C C).toRingHom (IsLocalRing.closedPoint C) :=
      Subsingleton.elim (α := PrimeSpectrum (DualNumber C)) _ _
    have h := hi (show IsLocalRing.closedPoint C ∈ (⊤ : (Sp C).Opens) from trivial)
    rw [← hx₁] at h
    exact h
  have m₂ : ⊤ ≤ (spMap (dualMap (toF R C)) ≫ y.left) ⁻¹ᵁ U.LG.L.U jG := GlobalTheory.FormalValue.top_le_comp hj _
  have hG₀ : (jFK (R := R) C ≫ jK R) ≫ eSec G =
      (spMap (toF R C) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ y.left := by
    rw [hjj, Category.assoc, hfR]
  have m₄ : ⊤ ≤ ((jFK (R := R) C ≫ jK R) ≫ eSec G) ⁻¹ᵁ U.LG.L.U jG := by
    rw [hG₀]; exact GlobalTheory.FormalValue.top_le_comp hj _
  have m₅ : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ ((U.LG.L.pull (eSec G)).U fun _ => jG) := by
    intro z' _
    refine mem_pull.2 ?_
    have h := GlobalTheory.FormalValue.top_le_comp hj (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
      (show z' ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [hfR] at h
    exact h
  obtain ⟨JA, hJA, cJA⟩ := exists_good (Z := Sp (DualNumber C)) A.L A.isLB (IsLocalRing.closedPoint (DualNumber C))
    (fun _ : Unit => yA ≫ (snd (TFK (R := R) C) A.A).left) (fun _ => i₀) (fun _ _ _ => rfl) (fun _ => m₁ trivial)
  obtain ⟨JG, hJG, cJG⟩ := exists_good (Z := Sp (DualNumber C)) U.LG.L U.LG.isLB (IsLocalRing.closedPoint (DualNumber C))
    (fun _ : Unit => spMap (dualMap (toF R C)) ≫ y.left) (fun _ => jG) (fun _ _ _ => rfl) (fun _ => m₂ trivial)
  obtain ⟨JA', hJA', cJA'⟩ := exists_good (Z := Sp C) A.L A.isLB (IsLocalRing.closedPoint C)
    (fun _ : Unit => jFK (R := R) C ≫ eSec A.A) (fun _ => i₀) (fun _ _ _ => rfl) (fun _ => hi trivial)
  obtain ⟨JG', hJG', cJG'⟩ := exists_good (Z := Sp C) U.LG.L U.LG.isLB (IsLocalRing.closedPoint C)
    (fun _ : Unit => (jFK (R := R) C ≫ jK R) ≫ eSec G) (fun _ => jG) (fun _ _ _ => rfl) (fun _ => m₄ trivial)

  have mp : ⊤ ≤ (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) ⁻¹ᵁ
      ((LB.div (U.LG.L.pull (pullback.fst G.hom (jK R))) (A.L.pull U.gen.hom.left)).U (fun _ => jG, fun _ => i₀)) := by
    intro z' _
    refine ⟨mem_pull.2 ?_, mem_pull.2 ?_⟩
    · have h := m₂ (show z' ∈ (⊤ : (Sp (DualNumber C)).Opens) from trivial)
      rw [← e₄] at h
      exact h
    · have h := m₁ (show z' ∈ (⊤ : (Sp (DualNumber C)).Opens) from trivial)
      rw [← e₂] at h
      exact h
  have mp₀ : ⊤ ≤ (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G)) ⁻¹ᵁ
      ((LB.div (U.LG.L.pull (pullback.fst G.hom (jK R))) (A.L.pull U.gen.hom.left)).U (fun _ => jG, fun _ => i₀)) := by
    rw [← e₅]; exact GlobalTheory.FormalValue.top_le_comp mp _
  have hv := GlobalTheory.FormalValue.isUnit_valR (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) _ mp
    (w₀.s (fun _ => jG, fun _ => i₀))
  have hvfst : TrivSqZeroExt.fst (valR (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) _
      (w₀.s (fun _ => jG, fun _ => i₀)).val) =
      valR (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G)) _ (w₀.s (fun _ => jG, fun _ => i₀)).val := by
    have := GlobalTheory.FormalValue.valR_spMap (TrivSqZeroExt.fstHom C C C).toRingHom
      (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) _ mp (w₀.s (fun _ => jG, fun _ => i₀)).val
    rw [e₅] at this
    exact this.symm
  have mρ : ⊤ ≤ (jFK (R := R) C) ⁻¹ᵁ LB.wchart A.L (fun _ : PUnit.{1} => eSec A.A) (fun _ => i₀) :=
    fun _ _ => Set.mem_iInter.2 fun _ => hi trivial
  have mr : ⊤ ≤ (jFK (R := R) C ≫ jK R) ⁻¹ᵁ LB.wchart U.LG.L (fun _ : PUnit.{1} => eSec G) (fun _ => jG) :=
    fun _ _ => Set.mem_iInter.2 fun _ => m₄ trivial
  have n₁ := GlobalTheory.UT.EvalZero.normW_ext U C hN (IsLocalRing.closedPoint C) hJA' hJG'
  replace n₁ : (GlobalTheory.BoxExpansion.pw w₀ (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G)) (IsLocalRing.closedPoint C)
      (JA' (jFK (R := R) C ≫ eSec A.A)) (JG' ((jFK (R := R) C ≫ jK R) ≫ eSec G))).val *
      (gm (jFK (R := R) C) (IsLocalRing.closedPoint C) (LB.wchart A.L (fun _ : PUnit.{1} => eSec A.A)
        (fun _ => JA' (jFK (R := R) C ≫ eSec A.A))) (ρ.s fun _ => JA' (jFK (R := R) C ≫ eSec A.A))).val =
      (gm (jFK (R := R) C ≫ jK R) (IsLocalRing.closedPoint C) (LB.wchart U.LG.L (fun _ : PUnit.{1} => eSec G)
        (fun _ => JG' ((jFK (R := R) C ≫ jK R) ≫ eSec G))) (U.LG.rig.s fun _ => JG' ((jFK (R := R) C ≫ jK R) ≫ eSec G))).val := n₁
  rw [cJA' (), cJG' ()] at n₁
  have g₁ := gs_unit (jFK (R := R) C) (IsLocalRing.closedPoint C) (LB.wchart A.L (fun _ : PUnit.{1} => eSec A.A) (fun _ => i₀))
      (mρ (show IsLocalRing.closedPoint C ∈ (⊤ : (Sp C).Opens) from trivial)) (ρ.s fun _ => i₀)
  have g₂ := gs_unit (jFK (R := R) C ≫ jK R) (IsLocalRing.closedPoint C) (LB.wchart U.LG.L (fun _ : PUnit.{1} => eSec G) (fun _ => jG))
      (mr (show IsLocalRing.closedPoint C ∈ (⊤ : (Sp C).Opens) from trivial)) (U.LG.rig.s fun _ => jG)
  replace n₁ := (congrArg (fun q => (GlobalTheory.BoxExpansion.pw w₀ (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G))
      (IsLocalRing.closedPoint C) i₀ jG).val * q) g₁).trans (n₁.trans g₂.symm)
  have hpw₀ : (GlobalTheory.BoxExpansion.pw w₀ (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G)) (IsLocalRing.closedPoint C)
      i₀ jG).val = gs (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G)) (IsLocalRing.closedPoint C) _
        (w₀.s (fun _ => jG, fun _ => i₀)).val := (gs_unit (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G)) (IsLocalRing.closedPoint C) _
        (mp₀ (show IsLocalRing.closedPoint C ∈ (⊤ : (Sp C).Opens) from trivial)) _).symm
  rw [hpw₀] at n₁
  have n₂ := congrArg (stalkClosedPointIso (CommRingCat.of C)).hom.hom n₁
  rw [map_mul, gs_to_valR _ _ mp₀, gs_to_valR _ _ mρ, gs_to_valR _ _ mr, hjj] at n₂
  have hr : valR (spMap (toF R C)) (LB.wchart U.LG.L (fun _ : PUnit.{1} => eSec G) (fun _ => jG))
      (U.LG.rig.s fun _ => jG).val = toF R C (GlobalTheory.MBLow.TanExp.rigVal U.LG jG) := by
    have := GlobalTheory.FormalValue.valR_spMap (toF R C) (𝟙 (Sp R)) _ m₅ (U.LG.rig.s fun _ => jG).val
    rw [Category.comp_id] at this
    exact this
  rw [hr, ← hvfst] at n₂

  have h1 : ((hv.unit ^ k)⁻¹ : (DualNumber C)ˣ).val *
      (valR (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) _
        (w₀.s (fun _ => jG, fun _ => i₀)).val) ^ k = 1 := by
    have := Units.inv_mul (hv.unit ^ k)
    rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec] at this
  refine ⟨(hv.unit ^ k)⁻¹, ?_, ?_⟩
  · have h2 := congrArg TrivSqZeroExt.fst h1
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_one] at h2
    rw [← n₂, mul_pow, ← _root_.mul_assoc, h2, _root_.one_mul]
    rfl
  intro t σ' hR n c σ hσ
  have cA : JA (yA ≫ (snd (TFK (R := R) C) A.A).left) = i₀ := cJA ()
  have cG : JG (spMap (dualMap (toF R C)) ≫ y.left) = jG := cJG ()
  have a₁ := GlobalTheory.BoxExpansion.isoRel_val hR yG (IsLocalRing.closedPoint (DualNumber C)) hJA hJG
  have e₄' : yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R) =
      spMap (dualMap (toF R C)) ≫ y.left := e₄
  rw [Category.comp_id, e₁, Category.assoc, e₂, cA, Category.assoc, e₄', cG] at a₁
  have a₂ := GlobalTheory.BoxExpansion.secLin_val hσ yG (IsLocalRing.closedPoint (DualNumber C)) hJG
  have st := sval_of t yA (IsLocalRing.closedPoint (DualNumber C)) JA (fun _ => i₀) (fun _ => cA)
  have sσ := fun i => sval_of (σ i) (yG ≫ UnifPre.gFK (G := G) C) (IsLocalRing.closedPoint (DualNumber C)) JG
    (fun _ => jG) (fun _ => by rw [Category.comp_id, e₄]; exact cG)
  have mt : ⊤ ≤ yA ⁻¹ᵁ LB.wchart A.L (fun _ : Fin 1 => (snd (TFK (R := R) C) A.A).left) (fun _ => i₀) :=
    fun _ _ => Set.mem_iInter.2 fun _ => m₁ trivial
  have mσ : ⊤ ≤ y.left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jG) :=
    fun _ _ => Set.mem_iInter.2 fun _ => hj trivial
  have mσ' : ⊤ ≤ (yG ≫ UnifPre.gFK (G := G) C) ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jG) := by
    rw [e₄]; exact GlobalTheory.FormalValue.top_le_comp mσ _
  have hpw : (stalkClosedPointIso (CommRingCat.of (DualNumber C))).hom.hom
      (GlobalTheory.BoxExpansion.pw w₀ (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left)
        (IsLocalRing.closedPoint (DualNumber C)) i₀ jG).val =
      valR (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) _ (w₀.s (fun _ => jG, fun _ => i₀)).val := by
    have g := gs_unit (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left)
      (IsLocalRing.closedPoint (DualNumber C)) _
      (mp (show IsLocalRing.closedPoint (DualNumber C) ∈ (⊤ : (Sp (DualNumber C)).Opens) from trivial))
      (w₀.s (fun _ => jG, fun _ => i₀))
    exact (congrArg (stalkClosedPointIso (CommRingCat.of (DualNumber C))).hom.hom g.symm).trans (gs_to_valR _ _ mp _)
  have ht : (stalkClosedPointIso (CommRingCat.of (DualNumber C))).hom.hom
      (sval t yA (IsLocalRing.closedPoint (DualNumber C)) JA) =
      valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := R) C)).U fun _ => i₀) (t.f fun _ => i₀) :=
    (congrArg _ st).trans (gs_to_valR _ _ mt _)
  have hσv : ∀ i, (stalkClosedPointIso (CommRingCat.of (DualNumber C))).hom.hom
      (sval (σ i) (yG ≫ UnifPre.gFK (G := G) C) (IsLocalRing.closedPoint (DualNumber C)) JG) =
      dualMap (toF R C) (valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) ((σ i).f fun _ => jG)) :=
    fun i => (congrArg _ (sσ i)).trans ((gs_to_valR _ _ mσ' _).trans (by
      rw [e₄]; exact GlobalTheory.FormalValue.valR_spMap _ _ _ mσ _))
  have hc : ∀ i, (stalkClosedPointIso (CommRingCat.of (DualNumber C))).hom.hom
      (gs yG (IsLocalRing.closedPoint (DualNumber C)) ⊤
        (scal (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left (c i))) = TrivSqZeroExt.inl (c i) := fun i => by
    have mtop : ⊤ ≤ yG ⁻¹ᵁ (⊤ : (UnifPre.GF (G := G) C).left.Opens) := fun x _ => show yG x ∈ (⊤ : (UnifPre.GF (G := G) C).left.Opens) from trivial
    rw [gs_to_valR _ _ mtop, ← resTop_top (scal _ (c i)),
      GlobalTheory.ZH.FormCount.valR_scal (algebraMap C (DualNumber C)) yG _ e₃ ⊤ mtop]
    rfl
  have E := congrArg (stalkClosedPointIso (CommRingCat.of (DualNumber C))).hom.hom (a₁.symm.trans a₂)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_sum, Units.val_pow_eq_pow_val, map_pow, hpw, ht] at E
  simp only [map_mul, hc, hσv] at E
  rw [← E, ← _root_.mul_assoc, h1, _root_.one_mul]

end GlobalTheory.MBLow.TanVal
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericTangentEqUnitMulCombinationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.sectionValue_genericTangent_eq_unit_mul_combination : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (C : Type) [Field C] [Algebra (FractionRing R) C] (w₀ : GlobalTheory.UT.W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U w₀ ρ → ∀ (y : epsR R ⟶ G) (yA : Sp (DualNumber C) ⟶ (TFK (R := R) C ⊗ A.A).left), IsTangent y → VecAt U C y yA → ∀ (k : ℕ) (i₀ : A.L.ι) (jG : U.LG.L.ι), ⊤ ≤ (jFK (R := R) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → ∃ Θ : (DualNumber C)ˣ, (Θ : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigVal U.LG jG) ^ k = valR (jFK (R := R) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k ∧ ∀ (t : GlobalTheory.UT.SecA A C k) (σ' : U.SecGF C k), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) C) A.A).left (U.genF C).left t (UnifPre.gFK (G := G) C) (𝟙 _) σ' → ∀ (n : ℕ) (c : Fin n → C) (σ : Fin n → H0 U.LG.L k), GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) C) (fun _ => (k : ℤ)) σ' (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) C) (fun i => scal (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left (c i)) → valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := R) C)).U fun _ => i₀) (t.f fun _ => i₀) = (Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) ((σ i).f fun _ => jG)) := by
  first | exact @GlobalTheory.MBLow.TanVal.value_tangent | exact GlobalTheory.MBLow.TanVal.value_tangent | (intros; apply GlobalTheory.MBLow.TanVal.value_tangent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelTangentVectorTorusPointReducesToOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelTangentVectorTorusPointReducesToOrigin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanRed

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
  {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem redE_dualMap (e : ℕ) :
    redE (R ⧸ I ^ (e + 1)) ≫ spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) = thick R I e ≫ redE R := by
  show spMap _ ≫ spMap _ = Spec.map _ ≫ spMap _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem red_lift_eq_eSec (y : epsR R ⟶ G) (hy : IsTangent y) (e : ℕ)
    (ye : Sp (DualNumber (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left)
    (h1 : ye ≫ (fstG I e G).left = spMap (dualMap (Ideal.Quotient.mk (I ^ (e + 1)))) ≫ y.left) :
    redE (R ⧸ I ^ (e + 1)) ≫ ye = eSec (thickObj R I e G) := by
  rw [← cancel_mono (fstG I e G).left, Category.assoc, h1, ← Category.assoc, redE_dualMap, Category.assoc]
  have hy' : redE R ≫ y.left = η[G].left := hy
  rw [hy']
  exact (UnitValue.eSec_fGl (G := G) e).symm

theorem levels_of_tanRel (U : UnifPre I D A G) (y : epsR R ⟶ G) (hy : IsTangent y) (gm : GtPt D.toPre (epsR R))
    (h : TanRel U y gm) (e : ℕ) :
    eSec (thickObj R I e G) ≫ (U.gt e).pG.left = (thick R I e ≫ redE R) ≫ gm.b.left ∧
    ∀ χ (z : Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) C, Good D.toPre.P.L z C →
      val ((U.gt e).t χ) (eSec (thickObj R I e G)) z C = val (gm.s χ) (thick R I e ≫ redE R) z C := by
  obtain ⟨ye, h1, h2, h3⟩ := h e
  have hr := red_lift_eq_eSec y hy e ye h1
  refine ⟨?_, fun χ z C hC => ?_⟩
  · rw [← hr, Category.assoc, h2, ← Category.assoc, redE_dualMap]
  · rw [← hr, ← redE_dualMap]
    exact (val_pull hC _ _ _).symm.trans ((val_corr hC (h3 χ) _).trans (val_pull hC _ _ _))

theorem gtTan_of_tanRel [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete I R] (U : UnifPre I D A G)
    (y : epsR R ⟶ G) (gm : GtPt D.toPre (epsR R)) (hy : IsTangent y) (h : TanRel U y gm) : GtTan gm := by
  have hL := D.toPre.P.isLB
  have hz := levels_of_tanRel U y hy gm h
  have hb : redE R ≫ gm.b.left = η[D.toPre.P.A].left := hom_ext_of_isHausdorff I fun e =>
    (Category.assoc _ _ _).symm.trans ((hz e).1.symm.trans (UnitValue.eSec_pGl U e))
  obtain ⟨o, ho⟩ := FormalValue.exists_isZero D.toPre (baseOver (Sp R))
  have hob : o.b.left = redE R ≫ gm.b.left := by
    rw [hb, ho.1]
    exact (congrArg (· ≫ η[D.toPre.P.A].left)
      ((Category.comp_id _).symm.trans (Over.w (toUnit (baseOver (Sp R)))))).trans (Category.id_comp _)
  have e₁ := TorusCoord.comp_eq_of_left gm.b o.b (redE R) (𝟙 _) (hob.symm.trans (Category.id_comp _).symm)
  refine ⟨o, ho, hob, fun χ => RedTotal.corr_of_levels I hL (fun W _ f => ?_) (o.isGen χ)
    (DVR.pullGen_isGen _ _ _ _ (gm.isGen χ) _) fun e z J hJ => ?_⟩
  · exact Finset.prod_congr rfl fun k _ => congrArg (fun q => f q ^ DegPre.gtε k)
      ((e₁.1 χ k).trans ((Category.id_comp _).trans (congrFun (TorusCoord.gtφT_eq o.b χ) k).symm)).symm
  · refine ((val_corr hJ (ho.2 χ) _).trans (val_one _)).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    refine Eq.trans ?_ ((hz e).2 χ z J hJ)
    have := (val_corr hJ ((U.gt e).t_unit χ) (𝟙 _)).trans (val_one _)
    rw [val_pull hJ, Category.id_comp] at this
    exact this.symm

theorem main : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)),
    IsTangent y → TanRel U.toUnifPre y gm₀ → GtTan gm₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ U y gm₀ hy h => gtTan_of_tanRel U.toUnifPre y gm₀ hy h

end GlobalTheory.MBLow.TanRed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelTangentVectorTorusPointReducesToOriginStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelTangentVector_torusPoint_reduces_to_origin : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)), IsTangent y → TanRel U.toUnifPre y gm₀ → GtTan gm₀ := by
  first | exact @GlobalTheory.MBLow.TanRed.main | exact GlobalTheory.MBLow.TanRed.main | (intros; apply GlobalTheory.MBLow.TanRed.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorSectionValueEqExpansionSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanExp

section Alg
variable {K : Type} [Field K]

theorem dualMap_fst {A : Type} [CommRing A] (f : A →+* K) (z : DualNumber A) : (dualMap f z).fst = f z.fst := by
  show (TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd) : DualNumber K).fst = _
  simp

theorem dualMap_snd {A : Type} [CommRing A] (f : A →+* K) (z : DualNumber A) : (dualMap f z).snd = f z.snd := by
  show (TrivSqZeroExt.inl (f z.fst) + TrivSqZeroExt.inr (f z.snd) : DualNumber K).snd = _
  simp

theorem dn_snd_mul (u x : DualNumber K) : (u * x).snd = u.fst * x.snd + u.snd * x.fst := by
  rw [TrivSqZeroExt.snd_mul]
  simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]

theorem unit_fst_ne (u : (DualNumber K)ˣ) : (u : DualNumber K).fst ≠ 0 := by
  intro h
  have h1 := congrArg TrivSqZeroExt.fst (Units.mul_inv u)
  rw [TrivSqZeroExt.fst_mul, h, zero_mul, TrivSqZeroExt.fst_one] at h1
  exact zero_ne_one h1

theorem unit_inv_fst (u : (DualNumber K)ˣ) : ((u⁻¹ : (DualNumber K)ˣ) : DualNumber K).fst = ((u : DualNumber K).fst)⁻¹ := by
  have h1 := congrArg TrivSqZeroExt.fst (Units.mul_inv u)
  rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_one] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem dualNumber_unit_mul_decomposition (U₁ : (DualNumber K)ˣ) (r : K) (hr : r ≠ 0) (P : DualNumber K) :
    (U₁ : DualNumber K) * P = TrivSqZeroExt.inl (((U₁ : DualNumber K) * TrivSqZeroExt.inl r).fst) *
      (TrivSqZeroExt.inl (P.fst / r) + TrivSqZeroExt.inr (P.snd / r +
        ((U₁ : DualNumber K) * TrivSqZeroExt.inl r).snd / ((U₁ : DualNumber K) * TrivSqZeroExt.inl r).fst * (P.fst / r))) := by
  have hu := unit_fst_ne U₁
  have e1 := dn_snd_mul (U₁ : DualNumber K) P
  have e2 := dn_snd_mul (U₁ : DualNumber K) (TrivSqZeroExt.inl r)
  ext
  · simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    field_simp
  · rw [e1, dn_snd_mul]
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, e2, add_zero, zero_add, mul_zero]
    field_simp
    ring

theorem fst_U (Θ T ω : (DualNumber K)ˣ) (k : ℕ) (r : K) :
    (((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber K)ˣ) : DualNumber K) * TrivSqZeroExt.inl r).fst =
      (Θ : DualNumber K).fst * ((T : DualNumber K).fst)⁻¹ * (((ω : DualNumber K).fst)⁻¹) ^ k * r := by
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow,
    TrivSqZeroExt.fst_inl, unit_inv_fst]

theorem fst_eq_of (θ τ ω g m r p : K) (k : ℕ) (hτ : τ ≠ 0) (hω : ω ≠ 0) (h1 : θ * g ^ k = p) (h2 : τ * m ^ k = r)
    (h3 : ω * g = m) : θ * τ⁻¹ * ω⁻¹ ^ k * r = p := by
  subst h1 h2 h3
  rw [mul_pow, inv_pow]
  field_simp

variable {Ix : Type}

theorem ds_mul_left {f : Ix → DualNumber K} {s : DualNumber K} [TopologicalSpace K] [IsTopologicalRing K] (u : DualNumber K)
    (h : HasSum (fun a => (f a).fst) s.fst ∧ HasSum (fun a => (f a).snd) s.snd) :
    HasSum (fun a => (u * f a).fst) (u * s).fst ∧ HasSum (fun a => (u * f a).snd) (u * s).snd := by
  refine ⟨?_, ?_⟩
  · simp only [TrivSqZeroExt.fst_mul]
    exact h.1.mul_left _
  · simp only [dn_snd_mul]
    exact (h.2.mul_left _).add (h.1.mul_left _)

theorem ds_sum {n : ℕ} [TopologicalSpace K] [IsTopologicalRing K] (f : Fin n → Ix → DualNumber K) (s : Fin n → DualNumber K)
    (h : ∀ i, HasSum (fun a => (f i a).fst) (s i).fst ∧ HasSum (fun a => (f i a).snd) (s i).snd) :
    HasSum (fun a => (∑ i, f i a).fst) (∑ i, s i).fst ∧ HasSum (fun a => (∑ i, f i a).snd) (∑ i, s i).snd := by
  refine ⟨?_, ?_⟩
  · simp only [TrivSqZeroExt.fst_sum]
    exact hasSum_sum fun i _ => (h i).1
  · simp only [TrivSqZeroExt.snd_sum]
    exact hasSum_sum fun i _ => (h i).2

private theorem isChart_choose_and_symm_apply {B : Type} [CommRing B] [IsLocalRing B] {X : Scheme.{0}} (x : Sp B ⟶ X) (W : X.Opens)
    (h : x (IsLocalRing.closedPoint B) ∈ W) : ⊤ ≤ x ⁻¹ᵁ W := by
  intro p _
  have hle : (p : PrimeSpectrum B) ⤳ IsLocalRing.closedPoint B :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
  first
  | exact (hle.map x.continuous).mem_open W.isOpen h
  | exact (hle.map x.base.hom.continuous).mem_open W.isOpen h

end Alg

theorem value_at_tangent : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)) (yA : Sp (DualNumber C) ⟶ (TFK (R := V) C ⊗ A.A).left), IsTangent y → TanRel U.toUnifPre y gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → VecAt U.toUnifPre C y yA → ∀ (k : ℕ) (i₀ : A.L.ι), ⊤ ≤ (jFK (R := V) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ∃ c : C, ∀ (t : GlobalTheory.UT.SecA A C k) (s : Fam D.toPre C k), U.ExpandsF C k w₀ t s → (Summable fun α => (jc ν s gm α).fst / ν.rg ^ k) ∧ (Summable fun α => (jc ν s gm α).snd / ν.rg ^ k) ∧ valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := V) C)).U fun _ => i₀) (t.f fun _ => i₀) = TrivSqZeroExt.inl (valR (jFK (R := V) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) * (TrivSqZeroExt.inl (∑' α, (jc ν s gm α).fst / ν.rg ^ k) + TrivSqZeroExt.inr ((∑' α, (jc ν s gm α).snd / ν.rg ^ k) + c * ∑' α, (jc ν s gm α).fst / ν.rg ^ k)) := by
  intro V _ _ _ _ hV D A G _ _ hG U C _ _ _ _ _ _ hC N ν hν w₀ ρ hρ y gm₀ gm yA hy hrel hpull hvec k i₀ hi₀
  haveI : IsLocalRing (DualNumber V) := GlobalTheory.MBLow.TanLift.isLocalRing_dualNumber V
  obtain ⟨J0, hJ0⟩ := GlobalTheory.UU.exists_good_pt U.LG.isLB (Z := Sp (DualNumber V)) (IsLocalRing.closedPoint (DualNumber V))
  obtain ⟨J1, hJ1⟩ := GlobalTheory.UU.exists_good_pt D.toPre.P.isLB (Z := Sp (DualNumber V)) (IsLocalRing.closedPoint (DualNumber V))
  have hjG : ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U (J0 y.left) := isChart_choose_and_symm_apply _ _ (hJ0 y.left)
  have hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J1 ψ) := fun ψ => isChart_choose_and_symm_apply _ _ (hJ1 ψ)
  have hgt : GtTan gm₀ := GlobalTheory.T.modelTangentVector_torusPoint_reduces_to_origin V hV D A G hG U y gm₀ hy hrel
  obtain ⟨W, hW1, hW2⟩ := GlobalTheory.T.integralSectionValue_tangent_eq_adicExpansionSum V hV D A G hG U y gm₀ hy hrel k (J0 y.left) J1 hjG hJ
  obtain ⟨T, hD, hT1, hT2⟩ := GlobalTheory.T.firstJetTerms_gauge_unit_mul_baseChange V D.toPre C N ν gm₀ gm hgt hpull k J1 hJ
  obtain ⟨Θ, hΘ1, hΘ2⟩ := GlobalTheory.T.sectionValue_genericTangent_eq_unit_mul_combination V (IsLocalRing.maximalIdeal V) D A G U.toUnifPre C w₀ ρ hρ y yA hy hvec k i₀
    (J0 y.left) hi₀ hjG
  obtain ⟨ω, hω⟩ : ∃ ω : (DualNumber C)ˣ, (ω : DualNumber C) = dualMap (toF V C) (W : DualNumber V) :=
    ⟨Units.map (dualMap (toF V C)).toMonoidHom W, rfl⟩
  have hωfst : (ω : DualNumber C).fst = toF V C (W : DualNumber V).fst := by rw [hω, dualMap_fst]
  have h3 : (ω : DualNumber C).fst * toF V C (rigVal U.LG (J0 y.left)) =
      toF V C (rigValD D.toPre (J1 gm₀.b.left)) := by
    rw [hωfst, ← map_mul, hW1]
  have hinj : Function.Injective (toF V C) := by
    show Function.Injective ((algebraMap (FractionRing V) C).comp (algebraMap V (FractionRing V)))
    rw [RingHom.coe_comp]
    exact (algebraMap (FractionRing V) C).injective.comp (IsFractionRing.injective V (FractionRing V))
  have hm : toF V C (rigValD D.toPre (J1 gm₀.b.left)) ≠ 0 := by
    intro h0
    apply hD
    apply hinj
    rw [h0, map_zero]
  have hτ := unit_fst_ne T
  have hωne := unit_fst_ne ω
  have hr : ν.rg ^ k ≠ 0 := by
    rw [← hT1]
    exact mul_ne_zero hτ (pow_ne_zero _ hm)
  have hfst := (fst_U Θ T ω k (ν.rg ^ k)).trans (fst_eq_of _ _ _ _ _ _ _ k hτ hωne hΘ1 hT1 h3)
  refine ⟨(((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * TrivSqZeroExt.inl (ν.rg ^ k)).snd /
    (((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * TrivSqZeroExt.inl (ν.rg ^ k)).fst, ?_⟩
  intro t s hts
  obtain ⟨σ', hcar, n, cc, σ, fa, hexp, hlin, hslin⟩ := hts
  have hA : ∀ i, HasSum (fun α => (dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α)))).fst)
        (dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))).fst ∧
      HasSum (fun α => (dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α)))).snd)
        (dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))).snd := by
    intro i
    obtain ⟨h1, h2⟩ := GlobalTheory.T.hasSum_dualNumber_coords_of_adicSum V (IsLocalRing.maximalIdeal V) C hC _ _ (hW2 (σ i) (fa i) (hexp i))
    simp only [dualMap_fst, dualMap_snd]
    exact ⟨(Equiv.hasSum_iff (f := fun β => toF V C (termV J1 gm₀ (fa i β)).fst) ν.eX.toEquiv).2 h1,
      (Equiv.hasSum_iff (f := fun β => toF V C (termV J1 gm₀ (fa i β)).snd) ν.eX.toEquiv).2 h2⟩
  have hB := ds_mul_left (T : DualNumber C)
    (ds_sum (fun i α => TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (termV J1 gm₀ (fa i (ν.eX α))))
      _ (fun i => ds_mul_left (TrivSqZeroExt.inl (cc i)) (hA i)))
  have hjc := hT2 s n cc fa hslin
  simp only [← hjc] at hB
  obtain ⟨hf, hs⟩ := hB
  have hS : ((Θ * T⁻¹ * ω⁻¹ ^ k : (DualNumber C)ˣ) : DualNumber C) * ((T : DualNumber C) *
      ∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) ((W : DualNumber V) ^ k * valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) =
      (Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left)) := by
    simp only [map_mul, map_pow, ← hω]
    have e1 : ∀ i, TrivSqZeroExt.inl (cc i) * ((ω : DualNumber C) ^ k * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) =
        (ω : DualNumber C) ^ k * (TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) :=
      fun i => by ring
    simp only [e1, ← Finset.mul_sum]
    have hb : ((T⁻¹ : (DualNumber C)ˣ) : DualNumber C) * (T : DualNumber C) = 1 := Units.inv_mul T
    have hw : ((ω⁻¹ : (DualNumber C)ˣ) : DualNumber C) ^ k * (ω : DualNumber C) ^ k = 1 := by
      rw [← mul_pow, Units.inv_mul, one_pow]
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination ((Θ : DualNumber C) * (∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) *
        ((ω⁻¹ : (DualNumber C)ˣ) : DualNumber C) ^ k * (ω : DualNumber C) ^ k) * hb +
      ((Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (cc i) * dualMap (toF V C) (valR y.left
          (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J0 y.left) ((σ i).f fun _ => J0 y.left))) * hw
  refine ⟨(hf.div_const _).summable, (hs.div_const _).summable, ?_⟩
  rw [(hf.div_const _).tsum_eq, (hs.div_const _).tsum_eq, hΘ2 t σ' hcar n cc σ hlin, ← hS, dualNumber_unit_mul_decomposition _ _ hr, hfst]

end GlobalTheory.MBLow.TanExp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorSectionValueEqExpansionSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.tangentVector_section_value_eq_expansion_sum : AllVC fun {V} _ _ _ {D} {A} {G} _ _ U {C} _ _ {N} ν => ∀ (w₀ : GlobalTheory.UT.W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)) (yA : Sp (DualNumber C) ⟶ (TFK (R := V) C ⊗ A.A).left), IsTangent y → TanRel U.toUnifPre y gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → VecAt U.toUnifPre C y yA → ∀ (k : ℕ) (i₀ : A.L.ι), ⊤ ≤ (jFK (R := V) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ∃ c : C, ∀ (t : GlobalTheory.UT.SecA A C k) (s : Fam D.toPre C k), U.ExpandsF C k w₀ t s → (Summable fun α => (jc ν s gm α).fst / ν.rg ^ k) ∧ (Summable fun α => (jc ν s gm α).snd / ν.rg ^ k) ∧ valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := V) C)).U fun _ => i₀) (t.f fun _ => i₀) = TrivSqZeroExt.inl (valR (jFK (R := V) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) * (TrivSqZeroExt.inl (∑' α, (jc ν s gm α).fst / ν.rg ^ k) + TrivSqZeroExt.inr ((∑' α, (jc ν s gm α).snd / ν.rg ^ k) + c * ∑' α, (jc ν s gm α).fst / ν.rg ^ k)) := by
  first | exact @GlobalTheory.MBLow.TanExp.value_at_tangent | exact GlobalTheory.MBLow.TanExp.value_at_tangent | (intros; apply GlobalTheory.MBLow.TanExp.value_at_tangent <;> assumption) | exact @GlobalTheory.MBLow.TanExp.ds_sum | exact GlobalTheory.MBLow.TanExp.ds_sum | (intros; apply GlobalTheory.MBLow.TanExp.ds_sum <;> assumption)
end
