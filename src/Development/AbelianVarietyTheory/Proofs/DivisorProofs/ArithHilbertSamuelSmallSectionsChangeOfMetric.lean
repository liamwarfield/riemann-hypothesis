module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArCalcOfPrincipalisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupNormBallCountAsymptoticGramDeterminant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogDetGramChangeSemiPositiveMetric

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogSectionCountChangeOfMetric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVolumeDensityChartProjArith
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVolumeDensityChartProjArith
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

theorem exists_volDens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → GenSmooth p D → ∀ σ : k →+* ℂ, Nonempty (VolDens p σ D) := by
  intro k _ X _ p D hX hS σ
  haveI := hX.compactSpace σ
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := hS σ
  obtain ⟨s, hs⟩ := R.exists_finite
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate (X := CxPts p σ) (ι := s) isClosed_univ
    (fun i => (R.chart i.1).e.source) (fun i => (R.chart i.1).e.open_source)
    (fun y _ => by
      obtain ⟨i, hi, hy⟩ := hs y
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hy⟩)
  have hsrc : ∀ (i : s) (y : CxPts p σ), f i y ≠ 0 → y ∈ (R.chart i.1).e.source := fun i y h =>
    hf i (subset_tsupport _ h)
  refine ⟨{ dens := fun c y => ∑ i : s, f i y * ‖ChartGlue.transDet c.e (R.chart i.1).e y‖ ^ 2
            cont := fun c => ?_
            pos := fun c y hy => ?_
            trans := fun c c' y hy hy' => ?_ }⟩
  · refine continuousOn_finsetSum _ fun i _ => fun y hy => ContinuousAt.continuousWithinAt ?_
    by_cases h : y ∈ tsupport (f i)
    · exact (f i).continuous.continuousAt.mul
        ((CurveDens.continuousAt_transDet_chart c _ hy (hf i h)).norm.pow 2)
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h] with z hz
      rw [hz, Pi.zero_apply, zero_mul]
  · obtain ⟨i, hi⟩ := f.exists_pos (Set.mem_univ y)
    refine Finset.sum_pos' (fun j _ => mul_nonneg (f.nonneg j y) (sq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos hi (pow_pos (norm_pos_iff.2 ?_) 2)⟩
    exact CurveDens.transDet_chart_ne_zero c _ hy (hsrc i y hi.ne')
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : f i y = 0
    · simp [h]
    · rw [CurveDens.transDet_trans_chart c c' _ hy hy' (hsrc i y h), norm_mul, mul_pow]
      ring

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVolumeDensityChartProjArithStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothVolumeDensityChart_projArith : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ σ : k →+* ℂ, Nonempty (VolDens p σ D) := by
  first | exact @GlobalTheory.HSAmp.exists_volDens | exact GlobalTheory.HSAmp.exists_volDens | (intros; apply GlobalTheory.HSAmp.exists_volDens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogSectionCountChangeOfMetric
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_intBasis {K : Type} [Field K] [CharZero K] (Λ : AddSubgroup K) (hΛ : Λ.FG) :
    ∃ f : Fin (Module.finrank ℤ Λ) → K, LinearIndependent ℤ f ∧ AddSubgroup.closure (Set.range f) = Λ ∧
      ∀ i, f i ∈ Λ := by
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg Λ).2 hΛ)
  haveI : Module.Free ℤ Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ Λ
  refine ⟨fun i => (b i : K), ?_, le_antisymm ?_ ?_, fun i => (b i).2⟩
  · exact b.linearIndependent.map' Λ.subtype.toIntLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · exact (AddSubgroup.closure_le _).2 (Set.range_subset_iff.2 fun i => (b i).2)
  · intro x hx
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    change _ = x at h
    rw [← h, AddSubmonoidClass.coe_finsetSum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [AddSubgroupClass.coe_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (f := fun i => (b i : K)) i)) _

theorem tendsto_logCount_sub_up : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → ∀ Λ : ℕ → AddSubgroup X.functionField, GoodFam P D (gdeg P.L D / D.factorial) Λ → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  intro HA k _ X _ p D hX hS P a hP ha Λ hΛ
  obtain ⟨C, hC1, hCs⟩ := hΛ.small
  refine ⟨Real.log C + 1, ?_⟩
  intro u B a' hB hu hup ha' t ht
  have := hX.charZero
  haveI : CharZero X.functionField :=
    charZero_of_injective_ringHom (germ_injective_of_isIntegral X (U := ⊤) _ trivial)
  choose f hli hcl hmemΛ using fun m => exists_intBasis (Λ m) (hΛ.fg m)
  let ω : ∀ σ, VolDens p σ D := fun σ => Classical.choice (GlobalTheory.T.exists_smoothVolumeDensityChart_projArith k X p D hX hS σ)
  have hmem : ∀ (m : ℕ) i, f m i ∈ P.H m 1 := fun m i => hΛ.le m (hmemΛ m i)
  have hmem' : ∀ (m : ℕ) i, f m i ∈ (upperParabolic P u).H m 1 := fun m i => by
    rw [(GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).1]; exact hmem m i
  have hC1' : 1 ≤ C * Real.exp B := one_le_mul_of_one_le_of_one_le hC1 (Real.one_le_exp hB)
  have hlog : Real.log (C * Real.exp B) = Real.log C + B := by
    rw [Real.log_mul (by positivity) (Real.exp_pos B).ne', Real.log_exp]
  have hs : ∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤
      AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (C ^ m)) := by
    intro m hm; rw [hcl m]; exact hCs m hm
  have hs' : ∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤
      AddSubgroup.closure (ballIn (upperParabolic P u) (AddSubgroup.closure (Set.range (f m))) m 1 ((C * Real.exp B) ^ m)) := by
    intro m hm
    rw [hcl m]
    refine (hCs m hm).trans (AddSubgroup.closure_mono ?_)
    rintro x ⟨hx, hb⟩
    refine ⟨hx, fun σ y => ?_⟩
    rw [((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).2.2 σ y x).2]
    have h0 : 0 ≤ P.nu m 1 σ y x := by rw [← norm_val]; exact norm_nonneg _
    rw [mul_pow, ← Real.exp_nat_mul]
    refine mul_le_mul (hb σ y) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by positivity)
    have hu' := (abs_le.1 (hu σ y)).1
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left (neg_le.1 hu') hm0, mul_nonneg hm0 hB]
  have h1 := GlobalTheory.T.supNormBall_count_asymptotic_gramDeterminant k X p D hX hS P hP ω _ f hmem hli _ hΛ.rank C hC1 hs t (by linarith)
  have h2 := GlobalTheory.T.supNormBall_count_asymptotic_gramDeterminant k X p D hX hS (upperParabolic P u) hup ω _ f hmem' hli _ hΛ.rank (C * Real.exp B) hC1' hs' t
    (by rw [hlog]; linarith)
  have h3 := GlobalTheory.T.tendsto_logDet_gram_change_semiPositive_metric HA k X p D hX hS P hP ω _ f hmem hli hΛ.rank u a a' hup ha ha'
  simp only [hcl] at h1 h2
  have key := (h2.sub h1).add (h3.div_const 2)
  convert key using 1
  · funext m; ring
  · congr 1; ring

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogSectionCountChangeOfMetricStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_logSectionCount_change_of_metric : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → ∀ Λ : ℕ → AddSubgroup X.functionField, GoodFam P D (gdeg P.L D / D.factorial) Λ → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  first | exact @GlobalTheory.HSAmp.tendsto_logCount_sub_up | exact GlobalTheory.HSAmp.tendsto_logCount_sub_up | (intros; apply GlobalTheory.HSAmp.tendsto_logCount_sub_up <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullbackGenericallyBirational
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullbackGenericallyBirational
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SemiPullBir

theorem exists_isIso_restrict {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    [IsSeparated π] [LocallyOfFiniteType π] (hη : π (genericPoint Y) = genericPoint X)
    (hd : π.residueDegree (genericPoint Y) = 1) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsIso (π ∣_ U) := by
  have hFX : IsField (X.presheaf.stalk (π (genericPoint Y))) := by
    rw [hη]
    exact Field.toIsField X.functionField
  have hFY : IsField (Y.presheaf.stalk (genericPoint Y)) := Field.toIsField Y.functionField
  have hrX : Function.Bijective (X.residue (π (genericPoint Y))).hom := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    letI := hFX.toField
    exact RingHom.injective _
  have hrY : Function.Bijective (Y.residue (genericPoint Y)).hom := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    letI := hFY.toField
    exact RingHom.injective _
  have hκ : Function.Bijective (π.residueFieldMap (genericPoint Y)).hom := by
    letI := (π.residueFieldMap (genericPoint Y)).hom.toAlgebra
    have h1 : Module.finrank (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) = 1 := hd
    refine ⟨RingHom.injective _, fun y => ?_⟩
    have htop := Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h1
    have hy : y ∈ (⊥ : Subalgebra (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y))) := by
      rw [htop]; exact Algebra.mem_top
    obtain ⟨a, ha⟩ := Algebra.mem_bot.1 hy
    exact ⟨a, ha⟩
  have hst : Function.Bijective (π.stalkMap (genericPoint Y)).hom := by
    have e := Scheme.residue_residueFieldMap (f := π) (genericPoint Y)
    have e' : (Y.residue (genericPoint Y)).hom.comp (π.stalkMap (genericPoint Y)).hom =
        (π.residueFieldMap (genericPoint Y)).hom.comp (X.residue (π (genericPoint Y))).hom := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← e]
    have hc : Function.Bijective ((Y.residue (genericPoint Y)).hom.comp (π.stalkMap (genericPoint Y)).hom) := by
      rw [e']; exact hκ.comp hrX
    refine (Function.Bijective.of_comp_iff' hrY _).1 hc
  have : IsIso (π.stalkMap (genericPoint Y)) := (ConcreteCategory.isIso_iff_bijective _).2 hst
  let φ : Spec (X.presheaf.stalk (π (genericPoint Y))) ⟶ Y :=
    Spec.map (inv (π.stalkMap (genericPoint Y))) ≫ Y.fromSpecStalk (genericPoint Y)
  have hφ : φ ≫ π = X.fromSpecStalk (π (genericPoint Y)) ≫ 𝟙 X := by
    simp only [φ, Category.assoc, Category.comp_id]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id,
      Category.id_comp]
  obtain ⟨U, hU, g, hg₁, hg₂⟩ := spread_out_of_isGermInjective' (𝟙 X) π φ hφ
  rw [Category.comp_id] at hg₂
  have : IsDominant (Y.fromSpecStalk (genericPoint Y)) :=
    ⟨((dense_iff_closure_eq.2 (genericPoint_spec Y)).mono
      (Set.singleton_subset_iff.2 ⟨_, Scheme.fromSpecStalk_closedPoint⟩))⟩
  have : IsDominant φ := inferInstance
  have : IsDominant g := by
    rw [hg₁] at this
    exact IsDominant.of_comp (U.fromSpecStalkOfMem _ hU) g
  exact ⟨U, ⟨_, hU⟩, GlobalTheory.ZH.isIso_morphismRestrict_of_local_dominant_sections π U fun y hy =>
    ⟨U, U.ι, inferInstance, g, ⟨⟨y, hy⟩, rfl⟩, by simp, ‹_›, hg₂⟩⟩

theorem semiPos_pull : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) = 1 → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  intro k _ X _ p D hp Y _ q hq π hπ hη hd L hL
  have hpr : IsProper q := GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver
  have hsep : IsSeparated (π ≫ p) := by rw [hπ]; infer_instance
  have hft : LocallyOfFiniteType (π ≫ p) := by rw [hπ]; infer_instance
  have : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  obtain ⟨U, hU, hi⟩ := exists_isIso_restrict π hη hd
  exact (GlobalTheory.SemiPosBir.semiPos_iff_pull k X Y p q D hp hq π hπ U hU hi L).1 hL

end GlobalTheory.SemiPullBir
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullbackGenericallyBirationalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPos_pullback_generically_birational : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) = 1 → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  first | exact @GlobalTheory.SemiPullBir.semiPos_pull | exact GlobalTheory.SemiPullBir.semiPos_pull | (intros; apply GlobalTheory.SemiPullBir.semiPos_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DominantProjArithSurjectiveComplexPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DominantProjArithSurjectiveComplexPoints
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.DomSurj

open CategoryTheory.Limits

theorem isProper_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProper f := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  infer_instance

theorem surjective_cxPts_map : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (E : ℕ), IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map π hπ (spMap σ) : CxPts q σ → CxPts p σ) := by
  intro k _ X _ p D hX Y _ q E hY π hπ hgen σ x
  have := isProper_of_projOver hX.isProjOver
  have : IsProper (π ≫ p) := hπ ▸ isProper_of_projOver hY.isProjOver
  have : IsProper π := IsProper.of_comp π p

  have hsurj : Function.Surjective π := by
    have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
    have hall : Set.range π = Set.univ := by
      rw [← Set.univ_subset_iff, ← genericPoint_closure X, hcl.closure_subset_iff]
      exact Set.singleton_subset_iff.2 ⟨_, hgen⟩
    exact Set.range_eq_univ.1 hall
  obtain ⟨y, hy⟩ := hsurj (x.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x.1) y
    (IsLocalRing.closedPoint ℂ) hy
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x.1)
  obtain ⟨c, -, hc'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(Limits.pullback π x.1)))
    ⟨z, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨⟨pointOfClosedPoint (pullback.snd π x.1) c hc ≫ pullback.fst π x.1, ?_⟩, Subtype.ext ?_⟩
  · rw [← hπ, ← Category.assoc, Category.assoc _ _ π, pullback.condition,
      ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp, x.2]
  · show (pointOfClosedPoint (pullback.snd π x.1) c hc ≫ pullback.fst π x.1) ≫ π = x.1
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

end GlobalTheory.DomSurj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DominantProjArithSurjectiveComplexPointsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_projArith_surjective_complexPoints : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (E : ℕ), IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map π hπ (spMap σ) : CxPts q σ → CxPts p σ) := by
  first | exact @GlobalTheory.DomSurj.surjective_cxPts_map | exact GlobalTheory.DomSurj.surjective_cxPts_map | (intros; apply GlobalTheory.DomSurj.surjective_cxPts_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermLineBundlePairPullbackDominant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermLineBundlePairPullbackDominant
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

open GlobalTheory.TrueGeo.SmallSec

theorem pair_pull : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (Y : Scheme.{0})
    [IsIntegral Y] (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X →
    ∀ P : Pair p, ∃ (Q : Pair q) (e : X.functionField →+* Y.functionField), Q.L = P.L.pull π hπ ∧
      Q.A = P.A.pull π hπ ∧ ∀ (a b : ℤ), ∀ f ∈ P.H a b, e f ∈ Q.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts q σ),
        Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map π hπ _ y) f := by
  intro k _ X _ p Y _ q π hπ hgen P
  subst hπ
  have hη : π (genericPoint Y) ⤳ genericPoint X := hgen ▸ specializes_rfl
  let Q : Pair (π ≫ p) :=
    ⟨P.L.pull π rfl, P.A.pull π rfl, _, _, MultPull.isRatSec_pull_map π hη P.hr,
      MultPull.isRatSec_pull_map π hη P.hr'⟩
  have hloc : ∀ (a b : ℤ) (f : X.functionField) (i : Q.L.B.ι) (j : Q.A.B.ι),
      Q.loc a b (fnMap π hη f) i j = fnMap π hη (P.loc a b f (i PUnit.unit) (j PUnit.unit)) := by
    intro a b f i j
    simp only [Pair.loc, map_mul, map_zpow₀]
    rfl
  have hmem : ∀ (a b : ℤ), ∀ f ∈ P.H a b, fnMap π hη f ∈ Q.H a b := by
    intro a b f hf x i j hi hj
    rw [hloc]
    exact FrameGlue.Pull.regAt_fnMap π hη
      (hf (π x) (i PUnit.unit) (j PUnit.unit) (Set.mem_iInter.1 hi PUnit.unit) (Set.mem_iInter.1 hj PUnit.unit))
  refine ⟨Q, fnMap π hη, rfl, rfl, fun a b f hf => ⟨hmem a b f hf, fun σ y => ?_⟩⟩
  let z := Points.PtsOver.map π (rfl : π ≫ p = π ≫ p) (spMap σ) y
  set i0 := pick (P.L.φ σ).isLB z
  set j0 := pick (P.A.φ σ).isLB z
  have hi0 : z ∈ ptsIn p σ (P.L.B.U i0) := mem_pick _ z
  have hj0 : z ∈ ptsIn p σ (P.A.B.U j0) := mem_pick _ z
  have hi : y ∈ ptsIn (π ≫ p) σ (Q.L.B.U fun _ => i0) :=
    mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hi0)
  have hj : y ∈ ptsIn (π ≫ p) σ (Q.A.B.U fun _ => j0) :=
    mem_ptsIn.2 (Set.mem_iInter.2 fun _ => mem_ptsIn.1 hj0)
  have hreg : RegAt (under z) (P.loc a b f i0 j0) :=
    hf (under z) i0 j0 (mem_ptsIn.1 hi0) (mem_ptsIn.1 hj0)
  have hval : ratVal (fnMap π hη (P.loc a b f i0 j0)) y = ratVal (P.loc a b f i0 j0) z := by
    show ratVal (fnMap π hη (P.loc a b f i0 j0)) y = ratVal (P.loc a b f i0 j0)
      (Points.PtsOver.map π (rfl : π ≫ p = π ≫ p) (spMap σ) y)
    rw [ratVal_eq_valAt y (FrameGlue.Pull.regAt_fnMap π hη hreg), valAt_fnMap π hη _ hreg,
      ratVal_eq_valAt _ hreg]
    rfl
  rw [GlobalTheory.VolBr.nu_eq k Y (π ≫ p) Q a b _ (hmem a b f hf) σ y _ _ hi hj,
    GlobalTheory.VolBr.nu_eq k X p P a b f hf σ z i0 j0 hi0 hj0]
  erw [hloc a b f (fun _ => i0) (fun _ => j0), hval]
  erw [(P.L.φ σ).pull_φ π rfl (fun _ => i0) y, (P.A.φ σ).pull_φ π rfl (fun _ => j0) y]

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermLineBundlePairPullbackDominantStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermLineBundlePair_pullback_dominant : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ P : Pair p, ∃ (Q : Pair q) (e : X.functionField →+* Y.functionField), Q.L = P.L.pull π hπ ∧ Q.A = P.A.pull π hπ ∧ ∀ (a b : ℤ), ∀ f ∈ P.H a b, e f ∈ Q.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts q σ), Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map π hπ _ y) f := by
  first | exact @GlobalTheory.HSAmp.pair_pull | exact GlobalTheory.HSAmp.pair_pull | (intros; apply GlobalTheory.HSAmp.pair_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelSmallSectionsChangeOfMetric
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.ChangeSing

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
  {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem up_pull_isometric (L : HermLB p) (u : SmFn p) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q) :
    (up (L.pull ρ hρ) (u.pull ρ hρ)).Isometric ((up L u).pull ρ hρ) := by
  refine HermLB.isometric_of_eqOn ?_
  intro σ a y _
  erw [Weight.pull_φ]
  exact (congrArg (· + u.u σ (Points.PtsOver.map ρ hρ (spMap σ) y)) (Weight.pull_φ (L.φ σ) ρ hρ a y)).symm

theorem ballIn_map (P : Pair p) (Q : Pair q) (e : X.functionField →+* Y.functionField) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q)
    (hs : ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map ρ hρ (spMap σ) : CxPts q σ → CxPts p σ))
    (Λ : AddSubgroup X.functionField) (a b : ℤ)
    (hn : ∀ f ∈ Λ, ∀ (σ : k →+* ℂ) (y : CxPts q σ), Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map ρ hρ (spMap σ) y) f)
    (R : ℝ) : ballIn Q (Λ.map e.toAddMonoidHom) a b R = e '' ballIn P Λ a b R := by
  ext g
  constructor
  · rintro ⟨⟨f, hf, rfl⟩, hR⟩
    refine ⟨f, ⟨hf, fun σ x => ?_⟩, rfl⟩
    obtain ⟨y, rfl⟩ := hs σ x
    rw [← hn f hf σ y]
    exact hR σ y
  · rintro ⟨f, ⟨hf, hR⟩, rfl⟩
    refine ⟨⟨f, hf, rfl⟩, fun σ y => ?_⟩
    rw [hn f hf σ y]
    exact hR σ _

theorem ncard_ballIn_map (P : Pair p) (Q : Pair q) (e : X.functionField →+* Y.functionField) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q)
    (hs : ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map ρ hρ (spMap σ) : CxPts q σ → CxPts p σ))
    (Λ : AddSubgroup X.functionField) (a b : ℤ)
    (hn : ∀ f ∈ Λ, ∀ (σ : k →+* ℂ) (y : CxPts q σ), Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map ρ hρ (spMap σ) y) f)
    (R : ℝ) : (ballIn Q (Λ.map e.toAddMonoidHom) a b R).ncard = (ballIn P Λ a b R).ncard := by
  rw [ballIn_map P Q e ρ hρ hs Λ a b hn R]
  exact Set.ncard_image_of_injective _ e.injective

theorem goodFam_map (P : Pair p) (Q : Pair q) (e : X.functionField →+* Y.functionField) (ρ : Y ⟶ X) (hρ : ρ ≫ p = q)
    (hs : ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map ρ hρ (spMap σ) : CxPts q σ → CxPts p σ))
    (he : ∀ (a b : ℤ), ∀ f ∈ P.H a b, e f ∈ Q.H a b ∧ ∀ (σ : k →+* ℂ) (y : CxPts q σ),
      Q.nu a b σ y (e f) = P.nu a b σ (Points.PtsOver.map ρ hρ (spMap σ) y) f)
    (D : ℕ) (g : ℝ) (Λ : ℕ → AddSubgroup X.functionField) (h : GoodFam P D g Λ) :
    GoodFam Q D g (fun m => (Λ m).map e.toAddMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    rintro _ ⟨f, hf, rfl⟩
    exact (he m 1 f (h.le m hf)).1
  · intro m
    obtain ⟨s, hs', hsFinite⟩ := (AddSubgroup.fg_iff (Λ m)).mp (h.fg m)
    refine (AddSubgroup.fg_iff _).mpr ⟨e '' s, ?_, hsFinite.image e⟩
    rw [← hs', AddMonoidHom.map_closure]
    rfl
  · obtain ⟨C, hC, hCm⟩ := h.small
    refine ⟨C, hC, fun m hm => ?_⟩
    have hn : ∀ f ∈ Λ m, ∀ (σ : k →+* ℂ) (y : CxPts q σ),
        Q.nu m 1 σ y (e f) = P.nu m 1 σ (Points.PtsOver.map ρ hρ (spMap σ) y) f :=
      fun f hf => (he m 1 f (h.le m hf)).2
    rw [ballIn_map P Q e ρ hρ hs (Λ m) m 1 hn]
    exact (AddSubgroup.map_mono (hCm m hm)).trans
      (AddMonoidHom.map_closure e.toAddMonoidHom (ballIn P (Λ m) m 1 (C ^ m))).le
  · have e' : ∀ m, Module.finrank ℤ ((Λ m).map e.toAddMonoidHom) = Module.finrank ℤ (Λ m) := fun m =>
      ((AddSubgroup.equivMapOfInjective (Λ m) e.toAddMonoidHom e.injective).toIntLinearEquiv.finrank_eq).symm
    simp only [e']
    exact h.rank

end GlobalTheory.HSAmp.ChangeSing

namespace GlobalTheory.HSAmp.ChangeSing

theorem count_change_of_principalisation : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → GoodFam P D (gdeg P.L D / D.factorial) (fun m => P.H m 1) → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  intro hPr k _ X _ p D hX P a hsp hsi hgf
  have hC : Published.ArCalc := MixHt.arCalc_of_principalisation hPr
  obtain ⟨Y, hY, ρ, hYa, hYs, hgen, hdeg⟩ := GenRes.exists_birational_genSmooth hPr k X p D hX
  obtain ⟨Q, e, hQL, -, he⟩ := T.exists_hermLineBundlePair_pullback_dominant k X p Y (ρ ≫ p) ρ rfl hgen P
  have hs : ∀ σ : k →+* ℂ, Function.Surjective
      (Points.PtsOver.map ρ rfl (spMap σ) : CxPts (ρ ≫ p) σ → CxPts p σ) :=
    T.dominant_projArith_surjective_complexPoints k X p D hX Y (ρ ≫ p) D hYa ρ rfl hgen
  have hne : ρ.residueDegree (genericPoint Y) ≠ 0 := by rw [hdeg]; exact one_ne_zero
  have hproj := hC.2.2.2.2.1 k X Y p (ρ ≫ p) D hX hYa ρ rfl hgen hne
  have hdeg' : ((ρ.residueDegree (genericPoint Y) : ℕ) : ℝ) = 1 := by rw [hdeg]; simp
  have hQsp : Q.L.SemiPos D := by
    rw [hQL]; exact T.semiPos_pullback_generically_birational k X p D hX Y (ρ ≫ p) hYa ρ rfl hgen hdeg P.L hsp
  have hQsi : Q.L.IsSelfInter a := by
    have h := hproj.1 P.L a hsi
    rw [hdeg', one_mul] at h
    rw [hQL]; exact h
  have hQg : gdeg Q.L D = gdeg P.L D := by
    rw [hQL, CovTest.gdegPull k X Y p (ρ ≫ p) D hX hYa ρ rfl hgen hne, hdeg', one_mul]
  have hgf' := goodFam_map P Q e ρ rfl hs he D _ _ hgf
  rw [← hQg] at hgf'
  obtain ⟨t₀, ht⟩ := T.tendsto_logSectionCount_change_of_metric hC k Y (ρ ≫ p) D hYa hYs Q a hQsp hQsi _ hgf'
  refine ⟨t₀, fun u B a' hB hu husp husi t ht' => ?_⟩
  have hiso : (up Q.L (u.pull ρ rfl)).Isometric ((up P.L u).pull ρ rfl) := by
    rw [hQL]; exact up_pull_isometric P.L u ρ rfl
  have h1 : (up Q.L (u.pull ρ rfl)).SemiPos D :=
    HermLB.Isometric.semiPos _ _ D hiso.symm (T.semiPos_pullback_generically_birational k X p D hX Y (ρ ≫ p) hYa ρ rfl hgen hdeg _ husp)
  have h2 : (up Q.L (u.pull ρ rfl)).IsSelfInter a' := by
    have h := hproj.1 (up P.L u) a' husi
    rw [hdeg', one_mul] at h
    exact hiso.symm.isSelfInter hYa h
  have h3 := ht (u.pull ρ rfl) B a' hB (fun σ y => hu σ _) h1 h2 t ht'
  have hnP : ∀ m : ℕ, ∀ f ∈ P.H (m : ℤ) 1, ∀ (σ : k →+* ℂ) (y : CxPts (ρ ≫ p) σ),
      Q.nu m 1 σ y (e f) = P.nu m 1 σ (Points.PtsOver.map ρ rfl (spMap σ) y) f :=
    fun m f hf => (he m 1 f hf).2
  have hnU : ∀ m : ℕ, ∀ f ∈ P.H (m : ℤ) 1, ∀ (σ : k →+* ℂ) (y : CxPts (ρ ≫ p) σ),
      (upperParabolic Q (u.pull ρ rfl)).nu m 1 σ y (e f) =
        (upperParabolic P u).nu m 1 σ (Points.PtsOver.map ρ rfl (spMap σ) y) f := by
    intro m f hf σ y
    rw [((T.raiseFirstWeight_sections_loci_values_norms k Y (ρ ≫ p) Q (u.pull ρ rfl) m 1).2.2 σ y (e f)).2,
      ((T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).2.2 σ _ f).2, hnP m f hf σ y]
    rfl
  refine h3.congr fun m => ?_
  rw [ncard_ballIn_map (upperParabolic P u) (upperParabolic Q (u.pull ρ rfl)) e ρ rfl hs _ _ _ (hnU m),
    ncard_ballIn_map P Q e ρ rfl hs _ _ _ (hnP m)]

end GlobalTheory.HSAmp.ChangeSing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelSmallSectionsChangeOfMetricStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHilbertSamuel_smallSections_change_of_metric : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → GoodFam P D (gdeg P.L D / D.factorial) (fun m => P.H m 1) → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (P.H m 1) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  first | exact @GlobalTheory.HSAmp.ChangeSing.count_change_of_principalisation | exact GlobalTheory.HSAmp.ChangeSing.count_change_of_principalisation | (intros; apply GlobalTheory.HSAmp.ChangeSing.count_change_of_principalisation <;> assumption)
end
