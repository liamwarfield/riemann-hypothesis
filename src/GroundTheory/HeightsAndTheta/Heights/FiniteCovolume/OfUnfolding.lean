module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Assembly
public import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.LinearIndependentRealOfInt
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineNormalForm
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTorusModulus
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchimedeanUnitaryEquiv

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoordLatticeFullRank
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField Module

noncomputable section

variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]

theorem CoordLatticeFullRank.proof (v : Basis ι E W) : CoordLatticeFullRank.Statement v := by
  intro La hL
  set f : W →ₗ[E] ι → E := (v.equivFun : W →ₗ[E] ι → E) with hf
  refine ⟨?_, ?_⟩
  · classical
    letI := hL.fg
    infer_instance
  set S : Set (ι → E) := ((La.map f.toAddMonoidHom : AddSubgroup (ι → E)) : Set (ι → E)) with hS
  set T : Submodule ℚ (ι → E) := Submodule.span ℚ S with hT

  have key : ∀ (a : E), ∀ s ∈ S, a • s ∈ T := by
    intro a s hs
    obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ ({a} : Finset E)
    have hda : IsIntegral ℤ (d • a) := hint a (Finset.mem_singleton_self a)
    obtain ⟨x, hx, rfl⟩ := (AddSubgroup.mem_map).mp hs
    let b : 𝓞 E := ⟨d • a, hda⟩
    have hbx : ((b : E) • x) ∈ La := hL.smul_mem b x hx
    have hfb : f ((b : E) • x) ∈ S := (AddSubgroup.mem_map).mpr ⟨_, hbx, rfl⟩
    have hd' : ((d : ℚ)) ≠ 0 := by exact_mod_cast hd
    have heq : a • f.toAddMonoidHom x = ((d : ℚ)⁻¹) • f ((b : E) • x) := by
      rw [map_smul]
      show a • f x = ((d : ℚ)⁻¹) • ((d • a) • f x)
      rw [zsmul_eq_mul, mul_smul, Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul ℚ,
        smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [heq]
    exact T.smul_mem _ (Submodule.subset_span hfb)

  have stable : ∀ (a : E), ∀ y ∈ T, a • y ∈ T := by
    intro a y hy
    induction hy using Submodule.span_induction with
    | mem s hs => exact key a s hs
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact T.add_mem hy hz
    | smul q y _ hy =>
      rw [smul_comm]
      exact T.smul_mem q hy
  let T' : Submodule E (ι → E) :=
    { carrier := T
      add_mem' := fun hy hz => T.add_mem hy hz
      zero_mem' := T.zero_mem
      smul_mem' := fun a y hy => stable a y hy }
  have hspan : Submodule.span E S = ⊤ := by
    have hSim : S = f '' (La : Set W) := by
      rw [hS, AddSubgroup.coe_map]; rfl
    rw [hSim, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact v.equivFun.surjective
  have hle : Submodule.span E S ≤ T' := Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
  rw [hspan] at hle
  exact eq_top_iff.mpr fun y _ => hle (Submodule.mem_top)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldAlongSubgroup
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal Pointwise

theorem UnfoldAlongSubgroup.proof (G Y : Type*) [Group G] [MeasurableSpace G] [MeasurableSpace Y] :
    UnfoldAlongSubgroup.Statement G Y := by
  intro μ H _ ν _ _ ρ _ s hm hμ Γ _ hΓH FD FD₀ hFD hFD₀ f hf hfH
  have hms : ∀ y, Measurable (fun x : H => (x : G) * s y) := fun y =>
    hm.comp measurable_prodMk_right

  have hnull : ∀ Z : Set G, μ Z = 0 →
      ∀ᵐ y ∂ρ, ν ((fun x : H => (x : G) * s y) ⁻¹' Z) = 0 := by
    intro Z hZ
    have hZm : MeasurableSet (toMeasurable μ Z) := measurableSet_toMeasurable μ Z
    have hin : ∀ y, ∫⁻ x, (toMeasurable μ Z).indicator 1 ((x : G) * s y) ∂ν =
        ν ((fun x : H => (x : G) * s y) ⁻¹' toMeasurable μ Z) := fun y => by
      rw [← lintegral_indicator_one (hZm.preimage (hms y))]
      rfl
    have h0 := hμ ((toMeasurable μ Z).indicator 1) (measurable_one.indicator hZm)
    rw [lintegral_indicator_one hZm, measure_toMeasurable, hZ] at h0
    simp only [hin] at h0
    have hmeas : Measurable fun y => ν ((fun x : H => (x : G) * s y) ⁻¹' toMeasurable μ Z) := by
      simp only [← hin]
      exact ((measurable_one.indicator hZm).comp hm).lintegral_prod_left'
    filter_upwards [(lintegral_eq_zero_iff hmeas).1 h0.symm] with y hy
    exact measure_mono_null (Set.preimage_mono (subset_toMeasurable μ Z)) hy

  let toΓ : Γ.subgroupOf H → Γ := fun γ => ⟨((γ : H) : G), Subgroup.mem_subgroupOf.1 γ.2⟩
  have htoΓ : Function.Injective toΓ := fun a b h => by
    simp only [toΓ, Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  have : Countable (Γ.subgroupOf H) := htoΓ.countable

  have hslice : ∀ y (γ : Γ.subgroupOf H) (A : Set G),
      (fun x : H => (x : G) * s y) ⁻¹' ((toΓ γ) • A) =
        γ • ((fun x : H => (x : G) * s y) ⁻¹' A) := by
    intro y γ A
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def,
      smul_eq_mul, toΓ, InvMemClass.coe_inv, Subgroup.coe_mul, mul_assoc]

  obtain ⟨t, htFD, htm, htae⟩ := hFD.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hZ1 : μ {g | ¬ ∃ γ : Γ, γ • g ∈ FD} = 0 := ae_iff.1 hFD.ae_covers
  have hZ2 : μ (FD \ t) = 0 := (ae_eq_set.1 htae).2
  have hZ3 : ∀ γ δ : Γ, ∀ᵐ y ∂ρ, γ ≠ δ →
      ν ((fun x : H => (x : G) * s y) ⁻¹' (γ • FD ∩ δ • FD)) = 0 := by
    intro γ δ
    by_cases h : γ = δ
    · exact ae_of_all _ fun _ h' => absurd h h'
    · filter_upwards [hnull _ (hFD.aedisjoint h)] with y hy _ using hy
  have hgood : ∀ᵐ y ∂ρ, ν ((fun x : H => (x : G) * s y) ⁻¹' t) = ν FD₀ := by
    filter_upwards [hnull _ hZ1, hnull _ hZ2, ae_all_iff.2 fun γ => ae_all_iff.2 (hZ3 γ)]
      with y h1 h2 h3
    have hae : (fun x : H => (x : G) * s y) ⁻¹' t =ᵐ[ν] (fun x : H => (x : G) * s y) ⁻¹' FD := by
      refine ae_eq_set.2 ⟨?_, h2⟩
      rw [Set.sdiff_eq_empty.2 (Set.preimage_mono htFD), measure_empty]
    have hFDy : IsFundamentalDomain (Γ.subgroupOf H) ((fun x : H => (x : G) * s y) ⁻¹' FD) ν :=
      { nullMeasurableSet := (htm.preimage (hms y)).nullMeasurableSet.congr hae
        ae_covers := by
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with x hx
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_not] at hx
          obtain ⟨γ, hγ⟩ := hx
          refine ⟨⟨⟨γ, hΓH γ.2⟩, Subgroup.mem_subgroupOf.2 γ.2⟩, ?_⟩
          simpa only [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul,
            mul_assoc] using hγ
        aedisjoint := by
          intro γ δ hγδ
          change ν (γ • _ ∩ δ • _) = 0
          rw [← hslice, ← hslice, ← Set.preimage_inter]
          exact h3 _ _ (htoΓ.ne hγδ) }
    rw [measure_congr hae, hFDy.measure_eq hFD₀]
  have hsm : Measurable s := by
    convert hm.comp ((measurable_const : Measurable fun _ : Y => (1 : H)).prodMk measurable_id) using 1
    ext y
    simp
  calc ∫⁻ g in FD, f g ∂μ = ∫⁻ g in t, f g ∂μ := setLIntegral_congr htae.symm
    _ = ∫⁻ g, t.indicator f g ∂μ := (lintegral_indicator htm _).symm
    _ = ∫⁻ y, ∫⁻ x, t.indicator f ((x : G) * s y) ∂ν ∂ρ := hμ _ (hf.indicator htm)
    _ = ∫⁻ y, f (s y) * ν ((fun x : H => (x : G) * s y) ⁻¹' t) ∂ρ := by
      refine lintegral_congr fun y => ?_
      have he : (fun x : H => t.indicator f ((x : G) * s y)) =
          ((fun x : H => (x : G) * s y) ⁻¹' t).indicator fun _ => f (s y) := by
        ext x
        by_cases hx : (x : G) * s y ∈ t
        · simp [hx, hfH]
        · simp [hx]
      rw [he, lintegral_indicator_const (htm.preimage (hms y))]
    _ = ∫⁻ y, ν FD₀ * f (s y) ∂ρ := lintegral_congr_ae (by
      filter_upwards [hgood] with y hy
      rw [hy, mul_comm])
    _ = ν FD₀ * ∫⁻ y, f (s y) ∂ρ := lintegral_const_mul _ (hf.comp hsm)

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PReducedBasisBound
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module Submodule Matrix GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen

noncomputable section

theorem ReducedBasisBound.short_basis {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (m : ℕ) : ∀ lam : ℝ, 0 < lam → ∀ C : ℝ, ∃ R : ℝ,
    ∀ b : Fin m → W, LinearIndependent ℝ b → Sep (span ℤ (Set.range b)) lam →
      (gram ℝ b).det ≤ C → ∃ b' : Fin m → W, span ℤ (Set.range b') = span ℤ (Set.range b) ∧
        ∀ i, ‖b' i‖ ≤ R := by
  induction m with
  | zero => exact fun _ _ _ => ⟨0, fun b _ _ _ => ⟨b, rfl, fun i => i.elim0⟩⟩
  | succ m ih =>
    intro lam hlam C
    obtain ⟨g, hg, hgb⟩ := (bounds (W := W) m).1 (lam / 2) (half_pos hlam)
    obtain ⟨R', hR'⟩ := ih (lam / 2) (half_pos hlam) (C / lam ^ 2)
    refine ⟨|R'| + Real.sqrt (C / g), fun b hb hsep hC => ?_⟩
    obtain ⟨v, c, hvL, hv, hlv, hmin, hc, hmemc, hsepc, hdet⟩ := decompose b hb hlam hsep
    have hgc := hgb c hc hsepc
    have hv2 : ‖v‖ ^ 2 ≤ C / g := by
      rw [le_div_iff₀ hg]
      nlinarith [mul_le_mul_of_nonneg_left hgc (sq_nonneg ‖v‖)]
    have hvR : ‖v‖ ≤ Real.sqrt (C / g) := (le_abs_self _).trans (Real.abs_le_sqrt hv2)
    have hcC : (gram ℝ c).det ≤ C / lam ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : lam ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ hlam.le hlv 2
      nlinarith [hg.le.trans hgc]
    obtain ⟨c', hc'span, hc'R⟩ := hR' c hc hsepc hcC
    set L := span ℤ (Set.range b) with hL
    have hlift : ∀ i, ∃ y ∈ L, proj v y = c' i ∧ ‖y‖ ≤ ‖c' i‖ + ‖v‖ / 2 := by
      intro i
      have hci : c' i ∈ span ℤ (Set.range c) := hc'span ▸ subset_span ⟨i, rfl⟩
      obtain ⟨x, hx, hxe⟩ := (hmemc _).1 hci
      obtain ⟨y, hyL, hy, hyn⟩ := exists_lift hvL hv hx
      exact ⟨y, hyL, hy.trans hxe, hxe ▸ hyn⟩
    choose y hyL hy hyn using hlift
    refine ⟨Fin.cons v y, le_antisymm ?_ ?_, fun i => ?_⟩
    · rw [span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hvL
      · simpa using hyL j
    · intro x hx
      obtain ⟨k, hk⟩ := (mem_span_range_iff_exists_fun ℤ).1
        (hc'span ▸ (hmemc (proj v x)).2 ⟨x, hx, rfl⟩)
      have hzL : ∑ j, k j • y j ∈ L := L.sum_mem fun j _ => L.smul_mem _ (hyL j)
      have h0 : proj v (x - ∑ j, k j • y j) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, map_sum, ← hk, sub_eq_zero]
        simp [map_zsmul, hy]
      obtain ⟨n, hn⟩ := mem_zsmul_of_proj_eq_zero hvL hv hmin (L.sub_mem hx hzL) h0
      have hxe : x = n • v + ∑ j, k j • y j := by rw [← hn]; abel
      rw [hxe]
      refine add_mem (smul_mem _ _ (subset_span ⟨0, by simp⟩))
        (sum_mem fun j _ => smul_mem _ _ (subset_span ⟨j.succ, by simp⟩))
    · have hs := Real.sqrt_nonneg (C / g)
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        linarith [abs_nonneg R']
      · simp only [Fin.cons_succ]
        linarith [hyn j, hc'R j, le_abs_self R']

theorem ReducedBasisBound.proof : ReducedBasisBound.Statement := by
  intro d t c ht
  obtain ⟨R, hR⟩ := ReducedBasisBound.short_basis (W := EuclideanSpace ℝ (Fin d)) d t ht (c ^ 2)
  refine ⟨R, fun L _ _ hmin hcov => ?_⟩
  have hrk : finrank ℤ L = d := by rw [ZLattice.rank ℝ L, finrank_euclideanSpace_fin]
  let e : Basis (Fin d) ℤ L := Module.finBasisOfFinrankEq ℤ L hrk
  have hspan : span ℤ (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d))) = L := by
    rw [show (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d))) = L.subtype '' Set.range e by
      rw [← Set.range_comp]; rfl, ← Submodule.map_span, e.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hli : LinearIndependent ℝ fun i => (e i : EuclideanSpace ℝ (Fin d)) := by
    have h := (e.ofZLatticeBasis ℝ L).linearIndependent
    rwa [show ⇑(e.ofZLatticeBasis ℝ L) = fun i => (e i : EuclideanSpace ℝ (Fin d)) from
      funext fun i => e.ofZLatticeBasis_apply ℝ L i] at h
  have hdet : (gram ℝ fun i => (e i : EuclideanSpace ℝ (Fin d))).det ≤ c ^ 2 := by
    have h1 := GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram L e
    rcases le_or_gt 0 (gram ℝ fun i => (e i : EuclideanSpace ℝ (Fin d))).det with h | h
    · rw [← Real.sq_sqrt h, ← h1]
      exact pow_le_pow_left₀ (ZLattice.covolume_pos L).le hcov 2
    · nlinarith [sq_nonneg c]
  have hsep : Sep (span ℤ (Set.range fun i => (e i : EuclideanSpace ℝ (Fin d)))) t := by
    rw [hspan]; exact hmin
  obtain ⟨b', hb'span, hb'R⟩ := hR _ hli hsep hdet
  rw [hspan] at hb'span
  have htop : ⊤ ≤ span ℝ (Set.range b') := by
    rw [← IsZLattice.span_top (K := ℝ) (L := L), ← hb'span, Submodule.span_span_of_tower]
  have hliR : LinearIndependent ℝ b' :=
    linearIndependent_of_top_le_span_of_card_eq_finrank htop (by simp)
  refine ⟨(Basis.span (hliR.restrict_scalars' ℤ)).map (LinearEquiv.ofEq _ _ hb'span), fun i => ?_⟩
  simpa using hb'R i

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIntegralFormCovolume
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module MeasureTheory Matrix

noncomputable section

variable (Q V K : Type*) [AddCommGroup Q] [Module ℚ Q] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype K]

theorem IntegralFormCovolume.proof : IntegralFormCovolume.Statement Q V K := by
  classical
  intro ψ e T μ hμ hT hli hrank
  have : FiniteDimensional ℚ Q := Module.Finite.of_basis e
  have hQ : finrank ℚ Q = Fintype.card K := finrank_eq_card_basis e
  let b₀ : Basis K ℝ V := basisOfLinearIndependentOfCardEqFinrank' _ hli hrank.symm
  have hb₀ : ∀ i, b₀ i = ψ (e i) := fun i => by simp [b₀]
  have hGe : (LinearMap.BilinForm.toMatrix e T).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e).1 hT
  refine ⟨μ.real (ZSpan.fundamentalDomain b₀) ^ 2 /
    |((LinearMap.BilinForm.toMatrix e T).det : ℝ)|, ?_⟩
  intro L k hk hfg hspan _ hdual
  set M := AddSubgroup.toIntSubmodule L with hM
  have : Module.Finite ℤ M := Module.Finite.iff_fg.2 ((Submodule.fg_iff_addSubgroup_fg M).2 hfg)
  have : Module.IsTorsionFree ℤ Q := .trans_faithfulSMul ℤ ℚ Q
  have hψq : ∀ (q : ℚ) (y : Q), ψ (q • y) = (q : ℝ) • ψ y := fun q y => by
    simpa using map_ratCast_smul ψ ℚ ℝ q y

  let x₀ := Module.Free.chooseBasis ℤ M
  have hli₀ : LinearIndependent ℚ (M.subtype ∘ x₀) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).1
      (x₀.linearIndependent.map' M.subtype (Submodule.ker_subtype M))
  have hspan₀ : Submodule.span ℤ (Set.range (M.subtype ∘ x₀)) = M := by
    rw [Set.range_comp, Submodule.span_image, x₀.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspanq : Submodule.span ℚ (Set.range (M.subtype ∘ x₀)) = ⊤ := by
    rw [← Submodule.span_span_of_tower ℤ, hspan₀]
    exact hspan
  let xq₀ : Basis _ ℚ Q := Basis.mk hli₀ hspanq.ge
  let σ := Fintype.equivOfCardEq ((finrank_eq_card_basis xq₀).symm.trans hQ)
  let x := x₀.reindex σ
  let xq := xq₀.reindex σ
  have hxq : ∀ i, xq i = (x i : Q) := fun i => by simp [xq, x, xq₀]
  have hspanx : Submodule.span ℤ (Set.range fun i => xq i) = M := by
    have : (fun i => xq i) = M.subtype ∘ x := funext hxq
    rw [this, Set.range_comp, Submodule.span_image, x.span_eq, Submodule.map_top,
      Submodule.range_subtype]

  set P := e.toMatrix xq with hP
  have hψe : ∀ y, ψ y = ∑ i, (e.repr y i : ℝ) • b₀ i := fun y => by
    calc ψ y = ψ (∑ i, e.repr y i • e i) := by rw [e.sum_repr]
      _ = _ := by rw [map_sum]; simp only [hψq, hb₀]
  have hmat : b₀.toMatrix (fun j => ψ (xq j)) = P.map (Rat.cast : ℚ → ℝ) := by
    ext i j
    rw [Basis.toMatrix_apply, hψe, b₀.repr_sum_self]
    simp [P, Basis.toMatrix_apply]
  have hdetP : b₀.det (fun j => ψ (xq j)) = (P.det : ℝ) := by
    rw [Basis.det_apply, hmat]
    simpa using (RingHom.map_det (Rat.castHom ℝ) P).symm
  have hP0 : P.det ≠ 0 := by
    rw [hP, ← Basis.det_apply]
    exact (e.isUnit_det xq).ne_zero
  have hw : LinearIndependent ℝ (fun j => ψ (xq j)) :=
    ((Basis.is_basis_iff_det b₀).2 (by rw [hdetP]; exact isUnit_iff_ne_zero.2 (by exact_mod_cast hP0))).1
  let bx : Basis K ℝ V := basisOfLinearIndependentOfCardEqFinrank' _ hw hrank.symm
  have hL : AddSubgroup.toIntSubmodule (L.map ψ) = Submodule.span ℤ (Set.range bx) := by
    change M.map ψ.toIntLinearMap = _
    rw [← hspanx, Submodule.map_span, ← Set.range_comp]
    congr 1
    simp [bx, Function.comp_def]

  have hPk : P.det ^ 2 * |(LinearMap.BilinForm.toMatrix e T).det| ≤ |(k : ℚ)| ^ Fintype.card K := by
    have hG : (LinearMap.BilinForm.toMatrix xq T).det =
        P.det ^ 2 * (LinearMap.BilinForm.toMatrix e T).det := by
      rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix e xq T, det_mul, det_mul, det_transpose]
      ring
    set d := T.dualBasis hT xq
    have hd : ∀ i j, T (d i) (xq j) = if j = i then 1 else 0 :=
      LinearMap.BilinForm.apply_dualBasis_left hT xq
    have hc : ∀ i, ∃ c : K → ℤ, ∑ j, c j • xq j = k • d i := by
      intro i
      have hmem : k • d i ∈ L := hdual (d i) fun y hy => by
        have hy' : y ∈ Submodule.span ℤ (Set.range fun j => xq j) := by rw [hspanx]; exact hy
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
        exact ⟨c i, by simp [map_sum, hd]⟩
      have hmem' : k • d i ∈ Submodule.span ℤ (Set.range fun j => xq j) := by
        rw [hspanx]; exact hmem
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem'
    choose c₀ hc using hc
    set c : Matrix K K ℤ := Matrix.of c₀ with hcdef
    have hcG : c.map (Int.cast : ℤ → ℚ) * LinearMap.BilinForm.toMatrix xq T = (k : ℚ) • 1 := by
      ext i l
      have h1 := congrArg (fun y => T y (xq l)) (hc i)
      simp [hd] at h1
      rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
      simp only [Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply, hcdef, Matrix.of_apply]
      simpa [zsmul_eq_mul, eq_comm] using h1
    have hdet := congrArg Matrix.det hcG
    rw [det_mul, det_smul, det_one, mul_one, hG] at hdet
    have hcd : (c.map (Int.cast : ℤ → ℚ)).det = (c.det : ℚ) := by
      simpa using (RingHom.map_det (Int.castRingHom ℚ) c).symm
    rw [hcd] at hdet
    have hc0 : c.det ≠ 0 := by
      rintro h0
      rw [h0, Int.cast_zero, zero_mul] at hdet
      exact pow_ne_zero _ (Int.cast_ne_zero.2 hk) hdet.symm
    have h1 : (1 : ℚ) ≤ |(c.det : ℚ)| := by exact_mod_cast Int.one_le_abs hc0
    calc P.det ^ 2 * |(LinearMap.BilinForm.toMatrix e T).det|
        = |P.det ^ 2 * (LinearMap.BilinForm.toMatrix e T).det| := by
          rw [abs_mul, abs_pow, sq_abs]
      _ ≤ |(c.det : ℚ)| * |P.det ^ 2 * (LinearMap.BilinForm.toMatrix e T).det| :=
          le_mul_of_one_le_left (abs_nonneg _) h1
      _ = |(k : ℚ)| ^ Fintype.card K := by rw [← abs_mul, hdet, abs_pow]
  have hPkR : (P.det : ℝ) ^ 2 * |((LinearMap.BilinForm.toMatrix e T).det : ℝ)| ≤
      |(k : ℝ)| ^ Fintype.card K := by exact_mod_cast hPk

  rw [hL]
  refine ⟨inferInstance, inferInstance, ?_⟩
  have := hμ
  let bZ : Basis K ℤ (Submodule.span ℤ (Set.range bx)) :=
    Basis.span (bx.linearIndependent.restrict_scalars' ℤ)
  have hcoe : ((↑) ∘ bZ : K → V) = fun j => ψ (xq j) := funext fun i => by
    simp [bZ, Basis.span_apply, bx]
  rw [ZLattice.covolume_eq_det_mul_measureReal _ μ bZ b₀, hcoe, hdetP, mul_pow, sq_abs,
    div_mul_eq_mul_div, le_div_iff₀ (abs_pos.2 (by exact_mod_cast hGe))]
  calc (P.det : ℝ) ^ 2 * μ.real (ZSpan.fundamentalDomain b₀) ^ 2 *
        |((LinearMap.BilinForm.toMatrix e T).det : ℝ)|
      = μ.real (ZSpan.fundamentalDomain b₀) ^ 2 *
        ((P.det : ℝ) ^ 2 * |((LinearMap.BilinForm.toMatrix e T).det : ℝ)|) := by ring
    _ ≤ μ.real (ZSpan.fundamentalDomain b₀) ^ 2 * |(k : ℝ)| ^ Fintype.card K :=
        mul_le_mul_of_nonneg_left hPkR (sq_nonneg _)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDoubleCosetCovolume
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise

set_option linter.unusedSectionVars false

noncomputable section

section Setup

variable {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]

def doubleCosetSetoid (Φ : G ≃ₜ* G₁ × G₂) (Γ : Subgroup G) (K : Subgroup G₂) : Setoid G₂ where
  r y y' := ∃ γ ∈ Γ, ∃ k ∈ K, y' = (Φ γ).2 * y * k
  iseqv :=
    { refl := fun y => ⟨1, Γ.one_mem, 1, K.one_mem, by simp⟩
      symm := by
        rintro y y' ⟨γ, hγ, k, hk, rfl⟩
        refine ⟨γ⁻¹, Γ.inv_mem hγ, k⁻¹, K.inv_mem hk, ?_⟩
        simp [mul_assoc]
      trans := by
        rintro y y' y'' ⟨γ, hγ, k, hk, rfl⟩ ⟨γ', hγ', k', hk', rfl⟩
        refine ⟨γ' * γ, Γ.mul_mem hγ' hγ, k * k', K.mul_mem hk hk', ?_⟩
        simp [mul_assoc] }

def leftCosetSet (K : Subgroup G₂) (s : G₂) : Set G₂ := {y | s⁻¹ * y ∈ K}

theorem isOpen_leftCosetSet {K : Subgroup G₂} (hK : IsOpen (K : Set G₂)) (s : G₂) :
    IsOpen (leftCosetSet K s) :=
  hK.preimage (continuous_const_mul s⁻¹)

theorem isCompact_leftCosetSet {K : Subgroup G₂} (hK : IsCompact (K : Set G₂)) (s : G₂) :
    IsCompact (leftCosetSet K s) := by
  have : leftCosetSet K s = (s * ·) '' (K : Set G₂) := by
    rw [Set.image_mul_left]; rfl
  rw [this]
  exact hK.image (continuous_const_mul s)

def sliceMeasure (Φ : G ≃ₜ* G₁ × G₂) (μ : Measure G) (V : Set G₂) : Measure G₁ :=
  (μ.restrict (Φ ⁻¹' (univ ×ˢ V))).map fun x => (Φ x).1

variable {Φ : G ≃ₜ* G₁ × G₂} {μ : Measure G} {V : Set G₂}

theorem measurable_fst_comp (Φ : G ≃ₜ* G₁ × G₂) : Measurable fun x => (Φ x).1 :=
  (continuous_fst.comp Φ.continuous).measurable

theorem measurableSet_preimage_univ_prod (hV : IsOpen V) : MeasurableSet (Φ ⁻¹' (univ ×ˢ V)) :=
  ((isOpen_univ.prod hV).preimage Φ.continuous).measurableSet

theorem preimage_prod_eq (A : Set G₁) :
    Φ ⁻¹' (A ×ˢ V) = (fun x => (Φ x).1) ⁻¹' A ∩ Φ ⁻¹' (univ ×ˢ V) := by
  ext x
  simp [mem_prod]

theorem measure_preimage_prod_eq_restrict (hV : IsOpen V) (A : Set G₁) :
    μ (Φ ⁻¹' (A ×ˢ V)) = μ.restrict (Φ ⁻¹' (univ ×ˢ V)) ((fun x => (Φ x).1) ⁻¹' A) := by
  rw [Measure.restrict_apply' (measurableSet_preimage_univ_prod hV), preimage_prod_eq]

theorem sliceMeasure_apply (hV : IsOpen V) {A : Set G₁} (hA : MeasurableSet A) :
    sliceMeasure Φ μ V A = μ (Φ ⁻¹' (A ×ˢ V)) := by
  rw [sliceMeasure, Measure.map_apply (measurable_fst_comp Φ) hA,
    measure_preimage_prod_eq_restrict hV]

theorem measure_preimage_prod_le (hV : IsOpen V) (A : Set G₁) :
    μ (Φ ⁻¹' (A ×ˢ V)) ≤ sliceMeasure Φ μ V A := by
  rw [measure_preimage_prod_eq_restrict hV]
  exact Measure.le_map_apply (measurable_fst_comp Φ).aemeasurable A

theorem sliceMeasure_isMulLeftInvariant [μ.IsMulLeftInvariant] (hV : IsOpen V) :
    (sliceMeasure Φ μ V).IsMulLeftInvariant := by
  refine (forall_measure_preimage_mul_iff _).1 fun g A hA => ?_
  rw [sliceMeasure_apply hV (measurable_const_mul g hA), sliceMeasure_apply hV hA]
  have : Φ ⁻¹' (((g * ·) ⁻¹' A) ×ˢ V) =
      (fun x => Φ.symm (g, 1) * x) ⁻¹' (Φ ⁻¹' (A ×ˢ V)) := by
    ext x
    simp [mem_prod]
  rw [this, measure_preimage_mul]

theorem sliceMeasure_isFiniteMeasureOnCompacts [T2Space G₁] [IsFiniteMeasureOnCompacts μ]
    (hV : IsOpen V) (hVc : IsCompact V) : IsFiniteMeasureOnCompacts (sliceMeasure Φ μ V) := by
  refine ⟨fun A hA => ?_⟩
  rw [sliceMeasure_apply hV hA.isClosed.measurableSet]
  have : IsCompact (Φ ⁻¹' (A ×ˢ V)) :=
    (Homeomorph.isCompact_preimage Φ.toHomeomorph).2 (hA.prod hVc)
  exact this.measure_lt_top

variable [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [μ.IsHaarMeasure]

theorem sliceMeasure_eq_smul_haar (hV : IsOpen V) (hVc : IsCompact V) :
    ∃ c : ℝ≥0, sliceMeasure Φ μ V = c • Measure.haar := by
  have := sliceMeasure_isMulLeftInvariant (Φ := Φ) (μ := μ) hV
  have := sliceMeasure_isFiniteMeasureOnCompacts (Φ := Φ) (μ := μ) hV hVc
  exact ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩

theorem quasiMeasurePreserving_fst_comp (hV : IsOpen V) (hVc : IsCompact V) :
    Measure.QuasiMeasurePreserving (fun x => (Φ x).1) (μ.restrict (Φ ⁻¹' (univ ×ˢ V)))
      (Measure.haar : Measure G₁) := by
  refine ⟨(measurable_fst_comp Φ).aemeasurable, fun A hA => ?_⟩
  change sliceMeasure Φ μ V A = 0
  obtain ⟨c, hc⟩ := sliceMeasure_eq_smul_haar (Φ := Φ) (μ := μ) hV hVc
  rw [hc, Measure.smul_apply, hA, smul_zero]

theorem measure_preimage_prod_null (hV : IsOpen V) (hVc : IsCompact V) {N : Set G₁}
    (hN : (Measure.haar : Measure G₁) N = 0) : μ (Φ ⁻¹' (N ×ˢ V)) = 0 := by
  rw [measure_preimage_prod_eq_restrict hV]
  exact QuasiMeasurePreserving.preimage_null (quasiMeasurePreserving_fst_comp hV hVc) hN

theorem nullMeasurableSet_preimage_prod (hV : IsOpen V) (hVc : IsCompact V) {A : Set G₁}
    (hA : NullMeasurableSet A (Measure.haar : Measure G₁)) :
    NullMeasurableSet (Φ ⁻¹' (A ×ˢ V)) μ := by
  rw [preimage_prod_eq]
  exact (nullMeasurableSet_restrict (measurableSet_preimage_univ_prod hV).nullMeasurableSet).1
    (hA.preimage (quasiMeasurePreserving_fst_comp hV hVc))

theorem measure_preimage_prod_lt_top (hV : IsOpen V) (hVc : IsCompact V) {A : Set G₁}
    (hA : (Measure.haar : Measure G₁) A < ∞) : μ (Φ ⁻¹' (A ×ˢ V)) < ∞ := by
  refine (measure_preimage_prod_le hV A).trans_lt ?_
  obtain ⟨c, hc⟩ := sliceMeasure_eq_smul_haar (Φ := Φ) (μ := μ) hV hVc
  rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hA

end Setup

theorem DoubleCosetCovolume.proof (G G₁ G₂ : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁]
    [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁]
    [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] :
    DoubleCosetCovolume.Statement G G₁ G₂ := by
  intro Φ Γ _ K S hKc hKo hinj hcover hFD μ _
  classical
  let R := doubleCosetSetoid Φ Γ K

  let rep : Quotient R → G₂ := fun q =>
    if h : ∃ t ∈ S, Quotient.mk R t = q then h.choose else 1
  have rep_spec : ∀ t ∈ S, rep (Quotient.mk R t) ∈ S ∧
      Quotient.mk R (rep (Quotient.mk R t)) = Quotient.mk R t := by
    intro t ht
    have h : ∃ t' ∈ S, Quotient.mk R t' = Quotient.mk R t := ⟨t, ht, rfl⟩
    simp only [rep, dif_pos h]
    exact h.choose_spec
  let T : Finset (Quotient R) := S.image (Quotient.mk R)
  have hT : ∀ q ∈ T, rep q ∈ S ∧ Quotient.mk R (rep q) = q := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hq
    exact rep_spec t ht

  let F : G₂ → Set G₁ := fun s =>
    if hs : s ∈ S then (hFD s hs (Measure.haar : Measure G₁)).choose else ∅
  have hF : ∀ s ∈ S, IsFundamentalDomain (sliceGroup Φ Γ K s) (F s) Measure.haar ∧
      (Measure.haar : Measure G₁) (F s) < ∞ := by
    intro s hs
    simp only [F, dif_pos hs]
    exact (hFD s hs Measure.haar).choose_spec
  have hVo := isOpen_leftCosetSet hKo
  have hVc := isCompact_leftCosetSet hKc
  let P : G₂ → Set G := fun s => Φ ⁻¹' (F s ×ˢ leftCosetSet K s)
  refine ⟨⋃ q ∈ T, P (rep q), IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_, ?_⟩
  ·
    refine NullMeasurableSet.biUnion T.countable_toSet fun q hq => ?_
    exact nullMeasurableSet_preimage_prod (hVo _) (hVc _) (hF _ (hT q hq).1).1.nullMeasurableSet
  ·
    let Nbad : G₂ → Set G₁ := fun s => {a | ¬ ∃ δ : sliceGroup Φ Γ K s, δ • a ∈ F s}
    let B : Set G := ⋃ η : Γ, ⋃ s ∈ S,
      (fun x => (η : G)⁻¹ * x) ⁻¹' (Φ ⁻¹' (Nbad s ×ˢ leftCosetSet K s))
    have hB : μ B = 0 := by
      refine measure_iUnion_null fun η => ?_
      refine (measure_biUnion_null_iff S.countable_toSet).2 fun s hs => ?_
      rw [measure_preimage_mul]
      exact measure_preimage_prod_null (hVo _) (hVc _) (ae_iff.1 (hF s hs).1.ae_covers)
    refine ae_iff.2 (measure_mono_null ?_ hB)
    intro x hx
    by_contra hxB
    apply hx
    obtain ⟨γ, hγ, t, ht, k, hk, hxt⟩ := hcover (Φ x).2
    have ht' : Quotient.mk R t = Quotient.mk R (Φ x).2 := Quotient.sound ⟨γ, hγ, k, hk, hxt⟩
    obtain ⟨hs, hsq⟩ := rep_spec t ht
    obtain ⟨η, hη, k', hk', hx2⟩ : R (rep (Quotient.mk R t)) (Φ x).2 :=
      Quotient.exact (hsq.trans ht')
    have e2 : (Φ ((η : G)⁻¹ * x)).2 = rep (Quotient.mk R t) * k' := by
      simp [hx2, mul_assoc]
    have hgood : ¬ (Φ ((η : G)⁻¹ * x)).1 ∈ Nbad (rep (Quotient.mk R t)) := by
      intro hbad
      apply hxB
      refine mem_iUnion.2 ⟨⟨η, hη⟩, mem_iUnion₂.2 ⟨_, hs, ?_⟩⟩
      refine ⟨hbad, ?_⟩
      show (rep (Quotient.mk R t))⁻¹ * (Φ ((η : G)⁻¹ * x)).2 ∈ K
      rw [e2, inv_mul_cancel_left]
      exact hk'
    simp only [Nbad, Set.mem_ofPred_eq, not_not] at hgood
    obtain ⟨δ, hδ⟩ := hgood
    obtain ⟨ζ, hζ, hζK, hζ1⟩ := mem_sliceGroup.1 δ.2
    refine ⟨⟨ζ * η⁻¹, Γ.mul_mem hζ (Γ.inv_mem hη)⟩, ?_⟩
    refine mem_iUnion₂.2 ⟨Quotient.mk R t, Finset.mem_image_of_mem _ ht, ?_⟩
    show Φ ((ζ * η⁻¹ : G) * x) ∈ F _ ×ˢ leftCosetSet K _
    rw [mul_assoc, map_mul]
    refine ⟨?_, ?_⟩
    · rw [Prod.fst_mul, hζ1]
      exact hδ
    · show (rep (Quotient.mk R t))⁻¹ * ((Φ ζ).2 * (Φ ((η : G)⁻¹ * x)).2) ∈ K
      rw [e2]
      have : (rep (Quotient.mk R t))⁻¹ * ((Φ ζ).2 * (rep (Quotient.mk R t) * k')) =
          (rep (Quotient.mk R t))⁻¹ * (Φ ζ).2 * rep (Quotient.mk R t) * k' := by
        simp only [mul_assoc]
      rw [this]
      exact K.mul_mem hζK hk'
  ·
    intro g hg
    let M : G₂ → Set G := fun s => ⋃ (h : (Φ g).1 ∈ sliceGroup Φ Γ K s),
      Φ ⁻¹' ((((⟨(Φ g).1, h⟩ : sliceGroup Φ Γ K s) • F s) ∩ F s) ×ˢ leftCosetSet K s)
    have hM : μ (⋃ s ∈ S, M s) = 0 := by
      refine (measure_biUnion_null_iff S.countable_toSet).2 fun s hs => ?_
      refine measure_iUnion_null fun h => ?_
      refine measure_preimage_prod_null (hVo _) (hVc _) ?_
      have hne : (⟨(Φ g).1, h⟩ : sliceGroup Φ Γ K s) ≠ 1 := by
        intro h1
        exact hg (Subtype.ext (hinj g g.2 (congrArg Subtype.val h1)))
      have := (hF s hs).1.aedisjoint hne
      simpa [Function.onFun, AEDisjoint] using this
    refine measure_mono_null ?_ hM
    rintro z ⟨hz1, hz2⟩
    rw [mem_smul_set_iff_inv_smul_mem] at hz1
    obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 hz1
    obtain ⟨q', hq', hzq'⟩ := mem_iUnion₂.1 hz2
    have hgz : Φ (g⁻¹ • z) = ((Φ g).1⁻¹ * (Φ z).1, (Φ g).2⁻¹ * (Φ z).2) := by
      rw [Subgroup.smul_def, smul_eq_mul, map_mul]
      simp [Prod.ext_iff]
    obtain ⟨hzF, hzK⟩ := hzq
    obtain ⟨hzF', hzK'⟩ := hzq'
    change (Φ (g⁻¹ • z)).1 ∈ F (rep q) at hzF
    change (Φ (g⁻¹ • z)).2 ∈ leftCosetSet K (rep q) at hzK
    rw [hgz] at hzF hzK
    simp only at hzF hzK
    change (rep q)⁻¹ * ((Φ g).2⁻¹ * (Φ z).2) ∈ K at hzK
    change (rep q')⁻¹ * (Φ z).2 ∈ K at hzK'
    have e1 : Quotient.mk R (rep q) = Quotient.mk R (Φ z).2 :=
      Quotient.sound ⟨g, g.2, _, hzK, by group⟩
    have e2 : Quotient.mk R (rep q') = Quotient.mk R (Φ z).2 :=
      Quotient.sound ⟨1, Γ.one_mem, _, hzK', by simp⟩
    have hqq : q = q' := by
      rw [← (hT q hq).2, ← (hT q' hq').2, e1, e2]
    subst hqq
    have hslice : (Φ g).1 ∈ sliceGroup Φ Γ K (rep q) := by
      refine mem_sliceGroup.2 ⟨g, g.2, ?_, rfl⟩
      have : (rep q)⁻¹ * (Φ g).2 * rep q =
          ((rep q)⁻¹ * (Φ z).2) * ((rep q)⁻¹ * ((Φ g).2⁻¹ * (Φ z).2))⁻¹ := by
        group
      rw [this]
      exact K.mul_mem hzK' (K.inv_mem hzK)
    refine mem_iUnion₂.2 ⟨rep q, (hT q hq).1, mem_iUnion.2 ⟨hslice, ?_⟩⟩
    refine ⟨⟨?_, hzF'⟩, hzK'⟩
    rw [mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
    exact hzF
  ·
    exact fun g => (measurePreserving_smul g μ).quasiMeasurePreserving
  ·
    refine (measure_biUnion_finset_le T _).trans_lt (ENNReal.sum_lt_top.2 fun q hq => ?_)
    exact measure_preimage_prod_lt_top (hVo _) (hVc _) (hF _ (hT q hq).1).2

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

universe u

theorem ReducedBasisBound.full : ReducedBasisBound.Statement := ReducedBasisBound.proof

section Closed

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

section OneSpace

variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)


omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
theorem ArchCovolumeBound.full : ArchCovolumeBound.Statement h v :=
  ArchCovolumeBound.proof h v (CoordEmbedBasis.proof E ι) (IntegralFormCovolume.proof _ _ _)
    (TraceHermNondegenerate.proof h v) (DualLatticeMultiple.proof h) (CoordLatticeFullRank.proof v)


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem MajorantTransport.full : MajorantTransport.Statement h v := MajorantTransport.proof h v


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem ComplementExtension.full : ComplementExtension.Statement h := ComplementExtension.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LineNormalForm.full : LineNormalForm.Statement h := LineNormalForm.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem ComplementLattice.full [FiniteDimensional E W] : ComplementLattice.Statement h :=
  ComplementLattice.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LatticePointsBelowFinite.full : LatticePointsBelowFinite.Statement h v :=
  LatticePointsBelowFinite.proof h v

theorem ArchimedeanUnitaryEquiv.full : ArchimedeanUnitaryEquiv.Statement h v :=
  ArchimedeanUnitaryEquiv.proof h v

theorem AdelicLatticeDictionary.full : AdelicLatticeDictionary.Statement h v :=
  AdelicLatticeDictionary.proof h v

end OneSpace

theorem LatticeOrbitsFiniteBelow.full (N : ℕ) : LatticeOrbitsFiniteBelow.{u} F E N :=
  LatticeOrbitsFiniteBelow.of_steps ReducedBasisBound.full
    (fun _ _ _ _ h _ v => ArchCovolumeBound.full h v) (fun _ _ _ _ h _ v => MajorantTransport.full h v)
    (fun _ _ _ _ h => ComplementExtension.full h) (fun _ _ _ _ h => LineNormalForm.full h)
    (fun _ _ _ _ h => ComplementLattice.full h) N

section Dimension

variable {W : Type u} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
variable (h : HermitianForm F E W)

theorem LatticeOrbitsFinite.full : LatticeOrbitsFinite.Statement h :=
  LatticeOrbitsFinite.step_of h (LatticeOrbitsFiniteBelow.full _) ReducedBasisBound.full
    (ArchCovolumeBound.full h _) (MajorantTransport.full h _) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h)

theorem LinePairOrbitsFinite.full : LinePairOrbitsFinite.Statement h :=
  LinePairOrbitsFinite.full_of h (LatticeOrbitsFiniteBelow.full _) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h)

theorem ScalingLaw.of_unfolding {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Basis ι E W)
    (hU : UnfoldingIntegral.Statement h v) : ScalingLaw.Statement h v :=
  ScalingLaw.full_of h v (LinePairOrbitsFinite.full h) hU

end Dimension

end Closed

section Adelic

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AdelicCovolumeFinite.of_covolume (h : HermitianForm F E W) (v : Basis ι E W)
    (hC : ArithmeticCovolumeFinite.Statement h v) : AdelicCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  AdelicCovolumeFinite.full_of h v (LatticeOrbitsFinite.full h) hC (ArchimedeanUnitaryEquiv.full h v)
    (AdelicLatticeDictionary.full h v) (DoubleCosetCovolume.proof _ _ _)

theorem HaarParabolicCoordinates.of_open (h : HermitianForm F E W) (v : Basis ι E W)
    (hAU : ArchUnimodular.Statement h v) (hMS : MajorantStabCompact.Statement h v)
    (hLS : LineStabHaar.Statement h v) : HaarParabolicCoordinates.Statement h v :=
  HaarParabolicCoordinates.proof h v (ParabolicDecomposition.full h v) hAU hMS hLS

end Adelic

section Open

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

variable
    (hAU : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), ArchUnimodular.Statement h v)
    (hMS : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), MajorantStabCompact.Statement h v)
    (hLS : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), LineStabHaar.Statement h v)
    (hSD : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W) (x₀ w₀ : W)
      (h' : HermitianForm F E (hypComplement h x₀ w₀)) (m : ℕ)
      (v' : Basis (Fin m) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (hSL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), StabilizerLevi.Statement h v)
    (hUM : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentModulus.Statement h v)
    (hUC : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentCocompact.Statement h v)
    (hCL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), CongruenceLift.Statement h)

include hAU hMS hLS hSD hSL hUM hUC hCL

theorem CovolumeFiniteBelow.of_open (N : ℕ) : CovolumeFiniteBelow.{u} F E N :=
  CovolumeFiniteBelow.of_steps ReducedBasisBound.full
    (fun _ _ _ _ h _ v => ArchCovolumeBound.full h v) (fun _ _ _ _ h _ v => MajorantTransport.full h v)
    (fun _ _ _ _ h => ComplementExtension.full h) (fun _ _ _ _ h => LineNormalForm.full h)
    (fun _ _ _ _ h => ComplementLattice.full h) (fun _ _ _ _ _ _ _ _ => UnfoldAlongSubgroup.proof _ _)
    (fun W _ _ _ h n v => HaarParabolicCoordinates.of_open h v (hAU W h n v) (hMS W h n v)
      (hLS W h n v))
    (fun W _ _ _ h n v hB => StabilizerCovolumeFinite.proof h v hB (hSD W h n v) (hSL W h n v)
      (hUM W h n v) (hUC W h n v) (hCL W h))
    (fun _ _ _ _ h _ v => LatticePointsBelowFinite.full h v) N

variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)

variable (hSD' : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (m : ℕ)
      (v' : Basis (Fin m) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (hSL' : StabilizerLevi.Statement h v) (hUM' : UnipotentModulus.Statement h v)
    (hUC' : UnipotentCocompact.Statement h v)

include hSD' hSL' hUM' hUC'

theorem StabilizerCovolumeFinite.of_open : StabilizerCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  StabilizerCovolumeFinite.proof h v
    (CovolumeFiniteBelow.of_open hAU hMS hLS hSD hSL hUM hUC hCL _) hSD' hSL' hUM' hUC' (hCL W h)

variable (hAU' : ArchUnimodular.Statement h v) (hMS' : MajorantStabCompact.Statement h v)
    (hLS' : LineStabHaar.Statement h v)

include hAU' hMS' hLS'

theorem UnfoldingIntegral.of_open : UnfoldingIntegral.Statement h v :=
  UnfoldingIntegral.full_of h v (fun _ => UnfoldAlongSubgroup.proof _ _)
    (HaarParabolicCoordinates.of_open h v hAU' hMS' hLS')
    (StabilizerCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC')

theorem ScalingLaw.of_open : ScalingLaw.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  ScalingLaw.of_unfolding h v
    (UnfoldingIntegral.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC' hAU' hMS' hLS')

theorem ArithmeticCovolumeFinite.of_open : ArithmeticCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  ArithmeticCovolumeFinite.step_of h v (LatticeOrbitsFiniteBelow.full _) ReducedBasisBound.full
    (ArchCovolumeBound.full h v) (MajorantTransport.full h v) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h) (fun _ => UnfoldAlongSubgroup.proof _ _)
    (HaarParabolicCoordinates.of_open h v hAU' hMS' hLS')
    (StabilizerCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC')
    (LatticePointsBelowFinite.full h v)

theorem AdelicCovolumeFinite.of_open : AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.of_covolume h v
    (ArithmeticCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC' hAU' hMS'
      hLS')

end Open

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
