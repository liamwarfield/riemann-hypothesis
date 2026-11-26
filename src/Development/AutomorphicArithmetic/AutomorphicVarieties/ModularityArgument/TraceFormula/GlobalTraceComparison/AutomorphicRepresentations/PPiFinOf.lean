module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ContinuousEmbInf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPiFinOf
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.piFinOf_pf :
    PiAdm → TensType → CvType → CvIn → TypeIn → PiFin := by
  intro hA hT hC hI hY E _ _ _ n hn D π hπ μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j
  obtain ⟨ht, K, W, k1, k2, w1, w2, hl⟩ := hT E n μa μb ha hb Ma Mb κ ka kb va vb R ψ U h1 h2 h3 h4 h5 i j
  obtain ⟨Y, y1, y2, y3⟩ := hA E n hn π hπ K W k1 w1
  refine ⟨Y, y1, y2, fun u hu φ hφ => ?_⟩
  obtain ⟨s0, s1⟩ := hI E n hn D π hπ φ hφ
  obtain ⟨s2, s3, -⟩ := s1 _ u ht hu
  have ty := hC E n D K W _ u φ.1 k2 w1 ht hl hu s0.1
  obtain ⟨φ', m, e⟩ := hY E n hn D π hπ K W k1 k2 w1 w2 _ s2 s3 ty
  refine ⟨φ', y3 φ' m ?_, fun x => congrFun e x⟩
  rw [← e] at ty
  exact ty
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PDetZero
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem zero_of_powers_compact {G : Type*} [Monoid G] [TopologicalSpace G] (f : G → ℝ) (hf : Continuous f)
    (hm : ∀ x y, f (x * y) = f x + f y) (S : Set G) (hS : IsCompact S) (k : G) (hk : ∀ m : ℕ, k ^ m ∈ S) : f k = 0 := by
  obtain ⟨C, hC⟩ := (hS.image hf).isBounded.exists_norm_le
  have h1 : f 1 = 0 := by
    have := hm 1 1
    rw [mul_one] at this
    linarith
  have hp : ∀ m : ℕ, f (k ^ m) = m * f k := by
    intro m
    induction m with
    | zero => simp [h1]
    | succ m ih => rw [pow_succ, hm, ih]; push_cast; ring
  by_contra hne
  have hpos : 0 < |f k| := abs_pos.2 hne
  obtain ⟨m, hmC⟩ := exists_nat_gt (C / |f k|)
  have hb := hC _ ⟨k ^ m, hk m, rfl⟩
  rw [hp, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at hb
  rw [div_lt_iff₀ hpos] at hmC
  linarith

private theorem continuous_kI (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Continuous (kI E n) := by
  have hu : Continuous (Unitary.toUnits : Kinf E n → _) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  exact GlobalTheory.CuspQuot.continuous_infGL.comp hu

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.detZero_pf :
    DetZero := by
  intro E _ _ _ n
  have hc := DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)
  have hm := DiscreteGroups.T1.G.Dcy.logAbs_det_mul' (E := E) (n := n)
  refine ⟨fun k => ?_, fun K hK k hk => ?_⟩
  · haveI : CompactSpace (Kinf E n) := GlobalTheory.KinfCompactness.compactSpace_Kinf E n
    exact zero_of_powers_compact _ hc hm (Set.range (kI E n)) (isCompact_range (continuous_kI E n)) _
      fun m => ⟨k ^ m, map_pow _ _ _⟩
  · exact zero_of_powers_compact _ hc hm (finGL E n '' (K : Set _))
      (hK.image GlobalTheory.BCT.GlobLev.continuous_finGL_ad) _ fun m => ⟨k ^ m, K.pow_mem hk m, map_pow _ _ _⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PCvType
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private lemma shiftInt (D : Dom E n 0) (a : H E n 0) (F : H E n 0 → ℂ) :
    ∫ y, F (a * y) ∂D.μ = ∫ y, F y ∂D.μ := by
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI := D.haar.1
  exact integral_mul_left_eq_self F a

private lemma ldet_shift (a : GA E n) (h : logAbs a.val.det = 0) (y : H E n 0) :
    ldet (((a, 1) : H E n 0) * y) = ldet y := by
  simp only [ldet, Prod.fst_mul, DiscreteGroups.T1.G.Dcy.logAbs_det_mul', h, zero_add]

private lemma cv_shift (D : Dom E n 0) (φ : H E n 0 → ℂ) (u : ℝ → ℂ) (f : GA E n → ℂ) (g a : GA E n)
    (h : logAbs a.val.det = 0) :
    cvF D.μ φ u f (g * a) = ∫ y, φ ((a⁻¹, 1) * y) * u (ldet y) * f (g * y.1) ∂D.μ := by
  rw [← shiftInt D ((a, 1) : H E n 0) (fun y => φ ((a⁻¹, 1) * y) * u (ldet y) * f (g * y.1))]
  unfold cvF
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have e : ((a⁻¹, 1) : H E n 0) * (((a, 1) : H E n 0) * y) = y := by
    rw [← mul_assoc]; simp
  simp only [e, ldet_shift a h, Prod.fst_mul, mul_assoc]

private lemma term_integrable (D : Dom E n 0) (φ : H E n 0 → ℂ) (u : ℝ → ℂ) (f : GA E n → ℂ) (g a : GA E n)
    (hφ : IsTestH φ) (hu : Continuous u) (hf : Continuous f) :
    Integrable (fun y : H E n 0 => φ ((a, 1) * y) * u (ldet y) * f (g * y.1)) D.μ := by
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI := D.haar.2.2.2
  haveI : IsFiniteMeasureOnCompacts D.μ :=
    ⟨fun _ h => h.measure_lt_top_of_nhdsWithin fun x _ => D.μ.finiteAt_nhdsWithin x _⟩
  have c1 : Continuous fun y : H E n 0 => φ ((a, 1) * y) := hφ.1.comp (continuous_const.mul continuous_id)
  have s1 : HasCompactSupport fun y : H E n 0 => φ ((a, 1) * y) :=
    hφ.2.comp_homeomorph (Homeomorph.mulLeft ((a, 1) : H E n 0))
  have s3 : HasCompactSupport fun y : H E n 0 => φ ((a, 1) * y) * u (ldet y) * f (g * y.1) :=
    (s1.mul_right (f' := fun y : H E n 0 => u (ldet y))).mul_right (f' := fun y : H E n 0 => f (g * y.1))
  have c3 : Continuous fun y : H E n 0 => φ ((a, 1) * y) * u (ldet y) * f (g * y.1) :=
    (c1.mul (hu.comp DiscreteGroups.T1.G.continuous_ldet)).mul (hf.comp (continuous_const.mul continuous_fst))
  exact c3.integrable_of_hasCompactSupport s3

theorem cvType_pf : DetZero → EvalBasis → CvType := by
  intro hdz hev E _ _ _ n D K W φ u f hK hW hφ hL hu hf
  refine ⟨fun k hk g => ?_, fun g => ?_⟩
  · rw [cv_shift D φ u f g _ ((hdz E n).2 K hK k hk)]
    unfold cvF
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have := hL.1 k⁻¹ (K.inv_mem hk) y
    simp only [map_inv] at this
    simp only [this]
  · obtain ⟨d, x, w, hw, hs⟩ := hev (Kinf E n) (Kinf E n → ℂ) (fun x => LinearMap.proj x)
      (fun v hv => funext hv) W hW
    set c : Fin d → ℂ := fun b =>
      ∫ y, φ (((kI E n (x b))⁻¹, 1) * y) * u (ldet y) * f (g * y.1) ∂D.μ with hc
    have key : (fun k : Kinf E n => cvF D.μ φ u f (g * kI E n k)) = ∑ b, c b • w b := by
      funext k
      rw [cv_shift D φ u f g _ ((hdz E n).1 k)]
      have e : ∀ y : H E n 0, φ (((kI E n k)⁻¹, 1) * y) * u (ldet y) * f (g * y.1) =
          ∑ b, w b k * (φ (((kI E n (x b))⁻¹, 1) * y) * u (ldet y) * f (g * y.1)) := by
        intro y
        have := congrFun (hs _ (hL.2 y)) k
        simp only [LinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        rw [this, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by ring
      simp only [e]
      rw [integral_finsetSum _ fun b _ => (term_integrable D φ u f g _ hφ hu hf).const_mul _]
      simp only [integral_const_mul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [key]
    exact Submodule.sum_mem _ fun b _ => W.smul_mem _ (hw b)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTwTrSum
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

attribute [local instance] borelG borelF borelA borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.TS

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private lemma trace_range_eq (A : V →ₗ[ℂ] V) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hA : LinearMap.range A ≤ W) (hW : ∀ x ∈ W, A x ∈ W) :
    LinearMap.trace ℂ (LinearMap.range A) (A.restrict fun x _ => LinearMap.mem_range_self A x) =
      LinearMap.trace ℂ W (A.restrict hW) := by
  have hfd : FiniteDimensional ℂ (LinearMap.range A) :=
    Submodule.finiteDimensional_of_le hA
  let f : W →ₗ[ℂ] LinearMap.range A :=
    (A.comp W.subtype).codRestrict _ fun x => LinearMap.mem_range_self A _
  let g : LinearMap.range A →ₗ[ℂ] W := Submodule.inclusion hA
  have e1 : A.restrict (fun x _ => LinearMap.mem_range_self A x) = f ∘ₗ g := by
    ext x; rfl
  have e2 : A.restrict hW = g ∘ₗ f := by
    ext x; rfl
  rw [e1, e2, LinearMap.trace_comp_comm' f g]

private lemma trace_sum {J : Type*} (s : Finset J) (c : J → ℂ) (L : J → V →ₗ[ℂ] V)
    (h : ∀ j ∈ s, FiniteDimensional ℂ (LinearMap.range (L j))) :
    FiniteDimensional ℂ (LinearMap.range (∑ j ∈ s, c j • L j)) ∧
    LinearMap.trace ℂ (LinearMap.range (∑ j ∈ s, c j • L j))
        ((∑ j ∈ s, c j • L j).restrict fun x _ => LinearMap.mem_range_self _ x) =
      ∑ j ∈ s, c j * LinearMap.trace ℂ (LinearMap.range (L j))
        ((L j).restrict fun x _ => LinearMap.mem_range_self _ x) := by
  classical
  let W : Submodule ℂ V := s.sup fun j => LinearMap.range (L j)
  have hfd : FiniteDimensional ℂ W := by
    refine Finset.sup_induction (p := fun U : Submodule ℂ V => FiniteDimensional ℂ U) ?_ ?_ h
    · exact inferInstanceAs (FiniteDimensional ℂ (⊥ : Submodule ℂ V))
    · intro a ha b hb
      exact Submodule.finiteDimensional_sup a b
  have hle : ∀ j ∈ s, LinearMap.range (L j) ≤ W := fun j hj =>
    Finset.le_sup (f := fun j => LinearMap.range (L j)) hj
  have hS : LinearMap.range (∑ j ∈ s, c j • L j) ≤ W := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.sum_apply]
    exact W.sum_mem fun j hj => W.smul_mem _ (hle j hj (LinearMap.mem_range_self _ x))
  have hj' : ∀ j ∈ s, ∀ x ∈ W, L j x ∈ W := fun j hj x _ => hle j hj (LinearMap.mem_range_self _ x)
  have hSW : ∀ x ∈ W, (∑ j ∈ s, c j • L j) x ∈ W := fun x _ => hS (LinearMap.mem_range_self _ x)
  refine ⟨Submodule.finiteDimensional_of_le hS, ?_⟩
  rw [trace_range_eq _ W hS hSW]
  have e : (∑ j ∈ s, c j • L j).restrict hSW =
      ∑ j ∈ s.attach, c j.1 • (L j.1).restrict (hj' j.1 j.2) := by
    ext x
    simp only [LinearMap.restrict_coe_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul]
    rw [← Finset.sum_attach s]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum, ← Finset.sum_attach s]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, trace_range_eq (L j.1) W (hle j.1 j.2) (hj' j.1 j.2)]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.TS

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.TS in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.twTrSum_pf :
    TwTrSum := by
  intro E _ _ _ n D π J s c φ t h
  have hL := fun j (hj : j ∈ s) => (h j hj).2
  choose! L e f ht using hL
  have hT := trace_sum s c L f
  haveI : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  refine ⟨∑ j ∈ s, c j • L j, fun ψ x => ?_, hT.1, ?_⟩
  · have hc : Continuous fun g : GA E n => ψ.1.1 (thetaA E n g) :=
      (DiscreteGroups.T1.G.twtr_cont_of_mem π ψ.2).comp (PositivityTheory.Rg.BcB.E1.thetaBasic_holds E n).1
    have hi : ∀ j ∈ s, Integrable (fun y => φ j y * ψ.1.1 (thetaA E n (x * y.1))) D.μ := fun j hj =>
      DiscreteGroups.T1.G.twtr_integrable D.μ (h j hj).1 hc x
    have hv : ((∑ j ∈ s, c j • L j) ψ).1.1 x = ∑ j ∈ s, c j * (L j ψ).1.1 x := by
      simp [LinearMap.sum_apply]
    rw [hv, Finset.sum_congr rfl fun j hj => by rw [e j hj ψ x]]
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun j hj => (hi j hj).const_mul _]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [Finset.sum_apply, Finset.sum_mul, mul_assoc]
  · rw [hT.2]
    exact Finset.sum_congr rfl fun j hj => by rw [ht j hj]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTensType
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open PositivityTheory.Rg.BcB.CG.prime_not_mem_section_base_place
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem uAt_mul' (v : InfinitePlace E) (k k' : Kinf E n) : uAt v (k * k') = uAt v k * uAt v k' := by
  apply Subtype.ext
  show ((k * k' : Kinf E n) : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v) =
    (k : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v) * (k' : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v)
  rw [← Matrix.map_mul]
  rfl

private theorem coef_mul' (M : Mods E n) (I L : IxA M) (x k : Kinf E n) :
    coef M I L (x * k) = ∑ m : IxA M, coef M I m k * coef M m L x := by
  have h1 : ∀ v, ent (M v) ((M v).ρ (uAt v (x * k)⁻¹)) (I v) (L v) =
      ∑ l, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) l * ent (M v) ((M v).ρ (uAt v x⁻¹)) l (L v) := by
    intro v
    rw [_root_.mul_inv_rev, uAt_mul', map_mul, PMul.ent_mul]
  calc coef M I L (x * k)
      = ∏ v, ∑ l, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) l * ent (M v) ((M v).ρ (uAt v x⁻¹)) l (L v) :=
        Finset.prod_congr rfl fun v _ => h1 v
    _ = ∑ m ∈ Fintype.piFinset fun _ => Finset.univ,
          ∏ v, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) (m v) * ent (M v) ((M v).ρ (uAt v x⁻¹)) (m v) (L v) :=
        Finset.prod_univ_sum _ _
    _ = ∑ m : IxA M, coef M I m k * coef M m L x := by
        simp only [Fintype.piFinset_univ, Finset.prod_mul_distrib, coef]

private theorem rinv_Wsp (M : Mods E n) : RInv (Wsp M) := by
  intro f hf k
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨p, rfl⟩ := h
    have e : (fun x => coef M p.1 p.2 (x * k)) = ∑ m : IxA M, coef M p.1 m k • coef M m p.2 := by
      funext x
      simp only [coef_mul', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    show (fun x => coef M p.1 p.2 (x * k)) ∈ Wsp M
    rw [e]
    exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(m, p.2), rfl⟩)
  | zero => exact (Wsp M).zero_mem
  | add a b _ _ ha hb => exact (Wsp M).add_mem ha hb
  | smul c a _ ha => exact (Wsp M).smul_mem c ha

private theorem level_open_compact {b : ℕ} (U : Subgroup (Hf E n b)) (hU : IsOpen (U : Set (Hf E n b))) :
    IsOpen ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) ∧
      IsCompact ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) := by
  have h1 : IsOpen ((U.comap (MonoidHom.inl _ _) : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) :=
    hU.preimage (Continuous.prodMk_left 1)
  have h2 : IsOpen ((U.comap (MonoidHom.inl _ _) ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n : Subgroup (GL (Fin n) (Af E))) : Set (GL (Fin n) (Af E))) :=
    h1.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E n)
  exact ⟨h2, (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E n).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ h2) Set.inter_subset_right⟩

end SlopeTestRemainingChoices

theorem tensType_pf : TensType := by
  intro E _ _ _ n μa μb _ _ Ma Mb κ ka kb va vb R ψ U ha hb hψ hU hlev i j
  obtain ⟨hKo, hKc⟩ := level_open_compact U hU
  refine ⟨tens_cs ha hb hψ i j, _, Wsp Ma, hKo, hKc, fd_Wsp Ma, rinv_Wsp Ma, fun u hu y => ?_, fun y => ?_⟩
  · have e1 : entA ka i.1.1 j.1.1 (finGL E n u * y.1) = entA ka i.1.1 j.1.1 y.1 := by
      have h := entA_fin ka i.1.1 j.1.1 u⁻¹ y.1
      rwa [map_inv, inv_inv] at h
    have e2 : hFin ((finGL E n u, 1) * y) = ((u, 1) : Hf E n 0) * hFin y := by
      show (gFin (finGL E n u * y.1), gFin (1 * y.2)) = (u * gFin y.1, 1 * gFin y.2)
      rw [map_mul, gFin_finGL, one_mul, one_mul]
    show entA ka i.1.1 j.1.1 (finGL E n u * y.1) * entA kb i.1.2 j.1.2 (1 * y.2) *
        ψ i.2 j.2 (hFin ((finGL E n u, 1) * y)) = entA ka i.1.1 j.1.1 y.1 * entA kb i.1.2 j.1.2 y.2 * ψ i.2 j.2 (hFin y)
    rw [e1, one_mul, e2, hlev i.2 j.2 (u, 1) hu.1 (hFin y)]
  · have e : (fun k : Kinf E n => tens ka kb ψ i j (((kI E n k)⁻¹, 1) * y)) =
        ∑ L : IxA Ma, (entA ka L j.1.1 y.1 * entA kb i.1.2 j.1.2 y.2 * ψ i.2 j.2 (hFin y)) • coef Ma i.1.1 L := by
      funext k
      have e2 : hFin (((kI E n k)⁻¹, 1) * y) = hFin y := by
        have h1 : gFin (infGL E n (Unitary.toUnits k)) = 1 := pFin_infGL _
        show (gFin ((infGL E n (Unitary.toUnits k))⁻¹ * y.1), gFin (1 * y.2)) = (gFin y.1, gFin y.2)
        rw [map_mul, map_inv, h1, inv_one, one_mul, one_mul]
      show entA ka i.1.1 j.1.1 ((infGL E n (Unitary.toUnits k))⁻¹ * y.1) * entA kb i.1.2 j.1.2 (1 * y.2) *
          ψ i.2 j.2 (hFin (((kI E n k)⁻¹, 1) * y)) = _
      rw [entA_inf ha, one_mul, e2, Finset.sum_mul, Finset.sum_mul]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun L _ => by ring
    rw [e]
    exact Submodule.sum_mem _ fun L _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i.1.1, L), rfl⟩)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PFormEx
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE

private theorem weight_ex : ∃ w : ℝ → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ s, 0 ≤ w s) ∧
    (∀ s ∈ Set.Ioo (-1 : ℝ) 1, w s ≠ 0) ∧ ∫ s, w s = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, b.continuous_normed, b.hasCompactSupport_normed, b.nonneg_normed, ?_,
    b.integral_normed⟩
  intro s hs
  have h : s ∈ Function.support (b.normed volume) := by
    rw [b.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_lt.2 hs
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def slabSp (D : Dom E n 0) : Submodule ℂ (GA E n → ℂ) where
  carrier := {f | Slab D f}
  zero_mem' := ⟨continuous_const, fun _ _ => rfl, fun _ _ => rfl, fun u _ _ => by
    simp only [Pi.zero_apply, zero_mul]
    exact MemLp.zero⟩
  add_mem' := by
    rintro a b ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨a1.add b1, fun γ g => ?_, fun t g => ?_, fun u hu hc => ?_⟩
    · simp only [Pi.add_apply, a2, b2]
    · simp only [Pi.add_apply, a3, b3]
    · have h := (a4 u hu hc).add (b4 u hu hc)
      refine (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).1 h
      simp only [Pi.add_apply, add_mul]
  smul_mem' := by
    rintro c a ⟨a1, a2, a3, a4⟩
    refine ⟨a1.const_smul c, fun γ g => ?_, fun t g => ?_, fun u hu hc => ?_⟩
    · simp only [Pi.smul_apply, a2]
    · simp only [Pi.smul_apply, a3]
    · have h := (a4 u hu hc).const_smul c
      refine (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).1 h
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem zero_of_ae (hB : Basic) (hA : AeEq) (hn : 1 ≤ n) (D : Dom E n 0) {f : GA E n → ℂ} (hf : Slab D f)
    (h : ∀ᵐ x ∂D.ν, ldet x ∈ Set.Ioo (-1 : ℝ) 1 → f x.1 = 0) : f = 0 := by
  obtain ⟨hl, hm, -⟩ := hB E n hn
  have hinv : Inv (fun x : H E n 0 => f x.1) := by
    rintro ⟨_, ⟨p, q⟩, rfl⟩ x
    exact hf.2.1 p x.1
  have key := hA E n D (fun x => f x.1) (fun _ => 0) _ (hf.1.comp continuous_fst) continuous_const hinv
    (fun _ _ => rfl) isOpen_Ioo h
  funext g
  have h0 : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1)) ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [hm, hl, neg_add_cancel]
    constructor <;> norm_num
  exact (hf.2.2.1 _ g).symm.trans (key _ h0)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.formEx_pf :
    Basic → AeEq → WtInd → FormEx := by
  intro hB hA hW E _ _ _ n hn D
  obtain ⟨w, wc, ws, w0, wp, w1⟩ := weight_ex
  have uc : Continuous fun s => (w s : ℂ) := Complex.continuous_ofReal.comp wc
  have us : HasCompactSupport fun s => (w s : ℂ) := ws.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have u1 : ∫ s, (w s : ℂ) = 1 := by rw [integral_complex_ofReal, w1, Complex.ofReal_one]
  have hI : ∀ a b : slabSp D, Integrable
      (fun x : H E n 0 => starRingEnd ℂ (a.1 x.1) * b.1 x.1 * (w (ldet x) : ℂ)) D.ν :=
    fun a b => (hW E n hn D a.1 b.1 a.2 b.2 _ uc us).1
  let B : slabSp D →ₗ⋆[ℂ] slabSp D →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun a b => prW D (fun s => (w s : ℂ)) a.1 b.1)
      (fun a a' b => by
        simp only [prW]
        rw [← integral_add (hI a b) (hI a' b)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
        ring)
      (fun c a b => by
        simp only [prW, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
        ring)
      (fun a b b' => by
        simp only [prW]
        rw [← integral_add (hI a b) (hI a b')]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_add, Pi.add_apply]
        ring)
      (fun c a b => by
        simp only [prW, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        ring)
  have hBv : ∀ a b, B a b = prW D (fun s => (w s : ℂ)) a.1 b.1 := fun _ _ => rfl
  refine ⟨slabSp D, B, fun _ => Iff.rfl, fun a b => ?_, fun a ha => ?_, fun a b u hu hc => ?_, fun g hg a => ⟨?_, ?_⟩⟩
  · rw [hBv, hBv, prW, prW, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  · have he : ∀ x : H E n 0, starRingEnd ℂ (a.1 x.1) * a.1 x.1 * (w (ldet x) : ℂ) =
        ((Complex.normSq (a.1 x.1) * w (ldet x) : ℝ) : ℂ) := fun x => by
      rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    have hi : Integrable (fun x : H E n 0 => Complex.normSq (a.1 x.1) * w (ldet x)) D.ν := by
      have h := (hI a a).re
      simp only [he, RCLike.re_to_complex, Complex.ofReal_re] at h
      exact h
    have hnn : 0 ≤ fun x : H E n 0 => Complex.normSq (a.1 x.1) * w (ldet x) :=
      fun x => mul_nonneg (Complex.normSq_nonneg _) (w0 _)
    rw [hBv, prW]
    simp only [he]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    refine lt_of_le_of_ne (integral_nonneg hnn) fun h0 => ha (Subtype.ext ?_)
    refine zero_of_ae hB hA hn D a.2 ?_
    filter_upwards [(integral_eq_zero_iff_of_nonneg hnn hi).1 h0.symm] with x hx hI'
    exact Complex.normSq_eq_zero.1 ((mul_eq_zero.1 hx).resolve_right (wp _ hI'))
  · exact (hW E n hn D a.1 b.1 a.2 b.2 u hu hc).2.1 _ uc us u1
  · exact ((hW E n hn D a.1 a.1 a.2 a.2 _ uc us).2.2 g hg).1
  · intro a' b b' h1 h2
    rw [hBv, hBv, funext h1, funext h2]
    exact ((hW E n hn D a.1 b.1 a.2 b.2 _ uc us).2.2 g hg).2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PAbsType
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

private lemma exists_projL {F : Type} [AddCommGroup F] [Module ℂ F] (B : F →ₗ⋆[ℂ] F →ₗ[ℂ] ℂ)
    (hsym : ∀ a b, starRingEnd ℂ (B a b) = B b a) (hpos : ∀ a, a ≠ 0 → 0 < (B a a).re)
    (S : Submodule ℂ F) [FiniteDimensional ℂ S] :
    ∃ P : F →ₗ[ℂ] F, (∀ x, P x ∈ S) ∧ ∀ x, ∀ a ∈ S, B a (x - P x) = 0 := by
  let core : InnerProductSpace.Core ℂ F :=
    { inner := fun a b => B a b
      conj_inner_symm := fun a b => hsym b a
      re_inner_nonneg := fun a => by
        by_cases h : a = 0
        · simp [h]
        · exact (hpos a h).le
      add_left := fun a b c => by simp
      smul_left := fun a b r => by simp
      definite := fun a h => by
        by_contra h0
        have h1 := hpos a h0
        have h2 : B a a = 0 := h
        simp [h2] at h1 }
  letI : NormedAddCommGroup F := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ F := InnerProductSpace.ofCore core.toCore
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
  refine ⟨S.starProjection.toLinearMap, fun x => S.starProjection_apply_mem x, fun x a ha => ?_⟩
  have h0 := S.starProjection_inner_eq_zero x a ha
  have h1 : B (x - S.starProjection x) a = 0 := h0
  have h2 := hsym (x - S.starProjection x) a
  rw [h1, map_zero] at h2
  exact h2.symm

private lemma orbit_stable {Γ F : Type} [Group Γ] [AddCommGroup F] [Module ℂ F]
    (R : Representation ℂ Γ F) (x : F) (g : Γ) :
    ∀ a ∈ Submodule.span ℂ (Set.range fun k => R k x),
      R g a ∈ Submodule.span ℂ (Set.range fun k => R k x) := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨k, rfl⟩ := h
    refine Submodule.subset_span ⟨g * k, ?_⟩
    simp [map_mul, Module.End.mul_apply]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

private lemma self_mem_orbit {Γ F : Type} [Group Γ] [AddCommGroup F] [Module ℂ F]
    (R : Representation ℂ Γ F) (x : F) : x ∈ Submodule.span ℂ (Set.range fun k => R k x) :=
  Submodule.subset_span ⟨1, by simp⟩

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.absType_pf :
    AbsType := by
  intro Γ F _ _ _ R B W V Y z hsym hpos hinv hW hV hVf hY hYV hzf hzt
  have hRR : ∀ k a, R k (R k⁻¹ a) = a := fun k a => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hadj : ∀ k a b, B a (R k b) = B (R k⁻¹ a) b := fun k a b => by
    have h := hinv k (R k⁻¹ a) b
    rwa [hRR] at h
  let T : Submodule ℂ F :=
    { carrier := {x | ∀ l : F →ₗ[ℂ] ℂ, (fun k => l (R k x)) ∈ W}
      add_mem' := fun {a b} ha hb l => by
        have h := W.add_mem (ha l) (hb l)
        convert h using 1
        ext k; simp
      zero_mem' := fun l => by
        have h := W.zero_mem
        convert h using 1
        ext k; simp
      smul_mem' := fun c x hx l => by
        have h := W.smul_mem c (hx l)
        convert h using 1
        ext k; simp }
  have hTR : ∀ g, ∀ x ∈ T, R g x ∈ T := fun g x hx l => by
    have h := hW _ (hx l) g
    convert h using 1
    ext k; simp [map_mul, Module.End.mul_apply]
  haveI : FiniteDimensional ℂ Y := hY
  haveI : FiniteDimensional ℂ (V ⊓ T : Submodule ℂ F) :=
    Submodule.finiteDimensional_of_le (S₂ := Y) fun x hx => hYV x hx.1 hx.2
  obtain ⟨P, hPm, hPo⟩ := exists_projL B hsym hpos (V ⊓ T)
  refine ⟨P z, (hPm z).1, hYV _ (hPm z).1 (hPm z).2, ?_⟩
  have hz1T : z - P z ∈ T := T.sub_mem hzt (hPm z).2
  have hZT : Submodule.span ℂ (Set.range fun k => R k (z - P z)) ≤ T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact hTR k _ hz1T
  have hZperp : ∀ a ∈ V ⊓ T, ∀ w ∈ Submodule.span ℂ (Set.range fun k => R k (z - P z)), B a w = 0 := by
    intro a ha w hw
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨k, rfl⟩ := h
      show B a (R k (z - P z)) = 0
      rw [hadj]
      exact hPo z _ ⟨hV _ _ ha.1, hTR _ _ ha.2⟩
    | zero => simp
    | add a' b _ _ ha' hb => rw [map_add (f := _), ha', hb, add_zero]
    | smul c a' _ ha' => rw [map_smul, ha', smul_zero]
  intro v hv
  haveI := hVf v hv
  obtain ⟨Q, hQm, hQo⟩ := exists_projL B hsym hpos (Submodule.span ℂ (Set.range fun k => R k v))
  have hV0V : Submodule.span ℂ (Set.range fun k => R k v) ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact hV k v hv
  have hzero : ∀ d, B d d = 0 → d = 0 := fun d h => by
    by_contra h0
    have h1 := hpos d h0
    simp [h] at h1
  have hQR : ∀ g x, Q (R g x) = R g (Q x) := fun g x => by
    have hd : Q (R g x) - R g (Q x) ∈ Submodule.span ℂ (Set.range fun k => R k v) :=
      Submodule.sub_mem _ (hQm _) (orbit_stable R v g _ (hQm x))
    have h1 := hQo (R g x) _ hd
    have h2 : B (Q (R g x) - R g (Q x)) (R g x - R g (Q x)) = 0 := by
      rw [← map_sub, hadj]
      exact hQo x _ (orbit_stable R v g⁻¹ _ hd)
    have h3 : B (Q (R g x) - R g (Q x)) (Q (R g x) - R g (Q x)) = 0 := by
      have h4 : B (Q (R g x) - R g (Q x)) (Q (R g x) - R g (Q x)) =
          B (Q (R g x) - R g (Q x)) (R g x - R g (Q x)) -
            B (Q (R g x) - R g (Q x)) (R g x - Q (R g x)) := by
        rw [← map_sub]
        congr 1
        abel
      rw [h4, h1, h2, sub_zero]
    exact sub_eq_zero.1 (hzero _ h3)
  have hQT : ∀ w ∈ Submodule.span ℂ (Set.range fun k => R k (z - P z)), Q w ∈ T := fun w hw l => by
    have h := hZT hw (l ∘ₗ Q)
    convert h using 1
    ext k; simp [hQR]
  have hQ0 : Q (z - P z) = 0 := by
    have hw := self_mem_orbit R (z - P z)
    have h1 := hZperp (Q (z - P z)) ⟨hV0V (hQm _), hQT _ hw⟩ _ hw
    have h2 := hQo (z - P z) _ (hQm (z - P z))
    rw [map_sub, h1, zero_sub, neg_eq_zero] at h2
    exact hzero _ h2
  have h := hQo (z - P z) v (self_mem_orbit R v)
  rwa [hQ0, sub_zero] at h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.ExistsCut
noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

open NumberField MeasureTheory Filter GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem borelSp : BorelSpace (H E n 0) := ⟨rfl⟩

attribute [local instance] borelSp

private theorem exists_cut (A : ℝ) : ∃ χ : ℝ → ℂ, Continuous χ ∧ HasCompactSupport χ ∧ ∀ s, |s| ≤ A → χ s = 1 := by
  obtain ⟨c, h1, -, h3, -⟩ := exists_continuous_one_zero_of_isCompact (isCompact_closedBall (0 : ℝ) A)
    (Metric.isOpen_ball (x := (0 : ℝ)) (ε := A + 1)).isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2 (Metric.closedBall_subset_ball (by linarith)))
  refine ⟨fun s => (c s : ℂ), Complex.continuous_ofReal.comp c.continuous,
    h3.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero, fun s hs => ?_⟩
  have : c s = 1 := h1 (by simpa [Real.norm_eq_abs] using hs)
  simp [this]

private def mulL (D : Dom E n 0) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ} (hC : ∀ s, ‖w s‖ ≤ C) :
    Lp ℂ 2 D.ν →L[ℂ] Lp ℂ 2 D.ν :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL D.ν ∞ 2 2
    (memLp_top_of_bound (hw.comp DiscreteGroups.T1.G.continuous_ldet).aestronglyMeasurable C
      (Eventually.of_forall fun x => hC (ldet x)) : MemLp (fun x : H E n 0 => w (ldet x)) ∞ D.ν).toLp

private theorem mulL_ae (D : Dom E n 0) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ} (hC : ∀ s, ‖w s‖ ≤ C)
    (v : Lp ℂ 2 D.ν) : (mulL D hw hC v : H E n 0 → ℂ) =ᵐ[D.ν] fun x => w (ldet x) * (v : H E n 0 → ℂ) x := by
  have hm : MemLp (fun x : H E n 0 => w (ldet x)) ∞ D.ν :=
    memLp_top_of_bound (hw.comp DiscreteGroups.T1.G.continuous_ldet).aestronglyMeasurable C
      (Eventually.of_forall fun x => hC (ldet x))
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) hm.toLp v, hm.coeFn_toLp] with x h1 h2
  refine Eq.trans h1 ?_
  simp only [ContinuousLinearMap.mul_apply']
  rw [h2]

private def mulV (D : Dom E n 0) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ} (hC : ∀ s, ‖w s‖ ≤ C) (ι : Type) [Fintype ι] :
    Hs (ι := ι) D →ₗ[ℂ] Hs (ι := ι) D where
  toFun f := WithLp.toLp 2 fun i => mulL D hw hC (f i)
  map_add' a b := PiLp.ext fun i => map_add (mulL D hw hC) (a i) (b i)
  map_smul' c a := PiLp.ext fun i => map_smul (mulL D hw hC) c (a i)

private theorem mulV_cont (D : Dom E n 0) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ} (hC : ∀ s, ‖w s‖ ≤ C)
    (ι : Type) [Fintype ι] : Continuous (mulV D hw hC ι) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
    (mulL D hw hC).continuous.comp (PiLp.continuous_apply 2 _ i))

private theorem mul_keep (D : Dom E n 0) (π : CuspSub E n) {w : ℝ → ℂ} (hw : Continuous w) {C : ℝ}
    (hC : ∀ s, ‖w s‖ ≤ C) (ι : Type) [Fintype ι] {f : Hs (ι := ι) D} (hf : f ∈ piSp D π ι) :
    mulV D hw hC ι f ∈ piSp D π ι := by
  have hle : Submodule.span ℂ {f | IsPiVec D π f} ≤ (piSp D π ι).comap (mulV D hw hC ι) := by
    refine Submodule.span_le.2 fun g hg => ?_
    choose ψ hψ u hu hu' hgu using hg
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span fun j => ?_)
    refine ⟨ψ j, hψ j, fun s => u j s * w s, (hu j).mul hw, (hu' j).mul_right, ?_⟩
    filter_upwards [mulL_ae D hw hC (g j), hgu j] with x h1 h2
    refine Eq.trans h1 ?_
    rw [h2]
    ring
  have hcl : IsClosed (((piSp D π ι).comap (mulV D hw hC ι)) : Set (Hs (ι := ι) D)) :=
    (show IsClosed (piSp D π ι : Set (Hs (ι := ι) D)) from Submodule.isClosed_topologicalClosure _).preimage
      (mulV_cont D hw hC ι)
  exact Submodule.topologicalClosure_minimal _ hle hcl hf

set_option synthInstance.maxHeartbeats 200000 in
private theorem cv_cont (μ : Measure (H E n 0)) [IsLocallyFiniteMeasure μ] {φ : H E n 0 → ℂ} (hφ : IsTestH φ)
    {u : ℝ → ℂ} (hu : Continuous u) {f : GA E n → ℂ} (hf : Continuous f) : Continuous (cvF μ φ u f) := by
  have hl : Continuous (ldet : H E n 0 → ℝ) := DiscreteGroups.T1.G.continuous_ldet
  haveI : SecondCountableTopology (H E n 0) := inferInstance
  haveI : FirstCountableTopology (H E n 0) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have h1 : Continuous fun x : H E n 0 => ∫ y in tsupport φ, φ y * u (ldet y) * f (x.1 * y.1) ∂μ :=
    continuous_parametric_integral_of_continuous
      (f := fun (x y : H E n 0) => φ y * u (ldet y) * f (x.1 * y.1))
      (((hφ.1.comp continuous_snd).mul (hu.comp (hl.comp continuous_snd))).mul
        (hf.comp ((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd))))
      hφ.2.isCompact
  have h2 : cvF μ φ u f = fun g : GA E n => ∫ y in tsupport φ, φ y * u (ldet y) * f ((g, (1 : GA E 0)).1 * y.1) ∂μ := by
    funext g
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    simp [image_eq_zero_of_notMem_tsupport hy]
  rw [h2]
  exact h1.comp (continuous_id.prodMk continuous_const)

private theorem form_rat (π : CuspSub E n) {ψ : Sm E n} (hψ : ψ ∈ π.V) (γ : ratH E n 0) (y : H E n 0) :
    ψ.1 ((γ : H E n 0) * y).1 = ψ.1 y.1 := by
  obtain ⟨⟨a, b⟩, hγ⟩ := γ.2
  have e : (γ : H E n 0).1 = ratGL E n a := by rw [← hγ]; rfl
  rw [Prod.fst_mul, e]
  exact (π.cusp ψ hψ).1.left a y.1

private theorem cut_value (hB : Basic) (hn : 1 ≤ n) (D : Dom E n 0) (π : CuspSub E n) (hθ : ThetaFix π)
    {ψ : Sm E n} (hψ : ψ ∈ π.V) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {u : ℝ → ℂ} (hu : Continuous u) (R : ℝ) :
    ∃ v ∈ piSp D π Unit, ∀ᵐ x ∂D.ν, |ldet x| ≤ R → (v () : H E n 0 → ℂ) x = cvF D.μ φ u ψ.1 x.1 := by
  obtain ⟨-, hmul, -, -, -, -, -, -, -, hrat, hl, -⟩ := hB E n hn
  set φ' : H E n 0 → ℂ := fun y => φ y * u (ldet y) with hφ'
  have ht : IsTestH φ' := ⟨hφ.1.mul (hu.comp hl), hφ.2.mul_right⟩
  obtain ⟨A, hA⟩ := (hφ.2.isCompact.image hl).isBounded.subset_closedBall (0 : ℝ)
  have hA' : ∀ y, φ y ≠ 0 → |ldet y| ≤ A := fun y hy => by
    have := hA (Set.mem_image_of_mem _ (subset_tsupport φ hy))
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  obtain ⟨χ, hχ, hχs, hχ1⟩ := exists_cut (R + A)
  set f : H E n 0 → ℂ := fun x => ψ.1 x.1 * χ (ldet x) with hf
  have hfL : MemLp f 2 D.ν := (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ χ hχ hχs).1
  let g : Hs (ι := Unit) D := WithLp.toLp 2 fun _ => hfL.toLp f
  have hg : g ∈ piSp D π Unit :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span fun _ => ⟨ψ, hψ, χ, hχ, hχs, hfL.coeFn_toLp⟩)
  obtain ⟨T, hT, -, -⟩ := PositivityTheory.Rg.BcB.E1.kernel_operator_exists_holds E n 0 D Unit (fun _ _ => φ') (fun _ _ => ht)
  refine ⟨T g, DiscreteGroups.T1.G.piInv E n hn D π hθ Unit _ T (fun _ _ => ht) hT g hg, ?_⟩
  filter_upwards [hT g ()] with x hx hxR
  let X : E1.Ctx :=
    haveI := CuspidalL2GL.t2Space_GA E n
    haveI := CuspidalL2GL.t2Space_GA E 0
    haveI := CuspidalL2GL.locallyCompactSpace_GA E n
    haveI := CuspidalL2GL.locallyCompactSpace_GA E 0
    haveI := CuspidalL2GL.secondCountableTopology_GA E n
    haveI := CuspidalL2GL.secondCountableTopology_GA E 0
    haveI := (E1.ratProper_holds E n).2.1
    haveI := (E1.ratProper_holds E 0).2.1
    { G := H E n 0
      ms := PositivityTheory.Rg.BcB.E.borelH E n 0
      bs := ⟨rfl⟩
      μ := D.μ
      haar := { toIsFiniteMeasureOnCompacts :=
                  @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ D.μ D.haar.2.2.2
                toIsMulLeftInvariant := D.haar.1
                toIsOpenPosMeasure := D.haar.2.2.1 }
      Γ := ratH E n 0
      cn := (((ratGL E n).prodMap (ratGL E 0)).rangeRestrict_surjective).countable
      proper := by
        intro C hC
        have h1 := (E1.ratProper_holds E n).2.2 _ (hC.image continuous_fst)
        have h2 := (E1.ratProper_holds E 0).2.2 _ (hC.image continuous_snd)
        refine ((h1.prod h2).image ((ratGL E n).prodMap (ratGL E 0)).rangeRestrict).subset ?_
        rintro ⟨_, γ, rfl⟩ hγ
        exact ⟨γ, ⟨⟨_, hγ, rfl⟩, ⟨_, hγ, rfl⟩⟩, rfl⟩
      F := D.F
      fd := D.fd }
  have hinv : ∀ (δ : ratH E n 0) (y : H E n 0), f ((δ : H E n 0) * y) = f y := fun δ y => by
    show ψ.1 ((δ : H E n 0) * y).1 * χ (ldet ((δ : H E n 0) * y)) = ψ.1 y.1 * χ (ldet y)
    rw [form_rat π hψ δ y, hmul, (hrat δ).1, zero_add]
  have e1 : ∫ y, kerH φ' x y * (g () : H E n 0 → ℂ) y ∂D.ν = ∫ y, kerH φ' x y * f y ∂D.ν :=
    integral_congr_ae (hfL.coeFn_toLp.mono fun y hy => by
      show kerH φ' x y * (hfL.toLp f : H E n 0 → ℂ) y = _
      rw [hy])
  have e2 : ∫ y, kerH φ' x y * f y ∂D.ν = ∫ y, φ' (x⁻¹ * y) * f y ∂D.μ :=
    (DiscreteGroups.T1.G.unfold X PositivityTheory.Rg.BcB.E1.kerBasic PositivityTheory.Rg.BcB.E1.kernel_rows_columns_square_integrable ht hinv hfL x).2
  have e3 : ∫ y, φ' (x⁻¹ * y) * f y ∂D.μ = ∫ y, φ' y * f (x * y) ∂D.μ := by
    haveI : D.μ.IsMulLeftInvariant := D.haar.1
    have h := integral_mul_left_eq_self (μ := D.μ) (fun y => φ' y * f (x * y)) x⁻¹
    simpa only [mul_inv_cancel_left] using h
  have e4 : ∫ y, φ' y * f (x * y) ∂D.μ = cvF D.μ φ u ψ.1 x.1 := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases h0 : φ y = 0
    · simp [hφ', h0]
    · have hy := hA' y h0
      have hc : χ (ldet (x * y)) = 1 := hχ1 _ (by
        rw [hmul]
        exact (abs_add_le _ _).trans (add_le_add hxR hy))
      simp only [hφ', hf, hc, mul_one, Prod.fst_mul]
  rw [hx]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  exact e1.trans (e2.trans (e3.trans e4))

private theorem cv_inS (hB : Basic) (hn : 1 ≤ n) (D : Dom E n 0) (π : CuspSub E n) (hθ : ThetaFix π)
    {ψ : Sm E n} (hψ : ψ ∈ π.V) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {u : ℝ → ℂ} (hu : Continuous u) :
    InS D π (cvF D.μ φ u ψ.1) := by
  intro w hw hws
  obtain ⟨R, hR⟩ := hws.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨C, hC⟩ := hw.bounded_above_of_compact_support hws
  obtain ⟨v, hv, hva⟩ := cut_value hB hn D π hθ hψ hφ hu R
  refine ⟨mulV D hw hC Unit v, mul_keep D π hw hC Unit hv, ?_⟩
  filter_upwards [mulL_ae D hw hC (v ()), hva] with x h1 h2
  refine Eq.trans h1 ?_
  by_cases h0 : w (ldet x) = 0
  · simp [h0]
  · have hx := hR (subset_tsupport w h0)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx
    rw [h2 hx, mul_comm]

private theorem form_inS (hn : 1 ≤ n) (D : Dom E n 0) (π : CuspSub E n) (hθ : ThetaFix π)
    {ψ : Sm E n} (hψ : ψ ∈ π.V) : InS D π ψ.1 := by
  intro w hw hws
  have hL := (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ w hw hws).1
  exact ⟨WithLp.toLp 2 fun _ => hL.toLp _,
    Submodule.le_topologicalClosure _ (Submodule.subset_span fun _ => ⟨ψ, hψ, w, hw, hws, hL.coeFn_toLp⟩),
    hL.coeFn_toLp⟩

end SlopeTestRemainingChoices

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.cvIn_pf :
    Basic → AeEq → CvIn := by
  intro hB _ E _ _ _ n hn D π hθ ψ hψ
  have hc := DiscreteGroups.T1.G.continuous_of_mem π hψ
  have hμ : MeasureTheory.IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  refine ⟨⟨hc, (π.cusp ψ hψ).1.left, hθ.1 ψ hψ, fun w hw hws =>
    (DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ w hw hws).1⟩, fun φ u hφ hu => ?_⟩
  have hin := cv_inS hB hn D π hθ hψ hφ hu
  refine ⟨⟨cv_cont D.μ hφ hu hc, fun γ g => ?_, fun t g => ?_, fun w hw hws => ?_⟩, hin, form_inS hn D π hθ hψ⟩
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show _ * ψ.1 (_ * g * y.1) = _ * ψ.1 (g * y.1)
    rw [mul_assoc (GlobalTheory.CuspRep.ratGL E n γ) g y.1, (π.cusp ψ hψ).1.left]
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show _ * ψ.1 (_ * g * y.1) = _ * ψ.1 (g * y.1)
    rw [mul_assoc (GlobalTheory.UnitaryBC.splitCentre E n t) g y.1, hθ.1 ψ hψ]
  · obtain ⟨v, -, hv⟩ := hin w hw hws
    exact (MeasureTheory.Lp.memLp (v ())).ae_eq hv
end
end
