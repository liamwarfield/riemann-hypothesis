module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.IntegrableShift

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PEvalBasis
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.evalBasis_pf :
    EvalBasis := by
  intro X V _ _ ev hsep W hW
  classical
  haveI := hW
  let r : X → Module.Dual ℂ W := fun x => (ev x).domRestrict W
  have hspan : Submodule.span ℂ (Set.range r) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    obtain ⟨v, rfl⟩ := (Module.evalEquiv ℂ W).surjective f
    have hv : (v : V) = 0 := hsep v fun x => by
      have h := hf (Submodule.subset_span (Set.mem_range_self x))
      simpa [r] using h
    have hv0 : v = 0 := Subtype.ext hv
    exact hf0 (by simp [hv0])
  obtain ⟨b, hbs, hbspan, hli⟩ := exists_linearIndependent ℂ (Set.range r)
  let B0 := Module.Basis.mk hli (by simp [hbspan, hspan])
  haveI : Finite b := Module.Finite.finite_basis B0
  letI := Fintype.ofFinite b
  let B := B0.reindex (Fintype.equivFin b)
  have hx : ∀ i, ∃ x, r x = B i := fun i => by
    have hm : B i ∈ b := by simp [B, B0]
    exact hbs hm
  choose x hx using hx
  refine ⟨Fintype.card b, x, fun i => ((Module.evalEquiv ℂ W).symm (B.coord i) : W),
    fun i => Subtype.coe_prop _, fun v hv => ?_⟩
  have key : (⟨v, hv⟩ : W) = ∑ i, (B i ⟨v, hv⟩) • (Module.evalEquiv ℂ W).symm (B.coord i) := by
    apply (Module.evalEquiv ℂ W).injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    exact (B.sum_dual_apply_smul_coord _).symm
  have h2 := congrArg (Subtype.val) key
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  refine h2.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [← hx i]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.LdetRatMul
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped Pointwise

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ldet_rat_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (γ : ratH E n 0) (x : H E n 0) : ldet ((γ : H E n 0) * x) = ldet x := by
  obtain ⟨⟨a, b⟩, hab⟩ := γ.2
  have h1 : (γ : H E n 0).1 = ratGL E n a := by rw [← hab]; rfl
  change logAbs (((γ : H E n 0).1 * x.1).val.det) = logAbs x.1.val.det
  rw [DiscreteGroups.T1.G.Dcy.logAbs_det_mul', h1, DiscreteGroups.T1.G.Dcy.logAbs_ratGL', zero_add]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.aeEq_pf :
    Basic → AeEq := by
  intro _ E _ _ _ n D f g I hf hg hfi hgi hI hae x hx
  by_contra hne
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  set S : Set (H E n 0) := {y | ldet y ∈ I ∧ f y ≠ g y} with hS
  have hSo : IsOpen S :=
    (hI.preimage continuous_ldet).inter (isOpen_ne_fun hf hg)
  have hSx : S.Nonempty := ⟨x, hx, hne⟩
  haveI : Countable (ratH E n 0) := DiscreteGroups.T1.G.Dcy.countable_ratH'
  haveI : D.μ.IsMulLeftInvariant := D.haar.1
  haveI : D.μ.IsOpenPosMeasure := D.haar.2.2.1
  haveI : MeasurableConstSMul (ratH E n 0) (H E n 0) :=
    ⟨fun γ => (continuous_const.mul continuous_id : Continuous fun y : H E n 0 => (γ : H E n 0) * y).measurable⟩
  haveI : SMulInvariantMeasure (ratH E n 0) (H E n 0) D.μ :=
    ⟨fun γ s _ => measure_preimage_mul D.μ (γ : H E n 0) s⟩
  have key : ∀ (δ : ratH E n 0) (y : H E n 0), y ∈ S → (δ : H E n 0) * y ∈ S := by
    intro δ y hy
    refine ⟨?_, ?_⟩
    · rw [ldet_rat_mul]; exact hy.1
    · rw [hfi δ y, hgi δ y]; exact hy.2
  have hinv : ∀ γ : ratH E n 0, γ • S = S := by
    intro γ
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact key γ y hy
    · intro y hy
      refine ⟨(γ⁻¹ : ratH E n 0) • y, ?_, smul_inv_smul γ y⟩
      exact key γ⁻¹ y hy
  have hnull : D.μ (S ∩ D.F) = 0 := by
    have h0 : D.ν S = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 hae)
      intro y hy h
      exact hy.2 (h hy.1)
    rwa [Dom.ν, Measure.restrict_apply hSo.measurableSet] at h0
  have hz : D.μ S = 0 := D.fd.measure_zero_of_invariant S hinv hnull
  exact (hSo.measure_pos D.μ hSx).ne' hz
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PBasic
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem logAbs_det_centre (τ : ℝ) :
    logAbs (splitCentre E n τ).val.det = Module.finrank ℚ E * (n * τ) := by
  have h := congrArg (fun g : GA E n => logAbs g.val.det) (Dcy.splitCentre_mul_tor (E := E) (n := n) τ (fun _ => 0))
  simp only [Dcy.logAbs_det_mul', Dcy.logAbs_det_tor] at h
  simpa using h

private theorem ldet_ac (hn : 1 ≤ n) (t : ℝ) : ldet (ac E n t) = t := by
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  change logAbs (splitCentre E n (t / (n * Module.finrank ℚ E))).val.det = t
  rw [logAbs_det_centre]
  field_simp

private theorem logAbs_det_inv (g : GA E n) : logAbs (g⁻¹ : GA E n).val.det = -logAbs g.val.det := by
  have h := Dcy.logAbs_det_mul' g g⁻¹
  have h1 := Dcy.logAbs_ratGL' (E := E) (n := n) 1
  rw [map_one] at h1
  rw [mul_inv_cancel, h1] at h
  linarith

private theorem logAbs_det_theta (g : GA E n) : logAbs (thetaA E n g).val.det = -logAbs g.val.det := by
  have h : (thetaA E n g).val.det = conjAd E (g⁻¹ : GA E n).val.det := by
    change (((g⁻¹ : GA E n).val.map (conjAd E))ᵀ).det = _
    rw [Matrix.det_transpose]
    exact (RingHom.map_det (conjAd E) _).symm
  rw [h, GlobalTheory.CompanionTheory.DegPairingProof.logAbs_conj D1.conjPlaces, logAbs_det_inv]

end SlopeTestRemainingChoices

theorem basic_pf : Basic := by
  intro E _ _ _ n hn
  refine ⟨ldet_ac hn, fun x y => Dcy.logAbs_det_mul' x.1 y.1, fun t x => ?_, fun s t => ?_, ?_, ?_, fun x => ?_, fun x => ?_,
    fun x y => ?_, ?_, continuous_ldet, ?_⟩
  · refine Prod.ext ?_ ?_
    · exact CuspidalL2GL.splitCentre_comm _ _
    · change 1 * x.2 = x.2 * 1
      rw [one_mul, mul_one]
  · refine Prod.ext ?_ (mul_one _).symm
    change splitCentre E n ((s + t) / _) = splitCentre E n (s / _) * splitCentre E n (t / _)
    rw [add_div, CuspidalL2GL.splitCentre_add]
  · refine Prod.ext ?_ rfl
    change splitCentre E n (0 / _) = 1
    rw [zero_div, CuspidalL2GL.splitCentre_zero]
  · exact (GlobalTheory.OneRep.SplitTwist.continuous_splitCentre.comp (continuous_id.div_const _)).prodMk continuous_const
  · exact logAbs_det_theta x.1
  · exact Prod.ext ((thetaBasic_holds E n).2.1 x.1) ((thetaBasic_holds E 0).2.1 x.2)
  · exact Prod.ext (map_mul (thetaA E n) x.1 y.1) (map_mul (thetaA E 0) x.2 y.2)
  · rintro ⟨_, γ, rfl⟩
    refine ⟨Dcy.logAbs_ratGL' γ.1, ⟨(thetaE E n γ.1, thetaE E 0 γ.2), ?_⟩⟩
    exact Prod.ext ((thetaBasic_holds E n).2.2 γ.1).symm ((thetaBasic_holds E 0).2.2 γ.2).symm
  · exact (((thetaBasic_holds E n).1.comp continuous_fst).prodMk ((thetaBasic_holds E 0).1.comp continuous_snd))

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.GFacPf
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical ENNReal

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

attribute [local instance] borelH

theorem gFac_pf : FinFac → DropP → GFac := by
  intro hF hD E _ _ _ n ι _ s
  obtain ⟨p, hp⟩ := hF E n ι s
  refine ⟨p, fun m x y => ?_⟩
  have hd := hD E n ι s m
  rw [hd x y]
  simp only [hd (ac E n (ldet x) * p.x _) y, Gk, ContinuousLinearMap.comp_apply]
  have hmem : ∀ i, (piSp s.D s.π ι).starProjection (m.Uπ (s.k₂ y i)) ∈ piSp s.D s.π ι := fun i =>
    Submodule.starProjection_apply_mem _ _
  calc _ = ∑ i, ∑ b, (p.w b).1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * p.x b) i)
          ((piSp s.D s.π ι).starProjection (m.Uπ (s.k₂ y i))) :=
        Finset.sum_congr rfl fun i _ => hp _ (hmem i) x i
    _ = _ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PPointRep
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem kerH_left {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (φ : H E n 0 → ℂ) (γ : ratH E n 0) (x y : H E n 0) :
    kerH φ ((γ : H E n 0) * x) y = kerH φ x y := by
  unfold kerH
  rw [← finsum_comp_equiv (Equiv.mulLeft γ)]
  refine finsum_congr fun δ => ?_
  congr 1
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, _root_.mul_inv_rev]
  group

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.pointRep_pf :
    AeEq → KInv → PointRep := by
  intro hA hK E _ _ _ n ι _ s Φ T hΦ hT h g hg x i
  obtain ⟨k, k', hk⟩ := vecsEx E n 0 s.D ι Φ Φ T T 0 hΦ hΦ hT hT
  have hF : Continuous fun x => inner ℂ (s.k₁ x i) h :=
    ((s.vecs.cont i).1).inner continuous_const
  have hG : Continuous fun x => inner ℂ (k x i) g := ((hk.cont i).1).inner continuous_const
  have hIF : Inv fun x => inner ℂ (s.k₁ x i) h := fun γ x => by
    simp only [(hK E n ι s).1 γ x]
  have hIG : Inv fun x => inner ℂ (k x i) g := fun γ x => by
    simp only [hk.rep₁, kerH_left]
  have hae : ∀ᵐ x ∂s.D.ν, ldet x ∈ (Set.univ : Set ℝ) →
      inner ℂ (s.k₁ x i) h = inner ℂ (k x i) g := by
    have h1 := s.o₁ h i
    have h2 := hT g i
    rw [hg] at h1
    filter_upwards [h1, h2] with y a1 a2 _
    rw [s.vecs.rep₁, hk.rep₁, ← a1, a2]
  have := hA E n s.D _ _ Set.univ hF hG hIF hIG isOpen_univ hae x (Set.mem_univ _)
  rw [this, hk.rep₁]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.KerRight
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open NumberField PositivityTheory.Rg.BcB.E MeasureTheory

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem ker_left (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {γ : H E n 0}
    (hγ : γ ∈ ratH E n 0) (x y : H E n 0) : kerH φ (γ * x) y = kerH φ x y :=
  ((PositivityTheory.Rg.BcB.E1.kerBasic (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) φ hφ).2.2.1 γ hγ x y).1

private theorem ker_right (D : Dom E n 0) {φ : H E n 0 → ℂ} (hφ : IsTestH φ) {γ : H E n 0}
    (hγ : γ ∈ ratH E n 0) (x y : H E n 0) : kerH φ x (γ * y) = kerH φ x y :=
  ((PositivityTheory.Rg.BcB.E1.kerBasic (PositivityTheory.Rg.BcB.E1.ctx PositivityTheory.Rg.BcB.E1.ratProper_holds D) φ hφ).2.2.1 γ hγ x y).2

private theorem th_mul' (x y : H E n 0) :
    PositivityTheory.Rg.BcB.E1.th (x * y) = PositivityTheory.Rg.BcB.E1.th x * PositivityTheory.Rg.BcB.E1.th y :=
  Prod.ext (map_mul (PositivityTheory.Rg.BcB.thetaA E n) x.1 y.1) (map_mul (PositivityTheory.Rg.BcB.thetaA E 0) x.2 y.2)

private theorem th_rat {δ : H E n 0} (hδ : δ ∈ ratH E n 0) : PositivityTheory.Rg.BcB.E1.th δ ∈ ratH E n 0 := by
  obtain ⟨γ, rfl⟩ := hδ
  refine ⟨(PositivityTheory.Rg.BcB.thetaE E n γ.1, PositivityTheory.Rg.BcB.thetaE E 0 γ.2), ?_⟩
  exact Prod.ext ((PositivityTheory.Rg.BcB.E1.thetaBasic_holds E n).2.2 γ.1).symm
    ((PositivityTheory.Rg.BcB.E1.thetaBasic_holds E 0).2.2 γ.2).symm

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.kInv_pf :
    KInv := by
  intro E _ _ _ n ι _ s
  refine ⟨fun γ x => ?_, fun γ x => ?_⟩
  · funext i
    refine ext_inner_right ℂ fun u => ?_
    rw [s.vecs.rep₁, s.vecs.rep₁]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ker_left s.D (s.t₁ i j) γ.2]
  · funext i
    refine ext_inner_left ℂ fun u => ?_
    rw [s.vecs.rep₂, s.vecs.rep₂]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [th_mul', ker_right s.D (s.t₂ j l) (th_rat γ.2)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SuppPf
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.supp_pf :
    Basic → Zero → KInv → PSupp → Ker → Supp := by
  intro hB hZ hK hP hKer E _ _ _ n ι _ s m R hR x y hxy
  obtain ⟨hac, hmul, -, -, hone, -, hldth, hthth, hthmul, hrat, -, hthc⟩ := hB E n s.pos
  have hl1 : ldet (1 : H E n 0) = 0 := by
    have h := hac 0
    rwa [hone] at h
  have hlinv : ∀ z : H E n 0, ldet z⁻¹ = -ldet z := by
    intro z
    have h := hmul z z⁻¹
    rw [mul_inv_cancel, hl1] at h
    linarith
  have hf : Continuous fun w : H E n 0 => m.G x (th w) := by
    show Continuous fun w : H E n 0 => ∑ i, inner ℂ (s.k₁ x i) (m.Uπ (s.k₂ (th w) i))
    refine continuous_finsetSum _ fun i _ => ?_
    exact continuous_const.inner (m.Uπ.continuous.comp (((s.vecs.cont i).2).comp hthc))
  have hinv : Inv fun w : H E n 0 => m.G x (th w) := by
    intro γ w
    have h := (hK E n ι s).2 ⟨th (γ : H E n 0), (hrat γ).2⟩ (th w)
    show Gk s.k₁ s.k₂ m.Uπ x (th ((γ : H E n 0) * w)) = Gk s.k₁ s.k₂ m.Uπ x (th w)
    rw [hthmul]
    unfold Gk
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show s.k₂ (th (γ : H E n 0) * th w) = s.k₂ (th w) from h]
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = (|ldet x + ldet y| - R) / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have key := hZ E n s.D (fun w => m.G x (th w)) (Set.Ioo (-ldet y - δ) (-ldet y + δ)) hf hinv isOpen_Ioo ?_ (th y) ?_
  · simpa only [hthth] using key
  · intro v hv
    refine ((hKer E n ι s m v x).2).trans ?_
    have hPv := hP E n s.D s.π (-ldet y - δ) (-ldet y + δ) v
      (hv.mono fun w h h' => h fun hI => h' (Set.Ioo_subset_Icc_self hI))
    apply integral_eq_zero_of_ae
    filter_upwards [hPv] with w hw
    by_cases hI : ldet w ∈ Set.Icc (-ldet y - δ) (-ldet y + δ)
    · have hk : kerH m.φ x w = 0 := by
        unfold kerH
        refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
        by_contra hne
        have h1 := hR _ hne
        rw [hmul, hmul, hlinv, (hrat γ).1] at h1
        obtain ⟨a1, a2⟩ := abs_le.mp h1
        obtain ⟨b1, b2⟩ := hI
        rcases abs_cases (ldet x + ldet y) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hδ <;> linarith
      simp [hk]
    · simp [hw hI]
  · rw [hldth]
    exact ⟨by linarith, by linarith⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.ZeroPf
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory Filter GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.zero_pf :
    AeEq → Zero := by
  intro hAe E _ _ _ n D f I hf hinv hI h
  classical
  haveI := CuspidalL2GL.t2Space_GA E n
  haveI := CuspidalL2GL.t2Space_GA E 0
  haveI := CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := CuspidalL2GL.locallyCompactSpace_GA E 0
  haveI := CuspidalL2GL.secondCountableTopology_GA E n
  haveI := CuspidalL2GL.secondCountableTopology_GA E 0
  haveI : SigmaCompactSpace (H E n 0) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  haveI : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  have key : ∀ K : Set (H E n 0), IsCompact K → ∀ᵐ x ∂D.ν, x ∈ K → ldet x ∈ I → f x = 0 := by
    intro K hK
    set S : Set (H E n 0) := K ∩ ldet ⁻¹' I with hS
    have hSm : MeasurableSet S :=
      hK.isClosed.measurableSet.inter (hI.preimage continuous_ldet).measurableSet
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
    have hνS : D.ν S < ⊤ :=
      lt_of_le_of_lt ((Measure.restrict_apply_le _ _).trans (measure_mono Set.inter_subset_left))
        (hK.measure_lt_top_of_nhdsWithin fun x _ => D.μ.finiteAt_nhdsWithin x K)
    set w : H E n 0 → ℂ := S.indicator fun x => starRingEnd ℂ (f x) with hwdef
    have hw : MemLp w 2 D.ν := by
      rw [hwdef, memLp_indicator_iff_restrict hSm.nullMeasurableSet]
      haveI : IsFiniteMeasure (D.ν.restrict S) := isFiniteMeasure_restrict.2 hνS.ne
      refine MemLp.of_bound (Complex.continuous_conj.comp hf).aestronglyMeasurable B
        ((ae_restrict_iff' hSm).2 (Eventually.of_forall fun x hx => ?_))
      simpa using hB x hx.1
    have hv : (hw.toLp w : H E n 0 → ℂ) =ᵐ[D.ν] w := hw.coeFn_toLp
    have h0 := h (hw.toLp w) (hv.mono fun y hy hl => by
      rw [hy]
      exact Set.indicator_of_notMem (by exact fun hs => hl hs.2) _)
    have hpt : ∀ y, w y * f y = ((‖w y‖ ^ 2 : ℝ) : ℂ) := by
      intro y
      by_cases hy : y ∈ S
      · simp only [hwdef, Set.indicator_of_mem hy, RCLike.norm_conj]
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      · simp [hwdef, Set.indicator_of_notMem hy]
    have h1 : ∫ y, ‖w y‖ ^ 2 ∂D.ν = 0 := by
      have e : ∫ y, (hw.toLp w : H E n 0 → ℂ) y * f y ∂D.ν = ∫ y, ((‖w y‖ ^ 2 : ℝ) : ℂ) ∂D.ν :=
        integral_congr_ae (hv.mono fun y hy => by
          show (hw.toLp w : H E n 0 → ℂ) y * f y = ((‖w y‖ ^ 2 : ℝ) : ℂ)
          rw [hy, hpt])
      rw [e, integral_complex_ofReal] at h0
      exact_mod_cast h0
    have hint : Integrable (fun y => ‖w y‖ ^ 2) D.ν := hw.integrable_norm_pow two_ne_zero
    have h2 := (integral_eq_zero_iff_of_nonneg (fun y => by positivity) hint).1 h1
    refine h2.mono fun x hx hxK hxI => ?_
    have hx0 : w x = 0 := by simpa using hx
    have hxS : x ∈ S := ⟨hxK, hxI⟩
    rw [hwdef, Set.indicator_of_mem hxS] at hx0
    simpa using hx0
  have all : ∀ᵐ x ∂D.ν, ∀ m : ℕ, x ∈ compactCovering (H E n 0) m → ldet x ∈ I → f x = 0 :=
    ae_all_iff.2 fun m => key _ (isCompact_compactCovering _ m)
  refine hAe E n D f (fun _ => 0) I hf continuous_const hinv (fun _ _ => rfl) hI (all.mono fun x hx hl => ?_)
  obtain ⟨m, hm⟩ := exists_mem_compactCovering x
  exact hx m hm hl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PFinFac
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private def evAt {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (π : CuspSub E n) (x : H E n 0) :
    π.V →ₗ[ℂ] ℂ where
  toFun ψ := ψ.1.1 x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.finFac_pf :
    Basic → EvalBasis → FinGen → FinFac := by
  intro hB hE hG E _ _ _ n ι _ s
  obtain ⟨hl, hmul, -⟩ := hB E n s.pos
  obtain ⟨W, hWV, hWf, hW⟩ := hG E n ι s
  have sep : ∀ ψ : s.π.V, (∀ x : {x : H E n 0 // ldet x = 0}, evAt s.π x.1 ψ = 0) → ψ = 0 := by
    intro ψ h
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    have hy : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)) = 0 := by
      rw [hmul, hl]; ring
    have h0 := h ⟨_, hy⟩
    have h1 := s.fix.1 ψ.1 ψ.2 (-ldet ((g, 1) : H E n 0) / (n * Module.finrank ℚ E)) g
    exact h1.symm.trans h0
  haveI : FiniteDimensional ℂ W := hWf
  obtain ⟨d, xs, ws, hw, hrep⟩ := hE {x : H E n 0 // ldet x = 0} s.π.V (fun x => evAt s.π x.1) sep
    (LinearMap.range (Submodule.inclusion hWV)) inferInstance
  refine ⟨{ B := Fin d, w := fun b => (ws b).1, x := fun b => (xs b).1, mem := fun b => (ws b).2,
            zero := fun b => (xs b).2 }, ?_⟩
  have key : ∀ v : Hs (ι := ι) s.D, IsPiVec s.D s.π v → ∀ (x : H E n 0) (i : ι),
      inner ℂ (s.k₁ x i) v =
        ∑ b, (ws b).1.1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) v := by
    intro v hv x i
    obtain ⟨ψ, hψ, hval⟩ := hW v hv i (ldet x)
    have hb : ∀ b, inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) v = ψ.1 (xs b).1.1 := by
      intro b
      rw [hval _ (by rw [hmul, hl, (xs b).2, add_zero])]
      exact s.fix.1 ψ (hWV hψ) _ _
    have hr := congrArg (evAt s.π x) (hrep ⟨ψ, hWV hψ⟩ ⟨⟨ψ, hψ⟩, rfl⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at hr
    rw [hval x rfl]
    refine hr.trans (Finset.sum_congr rfl fun b _ => ?_)
    rw [map_smul, hb b, smul_eq_mul, mul_comm]
    rfl
  intro v hv x i
  let L : Hs (ι := ι) s.D →L[ℂ] ℂ := innerSL ℂ (s.k₁ x i) -
    ∑ b, (ws b).1.1 x.1 • innerSL ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i)
  have hL : ∀ f, L f = inner ℂ (s.k₁ x i) f -
      ∑ b, (ws b).1.1 x.1 * inner ℂ (s.k₁ (ac E n (ldet x) * (xs b).1) i) f := by
    intro f
    simp [L, ContinuousLinearMap.sum_apply]
  have hle : Submodule.span ℂ {f | IsPiVec s.D s.π f} ≤ LinearMap.ker (L : Hs (ι := ι) s.D →ₗ[ℂ] ℂ) :=
    Submodule.span_le.2 fun f hf => by
      have := key f hf x i
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      rw [hL, this, sub_self]
  have hv' : v ∈ closure ((Submodule.span ℂ {f | IsPiVec s.D s.π f} : Submodule ℂ (Hs (ι := ι) s.D)) : Set (Hs (ι := ι) s.D)) := hv
  have h0 : L v = 0 :=
    closure_minimal (t := {f | L f = 0}) (fun f hf => LinearMap.mem_ker.1 (hle hf))
      (isClosed_eq L.continuous continuous_const) hv'
  rw [hL] at h0
  exact sub_eq_zero.1 h0

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PRangeW
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem ac_zero (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : ac E n 0 = 1 := by
  unfold ac
  rw [zero_div, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero]
  rfl

private theorem test_trM {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {ι : Type} [Fintype ι]
    {Φ : Matrix ι ι (H E n 0 → ℂ)} (hΦ : IsTestM Φ) (M : Matrix ι ι ℂ) :
    Continuous (trM Φ M) ∧ HasCompactSupport (trM Φ M) := by
  have e : trM Φ M = ∑ i, ∑ j, fun y => Φ i j y * M j i := by
    funext y
    simp [trM, Finset.sum_apply]
  constructor
  · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hΦ i j).1.mul continuous_const
  · rw [e]
    exact HasCompactSupport.finset_sum fun i _ => HasCompactSupport.finset_sum fun j _ => (hΦ i j).2.mul_right

private theorem ldet_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {φ : H E n 0 → ℂ}
    (hc : HasCompactSupport φ) : ∃ N : ℕ, ∀ z, φ z ≠ 0 → |ldet z| ≤ N := by
  obtain ⟨R, hR⟩ := (hc.isCompact.image (continuous_abs.comp (continuous_ldet (E := E) (n := n)))).bddAbove
  obtain ⟨N, hN⟩ := exists_nat_ge R
  exact ⟨N, fun z hz => (hR ⟨z, subset_tsupport _ hz, rfl⟩).trans hN⟩

private theorem cut_cont (N : ℕ) : Continuous fun t : ℝ => ((Dcy.chi N t : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (Dcy.continuous_chi N)

private theorem cut_supp (N : ℕ) : HasCompactSupport fun t : ℝ => ((Dcy.chi N t : ℝ) : ℂ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((N : ℝ) + 1)) fun t ht => by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at ht
    rw [Dcy.chi_eq_zero ht.le, Complex.ofReal_zero]

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.rangeW_pf :
    Rep → RangeW := by
  intro hR E _ _ _ n ι _ s p hF m ψ hψ x₀ h₀
  obtain ⟨N, hN⟩ := ldet_bound (test_trM m.t s.M).2
  set u : ℝ → ℂ := fun t => ((Dcy.chi N t : ℝ) : ℂ) with hu
  have rep := fun y => hR E n ι s m ψ hψ u (cut_cont N) (cut_supp N) y
  have key : ∀ y : H E n 0, ldet y = 0 →
      ∫ x, ψ.1 x.1 * m.G y x * u (ldet x) ∂s.D.ν = ∫ z, m.φ z * ψ.1 (thetaA E n (y.1 * z.1)) ∂s.D.μ := by
    intro y hy
    rw [(rep y).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : m.φ z = 0
    · simp [hz]
    · have h1 : |(-(ldet y + ldet z))| ≤ N := by
        rw [hy, zero_add, abs_neg]
        exact hN z hz
      simp only [hu, Dcy.chi_eq_one h1, Complex.ofReal_one, mul_one]
  rw [← key x₀ h₀]
  have hG : ∀ x, ψ.1 x.1 * m.G x₀ x * u (ldet x) =
      ∑ b, (p.w b).1 x₀.1 * (ψ.1 x.1 * m.G (p.x b) x * u (ldet x)) := by
    intro x
    rw [hF m x₀ x, h₀, ac_zero, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [one_mul]
    ring
  simp_rw [hG]
  rw [integral_finsetSum _ fun b _ => ((rep (p.x b)).1).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, key (p.x b) (p.zero b)]

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PInCut
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
private theorem deg_finrank_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (x : GA E n)
    (W : Submodule E (Fin n → E)) (hW : Module.finrank E W = 0) : deg x W = 0 := by
  have key : ∀ (k : ℕ) (M : Matrix (Fin n) (Fin k) E), k = 0 → degM x M = 0 := by
    rintro k M rfl
    exact degM_zero x M
  exact key _ _ hW

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
private theorem logSize_inv' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (h : GA E n) :
    logSize (h⁻¹ : GA E n) = logSize h := by
  simp only [logSize, inv_inv]
  exact add_comm _ _

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
private theorem tau_le_prof {n k : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) (h1 : 1 ≤ k) (hk : k ≤ n) : τ ≤ prof n τ k := by
  have a : (1 : ℝ) ≤ k := by exact_mod_cast h1
  have b : (k : ℝ) ≤ n := by exact_mod_cast hk
  have c : (1 : ℝ) ≤ 2 * n + 1 - k := by linarith
  have d : (1 : ℝ) ≤ (k : ℝ) * (2 * n + 1 - k) := by nlinarith
  have e : τ * 1 ≤ τ * ((k : ℝ) * (2 * n + 1 - k)) := mul_le_mul_of_nonneg_left d hτ
  simp only [prof]
  nlinarith

open NumberField PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E GlobalTheory.CuspRep GlobalTheory.UnitaryBC in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.inCut_pf :
    InCut := by
  intro E _ _ _ n
  obtain ⟨C, hC0, hC⟩ := E1.degRight E n
  obtain ⟨B, hB⟩ := (D1.degBdd E n).1 (1 : GA E n)
  have hB' : ∀ W, deg (1 : GA E n) W ≤ B := fun W => hB ⟨W, rfl⟩
  set A : ℝ := deg (1 : GA E n) ⊤ with hA
  refine ⟨|B| + |A| + 2 * C + 1, by positivity, fun τ g hτ => ?_⟩
  have hr : 0 ≤ redSize g := ((E1.redBasic E n).2.1 g).1
  have hcr : C * redSize g ≤ (|B| + |A| + 2 * C + 1) * redSize g := by
    apply mul_le_mul_of_nonneg_right _ hr
    have := abs_nonneg B
    have := abs_nonneg A
    linarith
  have hexp : (|B| + |A| + 2 * C + 1) * (1 + redSize g) =
      (|B| + |A| + 2 * C + 1) + (|B| + |A| + 2 * C + 1) * redSize g := by ring
  have hBa := le_abs_self B
  have hAa := neg_abs_le A
  have hBn := abs_nonneg B
  have hAn := abs_nonneg A
  have hτ0 : 0 ≤ τ := by
    have : 0 ≤ (|B| + |A| + 2 * C + 1) * redSize g := mul_nonneg (by positivity) hr
    linarith
  obtain ⟨γ, hγ⟩ : ∃ γ : GL (Fin n) E, logSize (ratGL E n γ * g) < redSize g + 1 :=
    exists_lt_of_ciInf_lt (lt_add_one (redSize g))
  have hinv := ((E1.mahler_holds E n τ).2.1 γ g)
  refine hinv.1 ?_
  set h : GA E n := ratGL E n γ * g with hh
  have hup : ∀ W, deg h W ≤ B + C * (2 + redSize g) := by
    intro W
    have s := hC 1 h W
    rw [one_mul] at s
    have t : C * (1 + logSize h) ≤ C * (2 + redSize g) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    linarith [hB' W]
  refine ⟨fun W => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Module.finrank E W) with h0 | h1
    · rw [deg_finrank_zero h W h0, h0]
      simp [prof]
    · have hk : Module.finrank E W ≤ n := by
        have := Submodule.finrank_le W
        simpa using this
      refine le_trans (hup W) (le_trans ?_ (tau_le_prof hτ0 h1 hk))
      linarith
  · have s := hC h (h⁻¹ : GA E n) ⊤
    rw [mul_inv_cancel, logSize_inv'] at s
    have t : C * (1 + logSize h) ≤ C * (2 + redSize g) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    linarith
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PThetaInt
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapInvolutionEq
open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qh1.map_involution_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (φ : G ≃ₜ* G) (hφ : ∀ x, φ (φ x) = x) :
    μ.map φ = μ := by
  have h1 : φ.trans φ = ContinuousMulEquiv.refl G := by
    ext x
    exact hφ x
  have h2 : mulEquivHaarChar φ * mulEquivHaarChar φ = 1 := by
    rw [← mulEquivHaarChar_trans, h1, mulEquivHaarChar_refl]
  have h3 : mulEquivHaarChar φ = 1 := by
    have h : (mulEquivHaarChar φ) ^ 2 = 1 := by rw [sq, h2]
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h
  have h4 := mulEquivHaarChar_smul_map μ φ
  rwa [h3, one_smul] at h4

theorem UpperTheory.Reformulated.B.Qh1.twist_general.{u_1} :
    ∀ {G : Type u_1} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [inst_5 : MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G)
    [Countable ↥Γ] {F : Set G},
    MeasureTheory.IsFundamentalDomain (↥Γ) F μ →
      ∀ (θ : G →* G),
        Continuous (⇑θ : G → G) →
          (∀ (x : G), (θ : G → G) ((θ : G → G) x) = x) →
            (∀ γ ∈ Γ, (θ : G → G) γ ∈ Γ) →
              ∀ (f : G → ℂ),
                (∀ (γ : ↥Γ) (x : G), f ((↑γ : G) * x) = f x) →
                  MeasureTheory.Integrable f (μ.restrict F) →
                    MeasureTheory.Integrable (fun (x : G) ↦ f ((θ : G → G) x)) (μ.restrict F) ∧
                      ∫ (x : G) in F, f ((θ : G → G) x) ∂μ = ∫ (x : G) in F, f x ∂μ := by
  intro G _ _ _ _ _ _ _ μ _ Γ _ F hF θ hθc hθθ hθΓ f hf hfi
  let φ : G ≃ₜ* G :=
    { toFun := θ
      invFun := θ
      left_inv := hθθ
      right_inv := hθθ
      map_mul' := map_mul θ
      continuous_toFun := hθc
      continuous_invFun := hθc }
  have hmp : MeasureTheory.MeasurePreserving θ μ μ :=
    ⟨hθc.measurable, UpperTheory.Reformulated.B.Qh1.map_involution_eq μ φ hθθ⟩
  have hemb : MeasurableEmbedding (θ : G → G) := φ.toHomeomorph.measurableEmbedding
  let e : Γ → Γ := fun γ => ⟨θ γ, hθΓ γ γ.2⟩
  have he : Function.Involutive e := fun γ => Subtype.ext (hθθ γ)
  have hF' : MeasureTheory.IsFundamentalDomain Γ (θ ⁻¹' F) μ := by
    refine hF.preimage_of_equiv hmp.quasiMeasurePreserving he.bijective ?_
    intro γ x
    change θ (θ γ * x) = γ * θ x
    rw [map_mul, hθθ]
  have hg : ∀ (γ : Γ) (x : G), f (θ (γ • x)) = f (θ x) := by
    intro γ x
    change f (θ (γ * x)) = f (θ x)
    rw [map_mul]
    exact hf (e γ) (θ x)
  refine ⟨?_, ?_⟩
  · have h1 : MeasureTheory.IntegrableOn (fun x => f (θ x)) (θ ⁻¹' F) μ :=
      (hmp.integrableOn_comp_preimage hemb).2 hfi
    exact (hF.integrableOn_iff hF' (f := fun x => f (θ x)) hg).2 h1
  · rw [hF.setIntegral_eq hF' (f := fun x => f (θ x)) hg]
    exact hmp.setIntegral_preimage_emb hemb f F
end

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory

private theorem twist_general {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] {F : Set G}
    (fd : IsFundamentalDomain Γ F μ) (θ : G →* G) (hc : Continuous θ) (hi : ∀ x, θ (θ x) = x)
    (hΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : G → ℂ) (hf : ∀ (γ : Γ) x, f ((γ : G) * x) = f x)
    (hI : Integrable f (μ.restrict F)) :
    Integrable (fun x => f (θ x)) (μ.restrict F) ∧
      ∫ x, f (θ x) ∂(μ.restrict F) = ∫ x, f x ∂(μ.restrict F) :=
  _root_.UpperTheory.Reformulated.B.Qh1.twist_general μ Γ fd θ hc hi hΓ f hf hI

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.thetaInt_pf :
    Basic → ThetaInt := by
  intro _ E _ _ _ n D f hf hI
  have hb := PositivityTheory.Rg.BcB.E1.thetaBasic_holds E
  let θ : PositivityTheory.Rg.BcB.E.H E n 0 →* PositivityTheory.Rg.BcB.E.H E n 0 :=
    (PositivityTheory.Rg.BcB.thetaA E n).prodMap (PositivityTheory.Rg.BcB.thetaA E 0)
  have hc : Continuous θ :=
    ((hb n).1.comp continuous_fst).prodMk ((hb 0).1.comp continuous_snd)
  have hi : ∀ x, θ (θ x) = x := fun x => Prod.ext ((hb n).2.1 x.1) ((hb 0).2.1 x.2)
  have hΓ : ∀ γ ∈ PositivityTheory.Rg.BcB.E.ratH E n 0, θ γ ∈ PositivityTheory.Rg.BcB.E.ratH E n 0 := by
    rintro _ ⟨g, rfl⟩
    exact ⟨(PositivityTheory.Rg.BcB.thetaE E n g.1, PositivityTheory.Rg.BcB.thetaE E 0 g.2),
      Prod.ext ((hb n).2.2 g.1).symm ((hb 0).2.2 g.2).symm⟩
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E 0
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E 0
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E 0
  haveI := (PositivityTheory.Rg.BcB.E1.ratProper_holds E n).2.1
  haveI := (PositivityTheory.Rg.BcB.E1.ratProper_holds E 0).2.1
  letI := PositivityTheory.Rg.BcB.E.borelH E n 0
  haveI : BorelSpace (PositivityTheory.Rg.BcB.E.H E n 0) := ⟨rfl⟩
  haveI : D.μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts :=
        @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ D.μ D.haar.2.2.2
      toIsMulLeftInvariant := D.haar.1
      toIsOpenPosMeasure := D.haar.2.2.1 }
  haveI : Countable (PositivityTheory.Rg.BcB.E.ratH E n 0) :=
    (((GlobalTheory.CuspRep.ratGL E n).prodMap (GlobalTheory.CuspRep.ratGL E 0)).rangeRestrict_surjective).countable
  exact twist_general D.μ _ D.fd θ hc hi hΓ f hf hI
end
