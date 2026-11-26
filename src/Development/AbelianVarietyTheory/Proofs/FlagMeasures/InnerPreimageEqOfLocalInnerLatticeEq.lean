module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdSt
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerPreimageEqOfLocalInnerLatticeEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerPreimageEqOfLocalInnerLatticeEq
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.LsubG

variable {D : D7}

theorem exists_proj (X : Submodule D.host.E (VS D).V) :
    ∃ Q : (VS D).V →ₗ[D.host.E] (VS D).V, (∀ x ∈ X, Q x = 0) ∧ (∀ v, v - Q v ∈ X) ∧ ∀ v, Q (Q v) = Q v := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl X
  have hC' : IsCompl C X := hC.symm
  refine ⟨C.projection X hC', fun x hx => (Submodule.projection_apply_eq_zero_iff hC').2 hx, fun v => ?_, fun v => ?_⟩
  · rw [← Submodule.projection_eq_self_sub_projection hC']
    exact Submodule.projection_apply_mem _ _
  · exact Submodule.projection_apply_of_mem_left hC' (Submodule.projection_apply_mem _ _)

def endP (p : PlF D) (Q : (VS D).V →ₗ[D.host.E] (VS D).V) : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p :=
  Fintype.linearCombination (D.s.atP p).Ep (fun i => baseChange₂ D p (Q ((VS D).frame i)))

theorem bcP_endP (p : PlF D) (Q : (VS D).V →ₗ[D.host.E] (VS D).V) (x : (VS D).V) :
    endP p Q (baseChange₂ D p x) = baseChange₂ D p (Q x) := by
  rw [endP, Fintype.linearCombination_apply]
  conv_rhs => rw [← (VS D).frame.sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, baseChange_smul₂]
  rfl

theorem endP_latP (Z : LocDat D) (p : PlF D) (Q : (VS D).V →ₗ[D.host.E] (VS D).V) (Λ : LV D) {y : Vp D p}
    (hy : y ∈ lattice₂ D Z.M p Λ) : endP p Q y ∈ lattice₂ D Z.M p (Λ.map (Q.restrictScalars (𝓞 D.host.E))) := by
  refine Submodule.span_induction (p := fun y _ => endP p Q y ∈ lattice₂ D Z.M p (Λ.map (Q.restrictScalars (𝓞 D.host.E))))
    ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨x, hx, rfl⟩
    rw [bcP_endP]
    exact Submodule.subset_span ⟨Q x, Submodule.mem_map_of_mem hx, rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    have e : endP p Q (c • a) = c • endP p Q a := by
      rw [Subring.smul_def, Subring.smul_def, map_smul]
    rw [e]; exact Submodule.smul_mem _ c ha

theorem localLattice_mono' (Z : LocDat D) (p : PlF D) {Λ Λ' : LV D} (h : Λ ≤ Λ') : lattice₂ D Z.M p Λ ≤ lattice₂ D Z.M p Λ' :=
  Submodule.span_mono (Set.image_mono h)

theorem mem_of_local (Z : LocDat D) (Γ : LV D) (hΓ : Submodule.IsLattice D.host.E Γ) (x : (VS D).V)
    (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p Γ) : x ∈ Γ := by
  let X := Submodule.span D.host.E (Γ : Set (VS D).V)
  obtain ⟨Q, hQX, hQv, hQQ⟩ := exists_proj X
  let B : LV D := Submodule.span (𝓞 D.host.E) (Set.range (VS D).frame)
  let Λ := Γ ⊔ B.map (Q.restrictScalars (𝓞 D.host.E))
  have hΓΛ : Γ ≤ Λ := le_sup_left
  have hB : B.FG := Submodule.fg_span (Set.finite_range _)
  have hΛ : Submodule.IsLattice D.host.E Λ :=
    Submodule.IsLattice.of_fg D.host.E (hΓ.fg.sup (hB.map _))
  have hspan : Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
    apply top_unique
    rw [← (VS D).frame.span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    change (VS D).frame i ∈ Submodule.span D.host.E (Λ : Set (VS D).V)
    have hdiff := Submodule.span_mono (show (Γ : Set (VS D).V) ⊆ Λ from hΓΛ) (hQv ((VS D).frame i))
    have hi : (VS D).frame i ∈ B := Submodule.subset_span (Set.mem_range_self i)
    have hQi : Q ((VS D).frame i) ∈ Λ :=
      Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := Q.restrictScalars (𝓞 D.host.E)) hi)
    simpa only [sub_add_cancel] using (Submodule.span D.host.E (Λ : Set (VS D).V)).add_mem
      hdiff (Submodule.subset_span hQi)
  have hfull : Submodule.IsFullLattice D.host.E (LatLoc.cL Λ) := by
    refine { toIsLattice := LatLoc.isLattice_map (LatLoc.cE D) Λ hΛ, span_eq_top := ?_ }
    change Submodule.span D.host.E ((LatLoc.cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
    rw [← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]
  have hrec := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices
    (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) hfull).1
  have hx : x ∈ Λ := by
    have hmem := (hrec (LatLoc.cE D x)).2 fun p => by
      rw [← LatLoc.baseChange_eq, ← LatLoc.localLattice_eq]
      exact localLattice_mono' Z p hΓΛ (h p)
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hmem
    exact (show y = x from (LatLoc.cE D).injective hyx) ▸ hy
  have hmap : Γ.map (Q.restrictScalars (𝓞 D.host.E)) = ⊥ := by
    apply (Submodule.eq_bot_iff _).2
    rintro _ ⟨y, hy, rfl⟩
    exact hQX y (Submodule.subset_span hy)
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  let p : PlF D := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField D.host.F)⟩
  have hbc := endP_latP Z p Q Γ (h p)
  rw [hmap, lattice₂, Submodule.bot_coe, Set.image_singleton, map_zero, Submodule.span_zero_singleton,
    Submodule.mem_bot, bcP_endP, ← map_zero (baseChange₂ D p)] at hbc
  have hQx : Q x = 0 := by
    refine (VS D).frame.ext_elem fun i => (D.s.atP p).ιE.injective ?_
    exact congrFun hbc i
  obtain ⟨y, hy, _, ⟨z, _, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hx
  change Q (y + Q z) = 0 at hQx
  rw [map_add, hQX y (Submodule.subset_span hy), hQQ, zero_add] at hQx
  simpa only [LinearMap.restrictScalars_apply, hQx, add_zero] using hy

theorem herm_smul_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (c : E) (u w : V) : H.h u (c • w) = M.L.cj c * H.h u w := by
  rw [H.h_herm (c • w) u, H.h_smul_left, map_mul, ← H.h_herm w u]

theorem herm_span_right {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (u : V) (S : Set V) (hS : ∀ s ∈ S, H.h u s = 0) :
    ∀ w ∈ Submodule.span E S, H.h u w = 0 := by
  intro w hw
  refine Submodule.span_induction (p := fun w _ => H.h u w = 0) hS ?_ ?_ ?_ hw
  · rw [H.h_herm 0 u, H.h_zero_left, map_zero]
  · intro a b _ _ ha hb
    rw [H.h_herm (a + b) u, H.h_add_left, map_add (f := _), ← H.h_herm a u, ← H.h_herm b u, ha, hb, add_zero]
  · intro c a _ ha
    rw [herm_smul_right, ha, mul_zero]

theorem X_iso {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) {x : (VS D).V} (hx : x ∈ Xsp G) :
    x ∈ orth (VS D) (Xsp G) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro y hy
  have hgen : ∀ b, (VS D).hT y (G.fl.e b) = 0 := by
    intro b
    refine Submodule.span_induction (p := fun y _ => (VS D).hT y (G.fl.e b) = 0) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨a, rfl⟩; exact G.fl.e_iso a b
    · simp
    · intro a c _ _ ha hc; simp [ha, hc]
    · intro c a _ ha; simp [ha]
  refine Submodule.span_induction (p := fun x _ => (VS D).hT y x = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨b, rfl⟩; exact hgen b
  · simp
  · intro a c _ _ ha hc; simp [ha, hc]
  · intro c a _ ha; simp [ha]

set_option maxHeartbeats 1000000 in
theorem lsub_le (Z : LocDat D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    (f : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p)
    (hf : ∀ p, f p = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) (Λ₁ Λ₂ : LV D)
    (h₂ : Submodule.IsLattice D.host.E Λ₂)
    (hL : ∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (f p) ⊆ (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (f p)) :
    Lsub Λ₁ G ≤ Lsub Λ₂ G := by
  obtain ⟨Q, hQX, hQv, hQQ⟩ := exists_proj (Xsp G)
  set Γ : LV D := Λ₂ ⊔ Λ₂.map (Q.restrictScalars (𝓞 D.host.E)) with hΓdef
  have hΓ : Submodule.IsLattice D.host.E Γ :=
    Submodule.IsLattice.of_fg D.host.E (h₂.fg.sup (h₂.fg.map _))
  intro v hv
  have hvo : v ∈ orth (VS D) (Xsp G) := hv.2
  obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.1 hv.1
  have hlo : l ∈ orth (VS D) (Xsp G) := hl.2
  have hloc : ∀ p, baseChange₂ D p (Q (l + x)) ∈ lattice₂ D Z.M p Γ := by
    intro p
    have hXQ : ∀ w ∈ (locH Z p).X (f p), endP p Q w = 0 := by
      intro w hw
      refine Submodule.span_induction (p := fun w _ => endP p Q w = 0) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨a, rfl⟩
        rw [hf p]
        simp only
        rw [map_smul, bcP_endP, hQX _ (Submodule.subset_span ⟨a, by simp [frame, FlagG.fvec]⟩), map_zero, smul_zero]
      · exact map_zero _
      · intro a b _ _ ha hb; rw [map_add (f := _), ha, hb, add_zero]
      · intro c a _ ha; rw [map_smul, ha, smul_zero]
    have hperp : baseChange₂ D p l ∈ (locH Z p).perp ((locH Z p).X (f p)) := by
      intro w hw
      refine herm_span_right (locH Z p) (baseChange₂ D p l) _ ?_ w hw
      rintro _ ⟨a, rfl⟩
      rw [hf p]
      simp only
      rw [herm_smul_right]
      have e0 : (locH Z p).h (baseChange₂ D p l) (baseChange₂ D p (frame G a.castSucc)) = 0 := by
        show LocFacts₂ Z.M p (baseChange₂ D p l) (baseChange₂ D p (frame G a.castSucc)) = 0
        rw [baseChangeAt_form Z.M p (Z.hcj p), brS]
        have hmem : frame G a.castSucc ∈ Xsp G := Submodule.subset_span ⟨a, by simp [frame, FlagG.fvec]⟩
        have := hlo
        simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at this
        rw [this _ hmem, map_zero]
      rw [e0, mul_zero]
    obtain ⟨y, hy, hyw⟩ := hL p ⟨⟨baseChange₂ D p l, hperp⟩, Submodule.subset_span ⟨l, hl.1, rfl⟩, rfl⟩
    have hdiff : ((y : Vp D p) - baseChange₂ D p l) ∈ (locH Z p).X (f p) := by
      have := (Submodule.Quotient.eq _).1 hyw
      simpa using this
    have e : endP p Q (baseChange₂ D p l) = endP p Q y := by
      have := hXQ _ hdiff
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    rw [← bcP_endP, map_add (f := _), map_add (f := _), e, bcP_endP p Q x, hQX x hx, map_zero, add_zero]
    exact localLattice_mono' Z p (le_sup_right : Λ₂.map (Q.restrictScalars (𝓞 D.host.E)) ≤ Γ) (endP_latP Z p Q Λ₂ hy)
  have hmem : Q (l + x) ∈ Γ := mem_of_local Z Γ hΓ _ hloc
  obtain ⟨a, ha, b', hb', hab⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 hb'
  have hQab : Q a + Q b = Q (l + x) := by
    have := congrArg Q hab
    simp only [LinearMap.restrictScalars_apply, map_add (f := _), hQQ] at this
    rw [map_add Q l x]
    exact this
  have h2 : Q (l + x - (a + b)) = 0 := by
    rw [map_sub Q, map_add Q a b, hQab, sub_self]
  have hc : l + x - (a + b) ∈ Xsp G := by
    have h1 := hQv (l + x - (a + b))
    rw [h2, sub_zero] at h1
    exact h1
  have hco : a + b ∈ orth (VS D) (Xsp G) := by
    have : a + b = (l + x) - (l + x - (a + b)) := by abel
    rw [this]
    exact Submodule.sub_mem _ hvo (X_iso G hc)
  refine ⟨Submodule.mem_sup.2 ⟨a + b, ⟨Submodule.add_mem _ ha hb, hco⟩, l + x - (a + b), hc, by abel⟩, hvo⟩

theorem lsub_eq_of_local : ∀ (D : D7) (Z : LocDat D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (Fr : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (Fr p).f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → (∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (Fr p).f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (Fr p).f) → Lsub Λ₁ G = Lsub Λ₂ G := by
  intro D Z T G Fr hFr Λ₁ Λ₂ h₁ h₂ hL
  exact le_antisymm
    (lsub_le Z G (fun p => (Fr p).f) hFr Λ₁ Λ₂ h₂ fun p => (hL p).le)
    (lsub_le Z G (fun p => (Fr p).f) hFr Λ₂ Λ₁ h₁ fun p => (hL p).ge)

end GlobalTheory.Unfold.LsubG
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerPreimageEqOfLocalInnerLatticeEqStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.innerPreimage_eq_of_local_innerLattice_eq : ∀ (D : D7) (Z : LocDat D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (Fr : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (Fr p).f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → (∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (Fr p).f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (Fr p).f) → Lsub Λ₁ G = Lsub Λ₂ G := by
  first | exact @GlobalTheory.Unfold.LsubG.lsub_eq_of_local | exact GlobalTheory.Unfold.LsubG.lsub_eq_of_local | (intros; apply GlobalTheory.Unfold.LsubG.lsub_eq_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWeakIntegralOfStronglyContinuous
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_weakIntegral_of_stronglyContinuous {X H : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure X) (R : X → (H →L[ℂ] H)) (hn : ∀ x F, ‖R x F‖ = ‖F‖)
    (hc : ∀ F, Continuous fun x => R x F) (φ : X → ℂ) (hφ : Integrable φ μ) :
    ∃ T : H →L[ℂ] H, ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, φ g * ⟪x, R g y⟫_ℂ ∂μ := by
  have hint : ∀ y : H, Integrable (fun g => φ g • R g y) μ := fun y =>
    (hφ.norm.mul_const ‖y‖).mono' (hφ.aestronglyMeasurable.smul (hc y).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun g => by rw [norm_smul, hn])
  let Tl : H →ₗ[ℂ] H :=
    { toFun := fun y => ∫ g, φ g • R g y ∂μ
      map_add' := fun y z => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (hint y) (hint z)
      map_smul' := fun c y => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        congr 1
        ext g
        rw [smul_comm] }
  refine ⟨Tl.mkContinuous (∫ g, ‖φ g‖ ∂μ) fun y => ?_, fun x y => ?_⟩
  · calc ‖Tl y‖ = ‖∫ g, φ g • R g y ∂μ‖ := rfl
      _ ≤ ∫ g, ‖φ g • R g y‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖φ g‖ * ‖y‖ ∂μ := by
        congr 1
        ext g
        rw [norm_smul, hn]
      _ = (∫ g, ‖φ g‖ ∂μ) * ‖y‖ := integral_mul_const _ _
  · show ⟪x, ∫ g, φ g • R g y ∂μ⟫_ℂ = _
    rw [← integral_inner (hint y)]
    congr 1
    ext g
    rw [inner_smul_right]

theorem AutInst_exists_isRConvF_and_isRConv : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R → (∀ e : I.Gf → ℂ, Integrable e μf → ∃ T, I.IsRConvF μf fund R e T) ∧ ∀ φ : I.GA → ℂ, Integrable φ (I.muA μf) → ∃ T, I.IsRConv μf fund R φ T := by
  intro I μf _ _ fund hfund R hR
  obtain ⟨-, -, hn, hc⟩ := GlobalTheory.T.rightRegularRepresentation_unitary_mul_continuous I μf fund hfund R hR
  haveI := GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints I
  refine ⟨fun e he => ?_, fun φ hφ => ?_⟩
  · obtain ⟨T, hT⟩ := exists_weakIntegral_of_stronglyContinuous μf (fun g => R (1, g))
      (fun g F => hn _ F) (fun F => (hc F).comp (by fun_prop)) e he
    exact ⟨T, he, hT⟩
  · obtain ⟨T, hT⟩ := exists_weakIntegral_of_stronglyContinuous (I.muA μf) R hn hc φ hφ
    exact ⟨T, hφ, hT⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFixingIsometriesEmbedProdLocalUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFixingIsometriesEmbedProdLocalUnitary
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PhiEmbed

theorem baseChange_injective₂ {D : D7} (p : PlF D) : Function.Injective (baseChange₂ D p) := by
  intro x y hxy
  refine (VS D).frame.ext_elem fun i => ?_
  have := congrFun hxy i
  simp only [baseChange₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  exact (D.s.atP p).ιE.injective this

theorem exists_place (D : D7) : Nonempty (PlF D) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩⟩


set_option maxHeartbeats 1000000 in
theorem phi_embed : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∃ φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0), Function.Injective φ ∧ ∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel
  obtain ⟨hext, hUW, -, -⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hRel
  choose e he using fun (g : GV D) (p : PlF D) => (hext g p).exists
  have ext_one : ∀ p, Ext p (1 : GV D) (1 : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) := fun p x => rfl
  have ext_mul : ∀ p (a b : GV D) ga gb, Ext p a ga → Ext p b gb → Ext p (a * b) (ga * gb) := by
    intro p a b ga gb ha hb x
    show ga (gb (baseChange₂ D p x)) = baseChange₂ D p (a (b x))
    rw [hb, ha]
  let φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0) :=
    { toFun := fun h p => ⟨e h p, hUW h h.2 p _ (he h p)⟩
      map_one' := by
        funext p
        apply Subtype.ext
        exact (hext 1 p).unique (he _ p) (ext_one p)
      map_mul' := by
        intro a b
        funext p
        apply Subtype.ext
        exact (hext _ p).unique (he _ p) (ext_mul p _ _ _ _ (he a p) (he b p)) }
  refine ⟨φ, ?_, fun h p => he h p⟩
  intro a b hab
  obtain ⟨p⟩ := exists_place D
  have h1 : e a p = e b p := congrArg Subtype.val (congrFun hab p)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply baseChange_injective₂ p
  rw [← he a p x, ← he b p x, h1]

end GlobalTheory.PhiEmbed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFixingIsometriesEmbedProdLocalUnitaryStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameFixingIsometries_embed_prod_localUnitary : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∃ φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0), Function.Injective φ ∧ ∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) := by
  first | exact @GlobalTheory.PhiEmbed.phi_embed | exact GlobalTheory.PhiEmbed.phi_embed | (intros; apply GlobalTheory.PhiEmbed.phi_embed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableCoeff
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab
open scoped InnerProductSpace Classical

noncomputable section

namespace GlobalTheory.LevelIdem

section Conv

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end Conv

section Alg

variable {Q : Type} [Group Q] [Fintype Q]

end Alg

section Lev

variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)

theorem vol_ne_zero (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] {g : ℕ} (hg : 1 ≤ g) :
    μf (I.Kg g) ≠ ⊤ ∧ ((μf (I.Kg g)).toReal : ℂ) ≠ 0 := by
  obtain ⟨-, -, -, hK, -, -, hKg⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨hopen, ⟨S, hS⟩, -⟩ := hKg g hg
  have hsub : I.Kg g ⊆ I.Kset := fun x hx => hx.1
  have hfin : μf (I.Kg g) ≠ ⊤ := ((measure_mono hsub).trans_lt hK.measure_lt_top).ne
  have h1 : (1 : I.Gf) ∈ I.Kg g := by rw [← hS]; exact S.one_mem
  have hpos : μf (I.Kg g) ≠ 0 := (hopen.measure_pos μf ⟨1, h1⟩).ne'
  exact ⟨hfin, Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hpos hfin).ne'⟩

theorem mem_fibre {s : I.Gf} (hs : s ∈ I.Kset) (x : I.Gf) :
    s⁻¹ * x ∈ I.Kg g ↔ x ∈ I.Kset ∧ ρ.toFun x = ρ.toFun s := by
  have hmul : ∀ a ∈ I.Kset, ∀ b ∈ I.Kset, a * b ∈ I.Kset := fun a ha b hb =>
    (mem_Ksub I _).1 ((Ksub I).mul_mem ((mem_Ksub I a).2 ha) ((mem_Ksub I b).2 hb))
  have hinv : ∀ a ∈ I.Kset, a⁻¹ ∈ I.Kset := fun a ha =>
    (mem_Ksub I _).1 ((Ksub I).inv_mem ((mem_Ksub I a).2 ha))
  constructor
  · intro h
    have hk : s⁻¹ * x ∈ I.Kset := (show s⁻¹ * x ∈ I.Kset ∧ _ from h).1
    have hx : x ∈ I.Kset := by simpa using hmul s hs _ hk
    refine ⟨hx, ?_⟩
    have hm := ρ.map_mul s hs _ hk
    rwa [mul_inv_cancel_left, (ρ.ker _ hk).2 h, mul_one] at hm
  · rintro ⟨hx, hxs⟩
    have hk := hmul _ (hinv s hs) x hx
    refine (ρ.ker _ hk).1 ?_
    rw [ρ.map_mul _ (hinv s hs) x hx, ρ.map_inv hs, hxs, inv_mul_cancel]

theorem integral_lift [Fintype Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (a : MonoidAlgebra ℂ Q)
    (s : Q → I.Gf) (hs : ∀ q, s q ∈ I.Kset ∧ ρ.toFun (s q) = q) (φ : I.Gf → ℂ)
    (hφ : ∀ x, ∀ k ∈ I.Kg g, φ (x * k) = φ x) :
    ∫ x, ρ.lift μf a x * φ x ∂μf = ∑ q, a.coeff q * φ (s q) := by
  classical
  obtain ⟨hfin, hvol⟩ := vol_ne_zero I μf hg
  have hopen := ((GlobalTheory.CongTop.adelic_topology I).2.2.2.2.2.2 g hg).1
  have hSm : ∀ q, MeasurableSet ((fun y => (s q)⁻¹ * y) ⁻¹' I.Kg g) := fun q =>
    (hopen.preimage (continuous_const_mul _)).measurableSet
  have hpt : ∀ x, ρ.lift μf a x * φ x = ∑ q, ((fun y => (s q)⁻¹ * y) ⁻¹' I.Kg g).indicator
      (fun _ => a.coeff q * φ (s q) / ((μf (I.Kg g)).toReal : ℂ)) x := by
    intro x
    by_cases hx : x ∈ I.Kset
    · rw [ρ.lift_of_mem μf a hx, Finset.sum_eq_single (ρ.toFun x)]
      · have hmem : (s (ρ.toFun x))⁻¹ * x ∈ I.Kg g :=
          (mem_fibre ρ (hs _).1 x).2 ⟨hx, (hs _).2.symm⟩
        rw [Set.indicator_of_mem (show x ∈ (fun y => (s (ρ.toFun x))⁻¹ * y) ⁻¹' I.Kg g from hmem)]
        have hφx : φ x = φ (s (ρ.toFun x)) := by
          have h' := hφ (s (ρ.toFun x)) _ hmem
          rwa [mul_inv_cancel_left] at h'
        rw [hφx]
        ring
      · intro q _ hq
        refine Set.indicator_of_notMem (fun hmem => hq ?_) _
        exact ((((mem_fibre ρ (hs q).1 x).1 hmem).2).trans (hs q).2).symm
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [ρ.lift_of_notMem μf a hx, zero_mul]
      refine (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (fun hmem => hx ?_) _).symm
      exact ((mem_fibre ρ (hs q).1 x).1 hmem).1
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hSm q), measureReal_def, measure_preimage_mul, Complex.real_smul]
    field_simp
  · intro q _
    refine (integrable_indicator_iff (hSm q)).2 (integrableOn_const ?_)
    rw [measure_preimage_mul]
    exact hfin

end Lev

end GlobalTheory.LevelIdem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HeightBoundByInfinityNorm
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TauNorm

theorem exists_bound {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] E) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B, ‖L B‖ ≤ c * ∑ i, ∑ j, ‖B i j‖ := by
  classical
  set c : ℝ := ∑ i, ∑ j, ‖L (Matrix.single i j (1 : ℂ))‖ with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨c, hc0, fun B => ?_⟩
  have hB : L B = ∑ i, ∑ j, B i j • L (Matrix.single i j (1 : ℂ)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single B]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, ← map_smul, Matrix.smul_single]
  have hle : ∀ i j, ‖L (Matrix.single i j (1 : ℂ))‖ ≤ c := fun i j =>
    (Finset.single_le_sum (f := fun j => ‖L (Matrix.single i j (1 : ℂ))‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖L (Matrix.single i j (1 : ℂ))‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  rw [hB]
  calc ‖∑ i, ∑ j, B i j • L (Matrix.single i j (1 : ℂ))‖
      ≤ ∑ i, ∑ j, ‖B i j‖ * ‖L (Matrix.single i j (1 : ℂ))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_smul _ _).le))
    _ ≤ ∑ i, ∑ j, ‖B i j‖ * c :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hle i j) (norm_nonneg _)
    _ = c * ∑ i, ∑ j, ‖B i j‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exp_dOp_le {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ B, P * B * Q ≠ 0 → Real.exp (GlobalTheory.Count.dOp (P * B * Q)) ≤ c * ∑ i, ∑ j, ‖B i j‖ := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    { toFun := fun B => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * B * Q))
      map_add' := fun B B' => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun a B => by simp }
  obtain ⟨c, hc, h⟩ := exists_bound L
  refine ⟨c, hc, fun B hB => ?_⟩
  have hpos : 0 < ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * B * Q))‖ := by
    rw [norm_pos_iff]
    intro h0
    apply hB
    have h1 : Matrix.toEuclideanLin (P * B * Q) = 0 :=
      LinearMap.toContinuousLinearMap.injective (h0.trans (map_zero _).symm)
    exact Matrix.toEuclideanLin.injective (h1.trans (map_zero _).symm)
  unfold GlobalTheory.Count.dOp
  rw [Real.exp_log hpos]
  exact h B

theorem exp_mean_le {ι : Type} [Fintype ι] [Nonempty ι] (d : ι → ℝ) (K : ℝ) (h : ∀ v, Real.exp (d v) ≤ K) :
    Real.exp ((∑ v, d v) / Fintype.card ι) ≤ K := by
  obtain ⟨v₀, hv₀⟩ := Finite.exists_max d
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hmean : (∑ v, d v) / Fintype.card ι ≤ d v₀ := by
    rw [div_le_iff₀ hcard]
    calc ∑ v, d v ≤ ∑ _v : ι, d v₀ := Finset.sum_le_sum fun v _ => hv₀ v
      _ = d v₀ * Fintype.card ι := by simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact (Real.exp_le_exp.2 hmean).trans (h v₀)

theorem card_places (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  have := I.cm.totReal
  have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := I.F)
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at h1 h2
  simp only [AutInst.f]
  omega

theorem inv_tau_mul_le (I : AutInst) (hn : 1 ≤ I.n) (x g : I.GA) (hg : g.2 = 1) (K : ℝ)
    (h : ∀ v, Real.exp (GlobalTheory.Count.dOp (uMat (g.1 v))) ≤ K) :
    (GlobalTheory.Count.tau1 I (x * g))⁻¹ ≤ (GlobalTheory.Count.tau1 I x)⁻¹ * K := by
  have hK1 : g.2 ∈ I.Kset := by
    rw [hg]
    show ((1 : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
    simp only [OneMemClass.coe_one]
    exact one_mem _
  have hlog := GlobalTheory.TauLipschitz.log_trunc_le I hn x g hK1
  have hx := GlobalTheory.TauLipschitz.trunc_pos I hn x
  have hxg := GlobalTheory.TauLipschitz.trunc_pos I hn (x * g)
  have hmean : Real.exp (GlobalTheory.Dec.dSum I g.1 / I.f) ≤ K := by
    have := exp_mean_le (fun v => GlobalTheory.Count.dOp (uMat (g.1 v))) K h
    rw [card_places] at this
    simpa only [GlobalTheory.Dec.dSum] using this
  have hdiv : GlobalTheory.Count.tau1 I x / GlobalTheory.Count.tau1 I (x * g) ≤ K := by
    rw [← Real.exp_log (div_pos hx hxg), Real.log_div hx.ne' hxg.ne']
    exact (Real.exp_le_exp.2 (by linarith)).trans hmean
  rw [inv_mul_eq_div, le_div_iff₀ hx, inv_mul_eq_div]
  exact hdiv

theorem sum_le_normInf {D : D7} {V : HSp D}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (g : GA D V) (τ : D.what₂.Tau) :
    ∑ i, ∑ j, ‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g i j‖ ≤ normInf θ V g := by
  unfold Formalism.L2.Theta.normInf
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun τ => ∑ i, ∑ j, (‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖))
    (fun _ _ => by positivity) (Finset.mem_univ τ))
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
    le_add_of_nonneg_right (norm_nonneg _)

theorem uMat_ne_zero (I : AutInst) (hn : 1 ≤ I.n) (g : I.GA) (v : InfinitePlace I.F) : uMat (g.1 v) ≠ 0 := by
  have : Nonempty (Fin I.n) := ⟨⟨0, hn⟩⟩
  exact Units.ne_zero _

end GlobalTheory.TauNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreFamilyUnique
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.LocalFibreUnique

theorem fibre_family_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ a : ℕ, ∀ (μ : Measure (Fin a → Fin n → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ a)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ fib : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib → ∀ fib' : HermR (Fv F v) σ a → Measure (Fin a → Fin n → Fv F v ⊗[F] E), IsFibreFamily μ (gramR (Fv F v) σ J) Subtype.val {X | LinearIndependent (Fv F v ⊗[F] E) X} ν Set.univ fib' → fib = fib' := by
  intro F E _ _ _ _ _ σ hE n J hJ v a μ ν hμ hν fib h1 fib' h2
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabS.sigma_invol σ hE.2.2.2
  have := PI.VolStabS.secondCountable_Fv F v
  have := PI.VolStabS.locallyCompact_Fv F v
  exact PI.VolStabS.FibUniq.fib_eq_tens σ hσ J hJ.1 a (Fv F v) (PI.VolStabS.isOpen_units_Fv F v)
    (PI.VolStabS.TensAllW.lip_field _) μ ν fib fib' h1 h2

end GlobalTheory.LocalFibreUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianRapidDecay
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GaussDecay

theorem isCMFam_of_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) : GlobalTheory.Mem.Vol.IsCMFam φ := by
  obtain ⟨hF, hE, h2, -⟩ := h
  unfold GlobalTheory.Mem.Vol.IsCMFam
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · have key : ∀ v, (InfinitePlace.mk (φ v)).comap (algebraMap F E) = v := by
      intro v
      rw [InfinitePlace.comap_mk, show (φ v).comp (algebraMap F E) = v.embedding from RingHom.ext (hφ v),
        InfinitePlace.mk_embedding]
    intro v w hvw
    rw [← key v, ← key w]
    exact congrArg (fun x : InfinitePlace E => x.comap (algebraMap F E)) hvw
  · have a1 := IsTotallyComplex.finrank E
    have a2 := IsTotallyReal.finrank F
    have a3 := Module.finrank_mul_finrank ℚ F E
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
      IsTotallyComplex.nrRealPlaces_eq_zero E]
    rw [h2] at a3
    omega

end GlobalTheory.GaussDecay
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeBoundedBelowUnipotentRa
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeBoundedBelowUnipotentRa
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem one_le_rank_of_isIsot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) :
    1 ≤ I.n := by
  by_contra h
  have h0 : I.n = 0 := by omega
  haveI : IsEmpty (Fin I.n) := by rw [h0]; infer_instance
  exact hW.1 (Subsingleton.elim _ _)

theorem exists_pos_le_tau1_mul_of_mem_NA_of_isIsot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (x : I.GA)
    (hW : I.IsIsot W) : ∃ c : ℝ, 0 < c ∧ ∀ m ∈ I.NA W, c ≤ tau1 I (m * x) := by
  obtain ⟨hpos, hcont, hinv, -⟩ := GlobalTheory.T.truncatedLeastLatticeSize_lipschitz_properties I (one_le_rank_of_isIsot I W hW)
  obtain ⟨-, -, -, -, Cp, hCp, -, hcov⟩ := GlobalTheory.UnipApprox.strong_approximation I W hW
  have hc : Continuous fun y : I.GA => tau1 I (y * x) := hcont.comp (continuous_id.mul continuous_const)
  have key : ∀ m ∈ I.NA W, ∃ y ∈ Cp, tau1 I (m * x) = tau1 I (y * x) := by
    intro m hm
    obtain ⟨γ, hγ, hy⟩ := hcov m hm
    refine ⟨γ⁻¹ * m, hy, ?_⟩
    rw [← hinv γ hγ.1 (γ⁻¹ * m * x)]
    congr 1
    group
  rcases Cp.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun m hm => ?_⟩
    obtain ⟨y, hy, -⟩ := key m hm
    rw [he] at hy
    exact hy.elim
  · obtain ⟨y₀, -, hmin⟩ := hCp.exists_isMinOn hne hc.continuousOn
    refine ⟨tau1 I (y₀ * x), hpos _, fun m hm => ?_⟩
    obtain ⟨y, hy, e⟩ := key m hm
    rw [e]
    exact hmin hy

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeBoundedBelowUnipotentRaStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncatedLeastLatticeSize_bounded_below_unipotentRadical : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (x : I.GA), I.IsIsot W → ∃ c : ℝ, 0 < c ∧ ∀ m ∈ I.NA W, c ≤ tau1 I (m * x) := by
  first | exact @GlobalTheory.Dec.exists_pos_le_tau1_mul_of_mem_NA_of_isIsot | exact GlobalTheory.Dec.exists_pos_le_tau1_mul_of_mem_NA_of_isIsot | (intros; apply GlobalTheory.Dec.exists_pos_le_tau1_mul_of_mem_NA_of_isIsot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColsSharpDictionary
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.St

section Abstract

open Formalism.L2.SG.ColsDim

theorem cols_sharp_abstract {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (ιi : Γ →* Gi) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (ψ : K →* ℂˣ) (π : Representation ℂ Gi V)
    (hπ : ∀ h : Gi, ∀ v w : V, ⟪π h v, π h w⟫_ℂ = ⟪v, w⟫_ℂ)
    (hψ : ∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1)
    (sh : (V →ₗ[ℂ] (Gi × Gf → ℂ)) → Gf → V)
    (hsh : ∀ (T : V →ₗ[ℂ] (Gi × Gf → ℂ)) (x : Gf) (ξ : V), ⟪sh T x, ξ⟫_ℂ = T ξ (1, x)) :
    (∀ (T : Cols ℂ ιi ιf K ψ π) (γ : Γ) (x : Gf) (κ : K),
      sh T.1 (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (sh T.1 x)) ∧
    (∀ T : Cols ℂ ιi ιf K ψ π, (∀ x, sh T.1 x = 0) → T = 0) ∧
    ∀ φ : Gf → V, (∀ (γ : Γ) (x : Gf) (κ : K),
      φ (ιf γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ιi γ) (φ x)) →
      ∃ T : Cols ℂ ιi ιf K ψ π, ∀ x, sh T.1 x = φ x := by
  obtain ⟨e, he, hsm⟩ := sharp_bijective Γ Gi Gf V ιi ιf K ψ π hπ hψ
  have key : ∀ (T : Cols ℂ ιi ιf K ψ π) (x : Gf), sh T.1 x = (e T).1 x := fun T x =>
    ext_inner_right ℂ fun ξ => by
      rw [hsh]
      exact he T x ξ
  refine ⟨?_, ?_, ?_⟩
  · intro T γ x κ
    rw [key, key]
    exact (e T).2 γ x κ
  · intro T hT
    have h0 : e T = e ((0 : ℂ) • T) := by
      apply Subtype.ext
      rw [hsm]
      funext x
      rw [← key, hT x]
      simp
    have := e.injective h0
    rw [this]
    simp
  · intro φ hφ
    refine ⟨e.symm ⟨φ, hφ⟩, fun x => ?_⟩
    rw [key, Equiv.apply_symm_apply]

end Abstract

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cols_sharp_dictionary :
    ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter), (∀ κ : Ku X u hK, ‖((psiK X u hK κ : ℂˣ) : ℂ)‖ = 1) ∧ (∀ (h : Hinf X u) (v w : X.Vpi u), ⟪piRep X u h v, piRep X u h w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ (T : Cu X u hK) (γ : Gam X u) (x : Hfin X u) (κ : Ku X u hK), shP X u T.1 (iotaF X u γ * x * κ) = (((psiK X u hK κ)⁻¹ : ℂˣ) : ℂ) • piRep X u (iotaI X u γ) (shP X u T.1 x)) ∧ (∀ T : Cu X u hK, (∀ x, shP X u T.1 x = 0) → T = 0) ∧ ∀ φ : Hfin X u → X.Vpi u, (∀ (γ : Gam X u) (x : Hfin X u) (κ : Ku X u hK), φ (iotaF X u γ * x * κ) = (((psiK X u hK κ)⁻¹ : ℂˣ) : ℂ) • piRep X u (iotaI X u γ) (φ x)) → ∃ T : Cu X u hK, ∀ x, shP X u T.1 x = φ x := by
  intro D X u hK
  have hψ : ∀ κ : Ku X u hK, ‖((psiK X u hK κ : ℂˣ) : ℂ)‖ = 1 := fun κ => hK.2.2.2.2 _ κ.2
  have hπ : ∀ (h : Hinf X u) (v w : X.Vpi u), ⟪piRep X u h v, piRep X u h w⟫_ℂ = ⟪v, w⟫_ℂ :=
    fun h v w => (X.piU_rep u).2.2.1 _ (hinf_le_sinf X u _ h.2) v w
  exact ⟨hψ, hπ, cols_sharp_abstract (iotaI X u) (iotaF X u) (Ku X u hK) (psiK X u hK) (piRep X u) hπ hψ
    (shP X u) (inner_shP X u)⟩

end GlobalTheory.St

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFixingIsometryExtPreservesCompletionsAe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFixingIsometryExtPreservesCompletionsAe
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold

theorem gmap_isLattice_rat {D : D7} (g : GV D) (Λ : LV D) (hΛ : Submodule.IsLattice D.host.E Λ) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g Λ) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  exact Submodule.IsLattice.of_fg D.host.E (hΛ.fg.map _)

theorem gmap_isFullLattice_rat {D : D7} (g : GV D) (Λ : LV D)
    (hΛ : Submodule.IsFullLattice D.host.E Λ) :
    Submodule.IsFullLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g Λ) := by
  refine { toIsLattice := gmap_isLattice_rat g Λ hΛ.toIsLattice, span_eq_top := ?_ }
  change Submodule.span D.host.E (g.toLinearMap '' (Λ : Set (VS D).V)) = ⊤
  rw [Submodule.span_image, hΛ.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem ext_fix_lattice_ae : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∀ h : ↥(FlagPairStabilizer F F'), {p | ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀ h
  obtain ⟨-, -, hlat, -⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR
  have hfin := ((GlobalTheory.T.hermitianLattice_local_global_principle D Z).1 (Formalism.HermitianLatticesTheory.gmap (h : GV D) Λ₀) Λ₀ (gmap_isFullLattice_rat _ _ hΛ₀) hΛ₀).1
  refine hfin.subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  intro heq
  apply hp
  apply Subgroup.subset_closure
  show LocNG.img _ _ = _
  rw [← hlat (h : GV D) p _ Λ₀ (hφ h p)]
  exact heq

end GlobalTheory.Unfold
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFixingIsometryExtPreservesCompletionsAeStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameFixingIsometry_ext_preserves_completions_ae : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∀ h : ↥(FlagPairStabilizer F F'), {p | ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  first | exact @GlobalTheory.Unfold.ext_fix_lattice_ae | exact GlobalTheory.Unfold.ext_fix_lattice_ae | (intros; apply GlobalTheory.Unfold.ext_fix_lattice_ae <;> first | assumption | exact (show Submodule.IsFullLattice _ _ from by assumption).toIsLattice)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelHyperbolicBasisScaled
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelHyperbolicBasisScaled
noncomputable section
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm.FramePf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ka_div (D : D7) : D.host.ka / (2 * Real.pi) = (2 * D.host.v)⁻¹ := by
  have h0 : 0 < D.host.rdE := GlobalTheory.TypeAsm.GramPf.rdE_pos' D
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [Formalism.BasicNotions.Host.ka, Formalism.BasicNotions.Host.v]
  field_simp

theorem two_v_pos (D : D7) : 0 < 2 * D.host.v := by
  have h0 : 0 < D.host.rdE := GlobalTheory.TypeAsm.GramPf.rdE_pos' D
  simp only [Formalism.BasicNotions.Host.v]
  linarith

theorem phiV_frame (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau) (a : Fin D.R.rS) :
    GlobalTheory.TypeAsm.phiV C τ (X.eX a) =
                 (((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) ∧
    GlobalTheory.TypeAsm.phiV C τ (X.fY a) =
                 ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  obtain ⟨hQiQ, _, _, hfr⟩ := C.isT τ
  obtain ⟨h1, h2⟩ := hfr a a rfl
  have hc : ((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) ≠ 0 := pow_ne_zero _ (two_v_pos D).ne'
  have hfp : frS D ^ (D.R.rS - a.val) = ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) := by
    unfold frS
    rw [ka_div, ← Complex.ofReal_pow, inv_pow]
  unfold GlobalTheory.TypeAsm.phiV
  constructor
  · have e : rv X.B.I (vOf X τ) (X.crd (X.eX a)) =
        ((((2 * D.host.v) ^ (D.R.rS - a.val)) : ℝ) : ℂ) • (C.Q τ *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1) := by
      rw [h1, hfp, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc, Complex.ofReal_one, one_smul]
      rfl
    rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
    rfl
  · have e : rv X.B.I (vOf X τ) (X.crd (X.fY a)) =
        ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • (C.Q τ *ᵥ Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) 1) := by
      rw [h2, hfp, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_inv, inv_inv, smul_smul,
        ← Complex.ofReal_mul, inv_mul_cancel₀ hc, Complex.ofReal_one, one_smul]
      rfl
    rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
    rfl

end GlobalTheory.TypeAsm.FramePf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelHyperbolicBasisScaledStatement
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModel_hyperbolicBasis_scaled : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau) (a : Fin D.R.rS),
    GlobalTheory.TypeAsm.phiV C τ (X.eX a) =
                 (((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) ∧
    GlobalTheory.TypeAsm.phiV C τ (X.fY a) =
                 ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  first | exact @GlobalTheory.TypeAsm.FramePf.phiV_frame | exact GlobalTheory.TypeAsm.FramePf.phiV_frame | (intros; apply GlobalTheory.TypeAsm.FramePf.phiV_frame <;> assumption)
end
end
