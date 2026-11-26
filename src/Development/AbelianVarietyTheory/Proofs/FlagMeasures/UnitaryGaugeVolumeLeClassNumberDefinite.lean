module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeGaussianSumOfLengthEqTsumStabilizerCosets
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeVolumeEqOfSemilinearIsometryGenus

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGaugeVolumeLeClassNumberDefinite
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGaugeVolumeLeClassNumberDefinite
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.DefiniteVolume

variable (I : AutInst)

theorem eps_eq {r : ℕ} (h : HasSig I r 0) (v : InfinitePlace I.F) : I.ε v = allPos I.n := by
  funext a
  have h0 := (h v).2
  unfold AutInst.qAt at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  have ha := h0 (Finset.mem_univ a)
  simp only [allPos]
  revert ha
  cases I.ε v a <;> simp

theorem rank_eq {r : ℕ} (h : HasSig I r 0) : r = I.n := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace I.F) := inferInstance
  have hp := (h v).1
  rw [AutInst.pAt, eps_eq I h v] at hp
  simpa [allPos] using hp.symm

theorem card_places : Fintype.card (InfinitePlace I.F) = I.f := by
  haveI := I.cm.totReal
  have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero] at h2
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, AutInst.f]
  omega

theorem pos_at (v : InfinitePlace I.F) (hv : I.ε v = allPos I.n) (y : Fin I.n → I.E) (hy : y ≠ 0) :
    0 < (I.φ v (star y ⬝ᵥ (I.J *ᵥ y))).re := by
  have hconj : ∀ a, I.φ v (star a) = starRingEnd ℂ (I.φ v a) := fun a => I.cm.cmUnram.2.1 (I.φ v) a
  have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hspec : (I.P v)ᴴ * I.J.map (I.φ v) * I.P v = 1 := by
    rw [I.P_spec v, hv, GlobalTheory.UnitaryVolume.Jm_allPos]
  have hmap : I.φ v (star y ⬝ᵥ (I.J *ᵥ y)) =
      star (fun i => I.φ v (y i)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ fun i => I.φ v (y i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, hconj, Matrix.map_apply,
      starRingEnd_apply]
  have hne : (fun i => I.φ v (y i)) ≠ 0 := by
    intro h0
    apply hy
    funext i
    exact (I.φ v).injective (by simpa using congrFun h0 i)
  rw [hmap]
  generalize (fun i => I.φ v (y i)) = w at hne ⊢
  have hwz : w = I.P v *ᵥ ((I.P v)⁻¹ *ᵥ w) := by
    rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, one_mulVec]
  have hz0 : (I.P v)⁻¹ *ᵥ w ≠ 0 := by
    intro h0
    apply hne
    rw [hwz, h0, mulVec_zero]
  rw [hwz, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hspec, one_mulVec]
  exact (Complex.pos_iff.1 (Matrix.dotProduct_star_self_pos_iff.2 hz0)).1

theorem pos_all {r : ℕ} (h : HasSig I r 0) (φ : I.E →+* ℂ) (y : Fin I.n → I.E) (hy : y ≠ 0) :
    0 < (φ (star y ⬝ᵥ (I.J *ᵥ y))).re := by
  have hJ : I.Jᴴ = I.J := by rw [← GlobalTheory.StabCosets.cT_star]; exact I.J_herm
  have hstar : star (star y ⬝ᵥ (I.J *ᵥ y)) = star y ⬝ᵥ (I.J *ᵥ y) := by
    rw [← star_dotProduct_star, star_star, star_mulVec, ← dotProduct_mulVec, hJ]
  obtain ⟨b, hb⟩ := (I.cm.fixed _).1 hstar
  haveI := I.cm.totReal
  have hreal : (InfinitePlace.mk (φ.comp (algebraMap I.F I.E))).IsReal :=
    NumberField.IsTotallyReal.isReal _
  have hemb := NumberField.InfinitePlace.embedding_mk_eq_of_isReal
    (NumberField.InfinitePlace.isReal_mk_iff.1 hreal)
  have hval : φ (star y ⬝ᵥ (I.J *ᵥ y)) =
      I.φ (InfinitePlace.mk (φ.comp (algebraMap I.F I.E))) (star y ⬝ᵥ (I.J *ᵥ y)) := by
    rw [← hb, I.φ_over, hemb]
    rfl
  rw [hval]
  exact pos_at I _ (eps_eq I h _) y hy

theorem hform_eq (z x : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J z x = star z ⬝ᵥ (I.J *ᵥ x) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, starRingEnd_apply, Pi.star_apply,
    mul_assoc]

abbrev DefLat (E : Type) [Field E] [NumberField E] [StarRing E] (r : ℕ) : Type :=
  {X : Matrix (Fin r) (Fin r) E × Submodule (𝓞 E) (Fin r → E) //
      X.1ᴴ = X.1 ∧ (∀ (φ : E →+* ℂ) (y : Fin r → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (X.1 *ᵥ y))).re) ∧
      Submodule.IsLattice E X.2 ∧
      ∀ x, x ∈ X.2 ↔ ∀ y ∈ X.2, star y ⬝ᵥ (X.1 *ᵥ x) ∈ (algebraMap (𝓞 E) E).range}

abbrev Isom (E : Type) [Field E] [NumberField E] [StarRing E] (r : ℕ) (X Y : DefLat E r) : Prop :=
  ∃ γ : GL (Fin r) E, (γ : Matrix (Fin r) (Fin r) E)ᴴ * Y.1.1 * (γ : Matrix (Fin r) (Fin r) E) = X.1.1 ∧
      ∀ y, (γ : Matrix (Fin r) (Fin r) E) *ᵥ y ∈ Y.1.2 ↔ y ∈ X.1.2

theorem isom_equivalence (E : Type) [Field E] [NumberField E] [StarRing E] (r : ℕ) :
    Equivalence (Isom E r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X
    exact ⟨1, by simp, fun y => by simp⟩
  · rintro X Y ⟨γ, h1, h2⟩
    refine ⟨γ⁻¹, ?_, fun y => ?_⟩
    · have hu : (γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1 := by
        simp
      calc ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)ᴴ * X.1.1 *
            ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)
          = ((γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E))ᴴ * Y.1.1 *
              ((γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E)) := by
            rw [← h1, conjTranspose_mul]
            simp only [Matrix.mul_assoc]
        _ = Y.1.1 := by rw [hu]; simp
    · have h3 := h2 (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y)
      rw [mulVec_mulVec, Units.mul_inv, one_mulVec] at h3
      exact h3.symm
  · rintro X Y Z ⟨γ, h1, h2⟩ ⟨δ, h3, h4⟩
    refine ⟨δ * γ, ?_, fun y => ?_⟩
    · rw [Units.val_mul, conjTranspose_mul, ← h1, ← h3]
      simp only [Matrix.mul_assoc]
    · rw [Units.val_mul, ← mulVec_mulVec, h4, h2]

def latOf {r : ℕ} (h : HasSig I r 0) (x : I.GA) : DefLat I.E I.n :=
  ⟨(I.J, lamX I x), by rw [← GlobalTheory.StabCosets.cT_star]; exact I.J_herm, pos_all I h,
    Submodule.IsLattice.of_fg I.E (GlobalTheory.PointLattice.lamX_selfDual I x).2.1,
    fun y => by
      simpa only [hform_eq] using (GlobalTheory.PointLattice.lamX_selfDual I x).2.2.2.1 y⟩

theorem coset_of_isom {r : ℕ} (h : HasSig I r 0) (x y : I.GA)
    (e : Isom I.E I.n (latOf I h y) (latOf I h x)) :
    ∃ a ∈ I.GFset, x.2⁻¹ * (a * y).2 ∈ I.Kset := by
  obtain ⟨γ, h1, h2⟩ := e
  change (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * γ = I.J at h1
  change ∀ z, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z ∈ lamX I x ↔ z ∈ lamX I y at h2
  have hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := by
    show Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γ = I.J
    rw [GlobalTheory.StabCosets.cT_star]
    exact h1
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.StabCosets.exists_isImage I γ hγ
  refine ⟨a, ⟨γ, hγ, ha1, ha2⟩, ?_⟩
  have hl : lamX I (a * y) = lamX I x := by
    rw [(GlobalTheory.PointEquivariance.equivariance I y γ a hγ ha1 ha2).1]
    ext z
    simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.toLin'_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (h2 u).2 hu
    · intro hz
      refine ⟨((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z, (h2 _).1 ?_, ?_⟩
      · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
        exact hz
      · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  exact (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I x (x⁻¹ * (a * y))).2 (by rw [mul_inv_cancel_left]; exact hl)

theorem covol_le {r : ℕ} (h : HasSig I r 0) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
    [Fintype (Quot (Isom I.E I.n))] :
    covol I.GFset (I.muA μf) Set.univ ≤
      (∏ v, Formalism.REAL.muG (I.ε v) Set.univ) * (Fintype.card (Quot (Isom I.E I.n)) * μf I.Kset) := by
  classical
  let pt : Quot (Isom I.E I.n) → I.GA := fun q =>
    if hq : ∃ x, Quot.mk (Isom I.E I.n) (latOf I h x) = q then hq.choose else 1
  let D : Quot (Isom I.E I.n) → Set I.GA := fun q =>
    Set.univ ×ˢ ((fun g => (pt q).2⁻¹ * g) ⁻¹' I.Kset)
  have hKo : IsOpen I.Kset := (GlobalTheory.adelicStab_isCompact_isOpen I).2.1
  have hDm : ∀ q, MeasurableSet (D q) := fun q =>
    MeasurableSet.univ.prod (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hcover : ∀ z ∈ (Set.univ : Set I.GA), ∃ γ ∈ I.GFset, γ * z ∈ ⋃ q, D q := by
    intro z _
    have hq : ∃ x, Quot.mk (Isom I.E I.n) (latOf I h x) = Quot.mk (Isom I.E I.n) (latOf I h z) :=
      ⟨z, rfl⟩
    have hpt : pt (Quot.mk (Isom I.E I.n) (latOf I h z)) = hq.choose := dif_pos hq
    have e : Isom I.E I.n (latOf I h z) (latOf I h hq.choose) :=
      (isom_equivalence I.E I.n).symm
        ((Equivalence.eqvGen_iff (isom_equivalence I.E I.n)).1 (Quot.eqvGen_exact hq.choose_spec))
    obtain ⟨a, ha, hk⟩ := coset_of_isom I h hq.choose z e
    refine ⟨a, ha, Set.mem_iUnion.2 ⟨Quot.mk (Isom I.E I.n) (latOf I h z), Set.mem_univ _, ?_⟩⟩
    show (pt (Quot.mk (Isom I.E I.n) (latOf I h z))).2⁻¹ * (a * z).2 ∈ I.Kset
    rw [hpt]
    exact hk
  calc covol I.GFset (I.muA μf) Set.univ ≤ I.muA μf (⋃ q, D q) := by
        unfold covol
        exact iInf_le_of_le _ (iInf_le_of_le (MeasurableSet.iUnion hDm) (iInf_le_of_le hcover le_rfl))
    _ ≤ ∑ q, I.muA μf (D q) := measure_iUnion_fintype_le _ _
    _ = ∑ _q : Quot (Isom I.E I.n), (∏ v, Formalism.REAL.muG (I.ε v) Set.univ) * μf I.Kset := by
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [D, AutInst.muA]
        rw [Measure.prod_prod, Measure.pi_univ, measure_preimage_mul]
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

theorem volU_pos (i : ℕ) : 0 < volU i := by
  unfold volU sphV
  exact mul_pos (Finset.prod_pos fun l _ => by positivity) (by positivity)

theorem gauge_local (N : ℕ) (ε : Fin N → Bool) (hε : ε = allPos N) (c : ℝ) (hc : IsGauge ε c) :
    0 ≤ c ∧ ENNReal.ofReal c * Formalism.REAL.muG ε Set.univ = ENNReal.ofReal (volU N) := by
  subst hε
  have h1 := GlobalTheory.T.riemannianHaarGauge_volume_unitaryGroup_eq N c hc
  have hlt := GlobalTheory.UnitaryVolume.muG_univ_lt_top N
  have hne := GlobalTheory.UnitaryVolume.muG_univ_ne_zero N
  have ht : 0 < (Formalism.REAL.muG (allPos N) Set.univ).toReal := ENNReal.toReal_pos hne hlt.ne
  have hc0 : 0 < c := by
    by_contra hle
    push_neg at hle
    nlinarith [volU_pos N]
  refine ⟨hc0.le, ?_⟩
  rw [← ENNReal.ofReal_toReal hlt.ne, ← ENNReal.ofReal_mul hc0.le, h1]

theorem gaugeVol_le : ∀ (I : AutInst) (r : ℕ), HasSig I r 0 → ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure], IsGaugeAll I c → gaugeVol I c μf ≤ ENNReal.ofReal (volU r ^ I.f) * ((defClassNum I.E r : ENat) : ENNReal) := by
  intro I r h c μf _ _ hc
  obtain rfl := rank_eq I h
  have hK := GlobalTheory.adelicStab_isCompact_isOpen I
  have h1K : (1 : I.Gf) ∈ I.Kset :=
    (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I 1 1).2 (by rw [mul_one])
  have hKpos : μf I.Kset ≠ 0 := (hK.2.1.measure_pos μf ⟨1, h1K⟩).ne'
  have hKtop : μf I.Kset ≠ ⊤ := hK.1.measure_lt_top.ne
  have hloc : ∀ v, 0 ≤ c v ∧
      ENNReal.ofReal (c v) * Formalism.REAL.muG (I.ε v) Set.univ = ENNReal.ofReal (volU I.n) :=
    fun v => gauge_local I.n (I.ε v) (eps_eq I h v) (c v) (hc v)
  have hV : ENNReal.ofReal (volU I.n ^ I.f) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (pow_pos (volU_pos _) _)).ne'
  have hprod : ENNReal.ofReal (∏ v, c v) * ∏ v, Formalism.REAL.muG (I.ε v) Set.univ =
      ENNReal.ofReal (volU I.n ^ I.f) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun v _ => (hloc v).1), ← Finset.prod_mul_distrib,
      Finset.prod_congr rfl (fun v _ => (hloc v).2), Finset.prod_const, Finset.card_univ, card_places,
      ENNReal.ofReal_pow (volU_pos _).le]
  by_cases hfin : Finite (Quot (Isom I.E I.n))
  · haveI := Fintype.ofFinite (Quot (Isom I.E I.n))
    have hcv := covol_le I h μf
    unfold gaugeVol
    calc ENNReal.ofReal (∏ v, c v) * covol I.GFset (I.muA μf) Set.univ / μf I.Kset
        ≤ ENNReal.ofReal (∏ v, c v) * ((∏ v, Formalism.REAL.muG (I.ε v) Set.univ) *
            ((Fintype.card (Quot (Isom I.E I.n)) : ENNReal) * μf I.Kset)) / μf I.Kset := by
          gcongr
      _ = ENNReal.ofReal (volU I.n ^ I.f) * (Fintype.card (Quot (Isom I.E I.n)) : ENNReal) := by
          rw [← mul_assoc, hprod, ← mul_assoc, ENNReal.mul_div_cancel_right hKpos hKtop]
      _ = ENNReal.ofReal (volU I.n ^ I.f) * ((defClassNum I.E I.n : ENat) : ENNReal) := by
          rw [defClassNum, ENat.card_eq_coe_fintype_card, ENat.toENNReal_coe]
  · haveI := not_finite_iff_infinite.1 hfin
    rw [defClassNum, ENat.card_eq_top_of_infinite, ENat.toENNReal_top, ENNReal.mul_top hV]
    exact le_top

end GlobalTheory.DefiniteVolume
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGaugeVolumeLeClassNumberDefiniteStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGaugeVolume_le_classNumber_definite : ∀ (I : AutInst) (r : ℕ), HasSig I r 0 → ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure], IsGaugeAll I c → gaugeVol I c μf ≤ ENNReal.ofReal (volU r ^ I.f) * ((defClassNum I.E r : ENat) : ENNReal) := by
  first | exact @GlobalTheory.DefiniteVolume.gaugeVol_le | exact GlobalTheory.DefiniteVolume.gaugeVol_le | (intros; apply GlobalTheory.DefiniteVolume.gaugeVol_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMassEqSumOverRationalGroupOrbits
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMassEqSumOverRationalGroupOrbits
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Unfold.massA_eq_sum_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → Function.Injective φ → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → ∀ d : Dat Z FP, massA F F' d = ∑' o : Quot (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y'), if (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite then (({h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • o.out p) = o.out}.encard : ℝ≥0∞))⁻¹ else 0 := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ _hinj _inst hmov d

  have huniq := (GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR).1

  have key : ∀ (h : ↥(FlagPairStabilizer F F')) (y y' : Dat Z FP),
      RMoves h.1 y y' ↔ (fun p => φ h p • y p) = y' := by
    intro h y y'
    constructor
    · intro hm
      funext p
      obtain ⟨g', hg', hmv⟩ := hm p
      have he : g' = ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) :=
        (huniq h.1 p).unique hg' (hφ h p)
      subst he
      exact (hmov p (φ h p) (y p) (y' p)).1 hmv
    · intro he p
      exact ⟨_, hφ h p, (hmov p (φ h p) (y p) (y' p)).2 (congrFun he p)⟩

  have hrel : GRel (Z := Z) (FP := FP) F F' =
      (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y') := by
    funext y y'
    apply propext
    constructor
    · rintro ⟨h, hh, hm⟩
      exact ⟨⟨h, (mem_H0sub F F' h).2 hh⟩, (key ⟨h, (mem_H0sub F F' h).2 hh⟩ y y').1 hm⟩
    · rintro ⟨h, hh⟩
      exact ⟨h.1, (mem_H0sub F F' h.1).1 h.2, (key h y y').2 hh⟩

  have hstab : ∀ y : Dat Z FP, (stabY F F' y).encard =
      {h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • y p) = y}.encard := by
    intro y
    have hs : stabY F F' y = Subtype.val '' {h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • y p) = y} := by
      ext g
      constructor
      · rintro ⟨hg, hm⟩
        exact ⟨⟨g, (mem_H0sub F F' g).2 hg⟩, (key ⟨g, (mem_H0sub F F' g).2 hg⟩ y y).1 hm, rfl⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨(mem_H0sub F F' h.1).1 h.2, (key h y y).2 hh⟩
    rw [hs, Subtype.val_injective.encard_image]
  rw [massA, hrel]
  refine tsum_congr fun o => ?_

  have hin : InGen d o.out ↔
      (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite := by
    unfold InGen
    refine and_congr (forall_congr' fun p => ?_) Iff.rfl
    constructor
    · rintro ⟨g, hg, hm⟩
      exact ⟨⟨g, hg⟩, (hmov p ⟨g, hg⟩ (d p) (o.out p)).1 hm⟩
    · rintro ⟨g, hg⟩
      exact ⟨g.1, g.2, (hmov p g (d p) (o.out p)).2 hg⟩
  by_cases hc : (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite
  · rw [if_pos (hin.2 hc), if_pos hc, hstab]
  · rw [if_neg (mt hin.1 hc), if_neg hc]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMassEqSumOverRationalGroupOrbitsStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genusMass_eq_sum_over_rationalGroup_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → Function.Injective φ → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → ∀ d : Dat Z FP, massA F F' d = ∑' o : Quot (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y'), if (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite then (({h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • o.out p) = o.out}.encard : ℝ≥0∞))⁻¹ else 0 := by
  first | exact @GlobalTheory.Unfold.massA_eq_sum_orbits | exact GlobalTheory.Unfold.massA_eq_sum_orbits | (intros; apply GlobalTheory.Unfold.massA_eq_sum_orbits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelLinearMapMatrixExists
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelLinearMapMatrixExists
noncomputable section
open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.TypeAsm.GramPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D}

theorem crd_map_mulVec (m : (VS D).V →ₗ[D.host.E] (VS D).V) (y : (VS D).V) :
    X.crd (m y) = (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i) *ᵥ X.crd y := by
  unfold Formalism.L2.SG.Pf.toV HidaSetting.crd crdOf
  have hb : ∀ j : Fin X.B.I.n, (∑ i, X.ιE ((Pi.single j (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) i) • X.bas i) = X.bas j := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hbj
      simp [Pi.single_apply, hbj]
    · intro h
      exact absurd (Finset.mem_univ j) h
  simp only [hb]
  funext i
  conv_lhs => rw [← X.bas.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Matrix.of_apply, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem phiV_linMat (C : Choice X 1) (τ : D.what₂.Tau) (m : (VS D).V →ₗ[D.host.E] (VS D).V) :
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  obtain ⟨-, hQ, -⟩ := C.isT τ
  refine ⟨C.Qi τ * (X.B.I.P (vOf X τ))⁻¹ *
      (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map (X.B.I.φ (vOf X τ)) *
      X.B.I.P (vOf X τ) * C.Q τ, fun y => ?_⟩
  have hP : (X.B.I.P (vOf X τ))⁻¹ * ((Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map
      (X.B.I.φ (vOf X τ)) * (X.B.I.P (vOf X τ) * (X.B.I.P (vOf X τ))⁻¹)) =
      (X.B.I.P (vOf X τ))⁻¹ * (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map
      (X.B.I.φ (vOf X τ)) := by
    by_cases h : IsUnit (X.B.I.P (vOf X τ)).det
    · rw [Matrix.mul_nonsing_inv _ h, Matrix.mul_one]
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.zero_mul, Matrix.zero_mul]
  have hw : (fun i => X.B.I.φ (vOf X τ) (X.crd (m y) i)) =
      (Matrix.of fun i j => X.crd (m (Formalism.L2.SG.Pf.toV X (Pi.single j 1))) i).map (X.B.I.φ (vOf X τ)) *ᵥ
        (fun i => X.B.I.φ (vOf X τ) (X.crd y i)) := by
    rw [crd_map_mulVec m y]
    funext i
    exact RingHom.map_mulVec _ _ _ i
  have e1 : ∀ z, GlobalTheory.TypeAsm.phiV C τ z =
      (C.Qi τ * (X.B.I.P (vOf X τ))⁻¹) *ᵥ (fun i => X.B.I.φ (vOf X τ) (X.crd z i)) := by
    intro z
    unfold GlobalTheory.TypeAsm.phiV Formalism.L2.SG.HidaSetting.rv
    rw [Matrix.mulVec_mulVec]
  rw [e1, e1, hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul, hP]

end GlobalTheory.TypeAsm.GramPf

namespace GlobalTheory.TypeAsm

theorem phiV_linMat_all : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau)
    (m : (VS D).V →ₗ[D.host.E] (VS D).V),
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  intro D X C τ m
  exact GramPf.phiV_linMat C τ m

end GlobalTheory.TypeAsm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelLinearMapMatrixExistsStatement
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModel_linearMap_matrix_exists : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau) (m : (VS D).V →ₗ[D.host.E] (VS D).V),
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  first | exact @GlobalTheory.TypeAsm.phiV_linMat_all | exact GlobalTheory.TypeAsm.phiV_linMat_all | (intros; apply GlobalTheory.TypeAsm.phiV_linMat_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralPointsAlgebraSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralPointsAlgebraSubgroup
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.AlgCutSubgroup

variable {n : ℕ} {ε : Fin n → Bool}

theorem sign_sq : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

theorem inv_sub_one (g : Formalism.REAL.UJ ε) :
    uMat g⁻¹ - 1 = Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := sign_sq
  have hg : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have hMN : uMat g * uMat g⁻¹ = 1 := by
    unfold uMat
    simp
  have hN : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
    calc uMat g⁻¹ = (Formalism.REAL.Jm ε * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g)) * uMat g⁻¹ := by
          rw [hg, hJ, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [hMN, Matrix.mul_one]
  rw [hN, conjTranspose_sub, conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJ]

theorem exists_subgroup : ∀ (I : AutInst) (xf : I.Gf) (A : InfinitePlace I.F → Submodule ℂ (Matrix (Fin I.n) (Fin I.n) ℂ)), (∀ v, ∀ X ∈ A v, ∀ Y ∈ A v, X * Y ∈ A v) → (∀ v, ∀ X ∈ A v, Formalism.REAL.Jm (I.ε v) * Xᴴ * Formalism.REAL.Jm (I.ε v) ∈ A v) → ∃ Γ : Subgroup I.Ginf, (Γ : Set I.Ginf) = {g | g ∈ latGroup I xf ∧ ∀ v, uMat (g v) - 1 ∈ A v} := by
  intro I xf A h1 h2
  obtain ⟨Γ0, hΓ0⟩ := (GlobalTheory.RatDiscrete.subgroup_countable_discrete I).1
  have hKmul : ∀ a b : I.Gf, a ∈ I.Kset → b ∈ I.Kset → a * b ∈ I.Kset := fun a b ha hb =>
    (Formalism.UG.stabGL I.Lf).mul_mem ha hb
  have hKinv : ∀ a : I.Gf, a ∈ I.Kset → a⁻¹ ∈ I.Kset := fun a ha =>
    (Formalism.UG.stabGL I.Lf).inv_mem ha
  have hKone : (1 : I.Gf) ∈ I.Kset := (Formalism.UG.stabGL I.Lf).one_mem
  have hUmul : ∀ (v : InfinitePlace I.F) (g h : I.Ginf), uMat ((g * h) v) = uMat (g v) * uMat (h v) :=
    fun _ _ _ => rfl
  have hUinv : ∀ (v : InfinitePlace I.F) (g : I.Ginf), uMat (g⁻¹ v) = uMat (g v)⁻¹ := fun _ _ => rfl
  have hUone : ∀ v : InfinitePlace I.F, uMat ((1 : I.Ginf) v) = 1 := fun _ => rfl
  refine ⟨{ carrier := {g | g ∈ latGroup I xf ∧ ∀ v, uMat (g v) - 1 ∈ A v},
            mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · rintro g h ⟨hg, hgA⟩ ⟨hh, hhA⟩
    refine ⟨?_, fun v => ?_⟩
    · unfold latGroup at hg hh ⊢
      obtain ⟨γ, hγ, rfl, hk⟩ := hg
      obtain ⟨δ, hδ, rfl, hk'⟩ := hh
      refine ⟨γ * δ, ?_, rfl, ?_⟩
      · rw [← hΓ0] at hγ hδ ⊢
        exact Γ0.mul_mem hγ hδ
      · have e : xf⁻¹ * (γ * δ).2 * xf = (xf⁻¹ * γ.2 * xf) * (xf⁻¹ * δ.2 * xf) := by
          simp [mul_assoc]
        rw [e]
        exact hKmul _ _ hk hk'
    · have e : uMat ((g * h) v) - 1 =
          (uMat (g v) - 1) * (uMat (h v) - 1) + (uMat (g v) - 1) + (uMat (h v) - 1) := by
        rw [hUmul]
        noncomm_ring
      rw [e]
      exact add_mem (add_mem (h1 v _ (hgA v) _ (hhA v)) (hgA v)) (hhA v)
  · refine ⟨?_, fun v => ?_⟩
    · unfold latGroup
      refine ⟨1, ?_, rfl, ?_⟩
      · rw [← hΓ0]
        exact Γ0.one_mem
      · simpa using hKone
    · rw [hUone, sub_self]
      exact zero_mem _
  · rintro g ⟨hg, hgA⟩
    refine ⟨?_, fun v => ?_⟩
    · unfold latGroup at hg ⊢
      obtain ⟨γ, hγ, rfl, hk⟩ := hg
      refine ⟨γ⁻¹, ?_, rfl, ?_⟩
      · rw [← hΓ0] at hγ ⊢
        exact Γ0.inv_mem hγ
      · have e : xf⁻¹ * γ⁻¹.2 * xf = (xf⁻¹ * γ.2 * xf)⁻¹ := by
          simp [mul_assoc]
        rw [e]
        exact hKinv _ hk
    · rw [hUinv, inv_sub_one]
      exact h2 v _ (hgA v)

end GlobalTheory.AlgCutSubgroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralPointsAlgebraSubgroupStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_points_algebra_subgroup : ∀ (I : AutInst) (xf : I.Gf) (A : InfinitePlace I.F → Submodule ℂ (Matrix (Fin I.n) (Fin I.n) ℂ)), (∀ v, ∀ X ∈ A v, ∀ Y ∈ A v, X * Y ∈ A v) → (∀ v, ∀ X ∈ A v, Formalism.REAL.Jm (I.ε v) * Xᴴ * Formalism.REAL.Jm (I.ε v) ∈ A v) → ∃ Γ : Subgroup I.Ginf, (Γ : Set I.Ginf) = {g | g ∈ latGroup I xf ∧ ∀ v, uMat (g v) - 1 ∈ A v} := by
  first | exact @GlobalTheory.AlgCutSubgroup.exists_subgroup | exact GlobalTheory.AlgCutSubgroup.exists_subgroup | (intros; apply GlobalTheory.AlgCutSubgroup.exists_subgroup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthComplementUnitVectorSameFields
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthComplementUnitVectorSameFields
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PerpReduce

section Lat

variable {E E' : Type} [Field E] [Field E'] {n : ℕ} (e : E' ≃+* E)

instance ringHomSurjective_mapRingEquiv : RingHomSurjective (RingOfIntegers.mapRingEquiv e : 𝓞 E' →+* 𝓞 E) :=
  ⟨(RingOfIntegers.mapRingEquiv e).surjective⟩

def vecMap (n : ℕ) : (Fin n → E') →ₛₗ[(RingOfIntegers.mapRingEquiv e : 𝓞 E' →+* 𝓞 E)] (Fin n → E) where
  toFun y := fun i => e (y i)
  map_add' a b := by funext i; simp
  map_smul' r a := by
    funext i
    show e ((r : E') * a i) = e (r : E') * e (a i)
    rw [map_mul]

def latMap (L : Submodule (𝓞 E') (Fin n → E')) : Submodule (𝓞 E) (Fin n → E) := L.map (vecMap e n)

theorem mem_latMap (L : Submodule (𝓞 E') (Fin n → E')) (y : Fin n → E') :
    (fun i => e (y i)) ∈ latMap e L ↔ y ∈ L := by
  refine ⟨fun ⟨z, hz, h⟩ => ?_, fun h => ⟨y, h, rfl⟩⟩
  have : z = y := funext fun i => e.injective (congrFun h i)
  exact this ▸ hz

theorem exists_vec (x : Fin n → E) : ∃ y : Fin n → E', x = fun i => e (y i) :=
  ⟨fun i => e.symm (x i), by funext i; simp⟩

theorem latMap_fg (L : Submodule (𝓞 E') (Fin n → E')) (h : L.FG) : (latMap e L).FG := h.map _

theorem latMap_span (L : Submodule (𝓞 E') (Fin n → E'))
    (h : Submodule.span E' (L : Set (Fin n → E')) = ⊤) :
    Submodule.span E (latMap e L : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := exists_vec e x
  have hy : y ∈ Submodule.span E' (L : Set (Fin n → E')) := h ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ((mem_latMap e L y).2 hy)
  | zero =>
    have : (fun i => e ((0 : Fin n → E') i)) = 0 := by funext i; simp
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun i => e ((a + b) i)) = (fun i => e (a i)) + (fun i => e (b i)) := by funext i; simp
    rw [this]; exact add_mem ha hb
  | smul r a _ ha =>
    have : (fun i => e ((r • a) i)) = e r • (fun i => e (a i)) := by funext i; simp
    rw [this]; exact Submodule.smul_mem _ _ ha

theorem mem_range_iff (a : E') :
    e a ∈ (algebraMap (𝓞 E) E).range ↔ a ∈ (algebraMap (𝓞 E') E').range := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨RingOfIntegers.mapRingEquiv e.symm b, ?_⟩
    show e.symm (b : E) = a
    rw [show (b : E) = e a from hb]; simp
  · rintro ⟨b, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e b, rfl⟩

variable [StarRing E] [StarRing E'] (he : ∀ y, e (star y) = star (e y))
include he

theorem hform_map (J : Matrix (Fin n) (Fin n) E') (y x : Fin n → E') :
    Formalism.UG.hform (starRingEnd E) (J.map e) (fun i => e (y i)) (fun i => e (x i)) =
      e (Formalism.UG.hform (starRingEnd E') J y x) := by
  simp [Formalism.UG.hform, starRingEnd_apply, he]

theorem isHerm_map {J : Matrix (Fin n) (Fin n) E'} (hJ : Formalism.UG.IsHerm (starRingEnd E') J) :
    Formalism.UG.IsHerm (starRingEnd E) (J.map e) := by
  ext i j
  have h : star (J j i) = J i j := congrFun (congrFun hJ i) j
  show star (e (J j i)) = e (J i j)
  rw [← h, he]

theorem latMap_dual {J : Matrix (Fin n) (Fin n) E'} {L : Submodule (𝓞 E') (Fin n → E')}
    (h : ∀ x : Fin n → E', x ∈ L ↔
      ∀ y ∈ L, Formalism.UG.hform (starRingEnd E') J y x ∈ (algebraMap (𝓞 E') E').range) (x : Fin n → E) :
    x ∈ latMap e L ↔
      ∀ y ∈ latMap e L, Formalism.UG.hform (starRingEnd E) (J.map e) y x ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨x, rfl⟩ := exists_vec e x
  rw [mem_latMap, h]
  refine ⟨fun H y hy => ?_, fun H y hy => ?_⟩
  · obtain ⟨y, rfl⟩ := exists_vec e y
    rw [hform_map e he, mem_range_iff]
    exact H y ((mem_latMap e L y).1 hy)
  · rw [← mem_range_iff e, ← hform_map e he]
    exact H _ ((mem_latMap e L y).2 hy)

end Lat

theorem det_map_ne {E E' : Type} [Field E] [Field E'] {n : ℕ} (e : E' ≃+* E)
    {J : Matrix (Fin n) (Fin n) E'} (h : J.det ≠ 0) : (J.map e).det ≠ 0 := by
  have := (IsUnit.mk0 _ h).map (e : E' →+* E)
  rw [RingHom.map_det] at this
  exact this.ne_zero

def sibOf (I I' : AutInst) (e : I'.E ≃+* I.E) (he : ∀ y, e (star y) = star (e y)) : Sib I :=
  have h := fun v : InfinitePlace I.F =>
    GlobalTheory.AutInhab.exists_frame (GlobalTheory.AutInhab.isHerm_map I.cm (isHerm_map e he I'.J_herm) (I.φ v))
      (GlobalTheory.AutInhab.isUnit_det_map (det_map_ne e I'.J_det) (I.φ v))
  { n := I'.n
    J := I'.J.map e
    J_herm := isHerm_map e he I'.J_herm
    J_det := det_map_ne e I'.J_det
    L := latMap e I'.L
    L_span := latMap_span e _ I'.L_span
    L_fg := latMap_fg e _ I'.L_fg
    L_dual := latMap_dual e he I'.L_dual
    ε := fun v => (h v).choose
    P := fun v => (h v).choose_spec.choose
    P_unit := fun v => (h v).choose_spec.choose_spec.1
    P_spec := fun v => (h v).choose_spec.choose_spec.2 }

theorem exists_sib : ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf → ∃ (D : Sib I) (B : Matrix (Fin I.n) (Fin D.n) I.E), IsPerp D s x B xf ∧ ∀ (c : InfinitePlace I.F → ℝ) (μ : Measure D.inst.Gf) [SigmaFinite μ] [μ.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μ' : Measure I'.Gf) [SigmaFinite μ'] [μ'.IsHaarMeasure], IsGaugeAll D.inst c → IsGaugeAll I' c' → gaugeVol D.inst c μ = gaugeVol I' c' μ' := by
  intro I I' e s x A xf ⟨he, hn, hx, hxA, hA, hxL, hL⟩
  refine ⟨sibOf I I' e he, A, ⟨hn, hx, hxA, hA, hxL, fun y => ?_⟩, ?_⟩
  · obtain ⟨y, rfl⟩ := exists_vec (n := I'.n) e y
    exact (mem_latMap e I'.L y).trans (hL y)
  · intro c μ _ _ c' μ' _ _ hc hc'
    refine GlobalTheory.T.gaugeVolume_eq_of_semilinear_isometry_genus (sibOf I I' e he).inst I' e (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) 1 he rfl ?_
      (fun y => ?_) c μ c' μ' hc hc'
    · show (1 : Matrix (Fin I'.n) (Fin I'.n) I.E)ᴴ * I'.J.map e * (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) =
        I'.J.map e
      rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    · rw [GlobalTheory.GaussMean.Test.lamX_one]
      show _ ↔ (1 : Matrix (Fin I'.n) (Fin I'.n) I.E) *ᵥ (fun i => e (y i)) ∈ latMap e I'.L
      rw [Matrix.one_mulVec, mem_latMap]

end GlobalTheory.PerpReduce
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthComplementUnitVectorSameFieldsStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthComplement_unitVector_same_fields : ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf → ∃ (D : Sib I) (B : Matrix (Fin I.n) (Fin D.n) I.E), IsPerp D s x B xf ∧ ∀ (c : InfinitePlace I.F → ℝ) (μ : Measure D.inst.Gf) [SigmaFinite μ] [μ.IsHaarMeasure] (c' : InfinitePlace I'.F → ℝ) (μ' : Measure I'.Gf) [SigmaFinite μ'] [μ'.IsHaarMeasure], IsGaugeAll D.inst c → IsGaugeAll I' c' → gaugeVol D.inst c μ = gaugeVol I' c' μ' := by
  first | exact @GlobalTheory.PerpReduce.exists_sib | exact GlobalTheory.PerpReduce.exists_sib | (intros; apply GlobalTheory.PerpReduce.exists_sib <;> assumption)
end
end
