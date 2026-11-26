module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPointLineDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial Matrix NumberField
open scoped ComplexOrder

noncomputable section

namespace DualPointLineDegreeAlt

theorem sum_log_norm {L : Type*} [Field L] [NumberField L] {x : L} (hx : x ≠ 0) :
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  classical
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))]
  congr 1
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ (fun φ => ‖φ x‖)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real,
    Real.norm_eq_abs]

theorem isMultiHomog_X {T : Type} [Fintype T] (t : T) :
    IsMultiHomog (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) (fun _ => 1) := by
  classical
  intro m hm k
  obtain ⟨⟩ := k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  rw [Finset.sum_eq_single t]
  · simp
  · intro c _ hc
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hc (sigma_mk_injective h).symm
  · simp

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} {K' : Type} [Field K'] [NumberField K'] [Algebra K K']

theorem dualNormSq_point (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (v : Fin i → K') (σ' : K' →+* ℂ) :
    dualNormSq b hb (fun t => σ' (dualPointCoord b v ⟨(), t⟩)) =
      (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re := by
  classical
  set σ := σ'.comp (algebraMap K K') with hσ
  let w : (K →+* ℂ) × Fin i → ℂ := fun q => if q.1 = σ then σ' (v q.2) else 0
  have hw : dualRecover b hb (fun t => σ' (dualPointCoord b v ⟨(), t⟩)) = w := by
    rw [dualRecover, LinearEquiv.symm_apply_eq]
    funext t
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      dualEmbMatrix, w, Fintype.sum_prod_type, mul_ite, mul_zero, dualPointCoord, map_sum, map_mul]
    rw [Finset.sum_eq_single σ (fun τ _ hτ => by simp [hτ]) (by simp)]
    simp [hσ]
  rw [dualNormSq, hw, Finset.sum_eq_single σ, Matrix.det_unique]
  · simp only [w, if_true, gramAt]
    rfl
  · intro τ _ hτ
    have h0 : (fun j => w (τ, j)) = 0 := by
      funext j
      simp [w, hτ]
    rw [h0]
    simp
  · simp

end DualPointLineDegreeAlt


open DualPointLineDegreeAlt in
theorem DualPointLineDegree.proof (hPt : DualCurvePoint.Statement) (hPos : PointDegCPos.Statement)
    (hAr : PointArInt.Statement) (hVert : PointVertR.Statement) (hIdx : DualLineIndex.Statement)
    (hSemi : DualLineSemipositive.Statement) : DualPointLineDegree.Statement := by
  intro K _ _ i F T _ _ b hb II hII W hW hbW
  obtain ⟨K', _, _, _, v, hv, rfl⟩ := hPt K i F T b W hW hbW
  set y := dualPointCoord b v with hy
  set A := dualLine F b hb with hA
  refine ⟨hPos T K' y hW, K', inferInstance, inferInstance, inferInstance, v, hv, ?_⟩
  obtain ⟨t₀, ht₀⟩ := hW.2.1.2.2 ()
  set s : MRing (dualBlocks T) := X ⟨(), t₀⟩ with hs
  have hs1 : IsMultiHomog s (fun _ => 1) := isMultiHomog_X t₀
  have hsec : IsSectionOn (mCoordIdeal y) A s := ⟨fun _ => 1, fun _ => rfl, hs1, ht₀⟩
  have hsm : IsSmoothHerm A := (hSemi K i F T b hb).1
  have hy0 : y ⟨(), t₀⟩ ≠ 0 := by
    intro h
    apply ht₀
    change mConeMap y (X ⟨(), t₀⟩) = 0
    simp [mConeMap, h]

  have hR := (hII Unit (dualBlocks T)).2.2 (mCoordIdeal y) 0 Fin.elim0 A s (fun _ => 1) hW
    (fun j => j.elim0) hsm (fun _ => rfl) hs1 ht₀
  have hsnoc : (Fin.snoc (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) A : Fin 1 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) =
      ![A] := by
    funext j
    fin_cases j
    rfl
  rw [hsnoc, Inter.SpecIntHeightFormula.proof Inter.arithVarZero Unit (dualBlocks T) _ _ A s hW hsm hsec] at hR

  have hV := hVert T K' y s hW hs1 ht₀
  have hI := hAr T K' y A s hW hsec
  have hL := hIdx K i F T b K' v hv
  have hys : aeval y s = y ⟨(), t₀⟩ := by simp [hs]
  have hlog : ∀ σ' : K' →+* ℂ, logNorm A s (fun p => σ' (y p)) =
      Real.log ‖σ' (y ⟨(), t₀⟩)‖ -
        1 / 2 * Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re := by
    intro σ'
    have hq : dualNormSq b hb (fun t => σ' (y ⟨(), t⟩)) =
        (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re :=
      dualNormSq_point b hb v σ'
    have hpos : 0 < dualNormSq b hb (fun t => σ' (y ⟨(), t⟩)) := by
      have := A.pos (fun p => σ' (y p)) (fun _ => ⟨t₀, (map_ne_zero σ').mpr hy0⟩)
      simpa [hA, dualLine] using this
    have hne : ‖σ' (y ⟨(), t₀⟩)‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hy0)
    simp only [logNorm, hs, map_X, eval_X, hA, dualLine]
    rw [Real.log_div hne (Real.sqrt_pos.mpr hpos).ne', Real.log_sqrt hpos.le, ← hq]
    ring
  rw [Finset.sum_congr rfl fun σ' _ => hlog σ', Finset.sum_sub_distrib,
    sum_log_norm hy0, ← Finset.mul_sum] at hI
  rw [hys] at hV
  have hn : (0 : ℝ) < Module.finrank ℚ K' := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < degC (mCoordIdeal y) := by exact_mod_cast hPos T K' y hW
  rw [← hy] at hL
  have hdeg : F.lineDegree K' v = (-Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
      (1 : Submodule (𝓞 K') K').toAddSubgroup) - 1 / 2 * ∑ σ' : K' →+* ℂ,
        Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re) /
      Module.finrank ℚ K' := by
    unfold HermLattice.lineDegree subDegree normalise
    rw [eq_inv_of_mul_eq_one_left hL, Real.log_inv]
  have hR' : II Unit (dualBlocks T) (mCoordIdeal y) 1 ![A] =
      vertR (mCoordIdeal y) Fin.elim0 s - arInt (mCoordIdeal y) s A Fin.elim0 := hR
  have key : (vertR (mCoordIdeal y) Fin.elim0 s - arInt (mCoordIdeal y) s A Fin.elim0) *
      Module.finrank ℚ K' = degC (mCoordIdeal y) * (Real.log (genIndex
        (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup) +
        1 / 2 * ∑ σ' : K' →+* ℂ,
          Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re) := by
    linear_combination hV - hI
  rw [hdeg, hR', neg_div, ← neg_div, div_eq_div_iff hn.ne' hd.ne']
  linear_combination key

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointArInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace PointArithIntersection

open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree

variable {T : Type} [Fintype T]

theorem logNorm_smul {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (fun _ : Unit => T)} {s : MRing (fun _ : Unit => T)}
    {P : Ideal (MRing (fun _ : Unit => T))} (hs : IsSectionOn P A s) (c : ℂ) (hc : c ≠ 0)
    (z : (Σ _ : Unit, T) → ℂ) : logNorm A s (fun p => c * z p) = logNorm A s z := by
  obtain ⟨a, ha, hhom, -⟩ := hs
  have hz : (fun p : Σ _ : Unit, T => c * z p) = scaleBlock () c z := by
    funext p
    simp [scaleBlock]
  have hh : A.h (fun p => c * z p) = ‖c‖ ^ A.a () * A.h z := by
    simpa using A.smul (fun _ => c) z (fun _ => hc)
  unfold logNorm
  rw [hh, hz, eval_scaleBlock () c z s a hhom, ha (), zpow_natCast, norm_mul, norm_pow]
  rw [mul_div_mul_left _ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hc))]

variable {K' : Type} [Field K'] [NumberField K']

theorem eq_of_ptOf_eq_smul {y : (Σ _ : Unit, T) → K'} {c : Unit → T} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {φ ψ : blockFnField y →ₐ[ℚ] ℂ} (t : ℂ) (h : ptOf y c φ = fun p => t * ptOf y c ψ p) : φ = ψ := by
  have ht : t = 1 := by
    have := congrFun h ⟨(), c ()⟩
    simp only [ptOf_chart hc, mul_one] at this
    exact this.symm
  subst ht
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (blockFnField_eq y c hc) ?_
  rintro _ ⟨p, rfl⟩
  have := congrFun h p
  simp only [one_mul] at this
  exact this

theorem sum_reps_eq {y : (Σ _ : Unit, T) → K'} (hP : IsArithVar (mCoordIdeal y) 1) {c : Unit → T}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (R : Finset ((Σ _ : Unit, T) → ℂ))
    (hR : ∀ t ∈ R, t ∈ mcPts (mCoordIdeal y))
    (hU : ∀ z ∈ mcPts (mCoordIdeal y), ∃! t, t ∈ R ∧ SameOrbit z t)
    (F : ((Σ _ : Unit, T) → ℂ) → ℝ) (hF : ∀ t : ℂ, t ≠ 0 → ∀ z, F (fun p => t * z p) = F z)
    [Fintype (blockFnField y →ₐ[ℚ] ℂ)] :
    ∑ t ∈ R, F t = ∑ φ : blockFnField y →ₐ[ℚ] ℂ, F (ptOf y c φ) := by
  have hex : ∀ t ∈ R, ∃ φ : blockFnField y →ₐ[ℚ] ℂ,
      ptOf y c φ = (fun p => (t ⟨p.1, c p.1⟩)⁻¹ * t p) ∧ ∀ k, t ⟨k, c k⟩ ≠ 0 :=
    fun t ht => exists_ptOf hP hc (hR t ht)
  refine Finset.sum_bij (fun t ht => (hex t ht).choose) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro t ht t' ht' he
    have h1 := (hex t ht).choose_spec
    have h2 := (hex t' ht').choose_spec
    rw [he] at h1
    obtain ⟨u, -, hu⟩ := hU t (hR t ht)
    have e1 : t = u := hu t ⟨ht, ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩⟩
    have e2 : t' = u := by
      refine hu t' ⟨ht', fun k => t ⟨k, c k⟩ * (t' ⟨k, c k⟩)⁻¹,
        fun k => mul_ne_zero (h1.2 k) (inv_ne_zero (h2.2 k)), funext fun p => ?_⟩
      have := congrFun (h1.1.symm.trans h2.1) p
      have h0 := h1.2 p.1
      have h0' := h2.2 p.1
      simp only at this ⊢
      rw [show t p = t ⟨p.1, c p.1⟩ * ((t ⟨p.1, c p.1⟩)⁻¹ * t p) by field_simp, this]
      ring
    rw [e1, e2]
  · intro φ _
    obtain ⟨u, ⟨hu, ⟨d, hd, hdu⟩⟩, -⟩ := hU _ (ptOf_mem hc φ)
    refine ⟨u, hu, eq_of_ptOf_eq_smul hc ((u ⟨(), c ()⟩)⁻¹ * (d ())⁻¹) ?_⟩
    rw [(hex u hu).choose_spec.1, hdu]
    funext p
    have h0 := hd ()
    ring_nf
    field_simp
  · intro t ht
    rw [(hex t ht).choose_spec.1]
    exact (hF _ (inv_ne_zero ((hex t ht).choose_spec.2 ())) t).symm

theorem sum_ringHom_restrict (κ : IntermediateField ℚ K') (H : (κ →ₐ[ℚ] ℂ) → ℝ)
    [Fintype (κ →ₐ[ℚ] ℂ)] :
    ∑ σ : K' →+* ℂ, H ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) =
      (Module.finrank κ K' : ℝ) * ∑ f, H f := by
  classical
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K' ℂ)
    (fun σ : K' →+* ℂ => H ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')))
    (fun σ : K' →ₐ[ℚ] ℂ => H (σ.comp (IsScalarTower.toAlgHom ℚ κ K'))) (fun _ => rfl)]
  let res : (K' →ₐ[ℚ] ℂ) → (κ →ₐ[ℚ] ℂ) := fun σ => σ.comp (IsScalarTower.toAlgHom ℚ κ K')
  rw [← Fintype.sum_fiberwise res, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hconst : ∀ i : {σ // res σ = f}, H (res i) = H f := fun i => by rw [i.2]
  rw [Finset.sum_congr rfl fun i _ => hconst i, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  congr 1
  have e : {σ // res σ = f} ≃ @AlgHom κ K' ℂ _ _ _ _ f.toRingHom.toAlgebra :=
    ((algHomEquivSigma (A := ℚ) (B := κ) (C := K') (D := ℂ)).subtypeEquiv
      (p := fun σ => res σ = f) (q := fun x => x.1 = f) fun σ => Iff.rfl).trans (Equiv.sigmaSubtype f)
  let _ := f.toRingHom.toAlgebra
  rw [Fintype.card_eq_nat_card, Nat.card_congr e,
    AlgHom.natCard_of_splits κ K' ℂ fun _ => IsAlgClosed.splits _]

end PointArithIntersection


open PointArithIntersection IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree in
theorem PointArInt.proof : PointArInt.Statement := by
  intro T _ K' _ _ y A s hP hs
  classical
  obtain ⟨c0, hc0⟩ := hP.2.1.2.2 ()
  let c : Unit → T := fun _ => c0
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h => hc0 (X_mem_of_eq_zero h)
  obtain ⟨R, hR, hU, hsum⟩ := Inter.regularityPointsSum_holds.proof Unit (fun _ => T) (mCoordIdeal y) hP
  have harInt : arInt (mCoordIdeal y) s A (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (fun _ : Unit => T)) =
      ∑ t ∈ R, logNorm A s t := by
    unfold arInt
    have e0 : (fun (j : Fin 0) (z : (Σ _ : Unit, T) → ℂ) =>
        Real.log (((Fin.elim0 j : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (fun _ : Unit => T))).h z)) =
        (Fin.elim0 : Fin 0 → ((Σ _ : Unit, T) → ℂ) → ℝ) := funext fun j => j.elim0
    rw [e0]
    apply hsum
    rintro z z' - ⟨d, hd, rfl⟩
    exact logNorm_smul hs (d ()) (hd ()) z'
  set κ := blockFnField y
  have hσ : ∀ σ : K' →+* ℂ, logNorm A s (fun p => σ (y p)) =
      logNorm A s (ptOf y c ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K'))) := by
    intro σ
    have hy0 : σ (y ⟨(), c0⟩) ≠ 0 := (map_ne_zero σ).mpr (hc ())
    have e : (fun p => σ (y p)) = fun p => σ (y ⟨(), c0⟩) *
        ptOf y c ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) p := by
      funext p
      have : ptOf y c ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) p =
          σ (y p / y ⟨(), c0⟩) := rfl
      rw [this, map_div₀]
      field_simp
    rw [e, logNorm_smul hs _ hy0]
  rw [harInt, sum_reps_eq hP hc R hR hU (logNorm A s) (fun t ht z => logNorm_smul hs t ht z),
    Finset.sum_congr rfl (fun σ _ => hσ σ),
    sum_ringHom_restrict κ (fun φ => logNorm A s (ptOf y c φ)), degC_eq hP,
    AlgHom.natCard_of_splits ℚ κ ℂ fun _ => IsAlgClosed.splits _, ← Module.finrank_mul_finrank ℚ κ K']
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights
end
