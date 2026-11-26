module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LeadingMinors
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LatticeGluingRadicals

namespace Formalism.L2.SG.LeadingMinorsNonvanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem leading_minor_ne_zero {D : D7} {T T' : ℕ} (hT : 0 < T) (F : LFlag (D.sp.Y 0) D.R.rS (T : D.host.E))
    (F' : LFlag (D.sp.Y 0) D.R.rS (T' : D.host.E)) (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hG : Gval F F' ≠ 0) :
    Dr1 F F' ≠ 0 := by
  intro h0
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have h1 := (b_G_pos (p_starConj D) hT F F' hz hz' hG (p_posX D T hT F) τ).1
  rw [b_tauG (p_starConj D) F F' τ, h0, map_zero, norm_zero, Complex.ofReal_re] at h1
  have h2 : (0:ℝ) ≤ (T:ℝ) * T' * ‖τ (Dr F F')‖ ^ 2 := by positivity
  nlinarith

theorem atSomeAll_holds : Formalism.L2.SG.TermTieOf.AtSomeAll := by
  intro D X Y u u' t hG hrel
  obtain ⟨F', ⟨hP, hmk⟩, hR⟩ := hrel
  have hf := Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) _ ((Y.rowsOK u).1 t.lam t.mem)
  have hGv : Gval (lf D (X.Fu u)) F' ≠ 0 := by
    have e := Formalism.L2.SG.TermDef.Gt_mk hf.1 ⟨F', hP⟩
    rw [hmk] at e
    exact fun h0 => hG (e.trans h0)
  have hTu := tie_Tu_pos D u
  have hTu' := tie_Tu_pos D u'
  have hDr1 : Dl (lf D (X.Fu u)).fl F'.fl (D.R.rS + 1) ≠ 0 :=
    leading_minor_ne_zero hTu (lf D (X.Fu u)) F' rfl hP.1.2 hGv
  have geo := cell_geom D.host.F D.host.E (hS D) D.R.rS _ _ (lf D (X.Fu u)).fl F'.fl (tie_trace D.sp.cm)
    (tie_aniso D _ hTu (lf D (X.Fu u))) (tie_aniso D _ hTu' F') hR
  obtain ⟨p, hp⟩ := cell_of_matRel cell_inv cell_sign cell_bruhat cell_mono cell_point (le_refl (D.R.rS + 1))
    ((Zhat (lf D (X.Fu u)).fl F'.fl).submatrix (Fin.castLE (le_refl (D.R.rS + 1))) (Fin.castLE (le_refl (D.R.rS + 1))))
    (by rw [← tie_Dl_eq']; exact hDr1) (geo (D.R.rS + 1) le_rfl (Or.inr ⟨rfl, hGv⟩))
  refine ⟨p, F', ⟨hP, hmk⟩, hGv, ?_⟩
  obtain ⟨L, U, hL, hU, hZ⟩ := hp
  refine ⟨L, U, hL, hU, ?_⟩
  rw [← hZ]
  funext a b
  first
  | rfl
  | (simp [ZhatOM, ZhatL, Matrix.submatrix_apply]; rfl)

end Formalism.L2.SG.LeadingMinorsNonvanishing

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.LocJEq

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

private theorem isUnit_y_det (τ : D.what₂.Tau) : IsUnit (C.y τ).det := by
  obtain ⟨hQiQ, hQQi, hH, -⟩ := C.isT τ
  have hJJ : Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  generalize Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) = J at hH hJJ
  have hHinv : (C.Qi τ * J * (C.Qi τ)ᴴ) * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = 1 := by
    rw [← hH]
    calc C.Qi τ * J * (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * J * C.Q τ)
        = C.Qi τ * J * (C.Q τ * C.Qi τ)ᴴ * J * C.Q τ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hQQi, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_assoc (C.Qi τ), hJJ, Matrix.mul_one, hQiQ]
  have hy' : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have h1 : (C.Qi τ * J * (C.Qi τ)ᴴ * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) * C.y τ = 1 := by
    rw [Matrix.mul_assoc, hy', hHinv]
  exact Matrix.isUnit_det_of_left_inverse h1

private theorem conj_lemma_2 (τ : D.what₂.Tau) (w : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) :
    C.Q τ * (C.Qi τ * w * C.Q τ * (C.y τ)⁻¹) * C.y τ * C.Qi τ = w := by
  obtain ⟨hQiQ, hQQi, -, -⟩ := C.isT τ
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQQi, Matrix.one_mul, ← Matrix.mul_assoc (C.y τ)⁻¹ (C.y τ),
    Matrix.nonsing_inv_mul _ (isUnit_y_det C τ), Matrix.one_mul, hQQi, Matrix.mul_one]

private theorem Qi_mul_Q_conj_mul_y_inv_eq (τ : D.what₂.Tau) (x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    C.Qi τ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) * C.Q τ * (C.y τ)⁻¹ = Matrix.of x := by
  obtain ⟨hQiQ, hQQi, -, -⟩ := C.isT τ
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Qi τ) (C.Q τ), hQiQ, Matrix.one_mul, ← Matrix.mul_assoc (C.Qi τ) (C.Q τ), hQiQ,
    Matrix.one_mul, Matrix.mul_nonsing_inv _ (isUnit_y_det C τ), Matrix.mul_one]

theorem mem_of_range (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (x : Set.range (Smap C τ γ)) :
    umat γ * (C.Q τ * Matrix.of x.1 * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ)) := by
  obtain ⟨z, hz⟩ := x.2
  rw [← hz]
  unfold Smap
  simp only [Equiv.apply_symm_apply]
  rw [conj_lemma_2 C τ]
  unfold umat UJset
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.mul_inv_cancel_left]
  exact z.2

def smapInv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (x : Set.range (Smap C τ γ)) :
    Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) :=
  ujOf' (umat γ * (C.Q τ * Matrix.of x.1 * C.y τ * C.Qi τ)) (mem_of_range C τ γ x)

theorem smapInv_cont (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Continuous (smapInv C τ γ) := by
  unfold smapInv ujOf'
  apply Continuous.subtype_mk
  have hx : Continuous fun x : Set.range (Smap C τ γ) => (Matrix.of (x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    continuous_subtype_val
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · dsimp only [Function.comp_def]
    fun_prop
  · dsimp only [Units.inv_mk]
    fun_prop

theorem smap_measEmb (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : MeasurableEmbedding (Smap C τ γ) := by
  have hu : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => umat (γ⁻¹ * z) := by
    unfold umat
    exact Units.continuous_val.comp (continuous_subtype_val.comp (continuous_const.mul continuous_id))
  have hc : Continuous (Smap C τ γ) := by
    have h2 : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹ :=
      ((continuous_const.matrix_mul hu).matrix_mul continuous_const).matrix_mul continuous_const
    exact h2
  refine MeasurableEmbedding.of_measurable_inverse_on_range hc.measurable ?_ (smapInv_cont C τ γ).measurable ?_
  · have hS : Set.range (Smap C τ γ) =
        {x | umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ))} := by
      ext x
      constructor
      · intro hx
        exact mem_of_range C τ γ ⟨x, hx⟩
      · intro hx
        have hx' : umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ)) := hx
        refine ⟨ujOf' _ hx', ?_⟩
        unfold Smap umat ujOf'
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mk, Units.inv_mul_cancel_left]
        rw [Qi_mul_Q_conj_mul_y_inv_eq C τ]
        simp
    rw [hS]
    apply IsClosed.measurableSet
    have hof : Continuous fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => Matrix.of x := continuous_id
    have hf : Continuous fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) :=
      continuous_const.matrix_mul (((continuous_const.matrix_mul hof).matrix_mul continuous_const).matrix_mul
        continuous_const)
    unfold UJset Formalism.REAL.inUJ
    exact isClosed_eq ((hf.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hf) continuous_const
  · intro z
    apply Subtype.ext
    apply Units.ext
    unfold smapInv ujOf' Set.rangeFactorization Smap
    simp only [Equiv.apply_symm_apply, Units.val_mk]
    rw [conj_lemma_2 C τ]
    unfold umat
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.mul_inv_cancel_left]

variable (hB : WuBessel C)

theorem integrand_S (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of (Smap C τ γ z)))).smulRight
      ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z))) =
      sclOf hB u u' τ • Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) (γ⁻¹ * z)) := by
  rw [phi'_S, phi_S]
  unfold Formalism.L2.SG.TermOp.rk1
  have hc : (starRingEnd ℂ) (sclOf hB u u' τ) = sclOf hB u u' τ := by
    unfold sclOf
    exact Complex.conj_ofReal _
  change (innerSL ℂ (sclOf hB u u' τ • X.Wloc u' (vOf X τ) (γ⁻¹ * z))).smulRight
      (X.Wloc u (vOf X τ) z) =
    sclOf hB u u' τ • (innerSL ℂ (X.Wloc u' (vOf X τ) (γ⁻¹ * z))).smulRight (X.Wloc u (vOf X τ) z)
  rw [map_smulₛₗ, hc]
  ext v
  simp [smul_smul]

theorem rank_one_continuous {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] {T : Type*} [TopologicalSpace T] {a : T → V} {b : T → V'} (ha : Continuous a)
    (hb : Continuous b) : Continuous fun t => Formalism.L2.SG.TermOp.rk1 (a t) (b t) := by
  unfold Formalism.L2.SG.TermOp.rk1
  have h1 : Continuous fun t => innerSL ℂ (b t) := (innerSL ℂ).continuous.comp hb
  exact (ContinuousLinearMap.smulRightL ℂ V' V).continuous₂.comp₂ h1 ha

theorem integrand_aesm (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) :
    AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) (ν.map (Smap C τ γ)) := by
  have hw : ∀ w : D.what₂.Word, Continuous (X.Wloc w (vOf X τ)) := fun w => by
    first
      | exact X.W.Wloc_cont w _
      | exact X.Wloc_cont w _
      | exact X.toWBlk.Wloc_cont w _
  rw [(smap_measEmb C τ γ).aestronglyMeasurable_map_iff]
  have he : (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) ∘ Smap C τ γ =
      fun z => sclOf hB u u' τ •
        Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) (γ⁻¹ * z)) := by
    funext z
    exact integrand_S C hB u u' τ γ z
  rw [he]
  apply Continuous.aestronglyMeasurable
  exact (rank_one_continuous (hw u) ((hw u').comp (continuous_const.mul continuous_id))).const_smul (sclOf hB u u' τ)

theorem locJ_map_eq' (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) :
    (locS hB u u' τ).J (ν.map (Smap C τ γ)) (trG (C.Q τ) (C.Qi τ) γ) =
      ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) •
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) :=
  locJ_map_eq (C := C) (hB := hB) u u' τ γ ν (integrand_aesm (C := C) (hB := hB) u u' τ γ ν)

end Formalism.L2.SG.Pf.LocJEq
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittFlags
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem gmap_mul (a b : V ≃ₗ[K] V) (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

theorem gmap_one (L : Submodule R V) : Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L = L := by
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_inv_gmap (a : V ≃ₗ[K] V) (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ (Formalism.HermitianLatticesTheory.gmap a L) = L := by
  rw [← gmap_mul, inv_mul_cancel, gmap_one]

theorem gmap_gmap_inv (a : V ≃ₗ[K] V) (L : Submodule R V) :
    Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap a⁻¹ L) = L := by
  rw [← gmap_mul, mul_inv_cancel, gmap_one]

end Gen

theorem LatIso_holds (D : D7) : Formalism.L2.SG.TermTieOf.LatIso D := by
  intro β hβ Λ
  obtain ⟨-, hloc, -, hU, hLat⟩ := Formalism.HermitianLatticesTheory.isomAct _ _ _ (VS D).hT β hβ Λ
  refine ⟨fun hΛ => ?_, hLat.2, hU.2⟩
  simp only [Formalism.HermitianLatticesTheory.genus, Set.mem_setOf_eq] at hΛ ⊢
  obtain ⟨hΛL, hΛG⟩ := hΛ
  letI := hLat.2 hΛL.toIsLattice
  refine ⟨?_, fun p hp => ?_⟩
  · refine { span_eq_top := ?_ }
    have he : ((Formalism.HermitianLatticesTheory.gmap β Λ : _) : Set _) =
        (β.toLinearMap : _ → _) '' (Λ : Set _) := by
      ext x
      simp [Formalism.HermitianLatticesTheory.gmap]
    rw [he, Submodule.span_image β.toLinearMap, hΛL.span_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr β.surjective
  obtain ⟨g, hg, hgΛ⟩ := hΛG p hp
  refine ⟨β * g, (Formalism.HermitianLatticesTheory.isom _).mul_mem hβ hg, ?_⟩
  rw [gmap_mul, hgΛ, hloc p]

end Formalism.L2.SG.Pf.WittFlags
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointQuot
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.JointQuot

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def OkPt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  (∃ γ, IsPtRep X u u' w γ) ∧ ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v

def ooF (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ x : X.B.I.Ginf) : X.Vpi u' →L[ℂ] X.Vpi u :=
  TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x))

def StInv (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ s ∈ StInf X u u' (gamW X u u' w), ∀ x,
    ooF X u u' (gamW X u u' w) (s * x) = ooF X u u' (gamW X u u' w) x

section Uniq

variable {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem lint_eq_bruhat (μR ν : Measure X.B.I.Ginf) (S : Set X.B.I.Ginf) (hS0 : μR Sᶜ = 0)
    (b : X.B.I.Ginf → ℝ≥0∞) (hbm : Measurable b) (hb1 : ∀ x, ∫⁻ s, b (s * x) ∂μR = 1)
    (hν : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR ν) (f : X.B.I.Ginf → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ s ∈ S, ∀ x, f (s * x) = f x) :
    ∫⁻ x, f x ∂ν = ∫⁻ x, b x * f x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
  rw [hν (fun x => b x * f x) (hbm.mul hf)]
  refine lintegral_congr fun x => ?_
  show f x = ∫⁻ s, b (s * x) * f (s * x) ∂μR
  have hS : ∀ᵐ s ∂μR, s ∈ S := by
    rw [ae_iff]
    exact hS0
  have h1 : ∫⁻ s, b (s * x) * f (s * x) ∂μR = ∫⁻ s, b (s * x) * f x ∂μR := by
    refine lintegral_congr_ae ?_
    filter_upwards [hS] with s hs
    rw [hinv s hs x]
  rw [h1, show ∫⁻ s, b (s * x) * f x ∂μR = (∫⁻ s, b (s * x) ∂μR) * f x from
    lintegral_mul_const _ (hbm.comp (measurable_mul_const x)), hb1, one_mul]

@[instance_reducible] def invMS (S : Set X.B.I.Ginf) : MeasurableSpace X.B.I.Ginf where
  MeasurableSet' A := MeasurableSet A ∧ ∀ s ∈ S, ∀ x, (s * x ∈ A ↔ x ∈ A)
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl A hA := ⟨hA.1.compl, fun s hs x => not_congr (hA.2 s hs x)⟩
  measurableSet_iUnion A hA := ⟨MeasurableSet.iUnion fun i => (hA i).1, fun s hs x => by
    simp only [Set.mem_iUnion]; exact exists_congr fun i => (hA i).2 s hs x⟩

theorem invMS_le (S : Set X.B.I.Ginf) : invMS S ≤ (inferInstance : MeasurableSpace X.B.I.Ginf) := by
  exact fun _ hA => hA.1

theorem integral_eq_of_quot (μR ν₁ ν₂ : Measure X.B.I.Ginf) (S : Set X.B.I.Ginf) (hS0 : μR Sᶜ = 0)
    (b : X.B.I.Ginf → ℝ≥0∞) (hbm : Measurable b) (hb1 : ∀ x, ∫⁻ s, b (s * x) ∂μR = 1)
    (h₁ : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR ν₁) (h₂ : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR ν₂)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (F : X.B.I.Ginf → E) (hF : Continuous F) (hinv : ∀ s ∈ S, ∀ x, F (s * x) = F x) :
    ∫ x, F x ∂ν₁ = ∫ x, F x ∂ν₂ := by
  have hle := invMS_le (X := X) S
  have hmeas : ∀ A, MeasurableSet[invMS S] A → ν₁ A = ν₂ A := by
    intro A hA
    have hAm : MeasurableSet A := hA.1
    have hind : ∀ s ∈ S, ∀ x, A.indicator (fun _ => (1 : ℝ≥0∞)) (s * x) =
        A.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      intro s hs x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hA.2 s hs x).2 hx)]
      · rw [Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (fun hx' => hx ((hA.2 s hs x).1 hx'))]
    have e₁ := lint_eq_bruhat μR ν₁ S hS0 b hbm hb1 h₁ _ (measurable_const.indicator hAm) hind
    have e₂ := lint_eq_bruhat μR ν₂ S hS0 b hbm hb1 h₂ _ (measurable_const.indicator hAm) hind
    rw [lintegral_indicator_const hAm, one_mul] at e₁ e₂
    rw [e₁, e₂]
  have htrim : ν₁.trim hle = ν₂.trim hle := by
    refine @Measure.ext _ (invMS S) _ _ fun A hA => ?_
    rw [trim_measurableSet_eq hle hA, trim_measurableSet_eq hle hA]
    exact hmeas A hA
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  borelize E
  have hFm : StronglyMeasurable[invMS S] F := by
    have hFm' : Measurable[invMS S] F := by
      intro B hB
      refine ⟨hF.measurable hB, fun s hs x => ?_⟩
      simp only [Set.mem_preimage, hinv s hs x]
    exact hFm'.stronglyMeasurable
  rw [integral_trim (μ := ν₁) hle hFm, integral_trim (μ := ν₂) hle hFm, htrim]

end Uniq

private theorem norm_tensU_eq_prod_norm (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)
    (x : ∀ v, X.Vloc u v) : ‖X.tensU u x‖ = ∏ v, ‖x v‖ := by
  have h2 := X.tensU_inner u x x
  simp only [inner_self_eq_norm_sq_to_K] at h2
  rw [Finset.prod_pow] at h2
  have h3 : ‖X.tensU u x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by exact_mod_cast h2
  exact (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun v _ => norm_nonneg _) two_ne_zero).1 h3

private theorem norm_rk1_eq_mul_norm {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (a : V) (b : V') :
    ‖TermOp.rk1 a b‖ = ‖b‖ * ‖a‖ := by
  unfold TermOp.rk1
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]

private theorem eq_of_inner_tensU_eq (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)
    (a b : X.Vpi u) (hab : ∀ z, inner ℂ (X.tensU u z) a = inner ℂ (X.tensU u z) b) : a = b := by
  have hsub : ∀ c ∈ Submodule.span ℂ (Set.range (X.tensU u)), inner ℂ c (a - b) = 0 := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      rw [inner_sub_right, hab, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul r x _ hx => rw [inner_smul_left, hx, mul_zero]
  have h0 := hsub (a - b) (by rw [X.tensU_span u]; trivial)
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

private theorem tensU_eq_zero_of_apply_eq_zero (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)
    (x : ∀ v, X.Vloc u v) (v0 : InfinitePlace X.B.I.F) (h : x v0 = 0) : X.tensU u x = 0 := by
  rw [← norm_eq_zero, norm_tensU_eq_prod_norm]
  exact Finset.prod_eq_zero (Finset.mem_univ v0) (by rw [h, norm_zero])

theorem oo_eq_tens (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf)
    (μR νq : Measure X.B.I.Ginf) (S : Set X.B.I.Ginf) (hS0 : μR Sᶜ = 0)
    (b : X.B.I.Ginf → ℝ≥0∞) (hbm : Measurable b) (hb1 : ∀ x, ∫⁻ s, b (s * x) ∂μR = 1)
    (ν : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (hσ : ∀ v, SigmaFinite (ν v))
    (hq : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR νq)
    (hp : Formalism.L2.SG.HidaSetting.IsQuotMeasS X.B.I μR (Measure.pi ν))
    (hinv : ∀ s ∈ S, ∀ x, ooF X u u' γ (s * x) = ooF X u u' γ x) (y : ∀ v, X.Vloc u' v) :
    (haveI := FiniteDimensional.complete ℂ (X.Vpi u);
      Formalism.L2.SG.TermOp.OO νq Set.univ (X.Wu u) (X.Wu u') γ) (X.tensU u' y) =
    X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
      Jv (ν v) (X.Wloc u v) (X.Wloc u' v) (γ v)) (y v)) := by
  have := FiniteDimensional.complete ℂ (X.Vpi u)
  have : ∀ v, CompleteSpace (X.Vloc u v) := fun v => FiniteDimensional.complete ℂ _
  have hWc : ∀ u₀, Continuous (X.Wu u₀) := fun u₀ => (X.Wu_spec u₀).2.2.1
  have hcont : Continuous (ooF X u u' γ) := by
    unfold ooF
    refine continuous_clm_apply.2 fun ξ => ?_
    simp only [TermOp.rankOneInnerOperator_apply]
    exact (((hWc u').comp (continuous_const.mul continuous_id)).inner continuous_const).smul (hWc u)
  have hOO : Formalism.L2.SG.TermOp.OO νq Set.univ (X.Wu u) (X.Wu u') γ =
      Formalism.L2.SG.TermOp.OO (Measure.pi ν) Set.univ (X.Wu u) (X.Wu u') γ := by
    unfold Formalism.L2.SG.TermOp.OO
    rw [Measure.restrict_univ, Measure.restrict_univ]
    exact integral_eq_of_quot μR νq (Measure.pi ν) S hS0 b hbm hb1 hq hp (ooF X u u' γ) hcont hinv
  rw [hOO]
  have hJ : ∀ v, Jv (ν v) (X.Wloc u v) (X.Wloc u' v) (γ v) =
      ∫ t, TermOp.rk1 (X.Wloc u v t) (X.Wloc u' v ((γ v)⁻¹ * t)) ∂(ν v) := by
    intro v
    simp only [Jv, Formalism.L2.SG.TermOp.OO, Measure.restrict_univ]
  simp only [hJ, Formalism.L2.SG.TermOp.OO, Measure.restrict_univ]
  have hLc : ∀ v, Continuous fun t : Formalism.REAL.UJ (X.B.I.ε v) =>
      TermOp.rk1 (X.Wloc u v t) (X.Wloc u' v ((γ v)⁻¹ * t)) := by
    intro v
    refine continuous_clm_apply.2 fun ξ => ?_
    simp only [TermOp.rankOneInnerOperator_apply]
    exact (((X.Wloc_cont u' v).comp (continuous_const.mul continuous_id)).inner
      continuous_const).smul (X.Wloc_cont u v)
  have hnormf : ∀ x : X.B.I.Ginf, ‖TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x))‖ =
      ∏ v, ‖TermOp.rk1 (X.Wloc u v (x v)) (X.Wloc u' v ((γ v)⁻¹ * x v))‖ := by
    intro x
    simp only [norm_rk1_eq_mul_norm, X.Wu_tens, norm_tensU_eq_prod_norm, Pi.mul_apply, Pi.inv_apply,
      Finset.prod_mul_distrib]
  have hmeasf : AEStronglyMeasurable (fun x : X.B.I.Ginf => TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)))
      (Measure.pi ν) := hcont.aestronglyMeasurable
  apply eq_of_inner_tensU_eq X u
  intro z
  by_cases hint : ∀ v, Integrable (fun t : Formalism.REAL.UJ (X.B.I.ε v) =>
      TermOp.rk1 (X.Wloc u v t) (X.Wloc u' v ((γ v)⁻¹ * t))) (ν v)
  · have hfint : Integrable (fun x : X.B.I.Ginf => TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)))
        (Measure.pi ν) :=
      Integrable.mono' (Integrable.fintype_prod_dep fun v => (hint v).norm) hmeasf
        (Filter.Eventually.of_forall fun x => (hnormf x).le)
    have hpt : ∀ x : X.B.I.Ginf,
        inner ℂ (X.tensU u z) (TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)) (X.tensU u' y)) =
          ∏ v, inner ℂ (z v) (TermOp.rk1 (X.Wloc u v (x v)) (X.Wloc u' v ((γ v)⁻¹ * x v)) (y v)) := by
      intro x
      simp only [TermOp.rankOneInnerOperator_apply, X.Wu_tens, inner_smul_right, X.tensU_inner, Pi.mul_apply,
        Pi.inv_apply, Finset.prod_mul_distrib]
    rw [ContinuousLinearMap.integral_apply hfint, ← integral_inner (hfint.apply_continuousLinearMap _),
      X.tensU_inner]
    simp_rw [hpt]
    rw [integral_fintype_prod_eq_prod (fun v t =>
      inner ℂ (z v) (TermOp.rk1 (X.Wloc u v t) (X.Wloc u' v ((γ v)⁻¹ * t)) (y v)))]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [ContinuousLinearMap.integral_apply (hint v),
      ← integral_inner ((hint v).apply_continuousLinearMap _)]
  · push Not at hint
    obtain ⟨v0, hv0⟩ := hint
    have hR0 : X.tensU u (fun v => (∫ t, TermOp.rk1 (X.Wloc u v t) (X.Wloc u' v ((γ v)⁻¹ * t)) ∂(ν v))
        (y v)) = 0 := by
      apply tensU_eq_zero_of_apply_eq_zero X u _ v0
      simp only [integral_undef hv0, ContinuousLinearMap.zero_apply]
    have hL0 : (∫ x, TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)) ∂(Measure.pi ν)) (X.tensU u' y) = 0 := by
      by_cases hf : Integrable (fun x : X.B.I.Ginf => TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)))
          (Measure.pi ν)
      · have h0 : ∫ x, ‖TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x))‖ ∂(Measure.pi ν) = 0 := by
          simp_rw [hnormf]
          rw [integral_fintype_prod_eq_prod (fun v t =>
            ‖TermOp.rk1 (X.Wloc u v t) (X.Wloc u' v ((γ v)⁻¹ * t))‖)]
          exact Finset.prod_eq_zero (Finset.mem_univ v0)
            (integral_undef fun hh => hv0 ((integrable_norm_iff
              (hLc v0).aestronglyMeasurable).1 hh))
        have hae := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg _) hf.norm).1 h0
        have hae' : (fun x : X.B.I.Ginf => TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x))) =ᵐ[Measure.pi ν] 0 := by
          filter_upwards [hae] with x hx
          simpa using hx
        rw [integral_congr_ae hae']
        simp
      · rw [integral_undef hf, ContinuousLinearMap.zero_apply]
    rw [hL0, hR0]

def psiU (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf) : ℂ :=
  Formalism.L2.SG.HidaSetting.psiInf X.B.I X.B.g X.eR X.fR (X.zR u) s

def StRel (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ w, OkPt X u u' w → ∀ s ∈ StInf X u u' (gamW X u u' w),
    psiU X u s * star (psiU X u' ((gamW X u u' w)⁻¹ * s * gamW X u u' w)) = 1

theorem rankOneInnerOperator_smul_smul_eq_mul_conj_smul {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (c d : ℂ) (a : V) (b : V') :
    TermOp.rk1 (c • a) (d • b) = (c * star d) • TermOp.rk1 a b := by
  ext x
  simp only [TermOp.rk1, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, smul_smul,
    innerSL_apply_apply, inner_smul_left]
  congr 1
  rw [Complex.star_def]
  ring

theorem stInv_of_rel (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (h : StRel X u u') : StInv X u u' := by
  intro w hw s hs x
  have hrel := h w hw s hs
  have hW : ∀ (u₀ : D.what₂.Word) (t : X.B.I.Ginf), t ∈ X.NinfU u₀ → ∀ y,
      X.Wu u₀ (t * y) = psiU X u₀ t • X.Wu u₀ y := by
    intro u₀ t ht y
    have h1 := (X.Wu_spec u₀).1 t (fun v => (ht v).1) y
    rw [(X.piU_rep u₀).2.2.2.1 t ht] at h1
    simp only [ContinuousLinearMap.one_apply] at h1
    exact h1
  unfold ooF
  rw [hW u s hs.1 x,
    show (gamW X u u' w)⁻¹ * (s * x) = ((gamW X u u' w)⁻¹ * s * gamW X u u' w) * ((gamW X u u' w)⁻¹ * x) by
      group,
    hW u' _ hs.2, rankOneInnerOperator_smul_smul_eq_mul_conj_smul, hrel, one_smul]

end Formalism.L2.SG.Pf.Carrier.JointQuot
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2RightTranslationThm
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Formalism.L2.SG.Pf.WuBL

theorem l2RightTranslation_thm : L2RightTranslation := by
  classical
  intro k r z hz hT μG μS ν hG hS hq Vp _ W hWc hW0 hWS y hy
  obtain ⟨hGg, hSg, hSG, hRG, hRS⟩ := quotient_measure_unitary_group k r z hz hT
  have hset : PI.QuotientSetting (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (Formalism.QuantumDeterminants.Sset k r z) μG μS ν :=
    ⟨hGg, hSg, hSG, hG, hS, hRG μG hG, hRS μS hS, hq⟩
  let G : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}
  have hGc : IsClosed G := hGg.1.preimage continuous_id
  let F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ((‖W (Matrix.of x)‖₊ : ℝ≥0∞)) ^ 2
  have hFG : F = G.piecewise F (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ G
    · simp [Set.piecewise, hx]
    · simp [Set.piecewise, hx, F, hW0 (Matrix.of x) hx]
  have hcont : ContinuousOn F G := by
    have hW' : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => W (Matrix.of x)) G :=
      hWc.comp continuous_id.continuousOn (fun x hx => hx)
    exact (ENNReal.continuous_pow 2).comp_continuousOn (ENNReal.continuous_coe.comp_continuousOn hW'.nnnorm)
  have hmeas : Measurable F := by
    rw [hFG]
    exact hcont.measurable_piecewise continuousOn_const hGc.measurableSet
  have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x : Formalism.QuantumDeterminants.Mt k r,
      Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
      F (fun i j => (s * Matrix.of x) i j) = F x := by
    intro s hs x hx
    have h2 : ‖W (s * Matrix.of x)‖₊ = ‖W (Matrix.of x)‖₊ := NNReal.eq (hWS s hs (Matrix.of x) hx)
    change ((‖W (s * Matrix.of x)‖₊ : ℝ≥0∞)) ^ 2 = _
    rw [h2]
  exact quotient_invariant (2 * r + k + 1) _ _ μG μS ν hset F hmeas hinv y hy

end Formalism.L2.SG.Pf.WuBL
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPf
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPf

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def IntNX (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : ℝ :=
  (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ /
            (((Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p) *
              (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP) *
    ((Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP * (IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D))

def LocRep (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) : Prop :=
  (∀ v, Measurable (L v) ∧ ∀ cv, 0 ≤ L v cv) ∧
    ∀ c ∈ Good X u u', ∀ v, hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = L v (c v)

def PlaceEnergy (P : Parts X u u') (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  ∀ v, Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v)) ≠ ⊤ ∧
    ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * L v cv) ∂(dcV (D := D)) =
      ENNReal.ofReal (K v * (Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))).toReal)

def ConstPin (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  (∀ v, 0 ≤ K v) ∧
    (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ /
              (((Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p) *
                (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP) *
      ((Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP * ((∏ v, K v) / Formalism.L2.SG.MassDataConc.kapN D)) =
      (P.Gam0 ^ P.S.f)⁻¹

end Formalism.L2.SG.Pf.Carrier.EnergyPf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittExistsHolds
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Flag

variable {D : D7} {T : D.host.E}

theorem flag_span_orth (F : FlagG (VS D) D.R.rS T) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range F.e)) : (VS D).hT x F.z = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact F.z_orth a
  | zero => simp
  | add y w _ _ hy hw => simp [hy, hw]
  | smul c y _ hy => simp [hy]

theorem flag_fvec_indep (hT : T ≠ 0) (F : FlagG (VS D) D.R.rS T) : LinearIndependent D.host.E F.fvec := by
  unfold FlagG.fvec
  rw [linearIndependent_finSnoc]
  refine ⟨F.e_indep, fun hz => hT ?_⟩
  have h1 := flag_span_orth F hz
  rw [F.z_norm] at h1
  exact neg_eq_zero.1 h1

theorem flag_gram {T' : D.host.E} (hTT : T = T') (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T')
    (i j : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec i) (F.fvec j) = (VS D).hT (F'.fvec i) (F'.fvec j) := by
  subst hTT
  have hze : ∀ (G : FlagG (VS D) D.R.rS T) (a : Fin D.R.rS), (VS D).hT G.z (G.e a) = 0 := by
    intro G a
    rw [← (VS D).herm.eq (G.e a) G.z, G.z_orth a, map_zero]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp only [FlagG.fvec, Fin.snoc_last, F.z_norm, F'.z_norm]
    | cast b => simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc, hze]
  | cast a =>
    induction j using Fin.lastCases with
    | last => simp only [FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc, F.z_orth, F'.z_orth]
    | cast b => simp only [FlagG.fvec, Fin.snoc_castSucc, F.e_iso, F'.e_iso]

theorem flag_witt {T' : D.host.E} (hT : T ≠ 0) (hTT : T = T') (F : FlagG (VS D) D.R.rS T)
    (F' : FlagG (VS D) D.R.rS T') :
    ∃ δ : (VS D).V ≃ₗ[D.host.E] (VS D).V, δ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ a, δ (F.e a) = F'.e a) ∧
      δ F.z = F'.z := by
  have hind := flag_fvec_indep hT F
  have hind' := flag_fvec_indep (hTT ▸ hT) F'
  set U := Submodule.span D.host.E (Set.range F.fvec) with hU
  let b : Module.Basis (Fin (D.R.rS + 1)) D.host.E U := Module.Basis.span hind
  let f : U →ₗ[D.host.E] (VS D).V :=
    Finsupp.linearCombination D.host.E F'.fvec ∘ₗ (b.repr : U →ₗ[D.host.E] (Fin (D.R.rS + 1) →₀ D.host.E))
  have hfb : ∀ i, f (b i) = F'.fvec i := by
    intro i
    simp [f, Module.Basis.repr_self, Finsupp.linearCombination_single]
  have hbv : ∀ i, ((b i : U) : (VS D).V) = F.fvec i := by
    intro i
    exact congrArg Subtype.val (Module.Basis.span_apply hind i)
  have hinj : Function.Injective f := by
    have h2 : Function.Injective (Finsupp.linearCombination D.host.E F'.fvec) := hind'
    exact h2.comp b.repr.injective
  have hB : ((VS D).hT.comp f).compl₂ f = ((VS D).hT.comp U.subtype).compl₂ U.subtype := by
    refine LinearMap.ext_basis b b fun i j => ?_
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, hfb, Submodule.subtype_apply, hbv]
    exact (flag_gram hTT F F' i j).symm
  have hiso : ∀ x y : U, (VS D).hT (f x) (f y) = (VS D).hT x y := by
    intro x y
    have h := congrArg (fun B => B x y) hB
    simpa only [LinearMap.compl₂_apply, LinearMap.comp_apply, Submodule.subtype_apply] using h
  obtain ⟨g, hg, hgf⟩ := _root_.witt_extension_theorem D.host.E (VS D).V (VS D).hT
    (fun x y => (VS D).herm.eq x y) (fun x hx => (VS D).nondeg.1 x hx) U f hinj hiso
  have hgi : ∀ i, g (F.fvec i) = F'.fvec i := by
    intro i
    have h := hgf (b i)
    rw [hbv, hfb] at h
    exact h
  refine ⟨g, hg, fun a => ?_, ?_⟩
  · have h := hgi (Fin.castSucc a)
    simpa only [FlagG.fvec, Fin.snoc_castSucc] using h
  · have h := hgi (Fin.last _)
    simpa only [FlagG.fvec, Fin.snoc_last] using h

end Flag

theorem WittExists_holds (D : D7) (X : HidaSetting D) : Formalism.L2.SG.TermTieOf.WittExists X := by
  have hT : ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := fun u =>
    Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  choose δ hδ he hz using fun u => flag_witt (hT u) rfl (X.Fu u) (Formalism.MainNotions.S.Inh.tie_flag0 D u)
  refine ⟨{ δ := δ, isom := hδ, e_eq := fun u a => ?_, z_eq := fun u => ?_ }⟩
  · have h := he u a
    rw [X.Fu_e u] at h
    exact h
  · have h := hz u
    rw [X.flagZVector u] at h
    exact h

end Formalism.L2.SG.Pf.WittFlags
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierInputExistsBuilt
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def instCMT2 (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

attribute [local instance] instCMT2

section hermitianSpaces

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem isBuilt_of_builtPlace {Cb Cc : ℝ} {S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq}
    {p : ∀ v, Formalism.FourierDecayAlt.KB.Pl (Formalism.FourierDecayAlt.D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (h : Formalism.FourierDecayAlt.KB.IsLeadingFormPlace Cb Cc S p f χ A₀) :
    Formalism.FourierDecayAlt.D.IsBuilt S (Formalism.FourierDecayAlt.KB.plT S p) f χ (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p)
      (Formalism.FourierDecayAlt.KB.plTop S p) A₀ := by
  obtain ⟨⟨-, -, -, hχ, -, -, -, -, -, -, -, -, -, -, -, hv⟩, hE, -⟩ := h
  exact ⟨hχ, fun v => ⟨(hv v).2.2.1, (p v).hT, (p v).hF, (p v).hP, (hv v).2.2.2.2, hE v⟩⟩

end hermitianSpaces

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def CarrierDataBound (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (jn CA : ℝ)
    (G0 : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ) (l : ℕ) (C₆ Cc Cb : ℝ) : Prop :=
  ∃ (Wp Wq : InfinitePlace D.host.E → Type) (_ : ∀ x, NormedAddCommGroup (Wp x)) (_ : ∀ x, InnerProductSpace ℂ (Wp x))
    (_ : ∀ x, NormedAddCommGroup (Wq x)) (_ : ∀ x, InnerProductSpace ℂ (Wq x)) (_ : ∀ x, FiniteDimensional ℂ (Wp x))
    (_ : ∀ x, FiniteDimensional ℂ (Wq x))
    (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (p : ∀ v, Formalism.FourierDecayAlt.KB.Pl (Formalism.FourierDecayAlt.D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))) (χ : ℝ → ℝ)
    (A₀ : ℝ) (c : Formalism.FourierDecayAlt.LE.Cut)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ)
    (Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v),
    S.CA = CA ∧ S.G = G0 ∧ S.de = de ∧ S.de' = de' ∧ S.l = l ∧ Formalism.L2.SG.DataInst.Compat S u u' ∧
    Formalism.FourierDecayAlt.KB.IsLeadingFormPlace Cb Cc S p f χ A₀ ∧ Formalism.FourierDecayAlt.JCT.SliceBudget S A₀ ∧ c.χ = χ ∧
    (∀ v, C₆ * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2) ≤
      S.cutHi v - S.cutLo v) ∧
    Formalism.FourierDecayAlt.JCT.VtTensor S (Formalism.FourierDecayAlt.KB.plT S p) f (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p)
      (VtPt X u u' sc i0 i0' FdN FdN' νq) ∧
    BuiltFromX X S u u' (Formalism.FourierDecayAlt.KB.plT S p) f τ Q Qi eP eQ ∧
    BaseFromX X S u u' i0 i0' τ Q Qi (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p) ∧
    TopTie X S u u' sc i0 i0' FdN FdN' νq τ ∧
    VJoint X S u u' sc i0 i0' νq (Formalism.FourierDecayAlt.KB.plT S p) f (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p) τ eP eQ ∧
    ∀ (L : ∀ v : Fin S.f, Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.MA.A (Formalism.FourierDecayAlt.D.parOf S v)
        (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf S v))) (Formalism.FourierDecayAlt.D.parOf S v).r)
      (j : ∀ v : Fin S.f, Formalism.FourierDecayAlt.M.Ty (Formalism.FourierDecayAlt.D.parOf S v) →
        Formalism.FourierDecayAlt.MA.SmQ (Formalism.FourierDecayAlt.D.parOf S v).r (Formalism.FourierDecayAlt.D.parOf S v).TT)
      (lam : ∀ v : Fin S.f, Fin ((Formalism.FourierDecayAlt.D.parOf S v).k + 2 * (Formalism.FourierDecayAlt.D.parOf S v).r + 1) → ℝ)
      (Cm σ : Fin S.f → ℝ),
      (∀ v, Formalism.FourierDecayAlt.JC.IsModelPlace S (Formalism.FourierDecayAlt.KB.plT S p) f χ v (L v) (j v) (lam v) c (Cm v) (σ v)) →
      (∏ v, Formalism.FourierDecayAlt.JCT.jvModel S j Cm v) = jn

end Formalism.L2.SG.Pf.CarrierT
end
end
