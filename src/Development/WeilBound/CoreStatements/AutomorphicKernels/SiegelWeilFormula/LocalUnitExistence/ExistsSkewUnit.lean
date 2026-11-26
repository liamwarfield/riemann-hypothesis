module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOfLeaves
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.ExistsLocUnit
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace PositivityTheory.SiegelWeilFormula.Ldexb.UnitA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem exists_xi (h : IsCMExt F E σ) : ∃ ξ : E, ξ ≠ 0 ∧ σ ξ = -ξ := by
  by_cases hx : ∃ x : E, σ x ≠ x
  · obtain ⟨x, hx⟩ := hx
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, sig_sig h]; ring
  · push Not at hx
    exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hr : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := h.2.2.2 τ x
      rw [hx] at this
      exact this.symm
    have := h.2.1
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) (InfinitePlace.isReal_mk_iff.2 hr)

omit [NumberField E] in
theorem compFin_cA (v : Pl (F := F)) (z : AE F E) : compFin F E v (cA σ z) = sigR (Fv F v) σ (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

omit [NumberField E] in
theorem compInf_cA (w : InfinitePlace F) (z : AE F E) :
    compInf F E w (cA σ z) = sigR w.Completion σ (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

omit [NumberField E] in
theorem compFin_inclR (v : Pl (F := F)) (x : E) : compFin F E v (inclR (AF F) x) = inclR (Fv F v) x := by
  change Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] x) = (1 : Fv F v) ⊗ₜ[F] x
  simp

omit [NumberField E] in
theorem compInf_inclR (w : InfinitePlace F) (x : E) : compInf F E w (inclR (AF F) x) = inclR w.Completion x := by
  change Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] x) = (1 : w.Completion) ⊗ₜ[F] x
  simp

omit [NumberField F] [NumberField E] in
theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := rfl

theorem exists_S (ξ : E) : ∃ S : Finset (Pl (F := F)), ∀ v ∉ S,
    inclR (Fv F v) ξ ∈ intLoc F E v ∧ inclR (Fv F v) ξ⁻¹ ∈ intLoc F E v := by
  have h := (GlobalTheory.ThK.Dbl.Frame.ae_locInt (F := F) ξ).and (GlobalTheory.ThK.Dbl.Frame.ae_locInt (F := F) ξ⁻¹)
  refine ⟨(Filter.eventually_cofinite.1 h).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
  exact ⟨hv.1.mem, hv.2.mem⟩

theorem exists_locUnit {B : Base F E} (hB : B.IsGood σ) {ξ : E} (hξ : ξ ≠ 0) (hσξ : σ ξ = -ξ) (v : Pl (F := F)) :
    ∃ u : (Fv F v ⊗[F] E)ˣ, (u : Fv F v ⊗[F] E) ∈ intLoc F E v ∧
      ((u⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v ∧ sigR (Fv F v) σ u = -(u : Fv F v ⊗[F] E) := by
  have hc := hB.cm
  rcases (GlobalTheory.KFinLoc.split_or_inert F E σ B hB v :
    Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w) with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · set e := splitAlgEquiv hc τ
    have hu : e.symm (1, -1) * e.symm (1, -1) = 1 := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul, neg_mul_neg, mul_one]
      exact map_one _
    let u : (Fv F v ⊗[F] E)ˣ := ⟨e.symm (1, -1), e.symm (1, -1), hu, hu⟩
    have hm : e.symm (1, -1) ∈ intLoc F E v := (mem_intLoc_iff_split hc τ).2
      ⟨by rw [splitProj_symm]; exact one_mem _, by rw [splitProj_comp_symm]; exact neg_mem (one_mem _)⟩
    refine ⟨u, hm, hm, ?_⟩
    apply e.injective
    change e (sigR (Fv F v) σ (e.symm (1, -1))) = e (-(e.symm (1, -1)))
    rw [splitAlgEquiv_sigR, map_neg, AlgEquiv.apply_symm_apply]
    simp
  · have h : w.under (𝓞 F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v
    have hv0 : w.valuation E ξ ≠ 0 := (Valuation.ne_zero_iff _).2 hξ
    set m := WithZero.log (w.valuation E ξ)
    set z : E := algebraMap F E (π ^ m) * ξ with hzdef
    have hz : w.valuation E z = 1 := by
      rw [hzdef, map_mul, GlobalTheory.InertValRestr.valuation_algebraMap_of_isInertAt F E v w hw, map_zpow₀, hπ,
        ← WithZero.exp_log hv0, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp [m]
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, map_zero] at hz; exact zero_ne_one hz
    have hint : ∀ y : E, w.valuation E y = 1 → inclR (Fv F v) y ∈ intLoc F E v := by
      intro y hy
      rw [GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h]
      change GlobalTheory.LFun.toCompl h ((1 : Fv F v) ⊗ₜ[F] y) ∈ _
      rw [GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]
      change _ ∈ HeightOneSpectrum.adicCompletionIntegers E w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w y
      exact (this.trans hy).le
    have h1 : inclR (F := F) (Fv F v) z * inclR (F := F) (Fv F v) z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz0, map_one]
    have h2 : inclR (F := F) (Fv F v) z⁻¹ * inclR (F := F) (Fv F v) z = 1 := by rw [← map_mul, inv_mul_cancel₀ hz0, map_one]
    refine ⟨⟨inclR (Fv F v) z, inclR (Fv F v) z⁻¹, h1, h2⟩, hint z hz, hint z⁻¹ (by rw [map_inv₀, hz, inv_one]), ?_⟩
    change sigR (Fv F v) σ (inclR (Fv F v) z) = -inclR (Fv F v) z
    rw [sigR_inclR, hzdef, map_mul, AlgHom.commutes, hσξ, mul_neg, map_neg]

end PositivityTheory.SiegelWeilFormula.Ldexb.UnitA

end
end

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def sc1 {R : Type} [CommRing R] : Rˣ →* GL (Fin 1) R :=
  Units.map (Matrix.scalar (Fin 1) : R →+* Matrix (Fin 1) (Fin 1) R).toMonoidHom

omit [NumberField F] [NumberField E] in
theorem det_sc1 {R : Type} [CommRing R] (x : Rˣ) : Matrix.GeneralLinearGroup.det (sc1 x) = x := by
  ext
  simp [sc1, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]

omit [NumberField F] [NumberField E] in
theorem map_det_bc {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (γ : GL (Fin 1) R) :
    Units.map f.toMonoidHom (Matrix.GeneralLinearGroup.det γ) = Matrix.GeneralLinearGroup.det (Formalism.UG.bc f γ) := by
  ext
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply]
  rw [RingHom.map_det]
  rfl

theorem exists_skewUnit {B : Base F E} (hB : B.IsGood σ) :
    ∃ r : (AE F E)ˣ, cA σ (r : AE F E) = -(r : AE F E) ∧
      (∀ v, compFin F E v (r : AE F E) ∈ intLoc F E v ∧ compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) ∈ intLoc F E v) ∧
      ∀ w, ‖piInf (B.emb w) (r : AE F E)‖ = 1 := by
  classical
  have hc := hB.cm
  obtain ⟨ξ, hξ, hσξ⟩ := UnitA.exists_xi hc
  obtain ⟨S, hS⟩ := UnitA.exists_S (F := F) ξ
  choose u hu1 hu2 hu3 using UnitA.exists_locUnit hB hξ hσξ
  let xv : ∀ v : Pl (F := F), (Fv F v ⊗[F] E)ˣ := fun v =>
    ⟨inclR (F := F) (Fv F v) ξ, inclR (F := F) (Fv F v) ξ⁻¹, by rw [← map_mul, mul_inv_cancel₀ hξ, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hξ, map_one]⟩
  let b : ∀ v : Pl (F := F), GL (Fin 1) (Fv F v ⊗[F] E) := fun v => if v ∈ S then sc1 (u v * (xv v)⁻¹) else 1
  have hb : ∀ v ∉ S, b v = 1 := fun v hv => if_neg hv
  let e : ∀ w : InfinitePlace F, w.Completion ⊗[F] E ≃+* ℂ := fun w =>
    RingEquiv.ofBijective (infEmb (B.emb w)) (infEmb_bijective hc (B.emb w))
  have hτ : ∀ w : InfinitePlace F, (B.emb w).1 ξ ≠ 0 := fun w => (map_ne_zero _).2 hξ
  let c : ∀ w : InfinitePlace F, GL (Fin 1) (w.Completion ⊗[F] E) := fun w =>
    sc1 (Units.map (e w).symm.toMonoidHom (Units.mk0 (Complex.I / (B.emb w).1 ξ) (div_ne_zero Complex.I_ne_zero (hτ w))))
  obtain ⟨γ, hγf, hγi⟩ := Frames.exists_GL_of_components S b hb c
  let X : (AE F E)ˣ := ⟨inclR (F := F) (AF F) ξ, inclR (F := F) (AF F) ξ⁻¹, by rw [← map_mul, mul_inv_cancel₀ hξ, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hξ, map_one]⟩
  let r : (AE F E)ˣ := Matrix.GeneralLinearGroup.det γ * X

  have hf : ∀ v, Units.map (compFin F E v).toMonoidHom r = if v ∈ S then u v else xv v := by
    intro v
    have hX : Units.map (compFin F E v).toMonoidHom X = xv v := Units.ext (UnitA.compFin_inclR v ξ)
    rw [map_mul, map_det_bc, hγf v, hX]
    by_cases hv : v ∈ S
    · simp only [b, if_pos hv, det_sc1, inv_mul_cancel_right]
    · simp only [b, if_neg hv, map_one, one_mul]
  have hfv : ∀ v, compFin F E v (r : AE F E) = ((if v ∈ S then u v else xv v : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    intro v; rw [← hf v]; rfl
  have hfi : ∀ v, compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) =
      (((if v ∈ S then u v else xv v : (Fv F v ⊗[F] E)ˣ)⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
    intro v; rw [← hf v, ← map_inv]; rfl

  have hi : ∀ w, infEmb (B.emb w) (compInf F E w (r : AE F E)) = Complex.I := by
    intro w
    have hX : Units.map (compInf F E w).toMonoidHom X = Units.map (inclR (F := F) w.Completion).toMonoidHom (Units.mk0 ξ hξ) :=
      Units.ext (UnitA.compInf_inclR w ξ)
    have h1 : Units.map (compInf F E w).toMonoidHom r = Matrix.GeneralLinearGroup.det (c w) *
        Units.map (inclR (F := F) w.Completion).toMonoidHom (Units.mk0 ξ hξ) := by
      rw [map_mul, map_det_bc, hγi w, hX]
    have h2 : compInf F E w (r : AE F E) = (e w).symm (Complex.I / (B.emb w).1 ξ) * inclR (F := F) w.Completion ξ := by
      have := congrArg Units.val h1
      simpa [c, det_sc1] using this
    rw [h2, map_mul]
    have h3 : infEmb (B.emb w) ((e w).symm (Complex.I / (B.emb w).1 ξ)) = Complex.I / (B.emb w).1 ξ :=
      (e w).apply_symm_apply _
    have h4 : infEmb (B.emb w) (inclR (F := F) w.Completion ξ) = (B.emb w).1 ξ := by
      change infEmb (B.emb w) ((1 : w.Completion) ⊗ₜ[F] ξ) = _
      rw [infEmb_tmul, map_one, one_mul]
    rw [h3, h4, div_mul_cancel₀ _ (hτ w)]
  refine ⟨r, ?_, fun v => ?_, fun w => ?_⟩
  ·
    have key : -(cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E)) = 1 := by
      refine GlobalTheory.AdelicU.Supp.adTens_eq_one' (fun w => ?_) (fun v => ?_)
      · have hz : sigR w.Completion σ (compInf F E w (r : AE F E)) = -compInf F E w (r : AE F E) := by
          apply (e w).injective
          change infEmb (B.emb w) _ = infEmb (B.emb w) _
          rw [← infEmb_sigR hc, hi w, map_neg, hi w, Complex.conj_I]
        have hu : compInf F E w (r : AE F E) * compInf F E w ((r⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [map_neg, map_mul, UnitA.compInf_cA, hz, neg_mul, neg_neg, hu]
      · have hz : sigR (Fv F v) σ (compFin F E v (r : AE F E)) = -compFin F E v (r : AE F E) := by
          rw [hfv v]
          by_cases hv : v ∈ S
          · simp only [if_pos hv]; exact hu3 v
          · simp only [if_neg hv, xv]
            rw [UnitA.sigR_inclR, hσξ, map_neg]
        have hu : compFin F E v (r : AE F E) * compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [map_neg, map_mul, UnitA.compFin_cA, hz, neg_mul, neg_neg, hu]
    have : cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E) = -1 := by
      rw [← neg_neg (cA σ (r : AE F E) * _), key]
    calc cA σ (r : AE F E) = cA σ (r : AE F E) * ((r⁻¹ : (AE F E)ˣ) : AE F E) * (r : AE F E) := by
          rw [mul_assoc, Units.inv_mul, mul_one]
      _ = -(r : AE F E) := by rw [this, neg_one_mul]
  · rw [hfv v, hfi v]
    by_cases hv : v ∈ S
    · simp only [if_pos hv]; exact ⟨hu1 v, hu2 v⟩
    · simp only [if_neg hv]; exact hS v hv
  · change ‖infEmb (B.emb w) (compInf F E w (r : AE F E))‖ = 1
    rw [hi w, Complex.norm_I]

end PositivityTheory.SiegelWeilFormula.Ldexb

end
