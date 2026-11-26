module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.EvLatLatO

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.FinIndex
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.SiegelWeilFormula.HeightDict

open PositivityTheory.SiegelWeilFormula.KWhit.Ht

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lat_vol (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    [lam.IsAddHaarMeasure] : lam (lat E v n : Set (Fin n → v.adicCompletion F ⊗[F] E)) ≠ 0 ∧
      lam (lat E v n : Set (Fin n → v.adicCompletion F ⊗[F] E)) ≠ ⊤ := by
  obtain ⟨ho, hc⟩ := lat_isCO (E := E) v n
  exact ⟨ho.measure_ne_zero lam ⟨0, zero_mem _⟩, hc.measure_lt_top.ne⟩

theorem vol_sig (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
    (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure]
    (S : Set (Fin n → v.adicCompletion F ⊗[F] E)) :
    lam ((fun y i => HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ (y i)) '' S) = lam S := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (v.adicCompletion F) (v.adicCompletion F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (v.adicCompletion F ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (v.adicCompletion F ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  let b := Algebra.TensorProduct.basis (v.adicCompletion F) (Module.finBasis F E)
  let coord : (v.adicCompletion F ⊗[F] E) ≃ₜ+ (Fin (Module.finrank F E) → v.adicCompletion F) :=
    { b.equivFun.toAddEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  haveI : LocallyCompactSpace (v.adicCompletion F ⊗[F] E) :=
    coord.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (v.adicCompletion F ⊗[F] E) :=
    coord.toHomeomorph.isEmbedding.secondCountableTopology
  have : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) := ⟨rfl⟩
  set sg := HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ with hsg
  let Lsg : (v.adicCompletion F ⊗[F] E) →ₗ[v.adicCompletion F] (v.adicCompletion F ⊗[F] E) :=
    (Algebra.TensorProduct.map (AlgHom.id (v.adicCompletion F) (v.adicCompletion F)) σ).toLinearMap
  have hL : ∀ z, Lsg z = sg z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Lsg, hsg, HeckeCharacterZeroLocus.SiegelWeilU.sigR]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hc : Continuous sg := by
    have := IsModuleTopology.continuous_of_linearMap Lsg
    exact (funext hL : ⇑Lsg = ⇑sg) ▸ this
  have hcv : Continuous fun y : Fin n → v.adicCompletion F ⊗[F] E => fun i => sg (y i) :=
    continuous_pi fun i => hc.comp (continuous_apply i)
  let φ : (Fin n → v.adicCompletion F ⊗[F] E) ≃ₜ+ (Fin n → v.adicCompletion F ⊗[F] E) :=
    { toFun := fun y i => sg (y i)
      invFun := fun y i => sg (y i)
      left_inv := fun y => funext fun i => sgv_sgv hcm v (y i)
      right_inv := fun y => funext fun i => sgv_sgv hcm v (y i)
      map_add' := fun y y' => funext fun i => map_add sg _ _
      continuous_toFun := hcv
      continuous_invFun := hcv }
  have hsymm : φ.symm = φ := rfl
  have hχ : addEquivAddHaarChar φ = 1 := by
    have h1 := addEquivAddHaarChar_symm (φ := φ)
    rw [hsymm] at h1
    have hpos := addEquivAddHaarChar_pos φ
    have h2 : addEquivAddHaarChar φ * addEquivAddHaarChar φ = 1 := by
      conv_lhs => arg 1; rw [h1]
      exact inv_mul_cancel₀ hpos.ne'
    have h3 : ((addEquivAddHaarChar φ : ℝ≥0) : ℝ) * (addEquivAddHaarChar φ : ℝ) = 1 := by exact_mod_cast h2
    rcases mul_self_eq_one_iff.1 h3 with h | h
    · exact_mod_cast h
    · linarith [NNReal.coe_nonneg (addEquivAddHaarChar φ)]
  have : lam.Regular := by
    obtain ⟨ho, hc⟩ := lat_isCO (E := E) v n
    exact Measure.regular_of_isAddLeftInvariant hc ⟨0, mem_interior_iff_mem_nhds.mpr (ho.mem_nhds (zero_mem _))⟩ hc.measure_lt_top.ne
  have h1 := addEquivAddHaarChar_smul_map lam φ
  have himg : (fun y i => sg (y i)) '' S = φ.toHomeomorph.toMeasurableEquiv '' S := rfl
  calc lam ((fun y i => sg (y i)) '' S) = (addEquivAddHaarChar φ • lam.map φ) ((fun y i => sg (y i)) '' S) := by
        rw [h1]
    _ = _ := by
      rw [Measure.smul_apply, himg, hχ, one_smul]
      have : Measure.map φ lam = Measure.map φ.toHomeomorph.toMeasurableEquiv lam := rfl
      rw [this, MeasurableEquiv.map_apply, MeasurableEquiv.preimage_image]

theorem norm_sig (v : HeightOneSpectrum (𝓞 F)) (z : v.adicCompletion F ⊗[F] E) :
    Algebra.norm (v.adicCompletion F) (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ z) =
      Algebra.norm (v.adicCompletion F) z :=
  GlobalTheory.Doubling.norm_sigR σ z

theorem fin_index (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (t u D β h : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)) (η e : v.adicCompletion F ⊗[F] E)
    (k k' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (v.adicCompletion F ⊗[F] E))
    (ht : IsUnit t.det) (hD : IsUnit D.det) (htu : tᵀ * u.map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1)
    (hη : IsUnit η) (he : IsUnit e) (he1 : ‖Algebra.norm (v.adicCompletion F) e‖ = 1) (hβ : β = -(η • hᵀ))
    (hh : ∀ a b, HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ (h b a) = h a b) (hkk : k * k' = 1)
    (hk : ∀ i j, k i j ∈ OE E v) (hk' : ∀ i j, k' i j ∈ OE E v)
    (h1 : e • t = D * k.toBlocks₂₁) (h2 : e • (β * u) = D * k.toBlocks₂₂)
    (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure] :
    ‖Algebra.norm (v.adicCompletion F) D.det‖ = ‖Algebra.norm (v.adicCompletion F) t.det‖ *
      Gen.nu2 lam (latM v (t.map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)))
        (latM v ((η • u).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ))) h := by
  set sg := HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ with hsg
  set O : Set (Fin n → v.adicCompletion F ⊗[F] E) := ((lat E v n : AddSubgroup _) : Set (Fin n → v.adicCompletion F ⊗[F] E)) with hO
  set sv : (Fin n → v.adicCompletion F ⊗[F] E) → (Fin n → v.adicCompletion F ⊗[F] E) := fun y i => sg (y i) with hsv
  have hsvO : ∀ y ∈ O, sv y ∈ O := fun y hy => (mem_lat v _).2 fun i => OE_sig v ((mem_lat v y).1 hy i)
  have hsvsv : ∀ y, sv (sv y) = y := fun y => funext fun i => sgv_sgv hcm v (y i)
  have hsvM : ∀ (M : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)) y, sv (M *ᵥ y) = M.map sg *ᵥ sv y :=
    fun M y => funext fun i => RingHom.map_mulVec sg M y i
  have hsvadd : ∀ y y', sv (y + y') = sv y + sv y' := fun y y' => funext fun i => map_add sg _ _
  have hsvneg : ∀ y, sv (-y) = -sv y := fun y => funext fun i => map_neg sg _
  have hsvsmul : ∀ (c : v.adicCompletion F ⊗[F] E) y, sv (c • y) = sg c • sv y := fun c y => funext fun i => map_mul sg _ _
  have hkO : ∀ (M : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E)), (∀ i j, M i j ∈ OE E v) → ∀ y ∈ O, M *ᵥ y ∈ O :=
    fun M hM y hy => (mem_lat v _).2 fun i => by
      simp only [Matrix.mulVec, dotProduct]
      exact sum_mem fun j _ => OE_mul v (hM i j) ((mem_lat v y).1 hy j)
  have hk21 : ∀ i j, k.toBlocks₂₁ i j ∈ OE E v := fun i j => hk _ _
  have hk22 : ∀ i j, k.toBlocks₂₂ i j ∈ OE E v := fun i j => hk _ _

  have hβs : β.map sg = -(sg η • h) := by
    ext a b
    simp [hβ, Matrix.transpose_apply, hh]
  have hD1 : ∀ y, D *ᵥ (k.toBlocks₂₁ *ᵥ y) = e • (t *ᵥ y) := fun y => by
    rw [Matrix.mulVec_mulVec, ← h1, Matrix.smul_mulVec]
  have hD2 : ∀ y, D *ᵥ (k.toBlocks₂₂ *ᵥ y) = e • (β *ᵥ (u *ᵥ y)) := fun y => by
    rw [Matrix.mulVec_mulVec, ← h2, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have hηu : (η • u).map sg = sg η • u.map sg := by
    ext a b; simp

  set X : Set (Fin n → v.adicCompletion F ⊗[F] E) :=
    {x | ∃ y ∈ latM v (t.map sg), ∃ y' ∈ latM v ((η • u).map sg), x = y + h *ᵥ y'} with hX
  have hset : (fun x => (sg e • (1 : Matrix (Fin n) (Fin n) _)) *ᵥ x) '' X = sv '' ((fun y => D *ᵥ y) '' O) := by
    ext w
    constructor
    · rintro ⟨x, ⟨y, hy, y', hy', rfl⟩, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hy
      obtain ⟨b, hb, rfl⟩ := hy'
      refine ⟨D *ᵥ (k.toBlocks₂₁ *ᵥ sv a + k.toBlocks₂₂ *ᵥ (-sv b)), ⟨_, add_mem (hkO _ hk21 _ (hsvO _ ha))
        (hkO _ hk22 _ (neg_mem (hsvO _ hb))), rfl⟩, ?_⟩
      simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply]
      rw [Matrix.mulVec_add, hD1, hD2, hsvadd, hsvsmul, hsvsmul, hsvM, hsvM, hsvM, hsvsv, hβs, hsvneg, hsvsv,
        Matrix.smul_mulVec, Matrix.one_mulVec, hηu]
      simp only [Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg, Matrix.smul_mulVec, Matrix.mulVec_smul,
        smul_add, smul_neg]
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨y₁, y₂, hy₁, hy₂, hyz⟩ := bottom_onto (OEsub E v) k k' hkk hk hk' z ((mem_lat v z).1 hz)
      refine ⟨t.map sg *ᵥ sv y₁ + h *ᵥ ((η • u).map sg *ᵥ (-sv y₂)),
        ⟨_, ⟨sv y₁, hsvO _ ((mem_lat v _).2 hy₁), rfl⟩, _, ⟨-sv y₂, neg_mem (hsvO _ ((mem_lat v _).2 hy₂)), rfl⟩, rfl⟩, ?_⟩
      dsimp only
      rw [← hyz, Matrix.mulVec_add D, hD1, hD2, hsvadd, hsvsmul, hsvsmul, hsvM, hsvM, hsvM, hβs, hηu]
      simp only [Matrix.mulVec_add, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, Matrix.mulVec_neg,
        Matrix.mulVec_smul, smul_add, smul_neg, neg_neg, Matrix.mulVec_mulVec, Matrix.mul_smul, Matrix.smul_mul]
      rw [Matrix.one_mul, Matrix.one_mul, Matrix.neg_mul, Matrix.smul_mul, Matrix.neg_mulVec, smul_neg,
        smul_comm (sg η) (sg e)]
      simp only [Matrix.smul_mulVec]
  have hsc : IsUnit ((sg e • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))).det) := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact (he.map sg).pow _
  have hnsc : ‖Algebra.norm (v.adicCompletion F) ((sg e • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))).det)‖₊
      = 1 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, map_pow, norm_sig, nnnorm_pow]
    have : ‖Algebra.norm (v.adicCompletion F) e‖₊ = 1 := by ext; simpa using he1
    rw [this, one_pow]
  have hvX : lam X = ((‖Algebra.norm (v.adicCompletion F) D.det‖₊ : ℝ≥0) : ℝ≥0∞) * lam O := by
    have e1 := vol_image_mulVec' v lam (sg e • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F ⊗[F] E))) hsc X
    rw [hset, vol_sig hcm v lam, vol_image_mulVec' v lam D hD O, hnsc, ENNReal.coe_one, one_mul] at e1
    exact e1.symm
  have hdet : (t.map sg).det = sg t.det := (RingHom.map_det sg t).symm
  have htu' : IsUnit (t.map sg).det := by rw [hdet]; exact ht.map sg
  have hvL1 : lam (latM v (t.map sg) : Set (Fin n → v.adicCompletion F ⊗[F] E)) =
      ((‖Algebra.norm (v.adicCompletion F) t.det‖₊ : ℝ≥0) : ℝ≥0∞) * lam O := by
    have e2 := vol_image_mulVec' v lam (t.map sg) htu' O
    rw [hdet, norm_sig] at e2
    rw [← e2]
    rfl
  obtain ⟨hO0, hOT⟩ := lat_vol (E := E) v lam
  have hnt : (‖Algebra.norm (v.adicCompletion F) t.det‖₊ : ℝ≥0∞) ≠ 0 := by
    have : Algebra.norm (v.adicCompletion F) t.det ≠ 0 := (ht.map (Algebra.norm (v.adicCompletion F))).ne_zero
    simpa using this
  show _ = _ * (lam X / lam (latM v (t.map sg) : Set (Fin n → v.adicCompletion F ⊗[F] E))).toReal
  rw [hvX, hvL1, ENNReal.mul_div_mul_right _ _ hO0 hOT, ENNReal.toReal_div, ENNReal.coe_toReal, ENNReal.coe_toReal,
    coe_nnnorm, coe_nnnorm]
  have : ‖Algebra.norm (v.adicCompletion F) t.det‖ ≠ 0 := by simpa using hnt
  field_simp

end PositivityTheory.SiegelWeilFormula.HeightDict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetSqNormEqHermitianBlockFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetSqNormEqHermitianBlockFormula
open Matrix

namespace GlobalTheory.CompanionTheory.KWhit

theorem norm_det_bottom_block_sq :
    ∀ {n : Type} [Fintype n] [DecidableEq n] (t u D K₁ K₂ β h g : Matrix n n ℂ) (e η : ℂ),
      ‖e‖ = 1 → η ≠ 0 → K₁ * K₁ᴴ + K₂ * K₂ᴴ = 1 → e • t = D * K₁ → e • (β * u) = D * K₂ →
      tᴴ * u = 1 → hᴴ = h → β = -(η • hᵀ) →
      g * uᴴ = ((‖η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1 → IsUnit g.det →
      ‖D.det‖ ^ 2 = ‖t.det‖ ^ 2 *
        (1 + (g⁻¹ * h.map star * g⁻¹ᴴ) * (g⁻¹ * h.map star * g⁻¹ᴴ)).det.re := by
  intro n _ _ t u D K₁ K₂ β h g e η he hη hK h1 h2 htu hh hβ hg hgdet
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ‖η‖ ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  rw [← hsdef] at hg
  obtain ⟨M, hM⟩ : ∃ M : Matrix n n ℂ, M = g⁻¹ * h.map star * g⁻¹ᴴ := ⟨_, rfl⟩
  rw [← hM]
  have hn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  have hss : s * s = ‖η‖ ^ (-1 : ℝ) := by
    rw [hsdef, ← Real.rpow_add hn]
    norm_num
  have hs : s * s * ‖η‖ = 1 := by
    rw [hss, Real.rpow_neg_one, inv_mul_cancel₀ hn.ne']
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs
    simp at hs
  have hinv : s⁻¹ = s * ‖η‖ := inv_eq_of_mul_eq_one_right (by linear_combination hs)
  have nsq : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    intro z
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.mul_conj z).symm
  have hsstar : star (s : ℂ) = s := by
    exact Complex.conj_ofReal s
  have hsinvstar : star ((s : ℂ)⁻¹) = (s : ℂ)⁻¹ := by
    rw [star_inv₀, hsstar]
  have hee : e * star e = 1 := by
    rw [← nsq e, he]
    norm_num
  have hee' : star e * e = 1 := by rw [mul_comm]; exact hee
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hsa : star (-(η * (s : ℂ))) = -(star η * (s : ℂ)) := by
    rw [star_neg, star_mul', hsstar]
  have ha : -(η * (s : ℂ)) * star (-(η * (s : ℂ))) = (s : ℂ)⁻¹ * (s : ℂ)⁻¹ := by
    rw [hsa]
    have e1 : -(η * (s : ℂ)) * -(star η * (s : ℂ)) = (η * star η) * ((s : ℂ) * (s : ℂ)) := by
      ring
    rw [e1, ← nsq η]
    have e2 : ‖η‖ ^ 2 * (s * s) = s⁻¹ * s⁻¹ := by
      rw [hinv]
      ring
    have e3 : ((‖η‖ ^ 2 : ℝ) : ℂ) * ((s : ℂ) * (s : ℂ)) = ((‖η‖ ^ 2 * (s * s) : ℝ) : ℂ) := by
      first | (push_cast; ring) | push_cast | simp
    rw [e3, e2]
    first | (push_cast; ring) | push_cast | simp
  have ha' : star (-(η * (s : ℂ))) * -(η * (s : ℂ)) = (s : ℂ)⁻¹ * (s : ℂ)⁻¹ := by
    rw [mul_comm]; exact ha
  have hs_ij : ∀ i j, star (h i j) = h j i := by
    intro i j
    have hx := congrArg (fun X : Matrix n n ℂ => X j i) hh
    simp only [Matrix.conjTranspose_apply] at hx
    exact hx
  have hT : h.map star = hᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply]
    exact hs_ij i j
  have hTH : hᵀᴴ = hᵀ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    exact hs_ij i j
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgdet
  have hgg' : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hgdet
  have hMH : Mᴴ = M := by
    rw [hM, hT, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hTH, mul_assoc]
  have hgM : g * M = hᵀ * g⁻¹ᴴ := by
    rw [hM, hT, ← mul_assoc, ← mul_assoc, hgg, one_mul]
  have hut : uᴴ * t = 1 := by
    have hx := congrArg Matrix.conjTranspose htu
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] at hx
  have huH : uᴴ = (s : ℂ) • g⁻¹ := by
    calc uᴴ = g⁻¹ * (g * uᴴ) := by rw [← mul_assoc, hgg', one_mul]
      _ = (s : ℂ) • g⁻¹ := by rw [hg, mul_smul_comm, mul_one]
  have hu : u = (s : ℂ) • g⁻¹ᴴ := by
    calc u = uᴴᴴ := (Matrix.conjTranspose_conjTranspose u).symm
      _ = (s : ℂ) • g⁻¹ᴴ := by rw [huH, Matrix.conjTranspose_smul, hsstar]
  have ht : t = (s : ℂ)⁻¹ • g := by
    have h3 : (s : ℂ) • t = g := by
      calc (s : ℂ) • t = ((s : ℂ) • (1 : Matrix n n ℂ)) * t := by rw [smul_mul_assoc, one_mul]
        _ = g * uᴴ * t := by rw [hg]
        _ = g := by rw [mul_assoc, hut, mul_one]
    rw [← h3, smul_smul, inv_mul_cancel₀ hsC, one_smul]
  have hβu : β * u = (-(η * (s : ℂ))) • (g * M) := by
    rw [hβ, hu, hgM, neg_mul, smul_mul_assoc, mul_smul_comm, smul_smul, neg_smul]
  have hDD : D * Dᴴ = t * tᴴ + (β * u) * (β * u)ᴴ := by
    have step1 : D * Dᴴ = (D * K₁) * (D * K₁)ᴴ + (D * K₂) * (D * K₂)ᴴ := by
      calc D * Dᴴ = D * (K₁ * K₁ᴴ + K₂ * K₂ᴴ) * Dᴴ := by rw [hK, mul_one]
        _ = (D * K₁) * (D * K₁)ᴴ + (D * K₂) * (D * K₂)ᴴ := by
          simp only [Matrix.conjTranspose_mul, mul_add, add_mul, mul_assoc]
    rw [step1, ← h1, ← h2]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hee', one_smul]
  have hmain : D * Dᴴ = ((s : ℂ)⁻¹ * (s : ℂ)⁻¹) • (g * (1 + M * M) * gᴴ) := by
    rw [hDD, ht, hβu]
    simp only [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hsinvstar, ha']
    rw [← smul_add]
    congr 1
    simp only [Matrix.conjTranspose_mul, hMH, mul_add, add_mul, mul_one, mul_assoc]
  have hdet : D.det * star D.det = t.det * star t.det * (1 + M * M).det := by
    have lhs : D.det * star D.det = (D * Dᴴ).det := by
      rw [Matrix.det_mul, Matrix.det_conjTranspose]
    rw [lhs, hmain, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
      ht, Matrix.det_smul, star_mul', star_pow, hsinvstar]
    ring
  rw [← nsq, ← nsq] at hdet
  have hre := congrArg Complex.re hdet
  first
    | (rw [Complex.ofReal_re, Complex.re_ofReal_mul] at hre; exact hre)
    | (simpa [Complex.mul_re] using hre)

end GlobalTheory.CompanionTheory.KWhit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetSqNormEqHermitianBlockFormulaStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_sq_norm_eq_hermitian_block_formula : ∀ {n : Type} [Fintype n] [DecidableEq n] (t u D K₁ K₂ β h g : Matrix n n ℂ) (e η : ℂ), ‖e‖ = 1 → η ≠ 0 → K₁ * K₁ᴴ + K₂ * K₂ᴴ = 1 → e • t = D * K₁ → e • (β * u) = D * K₂ → tᴴ * u = 1 → hᴴ = h → β = -(η • hᵀ) → g * uᴴ = ((‖η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1 → IsUnit g.det → ‖D.det‖ ^ 2 = ‖t.det‖ ^ 2 * (1 + (g⁻¹ * h.map star * g⁻¹ᴴ) * (g⁻¹ * h.map star * g⁻¹ᴴ)).det.re := by
  first | exact @GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq | exact GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq | (intros; apply GlobalTheory.CompanionTheory.KWhit.norm_det_bottom_block_sq <;> assumption)
end
end

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit.Ht

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev sgv (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F ⊗[F] E →+* v.adicCompletion F ⊗[F] E :=
  HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ

def L1 (σ : E →ₐ[F] E) {n : ℕ} (t : GL (Fin n) (AE F E)) (v : HeightOneSpectrum (𝓞 F)) :
    AddSubgroup (Fin n → v.adicCompletion F ⊗[F] E) :=
  latM v ((t.1.map (compFin F E v)).map (sgv σ v))

def L2 (σ : E →ₐ[F] E) {n : ℕ} (u : GL (Fin n) (AE F E)) (η : E) (v : HeightOneSpectrum (𝓞 F)) :
    AddSubgroup (Fin n → v.adicCompletion F ⊗[F] E) :=
  latM v (((inclR (F := F) (v.adicCompletion F) η) • u.1.map (compFin F E v)).map (sgv σ v))

theorem det_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) : (M.map f).det = f M.det := (RingHom.map_det f M).symm

theorem compFin_smul (v : HeightOneSpectrum (𝓞 F)) (a : AF F) (z : AE F E) :
    compFin F E v (a • z) = evFin F v a • compFin F E v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b e => simp [compFin, TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, map_mul]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem compFin_inclR (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    compFin F E v (inclR (F := F) (AF F) e) = inclR (F := F) (v.adicCompletion F) e := by
  simp [compFin, inclR, Algebra.TensorProduct.map_tmul]

theorem compFin_cA (v : HeightOneSpectrum (𝓞 F)) (z : AE F E) : compFin F E v (cA σ z) = sgv σ v (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b e => simp [compFin, cA, HeckeCharacterZeroLocus.SiegelWeilU.sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem compFin_sigR (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    compFin F E v (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ z) = sgv σ v (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b e => simp [compFin, HeckeCharacterZeroLocus.SiegelWeilU.sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem evFin_finOne (v : HeightOneSpectrum (𝓞 F)) : evFin F v (finOne F) = 1 := by
  simp only [evFin, finOne, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA, LinearMap.inr_apply]
  exact map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)

theorem compFin_intHat (v : HeightOneSpectrum (𝓞 F)) {z : AE F E} (hz : z ∈ intHat F E) : compFin F E v z ∈ OE E v := by
  have hle : intHat F E ≤ (OE E v).comap (compFin F E v).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, -, ha, o, rfl⟩
    show compFin F E v (a • inclR (F := F) (AF F) (o : E)) ∈ OE E v
    rw [compFin_smul, compFin_inclR]
    refine AddSubgroup.subset_closure ⟨evFin F v a, ha v, o, ?_⟩
    simp [inclR, TensorProduct.smul_tmul']
  exact hle hz

theorem k_int (d : SD σ) {k : d.G} (hk : k ∈ d.K) (v : HeightOneSpectrum (𝓞 F)) (i j : Fin d.n ⊕ Fin d.n) :
    compFin F E v (inFrame d.b k i j) ∈ OE E v ∧ compFin F E v (inFrame d.b k⁻¹ i j) ∈ OE E v := by
  have h := ((d.ok.stdK k).1 hk).2
  have e : ∀ z : AE F E, compFin F E v (finOne F • z) = compFin F E v z := fun z => by
    rw [compFin_smul, evFin_finOne, one_smul]
  exact ⟨e _ ▸ compFin_intHat v (h k (by simp) i j), e _ ▸ compFin_intHat v (h k⁻¹ (by simp) i j)⟩

theorem k_unit (d : SD σ) {k : d.G} (hk : k ∈ d.K) (w : InfinitePlace F) :
    (inFrame d.b k).map (piInf (d.B.emb w)) * ((inFrame d.b k).map (piInf (d.B.emb w)))ᴴ = 1 :=
  ((d.ok.stdK k).1 hk).1 w

theorem inFrame_mul_inv (d : SD σ) (k : d.G) : inFrame d.b k * inFrame d.b k⁻¹ = 1 := by
  rw [← inFrame_mul, mul_inv_cancel]
  simp only [inFrame, mat2, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]
  exact incM_inv_mul d

theorem compInf_cA (w : InfinitePlace F) (z : AE F E) :
    compInf F E w (cA σ z) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b e => simp [compInf, cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem piInf_cA (d : SD σ) (w : InfinitePlace F) (z : AE F E) :
    piInf (d.B.emb w) (cA σ z) = star (piInf (d.B.emb w) z) := by
  simp only [piInf, RingHom.comp_apply, compInf_cA]
  exact (GlobalTheory.AdelicU.infEmb_sigR d.ok.good.cm (d.B.emb w) _).symm

theorem sigR_eq_cA' (z : AF F ⊗[F] E) : HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ z = cA σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [HeckeCharacterZeroLocus.SiegelWeilU.sigR, cA, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem piInf_inclR (d : SD σ) (w : InfinitePlace F) (e : E) :
    piInf (d.B.emb w) (inclR (F := F) (AF F) e) = (d.B.emb w).1 e := by
  simp [piInf, compInf, inclR, Algebra.TensorProduct.map_tmul, infEmb_tmul]

theorem real_at (d : SD σ) (R : RD d) {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hR : Rel d R x t u T η T₀ hOf θ fr g) (ε : ℤˣ) (β : nA σ d.Y d.b)
    (D : GL (Fin d.n) (AE F E)) {k : d.G} (hk : k ∈ d.K)
    (h1 : ((ε : ℤ) : AE F E) • t.1 = D.1 * (inFrame d.b k).toBlocks₂₁)
    (h2 : ((ε : ℤ) : AE F E) • (β.1 * u.1) = D.1 * (inFrame d.b k).toBlocks₂₂) (w : InfinitePlace F) :
    ‖piInf (d.B.emb w) D.1.det‖ ^ 2 = ‖piInf (d.B.emb w) t.1.det‖ ^ 2 *
      (1 + (((g w)⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w) * (((g w)⁻¹).1)ᴴ) *
        (((g w)⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w) * (((g w)⁻¹).1)ᴴ)).det.re := by
  set pw := piInf (d.B.emb w) with hpw
  have hmap : ∀ {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)),
      (X * Y).map pw = X.map pw * Y.map pw := fun X Y => Matrix.map_mul
  have hsm : ∀ {a b : Type} (c : AE F E) (X : Matrix a b (AE F E)), (c • X).map pw = pw c • X.map pw := by
    intro a b c X; ext i j; simp
  have hθ : (Gen.matInf (hOf β).1).map (θ w) = ((hOf β).1.map pw).map star := by
    ext i j
    exact hR.th w _
  have hK : ((inFrame d.b k).map pw).toBlocks₂₁ * (((inFrame d.b k).map pw).toBlocks₂₁)ᴴ +
      ((inFrame d.b k).map pw).toBlocks₂₂ * (((inFrame d.b k).map pw).toBlocks₂₂)ᴴ = 1 := by
    have hu := k_unit d hk w
    ext i j
    have := congrFun (congrFun hu (Sum.inr i)) (Sum.inr j)
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.conjTranspose_apply, Matrix.one_apply,
      Sum.inr.injEq] at this
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.add_apply] using this
  have h1' := congrArg (fun M => M.map pw) h1
  have h2' := congrArg (fun M => M.map pw) h2
  simp only [hsm, hmap, map_intCast] at h1' h2'
  have htu : (t.1.map pw)ᴴ * u.1.map pw = 1 := by
    have h0 := congrArg (fun M => M.map pw) (levi_tu d x t u hR.levi)
    simp only [hmap, Matrix.map_one _ (map_zero pw) (map_one pw)] at h0
    have h3 : ((t.1ᵀ.map pw) * ((u.1.map (cA σ)).map pw)).map (starRingEnd ℂ) =
        (1 : Matrix (Fin d.n) (Fin d.n) ℂ).map (starRingEnd ℂ) := by rw [h0]
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h3
    have e1 : ((u.1.map (cA σ)).map pw).map (starRingEnd ℂ) = u.1.map pw := by
      ext i j
      simp only [Matrix.map_apply]
      rw [hpw, piInf_cA]
      simp
    rw [e1] at h3
    rw [← h3]
    rfl
  have hh : ((hOf β).1.map pw)ᴴ = (hOf β).1.map pw := by
    ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← (hOf β).2 a b, sigR_eq_cA', piInf_cA]
  have hβ : β.1.map pw = -(((d.B.emb w).1 η) • ((hOf β).1.map pw)ᵀ) := by
    rw [hR.hof β]
    ext i j
    simp [Matrix.map_apply, Matrix.mul_apply, Matrix.scalar_apply, incM, Matrix.diagonal_apply, hpw, piInf_inclR]
  have hg : (g w).1 * (u.1.map pw)ᴴ = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1 := hR.gc w
  have he : ‖(((ε : ℤ) : ℂ))‖ = 1 := by rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hη : (d.B.emb w).1 η ≠ 0 := (map_ne_zero _).2 hR.ne
  have hgi : IsUnit (g w).1.det := (Matrix.isUnit_iff_isUnit_det _).1 (g w).isUnit
  have key := GlobalTheory.T.det_sq_norm_eq_hermitian_block_formula (t.1.map pw) (u.1.map pw) (D.1.map pw) ((inFrame d.b k).map pw).toBlocks₂₁
    ((inFrame d.b k).map pw).toBlocks₂₂ (β.1.map pw) ((hOf β).1.map pw) (g w).1 ((ε : ℤ) : ℂ) ((d.B.emb w).1 η)
    he hη hK h1' h2' htu hh hβ hg hgi
  rw [det_map, det_map] at key
  rw [hθ, Matrix.coe_units_inv]
  exact key

theorem fin_at (d : SD σ) (R : RD d) {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hR : Rel d R x t u T η T₀ hOf θ fr g) (ε : ℤˣ) (β : nA σ d.Y d.b)
    (D : GL (Fin d.n) (AE F E)) {k : d.G} (hk : k ∈ d.K)
    (h1 : ((ε : ℤ) : AE F E) • t.1 = D.1 * (inFrame d.b k).toBlocks₂₁)
    (h2 : ((ε : ℤ) : AE F E) • (β.1 * u.1) = D.1 * (inFrame d.b k).toBlocks₂₂) (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) [lam.IsAddHaarMeasure] :
    ‖Algebra.norm (v.adicCompletion F) (compFin F E v D.1.det)‖ =
      ‖Algebra.norm (v.adicCompletion F) (compFin F E v t.1.det)‖ *
        Gen.nu2 lam (L1 σ t v) (L2 σ u η v) (Gen.matV v (hOf β).1) := by
  set cf := compFin F E v with hcf
  have hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ := d.ok.good.cm
  have hmap : ∀ {a b c : Type} [Fintype b] (X : Matrix a b (AE F E)) (Y : Matrix b c (AE F E)),
      (X * Y).map cf = X.map cf * Y.map cf := fun X Y => Matrix.map_mul
  have hsm : ∀ {a b : Type} (c : AE F E) (X : Matrix a b (AE F E)), (c • X).map cf = cf c • X.map cf := by
    intro a b c X; ext i j; simp
  have ht : IsUnit (t.1.map cf).det := by
    rw [det_map]; exact (Matrix.GeneralLinearGroup.det t).isUnit.map cf
  have hD : IsUnit (D.1.map cf).det := by
    rw [det_map]; exact (Matrix.GeneralLinearGroup.det D).isUnit.map cf
  have htu : (t.1.map cf)ᵀ * (u.1.map cf).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
    have h0 := congrArg (fun M => M.map cf) (levi_tu d x t u hR.levi)
    simp only [hmap, Matrix.map_one _ (map_zero cf) (map_one cf)] at h0
    rw [← h0, Matrix.transpose_map]
    congr 1
    ext i j
    exact (compFin_cA v _).symm
  have hη : IsUnit (inclR (F := F) (v.adicCompletion F) η) := (Ne.isUnit hR.ne).map _
  have he : IsUnit (((ε : ℤ) : v.adicCompletion F ⊗[F] E)) := ε.isUnit.map (Int.castRingHom _)
  have he1 : ‖Algebra.norm (v.adicCompletion F) (((ε : ℤ) : v.adicCompletion F ⊗[F] E))‖ = 1 := by
    rcases Int.units_eq_one_or ε with h | h
    · simp [h]
    · have : (((ε : ℤ) : v.adicCompletion F ⊗[F] E)) = algebraMap (v.adicCompletion F) _ (-1) := by
        rw [h]; simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, map_neg, map_one]
      rw [this, Algebra.norm_algebraMap, norm_pow, norm_neg, norm_one, one_pow]
  have hβ : β.1.map cf = -((inclR (F := F) (v.adicCompletion F) η) • ((hOf β).1.map cf)ᵀ) := by
    rw [hR.hof β]
    ext i j
    simp [Matrix.map_apply, Matrix.mul_apply, Matrix.scalar_apply, incM, Matrix.diagonal_apply, hcf,
      compFin_inclR]
  have hh : ∀ a b, HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ (((hOf β).1.map cf) b a) = ((hOf β).1.map cf) a b := by
    intro a b
    simp only [Matrix.map_apply]
    rw [← (hOf β).2 a b]
    exact (compFin_sigR v _).symm
  have hkk : (inFrame d.b k).map cf * (inFrame d.b k⁻¹).map cf = 1 := by
    rw [← hmap, inFrame_mul_inv, Matrix.map_one _ (map_zero cf) (map_one cf)]
  have h1' := congrArg (fun M => M.map cf) h1
  have h2' := congrArg (fun M => M.map cf) h2
  simp only [hsm, hmap, map_intCast] at h1' h2'
  have key := PositivityTheory.SiegelWeilFormula.HeightDict.fin_index hcm v d.n (t.1.map cf) (u.1.map cf) (D.1.map cf) (β.1.map cf) ((hOf β).1.map cf)
    (inclR (F := F) (v.adicCompletion F) η) (((ε : ℤ) : v.adicCompletion F ⊗[F] E))
    ((inFrame d.b k).map cf) ((inFrame d.b k⁻¹).map cf) ht hD htu hη he he1 hβ hh hkk
    (fun i j => (k_int d hk v i j).1) (fun i j => (k_int d hk v i j).2) h1' h2' lam
  rw [det_map, det_map] at key
  exact key

theorem exists_haar_tup (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ∃ lv : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E), lv.IsAddHaarMeasure :=
  PositivityTheory.SiegelWeilFormula.HeightDict.exists_haar_tup v n

theorem normV_eq (x : (AE F E)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖Algebra.norm (v.adicCompletion F) (compFin F E v x.1)‖ =
      ((GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v x) : ℝ≥0) : ℝ) := by
  rw [GlobalTheory.Doubling.absEv_unitFin, coe_nnnorm]
  exact congrArg norm (GlobalTheory.Doubling.norm_map (GlobalTheory.AdelicU.evFin F v) x.1)

theorem fin_supp (x : (AE F E)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖Algebra.norm (v.adicCompletion F) (compFin F E v x.1)‖).Finite := by
  refine (GlobalTheory.Doubling.finite_mulSupport_absEv x).subset fun v hv => ?_
  simp only [Function.mem_mulSupport, normV_eq] at hv ⊢
  exact fun h => hv (by rw [h, NNReal.coe_one])

theorem absE_pos (x : (AE F E)ˣ) : (0 : ℝ) < ((GlobalTheory.Doubling.absE F E x : ℝ≥0) : ℝ) := by
  have h := map_mul (GlobalTheory.Doubling.absE F E) x x⁻¹
  rw [mul_inv_cancel, map_one] at h
  rcases eq_or_ne (GlobalTheory.Doubling.absE F E x) 0 with h0 | h0
  · rw [h0, zero_mul] at h; exact absurd h one_ne_zero
  · exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)

theorem normV_ne (x : (AE F E)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖Algebra.norm (v.adicCompletion F) (compFin F E v x.1)‖ ≠ 0 := by
  rw [normV_eq]
  have h := map_mul (GlobalTheory.Doubling.absEv F E v) (GlobalTheory.Doubling.unitFin F E v x) (GlobalTheory.Doubling.unitFin F E v x)⁻¹
  rw [mul_inv_cancel, map_one] at h
  intro h0
  rw [NNReal.coe_eq_zero] at h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h

theorem absE_split (d : SD σ) (x : (AE F E)ˣ) :
    ((GlobalTheory.Doubling.absE F E x : ℝ≥0) : ℝ) =
      (∏ w, ‖piInf (d.B.emb w) x.1‖ ^ 2) * ∏ᶠ v, ‖Algebra.norm (v.adicCompletion F) (compFin F E v x.1)‖ := by
  rw [GlobalTheory.Doubling.absE_apply, NNReal.coe_mul, NNReal.coe_prod]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [GlobalTheory.Doubling.absEw_eq_sq d.ok.good.cm (d.B.emb w), NNReal.coe_pow, coe_nnnorm]
    rfl
  · set s := (GlobalTheory.Doubling.finite_mulSupport_absEv x).toFinset with hs
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := s) (by simp [s]), NNReal.coe_prod,
      finprod_eq_prod_of_mulSupport_subset _ (s := s) ?_]
    · exact Finset.prod_congr rfl fun v _ => (normV_eq x v).symm
    · intro v hv
      simp only [Set.Finite.coe_toFinset, s, Function.mem_mulSupport] at hv ⊢
      rw [normV_eq] at hv
      exact fun h => hv (by rw [h, NNReal.coe_one])

theorem heightDict : HeightDict := by
  intro F E _ _ _ _ _ σ d R x t u T η T₀ hOf θ fr g hR nb lam 𝓖 hc ε w hw
  choose lv hlv using fun v : HeightOneSpectrum (𝓞 F) => exists_haar_tup (E := E) v d.n
  have hfin :
        (∀ v : HeightOneSpectrum (𝓞 F),
          Gen.IsCO (latM v ((t.1.map (GlobalTheory.AdelicU.compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ))) ∧
          Gen.IsCO (latM v (((inclR (F := F) (v.adicCompletion F) η) • u.1.map (GlobalTheory.AdelicU.compFin F E v)).map
            (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)))) ∧
        ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
          ((latM v ((t.1.map (GlobalTheory.AdelicU.compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)) :
            Set (Fin d.n → v.adicCompletion F ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v) ∧
          ((latM v (((inclR (F := F) (v.adicCompletion F) η) • u.1.map (GlobalTheory.AdelicU.compFin F E v)).map
            (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)) : Set (Fin d.n → v.adicCompletion F ⊗[F] E)) =
              PositivityTheory.PfSWUS.Loc.latO d.bs v)
    := by
    open PositivityTheory.SiegelWeilFormula.HeightDict in
      classical
      have hinv1 : ∀ v : HeightOneSpectrum (𝓞 F),
          (t.1.map (compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) *
            ((t⁻¹ : GL (Fin d.n) (AE F E)).1.map (compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
        intro v
        have h := congrArg (fun M => (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ).mapMatrix
          ((compFin F E v).mapMatrix M)) (Units.mul_inv t)
        simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
      have hinv2 : ∀ v : HeightOneSpectrum (𝓞 F),
          ((inclR (F := F) (v.adicCompletion F) η) • u.1.map (compFin F E v)).map
              (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) *
            ((inclR (F := F) (v.adicCompletion F) η⁻¹) • (u⁻¹ : GL (Fin d.n) (AE F E)).1.map (compFin F E v)).map
              (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
        intro v
        have hu : u.1.map (compFin F E v) * (u⁻¹ : GL (Fin d.n) (AE F E)).1.map (compFin F E v) = 1 := by
          have h := congrArg (fun M => (compFin F E v).mapMatrix M) (Units.mul_inv u)
          simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
        have hc : inclR (F := F) (v.adicCompletion F) η * inclR (F := F) (v.adicCompletion F) η⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel₀ hR.ne, map_one]
        have h2 : (inclR (F := F) (v.adicCompletion F) η • u.1.map (compFin F E v)) *
            (inclR (F := F) (v.adicCompletion F) η⁻¹ • (u⁻¹ : GL (Fin d.n) (AE F E)).1.map (compFin F E v)) = 1 := by
          rw [Matrix.smul_mul, Matrix.mul_smul, hu, smul_smul, hc, one_smul]
        have h := congrArg (fun M => (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ).mapMatrix M) h2
        simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
      refine ⟨fun v => ⟨latM_isCO v _ (Matrix.isUnit_det_of_right_inverse (hinv1 v)),
        latM_isCO v _ (Matrix.isUnit_det_of_right_inverse (hinv2 v))⟩, ?_⟩
      have ent : ∀ M : Matrix (Fin d.n) (Fin d.n) (AE F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
          ∀ i j, compFin F E v (M i j) ∈ OE E v := fun M =>
        Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_OE (M i j)
      filter_upwards [ent t.1, ent (t⁻¹ : GL (Fin d.n) (AE F E)).1, ent u.1, ent (u⁻¹ : GL (Fin d.n) (AE F E)).1,
        ev_inclR (F := F) η, ev_inclR (F := F) η⁻¹, ev_lat_latO d.bs d.n] with v ht ht' hu hu' he he' hl
      refine ⟨?_, ?_⟩
      · rw [latM_eq_lat v _ _ (hinv1 v) (fun i j => OE_sig v (ht i j)) (fun i j => OE_sig v (ht' i j)), hl]
      · rw [latM_eq_lat v _ _ (hinv2 v) (fun i j => OE_sig v (OE_mul v he (hu i j)))
          (fun i j => OE_sig v (OE_mul v he' (hu' i j))), hl]
  obtain ⟨hCO, hstd⟩ := hfin
  have hat : (0 : ℝ) < ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ≥0) : ℝ) :=
    absE_pos _
  refine ⟨lv, L1 σ t, L2 σ u η, ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ≥0) : ℝ)⁻¹,
    inv_pos.2 hat, hlv, hCO, hstd, fun β => ?_⟩
  obtain ⟨D, k, hk, ha, hb1, hb2⟩ := frame_iwa d (w * nb β * x)
  obtain ⟨hr1, hr2⟩ := bottom_rows d x t u hR.levi nb hc.1 ε w hw β
  have h1 := hr1.symm.trans hb1
  have h2 := hr2.symm.trans hb2
  have hre := fun w' => real_at d R hR ε β D hk h1 h2 w'
  have hfi := fun v => fin_at d R hR ε β D hk h1 h2 v (lv v)
  set X : InfinitePlace F → ℝ := fun w' => (1 + (((g w')⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w') * (((g w')⁻¹).1)ᴴ) *
        (((g w')⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w') * (((g w')⁻¹).1)ᴴ)).det.re with hX
  set N : HeightOneSpectrum (𝓞 F) → ℝ := fun v => Gen.nu2 (lv v) (L1 σ t v) (L2 σ u η v) (Gen.matV v (hOf β).1)
    with hN
  have hnuA : Gen.nuA θ g lv (L1 σ t) (L2 σ u η) (hOf β).1 = (∏ w', X w') * ∏ᶠ v, N v := rfl
  have hsD := absE_split d (Matrix.GeneralLinearGroup.det D)
  have hsT := absE_split d (Matrix.GeneralLinearGroup.det t)
  simp only [Matrix.GeneralLinearGroup.val_det_apply] at hsD hsT
  have hfT := fin_supp (Matrix.GeneralLinearGroup.det t)
  have hfD := fin_supp (Matrix.GeneralLinearGroup.det D)
  simp only [Matrix.GeneralLinearGroup.val_det_apply] at hfT hfD
  have hT0 := normV_ne (Matrix.GeneralLinearGroup.det t)
  simp only [Matrix.GeneralLinearGroup.val_det_apply] at hT0
  have hNv : ∀ v, N v = ‖Algebra.norm (v.adicCompletion F) (compFin F E v D.1.det)‖ /
      ‖Algebra.norm (v.adicCompletion F) (compFin F E v t.1.det)‖ := fun v => by
    rw [hfi v, mul_div_cancel_left₀ _ (hT0 v)]
  have hNs : (Function.mulSupport N).Finite := by
    refine (hfD.union hfT).subset fun v hv => ?_
    by_contra hc'
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hc'
    exact hv (by rw [hNv v, hc'.1, hc'.2, div_one])
  have hA : ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det D) : ℝ≥0) : ℝ) =
      ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ≥0) : ℝ) *
        Gen.nuA θ g lv (L1 σ t) (L2 σ u η) (hOf β).1 := by
    rw [hsD, hsT, hnuA, Finset.prod_congr rfl fun w' _ => hre w', Finset.prod_mul_distrib,
      finprod_congr fun v => hfi v, finprod_mul_distrib hfT hNs]
    ring
  have hDpos := absE_pos (Matrix.GeneralLinearGroup.det D)
  refine ⟨?_, ?_⟩
  · rw [hA] at hDpos
    exact pos_of_mul_pos_right hDpos hat.le
  · rw [ha, hA, mul_inv]

end PositivityTheory.SiegelWeilFormula.KWhit.Ht

end
