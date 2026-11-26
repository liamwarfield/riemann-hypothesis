module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualProdIff
public import Development.WeilBound.ThetaLifts.SphericalLattices.LocMod

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.ChartSt
noncomputable section

namespace PositivityTheory.Sph.M2

open scoped Matrix
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas

def ChartSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (r s m : ℕ) (W : Spc F E (m + m)), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (h : w.under (𝓞 F) = v)
    (c : w.adicCompletion E →+* w.adicCompletion E), IsConjAt σ h c →
    ∀ (Cy : Matrix (Fin (m + m)) (Fin m) (AE F E)), IsLagAt σ W v Cy →
    ∃ Φ : UA σ W.J →* GL (Fin m ⊕ Fin m) (w.adicCompletion E),
      (∀ g, Φ g ∈ GW (w.adicCompletion E) c m) ∧
      (∀ g ∈ USub σ W v, ∀ g' ∈ USub σ W v, Φ g = Φ g' → g = g') ∧
      (∀ M ∈ GW (w.adicCompletion E) c m, ∃ g ∈ USub σ W v, Φ g = M) ∧
      (∀ g ∈ USub σ W v, g ∈ KSub σ W v ↔ Φ g ∈ IntGL (w.adicCompletion E) m) ∧
      (∀ g ∈ USub σ W v, g ∈ PositivityTheory.Sph.PSub σ W v Cy ↔ Φ g ∈ PW (w.adicCompletion E) c m) ∧
      ∀ p ∈ PositivityTheory.Sph.PSub σ W v Cy, ∀ t : Matrix (Fin m) (Fin m) (AE F E), mat p * Cy = Cy * t →
        ((Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₁₁).det = piE h t.det

end PositivityTheory.Sph.M2

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.ExistsFrameLag
section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.MemIntGLIff
noncomputable section

namespace PositivityTheory.Sph.M2.Chart

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal PositivityTheory.ThKH.Iwas

section Alg

variable {L : Type} [Field L] {c : L →+* L} {β : Type} [Fintype β] [DecidableEq β]

omit [Fintype β] in
theorem Wm_transpose : (Wm L β)ᵀ = Wm L β := by
  simp [Wm, fromBlocks_transpose]

theorem exists_compl (hc : ∀ x, c (c x) = x) {w : L} (hw : w + c w = 1) {Y : Matrix (β ⊕ β) β L} {R : Matrix β (β ⊕ β) L}
    (hR : R * Y = 1) (hY : Yᵀ * Wm L β * Y.map c = 0) : ∃ X : Matrix (β ⊕ β) β L, Iso c (Wm L β) (Wm L β) (fromCols Y X) := by
  have hcc : ∀ {ι κ : Type} (N : Matrix ι κ L), (N.map c).map c = N := fun N => Matrix.ext fun i j => hc _
  have sym : ∀ A B : Matrix (β ⊕ β) β L, ((Aᵀ * Wm L β * B.map c).map c)ᵀ = Bᵀ * Wm L β * A.map c := fun A B => by
    rw [Matrix.map_mul, Matrix.map_mul, hcc, Wm_map, transpose_mul, transpose_mul, Wm_transpose, Matrix.mul_assoc]
    rfl
  obtain ⟨X₀, h1⟩ : ∃ X₀ : Matrix (β ⊕ β) β L, Yᵀ * Wm L β * X₀.map c = 1 :=
    ⟨(Wm L β * Rᵀ).map c, by
      rw [hcc, Matrix.mul_assoc, ← Matrix.mul_assoc (Wm L β), Wm_mul_self, Matrix.one_mul, ← transpose_mul, hR,
        transpose_one]⟩
  have h2 : X₀ᵀ * Wm L β * Y.map c = 1 := by
    rw [← sym, h1, map_one', transpose_one]
  obtain ⟨H, hH⟩ : ∃ H, X₀ᵀ * Wm L β * X₀.map c = H := ⟨_, rfl⟩
  have h3 : (H.map c)ᵀ = H := by rw [← hH, sym]
  have h4 : ((w • H)ᵀ).map c = c w • H := by
    ext i j
    have : c (H j i) = H i j := congrFun (congrFun h3 i) j
    simp [this]
  have e1 : (X₀ - Y * (w • H)ᵀ).map c = X₀.map c - Y.map c * (c w • H) := by
    rw [Matrix.map_sub _ (map_sub c), Matrix.map_mul, h4]
  have e2 : (X₀ - Y * (w • H)ᵀ)ᵀ * Wm L β = X₀ᵀ * Wm L β - (w • H) * (Yᵀ * Wm L β) := by
    rw [transpose_sub, transpose_mul, transpose_transpose, Matrix.sub_mul, Matrix.mul_assoc]
  have a1 : Yᵀ * Wm L β * (X₀ - Y * (w • H)ᵀ).map c = 1 := by
    rw [e1, Matrix.mul_sub, h1, ← Matrix.mul_assoc, hY, Matrix.zero_mul, sub_zero]
  have a2 : (X₀ - Y * (w • H)ᵀ)ᵀ * Wm L β * Y.map c = 1 := by
    rw [← sym, a1, map_one', transpose_one]
  have a3 : (X₀ - Y * (w • H)ᵀ)ᵀ * Wm L β * (X₀ - Y * (w • H)ᵀ).map c = 0 := by
    rw [e2, Matrix.sub_mul, Matrix.mul_assoc (w • H), a1, e1, Matrix.mul_sub, hH, ← Matrix.mul_assoc, h2, Matrix.one_mul,
      Matrix.mul_one, sub_sub, ← add_smul, add_comm, hw, one_smul, sub_self]
  refine ⟨X₀ - Y * (w • H)ᵀ, ?_⟩
  unfold Iso
  rw [transpose_fromCols, fromCols_map, fromRows_mul, fromRows_mul_fromCols, hY, a1, a2, a3]
  rfl

theorem exists_leftInv {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {Y : Matrix ι κ L}
    (hY : ∀ z, Y *ᵥ z = 0 → z = 0) : ∃ R : Matrix κ ι L, R * Y = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' Y) (LinearMap.ker_eq_bot'.2 hY)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem block_iff {M : Matrix (β ⊕ β) (β ⊕ β) L} {T : Matrix β β L} (hT : IsUnit T.det) :
    (∃ t : Matrix β β L, M * fromRows T (0 : Matrix β β L) = fromRows T (0 : Matrix β β L) * t) ↔ M.toBlocks₂₁ = 0 := by
  rw [← fromBlocks_toBlocks M, fromBlocks_mul_fromRows, toBlocks_fromBlocks₂₁]
  simp only [Matrix.mul_zero, add_zero, fromRows_mul, Matrix.zero_mul, fromRows_ext_iff]
  constructor
  · rintro ⟨t, -, h⟩
    rw [← Matrix.mul_nonsing_inv_cancel_right T M.toBlocks₂₁ hT, h, Matrix.zero_mul]
  · intro h
    exact ⟨T⁻¹ * (M.toBlocks₁₁ * T), (Matrix.mul_nonsing_inv_cancel_left _ _ hT).symm, by rw [h, Matrix.zero_mul]⟩

theorem block_det {M : Matrix (β ⊕ β) (β ⊕ β) L} {T t : Matrix β β L} (hT : IsUnit T.det)
    (h : M * fromRows T (0 : Matrix β β L) = fromRows T (0 : Matrix β β L) * t) : M.toBlocks₁₁.det = t.det := by
  rw [← fromBlocks_toBlocks M, fromBlocks_mul_fromRows] at h
  simp only [Matrix.mul_zero, add_zero, fromRows_mul, Matrix.zero_mul, fromRows_ext_iff] at h
  have := congrArg det h.1
  rw [det_mul, det_mul, mul_comm] at this
  exact mul_left_cancel₀ hT.ne_zero this

end Alg

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L} {m : ℕ}

theorem exists_move {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ c q) {Y : Matrix (Fin m ⊕ Fin m) (Fin m) L}
    (hf : ∀ z, Y *ᵥ z = 0 → z = 0) (hY : Yᵀ * Wm L (Fin m) * Y.map c = 0) :
    ∃ k k' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L, k * k' = 1 ∧ Iso c (Wm L (Fin m)) (Wm L (Fin m)) k ∧
      (∀ i j, Valued.v (k i j) ≤ 1) ∧ (∀ i j, Valued.v (k' i j) ≤ 1) ∧
      ∃ T : Matrix (Fin m) (Fin m) L, IsUnit T.det ∧ k * Y = fromRows T (0 : Matrix (Fin m) (Fin m) L) := by
  obtain ⟨hc, hv, -, -, ⟨x, hx, hx1⟩, -, -⟩ := hU
  have hx0 : c x - x ≠ 0 := by
    intro h; rw [h, map_zero] at hx1; exact zero_ne_one hx1
  have hw : c x * (c x - x)⁻¹ + c (c x * (c x - x)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, map_sub, hc, ← neg_sub (c x) x, inv_neg]
    field_simp
    ring
  obtain ⟨R, hR⟩ := exists_leftInv hf
  obtain ⟨X, hX⟩ := exists_compl hc hw hR hY
  obtain ⟨k, hk, hki, h0⟩ := exists_reduce hc hv _ hX
  have hku := Matrix.mul_nonsing_inv _ (hk.isUnit_det Wm_det)
  have h21 : (k * fromCols Y X).toBlocks₂₁ = 0 := Matrix.ext h0
  refine ⟨k, k⁻¹, hku, hk, hki, fun i j => ?_, (k * fromCols Y X).toBlocks₁₁, ?_, ?_⟩
  · rw [inv_apply_of_iso hc hk hku, hv]; exact hki _ _
  · have := (hk.mul hX).isUnit_det Wm_det
    rw [← fromBlocks_toBlocks (k * fromCols Y X), h21, det_fromBlocks_zero₂₁] at this
    exact isUnit_of_mul_isUnit_left this
  · ext (i | i) j
    · rfl
    · exact h0 i j

theorem mem_IntGL_iff {g : GL (Fin m ⊕ Fin m) L} :
    g ∈ IntGL L m ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨fun i j => (k.val i j).2, fun i j => ((k⁻¹).val i j).2⟩
  · rintro ⟨h1, h2⟩
    have inj : Function.Injective
        ((intL L).subtype.mapMatrix : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (intL L) →+* _) := fun a b e => by
      ext i j
      exact congrFun (congrFun e i) j
    refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, inj ?_, inj ?_⟩, Units.ext rfl⟩
    · rw [map_mul, map_one]; exact Units.mul_inv g
    · rw [map_mul, map_one]; exact Units.inv_mul g

end PositivityTheory.Sph.M2.Chart

end
end

noncomputable section

namespace PositivityTheory.Sph.M2

open scoped Matrix
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

namespace Chart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

theorem frame_mul {n : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {a κ : GL (Fin n) (w.adicCompletion E)} (ha : IsFrameAt w Λ a)
    (h1 : ∀ i j, κ.1 i j ∈ Ov E w) (h2 : ∀ i j, (κ⁻¹).1 i j ∈ Ov E w) : IsFrameAt w Λ (a * κ) := fun z => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← ha]
  refine ⟨fun hz => mulVec_int h1 hz, fun hz i => ?_⟩
  have := mulVec_int h2 hz i
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem free_loc (h : w.under (𝓞 F) = v) (hw : IsInertAt F E v w) {n : ℕ} {W : Spc F E n}
    {Cy : Matrix (Fin n) (Fin m) (AE F E)} (hL : IsLagAt σ W v Cy) (z : Fin m → w.adicCompletion E)
    (hz : Cy.map (piE h) *ᵥ z = 0) : z = 0 := by
  obtain ⟨t, ht, rfl⟩ := vec_surj h z
  have z0 : ∀ {k : ℕ}, piE h ∘ (0 : Fin k → AE F E) = 0 := funext fun _ => map_zero _
  rw [hL.free t ht (vec_inj hw h (at_sub (at_mulVec_right _ ht) at_zero) (by rw [piE_mulVec, hz, z0])), z0]

theorem exists_frame_lag (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v)
    {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) {B : Base F E} {W : Spc F E (m + m)} {r s : ℕ}
    (hW : W.IsSkew σ B r s) {Cy : Matrix (Fin (m + m)) (Fin m) (AE F E)} (hL : IsLagAt σ W v Cy) :
    ∃ a : GL (Fin (m + m)) (w.adicCompletion E), IsFrameAt w W.L a ∧ ∃ l : w.adicCompletion E, l ≠ 0 ∧
      Iso c (W.J.map (algebraMap E _)) (l • antiJ _ (m + m)) a.1 ∧
      ∃ T : Matrix (Fin m) (Fin m) (w.adicCompletion E), IsUnit T.det ∧
        ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id = Matrix.fromRows T (0 : Matrix (Fin m) (Fin m) _) := by
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨a, ha, l, hl, hg⟩ := exists_frame hσ hw h hc hW
  have hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ (m + m)) a.1 := hg
  have hC : (Cy.map (piE h))ᵀ * W.J.map (algebraMap E (w.adicCompletion E)) * (Cy.map (piE h)).map c = 0 := by
    rw [← map_gram hc, hL.iso, Matrix.map_zero _ (map_zero _)]
  have hf := free_loc h hw hL
  generalize Cy.map (piE h) = C at hC hf ⊢
  obtain ⟨Z, rfl⟩ : ∃ Z, C = a.1 * Z := ⟨(a⁻¹).1 * C, by rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]⟩
  have hZ : Zᵀ * antiJ (w.adicCompletion E) (m + m) * Z.map c = 0 := by
    refine (smul_eq_zero_iff_right hl).1 ?_
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← hg, ← hC, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨k, k', hkk, hk, hi, hi', T, hT, eT⟩ := exists_move hU (Y := Z.submatrix (ee m) id) (fun z hz => hf z (by
      have : Z *ᵥ z = 0 := funext fun i => by
        obtain ⟨i, rfl⟩ := (ee m).surjective i
        exact congrFun hz i
      rw [← Matrix.mulVec_mulVec, this, Matrix.mulVec_zero])) (by
      rw [← antiJ_submatrix]
      change Zᵀ.submatrix id (ee m) * _ * (Z.map c).submatrix (ee m) id = _
      rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hZ]
      rfl)
  let κ : GL (Fin (m + m)) (w.adicCompletion E) :=
    ⟨k'.submatrix (ee m).symm (ee m).symm, k.submatrix (ee m).symm (ee m).symm,
      by rw [Matrix.submatrix_mul_equiv, mul_eq_one_comm.1 hkk, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, hkk, Matrix.submatrix_one_equiv]⟩
  refine ⟨a * κ, frame_mul ha (fun i j => hi' _ _) (fun i j => hi _ _), l, hl, hai.mul ((iso_smul_iff hl _ _).2 ?_), T, hT, ?_⟩
  · have h1 := iso_submatrix (ee m).symm (hk.inv hkk)
    rwa [← antiJ_submatrix, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] at h1
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (a⁻¹).1, Units.inv_mul, Matrix.one_mul, ← eT,
      ← Matrix.submatrix_mul_equiv _ _ _ (ee m)]
    rw [show (κ⁻¹).1 = k.submatrix (ee m).symm (ee m).symm from rfl, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]

def phi (h : w.under (𝓞 F) = v) (W : Spc F E (m + m)) (a : GL (Fin (m + m)) (w.adicCompletion E)) :
    UA σ W.J →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E) where
  toFun := fun g => ((a⁻¹).1 * (mat g).map (piE h) * a.1).submatrix (ee m) (ee m)
  map_one' := by
    rw [show mat (1 : UA σ W.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Units.inv_mul,
      Matrix.submatrix_one_equiv]
  map_mul' := fun g g' => by
    rw [show mat (g * g') = mat g * mat g' from rfl, Matrix.submatrix_mul_equiv, Matrix.map_mul]
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]

variable {h : w.under (𝓞 F) = v} {W : Spc F E (m + m)} {a : GL (Fin (m + m)) (w.adicCompletion E)}
  {c : w.adicCompletion E →+* w.adicCompletion E} {l : w.adicCompletion E}

theorem phi_apply (g : UA σ W.J) : phi h W a g = ((a⁻¹).1 * (mat g).map (piE h) * a.1).submatrix (ee m) (ee m) := rfl

theorem phi_iso (hc : IsConjAt σ h c) (hl : l ≠ 0) (hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ (m + m)) a.1)
    (g : UA σ W.J) : Iso c (Wm _ (Fin m)) (Wm _ (Fin m)) (phi h W a g) := by
  have h1 : Iso c (W.J.map (algebraMap E _)) (W.J.map (algebraMap E _)) ((mat g).map (piE h)) := by
    unfold Iso
    rw [← map_gram hc, show (mat g)ᵀ * incM F W.J * (mat g).map (cA σ) = incM F W.J from g.2]
    exact Matrix.ext fun i j => piE_incl h _
  rw [phi_apply, ← antiJ_submatrix]
  exact iso_submatrix _ ((iso_smul_iff hl _ _).1 (((hai.inv a.mul_inv).mul h1).mul hai))

theorem phi_inj (hw : IsInertAt F E v w) {g g' : UA σ W.J} (hg : g ∈ USub σ W v) (hg' : g' ∈ USub σ W v)
    (e : phi h W a g = phi h W a g') : g = g' := by
  have e1 : (mat g).map (piE h) = (mat g').map (piE h) := by
    have e2 := congrArg (fun N => a.1 * N.submatrix (ee m).symm (ee m).symm * (a⁻¹).1) e
    simpa [phi_apply, Matrix.mul_assoc] using e2
  refine Subtype.ext (Units.ext (mat_inj hw h ?_ e1))
  have := at_sub (show At (evFin F v) (mat g - 1) from hg) (show At (evFin F v) (mat g' - 1) from hg')
  rwa [sub_sub_sub_cancel_right] at this

theorem phi_surj (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) (hl : l ≠ 0) (hJ : W.J.det ≠ 0)
    (hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ (m + m)) a.1)
    {N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)} (hN : Iso c (Wm _ (Fin m)) (Wm _ (Fin m)) N) :
    ∃ g ∈ USub σ W v, phi h W a g = N := by
  have h1 := iso_submatrix (ee m).symm hN
  rw [← antiJ_submatrix, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] at h1
  have h2 := (hai.mul ((iso_smul_iff hl _ _).2 h1)).mul (hai.inv a.mul_inv)
  have h3 := h2.isUnit_det (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact ((map_ne_zero _).2 hJ).isUnit)
  obtain ⟨k, hk, ek⟩ := exists_lift_UA hw hc W (Matrix.mul_nonsing_inv _ h3) h2
  refine ⟨k, hk, ?_⟩
  rw [phi_apply, ek]
  simp [Matrix.mul_assoc]

theorem phi_int (hw : IsInertAt F E v w) (ha : IsFrameAt w W.L a) (g : UA σ W.J) :
    (∀ i j, Valued.v (phi h W a g i j) ≤ 1) ↔ ∀ y ∈ latW W v, mat g *ᵥ y ∈ latW W v := by
  rw [stab_iff hw h ha]
  refine ⟨fun H i j => ?_, fun H i j => H _ _⟩
  obtain ⟨i, rfl⟩ := (ee m).surjective i
  obtain ⟨j, rfl⟩ := (ee m).surjective j
  exact H i j

theorem phi_col (hw : IsInertAt F E v w) {Cy : Matrix (Fin (m + m)) (Fin m) (AE F E)} (hy : At (evFin F v) Cy)
    (g : UA σ W.J) (t : Matrix (Fin m) (Fin m) (AE F E)) :
    mat g * Cy = Cy * t ↔ phi h W a g * ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id =
      ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id * t.map (piE h) := by
  have e1 : phi h W a g * ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id =
      ((a⁻¹).1 * (mat g * Cy).map (piE h)).submatrix (ee m) id := by
    rw [phi_apply, Matrix.submatrix_mul_equiv, Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc a.1, Units.mul_inv,
      Matrix.one_mul, Matrix.mul_assoc]
  have e2 : ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id * t.map (piE h) =
      ((a⁻¹).1 * (Cy * t).map (piE h)).submatrix (ee m) id := by
    rw [Matrix.map_mul, ← Matrix.mul_assoc]
    rfl
  rw [e1, e2]
  refine ⟨fun e => by rw [e], fun e => mat_inj hw h (at_sub (at_mul_right _ hy) (at_mul_left hy _)) ?_⟩
  have e3 : (a⁻¹).1 * (mat g * Cy).map (piE h) = (a⁻¹).1 * (Cy * t).map (piE h) := by
    refine Matrix.ext fun i j => ?_
    obtain ⟨i, rfl⟩ := (ee m).surjective i
    exact congrFun (congrFun e i) j
  have e4 := congrArg (fun N => a.1 * N) e3
  simpa only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] using e4

theorem phi_par (hw : IsInertAt F E v w) {Cy : Matrix (Fin (m + m)) (Fin m) (AE F E)} (hy : At (evFin F v) Cy)
    {T : Matrix (Fin m) (Fin m) (w.adicCompletion E)} (hT : IsUnit T.det)
    (eT : ((a⁻¹).1 * Cy.map (piE h)).submatrix (ee m) id = Matrix.fromRows T (0 : Matrix (Fin m) (Fin m) _))
    (g : UA σ W.J) : (∃ t : Matrix (Fin m) (Fin m) (AE F E), mat g * Cy = Cy * t) ↔ (phi h W a g).toBlocks₂₁ = 0 := by
  rw [← block_iff hT, ← eT]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨_, (phi_col hw hy g t).1 ht⟩
  · rintro ⟨t, ht⟩
    obtain ⟨t', -, rfl⟩ := mat_surj h t
    exact ⟨t', (phi_col hw hy g t').2 ht⟩

end Chart

open Chart in
theorem chart : ChartSt := by
  intro F E _ _ _ _ _ σ B r s m W hB hW v w hw h c hc Cy hL
  obtain ⟨a, ha, l, hl, hai, T, hT, eT⟩ := exists_frame_lag hB.cm hw h hc hW hL
  have hG : ∀ g, (phi h W a).toHomUnits g ∈ GW (w.adicCompletion E) c m := fun g => phi_iso hc hl hai g
  have hP : ∀ g, (phi h W a).toHomUnits g ∈ PW (w.adicCompletion E) c m ↔
      ∃ t : Matrix (Fin m) (Fin m) (AE F E), mat g * Cy = Cy * t := fun g => by
    rw [phi_par hw hL.supp hT eT g]
    exact ⟨fun H => GlobalTheory.LGrp.mem_blockQ_two.1 H.2, fun H => ⟨hG g, GlobalTheory.LGrp.mem_blockQ_two.2 H⟩⟩
  refine ⟨(phi h W a).toHomUnits, hG, fun g hg g' hg' e => phi_inj hw hg hg' (congrArg Units.val e), fun M hM => ?_,
    fun g hg => ?_, fun g hg => ?_, fun p _ t ht => ?_⟩
  · obtain ⟨g, hg, e⟩ := phi_surj hw hc hl (det_ne_zero hW) hai hM
    exact ⟨g, hg, Units.ext e⟩
  · rw [mem_IntGL_iff, ← map_inv]
    exact ⟨fun H => ⟨(phi_int hw ha g).2 fun y hy => (H.2 y hy).1, (phi_int hw ha g⁻¹).2 fun y hy => (H.2 y hy).2⟩,
      fun H => ⟨hg, fun y hy => ⟨(phi_int hw ha g).1 H.1 y hy, (phi_int hw ha g⁻¹).1 H.2 y hy⟩⟩⟩
  · refine ⟨fun H => (hP g).2 H.1.2, fun H => ⟨⟨hg, (hP g).1 H⟩, (USub σ W v).inv_mem hg, (hP g⁻¹).1 ?_⟩⟩
    rw [map_inv]
    exact inv_mem H
  · have e := (phi_col (a := a) (h := h) hw hL.supp p t).1 ht
    rw [eT] at e
    exact (block_det hT e).trans (RingHom.map_det (piE h) t).symm

end PositivityTheory.Sph.M2

end
end

section -- merged from Development.WeilBound.ThetaLifts.SphericalLattices.RelIndexTransport
noncomputable section

namespace PositivityTheory.Sph.M2

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas MeasureTheory GlobalTheory.Doubling

theorem relIndex_transport {G H : Type} [Group G] [Group H] (U : Subgroup G) (Φ : G →* H)
    (hinj : ∀ g ∈ U, ∀ g' ∈ U, Φ g = Φ g' → g = g') {A B : Subgroup G} (hA : A ≤ U) (hB : B ≤ U) :
    (A.map Φ).relIndex (B.map Φ) = A.relIndex B := by
  have hφ : Function.Injective (Φ.comp U.subtype) := fun x y e => Subtype.ext (hinj _ x.2 _ y.2 e)
  have e : ∀ C : Subgroup G, C ≤ U → (C.subgroupOf U).map (Φ.comp U.subtype) = C.map Φ := fun C hC => by
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hC]
  rw [← e A hA, ← e B hB, Subgroup.relIndex_map_map_of_injective _ _ hφ, Subgroup.relIndex_subgroupOf hB]

theorem map_conj_map {G H : Type} [Group G] [Group H] (Φ : G →* H) (g : G) (A : Subgroup G) :
    (A.map (MulAut.conj g).toMonoidHom).map Φ = (A.map Φ).map (MulAut.conj (Φ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [map_mul, map_inv]

theorem modSt_of (hC : ChartSt) (hL : LocModSt) : PositivityTheory.Sph.ModSt := by
  intro F E _ _ _ _ _ σ d B W r s hB hW v w hw _ m Cy hLag hAd p hp t ht u hu
  obtain rfl : d = m + m := hLag.rank.trans (two_mul m)
  have hσ := hB.cm
  have h : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw h
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨Φ, hG, hinj, hsurj, hK, hP, hdet⟩ := hC F E σ B r s m W hB hW v w hw h c hc Cy hLag
  set KP := PositivityTheory.Sph.PSub σ W v Cy ⊓ KSub σ W v with hKP
  have hKPU : KP ≤ USub σ W v := fun g hg => (hg.2 : g ∈ KAt σ W v).1
  have hpU : p ∈ USub σ W v := (hp.1 : p ∈ PAt σ W v Cy).1
  have himg : KP.map Φ = KPW (w.adicCompletion E) c m := by
    ext M
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hgU := hKPU hg
      exact ⟨(hP g hgU).1 hg.1, hG g, (hK g hgU).1 hg.2⟩
    · rintro ⟨hM1, hM2, hM3⟩
      obtain ⟨g, hgU, rfl⟩ := hsurj _ hM2
      exact ⟨g, ⟨(hP g hgU).2 hM1, (hK g hgU).2 hM3⟩, rfl⟩
  have hconj : ∀ g ∈ USub σ W v, KP.map (MulAut.conj g).toMonoidHom ≤ USub σ W v := fun g hg => by
    rintro _ ⟨k, hk, rfl⟩
    exact (USub σ W v).mul_mem ((USub σ W v).mul_mem hg (hKPU hk)) ((USub σ W v).inv_mem hg)
  have tr : ∀ g ∈ USub σ W v, (KP.map (MulAut.conj g).toMonoidHom).relIndex KP =
      ((KPW (w.adicCompletion E) c m).map (MulAut.conj (Φ g)).toMonoidHom).relIndex (KPW (w.adicCompletion E) c m) :=
    fun g hg => by
      rw [← relIndex_transport (USub σ W v) Φ hinj (hconj g hg) hKPU, map_conj_map, himg]
  have hPW : Φ p ∈ PW (w.adicCompletion E) c m := (hP p hpU).1 hp
  have key := hL (w.adicCompletion E) ϖ c (Formalism.UG.qV F v) hU m (Φ p) hPW
  rw [← map_inv, ← tr p⁻¹ ((USub σ W v).inv_mem hpU), ← tr p hpU, hdet p hp t ht] at key
  rw [key]
  congr 1
  have h21 : (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₂₁ = 0 :=
    GlobalTheory.LGrp.mem_blockQ_two.1 hPW.2
  have hdetΦ : (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).det =
      (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₁₁.det *
        (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)).toBlocks₂₂.det := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Φ p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (w.adicCompletion E)), h21]
    exact Matrix.det_fromBlocks_zero₂₁ _ _ _
  have hne : piE h t.det ≠ 0 := by
    rw [← hdet p hp t ht]
    intro h0
    have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (Φ p).isUnit
    rw [hdetΦ, h0, zero_mul] at hu'
    exact not_isUnit_zero hu'
  let x : (Fv F v ⊗[F] E)ˣ := Units.map (complEquiv hw h).symm.toMonoidHom (Units.mk0 _ hne)
  have hx1 : x.1 = (t.map (compFin F E v)).det := by
    change (complEquiv hw h).symm ((complEquiv hw h) (compFin F E v t.det)) = _
    rw [RingEquiv.symm_apply_apply]
    exact RingHom.map_det _ _
  have habs := GlobalTheory.AbsInert.absEv_inert F E σ hσ v w h hw x
  have hm : (((sbClass (Fv F v)).modu u : NNReal) : ℝ) = (absEv F E v x : ℝ) := by
    have e1 := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v (u : Fv F v) u.ne_zero
    rw [Units.mk0_val] at e1
    change ((distribHaarChar (Fv F v) u : NNReal) : ℝ) = _
    rw [e1, absEv_apply, hx1, ← hu]
  have hx : piE h t.det = toCompl h x.1 := by
    rw [hx1]
    change toCompl h (compFin F E v t.det) = toCompl h (t.map (compFin F E v)).det
    rw [RingHom.map_det]
    rfl
  rw [hm, habs, hx, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

end PositivityTheory.Sph.M2

end
end

namespace PositivityTheory.Sph

theorem modSt2 : ModSt := M2.modSt_of M2.chart M2.locMod

end PositivityTheory.Sph
