module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Height
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilActDefs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitHtA
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit.Ht
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem par_topleft_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    ∃ tb : GL (Fin d.n) E, (inFrame d.b p).toBlocks₁₁ = incM F (tb⁻¹).1 * t.1 * incM F tb.1 := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  refine ⟨tb, ?_⟩
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1 := htb
  have hp' : mat2 p * DC = DC * t.1 := hp
  have hcol : ∀ M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), M * E1 = M.toCols₁ := by
    intro M
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 * E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1) = DC * incM F tb.1 := by
    rw [incM_mul']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 * E1 = DC * incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 * incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBB : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d
  have hdc : DC = incM F d.b.1 * E1 * incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have key : inFrame d.b p * E1 = E1 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
    have e0 : inFrame d.b p = incM F (d.b⁻¹).1 * mat2 p * incM F d.b.1 := rfl
    calc inFrame d.b p * E1 = incM F (d.b⁻¹).1 * (mat2 p * (incM F d.b.1 * E1)) := by
          rw [e0]; simp only [Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 * ((mat2 p * DC) * incM F tb.1) := by
          rw [hb, Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 * ((DC * t.1) * incM F tb.1) := by rw [hp']
      _ = (incM F (d.b⁻¹).1 * incM F d.b.1) * E1 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
          rw [hdc]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBB, Matrix.one_mul]
  ext i j
  have := congrFun (congrFun key (Sum.inl i)) j
  rw [hcol] at this
  simpa [E1, Matrix.toBlocks₁₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq] using this
theorem inFrame_form_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (y : d.G) : ∃ C' : Matrix (Fin d.n) (Fin d.n) (AE F E),
    (∃ ε : ℤˣ, C' = ((ε : ℤ) : AE F E) • 1) ∧
    (inFrame d.b y)ᵀ * Matrix.fromBlocks 0 1 C' 0 * (inFrame d.b y).map (cA σ) = Matrix.fromBlocks 0 1 C' 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have hF : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
    rw [e1, e2, ← key, hε]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨((ε : ℤ) : AE F E) • 1, ⟨ε, rfl⟩, ?_⟩
  have hM : (mat2 y)ᵀ * dbl (incM F d.Y.J) * (mat2 y).map (cA σ) = dbl (incM F d.Y.J) := y.2
  have := form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hM
  rw [← hF]
  exact this
theorem levi_tu_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (hx : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1) :
    t.1ᵀ * u.1.map (cA σ) = 1 := by
  obtain ⟨C', -, h⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.inFrame_form_k d x
  rw [hx] at h
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero (cA σ)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at h
  exact h.2.1
theorem frame_iwa_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g : d.G) : ∃ (D : GL (Fin d.n) (AE F E)) (k : d.G), k ∈ d.K ∧
    d.a g = ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det D) : ℝ≥0) : ℝ)⁻¹ ∧
    (inFrame d.b g).toBlocks₂₁ = D.1 * (inFrame d.b k).toBlocks₂₁ ∧
    (inFrame d.b g).toBlocks₂₂ = D.1 * (inFrame d.b k).toBlocks₂₂ := by
  obtain ⟨p, t', hp, k, hk, rfl⟩ := d.ok.hgt.iwa g
  have h21 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.parabolic_lowerLeft_block_zero d p t' hp
  obtain ⟨tb, htl⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.par_topleft_k d p t' hp
  set A := (inFrame d.b p).toBlocks₁₁ with hA
  set B := (inFrame d.b p).toBlocks₁₂ with hB
  set D₀ := (inFrame d.b p).toBlocks₂₂ with hD₀
  have hPb : inFrame d.b p = Matrix.fromBlocks A B 0 D₀ := by rw [← h21, Matrix.fromBlocks_toBlocks]
  obtain ⟨C', ⟨ε, hC'⟩, hform⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.inFrame_form_k d p
  rw [hPb, hC'] at hform
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero (cA σ)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at hform
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hDA : D₀ᵀ * A.map (cA σ) = 1 := by
    have h3 := hform.2.2.1
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at h3
    have := congrArg (fun M => ((ε : ℤ) : AE F E) • M) h3
    simpa [smul_smul, hεε] using this
  have hdet : D₀.det * cA σ A.det = 1 := by
    have := congrArg Matrix.det hDA
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one,
      show (A.map (cA σ)).det = cA σ A.det from (AlgHom.map_det (cA σ) A).symm] at this
    exact this
  have hDu : IsUnit D₀ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, hdet⟩)
  refine ⟨hDu.unit, k, hk, ?_, ?_, ?_⟩
  · rw [d.ok.hgt.val p t' hp k hk]
    have hAt : A.det = (Matrix.GeneralLinearGroup.det t').1 := by
      rw [htl, Matrix.det_mul, Matrix.det_mul]
      have hinv : (incM F (tb⁻¹).1).det * (incM F tb.1).det = 1 := by
        rw [← Matrix.det_mul]
        have e : incM F (tb⁻¹).1 * incM F tb.1 = 1 := by
          simp only [incM, ← Matrix.map_mul, Units.inv_mul]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        rw [e, Matrix.det_one]
      simp only [Matrix.GeneralLinearGroup.val_det_apply]
      linear_combination (t'.1.det) * hinv
    have hU : Matrix.GeneralLinearGroup.det hDu.unit *
        GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det t') = 1 := by
      ext
      simp only [Units.val_mul, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec,
        GlobalTheory.Doubling.conjUnit, Units.coe_map]
      change D₀.det * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ t'.1.det = 1
      rw [sigR_eq_cA, ← Matrix.GeneralLinearGroup.val_det_apply, ← hAt]
      exact hdet
    have := congrArg (GlobalTheory.Doubling.absE F E) hU
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one] at this
    have hpos : (0 : ℝ≥0) < GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det hDu.unit) := by
      rcases eq_or_ne (GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det hDu.unit)) 0 with h | h
      · rw [h, zero_mul] at this; exact absurd this zero_ne_one
      · exact pos_iff_ne_zero.2 h
    rw [eq_inv_of_mul_eq_one_right this, NNReal.coe_inv]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hPb]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (inFrame d.b k)]
    simp [Matrix.fromBlocks_multiply]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hPb]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (inFrame d.b k)]
    simp [Matrix.fromBlocks_multiply]
theorem bottom_rows_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (hx : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1)
    (nb : nA σ d.Y d.b → d.G) (hnb : IsNMap d.b nb) (ε : ℤˣ) (w : d.G) (hw : d.IsW ε w) (β : nA σ d.Y d.b) :
    (inFrame d.b (w * nb β * x)).toBlocks₂₁ = (((ε : ℤ) : AE F E) • t.1) ∧
    (inFrame d.b (w * nb β * x)).toBlocks₂₂ = (((ε : ℤ) : AE F E) • (β.1 * u.1)) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hw, hnb β, hx]
  simp only [Matrix.fromBlocks_multiply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, Matrix.of_apply, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂]
  constructor <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, ite_mul, Finset.sum_ite_eq,
    Finset.mul_sum, mul_assoc]
end PositivityTheory.SiegelWeilFormula.KWhit.Ht
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilHeightdictStd
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.KWhit.Ht
namespace PositivityTheory.SiegelWeilFormula.HeightDict
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fin_std_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (t u : GL (Fin n) (AE F E)) (η : E) (hη : η ≠ 0) :
    (∀ v : HeightOneSpectrum (𝓞 F),
      Gen.IsCO (latM v ((t.1.map (GlobalTheory.AdelicU.compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ))) ∧
      Gen.IsCO (latM v (((inclR (F := F) (v.adicCompletion F) η) • u.1.map (GlobalTheory.AdelicU.compFin F E v)).map
        (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)))) ∧
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ((latM v ((t.1.map (GlobalTheory.AdelicU.compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)) :
        Set (Fin n → v.adicCompletion F ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v) ∧
      ((latM v (((inclR (F := F) (v.adicCompletion F) η) • u.1.map (GlobalTheory.AdelicU.compFin F E v)).map
        (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)) : Set (Fin n → v.adicCompletion F ⊗[F] E)) =
          PositivityTheory.PfSWUS.Loc.latO d.bs v) := by
  classical
  have hinv1 : ∀ v : HeightOneSpectrum (𝓞 F),
      (t.1.map (compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) *
        ((t⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
    intro v
    have h := congrArg (fun M => (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ).mapMatrix
      ((compFin F E v).mapMatrix M)) (Units.mul_inv t)
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
  have hinv2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ((inclR (F := F) (v.adicCompletion F) η) • u.1.map (compFin F E v)).map
          (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) *
        ((inclR (F := F) (v.adicCompletion F) η⁻¹) • (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)).map
          (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
    intro v
    have hu : u.1.map (compFin F E v) * (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v) = 1 := by
      have h := congrArg (fun M => (compFin F E v).mapMatrix M) (Units.mul_inv u)
      simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
    have hc : inclR (F := F) (v.adicCompletion F) η * inclR (F := F) (v.adicCompletion F) η⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hη, map_one]
    have h2 : (inclR (F := F) (v.adicCompletion F) η • u.1.map (compFin F E v)) *
        (inclR (F := F) (v.adicCompletion F) η⁻¹ • (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hu, smul_smul, hc, one_smul]
    have h := congrArg (fun M => (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ).mapMatrix M) h2
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
  refine ⟨fun v => ⟨latM_isCO v _ (Matrix.isUnit_det_of_right_inverse (hinv1 v)),
    latM_isCO v _ (Matrix.isUnit_det_of_right_inverse (hinv2 v))⟩, ?_⟩
  have ent : ∀ M : Matrix (Fin n) (Fin n) (AE F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ i j, compFin F E v (M i j) ∈ OE E v := fun M =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_OE (M i j)
  filter_upwards [ent t.1, ent (t⁻¹ : GL (Fin n) (AE F E)).1, ent u.1, ent (u⁻¹ : GL (Fin n) (AE F E)).1,
    ev_inclR (F := F) η, ev_inclR (F := F) η⁻¹, ev_lat_latO d.bs n] with v ht ht' hu hu' he he' hl
  refine ⟨?_, ?_⟩
  · rw [latM_eq_lat v _ _ (hinv1 v) (fun i j => OE_sig v (ht i j)) (fun i j => OE_sig v (ht' i j)), hl]
  · rw [latM_eq_lat v _ _ (hinv2 v) (fun i j => OE_sig v (OE_mul v he (hu i j)))
      (fun i j => OE_sig v (OE_mul v he' (hu' i j))), hl]
end PositivityTheory.SiegelWeilFormula.HeightDict
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit.Ht
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem k_int_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {k : d.G} (hk : k ∈ d.K) (v : HeightOneSpectrum (𝓞 F)) (i j : Fin d.n ⊕ Fin d.n) :
    compFin F E v (inFrame d.b k i j) ∈ OE E v ∧ compFin F E v (inFrame d.b k⁻¹ i j) ∈ OE E v := by
  have h := ((d.ok.stdK k).1 hk).2
  have e : ∀ z : AE F E, compFin F E v (finOne F • z) = compFin F E v z := fun z => by
    rw [compFin_smul, evFin_finOne, one_smul]
  exact ⟨e _ ▸ compFin_intHat v (h k (by simp) i j), e _ ▸ compFin_intHat v (h k⁻¹ (by simp) i j)⟩
theorem k_unit_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {k : d.G} (hk : k ∈ d.K) (w : InfinitePlace F) :
    (inFrame d.b k).map (piInf (d.B.emb w)) * ((inFrame d.b k).map (piInf (d.B.emb w)))ᴴ = 1 :=
  ((d.ok.stdK k).1 hk).1 w
theorem inFrame_mul_inv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (k : d.G) : inFrame d.b k * inFrame d.b k⁻¹ = 1 := by
  rw [← _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, mul_inv_cancel]
  simp only [inFrame, mat2, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]
  exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d
theorem piInf_cA_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (z : AE F E) :
    piInf (d.B.emb w) (cA σ z) = star (piInf (d.B.emb w) z) := by
  simp only [piInf, RingHom.comp_apply, compInf_cA]
  exact (GlobalTheory.AdelicU.infEmb_sigR d.ok.good.cm (d.B.emb w) _).symm
theorem piInf_inclR_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (e : E) :
    piInf (d.B.emb w) (inclR (F := F) (AF F) e) = (d.B.emb w).1 e := by
  simp [piInf, compInf, inclR, Algebra.TensorProduct.map_tmul, infEmb_tmul]
theorem real_at_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hR : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g) (ε : ℤˣ) (β : nA σ d.Y d.b)
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
    have hu := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.k_unit_k d hk w
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
    have h0 := congrArg (fun M => M.map pw) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.levi_tu_k d x t u hR.levi)
    simp only [hmap, Matrix.map_one _ (map_zero pw) (map_one pw)] at h0
    have h3 : ((t.1ᵀ.map pw) * ((u.1.map (cA σ)).map pw)).map (starRingEnd ℂ) =
        (1 : Matrix (Fin d.n) (Fin d.n) ℂ).map (starRingEnd ℂ) := by rw [h0]
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h3
    have e1 : ((u.1.map (cA σ)).map pw).map (starRingEnd ℂ) = u.1.map pw := by
      ext i j
      simp only [Matrix.map_apply]
      rw [hpw, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.piInf_cA_k]
      simp
    rw [e1] at h3
    rw [← h3]
    rfl
  have hh : ((hOf β).1.map pw)ᴴ = (hOf β).1.map pw := by
    ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← (hOf β).2 a b, sigR_eq_cA', _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.piInf_cA_k]
  have hβ : β.1.map pw = -(((d.B.emb w).1 η) • ((hOf β).1.map pw)ᵀ) := by
    rw [hR.hof β]
    ext i j
    simp [Matrix.map_apply, Matrix.mul_apply, Matrix.scalar_apply, incM, Matrix.diagonal_apply, hpw, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.piInf_inclR_k]
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
theorem fin_at_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hR : _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g) (ε : ℤˣ) (β : nA σ d.Y d.b)
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
    have h0 := congrArg (fun M => M.map cf) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.levi_tu_k d x t u hR.levi)
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
    rw [← hmap, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.inFrame_mul_inv_k, Matrix.map_one _ (map_zero cf) (map_one cf)]
  have h1' := congrArg (fun M => M.map cf) h1
  have h2' := congrArg (fun M => M.map cf) h2
  simp only [hsm, hmap, map_intCast] at h1' h2'
  have key := PositivityTheory.SiegelWeilFormula.HeightDict.fin_index hcm v d.n (t.1.map cf) (u.1.map cf) (D.1.map cf) (β.1.map cf) ((hOf β).1.map cf)
    (inclR (F := F) (v.adicCompletion F) η) (((ε : ℤ) : v.adicCompletion F ⊗[F] E))
    ((inFrame d.b k).map cf) ((inFrame d.b k⁻¹).map cf) ht hD htu hη he he1 hβ hh hkk
    (fun i j => (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.k_int_k d hk v i j).1) (fun i j => (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.k_int_k d hk v i j).2) h1' h2' lam
  rw [det_map, det_map] at key
  exact key
theorem absE_split_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : (AE F E)ˣ) :
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
theorem heightDict_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.HeightDict_k := by
  intro F E _ _ _ _ _ σ d R x t u T η T₀ hOf θ fr g hR nb lam 𝓖 hc ε w hw
  choose lv hlv using fun v : HeightOneSpectrum (𝓞 F) => exists_haar_tup (E := E) v d.n
  obtain ⟨hCO, hstd⟩ := _root_.PositivityTheory.SiegelWeilFormula.HeightDict.fin_std_k (σ := σ) d d.n t u η hR.ne
  have hat : (0 : ℝ) < ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ≥0) : ℝ) :=
    absE_pos _
  refine ⟨lv, L1 σ t, L2 σ u η, ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det t) : ℝ≥0) : ℝ)⁻¹,
    inv_pos.2 hat, hlv, hCO, hstd, fun β => ?_⟩
  obtain ⟨D, k, hk, ha, hb1, hb2⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.frame_iwa_k d (w * nb β * x)
  obtain ⟨hr1, hr2⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.bottom_rows_k d x t u hR.levi nb hc.1 ε w hw β
  have h1 := hr1.symm.trans hb1
  have h2 := hr2.symm.trans hb2
  have hre := fun w' => _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.real_at_k d R hR ε β D hk h1 h2 w'
  have hfi := fun v => _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.fin_at_k d R hR ε β D hk h1 h2 v (lv v)
  set X : InfinitePlace F → ℝ := fun w' => (1 + (((g w')⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w') * (((g w')⁻¹).1)ᴴ) *
        (((g w')⁻¹).1 * (Gen.matInf (hOf β).1).map (θ w') * (((g w')⁻¹).1)ᴴ)).det.re with hX
  set N : HeightOneSpectrum (𝓞 F) → ℝ := fun v => Gen.nu2 (lv v) (L1 σ t v) (L2 σ u η v) (Gen.matV v (hOf β).1)
    with hN
  have hnuA : Gen.nuA θ g lv (L1 σ t) (L2 σ u η) (hOf β).1 = (∏ w', X w') * ∏ᶠ v, N v := rfl
  have hsD := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.absE_split_k d (Matrix.GeneralLinearGroup.det D)
  have hsT := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.absE_split_k d (Matrix.GeneralLinearGroup.det t)
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
end
