module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
public import Development.AutomorphicArithmetic.AdelicQuotients.NormGaloisSmulAdeleComponentAtSmulPlace

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup

noncomputable section


open Classical in
private def psi {K : Type} [Field K] (w : InfinitePlace K) : ℝ →+* w.Completion :=
  if hw : w.IsReal then ((ringEquivRealOfIsReal hw).symm : ℝ ≃+* w.Completion).toRingHom
  else ((ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm : ℂ ≃+* w.Completion).toRingHom.comp
    Complex.ofRealHom

private theorem continuous_psi {K : Type} [Field K] (w : InfinitePlace K) : Continuous (psi w) := by
  unfold psi
  split_ifs with hw
  · exact (isometryEquivRealOfIsReal hw).symm.continuous
  · exact (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm.continuous.comp
      Complex.continuous_ofReal

private theorem posRealElem_eq {K : Type} [Field K] (w : InfinitePlace K) {ρ : ℝ} (hρ : 0 < ρ) :
    posRealElem w (ρ ^ w.mult) = psi w ρ := by
  unfold posRealElem psi
  split_ifs with hw
  · simp [InfinitePlace.mult, hw]
  · simp [InfinitePlace.mult, hw, Real.sqrt_sq hρ.le]

private theorem real_hom_unique {A : Type} [Field A] [TopologicalSpace A] [T2Space A] (f g : ℝ →+* A)
    (hf : Continuous f) (hg : Continuous g) : f = g := by
  have h := Rat.denseRange_cast (𝕜 := ℝ) |>.equalizer hf hg (funext fun q => by simp)
  exact RingHom.ext (congrFun h)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem posIdele_fst {K : Type} [Field K] [NumberField K] (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace K) :
    ((posIdele ρ hρ : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).1 w = psi w ρ := by
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  exact posRealElem_eq w hρ

private theorem inf_posIdele (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace E) :
    InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) (((posIdele ρ hρ : IdeleGroup F) : NumberField.AdeleRing (𝓞 F) F).1) w =
      ((posIdele ρ hρ : IdeleGroup E) : NumberField.AdeleRing (𝓞 E) E).1 w := by
  have hx : ((posIdele ρ hρ : IdeleGroup F) : NumberField.AdeleRing (𝓞 F) F).1 =
      (RingHom.pi fun v : InfinitePlace F => psi v) ρ := funext fun v => posIdele_fst ρ hρ v
  rw [hx, posIdele_fst]
  have hc : Continuous (((Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp
      (InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))).comp
        (RingHom.pi fun v : InfinitePlace F => psi v)) :=
    (continuous_apply w).comp (InfinitePlace.continuous_infiniteAdeleRingMap.comp
      (continuous_pi fun v => continuous_psi v))
  exact congrArg (fun f : ℝ →+* w.Completion => f ρ) (real_hom_unique _ (psi w) hc (continuous_psi w))

private theorem fin_posIdele {K : Type} [Field K] [NumberField K] (ρ : ℝ) (hρ : 0 < ρ) :
    ((posIdele ρ hρ : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).2 = 1 :=
  IsDedekindDomain.FiniteAdeleRing.ext K fun v => posIdele_finite ρ hρ v

private theorem adeleMap_posIdele (ρ : ℝ) (hρ : 0 < ρ) :
    AdeleBaseChange.adeleMap F E ((posIdele ρ hρ : IdeleGroup F) : NumberField.AdeleRing (𝓞 F) F) =
      ((posIdele ρ hρ : IdeleGroup E) : NumberField.AdeleRing (𝓞 E) E) := by
  rw [AdeleBaseChange.adeleMap_apply]
  refine Prod.ext (funext fun w => inf_posIdele ρ hρ w) ?_
  change AdeleBaseChange.finiteAdeleMap F E _ = _
  rw [fin_posIdele, fin_posIdele, map_one]

private theorem exponent (n : ℕ) (hn : 0 < n) (s : {r : ℝ // 0 < r}) :
    rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹ (s ^ Module.finrank F E) =
      rpowHom ((n * Module.finrank ℚ F : ℝ))⁻¹ s := by
  refine Subtype.ext ?_
  change ((s ^ Module.finrank F E : {r : ℝ // 0 < r}) : ℝ) ^ ((n * Module.finrank ℚ E : ℝ))⁻¹ =
    (s : ℝ) ^ ((n * Module.finrank ℚ F : ℝ))⁻¹
  have hk : Module.finrank ℚ F * Module.finrank F E = Module.finrank ℚ E := Module.finrank_mul_finrank ℚ F E
  have hk0 : (Module.finrank F E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hd : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [Positive.val_pow, ← Real.rpow_natCast, ← Real.rpow_mul s.2.le, ← hk]
  congr 1
  push_cast
  field_simp

theorem UpperTheory.centralSection_baseChange :
    CentBC := by
  intro F E _ _ _ _ _ n s
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hn : 0 < n := i.pos
  have h1 : centralSection E n (s ^ Module.finrank F E) =
      diagUnits n fun _ => posIdeleHom E (rpowHom ((n * Module.finrank ℚ F : ℝ))⁻¹ s) := by
    rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, exponent n hn, scalarUnits_apply]
  have h2 : centralSection F n s =
      diagUnits n fun _ => posIdeleHom F (rpowHom ((n * Module.finrank ℚ F : ℝ))⁻¹ s) := by
    rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply]
  rw [h1, h2, coe_diagUnits]
  change AdeleBaseChange.adeleMap F E (((diagUnits n fun _ => posIdeleHom F _ : AdelicGLn.AdelicGL F n)).val i j) = _
  rw [coe_diagUnits]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdeleHom_apply, posIdeleHom_apply]
    exact adeleMap_posIdele _ _
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]
end
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.AdeleGaloisActionBaseChangeCompat
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped NumberField.AdeleRing TensorProduct

open PositivityTheory.Rg.Tf.Loc

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galOf_tmul' {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B]
    (e : E ⊗[F] A ≃ₐ[E] B) (σ : E ≃ₐ[F] E) (l : E) (a : A) :
    galOf e σ (e (l ⊗ₜ a)) = e (σ l ⊗ₜ a) := by
  simp [galOf]

private theorem tensor_fst (l : E) (x : 𝔸[F]) :
    (adeleTensorEquiv F E (l ⊗ₜ x)).1 =
      GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E) (l ⊗ₜ x.1) := by
  rw [adeleTensorEquiv_tmul, GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul']
  rfl

private theorem tensor_atFin (v : HeightOneSpectrum (𝓞 F)) (l : E) (x : 𝔸[F]) :
    atFin v (adeleTensorEquiv F E (l ⊗ₜ x)) = tensorEquiv' E v (l ⊗ₜ x.2 v) := by
  funext ⟨w, hw⟩
  obtain rfl : below F w = v := (below_eq_iff w v).2 hw
  exact adeleTensorEquiv_tmul_snd l x w

private theorem gal_fst (σ : E ≃ₐ[F] E) (a : 𝔸[E]) : (galAd σ a).1 = galInf σ a.1 := by
  obtain ⟨t, rfl⟩ := (adeleTensorEquiv F E).surjective a
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l x =>
    rw [galAd, galOf_tmul', tensor_fst, tensor_fst, galInf, galOf_tmul']
  | add s t hs ht =>
    rw [map_add (f := _), map_add (f := _)]
    change ((galAd σ) _).1 + ((galAd σ) _).1 = galInf σ (_ + _)
    rw [map_add (f := _), hs, ht]

private theorem gal_atFin (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸[E]) :
    atFin v (galAd σ a) = galFin σ v (atFin v a) := by
  obtain ⟨t, rfl⟩ := (adeleTensorEquiv F E).surjective a
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l x =>
    rw [galAd, galOf_tmul', tensor_atFin, tensor_atFin, galFin, galOf_tmul']
  | add s t hs ht =>
    simp only [map_add (f := _), hs, ht]

private theorem adele_atFin (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸[F]) :
    atFin v (adeleMap F E a) = incFin E v (a.2 v) := by
  funext ⟨w, hw⟩
  obtain rfl : below F w = v := (below_eq_iff w v).2 hw
  rfl

private theorem gal_adele (σ : E ≃ₐ[F] E) (a : 𝔸[F]) : galAd σ (adeleMap F E a) = adeleMap F E a := by
  have h : adeleMap F E a = adeleTensorEquiv F E ((1 : E) ⊗ₜ a) := by
    rw [adeleTensorEquiv_tmul, map_one, one_mul]
  rw [h, galAd, galOf_tmul', map_one]

private theorem gal_inf (σ : E ≃ₐ[F] E) (x : InfiniteAdeleRing F) :
    galInf σ (infMap F E x) = infMap F E x := by
  have h : infMap F E x =
      GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E) ((1 : E) ⊗ₜ x) := by
    rw [GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul]
  rw [h, galInf, galOf_tmul', map_one]

private theorem gal_algebraMap (σ : E ≃ₐ[F] E) (l : E) :
    galAd σ (algebraMap E 𝔸[E] l) = algebraMap E 𝔸[E] (σ l) := by
  have h (m : E) : algebraMap E 𝔸[E] m = adeleTensorEquiv F E (m ⊗ₜ (1 : 𝔸[F])) := by
    rw [adeleTensorEquiv_tmul, map_one, mul_one]
  rw [h l, galAd, galOf_tmul', ← h]

private theorem mapGL_square {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (n : ℕ) (f : A →+* B) (g : B →+* D) (h : A →+* C) (k : C →+* D) (H : ∀ a, g (f a) = k (h a))
    (x : GL (Fin n) A) : mapGL n g (mapGL n f x) = mapGL n k (mapGL n h x) :=
  Units.ext (by ext i j; simpa using H _)

end

theorem UpperTheory.adele_galois_action_baseChange_compat :
    Compat := by
  intro F E _ _ _ _ _ σ n
  refine ⟨fun g => ?_, fun v g => ?_, fun g => ?_, fun v g => ?_, fun g => ?_, fun g => ?_, fun δ => ?_, fun γ => ?_⟩
  · exact mapGL_square n _ _ _ _ (gal_fst σ) g
  · exact mapGL_square n _ _ _ _ (gal_atFin σ v) g
  · exact mapGL_square n _ _ _ _ (fun _ => rfl) g
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change atFin v (adeleMap F E ((g : Matrix (Fin n) (Fin n) 𝔸[F]) i j)) = incFin E v ((finAt v g : Matrix (Fin n) (Fin n) _) i j)
    rw [finAt_apply]
    exact adele_atFin v _
  · refine Units.ext ?_
    ext i j
    simpa using gal_adele σ _
  · refine Units.ext ?_
    ext i j
    simpa using gal_inf σ _
  · refine Units.ext ?_
    ext i j
    exact gal_algebraMap σ ((δ : Matrix (Fin n) (Fin n) E) i j)
  · refine Units.ext ?_
    ext i j
    exact adeleMap_algebraMap (K := F) (L := E) ((γ : Matrix (Fin n) (Fin n) F) i j)
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.FinAtMapGLGalAdMemIwahori
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private theorem val_lt_iff' {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y : w.adicCompletion E) : ValuativeRel.valuation (w.adicCompletion E) y < 1 ↔ ‖y‖ < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one,
    Valued.toNormedField.norm_lt_one_iff]

private theorem val_le_iff' {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y : w.adicCompletion E) : ValuativeRel.valuation (w.adicCompletion E) y ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one,
    Valued.toNormedField.norm_le_one_iff]

private theorem val_eq_iff' {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y : w.adicCompletion E) : ValuativeRel.valuation (w.adicCompletion E) y = 1 ↔ ‖y‖ = 1 := by
  rw [le_antisymm_iff, le_antisymm_iff, val_le_iff', not_iff_not.1 (by
    rw [not_le, not_le]; exact val_lt_iff' w y : ¬ (1 ≤ ValuativeRel.valuation (w.adicCompletion E) y) ↔ ¬ (1 ≤ ‖y‖))]

theorem UpperTheory.finAt_mapGL_galAd_mem_iwahori :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (g : AdelicGLn.AdelicGL E n),
        finAt w g ∈ GLnLocal.iwahori (w.adicCompletion E) n →
        finAt (σ • w) (mapGL n (galAd σ) g : AdelicGLn.AdelicGL E n) ∈ GLnLocal.iwahori ((σ • w).adicCompletion E) n := by
  intro F E _ _ _ _ _ σ n w g hg
  have key : ∀ i j, ‖finAt (σ • w) (mapGL n (galAd σ) g : AdelicGLn.AdelicGL E n) i j‖ = ‖finAt w g i j‖ :=
    fun i j => (UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ (g i j)).1 w
  obtain ⟨h1, h2, h3⟩ := (GLnLocal.mem_iwahori_iff _ n).1 hg
  refine (GLnLocal.mem_iwahori_iff _ n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [val_le_iff', key]; exact (val_le_iff' w _).1 (h1 i j)
  · rw [val_lt_iff', key]; exact (val_lt_iff' w _).1 (h2 i j hij)
  · rw [val_eq_iff', key]; exact (val_eq_iff' w _).1 (h3 i)
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.HaarQuotientSubgroup
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory

theorem UpperTheory.haar_quotient_subgroup :
    QSub := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ H hH μ j ν hp Φ hΦ hi
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  obtain ⟨ρ₀, -, hρ₀, -⟩ := normEx H T μ j ν hp
  have hemb : MeasurableEmbedding (Subtype.val : H → G) := MeasurableEmbedding.subtype_coe hH.measurableSet
  have hinj : Function.Injective (Subtype.val : H → G) := Subtype.val_injective
  have hex : ∃ ρ, IsNormAlong (fun x : H => (x : G)) (fun t => (j t : G)) ν ρ := by
    refine ⟨Function.extend Subtype.val (fun x : H => (ρ₀ x : ENNReal)) 0,
      hemb.measurable_extend hρ₀.1 measurable_const, fun x => ?_⟩
    have e : ∀ t, Function.extend Subtype.val (fun x : H => (ρ₀ x : ENNReal)) 0 ((j t : G) * (x : G))
        = (ρ₀ (j t * x) : ENNReal) := fun t => by
      rw [← Subgroup.coe_mul]
      exact hinj.extend_apply _ _ _
    simp only [e]
    exact hρ₀.2 x
  unfold quotInt
  rw [dite_eq_left hex]
  have hn : IsNrm j ν (fun x : H => hex.choose (x : G)) :=
    ⟨hex.choose_spec.1.comp measurable_subtype_coe, fun x => by
      simpa only [Subgroup.coe_mul] using hex.choose_spec.2 x⟩
  exact ((quotEq H T μ j ν hp Φ hΦ hi _ hn).2.2).symm
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.SeparableLocalOfSeparableScalar
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.separableLocal_of_separableScalar :
    SepSc → CentLoc → SepLoc := by
  intro hS hC F _ _ n γ hγ
  have hsep : (γ : Matrix (Fin n) (Fin n) F).charpoly.Separable := hγ
  have hI : ((pI F n (AdelicGLn.diagonal F n γ)).val : Matrix (Fin n) (Fin n) (InfiniteAdeleRing F)) =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F (InfiniteAdeleRing F)) := by
    ext a b
    rfl
  have hIs : (pI F n (AdelicGLn.diagonal F n γ)).val.charpoly.Separable := by
    rw [hI, Matrix.charpoly_map]
    exact hsep.map
  refine ⟨hIs, fun s => ?_, fun v => ?_⟩
  · obtain ⟨⟨r, hr⟩, -⟩ := hC F n ⟨Real.exp s, Real.exp_pos s⟩
    have h := hr (pI F n (AdelicGLn.diagonal F n γ))
    have h' : (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)).val =
        (r : InfiniteAdeleRing F) • (pI F n (AdelicGLn.diagonal F n γ)).val := h
    rw [h']
    exact hS _ n r _ hIs
  · have hv : ((finAt v (AdelicGLn.diagonal F n γ)).val : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
        (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F (v.adicCompletion F)) := by
      ext a b
      rfl
    rw [hv, Matrix.charpoly_map]
    exact hsep.map
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.BaseChangeTrivialExtension
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped TensorProduct

private theorem galOf_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : E ⊗[F] A ≃ₐ[E] B) :
    galOf e (1 : E ≃ₐ[F] E) = RingHom.id _ := by
  ext x
  have h : Algebra.TensorProduct.map (((1 : E ≃ₐ[F] E) : E →ₐ[F] E)) (AlgHom.id F A) = AlgHom.id F _ := by
    ext <;> simp
  simp only [galOf, RingHom.comp_apply, h]
  simp

private theorem infMap_self (F : Type) [Field F] [NumberField F] : infMap F F = RingHom.id _ := by
  have hd := InfiniteAdeleRing.denseRange_algebraMap F
  have h1 : Continuous (infMap F F) := InfinitePlace.continuous_infiniteAdeleRingMap
  have := hd.equalizer h1 continuous_id (funext fun k => by
    simpa using InfinitePlace.infiniteAdeleRingMap_algebraMap (K := F) (L := F) k)
  exact RingHom.ext fun x => congrFun this x

private theorem incFin_bij (F : Type) [Field F] [NumberField F] (v : Pl F) : Function.Bijective (incFin F v) := by
  have h : ∀ x, incFin F v x = tensorEquiv' F v ((1 : F) ⊗ₜ[F] x) := by
    intro x
    rw [tensorEquiv'_tmul, map_one, one_mul]
    rfl
  have hb : Function.Bijective (fun x : v.adicCompletion F => (1 : F) ⊗ₜ[F] x) :=
    (TensorProduct.lid F (v.adicCompletion F)).symm.bijective
  have : (incFin F v : _ → _) = tensorEquiv' F v ∘ (fun x : v.adicCompletion F => (1 : F) ⊗ₜ[F] x) := funext h
  rw [this]
  exact (tensorEquiv' F v).bijective.comp hb

theorem UpperTheory.baseChange_trivial_extension :
    Triv := by
  intro F _ _
  refine ⟨galOf_one' _, infMap_self F, fun v => ⟨galOf_one' _, incFin_bij F v⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.AdicCompletionIntegersBaseChangeIff
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global.SemiLocal GroundTheory.Automorphic ValuativeRel

private theorem mem_integers_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) : x ∈ 𝒪[v.adicCompletion K] ↔ Valued.v x ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  exact (ValuativeRel.isEquiv (valuation (v.adicCompletion K)) Valued.v).le_one_iff_le_one

private theorem completionMap_mem_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v) (x : v.adicCompletion F) :
    completionMap v w.1 x ∈ 𝒪[w.1.adicCompletion E] ↔ x ∈ 𝒪[v.adicCompletion F] := by
  rw [mem_integers_iff, mem_integers_iff, valued_completionMap]
  exact pow_le_one_iff (Ideal.ramificationIdx_pos (R := 𝓞 F) w.1.asIdeal).ne'

theorem UpperTheory.adicCompletion_integers_baseChange_iff :
    UnitIff := by
  intro F E _ _ _ _ _ n v t
  have key : ∀ w : PlacesOver E v,
      mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) (mapGL n (incFin E v) t) ∈
        GLnLocal.integralGL (w.1.adicCompletion E) n ↔ t ∈ KF F n v := by
    intro w
    have hc : ∀ s : GL (Fin n) (v.adicCompletion F),
        mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) (mapGL n (incFin E v) s) =
          mapGL n (completionMap v w.1) s := fun s => Units.ext (Matrix.ext fun i j => rfl)
    rw [hc, GLnLocal.mem_integralGL_iff, GLnLocal.mem_integralGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => completionMap_mem_iff v w _)
      (forall₂_congr fun i j => completionMap_mem_iff v w _)
  constructor
  · intro h
    have := v.isMaximal
    obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
    let w : PlacesOver E v := ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, hQv⟩
    exact (key w).1 (h w)
  · intro h w
    exact (key w).2 h
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.MaximalCompactNormOfUnitCriterion
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal

theorem UpperTheory.maximalCompactNorm_of_unit_criterion :
    K1 → Triv → UnitIff → Compat → SelmerRankBoundLaurent := by
  intro hK hT hU hC F _ _ n hn γ hγ
  have hincl : PositivityTheory.Rg.Tf.Loc.incl γ = γ := by
    ext i j
    rfl
  have hnorm : PositivityTheory.Rg.Tf.Loc.normGL (1 : F ≃ₐ[F] F) γ = PositivityTheory.Rg.Tf.Loc.incl γ := by
    rw [hincl, PositivityTheory.Rg.Tf.Loc.normGL, Module.finrank_self]
    simp [PositivityTheory.Rg.Tf.Loc.twNorm]
  have h1 : ∀ τ : F ≃ₐ[F] F, τ ∈ Subgroup.zpowers (1 : F ≃ₐ[F] F) := fun τ => by
    have : τ = 1 := AlgEquiv.ext fun x => τ.commutes x
    rw [this]
    exact one_mem _
  obtain ⟨-, -, -, c4, -, -, -, c8⟩ := hC F F 1 n
  filter_upwards [hK F F 1 h1 n hn γ γ hγ hnorm] with v hv x
  have hdiag : mapGL n (atFin v) (AdelicGLn.diagonal F n γ) =
      mapGL n (incFin F v) (finAt v (AdelicGLn.diagonal F n γ)) := by
    have h := c4 v (AdelicGLn.diagonal F n γ)
    rw [c8, hincl] at h
    exact h
  have hgal : ∀ y : GL (Fin n) (CompletionsOver F v), mapGL n (galFin (1 : F ≃ₐ[F] F) v) y = y := fun y => by
    rw [((hT F).2.2 v).1]
    ext i j
    rfl
  have key := hv (mapGL n (incFin F v) x)
  rw [hdiag, hgal, ← map_inv, ← map_mul, ← map_mul, hU F F n v] at key
  rw [key]
  constructor
  · rintro ⟨t, ht, y, hy, e⟩
    refine ⟨t, ht, t⁻¹ * x, ?_, by group⟩
    rw [← hU F F n v, map_mul, map_inv, e, inv_mul_cancel_left]
    exact hy
  · rintro ⟨t, ht, y, hy, rfl⟩
    exact ⟨t, ht, mapGL n (incFin F v) y, (hU F F n v y).2 hy, map_mul _ _ _⟩
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.TwistedNormCentralOfBaseChangeCompat
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem pow_fix {G : Type} [Group G] (θ : Monoid.End G) (z : G) (hz : θ z = z) (m : ℕ) :
    (θ ^ m) z = z := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ_apply, hz, ih]

private theorem twNorm_central {G : Type} [Group G] (θ : Monoid.End G) (z : G) (hz : θ z = z)
    (hc : ∀ g, z * g = g * z) (m : ℕ) (δ : G) :
    twNorm θ m (z * δ) = z ^ m * twNorm θ m δ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [twNorm_succ, twNorm_succ, ih, map_mul, pow_fix θ z hz m, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc (twNorm θ m δ) z, ← hc (twNorm θ m δ), mul_assoc]

theorem UpperTheory.twistedNorm_central_of_baseChange_compat :
    Compat → CentLoc → CentBC → ZNorm := by
  intro hC hL hB F E _ _ _ _ _ _ σ _ n _ s δ
  have hl : (Module.finrank F E : ℝ) ≠ 0 := by
    have : 0 < Module.finrank F E := Module.finrank_pos
    exact_mod_cast this.ne'
  have c3 := (hC F E σ n).2.2.1
  have c6 := (hC F E σ n).2.2.2.2.2.1

  have e1 : (⟨Real.exp (s / Module.finrank F E), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) ^ Module.finrank F E
      = ⟨Real.exp s, Real.exp_pos s⟩ := by
    apply Subtype.ext
    have : ((⟨Real.exp (s / Module.finrank F E), Real.exp_pos _⟩ ^ Module.finrank F E : {r : ℝ // 0 < r}) : ℝ) = Real.exp (s / Module.finrank F E) ^ Module.finrank F E := rfl
    rw [this, ← Real.exp_nat_mul, mul_div_cancel₀ _ hl]
  have hz : pI E n (zA E n s) =
      mapGL n (infMap F E) (pI F n (zA F n (s / Module.finrank F E))) := by
    rw [← c3, hB F E n, e1]
  have hfix : mapGL n (galInf σ) (pI E n (zA E n s)) = pI E n (zA E n s) := by
    rw [hz]; exact c6 _
  have hcen := (hL E n ⟨Real.exp s, Real.exp_pos s⟩).2.1
  have hpow : pI E n (zA E n s) ^ Module.finrank F E =
      mapGL n (infMap F E) (pI F n (zA F n s)) := by
    rw [← c3, hB F E n, ← map_pow, ← map_pow]
  exact (twNorm_central (mapGL n (galInf σ)) _ hfix hcen _ δ).trans (by rw [hpow])
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.TorusCommutativeOfCentralizerCommutative
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
private theorem cent_comm_of {F R : Type} [Field F] [CharZero F] [CommRing R] (hC : CentComm) (f : F →+* R) {n : ℕ}
    (γ : GL (Fin n) F) (hγ : (γ : Matrix (Fin n) (Fin n) F).charpoly.Separable) (D : GL (Fin n) R)
    (hD : (D : Matrix (Fin n) (Fin n) R) = (γ : Matrix (Fin n) (Fin n) F).map f) (s t : GL (Fin n) R)
    (hs : s * D = D * s) (ht : t * D = D * t) : s * t = t * s := by
  have hs' : (s : Matrix (Fin n) (Fin n) R) * (γ : Matrix (Fin n) (Fin n) F).map f =
      (γ : Matrix (Fin n) (Fin n) F).map f * (s : Matrix (Fin n) (Fin n) R) := by
    rw [← hD]
    exact congrArg Units.val hs
  have ht' : (t : Matrix (Fin n) (Fin n) R) * (γ : Matrix (Fin n) (Fin n) F).map f =
      (γ : Matrix (Fin n) (Fin n) F).map f * (t : Matrix (Fin n) (Fin n) R) := by
    rw [← hD]
    exact congrArg Units.val ht
  exact Units.ext (hC F R f n _ hγ _ _ hs' ht')

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.torusCommutative_of_centralizerCommutative :
    CentComm → TComm := by
  intro hC F _ _ n γ hγ
  have hsep : (γ : Matrix (Fin n) (Fin n) F).charpoly.Separable := hγ
  have hA : ∀ s t : GA F n, s * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * s →
      t * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * t → s * t = t * s := by
    refine cent_comm_of hC (algebraMap F _) γ hsep _ ?_
    ext a b
    rfl
  refine ⟨fun s t => ?_, fun s t => ?_, fun v s t => ?_, fun γ₁ h₁ s t => ?_⟩
  · exact Subtype.ext (hA _ _ (Subgroup.mem_centralizer_singleton_iff.1 s.2)
      (Subgroup.mem_centralizer_singleton_iff.1 t.2))
  · refine Subtype.ext (cent_comm_of hC (algebraMap F (InfiniteAdeleRing F)) γ hsep _ ?_ _ _
      (Subgroup.mem_centralizer_singleton_iff.1 s.2) (Subgroup.mem_centralizer_singleton_iff.1 t.2))
    ext a b
    rfl
  · refine Subtype.ext (cent_comm_of hC (algebraMap F (v.adicCompletion F)) γ hsep _ ?_ _ _
      (Subgroup.mem_centralizer_singleton_iff.1 s.2) (Subgroup.mem_centralizer_singleton_iff.1 t.2))
    ext a b
    rfl
  · have key : ∀ u : Subgroup.centralizer {γ₁}, u.1.1 * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * u.1.1 := by
      intro u
      rw [← h₁]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 u.2)
    exact Subtype.ext (Subtype.ext (hA _ _ (key s) (key t)))
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.TwistedNormLocalOfCompat
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem twNorm_hom' {G G' : Type} [Group G] [Group G'] (f : G →* G') (θ : Monoid.End G)
    (θ' : Monoid.End G') (h : ∀ x, f (θ x) = θ' (f x)) (m : ℕ) (δ : G) :
    f (PositivityTheory.Rg.Tf.Loc.twNorm θ m δ) = PositivityTheory.Rg.Tf.Loc.twNorm θ' m (f δ) := by
  have hp : ∀ (i : ℕ) (x : G), f ((θ ^ i) x) = (θ' ^ i) (f x) := fun i => by
    induction i with
    | zero => intro x; rfl
    | succ i ih =>
      intro x
      rw [PositivityTheory.Rg.Tf.Loc.pow_succ_apply', PositivityTheory.Rg.Tf.Loc.pow_succ_apply', h, ih]
  induction m with
  | zero => simp
  | succ m ih => rw [PositivityTheory.Rg.Tf.Loc.twNorm_succ, PositivityTheory.Rg.Tf.Loc.twNorm_succ, map_mul, ih, hp]

theorem UpperTheory.twistedNorm_local_of_compat :
    Compat → LocNorm := by
  intro hC F E _ _ _ _ _ _ σ _ n _ δ γ hδ
  obtain ⟨h1, h2, h3, h4, -, -, h7, h8⟩ := hC F E σ n
  have hdiag : GroundTheory.Automorphic.AdelicGLn.diagonal E n (PositivityTheory.Rg.Tf.Loc.normGL σ δ) =
      mapGL n (GroundTheory.Global.AdeleBaseChange.adeleMap F E) (GroundTheory.Automorphic.AdelicGLn.diagonal F n γ) := by
    rw [hδ, h8]
  constructor
  · have key := twNorm_hom' ((pI E n).comp (GroundTheory.Automorphic.AdelicGLn.diagonal E n)) (PositivityTheory.Rg.Tf.Loc.sigmaGL σ)
      (mapGL n (galInf σ)) (fun x => by
        simp only [MonoidHom.comp_apply]
        rw [← h7, h1]
        rfl) (Module.finrank F E) δ
    simp only [MonoidHom.comp_apply] at key
    rw [← key]
    change pI E n (GroundTheory.Automorphic.AdelicGLn.diagonal E n (PositivityTheory.Rg.Tf.Loc.normGL σ δ)) = _
    rw [hdiag, h3]
  · intro v
    have key := twNorm_hom' ((pE E n v).comp (GroundTheory.Automorphic.AdelicGLn.diagonal E n)) (PositivityTheory.Rg.Tf.Loc.sigmaGL σ)
      (mapGL n (galFin σ v)) (fun x => by
        simp only [MonoidHom.comp_apply]
        rw [← h7, h2]
        rfl) (Module.finrank F E) δ
    simp only [MonoidHom.comp_apply] at key
    rw [← key]
    change pE E n v (GroundTheory.Automorphic.AdelicGLn.diagonal E n (PositivityTheory.Rg.Tf.Loc.normGL σ δ)) = _
    rw [hdiag, h4]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionLocalScalar
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.SemiLocal

private theorem centralSection_val (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}) :
    ∃ u : GroundTheory.Global.IdeleGroup K, (∀ v, ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).2 v = 1) ∧
      ((centralSection K n s : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) =
        Matrix.diagonal fun _ => ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K) := by
  refine ⟨posIdeleHom K (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s), fun v => ?_, ?_⟩
  · rw [posIdeleHom_apply]
    exact posIdele_finite _ _ v
  · rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits]

theorem UpperTheory.centralSection_local_scalar :
    CentLoc := by
  intro K _ _ n s
  obtain ⟨u, hf, hu⟩ := centralSection_val K n s
  have hI : ∀ i j, ((pI K n (centralSection K n s) : GL (Fin n) (InfiniteAdeleRing K)) :
      Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j =
      (Matrix.diagonal fun _ => ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).1 :
        Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j := by
    intro i j
    change (((centralSection K n s : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).1 = _
    rw [hu]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
      rfl
  have hI' : ((pI K n (centralSection K n s) : GL (Fin n) (InfiniteAdeleRing K)) :
      Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) =
      Matrix.diagonal fun _ => ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).1 :=
    Matrix.ext hI
  have hF : ∀ (i j : Fin n), (((centralSection K n s : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 =
      ((1 : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 := by
    intro i j
    rw [hu]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact FiniteAdeleRing.ext K hf
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  refine ⟨⟨Units.map (RingHom.toMonoidHom (α := AdeleRing (𝓞 K) K) (β := InfiniteAdeleRing K) (RingHom.fst _ _)) u, fun g => ?_⟩,
    fun g => ?_, fun v => ?_, fun F _ _ _ v => ?_⟩
  · rw [Units.val_mul, hI']
    ext i j
    rw [Matrix.diagonal_mul]
    rfl
  · refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hI']
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [pF_apply]
    change (((centralSection K n s : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 v = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [hF]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      rfl
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
      rfl
  · refine Units.ext (Matrix.ext fun i j => funext fun w => ?_)
    change (((centralSection K n s : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 w.1 = (1 : Matrix (Fin n) (Fin n) (CompletionsOver K v)) i j w
    rw [hF]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      rfl
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
      rfl
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.OrbitalSideExtensionOfAbsoluteConvergence
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory NumberField IsDedekindDomain Topology Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

private theorem cent_closed {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] [T2Space G] (g : G) :
    IsClosed ((Subgroup.centralizer {g} : Subgroup G) : Set G) := by
  have h : ((Subgroup.centralizer {g} : Subgroup G) : Set G) = {x | x * g = g * x} := by
    ext x
    exact Subgroup.mem_centralizer_singleton_iff
  rw [h]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

theorem UpperTheory.orbitalSideExtension_of_absoluteConvergence :
    SideAbs → RPF → RPE → RPCen → UniLoc → UniOf → TComm → SepLoc → CentLoc → Compat → GalCont → LocEmb → UnitIff → LocNorm → BoundE → N3 → N5 → P2 → SideE := by
  intro hSA hRPF hRPE hRPC hUL hUO hTC hSL hCL hCo hGC hLE hUI hLN hBE hN3 hN5 hP2 F E _ _ _ _ _ _ σ hσ n hn _ _ _ _ _ _ _ _ μ μi m hμ hμi hm γ hγ δ hδ ν νi nv hν hνi hnv S a b ha hb hET hEE
    φi φ hφi hφc hφ hS
  obtain ⟨c1, c2, c3, c4, -⟩ := hCo F E σ n
  obtain ⟨g0, g1, g2⟩ := hGC F E σ n
  obtain ⟨l1, l2⟩ := hLE F E n
  obtain ⟨t1, t2, t3, -⟩ := hTC F n γ hγ
  have hG := hRPE F E n
  have hT := hRPC _ _ _ _ (pI F n) (pF F n) (KF F n) (hRPF F n) (AdelicGLn.diagonal F n γ)
  haveI : LocallyCompactSpace (TA γ) := (cent_closed _).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (TI γ) := (cent_closed _).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : ∀ v : Pl F, LocallyCompactSpace (TF γ v) :=
    fun v => (cent_closed _).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (TA γ) :=
    TopologicalSpace.Subtype.secondCountableTopology ((TA γ : Subgroup (GA F n)) : Set (GA F n))
  haveI : SecondCountableTopology (TI γ) :=
    TopologicalSpace.Subtype.secondCountableTopology ((TI γ : Subgroup _) : Set (GL (Fin n) (InfiniteAdeleRing F)))
  haveI : ∀ v : Pl F, SecondCountableTopology (TF γ v) := fun v =>
    TopologicalSpace.Subtype.secondCountableTopology ((TF γ v : Subgroup _) : Set (GL (Fin n) (v.adicCompletion F)))
  obtain ⟨uI, uV⟩ := hUL (Pl F) (GA E n) _ _ (pI E n) (fun v => pE E n v) (fun v => KE E n v) hG μ μi m hμ hμi hm
  have hZ : Continuous (zA E n) :=
    (continuous_centralSection (K := E) (n := n)).comp (Real.continuous_exp.subtype_mk _)
  have key := hSA (Pl F) (GA E n) (GL (Fin n) (InfiniteAdeleRing E)) (fun v => GL (Fin n) (CompletionsOver E v))
    (pI E n) (fun v => pE E n v) (fun v => KE E n v) (TA γ) (TI γ) (fun v => TF γ v)
    (cen (pI F n) (AdelicGLn.diagonal F n γ)) (fun v => cen (pF F n v) (AdelicGLn.diagonal F n γ))
    (fun v => (KF F n v).comap (TF γ v).subtype) hG hT
    ((mapGL n (adeleMap F E)).comp (TA γ).subtype) ((mapGL n (infMap F E)).comp (TI γ).subtype)
    (fun v => (mapGL n (incFin E v)).comp (TF γ v).subtype)
    (fun t => c3 t.1) (fun v t => c4 v t.1) (fun v t => (hUI F E n v t.1).symm)
    μ μi m ν νi nv
    ⟨hμ, (hN5 F E σ hσ n hn).1.comp (cent_closed _).isClosedEmbedding_subtypeVal, (hUO _ ν hν).2 t1⟩
    ⟨uI, (l1.comp (cent_closed _).isClosedEmbedding_subtypeVal), (hUO _ νi hνi).2 t2⟩
    (fun v => ⟨uV v, ((l2 v).comp (cent_closed _).isClosedEmbedding_subtypeVal), (hUO _ (nv v) (hnv v)).2 (t3 v)⟩)
    S a b ha hb hEE hET
    (mapGL n (galAd σ)) (mapGL n (galInf σ)) (fun v => mapGL n (galFin σ v)) c1 c2 g1 g2
    (AdelicGLn.diagonal E n δ) (zA E n) hZ
    (fun v s => (hCL E n ⟨Real.exp s, Real.exp_pos s⟩).2.2.2 F v)
    (fun t => (hN3 F E σ hσ n hn δ γ hγ hδ _).2 ⟨t.1, Subgroup.mem_centralizer_singleton_iff.1 t.2, rfl⟩)
    (fun D hD => by
      obtain ⟨C, hC, hCx⟩ := (hP2 F E σ hσ n hn).2 (pI F n (AdelicGLn.diagonal F n γ)) (pI E n (AdelicGLn.diagonal E n δ))
        (hSL F n γ hγ).1 (hLN F E σ hσ n hn δ γ hδ).1 D hD
      refine ⟨C, hC, fun x hx => ?_⟩
      obtain ⟨t, ht, y, hy, rfl⟩ := hCx x hx
      exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 ht⟩, y, hy, rfl⟩)
    (fun D hD => hBE F E σ hσ n hn (pI E n (AdelicGLn.diagonal E n δ)) D hD)
    φi φ hφi hφc hφ
    (fun v hv => by
      obtain ⟨e, hx⟩ := hS v hv
      refine ⟨e, fun x => ⟨fun h => ?_, ?_⟩⟩
      · obtain ⟨t, ht, y, hy, rfl⟩ := (hx x).1 h
        exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 ht⟩, y, hy, rfl⟩
      · rintro ⟨t, y, hy, rfl⟩
        exact (hx _).2 ⟨t.1, Subgroup.mem_centralizer_singleton_iff.1 t.2, y, hy, rfl⟩)
  have hc : ∀ (s : ℝ) (x : GL (Fin n) (InfiniteAdeleRing E)),
      x⁻¹ * (pI E n (zA E n s) * pI E n (AdelicGLn.diagonal E n δ)) * mapGL n (galInf σ) x =
        pI E n (zA E n s) * (x⁻¹ * pI E n (AdelicGLn.diagonal E n δ) * mapGL n (galInf σ) x) := by
    intro s x
    have h := (hCL E n ⟨Real.exp s, Real.exp_pos s⟩).2.1 x⁻¹
    rw [← mul_assoc x⁻¹, ← h]
    simp only [mul_assoc]
  refine ⟨key.1, ?_⟩
  simp only [hc]
  exact key.2
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.AdelicBoundOfCentralizerLocalization
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal Topology
open scoped NumberField.AdeleRing

noncomputable section

namespace UpperTheory.Bnd

variable (E : Type) [Field E] [NumberField E] (n : ℕ)

private def emb : GL (Fin n) (InfiniteAdeleRing E) →* GA E n where
  toFun x := (AdelicGLn.prodEquiv E n).symm (x, 1)
  map_one' := map_one (AdelicGLn.prodEquiv E n).symm
  map_mul' x y := by
    rw [← map_mul (AdelicGLn.prodEquiv E n).symm]
    simp

private theorem emb_apply (x : GL (Fin n) (InfiniteAdeleRing E)) :
    emb E n x = (AdelicGLn.prodEquiv E n).symm (x, 1) := rfl

private theorem continuous_emb : Continuous (emb E n) :=
  (AdelicGLn.prodEquiv E n).symm.continuous.comp (continuous_id.prodMk continuous_const)

private theorem prod_emb (x : GL (Fin n) (InfiniteAdeleRing E)) :
    AdelicGLn.prodEquiv E n (emb E n x) = (x, 1) := by
  rw [emb_apply]; exact (AdelicGLn.prodEquiv E n).apply_symm_apply _

private theorem pI_emb (x : GL (Fin n) (InfiniteAdeleRing E)) : pI E n (emb E n x) = x := by
  refine Units.ext ?_
  ext a b
  have h := AdelicGLn.prodEquiv_apply_fst E n (emb E n x) a b
  rw [prod_emb] at h
  exact h.symm

private theorem pE_emb {F : Type} [Field F] [NumberField F] [Algebra F E] (v : Pl F)
    (x : GL (Fin n) (InfiniteAdeleRing E)) : pE E n v (emb E n x) = 1 := by
  refine Units.ext (Matrix.ext fun a b => funext fun w => ?_)
  have h := AdelicGLn.prodEquiv_apply_snd E n (emb E n x) a b
  rw [prod_emb] at h
  change (((emb E n x : GL _ _) a b).2 : FiniteAdeleRing (𝓞 E) E) w.1 = _
  rw [← h]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> rfl

end UpperTheory.Bnd

open UpperTheory.Bnd in
theorem UpperTheory.adelicBound_of_centralizer_localization :
    N5 → Compat → CentLoc → RPE → BoundE := by
  intro hN hC hCL hR F E _ _ _ _ _ _ σ hσ n hn δ D hD
  have hRP := hR F E n
  obtain ⟨hC1, hC2, -⟩ := hC F E σ n

  have hz : ∀ s : ℝ, emb E n (pI E n (zA E n s)) = zA E n s := fun s =>
    hRP.ext _ _ (pI_emb E n _) fun v => by
      rw [pE_emb E n v]
      exact ((hCL E n ⟨Real.exp s, Real.exp_pos s⟩).2.2.2 F v).symm

  have hg : ∀ x, emb E n (mapGL n (galInf σ) x) = mapGL n (galAd σ) (emb E n x) := fun x =>
    hRP.ext _ _ (by rw [pI_emb, hC1, pI_emb]) fun v => by
      rw [pE_emb E n v, hC2, pE_emb E n v, map_one]
  have hm := (hN F E σ hσ n hn).2.2
  set d : GL (Fin n) (InfiniteAdeleRing E) →* {r : ℝ // 0 < r} := (detModule E n).comp (emb E n) with hd
  have hdc : Continuous fun y => (d y : ℝ) :=
    continuous_subtype_val.comp (continuous_detModule.comp (continuous_emb E n))
  have hdz : ∀ s : ℝ, (d (pI E n (zA E n s)) : ℝ) = Real.exp s := fun s => by
    simp only [hd, MonoidHom.comp_apply, hz]
    rw [zA, detModule_centralSection hn]
  have hds : ∀ x, d (mapGL n (galInf σ) x) = d x := fun x => by
    simp only [hd, MonoidHom.comp_apply, hg, hm]
  have hp : ∀ y, (d y : ℝ) ≠ 0 := fun y => (d y).2.ne'
  have hcont : Continuous fun y => Real.log ((d y : ℝ) / (d δ : ℝ)) :=
    (hdc.div_const _).log fun y => div_ne_zero (hp y) (hp δ)
  refine ⟨(fun y => Real.log ((d y : ℝ) / (d δ : ℝ))) '' D, hD.image hcont, fun s x hx => ⟨_, hx, ?_⟩⟩
  have e : d (pI E n (zA E n s) * (x⁻¹ * δ * mapGL n (galInf σ) x)) = d (pI E n (zA E n s)) * d δ := by
    rw [map_mul, map_mul, map_mul, hds, map_inv]
    congr 1
    rw [mul_comm (d x)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  change Real.log ((d _ : ℝ) / (d δ : ℝ)) = s
  rw [e, Positive.val_mul, hdz, mul_div_cancel_right₀ _ (hp δ), Real.log_exp]
end
end
