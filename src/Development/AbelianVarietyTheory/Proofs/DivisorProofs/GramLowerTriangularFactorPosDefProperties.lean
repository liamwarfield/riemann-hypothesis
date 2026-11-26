module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisInvariantPointDescendsToSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsListedFiniteGaloisExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelAffineCoverRadical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceMapOfTupleHasDivisor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefProperties
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

variable {s : ℕ} {G : Matrix (Fin s) (Fin s) ℂ}

theorem leadMinor_pos_of_posDef (h : G.PosDef) (j : ℕ) : 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0 := by
  have h1 : 0 < leadMinor G j := (h.submatrix Subtype.val_injective).det_pos
  rw [Complex.lt_def] at h1
  exact ⟨by simpa using h1.1, by simpa using h1.2.symm⟩

theorem ldPart_diag_of_posDef (h : G.PosDef) (i : Fin s) : 0 < grD G i ∧ ldPart G i i = grD G i := by
  obtain ⟨a1, a2⟩ := leadMinor_pos_of_posDef h ((i : ℕ) + 1)
  obtain ⟨b1, b2⟩ := leadMinor_pos_of_posDef h (i : ℕ)
  refine ⟨div_pos a1 b1, ?_⟩
  have e : (fun a : {a : Fin s // (a : ℕ) < (i : ℕ) + 1} => if a.1 = i then i else a.1) = Subtype.val := by
    funext a
    split_ifs with ha
    · exact ha.symm
    · rfl
  have ea : leadMinor G ((i : ℕ) + 1) = ((leadMinor G ((i : ℕ) + 1)).re : ℂ) :=
    Complex.ext (by simp) (by simpa using a2)
  have eb : leadMinor G (i : ℕ) = ((leadMinor G (i : ℕ)).re : ℂ) :=
    Complex.ext (by simp) (by simpa using b2)
  simp only [ldPart, Matrix.of_apply, grD]
  rw [e, Complex.ofReal_div, ← ea, ← eb]
  rfl

theorem ldPart_eq_zero_of_lt (G : Matrix (Fin s) (Fin s) ℂ) {i j : Fin s} (hij : i < j) : ldPart G i j = 0 := by
  have hij' : (i : ℕ) < j := hij
  simp only [ldPart, Matrix.of_apply]
  rw [Matrix.det_zero_of_row_eq (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩), zero_div]
  · intro h
    exact hij.ne (congrArg Subtype.val h)
  · funext b
    simp [Matrix.submatrix_apply]

theorem ldPart_posDef_spec : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ j, 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0) ∧ (∀ i, 0 < grD G i ∧ ldPart G i i = grD G i) ∧ (∀ i j, i < j → ldPart G i j = 0) ∧ IsUnit (ldPart G).det := by
  intro s G h
  refine ⟨leadMinor_pos_of_posDef h, ldPart_diag_of_posDef h, fun i j hij => ldPart_eq_zero_of_lt G hij, ?_⟩
  rw [Matrix.det_of_lowerTriangular (ldPart G) (fun i j hij => ldPart_eq_zero_of_lt G (by simpa using hij)),
    isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  obtain ⟨h1, h2⟩ := ldPart_diag_of_posDef h i
  rw [h2]
  exact_mod_cast h1.ne'

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLowerTriangularFactorPosDefPropertiesStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramLowerTriangularFactor_posDef_properties : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → (∀ j, 0 < (leadMinor G j).re ∧ (leadMinor G j).im = 0) ∧ (∀ i, 0 < grD G i ∧ ldPart G i i = grD G i) ∧ (∀ i j, i < j → ldPart G i j = 0) ∧ IsUnit (ldPart G).det := by
  first | exact @GlobalTheory.ChernCalc.ldPart_posDef_spec | exact GlobalTheory.ChernCalc.ldPart_posDef_spec | (intros; apply GlobalTheory.ChernCalc.ldPart_posDef_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionProjectiveOfPrincipalisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionProjectiveOfPrincipalisation
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogResProj

theorem exists_logResolution : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ T : Closeds X, genericPoint X ∉ T → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X), SmoothOfRelativeDimension D (π ≫ p) ∧ IsProjOver (π ≫ p) ∧ topologicalKrullDim Y = D ∧ π (genericPoint Y) = genericPoint X ∧ π.residueDegree (genericPoint Y) = 1 ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (⟨π ⁻¹' (T : Set X), T.isClosed.preimage π.continuous⟩ : Closeds Y)) := by
  intro hP F _ _ X _ p D hp hdim T hT
  obtain ⟨W', s, U, hW', hsm, hpr, hU, hiso⟩ := WeakRes.weak_resolution hP F X p D hp hdim
  have := hW'
  have g₁ := GlobalTheory.Published.generic_of_isIso_restrict s U hU
  let T' : Closeds W' := ⟨s ⁻¹' (T : Set X), T.isClosed.preimage s.continuous⟩
  let I : W'.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal T'
  have hIs : I.support = T' := by
    ext1; exact Scheme.IdealSheafData.coe_support_vanishingIdeal T'
  have hgW : genericPoint W' ∉ (T' : Set W') := by
    show s (genericPoint W') ∉ (T : Set X)
    rw [g₁.1]; exact hT
  have hI : I ≠ ⊥ := by
    intro h
    apply hgW
    have : I.support = ⊤ := by rw [h]; simp
    rw [← hIs, this]; trivial
  obtain ⟨Y, s', hY, hsm', hpr', -, hiso', -, hsnc⟩ := hP F D W' (s ≫ p) hW' hsm hpr I hI
  have := hY
  have hne : ((I.support.compl : W'.Opens) : Set W').Nonempty := ⟨genericPoint W', by
    show genericPoint W' ∉ (I.support : Set W'); rw [hIs]; exact hgW⟩
  have g₂ := GlobalTheory.Published.generic_of_isIso_restrict s' _ hne
  have hpL : LocallyOfFiniteType p := by
    obtain ⟨N, i, hi, rfl⟩ := hp
    have := isProper_str F N
    infer_instance
  have : Smooth (s ≫ p) := by haveI := hsm; exact SmoothOfRelativeDimension.smooth D _
  have : Smooth (s' ≫ s ≫ p) := by haveI := hsm'; exact SmoothOfRelativeDimension.smooth D _
  have hd₁ := GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict F X W' p (s ≫ p) s hpL inferInstance rfl U hU hiso
  have hd₂ := GlobalTheory.OpenDim.topologicalKrullDim_eq_of_isIso_restrict F W' Y (s ≫ p) (s' ≫ s ≫ p) s' inferInstance
    inferInstance rfl _ hne hiso'
  refine ⟨Y, hY, s' ≫ s, by simpa using hsm', by simpa using hpr', by rw [hd₂, hd₁, hdim], ?_, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply, g₂.1, g₁.1]
  · rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp, g₂.2, g₂.1, g₁.2, mul_one]
  · have hE : (I.comap s').support = ⟨(s' ≫ s) ⁻¹' (T : Set X), T.isClosed.preimage (s' ≫ s).continuous⟩ := by
      ext1
      rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, hIs]
      ext y; simp [T']
    rw [← hE]; exact hsnc

end GlobalTheory.LogResProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionProjectiveOfPrincipalisationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logResolution_projective_of_principalisation : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ T : Closeds X, genericPoint X ∉ T → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X), SmoothOfRelativeDimension D (π ≫ p) ∧ IsProjOver (π ≫ p) ∧ topologicalKrullDim Y = D ∧ π (genericPoint Y) = genericPoint X ∧ π.residueDegree (genericPoint Y) = 1 ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal (⟨π ⁻¹' (T : Set X), T.isClosed.preimage π.continuous⟩ : Closeds Y)) := by
  first | exact @GlobalTheory.LogResProj.exists_logResolution | exact GlobalTheory.LogResProj.exists_logResolution | (intros; apply GlobalTheory.LogResProj.exists_logResolution <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackGramMatricesIndependentOfFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackGramMatricesIndependentOfFrame
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

section Pull

variable {F : Type} [Field F] {σ : F →+* ℂ} {X Y : Var F}

theorem ratVal_eq_val_ratOf (y : CxPts X.str σ) {x : X.Fn} (hx : x ∈ (ratOf X).O (under y)) :
    ratVal x y = (ratOf X).val y.1 x := by
  obtain ⟨U, hy, a, e⟩ := (mem_O_ratOf.1 hx).exists_fnOf
  rw [← e, ratVal_fnOf (mem_ptsIn.2 hy), ← valF_fromSpecStalk]
  refine (GlobalTheory.ZH.RatModel.val_valF (M := ratOf X) ?_ a).symm
  rintro _ ⟨w, rfl⟩
  rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) w (IsLocalRing.closedPoint ℂ)]

theorem under_ptMap (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) (z : CxPts Y.str σ) :
    under (ptMap σ f hf z) = f (under z) := rfl

theorem ratVal_pull {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hφ : (ratOf X).IsHom (ratOf Y) φ f)
    (hf : f ≫ X.str = Y.str) (z : CxPts Y.str σ) {g : X.Fn} (hg : g ∈ (ratOf X).O (f (under z))) :
    ratVal (φ g) z = ratVal g (ptMap σ f hf z) := by
  rw [ratVal_eq_val_ratOf z (hφ.map_mem_O hg), ratVal_eq_val_ratOf (ptMap σ f hf z) hg]
  exact (hφ.val_comp z.1 _ hg).symm

end Pull

theorem pullGram_eq_of_frame : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ (z : CxPts Y.str σ), under (ptMap σ f hf z) = f (under z) ∧ ∀ A ∈ E.S (f (under z)), ∀ B ∈ E'.S (under z), ∀ τ, pullGram E H φ f hf B z τ = (B * (A.map φ)⁻¹).map (ratVal · z) τ * H A (ptMap σ f hf z) τ * ((B * (A.map φ)⁻¹).map (ratVal · z) τ)ᴴ := by
  intro F _ σ X Y ι m E E' φ f hf hR H hH z
  refine ⟨under_ptMap f hf z, ?_⟩
  intro A hA B hB τ
  have hA' : A ∈ E.S (under (ptMap σ f hf z)) := hA
  have hA₀ : (E.nonempty (under (ptMap σ f hf z))).choose ∈ E.S (f (under z)) :=
    (E.nonempty (under (ptMap σ f hf z))).choose_spec
  have hA₀' : (E.nonempty (under (ptMap σ f hf z))).choose ∈ E.S (under (ptMap σ f hf z)) :=
    (E.nonempty (under (ptMap σ f hf z))).choose_spec
  have htr := hH.trans (ptMap σ f hf z) mem_ptsIn_top A hA' _ hA₀' τ
  unfold pullGram
  rw [htr]
  generalize (E.nonempty (under (ptMap σ f hf z))).choose = A₀ at hA₀ hA₀'

  have hg : Par 0 ((ratOf Y).O (under z)).toSubring (B * (A₀.map φ)⁻¹) := hR.sub (under z) B hB A₀ hA₀
  have hc : Par 0 ((ratOf X).O (f (under z))).toSubring (A₀ * A⁻¹) := (Fr.mem_iff hA).1 hA₀
  have hh : Par 0 ((ratOf Y).O (under z)).toSubring ((A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn)) :=
    hc.map (φ : X.Fn →+* Y.Fn) fun x hx => hR.hom.map_mem_O hx
  have hprod : B * (A₀.map φ)⁻¹ * (A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn) = B * (A.map φ)⁻¹ := by
    change B * (A₀.map (φ : X.Fn →+* Y.Fn))⁻¹ * (A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn) = B * (A.map (φ : X.Fn →+* Y.Fn))⁻¹
    rw [Mat.map_mul, ← Mat.map_inv, mul_assoc, ← mul_assoc (A₀⁻¹.map _), ← Mat.map_mul,
      Mat.inv_mul (Fr.det_ne hA₀), Mat.map_one, one_mul, Mat.map_inv]
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := Y) (σ := σ) z
  have hmul := hg.map_mul_of hh (ratVal · z) ψ hψ
  rw [hprod] at hmul
  have hval : ((A₀ * A⁻¹).map (φ : X.Fn →+* Y.Fn)).map (ratVal · z) = (A₀ * A⁻¹).map (ratVal · (ptMap σ f hf z)) := by
    funext τ'
    ext i j
    exact ratVal_pull hR.hom hf z ((hc τ').1 i j)
  rw [hval] at hmul
  rw [hmul, Pi.mul_apply, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

end GlobalTheory.ChernCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackGramMatricesIndependentOfFrameStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ (z : CxPts Y.str σ), under (ptMap σ f hf z) = f (under z) ∧ ∀ A ∈ E.S (f (under z)), ∀ B ∈ E'.S (under z), ∀ τ, pullGram E H φ f hf B z τ = (B * (A.map φ)⁻¹).map (ratVal · z) τ * H A (ptMap σ f hf z) τ * ((B * (A.map φ)⁻¹).map (ratVal · z) τ)ᴴ := by
  first | exact @GlobalTheory.ChernCalc.pullGram_eq_of_frame | exact GlobalTheory.ChernCalc.pullGram_eq_of_frame | (intros; apply GlobalTheory.ChernCalc.pullGram_eq_of_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKerIdealDvd
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.DeRham (spOver spOver_comp)
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.KerPart

variable {k : Type} [Field k] {A B : AbVar k}

def KerPow (f : A ⟶ B) (c : ℕ) (H : Type) [CommRing H] [Algebra k H] (i : ptOver k H ⟶ A.X) : Prop :=
  (i ≫ f.hom = 1 ∧ i ^ c = 1) ∧
    ∀ (R : Type) [CommRing R] [Algebra k R] (x : ptOver k R ⟶ A.X), x ≫ f.hom = 1 → x ^ c = 1 →
      ∃! φ : H →ₐ[k] R, spMap φ.toRingHom ≫ i.left = x.left

theorem finrank_eq_of_kerPow {f : A ⟶ B} {c c' : ℕ} {H H' : Type} [CommRing H] [Algebra k H] [CommRing H']
    [Algebra k H'] {i : ptOver k H ⟶ A.X} {i' : ptOver k H' ⟶ A.X} (h : KerPow f c H i) (h' : KerPow f c' H' i')
    (e : ∀ (R : Type) [CommRing R] [Algebra k R] (x : ptOver k R ⟶ A.X), x ≫ f.hom = 1 → (x ^ c = 1 ↔ x ^ c' = 1)) :
    Module.finrank k H = Module.finrank k H' := by
  obtain ⟨φ, hφ, -⟩ := h.2 H' i' h'.1.1 ((e H' i' h'.1.1).2 h'.1.2)
  obtain ⟨ψ, hψ, -⟩ := h'.2 H i h.1.1 ((e H i h.1.1).1 h.1.2)
  have h1 : ψ.comp φ = AlgHom.id k H := by
    obtain ⟨χ, -, hχ⟩ := h.2 H i h.1.1 h.1.2
    refine (hχ _ ?_).trans (hχ _ ?_).symm
    · change spMap ((ψ : H' →+* H).comp (φ : H →+* H')) ≫ i.left = i.left
      rw [Cris.spMap_comp, Category.assoc]
      exact (congrArg (spMap (ψ : H' →+* H) ≫ ·) hφ).trans hψ
    · change spMap (RingHom.id H) ≫ i.left = i.left
      rw [Cris.spMap_id, Category.id_comp]
  have h2 : φ.comp ψ = AlgHom.id k H' := by
    obtain ⟨χ, -, hχ⟩ := h'.2 H' i' h'.1.1 h'.1.2
    refine (hχ _ ?_).trans (hχ _ ?_).symm
    · change spMap ((φ : H →+* H').comp (ψ : H' →+* H)) ≫ i'.left = i'.left
      rw [Cris.spMap_comp, Category.assoc]
      exact (congrArg (spMap (φ : H →+* H') ≫ ·) hψ).trans hφ
    · change spMap (RingHom.id H') ≫ i'.left = i'.left
      rw [Cris.spMap_id, Category.id_comp]
  exact (AlgEquiv.ofAlgHom φ ψ h2 h1).toLinearEquiv.finrank_eq

theorem pow_eq_one_of_comp {f : A ⟶ B} {g : B ⟶ A} {N : ℕ} (h : f ≫ g = N • 𝟙 A) {T : Over (Sp k)}
    (x : T ⟶ A.X) (hx : x ≫ f.hom = 1) : x ^ N = 1 := by
  have e := congrArg (fun u : A ⟶ A => x ≫ u.hom) h
  simp only [comp_hom, nsmul_hom, id_hom] at e
  rw [← Category.assoc, hx, MonObj.one_comp, MonObj.comp_pow, Category.comp_id] at e
  exact e.symm

section Tower

variable {p : ℕ} {G H : PDivGroup p k} (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B) (n : ℕ)

def kerPt : ptOver k (G.A n ⧸ kerIdeal ((t.map t' f.hom).app n)) ⟶ A.X :=
  spOver (Ideal.Quotient.mkₐ k (kerIdeal ((t.map t' f.hom).app n))) ≫ t.y n

theorem comp_eq_one_iff {R : Type} [CommRing R] [Algebra k R] (φ : G.A n →ₐ[k] R) :
    (spOver φ ≫ t.y n) ≫ f.hom = 1 ↔ kerIdeal ((t.map t' f.hom).app n) ≤ RingHom.ker φ := by
  let u : H.A n →ₐ[k] G.A n := (t.map t' f.hom).app n
  have hu : spOver u ≫ t'.y n = t.y n ≫ f.hom := t.map_y t' f.hom n
  rw [Category.assoc, ← hu, ← Category.assoc, spOver_comp, t'.eq_one_iff]
  exact (kerIdeal_le_ker_iff ((t.map t' f.hom).app n) φ).symm

theorem kerPow_kerPt : KerPow f (p ^ n) _ (kerPt t t' f n) := by
  let I := kerIdeal ((t.map t' f.hom).app n)
  let q := Ideal.Quotient.mkₐ k I
  refine ⟨⟨(comp_eq_one_iff t t' f n q).2 ?_, (t.exists_iff n _).1 ⟨q, rfl⟩⟩, ?_⟩
  · exact fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  · intro R _ _ x hx hp
    obtain ⟨φ, hφ⟩ := t.surj n R x hp
    have hI : I ≤ RingHom.ker φ := (comp_eq_one_iff t t' f n φ).1 (hφ ▸ hx)
    let ψ : G.A n ⧸ I →ₐ[k] R := Ideal.Quotient.liftₐ I φ (fun _ ha => hI ha)
    have hψ : ψ.comp q = φ := AlgHom.ext fun _ => rfl
    have hψx : spOver ψ ≫ kerPt t t' f n = x := by
      change spOver ψ ≫ (spOver q ≫ t.y n) = x
      rw [← Category.assoc, spOver_comp, hψ]
      exact hφ
    refine ⟨ψ, congrArg Over.Hom.left hψx, fun χ hχ => ?_⟩
    have hχx : spOver (χ.comp q) ≫ t.y n = x := by
      rw [← spOver_comp, Category.assoc]
      exact Over.OverMorphism.ext hχ
    exact Ideal.Quotient.algHom_ext k ((t.inj n R _ _ (hχx.trans hφ.symm)).trans hψ.symm)

end Tower

theorem finrank_quot_kerIdeal_dvd {p : ℕ} {G H : PDivGroup p k} (φ : G ⟶ H) (n : ℕ) :
    Module.finrank k (G.A n ⧸ kerIdeal (φ.app n)) ∣ p ^ (n * G.height) := by
  have h := finrank_eq_ker_mul_range k (G.A n) (H.A n) (φ.app n)
  have h2 : Module.finrank k (G.A n) = p ^ (n * G.height) := by
    have h3 := G.fibreDim_eq n ⟨⊥, Ideal.isPrime_bot⟩
    rw [fibreDim, Module.finrank_baseChange] at h3
    exact h3
  exact ⟨_, h2 ▸ h⟩

end GlobalTheory.AV.KerPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatBoundOfAnchor
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.FlatLine GlobalTheory.FlatTw

namespace GlobalTheory.FlatSplit

section Congr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}

theorem lieFacZ_congr (x : ℝ) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') : lieFacZ Dw x G = lieFacZ Dw x G' := by
  unfold lieFacZ
  congr 4
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun z : ℤ => (z : ℝ)) (congrFun h (some ⟨τ, i⟩))

theorem lat_congr {C C' : Submodule c.F (Rul Xo c)} (hC : C = C') {N N' : (c.F →+* ℂ) → Rul Xo c → ℝ} (hN : N = N') :
    ((HasGram (fun σ (f : C) => N σ f) ∧ (supLat C).FG ∧ Submodule.span c.F (supLat C : Set C) = ⊤) ↔
      (HasGram (fun σ (f : C') => N' σ f) ∧ (supLat C').FG ∧ Submodule.span c.F (supLat C' : Set C') = ⊤)) ∧
    Formalism.HN.rkK (supLat C) = Formalism.HN.rkK (supLat C') ∧
    slope_sq (fun σ (f : C) => N σ f) (supLat C) = slope_sq (fun σ (f : C') => N' σ f) (supLat C') := by
  subst hC hN
  exact ⟨Iff.rfl, rfl, rfl⟩

theorem congr_exZ (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D)
    (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E}
    (h : exZ Dw G = exZ Dw G') :
    (GoodW U x V dict G ↔ GoodW U x V dict G') ∧ rankW U G = rankW U G' ∧
      slopeW_sq U x V dict G = slopeW_sq U x V dict G' := by
  have hC : cuspW Xo c U G = cuspW Xo c U G' := by
    ext f
    rw [mem_cuspW, mem_cuspW, h]
    exact and_congr_right fun _ => forall₂_congr fun σ hσ => by rw [modelWt_congr (U σ) hσ (hU σ hσ) h]
  have hP : petW U x V dict G = petW U x V dict G' := by
    funext σ f
    unfold petW petAt
    rw [lieFacZ_congr x h, modelWt_congr (U (goodOf c σ)) (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) h]
  exact lat_congr hC hP

end Congr

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ)

theorem exZ_shift_neg (m kc : ℕ) (c0 : ℤ) :
    exZ Dw (shiftG Dw a (2 * m) (-c0)) =
      exZ Dw (wtOf Dw (uMinus Dw a (2 * m) kc c0 + parWt Dw (anchor Dw a (2 * m) kc)) ((0 : ℤ) + (m : ℤ))) := by
  rw [Model.exZ_shiftG, zero_add, exOf]
  congr 2
  simp only [uMinus, uWt, neg_smul]
  abel

end Weights

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

theorem twice_twist_ge {ι : Type} [Fintype ι] (w c1v : ι → ℝ) (pq q large₂ L b E mT CA lr m0 fr nV lS : ℝ)
    (hc1 : ∀ τ, |c1v τ + pq / 2 * large₂| ≤ 3 * q * L) (hA1 : |mT - ∑ τ, pq * w τ * large₂| ≤ CA * E)
    (hA2 : (∑ τ, |w τ|) * q * L ≤ CA * E) (hq : 0 ≤ q) (hlr : lr ≤ 2 * L) (hL : 10 ≤ L) (hm : 2 * m0 ≤ nV)
    (hm0 : 0 ≤ m0) (hfr : 0 ≤ fr) (hb : fr * nV * L ≤ b) (hbE : b ≤ E) (hLE : L ≤ E) (hlS : lS ≤ 40 * L) :
    -mT - (11 * CA + 83) * E ≤
      2 * ((∑ τ, w τ * c1v τ) - q * lr * (∑ τ, |w τ|) - m0 * fr * (Real.log (2 * Real.pi) / 2 + lr) - lS) := by
  have e1 : ∀ τ ∈ Finset.univ, (-1 / 2) * (pq * w τ * large₂) - (3 * q * L) * |w τ| ≤ w τ * c1v τ := by
    intro τ _
    have h1 : |w τ * (c1v τ + pq / 2 * large₂)| ≤ |w τ| * (3 * q * L) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hc1 τ) (abs_nonneg _)
    have h2 := neg_abs_le (w τ * (c1v τ + pq / 2 * large₂))
    have h3 : w τ * c1v τ = w τ * (c1v τ + pq / 2 * large₂) - pq * w τ * large₂ / 2 := by ring
    linarith
  have e2 := Finset.sum_le_sum e1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at e2
  have hS2 : 0 ≤ ∑ τ, |w τ| := Finset.sum_nonneg fun τ _ => abs_nonneg _
  have a1 := (abs_le.1 hA1).1
  have a2 : q * lr * (∑ τ, |w τ|) ≤ q * (2 * L) * (∑ τ, |w τ|) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlr hq) hS2
  have hpi : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hpi4 := Real.pi_le_four
  have a3 : Real.log (2 * Real.pi) / 2 + lr ≤ 3 * L := by linarith
  have a4 : m0 * fr * (Real.log (2 * Real.pi) / 2 + lr) ≤ m0 * fr * (3 * L) :=
    mul_le_mul_of_nonneg_left a3 (mul_nonneg hm0 hfr)
  have a5 : 2 * m0 * (fr * (3 * L)) ≤ nV * (fr * (3 * L)) :=
    mul_le_mul_of_nonneg_right hm (mul_nonneg hfr (by linarith))
  nlinarith

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

theorem lrd_le {PP A M : ℝ} (hH : HostNum D L PP A M) : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd D.host.E ≤ 2 * L.sc.L := by
  have hd : (0 : ℝ) < |(discr D.host.E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero D.host.E)
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have h1 := hH.disc
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd
  rw [rootDiscr_def]
  push_cast
  rw [Real.log_rpow hd, hH.deg]
  push_cast
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.FlatSplit

namespace GlobalTheory.FlatSplit

end GlobalTheory.FlatSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSymmetricFunctionValuesInGroundField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSymmetricFunctionValuesInGroundField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.SymRat

theorem grpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}

theorem thList_congr {m : ℕ} {R : Type} [CommRing R] {x : Sp R ⟶ S} (θ : SecAt G L x) {K : Type} [Field K]
    {y y' : Sp K ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x) (hu : u.left = u'.left)
    {N : ℕ} {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y (VVRank.pullS G _ u θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) pt' c := by
  subst e
  obtain rfl : u = u' := Over.OverMorphism.ext hu
  exact ⟨pt, H⟩

end GlobalTheory.UMin.SymRat

namespace GlobalTheory.UMin.SymRat

theorem symAt_exists : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω]
    (x : Sp Ω ⟶ S) (θ : SecAt G L x), Odd m → N = m ^ (4 * g) → PolFib G L g x → ∃ e : Fin N → Ω, SymAt G L ρ m x θ e := by
  intro S G _ _ L ρ hL hρ g m N Ω _ _ x θ hm hN hP
  obtain ⟨Ω', instF, instA, pt₀, c₀, hfd, hgal, -, hT, hτ⟩ := GlobalTheory.T.theta_constants_listed_finite_galois_extension S G L ρ hL hρ g m N Ω x θ hm hN hP
  haveI := hfd
  haveI := hgal
  have sb := GlobalTheory.T.thetaSymmetricFunctionsDegreeFactorial_basic_properties
  have hfix : ∀ j, ∃ e : Ω, algebraMap Ω Ω' e = symTup c₀ j := by
    intro j
    have hm : symTup c₀ j ∈ Set.range (algebraMap Ω Ω') := (IsGalois.mem_range_algebraMap_iff_fixed _).2 fun τ => by
      obtain ⟨σ, hσ⟩ := hτ τ
      have e1 : τ (symTup c₀ j) = symTup (fun b => τ (c₀ b)) j := sb.2.2.1 Ω' Ω' (τ : Ω' →+* Ω') N c₀ j
      rw [e1, show (fun b => τ (c₀ b)) = fun b => c₀ (σ b) from funext hσ, sb.2.1 Ω' N c₀ σ]
    obtain ⟨e, he⟩ := hm
    exact ⟨e, he⟩
  choose e he using hfix
  refine ⟨e, ?_⟩
  intro K _ i pt c hc j
  let k : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  letI : Algebra Ω (AlgebraicClosure K) := (k.comp i).toAlgebra
  haveI : Algebra.IsAlgebraic Ω Ω' := Algebra.IsAlgebraic.of_finite Ω Ω'
  let jj : Ω' →ₐ[Ω] AlgebraicClosure K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hcomp : (jj : Ω' →+* AlgebraicClosure K).comp (algebraMap Ω Ω') = k.comp i :=
    RingHom.ext fun r => jj.commutes r
  obtain ⟨p1, -, h1⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S G L ρ hL hρ m N Ω' (AlgebraicClosure K) (jj : Ω' →+* AlgebraicClosure K) _ _ pt₀ c₀ hT
  obtain ⟨p2, -, h2⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S G L ρ hL hρ m N K (AlgebraicClosure K) k _ _ pt c hc
  simp only [SecAt.pull] at h1 h2
  rw [pullS_comp G hL] at h1 h2
  have ey1 : spMap (jj : Ω' →+* AlgebraicClosure K) ≫ spMap (algebraMap Ω Ω') ≫ x = spMap (k.comp i) ≫ x := by
    rw [← Category.assoc, spMap_comp_ring, hcomp]
  have ey2 : spMap k ≫ spMap i ≫ x = spMap (k.comp i) ≫ x := by
    rw [← Category.assoc, spMap_comp_ring]
  obtain ⟨q1, H1⟩ := thList_congr θ ey1 _ (Over.homMk (spMap (k.comp i)) rfl : Over.mk (spMap (k.comp i) ≫ x) ⟶ Over.mk x)
    (by simp only [Over.comp_left, Over.homMk_left]; rw [spMap_comp_ring, hcomp]) h1
  obtain ⟨q2, H2⟩ := thList_congr θ ey2 _ (Over.homMk (spMap (k.comp i)) rfl : Over.mk (spMap (k.comp i) ≫ x) ⟶ Over.mk x)
    (by simp only [Over.comp_left, Over.homMk_left]; rw [spMap_comp_ring]) h2
  have hPy : PolFib G L g (spMap (k.comp i) ≫ x) :=
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S G L G L (𝟙 S) (𝟙 G.left) hL hL (grpPullback_self G) (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hL) g Ω
      x).2 (AlgebraicClosure K) (k.comp i) hP
  have hmAC : (m : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast (k.comp i) m]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hm.pos.ne')
  obtain ⟨σ, hσ⟩ := (GlobalTheory.T.thetaConstantLists_unique_up_to_perm_scalar S G L ρ hL hρ g m m N N (AlgebraicClosure K) (spMap (k.comp i) ≫ x) hm hmAC hm hmAC
    hPy).1 _ q2 q1 _ _ H2 H1
  apply k.injective
  calc k (i (e j)) = jj (algebraMap Ω Ω' (e j)) := (RingHom.congr_fun hcomp (e j)).symm
    _ = jj (symTup c₀ j) := by rw [he]
    _ = symTup (fun b => jj (c₀ b)) j := sb.2.2.1 _ _ (jj : Ω' →+* AlgebraicClosure K) _ _ _
    _ = symTup (fun b => k (c (σ b))) j := by rw [show (fun b => jj (c₀ b)) = fun b => k (c (σ b)) from funext hσ]
    _ = symTup (fun b => k (c b)) j := by rw [sb.2.1 _ N (fun b => k (c b)) σ]
    _ = k (symTup c j) := (sb.2.2.1 _ _ k _ _ _).symm

end GlobalTheory.UMin.SymRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSymmetricFunctionValuesInGroundFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_symmetric_function_values_in_ground_field : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ S) (θ : SecAt G L x), Odd m → N = m ^ (4 * g) → PolFib G L g x → ∃ e : Fin N → Ω, SymAt G L ρ m x θ e := by
  first | exact @GlobalTheory.UMin.SymRat.symAt_exists | exact GlobalTheory.UMin.SymRat.symAt_exists | (intros; apply GlobalTheory.UMin.SymRat.symAt_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationBundleTrivialAbelianPar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationBundleTrivialAbelianPar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.Gen0

section General

variable {X Y : Scheme.{0}}

def fs {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) : FreeAbelianGroup (Y ⟶ X) :=
  ∑ k, ε k • FreeAbelianGroup.of (φ k)

theorem formEq_of_fs {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : fs φ ε = fs φ' ε') : FormEq φ ε φ' ε' := by
  intro U _ g
  have e := congrArg (FreeAbelianGroup.lift (fun ψ => Additive.ofMul (g ψ))) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [fs, map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of] at e
  apply Additive.ofMul.injective
  simpa [ofMul_prod, ofMul_zpow] using e

theorem oneGen_isGen' (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

def genSub (L : LB X) (Y : Scheme.{0}) : AddSubgroup (FreeAbelianGroup (Y ⟶ X)) where
  carrier := {f | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ), fs φ ε = f ∧
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen}
  zero_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, by simp [fs], LB.oneGen L, oneGen_isGen' L⟩
  add_mem' := by
    rintro _ _ ⟨K, _, φ, ε, rfl, t, ht⟩ ⟨K', _, φ', ε', rfl, t', ht'⟩
    exact ⟨K ⊕ K', inferInstance, Sum.elim φ φ', Sum.elim ε ε', by simp [fs, Fintype.sum_sum_type],
      LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen L φ ε φ' ε' t t' ht ht'⟩
  neg_mem' := by
    rintro _ ⟨K, _, φ, ε, rfl, t, ht⟩
    exact ⟨K, inferInstance, φ, fun k => - ε k, by simp [fs, neg_smul, Finset.sum_neg_distrib],
      LB.invGen L φ ε t, DVR.invGen_isGen L φ ε t ht⟩

variable {L : LB X}

theorem mem_of_gen {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) : fs φ ε ∈ genSub L Y := ⟨K, inferInstance, φ, ε, rfl, t, ht⟩

theorem gen_of_mem (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : fs φ ε ∈ genSub L Y) : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨K', _, φ', ε', e, t, ht⟩ := h
  obtain ⟨t', ht', -⟩ := exists_gen hL (formEq_of_fs e) t ht
  exact ⟨t', ht'⟩

theorem exists_cl (hL : L.IsLB) (Y : Scheme.{0}) : ∃ (U : Type) (_ : CommGroup U) (c : (Y ⟶ X) → U),
    ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ),
      (∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) ↔ ∏ k, c (φ k) ^ ε k = 1 := by
  refine ⟨Multiplicative (FreeAbelianGroup (Y ⟶ X) ⧸ genSub L Y), inferInstance,
    fun ψ => Multiplicative.ofAdd (QuotientAddGroup.mk' _ (FreeAbelianGroup.of ψ)), fun K _ φ ε => ?_⟩
  have e : ∏ k, Multiplicative.ofAdd (QuotientAddGroup.mk' (genSub L Y) (FreeAbelianGroup.of (φ k))) ^ ε k =
      Multiplicative.ofAdd (QuotientAddGroup.mk' (genSub L Y) (fs φ ε)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [fs, map_sum, map_zsmul, ofAdd_sum, ofAdd_zsmul]
  rw [e, ofAdd_eq_one, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact ⟨fun ⟨t, ht⟩ => mem_of_gen t ht, gen_of_mem hL⟩

end General

section Deg

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_gen_twist [IsLocalRing R] (a : D.P.A ⟶ D.P.A) [IsMonHom a] (n j : ℤ) (mu ν δ β : D.X)
    (hν : D.c ν = D.c mu ≫ a) (u : LB.Gen (IotaLB D a ν δ)) (hu : u.IsGen) :
    ∃ u₀ : LB.Gen (LB.LinComb D.P.L (Sum.elim (tφ D a (β + (n • mu + j • δ)))
      (fun k => (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left ≫ tφ D a β k)) (dε n j)), u₀.IsGen := by
  obtain ⟨U, _, c, hc⟩ := exists_cl D.P.isLB D.P.A.left
  have k₀ : ∀ q : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A, c (toUnit D.P.A ≫ q).left = 1 := fun q => by
    obtain ⟨t, ht⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := PUnit) (fun _ => q.left) (fun _ => 1)
    have h := (hc PUnit (fun _ => (toUnit D.P.A).left ≫ q.left) (fun _ => 1)).1 ⟨_, DVR.pullGen_isGen _ _ _ _ ht _⟩
    rw [Fintype.prod_unique, zpow_one] at h
    exact h
  have k₁ : c (1 : D.P.A ⟶ D.P.A).left = 1 := k₀ _
  have k₂ : ∀ χ, c (DVR.cP D D.P.A χ).left = 1 := fun χ => k₀ _
  have sq : ∀ χ χ', c (𝟙 _ * DVR.cP D D.P.A (χ + χ')).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left =
      c (𝟙 _ * DVR.cP D D.P.A χ).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left *
        (c (𝟙 _ * DVR.cP D D.P.A χ').left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left) := fun χ χ' => by
    have h := (prod_cub (𝟙 D.P.A) (DVR.cP D _ χ) (DVR.cP D _ χ') c).symm.trans ((hc thK _ thε).1
      ⟨LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t _, DVR.pullGen_isGen _ _ _ _ D.cub.isGen _⟩)
    rw [_root_.mul_assoc (𝟙 D.P.A), ← DVR.cPoint_add, k₂, k₂, k₂, k₁] at h
    rw [← div_eq_one, ← h]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
    abel
  let Φ : D.X →+ Additive U := AddMonoidHom.mk' (fun χ => Additive.ofMul
    (c (𝟙 _ * DVR.cP D D.P.A χ).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left)) (fun χ χ' => congrArg Additive.ofMul (sq χ χ'))
  have e : ∀ χ, Additive.ofMul (c (𝟙 _ * DVR.cP D D.P.A χ).left) =
      Φ χ + Additive.ofMul (c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left) := fun χ =>
    congrArg Additive.ofMul (div_mul_cancel _ _).symm
  clear_value Φ
  have e₃ : Additive.ofMul (c (a * DVR.cP D _ ν).left) = Φ δ + Additive.ofMul (c a.left) := by
    have h := (hc _ _ _).1 ⟨u, hu⟩
    rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four] at h
    have h' : c (𝟙 _ * DVR.cP D D.P.A δ).left ^ (1 : ℤ) * c (DVR.cP D D.P.A δ).left ^ (-1 : ℤ) *
        c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (-1 : ℤ) * c (1 : D.P.A ⟶ D.P.A).left ^ (1 : ℤ) *
        (c (a * DVR.cP D D.P.A ν).left ^ (-1 : ℤ) * c (DVR.cP D D.P.A ν).left ^ (1 : ℤ) * c a.left ^ (1 : ℤ) *
          c (1 : D.P.A ⟶ D.P.A).left ^ (-1 : ℤ)) = 1 := h
    have h'' := congrArg Additive.ofMul h'
    simp only [ofMul_mul, ofMul_zpow, k₁, k₂, e, ofMul_one] at h''
    rw [eq_comm, ← sub_eq_zero, ← h'']
    module
  let T : D.P.A ⟶ D.P.A := 𝟙 _ * DVR.cP D _ mu
  have i₀ : T ≫ 𝟙 _ = 𝟙 _ * DVR.cP D _ mu := Category.comp_id _
  have i₁ : T ≫ (𝟙 _ * DVR.cP D _ β) = 𝟙 _ * DVR.cP D _ (mu + β) := by
    rw [MonObj.comp_mul, DVR.comp_cP, i₀, DVR.cPoint_add, _root_.mul_assoc]
  have i₂ : T ≫ DVR.cP D _ β = DVR.cP D _ β := DVR.comp_cP D _ _
  have i₃ : T ≫ (1 : D.P.A ⟶ D.P.A) = 1 := MonObj.comp_one _
  have i₄ : T ≫ a = a * DVR.cP D _ ν := by
    rw [MonObj.mul_comp, Category.id_comp, DVR.cP, DVR.cP, hν, Category.assoc]
  have h : c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (n - 1) * c (𝟙 _ * DVR.cP D D.P.A (β + (n • mu + j • δ))).left ^ (1 : ℤ) *
      c (DVR.cP D D.P.A (β + (n • mu + j • δ))).left ^ (-1 : ℤ) * c (1 : D.P.A ⟶ D.P.A).left ^ (1 : ℤ) * c a.left ^ j *
      (c (T ≫ 𝟙 _).left ^ (-(n - 1)) * c (T ≫ (𝟙 _ * DVR.cP D _ β)).left ^ (-1 : ℤ) *
        c (T ≫ DVR.cP D _ β).left ^ (-(-1) : ℤ) * c (T ≫ (1 : D.P.A ⟶ D.P.A)).left ^ (-1 : ℤ) * c (T ≫ a).left ^ (-j)) = 1 := by
    rw [i₀, i₁, i₂, i₃, i₄]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, k₁, k₂, e, e₃, ofMul_one, map_add (f := _), map_zsmul]
    module
  refine (hc _ _ _).2 ?_
  rw [Fintype.prod_sum_type, Fin.prod_univ_five, Fin.prod_univ_five]
  exact h

end Deg

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (mu β β' : D.toPre.X), β' = β + shift h h' n j mu → ∃ u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j)), u₀.IsGen := by
  intro R _ _ _ hR D a a' h h' hE n j mu β β' hβ
  obtain ⟨u, hu, -⟩ := exists_iota R hR D a a' h h' hE (h mu)
  haveI := hE.1
  subst hβ
  exact exists_gen_twist D.toPre a n j mu (h mu) (h' (h mu)) β (hE.2.2.2.1 mu) u hu

end GlobalTheory.TwFam.Gen0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationBundleTrivialAbelianParStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedFunctionalEquation_bundle_trivial_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (mu β β' : D.toPre.X), β' = β + shift h h' n j mu → ∃ u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j)), u₀.IsGen := by
  first | exact @GlobalTheory.TwFam.Gen0.main | exact GlobalTheory.TwFam.Gen0.main | (intros; apply GlobalTheory.TwFam.Gen0.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VarietyComplexPointsMapIsHolomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VarietyComplexPointsMapIsHolomorphic
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem ptMap_isHolo : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str),
    (atlas X σ).IsHolo (atlas Y σ) (ptMap σ f hf) := fun _ _ _ _ _ f _ =>
  ⟨CxPts.continuous_of_comp (f := f) fun _ => rfl, fun j i => AlgChart.holo_map (f := f) (fun _ => rfl) j i⟩

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VarietyComplexPointsMapIsHolomorphicStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.varietyComplexPointsMap_isHolomorphic : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), (atlas X σ).IsHolo (atlas Y σ) (ptMap σ f hf) := by
  first | exact @GlobalTheory.ChernCalc.ptMap_isHolo | exact GlobalTheory.ChernCalc.ptMap_isHolo | (intros; apply GlobalTheory.ChernCalc.ptMap_isHolo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfSurjectiveOfDimEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfSurjectiveOfDimEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isFinite_of_surjective_of_dim_eq : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → Surjective f.hom.left → IsFinite f.hom.left := by
  intro K _ A B f hd hs
  have dB : SmoothOfRelativeDimension A.dim B.X.hom := hd ▸ B.smooth
  exact GlobalTheory.OntoFinite.isFinite_of_surjective A.ab B.ab A.smooth dB f.hom

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfSurjectiveOfDimEqStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_of_surjective_of_dim_eq' : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → Surjective f.hom.left → IsFinite f.hom.left := by
  first | exact @GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq | exact GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq | (intros; apply GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSemipositiveWeightOfGenerated
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSemipositiveWeightOfGenerated
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory

theorem weight_cInf_semiPos_of_generated : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (B : LB X), B.IsLB → (∃ (n : ℕ) (u : Fin n → B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → ∃ (φ : Weight p σ B), φ.IsCInf ∧ ∀ D : ℕ, φ.SemiPosReg D := by
  intro k _ X p σ B hB ⟨n, u, hu⟩
  exact ⟨Weight.fsBasis p σ hB u hu 1 (by simp), Weight.isCInf_fsBasis hB u hu 1 (by simp),
    fun D => Weight.semiPosReg_fsBasis hB u hu 1 (by simp)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSemipositiveWeightOfGeneratedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_semipositive_weight_of_generated : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (B : LB X), B.IsLB → (∃ (n : ℕ) (u : Fin n → B.Sec), ⨆ i, nonzeroLocus (u i) = ⊤) → ∃ (φ : Weight p σ B), φ.IsCInf ∧ ∀ D : ℕ, φ.SemiPosReg D := by
  first | exact @GlobalTheory.weight_cInf_semiPos_of_generated | exact GlobalTheory.weight_cInf_semiPos_of_generated | (intros; apply GlobalTheory.weight_cInf_semiPos_of_generated <;> assumption)
end
end
