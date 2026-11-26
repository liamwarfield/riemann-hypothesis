module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerDegreeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleRationalExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientJacquetSegment
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleParabolicInduction

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JCh
noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.EisSo

theorem jCh : StdGood → BdetLaw → JTop → JCh := by
  intro hS hB _ F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hG hBase hi hJ
  have hL : (adStd F).GoodL := hS F
  obtain ⟨-, -, -, -, hk, hd⟩ := hB F 𝔸[F] (adStd F) hL (ι ⊕ ι) Set.univ
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ) := by
    have h := Continuous.units_map (Matrix.detMonoidHom (n := ι ⊕ ι) (R := 𝔸[F]))
      (Continuous.matrix_det continuous_id)
    convert h using 1
    funext x
    apply Units.ext
    rfl
  have hprj : Continuous (prj A ν ι) := continuous_snd.comp continuous_subtype_val
  have hfst : Continuous fun x : cover A ν ι => x.1.1 := continuous_fst.comp continuous_subtype_val
  have hadd : ∀ p g : cover A ν ι, ld (p * g) = ld p + ld g := by
    intro p g
    simp only [ld, map_mul]
    exact hL.lgmul _ _
  have hK : ∀ k ∈ cK α j, ld k = 0 := by
    intro k hk'
    obtain ⟨κ, hκ, he⟩ := hk'.2
    have hdk : Matrix.GeneralLinearGroup.det (prj A ν ι k) = Matrix.GeneralLinearGroup.det κ := by
      rw [← he]
      simp [MulAut.conj_apply, map_mul, map_inv, mul_comm]
    have := hk κ (by intro r hr; exact absurd (Set.mem_univ r) hr) hκ
    rw [hd] at this
    simp only [ld, hdk]
    exact this
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro p _ q _
    simp [c0]
  · intro p _
    exact Circle.norm_coe _
  · intro γ hγ _
    obtain ⟨⟨x, hx⟩, -⟩ := hγ
    have := hG.toGoodL.χi x
    simp only [c0]
    have hx' : Units.map A.i.toMonoidHom x = γ.1.1 := hx
    rw [← hx', this]
    simp
  · exact (continuous_subtype_val.comp (hG.toGoodL.χcont.comp hfst)).continuousOn
  · intro p _ g
    exact hadd p g
  · intro g k hk'
    rw [hadd, hK k hk', add_zero]
  · intro γ hγ _
    obtain ⟨-, ⟨g, hg⟩⟩ := hγ
    have e : Matrix.GeneralLinearGroup.det (prj A ν ι γ) = Units.map (adStd F).i.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
      have hg' : Matrix.GeneralLinearGroup.map (adStd F).i g = γ.1.2 := hg
      show Matrix.GeneralLinearGroup.det γ.1.2 = _
      rw [← hg']
      apply Units.ext
      show ((Matrix.GeneralLinearGroup.map (adStd F).i g : GL (ι ⊕ ι) 𝔸[F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).det =
        (adStd F).i (g : Matrix (ι ⊕ ι) (ι ⊕ ι) F).det
      rw [RingHom.map_det]
      rfl
    simp only [ld, e]
    exact hL.lgi _
  · exact hL.lgcont.comp (hdet.comp hprj)

end GlobalTheory.CompanionTheory.EisSo
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfimumOfEquality
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesOver
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetEqOfProdAddEq
namespace GlobalTheory.MultisetOfProduct

open Polynomial

theorem eval_prod_neg (m : Multiset ℂ) (u : ℂ) :
    (((m.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod).eval u
      = (m.map (fun x : ℂ => u + x)).prod := by
  rw [Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => ?_)
  simp [sub_neg_eq_add]

theorem multiset_eq_of_prod_add_eq {m m' : Multiset ℂ}
    (h : ∀ (u : ℂ), Multiset.prod (Multiset.map (fun (x : ℂ) ↦ u + x) m)
      = Multiset.prod (Multiset.map (fun (x : ℂ) ↦ u + x) m')) : m = m' := by

  have hp : ((m.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod =
      ((m'.map (fun x : ℂ => -x)).map (fun a : ℂ => X - C a)).prod := by
    apply Polynomial.funext
    intro u
    rw [eval_prod_neg, eval_prod_neg]
    exact h u
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

end GlobalTheory.MultisetOfProduct
end

open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IsobaricOfPublished

theorem multiset_eq_of_prod_map_add {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) : m = m' := by
  first
  | exact @_root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq
  | exact _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq
  | (apply _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultisetOfProduct.multiset_eq_of_prod_add_eq ..)

end GlobalTheory.IsobaricOfPublished

namespace GlobalTheory.IsobaricOfPublished

end GlobalTheory.IsobaricOfPublished
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfimumOfEquality
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue

theorem infOfEq_holds : InfOfEq := by
  intro E _ _ _ N t ψ m τ m' hT hI hψ h0 hC
  have hS := hT E N t τ m' hI
  refine GlobalTheory.IsobaricOfPublished.multiset_eq_of_prod_map_add fun u => ?_
  exact smul_left_injective ℂ h0 ((hS.2 u ψ hψ).symm.trans (hC τ u))

end GlobalTheory.CompanionTheory.EGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfimumOfEqualityStatement
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infimum_of_equality : GlobalTheory.CompanionTheory.EGlue.InfOfEq := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.infOfEq_holds | exact GlobalTheory.CompanionTheory.EGlue.infOfEq_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.infOfEq_holds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFormNonvanishingOnChart
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFormNonvanishingOnChart
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

theorem exists_form_of_mem_open : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (U : X.Opens), genericPoint X ∈ U → ∃ (j : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog j a ∧
      j ∉ ptIdeal (i (genericPoint X)) ∧ ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ),
        GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z → eval z (map (Int.castRingHom ℂ) j) ≠ 0 → y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ U := by
  intro m n X _ i _ U hU
  classical
  have hx : i (genericPoint X) ∈ mchart (ptChart (i (genericPoint X))) :=
    Set.mem_iInter.2 fun k => mem_ptChart _ k
  have hcl : IsClosed (i '' (U : Set X)ᶜ) :=
    i.isClosedEmbedding.isClosedMap _ U.isOpen.isClosed_compl
  let V : (MP ℤ m n).Opens := ⟨(i '' (U : Set X)ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hV : i (genericPoint X) ∈ V := by
    rintro ⟨x, hxU, hxe⟩
    exact hxU (i.isClosedEmbedding.injective hxe ▸ hU)
  obtain ⟨g, hgV, hgx⟩ := (SmoothRep.gen m n (ptChart (i (genericPoint X)))).1.exists_basicOpen_le ⟨_, hV⟩ hx
  obtain ⟨F0, rfl⟩ := ExRat.dehomog_surjective _ g
  obtain ⟨a, F, hF, e⟩ := ExRat.exists_homog (ptChart (i (genericPoint X))) F0
  rw [← e] at hgV hgx
  have hm := homog_mul hF (ExRat.isMultiHomog_mono (ptChart (i (genericPoint X))) 1)
  refine ⟨F * ExRat.mono (ptChart (i (genericPoint X))) 1, _, hm, ?_, ?_⟩
  · rw [mem_ptIdeal_iff_aeval_ptCoord m n _ _ _ hm, FnForm.aeval_ptCoord_eq_mul _ _ hx hm]
    simp only [ptCoord_ptChart, one_pow, Finset.prod_const_one, one_mul, map_mul, ExRat.dehomog_mono, mul_one]
    exact (Scheme.evaluation_ne_zero_iff_mem_basicOpen _ _ hx _).2 hgx
  · intro y z hyz hne
    have hz : ∀ k, z ⟨k, ptChart (i (genericPoint X)) k⟩ ≠ 0 := by
      intro k h0
      apply hne
      have : eval z (map (Int.castRingHom ℂ) (ExRat.mono (ptChart (i (genericPoint X))) 1)) = 0 := by
        simp only [ExRat.mono, Pi.one_apply, pow_one, map_prod, map_X]
        exact Finset.prod_eq_zero (Finset.mem_univ k) ((eval_X _).trans h0)
      rw [map_mul, map_mul, this, mul_zero]
    have hF0 : eval z (map (Int.castRingHom ℂ) F) ≠ 0 := by
      intro h0
      apply hne
      rw [map_mul, map_mul, h0, zero_mul]
    have hw : PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart (ptChart (i (genericPoint X)))) :=
      mem_ptsIn.2 (Set.mem_iInter.2 fun k => mem_ptsIn.1 ((hyz k _).1.2 (hz k)))
    have hev : ev (mpStr ℤ m n) σ₀ _ (dehomog (ptChart (i (genericPoint X))) F) (PtsOver.map i rfl _ y) ≠ 0 := by
      rw [GlobalTheory.T.dehomogenized_eval_eq_ratio m n _ F a hF _ z hyz hw]
      exact div_ne_zero hF0 (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hz k))
    have hb := mem_ptsIn.1 ((mem_ptsIn_basicOpen hw _).2 hev)
    have hp := hgV hb
    rw [mem_ptsIn]
    by_contra h
    exact hp ⟨_, h, rfl⟩

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFormNonvanishingOnChartStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_form_nonvanishing_on_chart : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (U : X.Opens), genericPoint X ∈ U → ∃ (j : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog j a ∧
      j ∉ ptIdeal (i (genericPoint X)) ∧ ∀ (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ),
        GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z → eval z (map (Int.castRingHom ℂ) j) ≠ 0 → y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ U := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.exists_form_of_mem_open | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.exists_form_of_mem_open | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.exists_form_of_mem_open <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Jcpt
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.RgEisSo

theorem jcpt : StdGood → GrpTop → JTop → JCpt := by
  intro hS hG hT F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hGood hB hi hJ
  show IsCompact (cK α j : Set (cover A ν ι))
  have hj : Continuous j := (hT F E R A ε ν r δ α ω ι i j hGood hB hi hJ).1
  obtain ⟨-, -, -, hUT2, -, -, hUK⟩ := hG E R A hGood ι ε
  have hν : Continuous ν := hB.cont

  have hmapν : Continuous (Matrix.GeneralLinearGroup.map (n := ι ⊕ ι) ν) := by
    refine Continuous.units_map _ ?_
    exact Continuous.matrix_map continuous_id hν
  let D : GL (ι ⊕ ι) R := dg ι (Units.map A.i.toMonoidHom δ)
  let M : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → GL (ι ⊕ ι) R :=
    fun h => D⁻¹ * Matrix.GeneralLinearGroup.map ν h * D
  have hM : Continuous M := (continuous_const.mul hmapν).mul continuous_const
  let φ : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → R :=
    fun p => ((p.1.1 * (M p.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)
  let ψ : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → R :=
    fun p => ((M p.2 * (p.1.1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)
  have hval : Continuous (Subtype.val : A.U ε ι → GL (ι ⊕ ι) R) := continuous_subtype_val
  have hφ : Continuous φ := by
    have : Continuous fun p : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (p.1.1 * (M p.2)⁻¹ : GL (ι ⊕ ι) R) :=
      (hval.comp continuous_fst).mul (hM.comp continuous_snd).inv
    exact (Units.continuous_val.comp this).matrix_elem _ _
  have hψ : Continuous ψ := by
    have : Continuous fun p : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (M p.2 * (p.1.1)⁻¹ : GL (ι ⊕ ι) R) :=
      (hM.comp continuous_snd).mul (hval.comp continuous_fst).inv
    exact (Units.continuous_val.comp this).matrix_elem _ _

  have hrel : ∀ x : cover A ν ι, ((j x).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (x.1.1 : R) • (M x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
    fun x => hJ x
  have hφv : ∀ x : cover A ν ι, φ (j x, x.1.2) = (x.1.1 : R) := by
    intro x
    have e : (((j x).1 * (M x.1.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (x.1.1 : R) • 1 := by
      rw [Units.val_mul, hrel x, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    show (((j x).1 * (M x.1.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i) = _
    rw [e]; simp
  have hψv : ∀ x : cover A ν ι, ψ (j x, x.1.2) = ((x.1.1⁻¹ : Rˣ) : R) := by
    intro x
    have e0 : (x.1.1 : R) • ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
      rw [Units.val_mul, ← Matrix.smul_mul, ← hrel x, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e : ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = ((x.1.1⁻¹ : Rˣ) : R) • 1 := by
      rw [← e0, smul_smul, Units.inv_mul, one_smul]
    show ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i) = _
    rw [e]; simp

  let C₂ : Set (GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :=
    ((((adStd F).kGL (ι ⊕ ι)).map (MulAut.conj (dg ι α)).toMonoidHom : Subgroup _) : Set _)
  have hC₂ : IsCompact C₂ := by
    have h0 := ((hS F).kcpt (ι ⊕ ι)).image
      (f := fun k => (MulAut.conj (dg ι α)).toMonoidHom k)
      (by
        show Continuous fun k => dg ι α * k * (dg ι α)⁻¹
        exact (continuous_const.mul continuous_id).mul continuous_const)
    exact h0
  let C₁ : Set (A.U ε ι) := (A.uK ε ι : Set (A.U ε ι))
  have hC : IsCompact (C₁ ×ˢ C₂) := hUK.prod hC₂
  have hS₁ := hC.image hφ
  have hS₂ : IsCompact (MulOpposite.op '' (ψ '' (C₁ ×ˢ C₂))) := (hC.image hψ).image MulOpposite.continuous_op
  let B : Set Rˣ := Units.embedProduct R ⁻¹' ((φ '' (C₁ ×ˢ C₂)) ×ˢ (MulOpposite.op '' (ψ '' (C₁ ×ˢ C₂))))
  have hBc : IsCompact B := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS₁.prod hS₂)

  have hdet : Continuous (Matrix.GeneralLinearGroup.det (n := ι ⊕ ι) (R := NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun g : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (g : Matrix (ι ⊕ ι) (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)).det
      exact Continuous.matrix_det Units.continuous_val
    · show Continuous fun g : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        ((g⁻¹ : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :
          Matrix (ι ⊕ ι) (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)).det
      exact Continuous.matrix_det (Units.continuous_val.comp continuous_inv)
  have hσ : Continuous A.σ := hGood.σcont
  have hUσ : Continuous (Units.map A.σ.toMonoidHom) := Continuous.units_map _ hσ
  have hUν : Continuous (Units.map ν.toMonoidHom) := Continuous.units_map _ hν
  have hcl : IsClosed ((cover A ν ι : Subgroup _) : Set (Rˣ × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) := by
    have hf : Continuous fun p : Rˣ × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        p.1 * Units.map A.σ.toMonoidHom p.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det p.2) :=
      (continuous_fst.mul (hUσ.comp continuous_fst)).mul (hUν.comp (hdet.comp continuous_snd))
    exact isClosed_singleton.preimage hf
  have hemb := hcl.isClosedEmbedding_subtypeVal
  have hP : IsCompact ((Subtype.val : cover A ν ι → _) ⁻¹' (B ×ˢ C₂)) :=
    hemb.isCompact_preimage (hBc.prod hC₂)
  have hprj : Continuous (prj A ν ι) := continuous_snd.comp continuous_subtype_val
  have hclK : IsClosed (cK α j : Set (cover A ν ι)) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact (hUK.isClosed.preimage hj).inter (hC₂.isClosed.preimage hprj)
  refine hP.of_isClosed_subset hclK ?_
  intro x hx
  have h1 : j x ∈ C₁ := hx.1
  have h2 : x.1.2 ∈ C₂ := hx.2
  refine ⟨?_, h2⟩
  refine ⟨⟨(j x, x.1.2), ⟨h1, h2⟩, hφv x⟩, ⟨ψ (j x, x.1.2), ⟨(j x, x.1.2), ⟨h1, h2⟩, rfl⟩, ?_⟩⟩
  rw [hψv x]
  rfl

end GlobalTheory.CompanionTheory.RgEisSo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTestFunctionFixedSubspace
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTestFunctionFixedSubspace
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.Inj

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_infGL_alt : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) := ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map (corner (matN a (sInf E))) (continuous_const.add (continuous_id.matrix_map hs))

theorem R_apply_eq {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {U : Subgroup (GL (Fin a) (Af E))}
    {v : L2 (latticeGL E a) μ} (hv : ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) {g : GA E a}
    (hu : GeneralLinearGroup.map (pFin E) g⁻¹ ∈ U) :
    R (latticeGL E a) μ g v = R (latticeGL E a) μ (infGL E a (GeneralLinearGroup.map (pInf E) g⁻¹)⁻¹) v := by
  have e : g = infGL E a (GeneralLinearGroup.map (pInf E) g⁻¹)⁻¹ * finGL E a (GeneralLinearGroup.map (pFin E) g⁻¹)⁻¹ := by
    rw [map_inv (infGL E a), map_inv (finGL E a), ← _root_.mul_inv_rev, ← infGL_comm, infGL_mul_finGL, inv_inv]
  conv_lhs => rw [e]
  rw [map_mul, ContinuousLinearMap.mul_apply, hv _ (U.inv_mem hu)]

theorem exists_isTest_Rop_injective : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X → (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) → ∃ β : Lie E a → ℂ, IsTest β ∧ ConjInv β ∧ ∀ v ∈ X, Rop (latticeGL E a) μ (tst U β) v = 0 → v = 0 := by
  intro E _ _ _ a μ _ _ U hU hUc X hX hfix
  let Φ : GL (Fin a) (Cinf E) → (X →L[ℂ] L2 (latticeGL E a) μ) := fun y =>
    (R (latticeGL E a) μ (infGL E a y⁻¹) - ContinuousLinearMap.id ℂ _) ∘L X.subtypeL
  have hΦv : ∀ y (w : X), Φ y w = R (latticeGL E a) μ (infGL E a y⁻¹) w - w := fun _ _ => rfl
  have hΦ : Continuous Φ := by
    refine continuous_clm_apply.2 fun w => ?_
    simp only [hΦv]
    exact ((continuous_R (w : L2 (latticeGL E a) μ)).comp (continuous_infGL_alt.comp continuous_inv)).sub
      continuous_const
  have hΦ1 : Φ 1 = 0 := by
    ext w
    simp [hΦv]
  have hN : {y | ‖Φ y‖ ≤ 1 / 2} ∈ 𝓝 (1 : GL (Fin a) (Cinf E)) := by
    have h1 : Metric.closedBall (0 : X →L[ℂ] L2 (latticeGL E a) μ) (1 / 2) ∈ 𝓝 (Φ 1) := by
      rw [hΦ1]; exact Metric.closedBall_mem_nhds _ (by norm_num)
    have h2 := hΦ.continuousAt.preimage_mem_nhds h1
    change {y | dist (Φ y) 0 ≤ 1 / 2} ∈ 𝓝 (1 : GL (Fin a) (Cinf E)) at h2
    simpa only [dist_zero_right] using h2
  obtain ⟨β₀, h0, hpos, htest, hconj, hsupp⟩ := GlobalTheory.T.exists_nonneg_test_function_near_one E a _ hN
  refine ⟨fun x => (β₀ x : ℂ), htest, hconj, fun v hv hRv => ?_⟩
  obtain ⟨hc, hcs⟩ := GlobalTheory.T.test_function_continuous_compact_support E a U hU hUc _ htest
  set f := tst U (fun x => (β₀ x : ℂ)) with hf
  set fr : GA E a → ℝ := fun g => (f g).re with hfr
  have hf_eq : ∀ g, f g = (fr g : ℂ) := by
    intro g
    simp only [hfr, hf, tst, ker]
    split_ifs <;> simp
  have hfr0 : ∀ g, 0 ≤ fr g := by
    intro g
    simp only [hfr, hf, tst, ker]
    split_ifs
    · simpa using h0 _
    · simp
  have hfrc : Continuous fr := Complex.continuous_re.comp hc
  have hfrs : HasCompactSupport fr := hcs.comp_left Complex.zero_re
  have hfr1 : fr 1 ≠ 0 := by
    have : fr 1 = β₀ (oneL E a) := by
      simp [hfr, hf, tst, ker, U.one_mem]
    rw [this]; exact hpos.ne'
  have hIpos : 0 < ∫ g, fr g ∂μ :=
    hfrc.integral_pos_of_hasCompactSupport_nonneg_nonzero hfrs hfr0 hfr1
  have hint : Integrable f μ := hc.integrable_of_hasCompactSupport hcs
  have hfrint : Integrable fr μ := hfrc.integrable_of_hasCompactSupport hfrs
  have hrep := (isRepOp_Rop (Γ := latticeGL E a) (μ := μ) hint) v
  have key : (∫ g, f g ∂μ) • v = ∫ g, f g • (v - R (latticeGL E a) μ g v) ∂μ := by
    calc (∫ g, f g ∂μ) • v = (∫ g, f g ∂μ) • v - ∫ g, f g • R (latticeGL E a) μ g v ∂μ := by
          have h2 := hrep.2.symm.trans hRv
          rw [show (∫ g, f g • R (latticeGL E a) μ g v ∂μ) = 0 from h2, sub_zero]
      _ = ∫ g, f g • (v - R (latticeGL E a) μ g v) ∂μ := by
          rw [← integral_smul_const, ← integral_sub (hint.smul_const v) hrep.1]
          simp_rw [smul_sub]
  have hI : (∫ g, f g ∂μ) = ((∫ g, fr g ∂μ : ℝ) : ℂ) := by
    simp_rw [hf_eq]; exact integral_ofReal
  have hpt : ∀ g, fr g ≠ 0 → ‖v - R (latticeGL E a) μ g v‖ ≤ ‖v‖ / 2 := by
    intro g hg
    have hfg : f g ≠ 0 := fun h => hg (by show (f g).re = 0; rw [h]; simp)
    simp only [hf, tst, ker] at hfg
    split_ifs at hfg with hu
    · have hb : β₀ (toL (GeneralLinearGroup.map (pInf E) g⁻¹).val) ≠ 0 := by
        intro h; apply hfg; simp only [Complex.ofReal_eq_zero]; convert h using 1
      obtain ⟨y, hyN, hy⟩ := hsupp _ hb
      have hy' : y = GeneralLinearGroup.map (pInf E) g⁻¹ := Units.ext (Matrix.of.symm.injective hy)
      rw [R_apply_eq (fun u hu' => hfix u hu' v hv) hu, norm_sub_rev]
      calc ‖R (latticeGL E a) μ (infGL E a (GeneralLinearGroup.map (pInf E) g⁻¹)⁻¹) v - v‖
          = ‖Φ y ⟨v, hv⟩‖ := by rw [hΦv, hy']
        _ ≤ ‖Φ y‖ * ‖(⟨v, hv⟩ : X)‖ := (Φ y).le_opNorm _
        _ ≤ 1 / 2 * ‖v‖ := mul_le_mul_of_nonneg_right hyN (norm_nonneg _)
        _ = ‖v‖ / 2 := by ring
    · exact absurd rfl hfg
  have hbound : ‖∫ g, f g • (v - R (latticeGL E a) μ g v) ∂μ‖ ≤ ∫ g, fr g * (‖v‖ / 2) ∂μ :=
    norm_integral_le_of_norm_le (hfrint.mul_const _) (Filter.Eventually.of_forall fun g => by
      rw [norm_smul, hf_eq, Complex.norm_real, Real.norm_of_nonneg (hfr0 g)]
      by_cases hg : fr g = 0
      · simp [hg]
      · exact mul_le_mul_of_nonneg_left (hpt g hg) (hfr0 g))
  rw [integral_mul_const, ← key, hI, norm_smul, Complex.norm_real, Real.norm_of_nonneg hIpos.le] at hbound
  have hle : ‖v‖ ≤ 0 := by nlinarith [norm_nonneg v]
  exact norm_le_zero_iff.1 hle

end GlobalTheory.CompanionTheory.SmoothRep.Inj
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTestFunctionFixedSubspaceStatement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_test_function_fixed_subspace : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X → (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) → ∃ β : Lie E a → ℂ, IsTest β ∧ ConjInv β ∧ ∀ v ∈ X, Rop (latticeGL E a) μ (tst U β) v = 0 → v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.Inj.exists_isTest_Rop_injective | exact GlobalTheory.CompanionTheory.SmoothRep.Inj.exists_isTest_Rop_injective | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.Inj.exists_isTest_Rop_injective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapHalfTr
open PositivityTheory.RgEis PositivityTheory.RgEis.So

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisFix

open scoped TensorProduct
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_conj (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := Classical.arbitrary _
  apply τ.injective
  rw [hτ, hτ, star_star]

theorem exists_moved (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  obtain ⟨-, hC, -, hτ⟩ := h
  by_contra hno
  push Not at hno
  let τ : E →+* ℂ := Classical.arbitrary _
  have hR : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    exact ((hτ τ x).symm.trans (congrArg τ (hno x)) : _)
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (hC.isComplex (InfinitePlace.mk τ)))
    (InfinitePlace.isReal_mk_iff.2 hR)

theorem add_conj_mem (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (e : E) :
    ∃ c : F, e + σ e = algebraMap F E c := by
  let S : Submodule F E := LinearMap.eqLocus σ.toLinearMap LinearMap.id
  have hS : S ≠ ⊤ := by
    obtain ⟨y, hy⟩ := exists_moved σ h
    intro hT
    have hyS : y ∈ S := hT ▸ Submodule.mem_top
    exact hy hyS
  have h1 : Submodule.span F {(1 : E)} ≤ S := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact map_one σ
  have hlt : Module.finrank F S < 2 := h.2.2.1 ▸ Submodule.finrank_lt hS
  have hone : Module.finrank F (Submodule.span F {(1 : E)}) = 1 :=
    finrank_span_singleton one_ne_zero
  have heq : Submodule.span F {(1 : E)} = S :=
    Submodule.eq_of_le_of_finrank_le h1 (by omega)
  have hmem : e + σ e ∈ S := by
    change σ (e + σ e) = e + σ e
    rw [map_add (f := _), conj_conj σ h, add_comm]
  rw [← heq, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩

def halfTr (σ : E →ₐ[F] E) : E →ₗ[F] F :=
  (4⁻¹ : F) • (Algebra.trace F E ∘ₗ (LinearMap.id + σ.toLinearMap))

theorem algebraMap_halfTr (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (halfTr σ e) = (2⁻¹ : F) • (e + σ e) := by
  obtain ⟨c, hc⟩ := add_conj_mem σ h e
  have hval : halfTr σ e = 2⁻¹ * c := by
    simp only [halfTr, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply,
      LinearMap.id_apply, AlgHom.toLinearMap_apply, smul_eq_mul]
    rw [hc, Algebra.trace_algebraMap, h.2.2.1, nsmul_eq_mul]
    push_cast
    ring
  rw [hval, hc, Algebra.smul_def, map_mul]

theorem halfTr_one (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : halfTr σ (1 : E) = 1 := by
  apply (algebraMap F E).injective
  rw [algebraMap_halfTr σ h, map_one, map_one, Algebra.smul_def, map_inv₀, map_ofNat]
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  field_simp
  norm_num

def rr (σ : E →ₐ[F] E) : AE F E →ₗ[AF F] AF F :=
  (TensorProduct.AlgebraTensorModule.rid F (AF F) (AF F)).toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.lTensor (AF F) (AF F) (halfTr σ)

theorem rr_tmul (σ : E →ₐ[F] E) (a : AF F) (e : E) : rr σ (a ⊗ₜ[F] e) = halfTr σ e • a := by
  simp [rr]

theorem nu_apply (x : AF F) : nuCM F E x = x ⊗ₜ[F] (1 : E) := rfl

theorem rr_nu (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : AF F) : rr σ (nuCM F E x) = x := by
  rw [nu_apply, rr_tmul, halfTr_one σ h, one_smul]

theorem cA_nu (σ : E →ₐ[F] E) (x : AF F) : cA σ (nuCM F E x) = nuCM F E x := by
  simp [nu_apply, cA]

theorem nu_rr (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (z : AE F E) :
    nuCM F E (rr σ z) = (2⁻¹ : F) • (z + cA σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), ← smul_add]
    congr 1
    abel
  | tmul a e =>
    have hc : cA σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [cA]
    rw [rr_tmul, nu_apply, hc, ← TensorProduct.tmul_add, ← TensorProduct.tmul_smul,
      ← algebraMap_halfTr σ h, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']

theorem continuous_nu : Continuous (nuCM F E) := by
  have h : (nuCM F E : AF F → AE F E) = fun x => x • (1 : AE F E) := by
    funext x
    rw [nu_apply, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h]
  exact Continuous.smul (f := fun x : AF F => x) (g := fun _ => (1 : AE F E)) continuous_id continuous_const

theorem bFix : BFix := by
  intro F E _ _ _ _ _ σ χ c hCM _ _ _
  refine ⟨continuous_nu, Function.LeftInverse.injective (rr_nu σ hCM), cA_nu σ, rr σ,
    IsModuleTopology.continuous_of_linearMap (rr σ), fun x hx => ?_⟩
  have hx' : cA σ x = x := hx
  rw [nu_rr σ hCM, hx', ← two_smul F x, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

end GlobalTheory.CompanionTheory.RgEisFix
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JMapVal
noncomputable section

open Matrix PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.RgEis.Cover

variable {R S : Type} [CommRing R] [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι]

def sc (a : Rˣ) : GL (ι ⊕ ι) R := Units.map (Matrix.scalar (ι ⊕ ι) : R →+* _).toMonoidHom a

theorem sc_val (a : Rˣ) (G : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    ((sc a : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * G = (a : R) • G := by
  show Matrix.scalar (ι ⊕ ι) (a : R) * G = (a : R) • G
  rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]

theorem sc_comm (a : Rˣ) (g : GL (ι ⊕ ι) R) : sc a * g = g * sc a := by
  apply Units.ext
  show Matrix.scalar (ι ⊕ ι) (a : R) * (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
    (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * Matrix.scalar (ι ⊕ ι) (a : R)
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, ← Matrix.smul_eq_mul_diagonal]

def jMap (D : GL (ι ⊕ ι) R) (ν : S →+* R) : Rˣ × GL (ι ⊕ ι) S →* GL (ι ⊕ ι) R where
  toFun x := sc x.1 * (D⁻¹ * Matrix.GeneralLinearGroup.map ν x.2 * D)
  map_one' := by
    have : (sc (1 : Rˣ) : GL (ι ⊕ ι) R) = 1 := by simp [sc]
    simp [this]
  map_mul' x y := by
    have h : (sc (x.1 * y.1) : GL (ι ⊕ ι) R) = sc x.1 * sc y.1 := by simp [sc]
    simp only [Prod.fst_mul, Prod.snd_mul, h, map_mul]
    rw [mul_assoc (sc x.1) _ (sc y.1 * _), ← mul_assoc _ (sc y.1), ← sc_comm y.1 (D⁻¹ * Matrix.GeneralLinearGroup.map ν x.2 * D)]
    simp only [mul_assoc, mul_inv_cancel_left]

theorem J_apply (e : ℤˣ) (i : ι) (hi : ∀ x : ι, x = i) (G G' : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (x y : ι ⊕ ι) :
    (Gᵀ * Ad.J R e ι * G') x y =
      G (Sum.inl i) x * G' (Sum.inr i) y + ((e : ℤ) : R) * G (Sum.inr i) x * G' (Sum.inl i) y := by
  have hs : ∀ f : ι → R, ∑ z, f z = f i := fun f =>
    Fintype.sum_eq_single i (fun z hz => (hz (hi z)).elim)
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, hs, Matrix.transpose_apply,
    PositivityTheory.RgEis.Ad.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq, Matrix.smul_apply,
    Matrix.zero_apply, smul_eq_mul]
  ring

theorem det_two (i : ι) (hi : ∀ x : ι, x = i) (N : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :
    N.det = N (Sum.inl i) (Sum.inl i) * N (Sum.inr i) (Sum.inr i) -
      N (Sum.inl i) (Sum.inr i) * N (Sum.inr i) (Sum.inl i) := by
  let e : Fin 2 ≃ ι ⊕ ι :=
    { toFun := ![Sum.inl i, Sum.inr i]
      invFun := Sum.elim (fun _ => 0) (fun _ => 1)
      left_inv := fun x => by fin_cases x <;> rfl
      right_inv := fun x => by
        rcases x with x | x <;> (have h := hi x; subst h; rfl) }
  rw [← Matrix.det_submatrix_equiv_self e N, Matrix.det_fin_two]
  rfl

theorem mem_aux (σ : R →+* R) (e : ℤˣ) (i : ι) (hi : ∀ x : ι, x = i) (a d d' : R)
    (N : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (hN : ∀ x y, σ (N x y) = N x y) (hd : d * d' = 1)
    (hσ : σ d = -(((e : ℤ) : R) * d)) (ha : a * σ a * N.det = 1) :
    (a • (Matrix.diagonal (Sum.elim (fun _ : ι => (1 : R)) fun _ => d') * N *
        Matrix.diagonal (Sum.elim (fun _ : ι => (1 : R)) fun _ => d)))ᵀ * Ad.J R e ι *
      (a • (Matrix.diagonal (Sum.elim (fun _ : ι => (1 : R)) fun _ => d') * N *
        Matrix.diagonal (Sum.elim (fun _ : ι => (1 : R)) fun _ => d))).map σ = Ad.J R e ι := by
  have he2 : ((e : ℤ) : R) * ((e : ℤ) : R) = 1 := by
    rcases Int.units_eq_one_or e with h | h <;> simp [h]
  have h1 : σ d * σ d' = 1 := by rw [← map_mul, hd, map_one]
  rw [hσ] at h1
  have hσd' : σ d' = -(((e : ℤ) : R) * d') := by
    linear_combination (-(((e : ℤ) : R) * d')) * h1 - (σ d' * ((e : ℤ) : R) ^ 2) * hd - σ d' * he2
  have hdet := GlobalTheory.CompanionTheory.RgEis.Cover.det_two i hi N
  ext x y
  rw [GlobalTheory.CompanionTheory.RgEis.Cover.J_apply e i hi]
  rcases x with x | x <;> rcases y with y | y <;> rw [hi x, hi y] <;>
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply,
      Sum.elim_inl, Sum.elim_inr, smul_eq_mul, map_mul, map_one, hN, hσ, hσd', one_mul, mul_one,
      PositivityTheory.RgEis.Ad.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply_eq]
  · ring
  · linear_combination (((e : ℤ) : R) ^ 2 * a * σ a * (N (Sum.inl i) (Sum.inl i) * N (Sum.inr i) (Sum.inr i) -
        N (Sum.inl i) (Sum.inr i) * N (Sum.inr i) (Sum.inl i))) * hd +
      (a * σ a * (N (Sum.inl i) (Sum.inl i) * N (Sum.inr i) (Sum.inr i) -
        N (Sum.inl i) (Sum.inr i) * N (Sum.inr i) (Sum.inl i))) * he2 + ha - (a * σ a) * hdet
  · linear_combination (((e : ℤ) : R) * a * σ a * (N (Sum.inl i) (Sum.inl i) * N (Sum.inr i) (Sum.inr i) -
        N (Sum.inl i) (Sum.inr i) * N (Sum.inr i) (Sum.inl i))) * hd +
      ((e : ℤ) : R) * ha - (((e : ℤ) : R) * a * σ a) * hdet
  · ring

theorem jMap_val (D : GL (ι ⊕ ι) R) (ν : S →+* R) (x : Rˣ × GL (ι ⊕ ι) S) :
    ((jMap D ν x : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
      (x.1 : R) • ((D⁻¹ * Matrix.GeneralLinearGroup.map ν x.2 * D : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
  show ((GlobalTheory.CompanionTheory.RgEis.Cover.sc x.1 * (D⁻¹ * Matrix.GeneralLinearGroup.map ν x.2 * D) : GL (ι ⊕ ι) R) :
    Matrix (ι ⊕ ι) (ι ⊕ ι) R) = _
  rw [Units.val_mul, GlobalTheory.CompanionTheory.RgEis.Cover.sc_val]

theorem jEx : JEx := by
  intro F E R _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i hD hi
  obtain ⟨-, -, hfix, -, -, -, -, -, -, -, -, -, hδ, -, -⟩ := hD
  refine ⟨((GlobalTheory.CompanionTheory.RgEis.Cover.jMap (PositivityTheory.RgEis.So.dg ι (Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ)) ν).comp
    (PositivityTheory.RgEis.So.cover A ν ι).subtype).codRestrict (PositivityTheory.RgEis.Ad.uSub A ε ι) ?_, ?_⟩
  · rintro ⟨⟨a, g⟩, hx⟩
    have h1 : (a : R) * PositivityTheory.RgEis.Ad.σ A (a : R) * ν (g : Matrix (ι ⊕ ι) (ι ⊕ ι) _).det = 1 :=
      congrArg Units.val ((MonoidHom.mem_ker).1 hx)
    have e1 : ((Matrix.GeneralLinearGroup.map ν g : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).det =
        ν (g : Matrix (ι ⊕ ι) (ι ⊕ ι) _).det := (RingHom.map_det ν _).symm
    have key := GlobalTheory.CompanionTheory.RgEis.Cover.mem_aux (PositivityTheory.RgEis.Ad.σ A) ε i hi (a : R)
      ((Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ : Rˣ) : R)
      (((Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ)⁻¹ : Rˣ) : R)
      ((Matrix.GeneralLinearGroup.map ν g : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)
      (fun x y => hfix ((g : Matrix (ι ⊕ ι) (ι ⊕ ι) _) x y)) (Units.mul_inv _) hδ (by rw [e1]; exact h1)
    show ((GlobalTheory.CompanionTheory.RgEis.Cover.jMap (PositivityTheory.RgEis.So.dg ι (Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ)) ν (a, g) :
        GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)ᵀ * PositivityTheory.RgEis.Ad.J R ε ι *
      ((GlobalTheory.CompanionTheory.RgEis.Cover.jMap (PositivityTheory.RgEis.So.dg ι (Units.map (PositivityTheory.RgEis.Ad.i A : E →* R) δ)) ν (a, g) :
        GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).map (PositivityTheory.RgEis.Ad.σ A) =
      PositivityTheory.RgEis.Ad.J R ε ι
    rw [GlobalTheory.CompanionTheory.RgEis.Cover.jMap_val]
    exact key
  · intro x
    exact GlobalTheory.CompanionTheory.RgEis.Cover.jMap_val _ _ _

end GlobalTheory.CompanionTheory.RgEis.Cover
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrregularProjectionImageNull
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrregularProjectionImageNull
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

open GlobalTheory.CompanionTheory.MPDict.SmoothRep (rt mem_mchart ev_rt)

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

def ratioVec {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (p : ∀ k, Bk n k) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    (Σ k, Bk n k) → ℂ :=
  fun q => ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) ((i.appLE (mchart p) (i ⁻¹ᵁ mchart p) le_rfl).hom (rt p q)) y

theorem mem_ptsIn_of_over {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) :=
  (mem_ptsIn_preimage (f := i) (m := PtsOver.map i rfl _) fun _ => rfl).2 (mem_mchart H hp)

theorem ratioVec_apply {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0)
    (q : Σ k, Bk n k) : ratioVec i p y q = z q / z ⟨q.1, p q.1⟩ :=
  (CxPts.ev_appLE_of_comp (r := i) (m := PtsOver.map i rfl _) (fun _ => rfl) le_rfl _
    (mem_ptsIn_of_over i H hp)).trans (ev_rt H hp q)

theorem sameOrbit_ratioVec {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    SameOrbit z (ratioVec i p y) := by
  refine ⟨fun k => z ⟨k, p k⟩, hp, funext fun q => ?_⟩
  rw [ratioVec_apply i H hp q, mul_div_cancel₀ _ (hp q.1)]

theorem over_liftOf {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : Over i y (liftOf i y) := by
  obtain ⟨z, -, hz⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i y
  have h : ∃ z, Over i y z := ⟨z, hz⟩
  rw [liftOf, dite_eq_left h]
  exact h.choose_spec

theorem differentiableAt_projCoord {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (Ψ : LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D) {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀}
    (hy : y ∈ c.e.source) {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (h0 : Ψ (segre z) 0 ≠ 0) :
    DifferentiableAt ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) := by
  choose p hp using fun k => exists_block_ne_zero_of_isUnder H k
  have hyW := mem_ptsIn_of_over i H hp
  have hOo : IsOpen (c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p)) :=
    c.finChart.isOpen_inter_preimage_symm (isOpen_ptsIn _)
  have hv : c.finChart y ∈ c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) :=
    ⟨c.finChart.map_source hy, by rwa [Set.mem_preimage, c.finChart.left_inv hy]⟩
  have hl : DifferentiableAt ℂ (fun v => ratioVec i p (c.finChart.symm v)) (c.finChart y) :=
    differentiableAt_pi.2 fun q =>
      (((c.analyticOnNhd_finChart_iff (isOpen_ptsIn _) _).2 (c.holo _ _)) _ hv).differentiableAt
  have hs := ReciprocityTheory.ChartRestriction.G.Geo.segre_differentiableAt hl
  let L := LinearMap.toContinuousLinearMap Ψ
  have hL : DifferentiableAt ℂ (fun v => L (segre (ratioVec i p (c.finChart.symm v)))) (c.finChart y) :=
    L.differentiableAt.comp _ hs
  have hc (a : Fin (D + 1)) := differentiableAt_pi.1 hL a
  have hne : Ψ (segre (ratioVec i p y)) 0 ≠ 0 := by
    obtain ⟨l, hl0, e⟩ := sameOrbit_ratioVec i H hp
    intro h
    apply h0
    rw [segre_orbit e, map_smul, Pi.smul_apply, h, smul_zero]
  have hne' : L (segre (ratioVec i p (c.finChart.symm (c.finChart y)))) 0 ≠ 0 := by
    rw [c.finChart.left_inv hy]
    exact hne
  have hev : (projCoord i Ψ ∘ c.finChart.symm) =ᶠ[nhds (c.finChart y)]
      fun v => ratios Ψ (ratioVec i p (c.finChart.symm v)) := by
    filter_upwards [hOo.mem_nhds hv, (hc 0).continuousAt.eventually_ne hne'] with v hvO hv0
    have H' := over_liftOf i (c.finChart.symm v)
    have hp' : ∀ k, liftOf i (c.finChart.symm v) ⟨k, p k⟩ ≠ 0 := fun k =>
      (H' k (p k)).1.1 (ptsIn_mono (mchart_le p k)
        ((mem_ptsIn_preimage (f := i) (m := PtsOver.map i rfl _) fun _ => rfl).1 hvO.2))
    exact ratios_eq_of_sameOrbit Ψ (sameOrbit_ratioVec i H' hp') hv0
  refine DifferentiableAt.congr_of_eventuallyEq (differentiableAt_pi.2 fun a => ?_) hev
  simp only [ratios, div_eq_mul_inv]
  exact (hc a.succ).mul ((hc 0).inv hne')

theorem volume_image_crit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D),
    volume (GlobalTheory.CompanionTheory.MixZ.ArchEq.projCoord i Ψ '' {y | y ∈ c.e.source ∧
      (∃ z, GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ GlobalTheory.CompanionTheory.MixZ.ArchEq.IsRegAt i Ψ c y}) = 0 := by
  intro m n X _ i _ D Ψ c
  set A := {y | y ∈ c.e.source ∧ (∃ z, Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ IsRegAt i Ψ c y} with hA
  have e : projCoord i Ψ '' A = (projCoord i Ψ ∘ c.finChart.symm) '' (c.finChart '' A) := by
    rw [Set.image_image]
    exact Set.image_congr fun y hy => by
      simp only [Function.comp_apply, c.finChart.left_inv (show y ∈ c.finChart.source from hy.1)]
  rw [e]
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fun v => (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) v).restrictScalars ℝ) ?_ ?_
  · rintro _ ⟨y, ⟨hy, ⟨z, hz, h0⟩, -⟩, rfl⟩
    exact ((differentiableAt_projCoord i Ψ c hy hz h0).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  · rintro _ ⟨y, ⟨-, -, hc⟩, rfl⟩
    have h0 := not_not.1 hc
    have hdet : ((fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y)).restrictScalars ℝ).det =
        Algebra.norm ℝ (LinearMap.det (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) :=
      LinearMap.det_restrictScalars (f := (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
        (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))
    rw [hdet, h0, Algebra.norm_complex_apply, map_zero]

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrregularProjectionImageNullStatement
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irregular_projection_image_null : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D),
    volume (GlobalTheory.CompanionTheory.MixZ.ArchEq.projCoord i Ψ '' {y | y ∈ c.e.source ∧
      (∃ z, GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ GlobalTheory.CompanionTheory.MixZ.ArchEq.IsRegAt i Ψ c y}) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.volume_image_crit | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.volume_image_crit | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.volume_image_crit <;> assumption)
end
end
