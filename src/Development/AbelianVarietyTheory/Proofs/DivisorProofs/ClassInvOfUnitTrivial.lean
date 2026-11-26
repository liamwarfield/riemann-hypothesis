module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePrincMulUnit
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassInvOfUnitTrivial
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal

namespace GlobalTheory.ClassInvAny


open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates in
theorem classInv_of_unit_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E), HasInf χ φ (fun i => (κ i : ℤ) + s) → (∀ u ∈ hatOUnits c, finPart χ u = 1) → ∀ (y y' : (Af E)ˣ) (S S' : ℂ → ℂ), (QuotientGroup.mk y : PicO c) = QuotientGroup.mk y' → IsLatSum φ (2 * s) κ (lattice c y) S → IsLatSum φ (2 * s) κ (lattice c y') S' → ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0 = ((finPart χ y' : ℂ) * ((modF y' ^ s : ℝ) : ℂ))⁻¹ * S' 0 := by
  intro E _ _ _ I _ φ hφ s κ c χ hχ hunit y y' S S' hq hS hS'
  classical
  obtain ⟨a, ⟨α, rfl⟩, u, hu, hau⟩ := Subgroup.mem_sup.1 (QuotientGroup.eq.1 hq)
  set a : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom α with ha
  have hy' : y' = a * y * u := by
    have : y' = y * (a * u) := by rw [hau]; group
    rw [this]; exact (by ac_rfl : y * (a * u) = a * y * u)
  subst hy'
  have hL := GlobalTheory.ClassInv.lattice_princ_mul_unit (c := c) y α hu
  rw [hL] at hS'
  have hS0 : S' 0 = (lamInf φ (2 * s) κ α)⁻¹ * S 0 :=
    (GlobalTheory.HomothetyLatSum.homothety E I φ hφ s _ κ α S hS).2 S' hS'
  have hAB : ((finPart χ a : ℂˣ) : ℂ) * ((χ.inf α : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, show finPart χ a * χ.inf α = 1 from finPart_mul_inf χ α, Units.val_one]
  have hfu : finPart χ u = 1 := hunit u hu
  have hmu : modF u = 1 := ObjModel.modF_unit hu
  have hma : modF a = (|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)|)⁻¹ := IdeleModule.modF_princ α
  have hn : |((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| ≠ 0 := by
    have h0 : Algebra.norm ℚ (α : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 α.ne_zero
    exact abs_ne_zero.2 (by exact_mod_cast h0)
  have hmy : modF y ≠ 0 := (IdeleModule.modF_pos y).ne'
  rw [hS0, GlobalTheory.ClassInv.lamInf_eq hφ hχ α]
  rw [map_mul, map_mul, hfu, mul_one, IdeleModule.modF_mul, IdeleModule.modF_mul, hmu, mul_one, hma, Units.val_mul]
  have hF : ((finPart χ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA : ((finPart χ a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hB : ((χ.inf α : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hA' : ((finPart χ a : ℂˣ) : ℂ) = (((χ.inf α : ℂˣ) : ℂ))⁻¹ := eq_inv_of_mul_eq_one_left hAB
  have hn' : ((|((Algebra.norm ℚ (α : E) : ℚ) : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hmy' : ((modF y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmy
  rw [hA']
  push_cast
  field_simp
  rw [div_pow]
  field_simp

end GlobalTheory.ClassInvAny
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationOfExponentialLatt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationOfExponentialLatt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
open GlobalTheory.PELU

namespace GlobalTheory

theorem exists_holUnif_of_isExp : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (Λ : Submodule ℤ (Fin g → ℂ)), IsExp (𝟙 (Sp ℂ)) e → DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Λ) →
    ∃ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g), u₀.ex = e := by
  intro A _ g e Λ he hd hf hk
  refine ⟨⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩,
    { ex := e
      ex_add := he.1
      ex_onto := he.2.1
      Λ := Λ
      ker := hk
      discrete := hd
      full := hf
      hol := fun U f => by
        have h := he.2.2.1 U f
        simpa using h
      fr := fun _ _ => 1
      fr_hol := fun _ => differentiableOn_const _
      fr_ne := fun _ _ _ => one_ne_zero
      fr_compat := fun i j z h => by
        show (1 : ℂ) = _
        exact ((_root_.mul_one _).trans (valAt'_one _ h)).symm }, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicUniformisationOfExponentialLattStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix
open GlobalTheory.PELU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_uniformisation_of_exponential_lattice : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A))
    (Λ : Submodule ℤ (Fin g → ℂ)), IsExp (𝟙 (Sp ℂ)) e → DiscreteTopology Λ →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z, e z = 1 ↔ z ∈ Λ) →
    ∃ (L₀ : LB A.left) (u₀ : HolUnif A L₀ g), u₀.ex = e := by
  first | exact @GlobalTheory.exists_holUnif_of_isExp | exact GlobalTheory.exists_holUnif_of_isExp | (intros; apply GlobalTheory.exists_holUnif_of_isExp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodParameterFirstSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContragredientPar

open Finset GlobalTheory.SignedHC

theorem v_strictAnti {R : Ranks} (P : HCParam R) : StrictAnti P.v := by
  have hs : ∀ (a : ℕ) (h : a + 1 < R.k - 1), P.v ⟨a + 1, h⟩ < P.v ⟨a, by omega⟩ :=
    fun a h => (P.u_gt_v ⟨a + 1, h⟩).trans (P.v_gt_u ⟨a, by omega⟩)
  have hA : ∀ (d a : ℕ) (h : a + d + 1 < R.k - 1), P.v ⟨a + d + 1, h⟩ < P.v ⟨a, by omega⟩ := by
    intro d
    induction d with
    | zero => exact hs
    | succ d ih => intro a h; exact (hs (a + d + 1) h).trans (ih a (by omega))
  rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show a < c from hac)
  exact hA d a hc

theorem b_strictMono {R : Ranks} (P : HCParam R) : StrictMono P.b := by
  have hs : ∀ (a : ℕ) (h : a + 1 < R.m), P.b ⟨a, by omega⟩ < P.b ⟨a + 1, h⟩ := fun a h => by
    have h1 := P.gap_be ⟨a, by omega⟩
    have h2 := P.gap_eb ⟨a, by omega⟩ h
    have h3 : (0 : ℚ) ≤ R.t := by positivity
    linarith
  have hA : ∀ (d a : ℕ) (h : a + d + 1 < R.m), P.b ⟨a, by omega⟩ < P.b ⟨a + d + 1, h⟩ := by
    intro d
    induction d with
    | zero => exact hs
    | succ d ih => intro a h; exact (ih a (by omega)).trans (hs (a + d + 1) h)
  rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt (show a < c from hac)
  exact hA d a hc

theorem neg_v_lt_b {R : Ranks} (P : HCParam R) (i : Fin (R.k - 1)) (j : Fin R.m) : -P.v i < P.b j := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have h1 := P.u_last_gt (by omega) (by omega)
  have h2 := P.v_gt_u ⟨R.k - 2, by omega⟩
  have h3 : P.v ⟨R.k - 2, by omega⟩ ≤ P.v i :=
    (v_strictAnti P).antitone (show i.1 ≤ R.k - 2 by have := i.2; omega)
  have h4 : P.b ⟨0, by omega⟩ ≤ P.b j := (b_strictMono P).monotone (show 0 ≤ j.1 from Nat.zero_le _)
  have h5 : (⟨R.k - 2 + 1, by omega⟩ : Fin R.k) = ⟨R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
  simp only [h5] at h2
  linarith

end GlobalTheory.ContragredientPar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMapClosedFibre
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

namespace GlobalTheory


set_option backward.isDefEq.respectTransparency.types false in
theorem fibre_finite_isClosed_of_affine_finite {X Y : Scheme.{0}} (f : Y ⟶ X) (V : X.Opens)
    (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hfin : letI := (f.app V).hom.toAlgebra; Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V))
    (x : X) (hxV : x ∈ V) (hx : IsClosed ({x} : Set X)) :
    (f.base ⁻¹' {x}).Finite ∧ ∀ y : Y, f.base y = x → IsClosed ({y} : Set Y) := by
  haveI : IsAffine V.toScheme := hV
  haveI : IsAffine (f ⁻¹ᵁ V).toScheme := hU
  haveI hg : IsFinite (f ∣_ V) := by
    rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    refine ⟨inferInstance, ?_⟩
    have h1 : (f.app (V.ι ''ᵁ ⊤)).hom.Finite := by
      rw [Scheme.Opens.ι_image_top]; exact hfin
    have h2 : ∀ {A B : CommRingCat.{0}} (e : A ⟶ B) [IsIso e], e.hom.Finite := fun e _ =>
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso e).2
    rw [morphismRestrict_appTop]
    exact (h2 _).comp h1
  have hmemU : ∀ y : Y, f.base y = x → y ∈ f ⁻¹ᵁ V := fun y hy => by
    show f.base y ∈ V
    rw [hy]; exact hxV
  have hres : ∀ (y : Y) (hy : f.base y = x),
      (f ∣_ V) (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) = (⟨x, hxV⟩ : V.toScheme) := by
    intro y hy
    exact Subtype.ext ((morphismRestrict_base_coe f V _).trans hy)
  refine ⟨?_, ?_⟩
  · refine (((f ∣_ V).finite_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).image
      (f ⁻¹ᵁ V).ι.base).subset ?_
    intro y hy
    exact ⟨⟨y, hmemU y hy⟩, hres y hy, rfl⟩
  · intro y hy
    rw [← closure_subset_iff_isClosed]
    intro z hz
    rw [← specializes_iff_mem_closure] at hz
    have hfz : f.base z = x := by
      have h1 : f.base y ⤳ f.base z := hz.map f.base.hom.continuous
      rw [hy, specializes_iff_mem_closure, hx.closure_eq] at h1
      exact h1
    have hspec : (⟨y, hmemU y hy⟩ : (f ⁻¹ᵁ V).toScheme) ⤳ ⟨z, hmemU z hfz⟩ :=
      (f ⁻¹ᵁ V).ι.isOpenEmbedding.isInducing.specializes_iff.1 hz
    have hdisc := ((f ∣_ V).isDiscrete_preimage_singleton (⟨x, hxV⟩ : V.toScheme)).to_subtype
    have hs2 : (⟨_, hres y hy⟩ : ((f ∣_ V) ⁻¹' {(⟨x, hxV⟩ : V.toScheme)} : Set _)) ⤳
        ⟨_, hres z hfz⟩ :=
      Topology.IsInducing.subtypeVal.specializes_iff.1 hspec
    have := congrArg (fun p => (p.1 : (f ⁻¹ᵁ V).toScheme).1) hs2.eq
    exact (Set.mem_singleton_iff.2 this.symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalCoefficientElementarySymm
open IsDedekindDomain NumberField Formalism.UG Formalism.IndefR.Mult GlobalTheory.SphPar Polynomial

namespace GlobalTheory.SphPar

theorem dualLab_splitLab_getD (n k : ℕ) (i : ℕ) :
    (dualLab (splitLab n k)).getD i 0 = if i < k then 1 else 0 := by
  have h : dualLab (splitLab n k) = List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0 := by
    simp [dualLab, splitLab]
  rw [h]
  split_ifs with hi
  · rw [List.getD_append _ _ _ _ (by simpa using hi)]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_append_right _ _ _ _ (by simpa using hi)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl

theorem diagonal_dualLab_splitLab {L : Type} [Field L] (n k : ℕ) (ϖ : L) :
    Matrix.diagonal (fun i : Fin n => ϖ ^ (dualLab (splitLab n k)).getD i 0) = diagJ n ϖ k := by
  unfold diagJ
  congr 1
  funext i
  rw [dualLab_splitLab_getD]
  split_ifs <;> simp

theorem Tj_eq_of_isUnifV (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n k : ℕ)
    {ϖ ϖ' : P.adicCompletion E} (h : IsUnifV E P ϖ) (h' : IsUnifV E P ϖ') :
    Tj ℂ n (Ov E P) ϖ' k = Tj ℂ n (Ov E P) ϖ k := by
  unfold IsUnifV at h h'
  have hv0 : Valued.v ϖ ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  have hv0' : Valued.v ϖ' ≠ 0 := by rw [h']; exact WithZero.coe_ne_zero
  have h0 : ϖ ≠ 0 := fun e => hv0 (by rw [e, map_zero])
  have h0' : ϖ' ≠ 0 := fun e => hv0' (by rw [e, map_zero])
  have hu : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, h', ← h, div_self hv0]
  have e : ϖ' = ϖ' / ϖ * ϖ := (div_mul_cancel₀ _ h0).symm
  rw [e]
  refine Final.TjIndep _ _ _ _ _ _ _ ?_ ?_ (div_ne_zero h0' h0)
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hu.le
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hu, inv_one])

theorem divInd_dualLab_splitLab (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n k : ℕ)
    {ϖ : P.adicCompletion E} (h : IsUnifV E P ϖ) :
    divInd (n := n) (Ov E P) (dualLab (splitLab n k)) = Tj ℂ n (Ov E P) ϖ k := by
  funext g
  by_cases hg : HasDiv (Ov E P) (dualLab (splitLab n k)) g
  · obtain ⟨ϖ', h', hab⟩ := id hg
    rw [diagonal_dualLab_splitLab] at hab
    rw [← Tj_eq_of_isUnifV E P n k h h', divInd, Tj, Set.indicator_of_mem (by exact hg),
      Set.indicator_of_mem (by exact hab)]
  · rw [divInd, Tj, Set.indicator_of_notMem (by exact hg), Set.indicator_of_notMem]
    intro hab
    refine hg ⟨ϖ, h, ?_⟩
    rw [diagonal_dualLab_splitLab]
    exact hab

end GlobalTheory.SphPar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatQuasicoherentLocal
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

noncomputable section

namespace GlobalTheory

theorem restrictGlobal_appTop_eq_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) (V : X.Opens)
    (a : Γ(X, ⊤)) :
    restrictGlobal Y (f ⁻¹ᵁ V) (f.appTop a) = f.appLE V (f ⁻¹ᵁ V) le_rfl (restrictGlobal X V a) := by
  have h : f.app V (restrictGlobal X V a) = restrictGlobal Y (f ⁻¹ᵁ V) (f.appTop a) :=
    ConcreteCategory.congr_hom (f.naturality (homOfLE le_top : V ⟶ ⊤).op) _
  rw [← h, Scheme.Hom.app_eq_appLE]

theorem length_sectionsOn_pullback_of_free (O : Type) [CommRing O] {X Y : Scheme.{0}}
    [Algebra O Γ(X, ⊤)] [Algebra O Γ(Y, ⊤)] (f : Y ⟶ X)
    (hO : ∀ r : O, f.appTop (algebraMap O Γ(X, ⊤) r) = algebraMap O Γ(Y, ⊤) r)
    (V : X.Opens) (n : ℕ) (hV : IsAffineOpen V) (hU : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree : letI := (f.app V).hom.toAlgebra; Module.Free Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧
      Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) ∧ Module.finrank Γ(X, V) Γ(Y, f ⁻¹ᵁ V) = n)
    (G : X.Modules) [G.IsQuasicoherent] :
    Module.length O (sectionsOn ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V)) =
      n * Module.length O (sectionsOn G V) := by
  rw [Scheme.Hom.app_eq_appLE] at hfree
  letI := appLEAlgebra f (le_refl (f ⁻¹ᵁ V))
  letI := appLEModule f ((Scheme.Modules.pullback f).obj G) (le_refl (f ⁻¹ᵁ V))
  haveI := appLE_isScalarTower f ((Scheme.Modules.pullback f).obj G) (le_refl (f ⁻¹ᵁ V))
  obtain ⟨hF, hFin, hr⟩ := hfree
  have hbc := isBaseChange_pullbackSections f G hU hV (le_refl (f ⁻¹ᵁ V))
  let b := Module.Free.chooseBasis Γ(X, V) Γ(Y, f ⁻¹ᵁ V)
  let ι := Module.Free.ChooseBasisIndex Γ(X, V) Γ(Y, f ⁻¹ᵁ V)
  let E : Γ((Scheme.Modules.pullback f).obj G, f ⁻¹ᵁ V) ≃ₗ[Γ(X, V)] (ι → Γ(G, V)) :=
    (hbc.equiv.restrictScalars Γ(X, V)).symm ≪≫ₗ
      TensorProduct.congr b.equivFun (LinearEquiv.refl Γ(X, V) Γ(G, V)) ≪≫ₗ
      TensorProduct.comm _ _ _ ≪≫ₗ TensorProduct.piScalarRight _ _ _ _
  let A : sectionsOn ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V) ≃+ (ι → sectionsOn G V) :=
    (sectionsOn.toΓ _ _).trans (E.toAddEquiv.trans
      (AddEquiv.piCongrRight fun _ ↦ (sectionsOn.toΓ G V).symm))
  let Φ : sectionsOn ((Scheme.Modules.pullback f).obj G) (f ⁻¹ᵁ V) ≃ₗ[O]
      (ι → sectionsOn G V) :=
    A.toLinearEquiv fun r x ↦ by
      funext i
      apply (sectionsOn.toΓ G V).injective
      change sectionsOn.toΓ G V ((sectionsOn.toΓ G V).symm
          (E (sectionsOn.toΓ _ _ (r • x)) i)) =
        sectionsOn.toΓ G V (r • (sectionsOn.toΓ G V).symm (E (sectionsOn.toΓ _ _ x) i))
      rw [AddEquiv.apply_symm_apply, sectionsOn.toΓ_smul, sectionsOn.toΓ_smul,
        AddEquiv.apply_symm_apply, ← hO, restrictGlobal_appTop_eq_appLE]
      rw [← appLEModule_smul, E.map_smul]
      rfl
  rw [Φ.length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rcases subsingleton_or_nontrivial Γ(X, V) with hA | hA
  · haveI : Subsingleton Γ(G, V) := Module.subsingleton Γ(X, V) Γ(G, V)
    haveI : Subsingleton (sectionsOn G V) := (sectionsOn.toΓ G V).toEquiv.subsingleton_congr.2 this
    rw [Module.length_eq_zero_iff.2 this, mul_zero, mul_zero]
  · rw [← hr, Module.finrank_eq_card_chooseBasisIndex]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleLengthDisjointSupport
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem sectionsOn_res_pi_bijective_of_separating {X : Scheme.{0}} (F : X.Modules) [IsFiniteQC F]
    (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] {ι : Type} [Fintype ι] (W : ι → X.Opens)
    (hcov : support F ⊆ ⋃ i, (W i : Set X))
    (hdisj : ∀ i j, i ≠ j → ∀ x ∈ support F, x ∈ W i → x ∉ W j) :
    Function.Bijective
      (LinearMap.pi fun i => sectionsOn.res R F (le_top : W i ≤ ⊤) :
        sectionsOn F ⊤ →ₗ[R] ∀ i, sectionsOn F (W i)) := by
  classical
  refine ⟨?_, fun t => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    apply (sectionsOn.toΓ F ⊤).injective
    rw [map_zero]
    refine section_eq_zero_of_germ _ fun x hx => ?_
    by_cases hxs : x ∈ support F
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov hxs)
      have h0 : sectionsOn.res R F (le_top : W i ≤ ⊤) s = 0 := congrFun hs i
      have := congrArg (fun u => F.presheaf.germ (W i) x hi (sectionsOn.toΓ F (W i) u)) h0
      simp only [sectionsOn.toΓ_res, map_zero] at this
      rwa [F.presheaf.germ_res_apply] at this
    · exact (notMem_support_iff.1 hxs).elim _ _
  have key (i : ι) : ∃ s : sectionsOn F ⊤, sectionsOn.res R F (le_top : W i ≤ ⊤) s = t i ∧
      ∀ j, j ≠ i → sectionsOn.res R F (le_top : W j ≤ ⊤) s = 0 := by
    let C : X.Opens := ⟨(support F)ᶜ, (isClosed_support F).isOpen_compl⟩
    let V : X.Opens := (⨆ (j : ι) (_ : j ≠ i), W j) ⊔ C
    have hWV (j : ι) (hj : j ≠ i) : W j ≤ V :=
      le_sup_of_le_left (le_iSup₂ (f := fun (j : ι) (_ : j ≠ i) => W j) j hj)
    have hcovV : (⊤ : X.Opens) ≤ W i ⊔ V := fun x _ => by
      by_cases hxs : x ∈ support F
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcov hxs)
        by_cases hji : j = i
        · exact Or.inl (hji ▸ hj)
        · exact Or.inr (hWV j hji hj)
      · exact Or.inr (Or.inr hxs)
    have : Subsingleton Γ(F, W i ⊓ V) := subsingleton_sections_of_notMem_support fun y hy hys => by
      rcases hy.2 with hy' | hy'
      · obtain ⟨j, hj, hyj⟩ : ∃ j, j ≠ i ∧ y ∈ W j := by
          simpa [Opens.mem_iSup] using hy'
        exact hdisj i j (Ne.symm hj) y hys hy.1 hyj
      · exact hy' hys
    obtain ⟨s, h₁, h₂⟩ := Qcqs.exists_section_glue₂ F (V₁ := W i) (V₂ := V) (W := ⊤) le_top le_top
      hcovV (sectionsOn.toΓ F (W i) (t i)) 0 (Subsingleton.elim _ _)
    refine ⟨(sectionsOn.toΓ F ⊤).symm s, (sectionsOn.toΓ F (W i)).injective ?_, fun j hj =>
      (sectionsOn.toΓ F (W j)).injective ?_⟩
    · rw [sectionsOn.toΓ_res, AddEquiv.apply_symm_apply]
      exact h₁
    · rw [sectionsOn.toΓ_res, AddEquiv.apply_symm_apply, map_zero]
      have e := congrArg (F.presheaf.map (homOfLE (hWV j hj)).op) h₂
      rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at e
      exact e
  choose s h₁ h₂ using key
  refine ⟨∑ i, s i, funext fun j => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.pi_apply, map_sum, Finset.sum_eq_single j (fun i _ hi => h₂ i j hi.symm) (by simp),
    h₁]

theorem length_sectionsOn_top_eq_sum_of_separating :
    ∀ {X : Scheme.{0}} (F : X.Modules) [IsFiniteQC F] (R : Type) [CommRing R]
      [Algebra R Γ(X, ⊤)] {ι : Type} [Fintype ι] (W : ι → X.Opens),
      support F ⊆ ⋃ i, (W i : Set X) → (∀ i j, i ≠ j → ∀ x ∈ support F, x ∈ W i → x ∉ W j) →
      Module.length R (sectionsOn F ⊤) = ∑ i, Module.length R (sectionsOn F (W i)) := by
  intro X F _ R _ _ ι _ W hcov hdisj
  rw [(LinearEquiv.ofBijective _
    (sectionsOn_res_pi_bijective_of_separating F R W hcov hdisj)).length_eq,
    Module.length_pi_of_fintype]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechLineBundleAmbientOfOpenImmersion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechLineBundleAmbientOfOpenImmersion
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue.OpenExt

variable {X X' : Scheme.{0}} (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X')

theorem image_inf_le (a b : L.ι) : f ''ᵁ L.U a ⊓ f ''ᵁ L.U b ≤ f ''ᵁ (L.U a ⊓ L.U b) := fun x hx ↦ by
  obtain ⟨w, hw, rfl⟩ := hx.1
  exact f.apply_mem_image_iff.2 ⟨hw, f.apply_mem_image_iff.1 hx.2⟩

def extLB : LB X :=
  ⟨L.ι, fun a ↦ f ''ᵁ L.U a, fun a b ↦ res (image_inf_le f L a b) (GlobalTheory.GlueLineBundle.imU f _ (L.g a b))⟩

theorem gm_ext_g {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z) (a b : L.ι) (ha : r z ∈ L.U a) (hb : r z ∈ L.U b) :
    gm (r ≫ f) z ((extLB f L).U a ⊓ (extLB f L).U b) ((extLB f L).g a b) = gm r z (L.U a ⊓ L.U b) (L.g a b) := by
  have hm : (r ≫ f) z ∈ f ''ᵁ L.U a ⊓ f ''ᵁ L.U b := ⟨f.apply_mem_image_iff.2 ha, f.apply_mem_image_iff.2 hb⟩
  exact (gm_res (r ≫ f) z (image_inf_le f L a b) hm _).trans
    (GlobalTheory.GlueLineBundle.gm_imU f r z (L.U a ⊓ L.U b) ⟨ha, hb⟩ _)


variable {f} in
theorem gm_eq_map {Y : Scheme.{0}} (g : Y ⟶ X) (y : Y) (U : X.Opens) (h : g y ∈ U) (a : Γ(X, U)ˣ) :
    gm g y U a = Units.map (g.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (g y) U a) := by
  apply Units.ext
  rw [Units.coe_map, gm_val g y U h, GlobalTheory.GlueLineBundle.gm_id_val h]
  exact (Scheme.Hom.germ_stalkMap_apply g U y h a.val).symm

end GlobalTheory.PicGlue.OpenExt

namespace GlobalTheory.PicGlue.OpenExt

variable {X X' : Scheme.{0}} (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X')

theorem isOn_extLB (hL : L.IsLB) : IsOn f.opensRange (extLB f L) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a x hx
    obtain ⟨w, -, rfl⟩ := hx
    exact ⟨w, rfl⟩
  · intro x hx
    obtain ⟨w, rfl⟩ := hx
    obtain ⟨a, ha⟩ := exists_chart hL w
    exact ⟨a, f.apply_mem_image_iff.2 ha⟩
  · intro x a b c hxa hxb hxc
    obtain ⟨w, ha, rfl⟩ := hxa
    have hb : w ∈ L.U b := f.apply_mem_image_iff.1 hxb
    have hc : w ∈ L.U c := f.apply_mem_image_iff.1 hxc
    have e : ∀ (d d' : L.ι) (hd : w ∈ L.U d) (hd' : w ∈ L.U d'),
        Units.map (f.stalkMap w).hom.toMonoidHom (gm (𝟙 X) (f w) _ ((extLB f L).g d d')) =
          gm (𝟙 X') w (L.U d ⊓ L.U d') (L.g d d') := by
      intro d d' hd hd'
      rw [← gm_eq_map f w ((extLB f L).U d ⊓ (extLB f L).U d') ⟨f.apply_mem_image_iff.2 hd, f.apply_mem_image_iff.2 hd'⟩]
      have k := gm_ext_g f L (𝟙 X') w d d' hd hd'
      rwa [Category.id_comp] at k
    apply Units.map_injective (f := (f.stalkMap w).hom.toMonoidHom)
      (fun u v h ↦ (ConcreteCategory.bijective_of_isIso (f.stalkMap w)).1 h)
    refine (MonoidHom.map_mul _ _ _).trans ?_
    exact (congrArg₂ (· * ·) (e a b ha hb) (e b c hb hc)).trans
      ((gm_cocycle hL (𝟙 X') w ha hb hc).trans (e a c ha hc).symm)

end GlobalTheory.PicGlue.OpenExt


open GlobalTheory.PicGlue.OpenExt in
theorem GlobalTheory.PicGlue.exists_isOn_of_openImmersion : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X'),
    L.IsLB → ∃ L' : LB X, IsOn f.opensRange L' ∧ LBIso (L'.pull f) L := by
  intro X X' f _ L hL
  refine ⟨extLB f L, isOn_extLB f L hL, iso_of_chart hL ⟨fun J ↦ J PUnit.unit, ?_, ?_⟩⟩
  · intro J y hy
    exact f.apply_mem_image_iff.1 (mem_pull.1 hy)
  · intro y J J' hj hj'
    exact (gm_pull_g (extLB f L) f (𝟙 X') y J J' hj hj').trans
      (gm_ext_g f L (𝟙 X') y _ _ (f.apply_mem_image_iff.1 (mem_pull.1 hj)) (f.apply_mem_image_iff.1 (mem_pull.1 hj')))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechLineBundleAmbientOfOpenImmersionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cech_lineBundle_ambient_of_openImmersion : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsOpenImmersion f] (L : LB X'), L.IsLB → ∃ L' : LB X, IsOn f.opensRange L' ∧ LBIso (L'.pull f) L := by
  first | exact @GlobalTheory.PicGlue.exists_isOn_of_openImmersion | exact GlobalTheory.PicGlue.exists_isOn_of_openImmersion | (intros; apply GlobalTheory.PicGlue.exists_isOn_of_openImmersion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantMeanSquareForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantMeanSquareForm
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaMeanSquareForm

open GlobalTheory.HeisOrtho

theorem exists_form {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (M : Submodule ℂ (X → ℂ))
    (hm : ∀ f ∈ M, Measurable f) (hb : ∀ f ∈ M, ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    ∃ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ f g : M, B f g = ∫ x, (f : X → ℂ) x * (starRingEnd ℂ) ((g : X → ℂ) x) ∂ν) ∧
      ∀ f : M, ∫⁻ x, ‖(f : X → ℂ) x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (B f f).re := by
  have hi : ∀ f g : M, Integrable (fun x => (f : X → ℂ) x * (starRingEnd ℂ) ((g : X → ℂ) x)) ν := fun f g => by
    obtain ⟨C, hC⟩ := hb f f.2
    obtain ⟨C', hC'⟩ := hb g g.2
    refine Integrable.of_bound
      (((hm f f.2).mul (Complex.continuous_conj.measurable.comp (hm g g.2))).aestronglyMeasurable)
      (C * C') (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC x) (hC' x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun f g : M => ∫ x, (f : X → ℂ) x * (starRingEnd ℂ) ((g : X → ℂ) x) ∂ν) ?_ ?_ ?_ ?_, fun _ _ => rfl, fun f => ?_⟩
  · intro f f' g
    rw [← integral_add (hi f g) (hi f' g)]
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
  · intro c f g
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  · intro f g g'
    rw [← integral_add (hi f g) (hi f g')]
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _), mul_add]
  · intro c f g
    rw [smul_eq_mul, ← integral_const_mul]
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm]
  · rw [LinearMap.mk₂'ₛₗ_apply]
    have h1 : Integrable (fun x => ‖(f : X → ℂ) x‖ ^ 2) ν := by
      refine (hi f f).norm.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [norm_mul, Complex.norm_conj, sq]
    simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
    rw [integral_complex_ofReal, Complex.ofReal_re,
      ofReal_integral_eq_lintegral_ofReal h1 (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem exists_invariant_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsCharAF D.host.F ψ → ∀ M : Submodule ℂ (WO S T → ℂ), (∀ f ∈ M, IsThetaFunO ψ S T f) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WO S T) (f g f' g' : M), (f' : WO S T → ℂ) = heisO ψ S T u f → (g' : WO S T → ℂ) = heisO ψ S T u g → B f' g' = B f g) ∧ ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WO S T → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (B f f).re := by
  intro D ψ S T hψ M hM μ 𝓕 hμ h𝓕
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO S T) (ratL T S) hK hKc μ h𝓕⟩
  have hb : ∀ f ∈ M, ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C := fun f hf => by
    have hp : ∀ γ ∈ ratL T S, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm ((hM f hf).quasi γ w)).trans (by rw [norm_mul, hψ.2.1, one_mul])
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hM f hf).cont.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hKc w
    rw [← hp γ hγ w]
    exact hC _ h
  obtain ⟨B, hB, hN⟩ := exists_form (μ.restrict 𝓕) M (fun f hf => (hM f hf).cont.measurable) hb
  refine ⟨B, fun u f g f' g' hf hg => ?_, hN⟩
  rw [hB, hB, hf, hg]
  have key := setIntegral_add_right (G := WO S T) (ratL T S) μ 𝓕 h𝓕
    (fun w => (f : WO S T → ℂ) w * (starRingEnd ℂ) ((g : WO S T → ℂ) w)) (by
      rintro _ ⟨γ, rfl⟩ w
      have h0 := mul_conj_of_norm_one (hψ.2.1 (-(symplOH S T (ratW T S γ) w)))
      have h1 := (hM f f.2).quasi γ w
      have h2 := (hM g g.2).quasi γ w
      show (f : WO S T → ℂ) (ratW T S γ + w) * (starRingEnd ℂ) ((g : WO S T → ℂ) (ratW T S γ + w)) = _
      rw [h1, h2, map_mul, mul_mul_mul_comm, h0, one_mul]) u
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have h0 := mul_conj_of_norm_one (hψ.2.1 (symplOH S T w u))
  show ψ (symplOH S T w u) * (f : WO S T → ℂ) (w + u) *
    (starRingEnd ℂ) (ψ (symplOH S T w u) * (g : WO S T → ℂ) (w + u)) = _
  rw [map_mul, mul_mul_mul_comm, h0, one_mul]

end GlobalTheory.ThetaMeanSquareForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeisenbergInvariantMeanSquareFormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heisenbergInvariant_meanSquare_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsCharAF D.host.F ψ → ∀ M : Submodule ℂ (WO S T → ℂ), (∀ f ∈ M, IsThetaFunO ψ S T f) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ (u : WO S T) (f g f' g' : M), (f' : WO S T → ℂ) = heisO ψ S T u f → (g' : WO S T → ℂ) = heisO ψ S T u g → B f' g' = B f g) ∧ ∀ f : M, ∫⁻ w in 𝓕, ‖(f : WO S T → ℂ) w‖ₑ ^ 2 ∂μ = ENNReal.ofReal (B f f).re := by
  first | exact @GlobalTheory.ThetaMeanSquareForm.exists_invariant_form | exact GlobalTheory.ThetaMeanSquareForm.exists_invariant_form | (intros; apply GlobalTheory.ThetaMeanSquareForm.exists_invariant_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitDetOfSplitDetermines
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev IsDedekindDomain NumberField Polynomial
open scoped Pointwise

namespace GlobalTheory.PartsCompare

open GlobalTheory.IndefiniteRowSideFullHecke

section Poly

variable {K L : Type} [Field K] [Field L]

theorem dualPoly_comp {a : K} (ha : a ≠ 0) (s : K) (p : K[X]) :
    dualPoly s (p.comp (C a⁻¹ * X)) = dualPoly (s * a) p := by
  have hd : (p.comp (C a⁻¹ * X)).natDegree = p.natDegree := by
    rw [natDegree_comp, natDegree_C_mul_X _ (inv_ne_zero ha), mul_one]
  have hl : (p.comp (C a⁻¹ * X)).leadingCoeff = p.leadingCoeff * a⁻¹ ^ p.natDegree := by
    rw [leadingCoeff, hd, comp_C_mul_X_coeff, leadingCoeff]
  ext i
  by_cases hi : i ≤ p.natDegree
  · rw [coeff_dualPoly_of_le _ _ (hd ▸ hi), coeff_dualPoly_of_le _ _ hi, hl, hd, comp_C_mul_X_coeff]
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi
    rw [hj, Nat.add_sub_cancel_left, pow_add, mul_pow]
    have h1 : a⁻¹ ^ i * a ^ i = 1 := by rw [← mul_pow, inv_mul_cancel₀ ha, one_pow]
    have h2 : a⁻¹ ^ j ≠ 0 := pow_ne_zero _ (inv_ne_zero ha)
    have h3 : (a⁻¹ ^ i)⁻¹ = a ^ i := by rw [inv_pow, inv_inv]
    rw [mul_inv, mul_inv, h3]
    field_simp
  · have hi' := not_le.1 hi
    rw [coeff_dualPoly_of_lt _ _ (hd ▸ hi'), coeff_dualPoly_of_lt _ _ hi']

theorem coeff_heckePolyOf (n q : ℕ) (a : ℕ → K) (i : ℕ) :
    (Formalism.L2.Col.heckePolyOf n q a).coeff i =
      if i ≤ n then (-1) ^ i * (q : K) ^ (i * (i - 1) / 2) * a i else 0 := by
  unfold Formalism.L2.Col.heckePolyOf
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range,
    Nat.lt_succ_iff]

theorem tri_add (i j : ℕ) : (i + j) * (i + j - 1) / 2 + i * (i - 1) / 2 = j * (j - 1) / 2 + (i + j - 1) * i := by
  have h : ∀ n : ℕ, 2 * (n * (n - 1) / 2) + n = n * n := by
    intro n
    rw [Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd]
    cases n with
    | zero => rfl
    | succ m => simp; ring
  have h1 := h (i + j)
  have h2 := h i
  have h3 := h j
  have h4 : (i + j - 1) * i + i = (i + j) * i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      have : m + 1 + j - 1 = m + j := by omega
      rw [this]; ring
  nlinarith

theorem heckePolyOf_dual {n q : ℕ} (hq : (q : K) ≠ 0) {a b : ℕ → K} (h0 : a 0 = 1)
    (h : ∀ k ≤ n, a n * b k = a (n - k)) :
    Formalism.L2.Col.heckePolyOf n q b = dualPoly ((q : K) ^ (n - 1)) (Formalism.L2.Col.heckePolyOf n q a) := by
  have hn : a n ≠ 0 := by
    have := h n le_rfl
    rw [Nat.sub_self, h0] at this
    exact left_ne_zero_of_mul_eq_one this
  have htop : (Formalism.L2.Col.heckePolyOf n q a).coeff n ≠ 0 := by
    rw [coeff_heckePolyOf, if_pos le_rfl]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by simp)) (pow_ne_zero _ hq)) hn
  have hd : (Formalism.L2.Col.heckePolyOf n q a).natDegree = n :=
    le_antisymm (natDegree_le_iff_coeff_eq_zero.2 fun i hi => by rw [coeff_heckePolyOf, if_neg (not_le.2 hi)])
      (le_natDegree_of_ne_zero htop)
  ext i
  by_cases hi : i ≤ n
  · rw [coeff_dualPoly_of_le _ _ (by rw [hd]; exact hi), leadingCoeff, hd, eq_inv_mul_iff_mul_eq₀ htop,
      coeff_heckePolyOf, coeff_heckePolyOf, coeff_heckePolyOf, if_pos le_rfl, if_pos hi, if_pos (Nat.sub_le _ _),
      ← h i hi]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [Nat.add_sub_cancel_left, ← pow_mul]
    have e := congrArg (fun m => (q : K) ^ m) (tri_add i j)
    simp only [pow_add] at e
    have e2 : ((-1 : K) ^ i) * (-1) ^ i = 1 := by rw [← mul_pow]; simp
    rw [pow_add]
    linear_combination ((-1 : K) ^ j * a (i + j) * b i * ((-1) ^ i * (-1) ^ i)) * e +
      ((-1 : K) ^ j * a (i + j) * b i * ((q : K) ^ (j * (j - 1) / 2) * (q : K) ^ ((i + j - 1) * i))) * e2
  · rw [coeff_dualPoly_of_lt _ _ (by rw [hd]; exact not_le.1 hi), coeff_heckePolyOf, if_neg hi]

end Poly

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

section Label

variable {R : RealDat D A Ks} {F : Face D A} {s : ℕ} (hs : A.fam.Ok s) (h : R.Char F)
include hs h

variable {X : DivX D} {E : EigIdx D X} {sys : E.Pi → PolarisedDualSystem.Sys D} {jE : D.what₂.EE →ₗ[ℂ] R.HE.H}
  {jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H}

end Label

section Ties

variable {R : RealDat D A Ks} {F : Face D A} {X : DivX D} {E : EigIdx D X} {sys : E.Pi → PolarisedDualSystem.Sys D}
  {jE : D.what₂.EE →ₗ[ℂ] R.HE.H} {jW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H}

end Ties

section Main

variable {R : RealDat D A Ks} {F : Face D A} {X : DivX D} {E : EigIdx D X}

end Main

end GlobalTheory.PartsCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookProductPosLogEq
namespace GlobalTheory.HookDiagram

theorem hookProd_eq_of_mem (μ : YoungDiagram) (n : ℕ) (a : ℕ → ℕ)
    (h : ∀ i j, (i, j) ∈ μ ↔ i < n ∧ j < a i) :
    Formalism.LatticeIndexTer.hookProd μ = GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
  have hrow : ∀ r, r < n → μ.rowLen r = a r := by
    intro r hr
    apply le_antisymm
    · by_contra hlt
      rw [not_le] at hlt
      have hm : (r, a r) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hlt
      exact lt_irrefl _ ((h r (a r)).mp hm).2
    · by_contra hlt
      rw [not_le] at hlt
      have hm : (r, μ.rowLen r) ∈ μ := (h r _).mpr ⟨hr, hlt⟩
      exact lt_irrefl _ (YoungDiagram.mem_iff_lt_rowLen.mp hm)
  have hcol : ∀ r c, Finset.filter (fun r' => c < a r') (Finset.Ioo r n) =
      Finset.Ioo r (μ.colLen c) := by
    intro r c
    ext r'
    simp only [Finset.mem_filter, Finset.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, YoungDiagram.mem_iff_lt_colLen.mp ((h r' c).mpr ⟨h2, h3⟩)⟩
    · rintro ⟨h1, h2⟩
      have hm := (h r' c).mp (YoungDiagram.mem_iff_lt_colLen.mpr h2)
      exact ⟨⟨h1, hm.1⟩, hm.2⟩
  have hrc : ∀ r c, r < n → c < a r → r < μ.colLen c := fun r c hr hc =>
    YoungDiagram.mem_iff_lt_colLen.mp ((h r c).mpr ⟨hr, hc⟩)
  unfold Formalism.LatticeIndexTer.hookProd GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd
  rw [Finset.prod_finset_product μ.cells (Finset.range n) (fun r => Finset.range (a r))]
  · apply Finset.prod_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    apply Finset.prod_congr rfl
    intro c hc
    rw [Finset.mem_range] at hc
    dsimp only
    rw [hcol r c, Nat.card_Ioo, hrow r hr]
    have := hrc r c hr hc
    omega
  · rintro ⟨i, j⟩
    simp only [YoungDiagram.mem_cells, Finset.mem_range]
    exact h i j

theorem hookOf_eq (n : ℕ) (a : ℕ → ℕ) (ha : ∀ x y, x ≤ y → y < n → a y ≤ a x) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a = GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
  have hsort : ((List.range n).map a).Pairwise (· ≥ ·) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp_of_mem
      (fun {x y} _ hy hxy => ha x y hxy.le (List.mem_range.mp hy))
  have hL : ((List.range n).map a).insertionSort (· ≥ ·) = (List.range n).map a :=
    hsort.insertionSort_eq
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf
  apply hookProd_eq_of_mem
  intro i j
  rw [YoungDiagram.mem_ofRowLens]
  simp only [hL, List.length_map, List.length_range, List.getElem_map, List.getElem_range,
    exists_prop]

theorem hookOf_pos_log (n : ℕ) (a : ℕ → ℕ) (ha : ∀ x y, x ≤ y → y < n → a y ≤ a x) :
    0 < GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a ∧
      Real.log (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a : ℝ) = Formalism.BasicNotions.DV.logHook n (fun k => (a k : ℝ)) := by
  rw [hookOf_eq n a ha]
  have hm := GlobalTheory.LiftSizeCompare.hookProd_mul n a ha
  have hinner : ∀ r ∈ Finset.range n,
      0 < ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) := by
    intro r _
    apply Finset.prod_pos
    intro l hl
    rw [Finset.mem_Ioo] at hl
    omega
  have hPpos : 0 < ∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) :=
    Finset.prod_pos hinner
  have hHpos : 0 < GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a := by
    rcases Nat.eq_zero_or_pos (GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a) with h0 | h0
    · have hF : 0 < ∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial :=
        Finset.prod_pos fun r _ => Nat.factorial_pos _
      rw [h0, zero_mul] at hm
      omega
    · exact h0
  refine ⟨hHpos, ?_⟩
  have hmR : (GlobalTheory.IndefiniteRowSideFullHecke.SchurTensorLattices.hookProd n a : ℝ) =
      ((∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial : ℕ) : ℝ) /
        ((∏ r ∈ Finset.range n, ∏ l ∈ Finset.Ioo r n, (a r - a l + (l - r)) : ℕ) : ℝ) := by
    rw [eq_div_iff (by exact_mod_cast hPpos.ne'), ← Nat.cast_mul, hm]
  have hFpos : (0 : ℝ) < ((∏ r ∈ Finset.range n, (a r + n - 1 - r).factorial : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun r _ => Nat.factorial_pos _
  rw [hmR, Real.log_div hFpos.ne' (by exact_mod_cast hPpos.ne')]
  unfold Formalism.BasicNotions.DV.logHook
  congr 1
  · rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mem_range] at hr
      have hg : (a r : ℝ) + n - r = ((a r + n - 1 - r : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub (show r ≤ a r + n - 1 by omega), Nat.cast_sub (show 1 ≤ a r + n by omega)]
        push_cast
        ring
      rw [hg, Real.Gamma_nat_eq_factorial]
    · intro r _
      exact_mod_cast (Nat.factorial_pos _).ne'
  · rw [Nat.cast_prod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [Nat.cast_prod, Real.log_prod]
      · apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mem_Ioo] at hl
        have hal : a l ≤ a r := ha r l hl.1.le hl.2
        congr 1
        rw [Nat.cast_add, Nat.cast_sub hal, Nat.cast_sub hl.1.le]
        ring
      · intro l hl
        rw [Finset.mem_Ioo] at hl
        have hpos : 0 < a r - a l + (l - r) := by omega
        exact_mod_cast hpos.ne'
    · intro r hr
      exact_mod_cast (hinner r hr).ne'

end GlobalTheory.HookDiagram
end
