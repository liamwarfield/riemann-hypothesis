module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.PrimitiveGermFrames
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueHomExtensionSemiAbelianDvr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_prime_isUnit_of_isLocalRing (T : Type) [CommRing T] [IsLocalRing T] :
    ∃ n : ℕ, n.Prime ∧ IsUnit (n : T) := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (3 : T) with h | h
  · exact ⟨3, Nat.prime_three, by simpa using h⟩
  · refine ⟨2, Nat.prime_two, ?_⟩
    have : (1 - 3 : T) = -((2 : ℕ) : T) := by push_cast; ring
    rw [this] at h
    exact (IsUnit.neg_iff _).1 h

theorem existsUnique_hom_extension_semiAbelian_dvr :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) := by
  intro hfin T K _ _ _ _ _ _ G G' _ _ hG hG' f hf
  have := hG.comm
  have := hG'.comm
  have := hG.smooth
  have := hG'.smooth
  have := hG.separated
  have := hG'.separated
  have := hG.quasiCompact
  have := hG'.quasiCompact
  have hGflat : Flat G.hom := inferInstance
  obtain ⟨n, hn, hnT⟩ := exists_prime_isUnit_of_isLocalRing T
  let Φ := Over.pullback (spMap (algebraMap T K))
  let i : Φ.obj G ⟶ Φ.obj (G ⊗ G') := lift (𝟙 _) f ≫ Functor.LaxMonoidal.μ Φ G G'
  have hi : IsMonHom i := inferInstance
  have hi1 : i ≫ Φ.map (fst G G') = 𝟙 _ := by
    rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
  have hi2 : i ≫ Φ.map (snd G G') = f := by simp [i]
  have hs1 : IsSeparated (fst G G').left := inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom))
  have hs2 : LocallyOfFiniteType (fst G G').left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom))
  have hs3 : QuasiCompact (fst G G').left :=
    inferInstanceAs (QuasiCompact (pullback.fst G.hom G'.hom))
  have hsP : IsSeparated (G ⊗ G').hom :=
    inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom ≫ G.hom))
  have hlP : LocallyOfFiniteType (G ⊗ G').hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom ≫ G.hom))
  have hs4 : IsSeparated (Φ.map (fst G G')).left := by
    have h1 : IsSeparated (Φ.obj (G ⊗ G')).hom :=
      inferInstanceAs (IsSeparated (pullback.snd (G ⊗ G').hom _))
    rw [← Over.w (Φ.map (fst G G'))] at h1
    exact IsSeparated.of_comp _ (Φ.obj G).hom
  have hic : IsClosedImmersion i.left := by
    have h1 : IsClosedImmersion (i.left ≫ (Φ.map (fst G G')).left) := by
      rw [← Over.comp_left, hi1, Over.id_left]; infer_instance
    exact IsClosedImmersion.of_comp i.left (Φ.map (fst G G')).left
  obtain ⟨Ga, io, e, hio, hGa, he⟩ := exists_flat_closure T K (G ⊗ G') (Φ.obj G) i hic
  obtain ⟨_, hio', -, hc⟩ := flat_closure_subgroup T K (G ⊗ G') Ga io (Φ.obj G) i e hio hGa hi he
  have := hc inferInstance
  have hp : IsMonHom (io ≫ fst G G') := inferInstance
  have hpK : Φ.map (io ≫ fst G G') = e.hom := by
    rw [Functor.map_comp, ← he, Category.assoc, hi1, Category.comp_id]
  have hpKi : IsIso (Φ.map (io ≫ fst G G')) := by rw [hpK]; infer_instance
  have hGaS : IsSeparated Ga.hom := by rw [← Over.w io]; infer_instance
  have hGaL : LocallyOfFiniteType Ga.hom := by rw [← Over.w io]; infer_instance
  have hp1 : IsSeparated (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp2 : LocallyOfFiniteType (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp3 : QuasiCompact (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hnt := KernelNoTorsion.eq_one_of_pow_eq_one_of_comp_eq_one T K Ga G (io ≫ fst G G') n hp hGaS
    (etale_mulN_torsion_dvr T Ga n hnT hGa hGaL).2
    (etale_mulN_torsion_dvr T G n hnT hGflat inferInstance).2 hpKi
  have hnS : IsUnit (n : Γ(Sp T, ⊤)) := by
    simpa using hnT.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  have hker := finite_geometric_kernel_of_pow_eq_one hfin (Sp T) G G' Ga io n hG' hio' hio hn hnS hnt
  have hqf := locallyQuasiFinite_of_finite_geometric_ker (Sp T) Ga G (io ≫ fst G G') hp hp2 hp3 hker
  have hiso := isIso_of_quasiFinite_of_isIso_genericFibre_dvr T K Ga G (io ≫ fst G G') hp hGa hp1 hp2
    hp3 hqf hG.smooth hG.geomConnected hpKi
  have hF : Φ.map (inv (io ≫ fst G G') ≫ io ≫ snd G G') = f := by
    rw [Functor.map_comp, Functor.map_inv, IsIso.inv_comp_eq, hpK, Functor.map_comp, ← he,
      Category.assoc, hi2]
  refine ⟨inv (io ≫ fst G G') ≫ io ≫ snd G G', ⟨?_, hF⟩, fun F hF' => ?_⟩
  · refine flat_dvr_generic_fibre.2.2 T K G G' _ hGflat hG'.separated ?_
    exact hF ▸ hf
  · exact flat_dvr_generic_fibre.1 T K G G' hGflat hG'.separated _ _ (hF'.2.trans hF.symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOfImHermFormEq
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.UnitDet

theorem eq_of_im_hermForm_eq {g : ℕ} (S : Set (Fin g → ℂ)) (hS : Submodule.span ℝ S = ⊤)
    (A B : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ z ∈ S, ∀ w ∈ S, (hermForm A z w).im = (hermForm B z w).im) : A = B := by
  have h1 : ∀ z, ∀ w ∈ S, (hermForm A z w).im = (hermForm B z w).im := by
    intro z w hw
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact h x hx w hw
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, add_dotProduct, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, smul_dotProduct, Complex.smul_im] at hx ⊢
      rw [hx]
  have h2 : ∀ z w, (hermForm A z w).im = (hermForm B z w).im := by
    intro z w
    have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx => exact h1 z x hx
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul a x _ hx =>
      simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im] at hx ⊢
      rw [hx]
  ext i j
  have e1 := h2 (Pi.single i 1) (Pi.single j 1)
  have e2 := h2 (Pi.single i Complex.I) (Pi.single j 1)
  simp [hermForm] at e1 e2
  exact Complex.ext e2 e1

theorem hermForm_mulVec {g : ℕ} (A h : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm A (h *ᵥ z) (h *ᵥ w) = hermForm (hᵀ * (A * h.map (starRingEnd ℂ))) z w := by
  have : star (h *ᵥ w) = h.map (starRingEnd ℂ) *ᵥ star w := by
    ext a; simp [Matrix.mulVec, dotProduct]
  rw [hermForm, hermForm, this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec z, Matrix.vecMul_transpose]

theorem det_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ x ∈ (M.X k).dom, (∀ τ i, ‖dmin (M.X k).Gm x τ i‖ = 1) → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ a b, (hermForm Hm (Pf x a) (Pf x b)).im = (F.Di k).EF a b) → Hm.det = ((∏ j, (2 * ‖relab c σ (e j).1 (M.X k).ξ0‖) : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x hx hu Hm hHm
  obtain ⟨hl1, hl2, -⟩ := GlobalTheory.T.unitFrame_eq_orthonormal_mul_triangular E r (M.X k).p0 (M.X k).Ψ (M.X k).Gm (M.X k).Gm_herm
  obtain ⟨x₀, b, hb, hgr, hb1, rfl⟩ := hl1 x hx hu
  have hx₀ : x₀ ∈ (M.X k).dom := (hl2 x₀ hgr).1
  obtain ⟨h₀, -, hh, -, -, hdet, -⟩ :=
    GlobalTheory.T.triangularFrame_moves_period_blockTriangular E H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x₀ hx₀ b hb
  replace hdet := hdet hb1
  obtain ⟨Pf', -, huniq, hper, -⟩ := GlobalTheory.T.exists_framePeriods_alt E H Dw l Xo c σ g e F r M hG hB hN k
  obtain rfl := huniq Pf hPf
  have hspan := (hper x₀ hx₀).2.2.2.1
  obtain ⟨⟨idx, hty, -, hfr⟩, hp, -, hξ, hpos, hφ⟩ := GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hG hB hN k
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hD := GlobalTheory.UnitFrame.im_hermForm_eq E H (F.Di k) r (-(M.X k).ξ0) (M.X k).Gm φ (M.X k).Ψ
    (hB.type k).2 g idx (fun j => relab c σ (e j).1) hty hξ hpos (hφ φ fun _ => rfl).2 x₀ (Pf x₀)
    (fun v j => by rw [hPf, hfr]; rfl) (fun τ => by rw [← hp]; exact hgr τ)
  have key : h₀ᵀ * (Hm * h₀.map (starRingEnd ℂ)) =
      Matrix.diagonal fun j => ((2 * ‖(idx j).1.1 (-(M.X k).ξ0)‖ : ℝ) : ℂ) := by
    refine eq_of_im_hermForm_eq _ hspan _ _ ?_
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [hD, ← hermForm_mulVec, ← hh, ← hh, hHm]
  have h1 := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h1
  have h2 : h₀.det * starRingEnd ℂ h₀.det = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hdet]; simp
  have h3 : Hm.det = h₀.det * (Hm.det * starRingEnd ℂ h₀.det) := by
    linear_combination (-Hm.det) * h2
  rw [h3, h1, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hty j, map_neg, norm_neg]
  split_ifs
  · rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
  · rfl

end GlobalTheory.UnitDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDiscreteArithGroupImageRealUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDiscreteArithGroupImageRealUnitary
set_option autoImplicit false

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.ArithImage

open GlobalTheory.PeterssonCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem frameOf_one : frameOf X 1 = baseFr X := by
  funext τ
  show mat (frameOf X 1) τ = mat (baseFr X) τ
  rw [mat_frameOf]
  simp

theorem lact_one_fr (y : Frame X.Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ = mat y τ
  simp

theorem lact_mul_fr (a b : GL (Fin r) E) (y : Frame X.Ψ r) : lact (a * b) y = lact a (lact b y) := by
  funext τ
  show ((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ =
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

def image : Subgroup (RealGrp X) where
  carrier := {s | ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s}
  one_mem' := ⟨1, X.Γ.one_mem, by rw [lact_one_fr, frameOf_one]⟩
  mul_mem' := by
    rintro s t ⟨γ, hγ, e⟩ ⟨δ, hδ, f⟩
    exact ⟨γ * δ, X.Γ.mul_mem hγ hδ, by rw [lact_mul_fr, f, lact_frameOf X e]⟩
  inv_mem' := by
    rintro s ⟨γ, hγ, e⟩
    refine ⟨γ⁻¹, X.Γ.inv_mem hγ, ?_⟩
    have h := lact_frameOf X e s⁻¹
    rw [mul_inv_cancel, frameOf_one] at h
    rw [← h, ← lact_mul_fr, inv_mul_cancel, lact_one_fr]

def smallSet : Set (RealGrp X) :=
  {s | ∀ (τ : X.Ψ) (a b : Fin r), ‖(mat (frameOf X s) τ * (mat (baseFr X) τ)⁻¹) a b‖ < 2}

theorem isOpen_smallSet : IsOpen (smallSet X) := by
  unfold smallSet
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b => ?_
  refine isOpen_lt (Continuous.norm ?_) continuous_const
  have h : Continuous fun s : RealGrp X =>
      mat (baseFr X) τ * ((s τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat (baseFr X) τ)⁻¹ :=
    (continuous_const.matrix_mul (Units.continuous_val.comp
      (continuous_subtype_val.comp (continuous_apply τ)))).matrix_mul continuous_const
  exact h.matrix_elem a b

theorem one_mem_smallSet : (1 : RealGrp X) ∈ smallSet X := by
  intro τ a b
  rw [frameOf_one, Matrix.mul_nonsing_inv _ (det_baseFr X τ).isUnit, Matrix.one_apply]
  split_ifs <;> simp

theorem finite_image_inter : ((image X : Set (RealGrp X)) ∩ smallSet X).Finite := by
  refine Set.Finite.of_finite_image (f := frameOf X) ?_ (frameOf_injective X).injOn
  refine (((GlobalTheory.LatFin.latFin (E := E)).2 r X 2).image fun γ => lact γ (baseFr X)).subset ?_
  rintro _ ⟨s, ⟨⟨γ, hγ, e⟩, hs⟩, rfl⟩
  refine ⟨γ, ⟨X.Γ_stab γ hγ, fun τ a b => ?_⟩, e⟩
  have h1 : (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (baseFr X) τ = mat (frameOf X s) τ := congrFun e τ
  have h2 := hs τ a b
  rw [← h1, Matrix.mul_nonsing_inv_cancel_right _ _ (det_baseFr X τ).isUnit] at h2
  exact h2.le

theorem exists_discrete_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∃ Λ : Subgroup (RealGrp X), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) ∧ ∃ W ∈ 𝓝 (1 : RealGrp X), ∀ w ∈ Λ, w ∈ W → w = 1 := by
  intro E _ _ _ r X
  refine ⟨image X, fun _ => Iff.rfl, smallSet X \ (((image X : Set (RealGrp X)) ∩ smallSet X) \ {1}), ?_, ?_⟩
  · exact ((isOpen_smallSet X).sdiff ((finite_image_inter X).subset Set.diff_subset).isClosed).mem_nhds
      ⟨one_mem_smallSet X, fun h => h.2 rfl⟩
  · intro w hw hW
    by_contra hne
    exact hW.2 ⟨⟨hw, hW.1⟩, hne⟩

end GlobalTheory.ArithImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDiscreteArithGroupImageRealUnitaryStatement
open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_discrete_arithGroupImage_realUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∃ Λ : Subgroup (RealGrp X), (∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) ∧ ∃ W ∈ 𝓝 (1 : RealGrp X), ∀ w ∈ Λ, w ∈ W → w = 1 := by
  first | exact @GlobalTheory.ArithImage.exists_discrete_image | exact GlobalTheory.ArithImage.exists_discrete_image | (intros; apply GlobalTheory.ArithImage.exists_discrete_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsGermGIffExistsFrame
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GermSectionCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws GlobalTheory.IndefiniteRowSideFullHecke.RigidAdjointFrameLaws GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveGermFrames Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

section General

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem isGen_iff_gm {M : LB Y} (t : LB.Gen M) :
    t.IsGen ↔ ∀ i j y, y ∈ M.U i ⊓ M.U j →
      gm (𝟙 Y) y (M.U i) (t.s i) = gm (𝟙 Y) y (M.U i ⊓ M.U j) (M.g i j) * gm (𝟙 Y) y (M.U j) (t.s j) := by
  constructor
  · intro h i j y hy
    exact (gm_res (𝟙 Y) y _ hy _).symm.trans ((congrArg (gm (𝟙 Y) y _) (h i j)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))))
  · intro h i j
    exact unit_ext fun y hy => (gm_res (𝟙 Y) y _ hy _).trans ((h i j y hy).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))).symm)

theorem le_div (φ : K → (X ⟶ X)) (ε : K → ℤ) (j : Fin 1 ⊕ K → L.ι) :
    LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j ≤
      (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)) := fun _ hy =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k), Set.mem_iInter.1 hy (Sum.inl 0)⟩

theorem div_le (φ : K → (X ⟶ X)) (ε : K → ℤ) (p : (K → L.ι) × L.ι) :
    (LB.div (LB.LinComb L φ ε) L).U p ≤
      LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => p.2) p.1) := fun _ hy =>
  Set.mem_iInter.2 fun k => by
    rcases k with k | k
    · exact hy.2
    · exact Set.mem_iInter.1 hy.1 k

omit [Fintype K] in
theorem idx_split (j : Fin 1 ⊕ K → L.ι) : ∃ p : (K → L.ι) × L.ι, j = Sum.elim (fun _ => p.2) p.1 :=
  ⟨(j ∘ Sum.inr, j (Sum.inl 0)), funext fun k => by
    rcases k with k | k
    · rw [Subsingleton.elim k 0]; rfl
    · rfl⟩

def divEquiv (φ : K → (X ⟶ X)) (ε : K → ℤ) : LB.Iso L (LB.LinComb L φ ε) ≃
    LB.Gen (LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)) where
  toFun w := ⟨fun j => res (le_div φ ε j) (w.s (j ∘ Sum.inr, j (Sum.inl 0)))⁻¹⟩
  invFun v := ⟨fun p => res (div_le φ ε p) (v.s (Sum.elim (fun _ => p.2) p.1))⁻¹⟩
  left_inv w := by
    obtain ⟨s⟩ := w
    refine congrArg LB.Gen.mk (funext fun p => unit_ext fun y hy => ?_)
    refine (gm_res _ y _ hy _).trans ((map_inv _ _).trans (inv_eq_iff_eq_inv.2 ?_))
    exact (gm_res _ y _ (div_le φ ε p hy) _).trans (map_inv _ _)
  right_inv v := by
    obtain ⟨s⟩ := v
    refine congrArg LB.Gen.mk (funext fun j => ?_)
    obtain ⟨p, rfl⟩ := idx_split j
    refine unit_ext fun y hy => ?_
    refine (gm_res _ y _ hy _).trans ((map_inv _ _).trans (inv_eq_iff_eq_inv.2 ?_))
    exact (gm_res _ y _ (le_div φ ε _ hy) _).trans (map_inv _ _)

theorem gm_g_div (φ : K → (X ⟶ X)) (ε : K → ℤ) (i j : Fin 1 ⊕ K → L.ι) (y : X)
    (hi : y ∈ LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) i)
    (hj : y ∈ LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j) :
    gm (𝟙 X) y _ ((LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)).g i j) =
      (gm (𝟙 X) y _ ((LB.div (LB.LinComb L φ ε) L).g (i ∘ Sum.inr, i (Sum.inl 0)) (j ∘ Sum.inr, j (Sum.inl 0))))⁻¹ := by
  have hi' := le_div φ ε i hi
  have hj' := le_div φ ε j hj
  refine (gm_linComb L _ _ (𝟙 _) y i j hi hj).trans (inv_eq_iff_eq_inv.1 (Eq.symm ?_))
  refine (gm_div L (LB.LinComb L φ ε) (𝟙 X) y (i ∘ Sum.inr, i (Sum.inl 0)) (j ∘ Sum.inr, j (Sum.inl 0))
    ⟨hi', hj'⟩).trans ?_
  refine (congrArg₂ (· * ·) (gm_linComb L φ ε (𝟙 _) y _ _ hi'.1 hj'.1) rfl).trans ?_
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Fin.prod_univ_one, zpow_one,
    Category.comp_id, Category.id_comp, mul_inv_rev, inv_inv]
  rfl

theorem isGen_divEquiv (φ : K → (X ⟶ X)) (ε : K → ℤ) (w : LB.Iso L (LB.LinComb L φ ε)) :
    (divEquiv φ ε w).IsGen ↔ w.IsGen := by
  have hv : ∀ (j : Fin 1 ⊕ K → L.ι) (y : X), y ∈ LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j →
      gm (𝟙 X) y (LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j) ((divEquiv φ ε w).s j) =
        (gm (𝟙 X) y _ (w.s (j ∘ Sum.inr, j (Sum.inl 0))))⁻¹ := fun j y hy =>
    (gm_res _ y _ hy _).trans (map_inv _ _)
  rw [isGen_iff_gm, isGen_iff_gm]
  constructor
  · intro h p q y hy
    have hp := div_le φ ε p hy.1
    have hq := div_le φ ε q hy.2
    have e := (hv _ y hp).symm.trans ((h _ _ y ⟨hp, hq⟩).trans
      (congrArg₂ (· * ·) (gm_g_div φ ε _ _ y hp hq) (hv _ y hq)))
    exact inv_injective (e.trans (mul_inv _ _).symm)
  · intro h i j y hy
    have e := h (i ∘ Sum.inr, i (Sum.inl 0)) (j ∘ Sum.inr, j (Sum.inl 0)) y ⟨le_div φ ε i hy.1, le_div φ ε j hy.2⟩
    exact (hv i y hy.1).trans (((congrArg (·⁻¹) e).trans (mul_inv _ _)).trans
      (congrArg₂ (· * ·) (gm_g_div φ ε i j y hy.1 hy.2) (hv j y hy.2)).symm)

end General

section Jets

variable {S : Type} [CommRing S] {d : ℕ}

end Jets

section Compare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X₀ : Scheme.{0}} (t : SAB H X₀)

variable {S : Type} [CommRing S] (x : Sp S ⟶ X₀) {d : ℕ}

variable {t x}

variable {j : JetPts t.G x d} (act : 𝓞 E → Germ.Pt S 1 d) (e : FrameFam t.G x t.PP.L j) (w : PrimIso t)

end Compare

end GlobalTheory.GermSectionCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMeasurePreservingFrameChangeProportionalHe
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMeasurePreservingFrameChangeProportionalHe
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PeterssonFrameChange

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

variable {r : ℕ}

set_option autoImplicit false in
private lemma det_ne_zero_of_form_eq {K G M : Matrix (Fin r) (Fin r) ℂ} (hK : K.det ≠ 0)
    (h : Mᵀ * G * M.map (starRingEnd ℂ) = K) : M.det ≠ 0 := by
  intro hM0
  apply hK
  rw [← h, det_mul, det_mul, det_transpose, hM0, zero_mul, zero_mul]

set_option autoImplicit false in
private lemma form_smul_left_automorphic_membership (c : ℂ) (K A : Matrix (Fin r) (Fin r) ℂ) :
    Aᵀ * (c • K) * A.map (starRingEnd ℂ) = c • (Aᵀ * K * A.map (starRingEnd ℂ)) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

set_option autoImplicit false in
private lemma form_smul_right_automorphic_membership (a : ℝ) (K A : Matrix (Fin r) (Fin r) ℂ) :
    ((a : ℂ) • A)ᵀ * K * ((a : ℂ) • A).map (starRingEnd ℂ) =
      ((a ^ 2 : ℝ) : ℂ) • (Aᵀ * K * A.map (starRingEnd ℂ)) := by
  rw [transpose_smul]
  have : ((a : ℂ) • A).map (starRingEnd ℂ) = (a : ℂ) • A.map (starRingEnd ℂ) := by
    ext i j
    simp
  rw [this, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  push_cast
  ring

set_option autoImplicit false in
private lemma form_mul' (K A B : Matrix (Fin r) (Fin r) ℂ) :
    (A * B)ᵀ * K * (A * B).map (starRingEnd ℂ) =
      Bᵀ * (Aᵀ * K * A.map (starRingEnd ℂ)) * B.map (starRingEnd ℂ) := by
  rw [transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

set_option autoImplicit false in
private lemma form_one' (K : Matrix (Fin r) (Fin r) ℂ) :
    (1 : Matrix (Fin r) (Fin r) ℂ)ᵀ * K * (1 : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = K := by
  simp [Matrix.map_one]

set_option autoImplicit false in
private lemma form_conj_eq_of_similitude {J B g : Matrix (Fin r) (Fin r) ℂ} {c : ℂ} (hc : c ≠ 0) (hB : B.det ≠ 0)
    (hsim : Bᵀ * J * B.map (starRingEnd ℂ) = c • J) (hg : gᵀ * J * g.map (starRingEnd ℂ) = J) :
    (B⁻¹ * g * B)ᵀ * J * (B⁻¹ * g * B).map (starRingEnd ℂ) = J := by
  have hinv : (B⁻¹)ᵀ * J * (B⁻¹).map (starRingEnd ℂ) = c⁻¹ • J := by
    have h1 : (B * B⁻¹)ᵀ * J * (B * B⁻¹).map (starRingEnd ℂ) = J := by
      rw [mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB), form_one']
    rw [form_mul', hsim, form_smul_left_automorphic_membership] at h1
    calc (B⁻¹)ᵀ * J * (B⁻¹).map (starRingEnd ℂ)
        = c⁻¹ • (c • ((B⁻¹)ᵀ * J * (B⁻¹).map (starRingEnd ℂ))) := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = c⁻¹ • J := by rw [h1]
  rw [form_mul', form_mul', hinv, form_smul_left_automorphic_membership, hg, form_smul_left_automorphic_membership, hsim, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

set_option autoImplicit false in
private lemma exists_transport_haarU_pi {ι : Type} (Ψ Ψ' : Finset ι) (p p' : ℕ) (hΨ : Ψ = Ψ')
    (hp : p = p') :
    ∃ e : (Ψ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r p) ≃ᵐ (Ψ' → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r p'),
      MeasurePreserving e (Measure.pi fun _ => _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.haarU r p)
        (Measure.pi fun _ => _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.haarU r p') ∧
      ∀ t (τ : Ψ) (τ' : Ψ'), τ.1 = τ'.1 → ((e t τ' : GL (Fin r) ℂ)) = (t τ : GL (Fin r) ℂ) := by
  subst hΨ hp
  refine ⟨MeasurableEquiv.refl _, MeasurePreserving.id _, fun t τ τ' h => ?_⟩
  rw [Subtype.ext h]
  rfl

set_option autoImplicit false in
theorem _root_.GlobalTheory.PeterssonFrameChange.frame_change : ∀ (E : Type) [Field E]
    [NumberField E] [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)
    (y' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X'.Ψ r), X.Ψ = X'.Ψ → X.p0 = X'.p0 → y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.OrthFr X →
    y' ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.OrthFr X' →
    (∀ (τ : X.Ψ), ∃ t : ℝ, t ≠ 0 ∧ X'.Gm.map τ.1 = (t : ℂ) • X.Gm.map τ.1) →
    ∃ (e : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X ≃ᵐ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X')
      (α : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X)
      (u : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X),
      MeasurePreserving e (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.haarR X) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.haarR X') ∧
      Measurable α ∧ (∀ t, α (α t) = u⁻¹ * t * u) ∧
      ∀ t (τ : X.Ψ) (τ' : X'.Ψ), τ.1 = τ'.1 →
        _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' τ' * ((e (α t) τ' : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
            (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' τ')⁻¹ =
          _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ)⁻¹ := by
  intro E _ _ _ r X X' y y' hΨ hp hy hy' hG
  choose tf htf hGt using hG
  set J := _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.sgnMat r X.p0 with hJdef
  have hJJ : J * J = 1 := by
    rw [hJdef, _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.sgnMat, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> simp
  have hJdet : J.det ≠ 0 := by
    intro h
    have := congrArg det hJJ
    rw [det_mul, h, zero_mul, det_one] at this
    exact zero_ne_one this
  let τ' : X.Ψ → X'.Ψ := fun τ => ⟨τ.1, hΨ ▸ τ.2⟩
  have hy0 : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ) = J := hy
  have hy0' : ∀ τ : X'.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X'.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' τ) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.sgnMat r X'.p0 := hy'
  have hM : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ)ᵀ * X.Gm.map τ.1 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ).map (starRingEnd ℂ) = J := by
    intro τ
    have := hy0 τ
    rwa [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq] at this
  have hM' : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))ᵀ * X'.Gm.map τ.1 *
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ)).map (starRingEnd ℂ) = J := by
    intro τ
    have := hy0' (τ' τ)
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.gram_eq, ← hp] at this
    exact this
  have hMdet : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ).det ≠ 0 := fun τ => det_ne_zero_of_form_eq hJdet (hM τ)
  have hM'det : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ)).det ≠ 0 := fun τ => det_ne_zero_of_form_eq hJdet (hM' τ)
  set B : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ =>
    ((Real.sqrt |tf τ| : ℝ) : ℂ) • ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ)⁻¹ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ)) with hBdef
  set s : X.Ψ → ℂ := fun τ => ((|tf τ| / tf τ : ℝ) : ℂ) with hsdef
  have hs0 : ∀ τ, s τ ≠ 0 := by
    intro τ
    simp only [hsdef]
    exact_mod_cast div_ne_zero (abs_ne_zero.mpr (htf τ)) (htf τ)
  have hs2 : ∀ τ, s τ * s τ = 1 := by
    intro τ
    simp only [hsdef]
    rw [← Complex.ofReal_mul, ← sq, div_pow, sq_abs, div_self (pow_ne_zero _ (htf τ)), Complex.ofReal_one]
  have hsim : ∀ τ : X.Ψ, (B τ)ᵀ * J * (B τ).map (starRingEnd ℂ) = s τ • J := by
    intro τ
    have ht := htf τ
    have h1 : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))ᵀ * X.Gm.map τ.1 * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ)).map (starRingEnd ℂ) =
        ((tf τ : ℝ) : ℂ)⁻¹ • J := by
      have := hM' τ
      rw [hGt τ, form_smul_left_automorphic_membership] at this
      rw [← this, smul_smul, inv_mul_cancel₀ (by exact_mod_cast ht), one_smul]
    simp only [hBdef, hsdef]
    rw [form_smul_right_automorphic_membership, Real.sq_sqrt (abs_nonneg _)]
    conv_lhs => rw [← hM τ]
    rw [← form_mul', mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (hMdet τ)), h1, smul_smul]
    congr 1
    push_cast
    ring
  have hBdet : ∀ τ, (B τ).det ≠ 0 := by
    intro τ
    refine det_ne_zero_of_form_eq ?_ (hsim τ)
    rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ (hs0 τ)) hJdet
  let Bu : X.Ψ → GL (Fin r) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero (B τ) (hBdet τ)
  have hBu : ∀ τ, ((Bu τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = B τ := fun τ => rfl
  have hBuinv : ∀ τ, (((Bu τ)⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (B τ)⁻¹ := by
    intro τ
    rw [Matrix.coe_units_inv, hBu]
  have hmem : ∀ g : GL (Fin r) ℂ, g ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r X.p0 ↔
      (g : Matrix (Fin r) (Fin r) ℂ)ᵀ * J * (g : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = J :=
    fun g => Iff.rfl
  have hαmem : ∀ (g : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r X.p0) (τ : X.Ψ),
      (Bu τ)⁻¹ * (g : GL (Fin r) ℂ) * Bu τ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r X.p0 := by
    intro g τ
    rw [hmem, Units.val_mul, Units.val_mul, hBuinv, hBu]
    exact form_conj_eq_of_similitude (hs0 τ) (hBdet τ) (hsim τ) ((hmem g).mp g.2)
  have humem : ∀ τ : X.Ψ, Bu τ * Bu τ ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r X.p0 := by
    intro τ
    rw [hmem, Units.val_mul, hBu, form_mul', hsim, form_smul_left_automorphic_membership, hsim, smul_smul, hs2, one_smul]
  let α : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X :=
    fun t τ => ⟨(Bu τ)⁻¹ * (t τ : GL (Fin r) ℂ) * Bu τ, hαmem (t τ) τ⟩
  let u : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.RealGrp X := fun τ => ⟨Bu τ * Bu τ, humem τ⟩
  obtain ⟨e, he, hecoe⟩ := exists_transport_haarU_pi (r := r) X.Ψ X'.Ψ X.p0 X'.p0 hΨ hp
  refine ⟨e, α, u, he, ?_, ?_, ?_⟩
  · have hcont : Continuous α := by
      refine continuous_pi fun τ => Continuous.subtype_mk ?_ _
      exact (continuous_const.mul ((continuous_apply τ).subtype_val)).mul continuous_const
    exact hcont.measurable
  · intro t
    funext τ
    apply Subtype.ext
    show (Bu τ)⁻¹ * ((Bu τ)⁻¹ * (t τ : GL (Fin r) ℂ) * Bu τ) * Bu τ =
      (Bu τ * Bu τ)⁻¹ * (t τ : GL (Fin r) ℂ) * (Bu τ * Bu τ)
    group
  · intro t τ σ hτσ
    obtain rfl : σ = τ' τ := Subtype.ext hτσ.symm
    rw [hecoe (α t) τ (τ' τ) rfl]
    show _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) * (((Bu τ)⁻¹ * (t τ : GL (Fin r) ℂ) * Bu τ : GL (Fin r) ℂ) :
      Matrix (Fin r) (Fin r) ℂ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))⁻¹ = _
    rw [Units.val_mul, Units.val_mul, hBuinv, hBu]
    set c : ℂ := ((Real.sqrt |tf τ| : ℝ) : ℂ) with hc
    have hc0 : c ≠ 0 := by
      simp only [hc]
      exact_mod_cast (Real.sqrt_pos.mpr (abs_pos.mpr (htf τ))).ne'
    have hMB : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ * B τ = c • _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) := by
      simp only [hBdef]
      rw [Matrix.mul_smul, mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr (hMdet τ))]
    have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) * (B τ)⁻¹ = c⁻¹ • _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ := by
      have : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) = c⁻¹ • (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ * B τ) := by
        rw [hMB, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [this, Matrix.smul_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hBdet τ)), Matrix.mul_one]
    have h2 : B τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))⁻¹ = c • (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y τ)⁻¹ := by
      simp only [hBdef]
      rw [Matrix.smul_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hM'det τ)), Matrix.mul_one]
    calc _root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) * ((B τ)⁻¹ * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * B τ) *
          (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))⁻¹
        = (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ) * (B τ)⁻¹) * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
          (B τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat y' (τ' τ))⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [h1, h2]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc0, inv_mul_cancel₀ hc0,
          one_smul]

end GlobalTheory.PeterssonFrameChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMeasurePreservingFrameChangeProportionalHeStatement
open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurePreserving_frameChange_proportional_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (y : Frame X.Ψ r) (y' : Frame X'.Ψ r), X.Ψ = X'.Ψ → X.p0 = X'.p0 → y ∈ OrthFr X → y' ∈ OrthFr X' → (∀ (τ : X.Ψ), ∃ t : ℝ, t ≠ 0 ∧ X'.Gm.map τ.1 = (t : ℂ) • X.Gm.map τ.1) → ∃ (e : RealGrp X ≃ᵐ RealGrp X') (α : RealGrp X → RealGrp X) (u : RealGrp X), MeasurePreserving e (haarR X) (haarR X') ∧ Measurable α ∧ (∀ t, α (α t) = u⁻¹ * t * u) ∧ ∀ t (τ : X.Ψ) (τ' : X'.Ψ), τ.1 = τ'.1 → mat y' τ' * ((e (α t) τ' : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat y' τ')⁻¹ = mat y τ * ((t τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat y τ)⁻¹ := by
  first | exact @GlobalTheory.PeterssonFrameChange.frame_change | exact GlobalTheory.PeterssonFrameChange.frame_change | (intros; apply GlobalTheory.PeterssonFrameChange.frame_change <;> assumption)
end
end
