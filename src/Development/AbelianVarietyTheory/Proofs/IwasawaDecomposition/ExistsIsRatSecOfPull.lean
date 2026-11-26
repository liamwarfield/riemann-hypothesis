module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGeneric
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupAtPlaceDenseInDecompositionGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar
open scoped Pointwise

namespace GlobalTheory.TrueGeo.SmallSec

variable {F : Type} [Field F] [NumberField F]

section Local

variable {Z : Scheme.{0}} [IsIntegral Z] {D : CartierDiv Z} {x : Z} {u g : Z.functionFieldˣ}
  {f : Z.functionField} {k τ : ℕ}

end Local

variable {C : CxSt F} {Y : Var F} (A : Adl C Y) {k τ : ℕ} {f : Y.Fn}

theorem isRatSec_pow {Z : Scheme.{0}} [IsIntegral Z] {L : LB Z} {r : L.ι → Z.functionFieldˣ}
    (hr : IsRatSec L r) (τ : ℕ) : IsRatSec (lbPow L τ) fun c => r (c PUnit.unit) ^ τ :=
  fun c c' h => by
  have l : (lbPow L τ).U c ⊓ (lbPow L τ).U c' ≤ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have e : (lbPow L τ).g c c' = res l (L.g (c PUnit.unit) (c' PUnit.unit)) ^ τ := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    ← mul_pow, hr _ _ (l h)]
  exact congrArg (fun a => (a * _) ^ τ) (fnOf_resG l h _).symm


end GlobalTheory.TrueGeo.SmallSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts

namespace GlobalTheory.ProjModel

theorem isArithVar_pspace (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k]
    (hd : ringKrullDim k = 1) (N : ℕ) : IsArithVar (PSpace.str k N) N := by
  have := isIntegral_of_isDomain k N
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : Smooth (PSpace.str k N) := SmoothOfRelativeDimension.smooth N _
  have hc : ∀ i, topologicalKrullDim (chart k N i : Set (PSpace k N)) = (N + 1 : ℕ) := fun i => by
    rw [topologicalKrullDim_eq_of_isEmbedding (chartι k N i).isOpenEmbedding.isEmbedding
      (congrArg SetLike.coe (opensRange_chartι k N i))]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim
      (R := MvPolynomial {j // j ≠ i} k)).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hd]
    simp [add_comm]
  refine ⟨inferInstance, inferInstance, ‹_›, ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩, ?_,
    le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_)
      ((hc 0).ge.trans (topologicalKrullDim_subspace_le _ _))⟩
  · have h := (ArithBase.isArithVar_id hd).flat
    rw [Category.id_comp] at h
    infer_instance
  · obtain ⟨i, hi⟩ := exists_mem_chart k N x
    exact ⟨_, (chart k N i).isOpen, hi, (hc i).le⟩

theorem nefFib_of_isAmpleLB {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsProper p]
    (L : HermLB p) (hL : IsAmpleLB L.B) : ArInt.NefFib L := by
  intro Z i _ _ κ _ _ _ hd
  have hA := hL.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 (hA.isNef (k := κ))).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

end GlobalTheory.ProjModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

theorem cls_eq_zero_of_chart_eq_top {Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (i₀ : L.ι)
    (h : L.U i₀ = ⊤) : cls L hL = 0 := by
  have le : ∀ j, L.U j ≤ L.U j ⊓ L.U i₀ := fun j => le_inf le_rfl (h ▸ le_top)
  have hm : ∀ y : Z, y ∈ L.U i₀ := fun y => h ▸ Opens.mem_top y
  have H : ∃ t : LB.Gen L, t.IsGen :=
    ⟨⟨fun j => res (le j) (L.g j i₀)⟩, fun i j => unit_ext fun y hy => by
      rw [map_mul, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.1, gm_res (𝟙 Z) y _ hy, gm_res (𝟙 Z) y _ hy.2]
      exact (gm_cocycle hL (𝟙 Z) y hy.1 hy.2 (hm y)).symm⟩
  exact (cls_eq_iff hL (LB.isLB_triv Z)).2 (LBIso.symm ((iso_triv_iff L).2 H))

theorem topSelf_pull_eq_zero_of_const {X Z : Scheme.{0}} (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)]
    {M : LB X} (hM : M.IsLB) (g : Z ⟶ X) (x : X) (hg : ∀ z, g z = x) :
    topSelfIntersection κ (M.pull g) 1 = 0 := by
  obtain ⟨i, hi⟩ := exists_chart hM x
  have h := cls_eq_zero_of_chart_eq_top (pull_isLB hM g) (fun _ => i)
    (top_le_iff.1 fun z _ => mem_pull.2 ((hg z).symm ▸ hi))
  exact interNum_eq_zero_of_cls_eq_zero κ _ (fun _ => pull_isLB hM g) 0 h

theorem isProper_strHom (κ : Type) [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] (t : Z ⟶ Sp ℤ)
    [IsProper t] : IsProper (strHom κ (X := Z)) := by
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = t := specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  exact IsProper.of_comp _ (spMap (Int.castRingHom κ))

theorem appTop_injective_of_denseRange {Z W : Scheme.{0}} [IsReduced Z] (φ : W ⟶ Z)
    (h : DenseRange φ) : Function.Injective φ.appTop.hom := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  by_contra hne0
  have hne : Z.basicOpen a ≠ ⊥ := fun h0 => hne0 ((basicOpen_eq_bot_iff a).1 h0)
  obtain ⟨w, hw⟩ := h.exists_mem_open (Z.basicOpen a).isOpen
    (Set.nonempty_iff_ne_empty.2 fun e => hne (Opens.ext e))
  have e : φ ⁻¹ᵁ Z.basicOpen a = W.basicOpen (φ.appTop.hom a) := Scheme.preimage_basicOpen_top φ a
  have hw' : w ∈ W.basicOpen (φ.appTop.hom a) := e ▸ hw
  rw [ha, Scheme.basicOpen_zero] at hw'
  exact hw'

section

attribute [local instance low] specializationOrder

theorem one_le_dim {S : Type} [TopologicalSpace S] [QuasiSober S] [T0Space S] {a b : S} (h : a ⤳ b)
    (hne : a ≠ b) : 1 ≤ topologicalKrullDim S := by
  rw [PosBaseChange.dim_eq_krullDim]
  exact Order.one_le_krullDim_iff.2 ⟨b, a, lt_of_le_of_ne h hne.symm⟩

end

section Curve

variable {X W : Scheme.{0}} [IsIntegral W] (ℓ : ℕ) [Fact ℓ.Prime] [Algebra (ZMod ℓ) Γ(W, ⊤)]

theorem topSelf_pull_nonneg (t : X ⟶ Sp ℤ) [IsProper t] (hd : topologicalKrullDim W = 1)
    {M : LB X} (hM : M.IsLB) (g : W ⟶ X) [IsProper (g ≫ t)]
    (H : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      [Algebra (ZMod ℓ) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod ℓ) (M.pull i) 1) :
    0 ≤ topSelfIntersection (ZMod ℓ) (M.pull g) 1 := by
  have : IsProper g := .of_comp g t
  have hW : IsProper (strHom (ZMod ℓ) (X := W)) := isProper_strHom (ZMod ℓ) (g ≫ t)
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (strHom (ZMod ℓ) W)
  have := isNoetherian_of_locallyOfFiniteType_field (strHom (ZMod ℓ) W)
  by_cases hc : ∀ w, g w = g (genericPoint W)
  · exact (topSelf_pull_eq_zero_of_const (ZMod ℓ) hM g _ hc).ge
  push_neg at hc
  obtain ⟨x₀, hx₀⟩ := hc
  let φ : W ⟶ g.image := g.toImage
  have e : φ ≫ g.imageι = g := g.toImage_imageι
  have : IsProper (φ ≫ g.imageι) := by rw [e]; infer_instance
  have : IsProper φ := .of_comp φ g.imageι
  have hne : φ x₀ ≠ φ (genericPoint W) := fun h => hx₀ (by
    rw [← e, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h])
  have : LocallyQuasiFinite φ := ProperCurve.locallyQuasiFinite_of_ne hd φ hne
  have : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  have hdense : DenseRange φ := g.toImage.denseRange
  have hsurj : Function.Surjective φ := by
    rw [← Set.range_eq_univ, ← φ.isClosedMap.isClosed_range.closure_eq]
    exact hdense.closure_range
  have hgen : φ (genericPoint W) = genericPoint g.image := by
    have h₁ := (genericPoint_spec W).image φ.continuous
    rw [Set.image_univ, hdense.closure_range] at h₁
    exact h₁.eq (genericPoint_spec _)
  have hdZ : topologicalKrullDim g.image = 1 := by
    exact le_antisymm ((PosBaseChange.dim_le_of_isClosedMap φ.isClosedMap hsurj).trans hd.le)
      (one_le_dim (genericPoint_specializes (φ x₀)) fun h => hne (h.symm.trans hgen.symm))
  have hinj := appTop_injective_of_denseRange φ hdense
  have : CharP Γ(W, ⊤) ℓ := charP_of_injective_algebraMap (algebraMap (ZMod ℓ) Γ(W, ⊤)).injective ℓ
  have : CharP Γ(g.image, ⊤) ℓ := φ.appTop.hom.charP hinj ℓ
  letI : Algebra (ZMod ℓ) Γ(g.image, ⊤) := ZMod.algebra _ ℓ
  have hf (r : ZMod ℓ) : φ.appTop (algebraMap (ZMod ℓ) Γ(g.image, ⊤) r) = algebraMap (ZMod ℓ) Γ(W, ⊤) r :=
    RingHom.congr_fun (RingHom.ext_zmod (φ.appTop.hom.comp (algebraMap (ZMod ℓ) Γ(g.image, ⊤)))
      (algebraMap (ZMod ℓ) Γ(W, ⊤))) r
  have : IsProper (g.imageι ≫ t) := inferInstance
  have hZ : IsProper (strHom (ZMod ℓ) (X := g.image)) := isProper_strHom (ZMod ℓ) (g.imageι ≫ t)
  have hproj : IsProjOver (strHom (ZMod ℓ) (X := g.image)) := ProperCurve.isProjOver_of_isProper _ hdZ
  have hN := pull_isLB hM g.imageι
  have h₁ := GlobalTheory.ProjFin.interNumOn_eq_residueDegree_mul (ZMod ℓ) g.image W φ hproj hdZ hgen (M.pull g.imageι) hN
  have h₂ := interNumOn_eq_interNum_pull (k := ZMod ℓ) (L := ![M.pull g.imageι]) hf
    (fun i => by fin_cases i; exact hN)
  have h₃ : topSelfIntersection (ZMod ℓ) (M.pull g) 1 =
      interNum (ZMod ℓ) (structureModule W) fun i => (![M.pull g.imageι] i).pull φ := by
    refine interNum_congr_cls _ _ (fun _ => pull_isLB hM g) (fun i => by fin_cases i; exact pull_isLB hN φ) fun i => ?_
    fin_cases i
    refine (cls_pull hM g _).trans ?_
    refine Eq.trans ?_ (cls_pull hN φ _).symm
    exact (congrArg (fun f => pull f (cls M hM)) e.symm).trans (pull_comp φ g.imageι _)
  have h₄ : interNum (ZMod ℓ) (structureModule g.image) ![M.pull g.imageι] =
      topSelfIntersection (ZMod ℓ) (M.pull g.imageι) 1 := by
    refine congrArg _ (funext fun j => ?_)
    fin_cases j
    rfl
  rw [h₃, ← h₂, h₁, h₄]
  exact mul_nonneg (Int.natCast_nonneg _) (H _ g.imageι hdZ)

end Curve

theorem nefFib_pull : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k)
    (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p),
    ArInt.NefFib L → ArInt.NefFib (L.pull π hπ) := by
  intro k _ _ X Y p q hp hq π hπ L hL
  refine nefFib_of_primeField k Y q _ fun W i _ _ ℓ _ _ hd => ?_
  obtain ⟨N, j, _, hj⟩ := hp
  obtain ⟨N', j', _, hj'⟩ := hq
  have := isProper_str k N
  have := isProper_str k N'
  have : IsProper p := hj ▸ inferInstance
  have : IsProper q := hj' ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have hp' : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := .of_comp π p
  have hg : IsProper ((i ≫ π) ≫ p ≫ spMap (Int.castRingHom k)) := inferInstance
  have h := topSelf_pull_nonneg ℓ (p ≫ spMap (Int.castRingHom k)) hd L.isLB (i ≫ π)
    fun Z i' _ _ _ hd' => hL Z i' (ZMod ℓ) hd'
  have e : cls ((L.pull π hπ).B.pull i) (pull_isLB (L.pull π hπ).isLB i) =
      cls (L.B.pull (i ≫ π)) (pull_isLB L.isLB _) := by
    refine (cls_pull (L.pull π hπ).isLB i _).trans ?_
    refine Eq.trans ?_ (cls_pull L.isLB (i ≫ π) _).symm
    exact (pull_comp i π (cls L.B L.isLB)).symm
  rwa [topSelf_congr (ZMod ℓ) (pull_isLB (L.pull π hπ).isLB i) (pull_isLB L.isLB _)
    ((cls_eq_iff _ _).1 e)]

end GlobalTheory.ArInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelFunctionFieldCompatibility
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ModelFn

open SmallSec

theorem ratVal_eq {Z : Scheme.{0}} [IsIntegral Z] {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ}
    (y : CxPts q σ) (f : Z.functionField) : ratVal f y = valAt y.1 f := by
  by_cases hf : RegAt (under y) f
  · exact ratVal_eq_valAt y hf
  · rw [ratVal, valAt, dite_eq_right hf, dite_eq_right hf]

theorem valAt_comp {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X) [IsPreimmersion j]
    (hη : j (genericPoint Y) ⤳ genericPoint X) {K : Type} [Field K] (y : Sp K ⟶ Y) (f : X.functionField) :
    valAt (y ≫ j) f = valAt y (fnMap j hη f) := by
  by_cases hf : RegAt (j (below y)) f
  · exact (valAt_fnMap j hη y hf).symm
  · have h₁ : ¬ RegAt (below (y ≫ j)) f := hf
    rw [valAt, valAt, dite_eq_right h₁, dite_eq_right (mt (regAt_fnMap_iff j hη).1 hf)]

end GlobalTheory.TrueGeo.ModelFn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtWeilRepRealOneParamAdelicPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtWeilRepRealOneParamAdelicPoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.Mem.LiftGen

open GlobalTheory.RealWeil

theorem deriv_eq_of_norm {B H : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (Φ : B →L[ℂ] H) {u v : ℝ → B} {A G A' : B} (hu : HasDerivAt u A 0) (hv : HasDerivAt v G 0)
    (hn : ∀ t : ℝ, ‖Φ (v t - v 0 - (t : ℂ) • A')‖ = ‖Φ (u t - u 0 - (t : ℂ) • A)‖) : Φ G = Φ A' := by
  have h1 : HasDerivAt (fun t => Φ (u t)) (Φ A) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu
  have h2 : HasDerivAt (fun t => Φ (v t)) (Φ G) 0 :=
    (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hv
  refine h2.unique ?_
  rw [hasDerivAt_iff_isLittleO] at h1 ⊢
  rw [← Asymptotics.isLittleO_norm_left] at h1 ⊢
  refine h1.congr_left fun t => ?_
  have := hn t
  rw [map_sub, map_sub, map_sub, map_sub, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul] at this
  simp only [sub_zero]
  exact this.symm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem deriv_om (hψ : IsStdChar D ψ (-1)) {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : GlobalTheory.Ker.IsWeak ψ S T om) (p : GA D S × GA D T) {u v : ℝ → BB ψ S T} {A G : BB ψ S T}
    (hu : HasDerivAt u A 0) (hv : HasDerivAt v G 0) (hut : ∀ t, IsThetaFunO ψ S T (u t).1)
    (hA : IsThetaFunO ψ S T A.1) (e : ∀ t, ((v t).1 : WO S T → ℂ) = om p (u t).1) :
    (G.1 : WO S T → ℂ) = om p A.1 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO S T) (ratL T S) K hK hKc).1
  have : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  let A' : BB ψ S T := toB hψ _ (hW.om_pres p _ hA)
  have hA' : (A'.1 : WO S T → ℂ) = om p A.1 := coe_toB _ _ _
  have hk : ∀ a b : BB ψ S T, IsThetaFunO ψ S T b.1 → (a.1 : WO S T → ℂ) = om p b.1 →
      ‖toL2 _ _ (μ.restrict 𝓕) a‖ = ‖toL2 _ _ (μ.restrict 𝓕) b‖ := by
    intro a b hb hab
    rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2, hab]
    exact hW.om_unit μ 𝓕 hμ h𝓕 p _ hb
  have key : toL2 _ _ (μ.restrict 𝓕) G = toL2 _ _ (μ.restrict 𝓕) A' := by
    refine deriv_eq_of_norm _ hu hv fun t => ?_
    have e1 : ((u t - u 0 - (t : ℂ) • A).1 : WO S T → ℂ) =
        ((u t).1 : WO S T → ℂ) - ((u 0).1 : WO S T → ℂ) - (t : ℂ) • (A.1 : WO S T → ℂ) := rfl
    have e2 : ((v t - v 0 - (t : ℂ) • A').1 : WO S T → ℂ) = om p (u t - u 0 - (t : ℂ) • A).1 := by
      rw [e1, map_sub, map_sub, map_smul, ← e, ← e, ← hA']
      rfl
    have h3 : IsThetaFunO ψ S T (u t - u 0 - (t : ℂ) • A).1 := by
      rw [e1]
      exact (thetaSub ψ S T).sub_mem ((thetaSub ψ S T).sub_mem (hut t) (hut 0)) ((thetaSub ψ S T).smul_mem _ hA)
    exact hk _ _ h3 e2
  have h4 := lintegral_norm_sq_eq_toL2 (μ.restrict 𝓕) (G - A')
  rw [map_sub, key, sub_self, enorm_zero, zero_pow two_ne_zero,
    lintegral_eq_zero_iff ((G - A').1.continuous.measurable.enorm.pow_const 2)] at h4
  have h5 := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL T S) μ 𝓕 h𝓕 _ (G - A').1.continuous
    (BB_norm_periodic hψ _) (by filter_upwards [h4] with x hx; simpa using hx)
  rw [← hA']
  exact sub_eq_zero.1 h5

theorem hasDerivAt_om : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∀ p w, HasDerivAt (fun t => om (p * γ t) F.1 w) (om p (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F).1 w) 0 := by
  intro D θ σ h ψ hψ S T om hW hc γ hγ hadd hinf X hX
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.exists_weilRep_generator_realOneParameter_supNorm D θ σ h ψ hψ S T om hW hc γ hγ hadd hinf X hX
  obtain ⟨x, d, -, hxd⟩ := GlobalTheory.T.exists_ccr_operators_thetaFunctions D θ σ h ψ hψ S T
  refine ⟨lam, fun F hF p w => ?_⟩
  obtain ⟨u, hu, hud⟩ := hlam F hF
  have hA : IsThetaFunO ψ S T (nOp (rhoV hψ σ S T) (HM S T) X F + lam • F).1 := by
    have h1 := ((∑ k, ∑ l, X k l • (x k * d l)) ⟨F.1, hF⟩).2
    rw [hxd X ⟨F.1, hF⟩ F rfl] at h1
    exact (thetaSub ψ S T).add_mem h1 ((thetaSub ψ S T).smul_mem lam hF)
  have : IsTopologicalGroup (GA D S) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S).2.2.2.2.1
  have : IsTopologicalGroup (GA D T) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T).2.2.2.2.1
  have hn : ∀ V : HSp D, (GinfC V).Normal := fun V => MonoidHom.normal_ker _
  obtain ⟨lam', hlam'⟩ := GlobalTheory.T.exists_weilRep_generator_realOneParameter_supNorm D θ σ h ψ hψ S T om hW hc (fun t => p * γ t * p⁻¹)
    ((continuous_const.mul hγ).mul continuous_const) (fun s t => by rw [hadd]; group)
    (fun t => ⟨(hn S).conj_mem _ (hinf t).1 p.1, (hn T).conj_mem _ (hinf t).2 p.2⟩)
    (mM θ S T p * X * mM θ S T p⁻¹) (fun k l => by
      simp only [map_mul, Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun j _ => (HasDerivAt.fun_sum fun i _ => (hX i j).const_mul _).mul_const _)
  obtain ⟨v, hv, hvd⟩ := hlam' (toB hψ _ (hW.om_pres p _ hF)) (by rw [coe_toB]; exact hW.om_pres p _ hF)
  have e : ∀ t, ((v t).1 : WO S T → ℂ) = om (p * γ t) F.1 := fun t => by
    rw [hv, coe_toB, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
  have key := deriv_om hψ hW p hud hvd (fun t => by rw [hu]; exact hW.om_pres _ _ hF) hA
    (fun t => by rw [e, hu, map_mul, Module.End.mul_apply])
  rw [← key]
  have h3 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hvd
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  exact (congrFun (e t) w).symm

end GlobalTheory.Mem.LiftGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtWeilRepRealOneParamAdelicPointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_weilRep_realOneParam_adelicPoint : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∀ p w, HasDerivAt (fun t => om (p * γ t) F.1 w) (om p (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F).1 w) 0 := by
  first | exact @GlobalTheory.Mem.LiftGen.hasDerivAt_om | exact GlobalTheory.Mem.LiftGen.hasDerivAt_om | (intros; apply GlobalTheory.Mem.LiftGen.hasDerivAt_om <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximal
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHorizontalPrimeLeOfIsMaximal
namespace GlobalTheory

theorem exists_intCast_mem_of_isMaximal (R : Type*) [CommRing R] [Algebra.FiniteType ℤ R]
    (m : Ideal R) [m.IsMaximal] : ∃ p : ℤ, p ≠ 0 ∧ algebraMap ℤ R p ∈ m := by
  let := Ideal.Quotient.field m
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have : Module.Finite ℤ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ _
  by_contra h
  push Not at h
  have hinj : Function.Injective (algebraMap ℤ (R ⧸ m)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    apply h a ha0
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using ha
  have hF : IsField ℤ :=
    (Algebra.IsIntegral.isField_iff_isField hinj).mpr (Field.toIsField (R ⧸ m))
  exact Int.not_isField hF

theorem exists_horizontal_prime_le_of_isMaximal :
    ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] [CharZero R] (𝔪 : Ideal R),
      𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ q : Ideal R, q.IsPrime ∧ q ≤ 𝔪 ∧ g ∉ q ∧
        CharZero (R ⧸ q) ∧ Algebra.IsAlgebraic ℤ (R ⧸ q) := by
  intro R _ _ _ _ m hm g hg
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  obtain ⟨p₀, hp₀, hp₀m⟩ := exists_intCast_mem_of_isMaximal R m
  obtain ⟨p, hp⟩ := (IsPrincipalIdealRing.principal (m.comap (algebraMap ℤ R))).principal
  have hp' : m.comap (algebraMap ℤ R) = Ideal.span {p} := hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    have : p₀ ∈ m.comap (algebraMap ℤ R) := hp₀m
    rw [hp'] at this
    exact hp₀ (by simpa using this)
  have hpprime : Prime p := by
    rw [← Ideal.span_singleton_prime hp0, ← hp']
    infer_instance
  have hpm : algebraMap ℤ R p ∈ m := by
    have : p ∈ m.comap (algebraMap ℤ R) := hp' ▸ Ideal.mem_span_singleton_self p
    exact this
  set x : R := algebraMap ℤ R p * g with hx
  have hx0 : x ≠ 0 := mul_ne_zero (by simpa using hp0) hg
  obtain ⟨q, ⟨hqp, hqm, hxq⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {q : Ideal R | q.IsPrime ∧ q ≤ m ∧ x ∉ q}
    ⟨⊥, Ideal.isPrime_bot, bot_le, by simpa using hx0⟩
  change Ideal R at q
  have hpq : algebraMap ℤ R p ∉ q := fun h => hxq (q.mul_mem_right _ h)
  have hinj : Function.Injective (algebraMap ℤ (R ⧸ q)) := by
    have hq' : (q.comap (algebraMap ℤ R)).IsPrime := inferInstance
    have hbot : q.comap (algebraMap ℤ R) = ⊥ := by
      by_contra hne
      have hM : (q.comap (algebraMap ℤ R)).IsMaximal := IsPrime.to_maximal_ideal hne
      have := hM.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (Ideal.comap_mono (f := algebraMap ℤ R) hqm)
      apply hpq
      have h2 : p ∈ q.comap (algebraMap ℤ R) := this ▸ hpm
      exact h2
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ q.comap (algebraMap ℤ R) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      simpa using ha
    rwa [hbot, Ideal.mem_bot] at this
  have hsurj := Ideal.Quotient.mk_surjective (I := q)
  refine ⟨q, hqp, hqm, fun h => hxq (q.mul_mem_left _ h), charZero_of_injective_algebraMap hinj, ?_⟩
  have hm' : (m.map (Ideal.Quotient.mk q)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)
  have hcm : (m.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have h1 : (m.map (Ideal.Quotient.mk q)).height ≤ 1 := by
    refine height_le_one_of_forall_mem _ (f := Ideal.Quotient.mk q x)
      (by simpa [Ideal.Quotient.eq_zero_iff_mem] using hxq) ?_
    intro P hP hP0 hPm
    by_contra hxP
    refine hmax (P.comap (Ideal.Quotient.mk q)) ⟨inferInstance, ?_, hxP⟩ ?_
    · exact hcm ▸ Ideal.comap_mono hPm
    · refine lt_of_le_of_ne ?_ ?_
      · intro a ha
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
        exact P.zero_mem
      · intro e
        apply hP0
        rw [eq_bot_iff]
        intro b hb
        obtain ⟨a, rfl⟩ := hsurj b
        have : a ∈ q := e ▸ hb
        exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  have : Algebra.QuasiFiniteAt ℤ (m.map (Ideal.Quotient.mk q)) :=
    quasiFiniteAt_of_height_le_one _ h1 p (fun e => hp0 (hinj (by simpa using e)))
      (Ideal.mem_map_of_mem _ hpm)
  have : FaithfulSMul ℤ (R ⧸ q) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact isAlgebraic_of_quasiFiniteAt ℤ (R ⧸ q) (m.map (Ideal.Quotient.mk q))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximal
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open Pointwise

namespace GlobalTheory.TrueGeo.HorizRing

variable {F : Type} [Field F] [NumberField F]

theorem exists_embed (B : Type) [CommRing B] [IsDomain B] [Algebra (𝓞 F) B] [CharZero B] [Algebra.IsAlgebraic ℤ B] :
    ∃ ψ : B →ₐ[𝓞 F] AlgebraicClosure F, Function.Injective ψ := by
  have hinj : Function.Injective (algebraMap (𝓞 F) B) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    change Ideal.comap (algebraMap ℤ (𝓞 F)) (RingHom.ker (algebraMap (𝓞 F) B)) = ⊥
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  haveI : Algebra.IsAlgebraic (𝓞 F) B :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ) (RingHom.injective_int _)
  haveI : Module.IsTorsionFree (𝓞 F) B := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  haveI : Module.IsTorsionFree (𝓞 F) (AlgebraicClosure F) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq (𝓞 F) F (AlgebraicClosure F)]
    exact (algebraMap F _).injective.comp (IsFractionRing.injective (𝓞 F) F)
  let ψ : B →ₐ[𝓞 F] AlgebraicClosure F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ, ?_⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  refine Ideal.comap_ne_bot_of_algebraic_mem (R := ℤ) (I := RingHom.ker ψ.toRingHom) h0 hx
    (Algebra.IsAlgebraic.isAlgebraic x) ?_
  change Ideal.comap (algebraMap ℤ B) (RingHom.ker ψ.toRingHom) = ⊥
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem comap_ne_bot {R : Type} [CommRing R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (𝔪 : Ideal R)
    [h : 𝔪.IsMaximal] : 𝔪.comap (algebraMap (𝓞 F) R) ≠ ⊥ := by
  intro h0
  letI := Ideal.Quotient.field 𝔪
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  haveI : IsJacobsonRing (𝓞 F) := isJacobsonRing_of_isIntegral (R := ℤ)
  haveI : Module.Finite (𝓞 F) (R ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing _ _
  have hinj : Function.Injective (algebraMap (𝓞 F) (R ⧸ 𝔪)) := by
    rw [RingHom.injective_iff_ker_eq_bot, IsScalarTower.algebraMap_eq (𝓞 F) R (R ⧸ 𝔪), ← RingHom.comap_ker,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, h0]
  exact RingOfIntegers.not_isField F
    ((Algebra.IsIntegral.isField_iff_isField hinj).2 (Field.toIsField _))

theorem exists_valuationSubring {R K : Type} [CommRing R] [Field K] (ψ : R →+* K) (𝔪 : Ideal R) [h : 𝔪.IsMaximal]
    (hk : RingHom.ker ψ ≤ 𝔪) : ∃ A : ValuationSubring K, (∀ x, ψ x ∈ A) ∧ ∀ x, A.valuation (ψ x) < 1 ↔ x ∈ 𝔪 := by
  have hs := ψ.rangeRestrict_surjective
  have hc : (𝔪.map ψ.rangeRestrict).comap ψ.rangeRestrict = 𝔪 := by
    rw [Ideal.comap_map_of_surjective _ hs, sup_eq_left, ← RingHom.ker_eq_comap_bot, RingHom.ker_rangeRestrict]
    exact hk
  have hne : 𝔪.map ψ.rangeRestrict ≠ ⊤ := fun ht => h.ne_top (by rw [← hc, ht, Ideal.comap_top])
  obtain ⟨A, hA, hI⟩ := Ideal.image_subset_nonunits_valuationSubring (A := ψ.range) _ hne
  have hm : ∀ x, ψ x ∈ A := fun x => hA ⟨x, rfl⟩
  refine ⟨A, hm, ?_⟩
  let φ : R →+* A := ψ.codRestrict A hm
  have hle : 𝔪 ≤ (IsLocalRing.maximalIdeal A).comap φ := fun x hx => by
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
    exact hI ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩
  have he := h.eq_of_le (Ideal.comap_ne_top φ (IsLocalRing.maximalIdeal.isMaximal A).ne_top) hle
  intro x
  rw [he, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] [CharZero R] (𝔪 : Ideal R), 𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : R →+* e.O), (∀ a : 𝓞 F, ((φ (algebraMap (𝓞 F) R a) : e.O) : AlgebraicClosure F) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ (IsLocalRing.maximalIdeal e.O).comap φ = 𝔪 ∧ φ g ≠ 0 := by
  intro F _ _ R _ _ _ _ _ 𝔪 h𝔪 g hg
  haveI : Algebra.FiniteType ℤ R := Algebra.FiniteType.trans (S := 𝓞 F) inferInstance inferInstance
  obtain ⟨q, hq, hqm, hgq, hc, ha⟩ := GlobalTheory.exists_horizontal_prime_le_of_isMaximal R 𝔪 h𝔪 g hg
  obtain ⟨ψ₀, hψ₀⟩ := @exists_embed F _ _ (R ⧸ q) _ _ _ hc (by convert ha <;> first | rfl | exact Subsingleton.elim _ _)
  let ψ : R →ₐ[𝓞 F] AlgebraicClosure F := ψ₀.comp (Ideal.Quotient.mkₐ (𝓞 F) q)
  have hker : ∀ x, ψ x = 0 ↔ x ∈ q := fun x => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff ψ₀ hψ₀]
    rfl
  have hψ (a : 𝓞 F) : ψ (algebraMap (𝓞 F) R a) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a) := by
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply]
  obtain ⟨A, hA, hAm⟩ := exists_valuationSubring ψ.toRingHom 𝔪 (fun x hx => hqm ((hker x).1 hx))
  let v : HeightOneSpectrum (𝓞 F) := ⟨𝔪.comap (algebraMap (𝓞 F) R), inferInstance, comap_ne_bot 𝔪⟩
  obtain ⟨e⟩ := (ExtConj.main F).1 v
  have hov (x : 𝓞 F) : A.valuation (algebraMap F (AlgebraicClosure F) (x : F)) < 1 ↔ x ∈ v.asIdeal := by
    have := hAm (algebraMap (𝓞 F) R x)
    rwa [show ψ.toRingHom (algebraMap (𝓞 F) R x) = _ from hψ x] at this
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_smul_eq_of_over hov (ExtConj.lies_over e)
  have hm (x : R) : σ (ψ x) ∈ e.O := by
    rw [← hσ]
    exact ValuationSubring.smul_mem_pointwise_smul σ _ A (hA x)
  let φ : R →+* e.O := (σ.toRingEquiv.toRingHom.comp ψ.toRingHom).codRestrict e.O hm
  have hφ (x : R) : (φ x : AlgebraicClosure F) = σ (ψ x) := rfl
  refine ⟨v, e, φ, fun a => ?_, ?_, fun h0 => hgq ?_⟩
  · rw [hφ, hψ, σ.commutes]
  · ext x
    rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff, hφ, ← hAm]
    have := ReciprocityTheory.Gal.smul_valuation_lt_one_iff σ A (σ (ψ x))
    rw [hσ] at this
    rw [this]
    simp
  · have := hφ g
    rw [h0] at this
    exact (hker g).1 (by simpa using this.symm)

end GlobalTheory.TrueGeo.HorizRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPlaceOfNeZeroMaximalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ext_place_of_ne_zero_maximal : ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] [CharZero R] (𝔪 : Ideal R), 𝔪.IsMaximal → ∀ g : R, g ≠ 0 → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (φ : R →+* e.O), (∀ a : 𝓞 F, ((φ (algebraMap (𝓞 F) R a) : e.O) : AlgebraicClosure F) = algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F a)) ∧ (IsLocalRing.maximalIdeal e.O).comap φ = 𝔪 ∧ φ g ≠ 0 := by
  first | exact @GlobalTheory.TrueGeo.HorizRing.main | exact GlobalTheory.TrueGeo.HorizRing.main | (intros; apply GlobalTheory.TrueGeo.HorizRing.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapSingleAtEmb
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.OneRep

variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ}


omit [NumberField E] [NumberField.IsTotallyComplex E] in
theorem atEmb_zero (τ : E →+* ℂ) : atEmb τ 0 = 0 := by
  classical
  unfold atEmb; split_ifs <;> simp


omit [NumberField E] [NumberField.IsTotallyComplex E] in
theorem map_single_atEmb (τ : E →+* ℂ) (i k : Fin a) (z : ℂ) :
    (Matrix.single i k z).map (atEmb τ) = Matrix.single i k (atEmb τ z) := by
  ext p q
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp [atEmb_zero]

end GlobalTheory.OneRep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingWeilActionFiniteExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingWeilActionFiniteExtension
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocDec

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem exists_lifts_mul_mem (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (ι : Ω →ₐ[E] Kbar w) (θ : Dec (F := E) A ≃* GalLoc w) (hθ : Continuous θ)
    (hl : ∀ σ : Dec (F := E) A, Lifts ι (θ σ) (σ : G E Ω)) (g : GalLoc w) (H : Subgroup (GalLoc w))
    (hH : IsOpen (H : Set (GalLoc w))) :
    ∃ (σ : Weil h) (g' : GalLoc w), Lifts ι g' (σ : G E Ω) ∧ g⁻¹ * g' ∈ H := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  set d := θ.symm g with hd
  let S : Set (Dec (F := E) A) := (fun σ => g⁻¹ * θ σ) ⁻¹' (H : Set (GalLoc w))
  have hS : IsOpen S := hH.preimage (continuous_const.mul hθ)
  have hdS : d ∈ S := by
    show g⁻¹ * θ d ∈ H
    rw [hd, MulEquiv.apply_symm_apply, inv_mul_cancel]
    exact H.one_mem
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp hS
  have hdt : (d : G E Ω) ∈ t := by
    rw [← hts] at hdS
    exact hdS
  have hnhds : {x : G E Ω | (d : G E Ω) * x ∈ t} ∈ nhds (1 : G E Ω) := by
    apply (continuous_const_mul (d : G E Ω)).continuousAt.preimage_mem_nhds
    simpa using ht.mem_nhds hdt
  obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp hnhds
  let pb := Field.powerBasisOfFiniteOfSeparable E F
  obtain ⟨τ, hτW, hτ⟩ := GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup E Ω A w h (d : G E Ω) d.2 (pb.gen : Ω)
  have hfix : (d : G E Ω)⁻¹ * τ ∈ F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have e : (((d : G E Ω)⁻¹ * τ : G E Ω) : Ω →ₐ[E] Ω).comp F.val = F.val := pb.algHom_ext (by
      show ((d : G E Ω)⁻¹ * τ) (pb.gen : Ω) = pb.gen
      rw [AlgEquiv.mul_apply, hτ]
      show ((d : G E Ω)⁻¹ * (d : G E Ω)) (pb.gen : Ω) = pb.gen
      simp)
    exact congrArg (fun φ : F →ₐ[E] Ω => φ ⟨x, hx⟩) e
  have hτt : τ ∈ t := by
    have := hFs hfix
    simpa using this
  let σ : Dec (F := E) A := ⟨τ, Weil_le_Dec h hτW⟩
  have hσS : σ ∈ S := by
    rw [← hts]
    exact hτt
  exact ⟨⟨τ, hτW⟩, θ σ, hl σ, hσS⟩

end GlobalTheory.LocDec

namespace GlobalTheory.LocDec

theorem eq_adjoin_of_fixing_iff (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [Algebra E K] [IsScalarTower E K Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w)
    (hι : IsLocEmb A w ι) (L : IntermediateField (w.adicCompletion E) (Kbar w))
    [FiniteDimensional (w.adicCompletion E) L]
    (hfix : ∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ →
      ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) :
    L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  obtain ⟨θ, hθ, -, hl⟩ := decomposition_mulEquiv_galLoc E Ω A w h ι hι
  set Kw := w.adicCompletion E
  have : CharZero Kw := charZero_of_injective_algebraMap (algebraMap E Kw).injective
  have : IsGalois Kw (Kbar w) := IsAlgClosure.isGalois Kw (Kbar w)
  set M := IntermediateField.adjoin Kw (Set.range fun x : K => ι (algebraMap K Ω x)) with hM
  have hfx : ∀ (σ : G E Ω) (g' : GalLoc w), Lifts ι g' σ → ∀ x : K,
      (g' (ι (algebraMap K Ω x)) = ι (algebraMap K Ω x) ↔ σ (algebraMap K Ω x) = algebraMap K Ω x) :=
    fun σ g' hg x => by rw [hg]; exact ι.toRingHom.injective.eq_iff
  have : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  let pb := Field.powerBasisOfFiniteOfSeparable E K
  have hprim : ∀ σ : G E Ω, σ (algebraMap K Ω pb.gen) = algebraMap K Ω pb.gen →
      ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω x := by
    intro σ hσ x
    have e : ((σ : Ω →ₐ[E] Ω).comp (IsScalarTower.toAlgHom E K Ω)) = IsScalarTower.toAlgHom E K Ω :=
      pb.algHom_ext (by simpa using hσ)
    simpa using congrArg (fun φ : K →ₐ[E] Ω => φ x) e
  have hopen : ∀ z : Kbar w,
      IsOpen ((IntermediateField.adjoin Kw {z}).fixingSubgroup : Set (GalLoc w)) := fun z => by
    have : FiniteDimensional Kw (IntermediateField.adjoin Kw {z}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
    exact IntermediateField.fixingSubgroup_isOpen _
  have hmemz : ∀ (z : Kbar w) (k : GalLoc w), k ∈ (IntermediateField.adjoin Kw {z}).fixingSubgroup → k z = z :=
    fun z k hk => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk z (IntermediateField.mem_adjoin_simple_self _ _)
  have hLopen : IsOpen (L.fixingSubgroup : Set (GalLoc w)) := IntermediateField.fixingSubgroup_isOpen L
  have hLfix : ∀ k : GalLoc w, k ∈ L.fixingSubgroup → ∀ z ∈ L, k z = z :=
    fun k hk => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk
  apply le_antisymm
  · intro z hz
    rw [← InfiniteGalois.fixedField_fixingSubgroup M, IntermediateField.mem_fixedField_iff]
    intro g hg
    have hga : g (ι (algebraMap K Ω pb.gen)) = ι (algebraMap K Ω pb.gen) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _
        (IntermediateField.subset_adjoin _ _ ⟨pb.gen, rfl⟩)
    obtain ⟨σ, g', hlift, hk⟩ := exists_lifts_mul_mem A w h ι θ hθ hl g
      (L.fixingSubgroup ⊓ (IntermediateField.adjoin Kw {ι (algebraMap K Ω pb.gen)}).fixingSubgroup)
      (hLopen.inter (hopen _))
    have hg' : g' = g * (g⁻¹ * g') := by group
    have h1 : g' (ι (algebraMap K Ω pb.gen)) = ι (algebraMap K Ω pb.gen) := by
      rw [hg', AlgEquiv.mul_apply, hmemz _ _ (Subgroup.mem_inf.1 hk).2, hga]
    have h2 := hprim σ ((hfx σ g' hlift pb.gen).1 h1)
    have h3 := (hfix σ g' hlift).2 h2 z hz
    rw [hg', AlgEquiv.mul_apply, hLfix _ (Subgroup.mem_inf.1 hk).1 z hz] at h3
    exact h3
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    rw [← InfiniteGalois.fixedField_fixingSubgroup L]
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro g hg
    obtain ⟨σ, g', hlift, hk⟩ := exists_lifts_mul_mem A w h ι θ hθ hl g
      (L.fixingSubgroup ⊓ (IntermediateField.adjoin Kw {ι (algebraMap K Ω x)}).fixingSubgroup)
      (hLopen.inter (hopen _))
    have hg' : g' = g * (g⁻¹ * g') := by group
    have h1 : ∀ z ∈ L, g' z = z := fun z hz => by
      rw [hg', AlgEquiv.mul_apply, hLfix _ (Subgroup.mem_inf.1 hk).1 z hz, hLfix g hg z hz]
    have h2 := (hfx σ g' hlift x).2 ((hfix σ g' hlift).1 h1 x)
    rw [hg', AlgEquiv.mul_apply, hmemz _ _ (Subgroup.mem_inf.1 hk).2] at h2
    exact h2

theorem eq_adjoin_of_fixing_iff_weil : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), FiniteDimensional (w.adicCompletion E) L → (∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) → L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  intro E K Ω _ _ _ _ _ _ _ _ _ _ _ A w h ι hι L _ hfix
  exact eq_adjoin_of_fixing_iff E K Ω A w h ι hι L hfix

end GlobalTheory.LocDec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingWeilActionFiniteExtensionStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embedding_weil_action_finite_extension : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), FiniteDimensional (w.adicCompletion E) L → (∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) → L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  first | exact @GlobalTheory.LocDec.eq_adjoin_of_fixing_iff_weil | exact GlobalTheory.LocDec.eq_adjoin_of_fixing_iff_weil | (intros; apply GlobalTheory.LocDec.eq_adjoin_of_fixing_iff_weil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBijectiveFieldPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBijectiveFieldPoints
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

namespace GlobalTheory.FlagBundle

theorem CoBear₂ : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ g : Y₁.X ⟶ Y₂.X, g ≫ f₂ = f₁ → (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g)) → ∀ (K : Type) [Field K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ g) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ g hg hco K _
  have hcomp : ∀ p : Sp K ⟶ Y₁.X, p ≫ f₁ = (p ≫ g) ≫ f₂ := by
    intro p; rw [Category.assoc, hg]
  constructor
  · intro p p' hpp'
    simp only at hpp'
    have h1 := hco K p
    have h2 := hco K p'
    rw [← hpp'] at h2
    exact GlobalTheory.T.eq_of_bear_common_fullFlag F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K p p' (p ≫ g) (hcomp p)
      (by rw [hcomp p', hpp']) h1 h2
  · intro w
    obtain ⟨A, hA, h, hh, hw⟩ := GlobalTheory.T.exists_pointCarriesFrameFlags_own_frame F ι m X Y₂ Eb S₂ φ₂ f₂ hR₂ K w
    obtain ⟨p, ⟨hpx, hpA⟩, -⟩ := hR₁.2.2 K (w ≫ f₂) A hA h hh
    obtain ⟨B, hB, h', -, hpB, hqB⟩ := hco K p
    have hA' : A ∈ Eb.S ((p ≫ f₁) (IsLocalRing.closedPoint K)) := by rw [hpx]; exact hA
    have hqA : Bears S₂ φ₂ A h (p ≫ g) :=
      GlobalTheory.T.pointCarriesFrameFlags_transfer_between_flag_bundles F ι m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ hR₁ hR₂ K p (p ≫ g) (hcomp p) A hA' B hB h h'
        hpA hpB hqB
    obtain ⟨q, -, hq⟩ := hR₂.2.2 K (w ≫ f₂) A hA h hh
    refine ⟨p, ?_⟩
    simp only
    rw [hq (p ≫ g) ⟨by rw [← hcomp p, hpx], hqA⟩, hq w ⟨rfl, hw⟩]

end GlobalTheory.FlagBundle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleMorphismBijectiveFieldPointsStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagBundleMorphism_bijective_fieldPoints : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ g : Y₁.X ⟶ Y₂.X, g ≫ f₂ = f₁ → (∀ (K : Type) [Field K] (p : Sp K ⟶ Y₁.X), CoBear Eb S₁ φ₁ S₂ φ₂ (p ≫ f₁) p (p ≫ g)) → ∀ (K : Type) [Field K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ g) := by
  first | exact @GlobalTheory.FlagBundle.CoBear₂ | exact GlobalTheory.FlagBundle.CoBear₂ | (intros; apply GlobalTheory.FlagBundle.CoBear₂ <;> assumption)
end
end
