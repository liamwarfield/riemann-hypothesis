module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberZeroSmallImage

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def SquareTriple (W : G.Weil) (t : T) (i j : ℕ) : Prop :=
  ∀ M : Vol G, M.Is t → ∃ (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : _) (om' : _),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' ∧
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁

theorem SquareTriple.of_forall {W : G.Weil} {t : T} {i j : ℕ} (h : SquareTriple W t i j) {M : Vol G} (hM : M.Is t) :
    ∃ (e : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : _) (om' : _),
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.IsTripleOf W M t i j e Bs Γ X ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' ∧
      ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ Bs.v₁ := h M hM

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev UD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Type := UG (cA σ) (dbl (incM F W.J))

def matD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := g.1.1

def latD {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (Fin d ⊕ Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  {z | z ∘ Sum.inl ∈ GlobalTheory.InertSph.latAt W v ∧ z ∘ Sum.inr ∈ GlobalTheory.InertSph.latAt W v}

def KD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {g | At (evFin F v) (matD g - 1) ∧ ∀ z ∈ latD W v, matD g *ᵥ z ∈ latD W v ∧ matD g⁻¹ *ᵥ z ∈ latD W v}

def PDiag (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Set (UD σ W) :=
  {p | ∃ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))}

def antiCols (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := Matrix.fromRows 1 (-1)

def PAnti (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Set (UD σ W) :=
  {p | ∃ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD p * antiCols d = antiCols d * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))}

end GlobalTheory.DblVac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertDbl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev UD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : Type := UG (cA σ) (dbl (incM F W.J))

def matD {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (g : UD σ W) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  g.1.1

def latAtD {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (Fin d ⊕ Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  {z | (fun i => z (Sum.inl i)) ∈ GlobalTheory.InertSph.latAt W v ∧ (fun i => z (Sum.inr i)) ∈ GlobalTheory.InertSph.latAt W v}

def KAtD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {g | At (evFin F v) (matD g - 1) ∧
    ∀ z ∈ latAtD W v, matD g *ᵥ z ∈ latAtD W v ∧ matD g⁻¹ *ᵥ z ∈ latAtD W v}

def antiCols (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := Matrix.fromRows 1 (-1)

def ParD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {p | p ∈ KAtD σ W v ∧ ∃ t : GL (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD p * diagCols (Fin d) = diagCols (Fin d) * (t : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))}

def NabD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) : Set (UD σ W) :=
  {n | n ∈ KAtD σ W v ∧ matD n * antiCols d = antiCols d ∧
    ∃ b : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), matD n * diagCols (Fin d) = diagCols (Fin d) + antiCols d * b}

theorem fromBlocks_mem {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} (k : UA σ W.J) :
    ((Matrix.fromBlocks (mat k) 0 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))ᵀ * dbl (incM F W.J) *
      (Matrix.fromBlocks (mat k) 0 0 1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).map (cA σ) = dbl (incM F W.J) := by
  have hk : (mat k)ᵀ * incM F W.J * (mat k).map (cA σ) = incM F W.J := k.2
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, dbl, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hk, Matrix.map_one _ (map_zero (cA σ)) (map_one (cA σ))]

def inlD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) : UA σ W.J →* UD σ W where
  toFun k := ⟨⟨Matrix.fromBlocks (mat k) 0 0 1, Matrix.fromBlocks (mat k⁻¹) 0 0 1,
      by rw [Matrix.fromBlocks_multiply]; simp [mat, ← Matrix.GeneralLinearGroup.coe_mul, Matrix.fromBlocks_one],
      by rw [Matrix.fromBlocks_multiply]; simp [mat, ← Matrix.GeneralLinearGroup.coe_mul, Matrix.fromBlocks_one]⟩,
    fromBlocks_mem k⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    show Matrix.fromBlocks (mat (1 : UA σ W.J)) 0 0 1 = 1
    simp [mat, Matrix.fromBlocks_one]
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    show Matrix.fromBlocks (mat (a * b)) 0 0 1 = Matrix.fromBlocks (mat a) 0 0 1 * Matrix.fromBlocks (mat b) 0 0 1
    rw [Matrix.fromBlocks_multiply]; simp [mat]

theorem matD_inlD (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (k : UA σ W.J) :
    matD (inlD σ W k) = Matrix.fromBlocks (mat k) 0 0 1 := rfl

def dblFun {κ : Type} (Ψ : (κ → AF F) → ℂ) : (κ ⊕ κ → AF F) → ℂ := boxFun Ψ fun x => star (Ψ x)

end GlobalTheory.InertDbl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore.VanishNumberField

open GlobalTheory.AbLaw

theorem subsingleton_of_tensor {k E V : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup V] [Module k V]
    (h : Subsingleton (TensorProduct k E V)) : Subsingleton V := by
  by_contra hV
  rw [not_subsingleton_iff_nontrivial] at hV
  exact not_nontrivial_iff_subsingleton.2 h (Module.FaithfullyFlat.lTensor_nontrivial k E V)

theorem subsingleton_coh_of_pull {k E : Type} [Field k] [Field E] [Algebra k E] {X X' : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of k)} {f' : X' ⟶ Spec (CommRingCat.of E)} {π : X' ⟶ X} [QuasiCompact f] [IsSeparated f]
    (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom (algebraMap k E)))) {M : LB X} (hM : M.IsLB) (n : ℕ)
    (h : Subsingleton (coh (twist (structureModule X') (M.pull π)) n)) :
    Subsingleton (coh (twist (structureModule X) M) n) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom f'
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have cechIso {R : Type} [CommRing R] {Z : Scheme.{0}} (g : Z ⟶ Spec (CommRingCat.of R))
      (N : LB Z) {κ : Type} [LinearOrder κ] (U : κ → Z.Opens) :
      letI := algebraΓOfHom g
      cechLB g N U ≅ cech R (LB.toMod N) ⊤ U := by
    letI := algebraΓOfHom g
    exact (cechFunctor κ R).mapIso (Cube.isoMk (fun s => LinearEquiv.ofBijective
      (M := SecOnR g N (⨅ i ∈ s, U i)) (M₂ := sectionsOn (LB.toMod N) (⊤ ⊓ ⨅ i ∈ s, U i))
      (SecOnR.restrict g N (inf_le_right : ⊤ ⊓ (⨅ i ∈ s, U i) ≤ ⨅ i ∈ s, U i))
      (SecOnR.restrict_bijective g _ (le_inf le_top le_rfl)))
      fun {s t} ht x => (SecOnR.restrict_restrict g _ inf_le_right x).trans
        (SecOnR.restrict_restrict g inf_le_right (cechOpen_anti ⊤ U ht) x).symm)
  have cohEquiv {R : Type} [CommRing R] {Z : Scheme.{0}} (g : Z ⟶ Spec (CommRingCat.of R))
      {N : LB Z} (hN : N.IsLB) {κ : Type} [LinearOrder κ] [Finite κ] {U : κ → Z.Opens}
      (hu : ⨆ i, U i = ⊤) (hU : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (i : ℕ) :
      letI := algebraΓOfHom g
      Nonempty ((cechLB g N U).homology i ≃ₗ[R] coh (twist (structureModule Z) N) i) := by
    letI := algebraΓOfHom g
    haveI := LB.isQuasicoherent_toMod hN
    exact ⟨((HomologicalComplex.homologyFunctor _ _ i).mapIso (cechIso g N U)).toLinearEquiv ≪≫ₗ
      cechHEquivCoh R hu hU (LB.toMod N) i ≪≫ₗ (cohOn.mapIso R ⊤ i (Twist.unitTwistIso N)).symm⟩
  have homologyEquiv {R : Type} (O : Type) [CommRing R] [CommRing O] [Algebra R O] [Module.Flat R O]
      (C : CochainComplex (ModuleCat.{0} R) ℕ) (i : ℕ) :
      Nonempty ((((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj
        C).homology i ≃ₗ[O] TensorProduct R O (C.homology i)) := by
    have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.2 (inferInstance : Module.Flat R O))
    have : (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R O)).isLeftAdjoint
    obtain ⟨e⟩ := Semicont.nonempty_extendScalars_obj_equiv O (C.homology i)
    exact ⟨((C.sc i).mapHomologyIso
      (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O))).toLinearEquiv ≪≫ₗ e⟩
  obtain ⟨e₁⟩ := cohEquiv f hM hc hD' n
  obtain ⟨e₂⟩ := cohEquiv f' (LB.isLB_pull hM π) (U := fun i => π ⁻¹ᵁ D i)
    (by rw [← Scheme.Hom.preimage_iSup, hc]; rfl) (fun s hs => isAffineOpen_biInf_preimage H (hD' s hs)) n
  obtain ⟨e₃⟩ := homologyEquiv E (cechLB f M D) n
  have bcIso (g : k →+* E)
      (H' : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) :
      ((ModuleCat.extendScalars g).mapHomologicalComplex _).obj (cechLB f M D) ≅
        cechLB f' (M.pull π) (fun i => π ⁻¹ᵁ D i) := by
    letI := g.toAlgebra
    let φ : (secCube f M D ⋙ ModuleCat.extendScalars g) ⟶
        secCube f' (M.pull π) (fun i => π ⁻¹ᵁ D i) :=
      Cube.homMk (Fin m) E (fun s => SecOnR.baseChangeHom M H'.w _ _ (preimage_biInf D π s).ge)
        fun {s t} ht x => SecOnR.baseChangeHom_restrict H'.w (iInf_le_iInf_of_subset D ht)
          (iInf_le_iInf_of_subset (fun i => π ⁻¹ᵁ D i) ht) (preimage_biInf D π s).ge
          (preimage_biInf D π t).ge x
    exact @asIso _ _ _ _ (cechComparison (ModuleCat.extendScalars g) (secCube f M D))
      (isIso_cechComparison _ _) ≪≫
      @asIso _ _ _ _ (cechComplexMap φ)
        (isIso_cechComplexMap _ fun s hs => SecOnR.baseChangeHom_bijective hM H' (hD' s hs) (preimage_biInf D π s).symm)
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso (bcIso (algebraMap k E) H)).toLinearEquiv
  have h₁ : Subsingleton (TensorProduct k E ((cechLB f M D).homology n)) :=
    (e₃.symm.toEquiv.trans (e₄.toEquiv.trans e₂.toEquiv)).subsingleton_congr.2 h
  exact e₁.symm.toEquiv.subsingleton_congr.2 (subsingleton_of_tensor h₁)

theorem topologicalKrullDim_eq_of_smooth {k : Type} [Field k] {Y : Scheme.{0}} [Nonempty Y] (p : Y ⟶ Sp k) (D : ℕ)
    (h : SmoothOfRelativeDimension D p) : topologicalKrullDim Y = D := by
  have key : topologicalKrullDim (Set.univ : Set Y) = D := by
    refine topologicalKrullDim_eq_of_forall_exists_isOpen Set.univ_nonempty fun x _ => ?_
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
      (TopologicalSpace.Opens.mem_top x)
    replace hU : IsAffineOpen (X := Y) U := hU
    refine ⟨U, U.isOpen, hx, ?_⟩
    rw [Set.inter_univ, topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, U))).trans
      (SmoothDim.ringKrullDim_affineOpen k _ p _ h U hU ⟨x, hx⟩)
  rw [← key]
  exact (topologicalKrullDim_eq_of_isEmbedding (e := (id : Y → Y)) Topology.IsEmbedding.id Set.range_id).symm

theorem vanishFrom_adj : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA →
    VanishFrom G.L (GlobalTheory.LB.toMod (tens G.K.bundle G.LA)) 0 := by
  intro Q K _ _ G hnef hbig j hj q hq
  lift j to ℕ using hj
  let Ω := AlgebraicClosure K
  let S := G.toLinSys
  have hV : S.IsVariety := G.geom.alg.variety
  have hV' := hV.baseChange Ω
  have hH := S.isPullback_baseChange Ω
  haveI : IsIntegral (S.baseChange Ω).Y := hV'.isIntegral
  haveI : SmoothOfRelativeDimension G.D (S.baseChange Ω).str := hV'.smooth
  obtain ⟨hprop, A₀, hA₀⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hV.proj
  haveI := hprop
  have hstr : strHom K G.Y = G.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom K (X := G.Y)) := hstr ▸ hV.proj
  haveI : IsProper (strHom K (X := G.Y)) := hstr ▸ hprop

  have hLnef : IsNef K G.L := IsGenerated.isNef_of_isProjOver (L := G.L) ⟨G.N, G.b, G.geom.alg.bpf⟩ hV.proj
  have hLj : IsNef K (lbPow G.L j) := hLnef.pow hA₀ j
  have hNnef : IsNef K (tens G.LA (lbPow G.L j)) := hnef.tens_of_isProjOver hLj hV.proj
  have hNbig : IsBig K (tens G.LA (lbPow G.L j)) := hbig.tens_nef Q.nef hproj hnef hLj

  haveI : IsIntegralHom (spMap (algebraMap K Ω)) :=
    IsIntegralHom.SpecMap_iff.2 fun x => Algebra.IsIntegral.isIntegral x
  haveI : IsIntegralHom (S.bcFst Ω) := MorphismProperty.of_isPullback (P := @IsIntegralHom) hH.flip ‹_›
  let π := S.bcFst Ω

  have hN'nef : IsNef Ω ((tens G.LA (lbPow G.L j)).pull π) :=
    PosBaseChange.isNef_pull hNnef hA₀ (hA₀.pull_of_isAffineHom π) π π.isClosedMap
  have hN'big : IsBig Ω ((tens G.LA (lbPow G.L j)).pull π) := by
    obtain ⟨D₀, hD₀, c, hc, hm⟩ := hNbig.3
    have hD : topologicalKrullDim G.Y = G.D := topologicalKrullDim_eq_of_smooth G.str G.D hV.smooth
    obtain rfl : D₀ = G.D := by exact_mod_cast hD₀.symm.trans hD
    have hL := LB.isLB_pull hNbig.1 π
    refine (isBig_iff (f := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj
      (topologicalKrullDim_eq_of_smooth _ G.D hV'.smooth)).2 ⟨hL, c, hc, hm.mono fun m hm => hm.trans_eq (congrArg _ ?_)⟩
    rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL m) (LB.isLB_pull (isLB_lbPow hNbig.1 m) π)
      (by rw [cls_lbPow hL, cls_pull hNbig.1, cls_pull (isLB_lbPow hNbig.1 m), cls_lbPow hNbig.1, map_nsmul])]
    exact (FieldChangeInter.hdim_pull hH (isLB_lbPow hNbig.1 m) 0).symm

  have hM' := LB.isLB_pull (G.isLB_adj j) π
  have hKV : Subsingleton (coh (twist (structureModule (S.baseChange Ω).Y) ((G.adj j).pull π)) q) :=
    Q.kv.twist (k := Ω) (p := (S.baseChange Ω).str) (fun _ => rfl) hV'.proj (G.K.baseChange hH) hN'nef hN'big hM'
      (by
        rw [cls_pull (G.isLB_adj j) π]
        erw [cls_pull G.K.isLB π, cls_pull hNnef.isLB π]
        rw [← map_add (f := _)]
        congr 1
        erw [cls_tens (isLB_tens G.K.isLB G.isLBA) (Twist.isLB_lbZPow G.isLB j), cls_tens G.K.isLB G.isLBA,
          cls_tens G.isLBA (isLB_lbPow G.isLB j)]
        exact add_assoc _ _ _) hq

  have hY : Subsingleton (coh (twist (structureModule G.Y) (G.adj j)) q) :=
    subsingleton_coh_of_pull (f := G.str) (f' := (S.baseChange Ω).str) hH (G.isLB_adj j) q hKV
  have hB : (tens G.K.bundle G.LA).IsLB := isLB_tens G.K.isLB G.isLBA
  obtain ⟨i⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule G.Y) hB (Twist.isLB_lbZPow G.isLB j)
    (G.isLB_adj j) rfl
  exact (cohOn.mapIso Γ(G.Y, ⊤) ⊤ q
    ((twistFunctor (lbZPow G.L j)).mapIso (Twist.unitTwistIso (tens G.K.bundle G.LA)).symm ≪≫ i)).toEquiv.subsingleton_congr.2 hY

end GlobalTheory.HSCore.VanishNumberField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwistStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kawamataViehweg_vanishing_numberField_twist : Quoted → ∀ (K : Type) [Field K] [NumberField K] (G : Geo K), IsNef K G.LA → IsBig K G.LA → VanishFrom G.L (GlobalTheory.LB.toMod (tens G.K.bundle G.LA)) 0 := by
  first | exact @GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj | exact GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj | (intros; apply GlobalTheory.HSCore.VanishNumberField.vanishFrom_adj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilVacChar

variable {D : D7}

theorem hecke_mul_inv {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') :
    IsHeckeChar D (χ * χ'⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · change Continuous fun a => χ a * (χ' a)⁻¹
    exact h.1.mul h'.1.inv
  · change χ _ * (χ' _)⁻¹ = 1
    rw [h.2 x, h'.2 x, inv_one, mul_one]

theorem resEta_mul_inv {χ χ' : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (h' : ResEta D χ' n) :
    ResEta D (χ * χ'⁻¹) 0 := by
  refine ⟨h.1, fun η hη a => ?_⟩
  change χ _ * (χ' _)⁻¹ = _
  rw [h.2 η hη a, h'.2 η hη a, mul_inv_cancel, pow_zero]

theorem mul_mul_inv_cancel (χ χ' : (AE D)ˣ →* Circle) : χ' * (χ * χ'⁻¹) = χ := by
  refine MonoidHom.ext fun a => ?_
  change χ' a * (χ a * (χ' a)⁻¹) = χ a
  rw [mul_comm (χ a), mul_inv_cancel_left]

theorem vacuum_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))) (η : (AE D)ˣ →* Circle), IsEtaTilde D η → IsWeilDatumO ψ S T χS χT om → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt S g) = compAt θ τ (Formalism.L2.Theta.mt S g) * sS τ) → (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) → ∀ x y, IsDetRoot S g x → IsDetRoot T h y → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → om (g, h) f = (((((χT * (η ^ T.rank)⁻¹) x)⁻¹ * (χS * (η ^ S.rank)⁻¹) y : Circle) : ℂ) * ∏ τ, detPlus (sS τ) (sT τ) (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h))) • f := by
  intro D ψ hψ S T θ hθ χS χT om η hη hom sS sT hS hT g hg h hh cS cT x y hx hy f hf hv
  obtain ⟨om₀, h₀, -, hvac⟩ := GlobalTheory.T.exists_weilDatum_powers_unramifiedEtaTilde D ψ hψ S T θ hθ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) η hη
  obtain ⟨om', h', htw⟩ := GlobalTheory.T.exists_weilDatum_twist_heckeCharacters D ψ hψ S T _ _ (χS * (η ^ S.rank)⁻¹) (χT * (η ^ T.rank)⁻¹) om₀ h₀
    (hecke_mul_inv hom.hecS h₀.hecS) (hecke_mul_inv hom.hecT h₀.hecT)
    (resEta_mul_inv hom.resS h₀.resS) (resEta_mul_inv hom.resT h₀.resT)
  rw [mul_mul_inv_cancel, mul_mul_inv_cancel] at h'
  rw [GlobalTheory.T.weilDatum_unique_on_thetaFunctions D ψ hψ S T χS χT om om' hom h' (g, h) f hf, htw g h x y hx hy, LinearMap.smul_apply,
    hvac sS sT hS hT g hg h hh cS cT f hf hv, smul_smul]

end GlobalTheory.WeilVacChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))) (η : (AE D)ˣ →* Circle), IsEtaTilde D η → IsWeilDatumO ψ S T χS χT om → ∀ (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt S g) = compAt θ τ (Formalism.L2.Theta.mt S g) * sS τ) → (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) → ∀ x y, IsDetRoot S g x → IsDetRoot T h y → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → om (g, h) f = (((((χT * (η ^ T.rank)⁻¹) x)⁻¹ * (χS * (η ^ S.rank)⁻¹) y : Circle) : ℂ) * ∏ τ, detPlus (sS τ) (sT τ) (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h))) • f := by
  first | exact @GlobalTheory.WeilVacChar.vacuum_character | exact GlobalTheory.WeilVacChar.vacuum_character | (intros; apply GlobalTheory.WeilVacChar.vacuum_character <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharacters
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilExist

variable {D : D7}

theorem isHeckeChar_div_pow {χ η : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : IsHeckeChar D η) (n : ℕ) :
    IsHeckeChar D ((η ^ n)⁻¹ * χ) := by
  refine ⟨?_, fun x => ?_⟩
  · have : (((η ^ n)⁻¹ * χ : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => (η x ^ n)⁻¹ * χ x := by
      funext x; simp
    rw [this]
    exact ((hη.1.pow n).inv).mul hχ.1
  · have h1 := hχ.2 x
    have h2 := hη.2 x
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, h1, h2, one_pow, inv_one, mul_one]

theorem resEta_div_pow {χ η : (AE D)ˣ →* Circle} {n : ℕ} (hχ : ResEta D χ n) (hη : ResEta D η 1) :
    ResEta D ((η ^ n)⁻¹ * χ) 0 := by
  refine ⟨hχ.1, fun e he a => ?_⟩
  have h1 := hχ.2 e he a
  have h2 := hη.2 e he a
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, h1, h2, pow_one, pow_zero, inv_mul_cancel]

theorem exists_isWeilDatumO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), (∃ η, IsEtaTilde D η) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank → ∃ om, IsWeilDatumO ψ S T χS χT om := by
  intro D ψ hψ S T χS χT ⟨η, hη⟩ hS hT rS rT
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨om, hom, -⟩ := GlobalTheory.T.exists_weilDatum_powers_unramifiedEtaTilde D ψ hψ S T θ hθ _ _ (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) η hη
  obtain ⟨om', hom', -⟩ := GlobalTheory.T.exists_weilDatum_twist_heckeCharacters D ψ hψ S T _ _ ((η ^ S.rank)⁻¹ * χS) ((η ^ T.rank)⁻¹ * χT) om hom
    (isHeckeChar_div_pow hS hη.1 _) (isHeckeChar_div_pow hT hη.1 _)
    (resEta_div_pow rS hη.2.2.1) (resEta_div_pow rT hη.2.2.1)
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at hom'
  exact ⟨om', hom'⟩

end GlobalTheory.WeilExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumOfSplittingCharactersStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_of_splittingCharacters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), (∃ η, IsEtaTilde D η) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank → ∃ om, IsWeilDatumO ψ S T χS χT om := by
  first | exact @GlobalTheory.WeilExist.exists_isWeilDatumO | exact GlobalTheory.WeilExist.exists_isWeilDatumO | (intros; apply GlobalTheory.WeilExist.exists_isWeilDatumO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCO
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {D : D7}

def IsCO (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Prop :=
  IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) ∧
    IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V))

end GlobalTheory.FunObj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.LB (toMod)
open Limits (pullback)

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}


variable (p) in
def ratFibre : Scheme.{0} := pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))

namespace ratFibre

variable (p)

def fst : ratFibre p ⟶ X := pullback.fst _ _

def snd : ratFibre p ⟶ Sp ℚ := pullback.snd _ _

instance algebra : Algebra ℚ Γ(ratFibre p, ⊤) := algebraΓOfHom (snd p)

theorem isPullback : IsPullback (fst p) (snd p) (p ≫ spMap (Int.castRingHom k))
    (spMap (Int.castRingHom ℚ)) := IsPullback.of_hasPullback _ _

theorem strHom_eq : strHom ℚ (ratFibre p) = snd p := GlobalTheory.strHom_eq fun _ => rfl

end ratFibre


variable (p) in
def ratDeg (L : LB X) : ℤ := degOfRank ℚ (toMod (L.pull (ratFibre.fst p))) 1

abbrev CxPts.pt (y : CxPts p σ) : X := y.1 (IsLocalRing.closedPoint ℂ)

def germOrd {W : X.Opens} (f : Γ(X, W)) {x : X} (hx : x ∈ W) : ℕ :=
  (Ring.ord (X.presheaf.stalk x) (X.presheaf.germ W x hx f)).toNat

theorem exists_mem_chart {L : LB X} (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i :=
  Opens.mem_iSup.1 (hL.cover.ge (Opens.mem_top x))

def secOrd {L : LB X} (hL : L.IsLB) (s : L.Sec) (x : X) : ℕ :=
  germOrd (s.f (exists_mem_chart hL x).choose) (exists_mem_chart hL x).choose_spec

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppLESecEpsZeroEpsFn
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.Conormal

namespace GlobalTheory.LieVB

variable {O : Type} [CommRing O]

theorem surjective_sec_epsZero : Function.Surjective (sec (epsZero O)) := by
  intro t
  have hs : Function.Surjective (TrivSqZeroExt.fstHom O O O).toRingHom :=
    fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have ht : (t : PrimeSpectrum (DualNumber O)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom O O O).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro a ha
    have ha : a.fst = 0 := ha
    have h : a * a = 0 := by ext <;> simp [ha]
    have := (t : PrimeSpectrum (DualNumber O)).isPrime
    exact (this.mem_or_mem (h ▸ Ideal.zero_mem _)).elim id id
  exact ht

theorem appLE_sec_epsZero_epsFn {V : (Sp O).Opens} {T : (specO O (DualNumber O)).left.Opens}
    (h : V ≤ sec (epsZero O) ⁻¹ᵁ T) :
    (sec (epsZero O)).appLE T V h (resG _ le_top (epsFn O)) = 0 := by
  have e : (sec (epsZero O)).appLE ⊤ ⊤ (le_preimage_top _ _) (epsFn O) = 0 :=
    congr($(Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (TrivSqZeroExt.fstHom O O O).toRingHom)) DualNumber.eps).symm.trans
      (map_zero (Scheme.ΓSpecIso (.of O)).inv.hom)
  rw [GlobalTheory.DualPull.appLE_resG, ← GlobalTheory.DualPull.resG_appLE _ le_top (le_preimage_top _ _), e,
    map_zero]

variable {G : Over (Sp O)} [GrpObj G]

theorem sec_epsZero_comp (x : LieG G) : sec (epsZero O) ≫ x.1.left = unitSec G :=
  congrArg (·.left) (epsZero_comp x)

theorem preimage_le_of_lieG (x : LieG G) {U : (Sp O).Opens} {W : G.left.Opens}
    (h : U ≤ unitSec G ⁻¹ᵁ W) : (specO O (DualNumber O)).hom ⁻¹ᵁ U ≤ x.1.left ⁻¹ᵁ W := by
  intro t ht
  obtain ⟨s, rfl⟩ := surjective_sec_epsZero t
  have h₁ : s ∈ (sec (epsZero O) ≫ (specO O (DualNumber O)).hom) ⁻¹ᵁ U := ht
  rw [sec_hom] at h₁
  have h₂ := h h₁
  rw [← sec_epsZero_comp x] at h₂
  exact h₂

theorem appLE_lieG (x : LieG G) {U : (Sp O).Opens} (hU : IsAffineOpen U) {W : G.left.Opens}
    (h : U ≤ unitSec G ⁻¹ᵁ W) (f : Γ(G.left, W)) :
    x.1.left.appLE W _ (preimage_le_of_lieG x h) f =
      (specO O (DualNumber O)).hom.appLE U _ le_rfl ((unitSec G).appLE W U h f) +
        (specO O (DualNumber O)).hom.appLE U _ le_rfl
          (GlobalTheory.VB.dualApp (tangent x) le_top (dUnit G h f)) * resG _ le_top (epsFn O) := by
  obtain ⟨⟨a, b⟩, e⟩ := (GlobalTheory.T.dualNumberSpec_affineOpen_functions_bijective O U hU).2 (x.1.left.appLE W _ (preimage_le_of_lieG x h) f)
  have hV : U ≤ sec (epsZero O) ⁻¹ᵁ (specO O (DualNumber O)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero O))).2 le_rfl
  have hb := dualApp_tangent_dUnit x h f hV le_rfl (preimage_le_of_lieG x h) a b e.symm
  have ha : (unitSec G).appLE W U h f = a := by
    have e' := congrArg ((sec (epsZero O)).appLE _ U hV) e
    simp only [map_add (f := _), map_mul] at e'
    rw [appLE_sec_epsZero_epsFn, mul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl,
      GlobalTheory.LB.resG_self, appLE_appLE (sec_epsZero_comp x) _ _ h] at e'
    exact e'.symm
  rw [ha, hb]
  exact e.symm

theorem tangent_injective (O : Type) [CommRing O] (G : Over (Sp O)) [GrpObj G] :
    Function.Injective (tangent : LieG G → Γ(Lie G, ⊤)) := by
  intro x y hxy
  refine Subtype.ext (Over.OverMorphism.ext (Scheme.hom_ext_of_forall _ _ fun t => ?_))
  obtain ⟨U, W, hU, -, c⟩ := exists_isChart (sec_hom (MonObj.one (X := G))) (V := ⊤)
    (x := (specO O (DualNumber O)).hom t) trivial
  have hT : IsAffineOpen ((specO O (DualNumber O)).hom ⁻¹ᵁ U) := c.affine_base.preimage _
  have e : x.1.left.appLE W _ (preimage_le_of_lieG x c.le) =
      y.1.left.appLE W _ (preimage_le_of_lieG y c.le) := by
    ext f
    exact (appLE_lieG x c.affine_base c.le f).trans
      (hxy ▸ (appLE_lieG y c.affine_base c.le f).symm)
  refine ⟨(specO O (DualNumber O)).hom ⁻¹ᵁ U, hU, ?_⟩
  rw [← cancel_epi hT.isoSpec.inv, ← Category.assoc, ← Category.assoc, hT.isoSpec_inv_ι,
    ← c.affine.SpecMap_appLE_fromSpec _ hT (preimage_le_of_lieG x c.le),
    ← c.affine.SpecMap_appLE_fromSpec _ hT (preimage_le_of_lieG y c.le), e]

end GlobalTheory.LieVB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ChartGlue
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (cokernel)

namespace GlobalTheory

namespace Vert.Flag

variable {X Y : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl : Flag E N) (π : Y ⟶ X)

def pull : Flag ((Scheme.Modules.pullback π).obj E) N where
  F i := (Scheme.Modules.pullback π).obj (fl.F i)
  ι i := (Scheme.Modules.pullback π).map (fl.ι i)
  isSubbundle i := SubPull.isSubbundle_pullback X Y π _ _ _ i (fl.isVB i) (fl.isSubbundle i)
  isVB i := (fl.isVB i).pullback π
  step i := (Scheme.Modules.pullback π).map (fl.step i)
  step_ι i := by rw [← Functor.map_comp, fl.step_ι]
  isIso_last := inferInstance

end Vert.Flag

namespace VMetric

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
  {E : X.Modules} {r : ℕ} (fl : Vert.Flag E r) (π : Y ⟶ X) (i : Fin r)

variable {fl π i}

end VMetric

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmul
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

open GlobalTheory.LieVB GlobalTheory.Conormal

theorem kappa_cotMap_cst_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A)
    (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Γ(omega A, ⊤)) :
    kappa O M ((cotMap z h).app ⊤ (cst O c • w)) = c • kappa O M ((cotMap z h).app ⊤ w) := by
  rw [show (cotMap z h).app ⊤ (cst O c • w) = cst O c • (cotMap z h).app ⊤ w from
    (QCoh.appLinear (cotMap z h) ⊤).map_smul (cst O c) w]
  obtain ⟨b, hb⟩ := (isChart O M).d_surjective (sec_hom (zeroSec O M)) ((cotMap z h).app ⊤ w)
  rw [← hb]
  have key : cst O c • d (sec_hom (zeroSec O M)) (isChart O M).le b =
      d (sec_hom (zeroSec O M)) (isChart O M).le ((TM O M).hom.appLE ⊤ ⊤ le_top (cst O c) * b) := by
    rw [d_mul]
    erw [d_base (sec_hom (zeroSec O M)) (isChart O M).le le_top (cst O c)]
    rw [smul_zero, add_zero]
    erw [appLE_base (sec_hom (zeroSec O M)) _ _ le_rfl]
    rfl
  rw [key, kappa_d, kappa_d, map_mul, toTsze_base, TrivSqZeroExt.snd_mul]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem Phi_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
    [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A)
    (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Wmod A) :
    Phi z h (c • w) = c • Phi z h w :=
  kappa_cotMap_cst_smul O M A z h c w

end GlobalTheory.SqZeroPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open GlobalTheory.LieVB GlobalTheory.Conormal

namespace GlobalTheory.SqZeroPt

theorem zeroSec_sqZeroMap (O : Type) [CommRing O] (M N : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N]
    [IsCentralScalar O N] (l : M →ₗ[O] N) :
    zeroSec O N ≫ GlobalTheory.GrpTangent.sqZeroMap l = zeroSec O M := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp

theorem Phi_sqZeroMap_comp : ∀ (O : Type) [CommRing O] (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (A : Over (Sp O)) [GrpObj A] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w) := by
  intro O _ M N _ _ _ _ _ _ _ _ A _ l z h h' w
  have hl := zeroSec_sqZeroMap O M N l
  rw [Phi_apply, Phi_apply, ← cotMap_comp h hl rfl h']
  obtain ⟨b, hb⟩ := (isChart O M).d_surjective (sec_hom (zeroSec O M)) ((cotMap z h).app ⊤ w)
  have e : (ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap z h ≫ cotMap (GlobalTheory.GrpTangent.sqZeroMap l) hl) ⊤)) w = (ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap (GlobalTheory.GrpTangent.sqZeroMap l) hl) ⊤)) ((ConcreteCategory.hom (Scheme.Modules.Hom.app (cotMap z h) ⊤)) w) := rfl
  rw [e, ← hb, cotMap_d (GlobalTheory.GrpTangent.sqZeroMap l) hl _ (le_preimage_top _ ⊤) (le_preimage_top _ ⊤), kappa_d, kappa_d, appLE_top]
  change (toTsze O N ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)).appTop b)).snd = _
  rw [show toTsze O N ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)).appTop b) = TrivSqZeroExt.map l (toTsze O M b) from
    congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)) b)]
  simp

end GlobalTheory.SqZeroPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupSche
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupSche
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramesFGP

theorem finite_projective_top {O : Type} [CommRing O] (F : (Sp O).Modules)
    (h : ∀ x : Sp O, ∃ (U : (Sp O).Opens) (n : ℕ) (s : Fin n → Γ(F, U)),
      x ∈ U ∧ GlobalTheory.VB.IsFrame s) :
    Module.Finite Γ(Sp O, ⊤) Γ(F, ⊤) ∧ Module.Projective Γ(Sp O, ⊤) Γ(F, ⊤) := by
  haveI : F.IsQuasicoherent := GlobalTheory.OmegaGlobal.isQuasicoherent_of_frames h
  choose U n e hx he using h
  have hU := isAffineOpen_top (Sp O)
  let s : Set Γ(Sp O, ⊤) := {f | ∃ x, (Sp O).basicOpen f ≤ U x}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro y _
    obtain ⟨f, hf, hyf⟩ := hU.exists_basicOpen_le (V := U y) ⟨y, hx y⟩ (by simp)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, y, hf⟩, hyf⟩
  haveI (g : s) := hU.isLocalization_basicOpen g.1
  haveI (g : s) := GlobalTheory.QCoh.isLocalizedModule_resBasicOpen F hU g.1
  let b (g : s) : Module.Basis (Fin (n g.2.choose)) Γ(Sp O, (Sp O).basicOpen g.1)
      Γ(F, (Sp O).basicOpen g.1) := (he g.2.choose).basis g.2.choose_spec
  haveI (g : s) : Module.Free Γ(Sp O, (Sp O).basicOpen g.1) Γ(F, (Sp O).basicOpen g.1) :=
    .of_basis (b g)
  haveI (g : s) : Module.Finite Γ(Sp O, (Sp O).basicOpen g.1) Γ(F, (Sp O).basicOpen g.1) :=
    .of_basis (b g)
  haveI (g : s) : Module.Flat Γ(Sp O, ⊤) Γ(F, (Sp O).basicOpen g.1) := by
    haveI : Module.Flat Γ(Sp O, ⊤) Γ(Sp O, (Sp O).basicOpen g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans Γ(Sp O, ⊤) Γ(Sp O, (Sp O).basicOpen g.1) _
  haveI hfp : Module.FinitePresentation Γ(Sp O, ⊤) Γ(F, ⊤) :=
    Module.FinitePresentation.of_localizationSpan' s hs
      (Mₚ := fun g : s => Γ(F, (Sp O).basicOpen g.1))
      (Rₚ := fun g : s => Γ(Sp O, (Sp O).basicOpen g.1))
      (fun g => GlobalTheory.QCoh.resBasicOpen F g.1) fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat Γ(Sp O, ⊤) Γ(F, ⊤) :=
    Module.flat_of_isLocalized_span Γ(Sp O, ⊤) Γ(F, ⊤) s hs
      (fun g : s => Γ(F, (Sp O).basicOpen g.1)) (fun g => GlobalTheory.QCoh.resBasicOpen F g.1)
      fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.FramesFGP

theorem GlobalTheory.FramesFGP.finite_projective_wmod : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A],
    (∀ x : Sp O, ∃ (U : (Sp O).Opens) (n : ℕ) (s : Fin n → Γ(GlobalTheory.LieVB.omega A, U)),
      x ∈ U ∧ GlobalTheory.VB.IsFrame s) → Module.Finite O (Wmod A) ∧ Module.Projective O (Wmod A) := by
  intro O _ A _ h
  obtain ⟨h1, h2⟩ := GlobalTheory.FramesFGP.finite_projective_top (GlobalTheory.LieVB.omega A) h
  letI : Module Γ(Sp O, ⊤) (Wmod A) := inferInstanceAs (Module Γ(Sp O, ⊤) Γ(GlobalTheory.LieVB.omega A, ⊤))
  haveI : Module.Finite Γ(Sp O, ⊤) (Wmod A) := h1
  haveI : Module.Projective Γ(Sp O, ⊤) (Wmod A) := h2
  have hb : Function.Bijective (GlobalTheory.LieVB.cst O) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv
  let E : O ≃+* Γ(Sp O, ⊤) := RingEquiv.ofBijective (GlobalTheory.LieVB.cst O) hb
  letI : Algebra O Γ(Sp O, ⊤) := (GlobalTheory.LieVB.cst O).toAlgebra
  haveI : IsScalarTower O Γ(Sp O, ⊤) (Wmod A) := .of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite O Γ(Sp O, ⊤) :=
    Module.Finite.of_surjective (Algebra.linearMap O Γ(Sp O, ⊤)) hb.2
  refine ⟨Module.Finite.trans Γ(Sp O, ⊤) (Wmod A), ?_⟩
  haveI : RingHomInvPair (E.symm : Γ(Sp O, ⊤) →+* O) (E : O →+* Γ(Sp O, ⊤)) :=
    ⟨RingHom.ext E.apply_symm_apply, RingHom.ext E.symm_apply_apply⟩
  haveI : RingHomInvPair (E : O →+* Γ(Sp O, ⊤)) (E.symm : Γ(Sp O, ⊤) →+* O) := .symm _ _
  let e : Wmod A ≃ₛₗ[(E.symm : Γ(Sp O, ⊤) →+* O)] Wmod A :=
    { toFun := id
      invFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        change r • m = GlobalTheory.LieVB.cst O (E.symm r) • m
        congr 1
        exact (E.apply_symm_apply r).symm
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Projective.of_equiv e

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupScheStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_projective_cotangentGlobalSections_groupScheme : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A], (∀ x : Sp O, ∃ (U : (Sp O).Opens) (n : ℕ) (s : Fin n → Γ(GlobalTheory.LieVB.omega A, U)), x ∈ U ∧ GlobalTheory.VB.IsFrame s) → Module.Finite O (Wmod A) ∧ Module.Projective O (Wmod A) := by
  first | exact @GlobalTheory.FramesFGP.finite_projective_wmod | exact GlobalTheory.FramesFGP.finite_projective_wmod | (intros; apply GlobalTheory.FramesFGP.finite_projective_wmod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertLocalUniformizerImports
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertBridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def Chart (σ : E →ₐ[F] E) (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (v : Pl (F := F)) {L : Type} [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (JS : GL (Fin a') L)
    (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
    (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
    (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
    (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J) : Prop :=
  Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧
  JS ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) ∧ JT ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) ∧
  (∀ i j, σL ((JS : Matrix (Fin a') (Fin a') L) i j) = (JS : Matrix (Fin a') (Fin a') L) j i) ∧
  (∀ i j, σL ((JT : Matrix (Fin (a + a')) (Fin (a + a')) L) i j) = (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) j i) ∧
  (Valued.v δ = 1 ∧ σL δ = -δ) ∧
  (∀ z ∈ Formalism.UG.intL L, σL z = z → ψL z = 1) ∧
  (∃ z ∈ Formalism.UG.intL L, σL z = z ∧ ψL (ϖ⁻¹ * z) ≠ 1) ∧
  (∀ x, At (evFin F v) (κ x)) ∧
  (∀ γ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) γ → ∃ x, κ x = γ) ∧
  (∀ x, (∀ i j, x i j ∈ Formalism.UG.intL L) ↔ κ x ∈ latAtV G.V' G.W v) ∧
  (∀ x y, ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) =
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (κ x) (κ y))) ∧
  (∀ g h x, actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (ιS g, ιT h) (κ x) =
    κ (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
      (((g : GL (Fin a') L)⁻¹ : GL (Fin a') L) : Matrix (Fin a') (Fin a') L))) ∧
  (∀ g, ιS g ∈ UAt σ G.V' (evFin F v)) ∧ (∀ h, ιT h ∈ UAt σ G.W (evFin F v)) ∧
  (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L),
    (g : GL (Fin a') L) ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) → ιS g ∈ GlobalTheory.InertSph.KAt σ G.V' v) ∧
  (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L),
    (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ιT h ∈ GlobalTheory.InertSph.KAt σ G.W v)

end GlobalTheory.InertBridge

end
end
