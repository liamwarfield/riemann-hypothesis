module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleThetaEval
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairBigMemberTwistedTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalModificationKsIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalModificationKsIsoSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseScaleThetaConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortLatticeSpanningSets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBetaInvHeckeU

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
noncomputable section

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

variable {D : D7}

def GoodMod (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) : Prop :=
  𝔪 ≠ ⊥ ∧ 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ ∧ IsCoprime 𝔪 (Ideal.span {((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E)}) ∧
    ∀ v, v ∈ Sf ↔ ∃ w : HeightOneSpectrum (𝓞 D.host.E), 𝔪 ≤ w.asIdeal ∧ w.under (𝓞 D.host.F) = v

abbrev stdLat (V : HSp D) : Lat V := Formalism.MainNotions.StandardLatticesGL3.stdL D V.rank

def locNorm (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a a' : ℕ) : ℝ :=
  ∏ w ∈ (normalizedFactors 𝔪).toFinset,
    (((Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * a * a'))⁻¹ * glVol (Ideal.absNorm w : ℝ) a)

def locIdx (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (a a' : ℕ) : ℝ :=
  ∏ w ∈ (normalizedFactors 𝔪).toFinset, blockIdx (Ideal.absNorm w : ℝ) ((normalizedFactors 𝔪).count w) a a'

def vacNorm (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) (a d : ℕ) : ℝ :=
  Formalism.MainNotions.StandardLatticesGL3.nrm1Sq (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) (Formalism.MainNotions.GL3Theta.th0 (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) t0) ^ (Formalism.MainNotions.TaylorLogMetric.fF D * a * d)

def mass (D : D7) (N : ℕ) : ℂ := ∑ᶠ x : Cls D N (intG D N), ((gam D (intG D N) x.out : ℂ))⁻¹

def fockSum (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) : ℂ :=
  ∑ T : Tup D a d n, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T)

theorem goodMod_modT {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (hpq : Nat.Coprime D.host.pde (D.host.QS * D.host.q))
    (hpq' : Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) (G : GridData L sc) (t : T) : GoodMod D (modT G t) (sfB G t) := by
  refine ⟨GlobalTheory.FunObj.StdDatum.TwBig.modT_ne_bot G t, GlobalTheory.SqTop.modT_sup_conj hL G t,
    GlobalTheory.BotPairSmallTw.modT_isCoprime_two_q hL hpq hpq' G t, fun v => ?_⟩
  have key : ∀ w : HeightOneSpectrum (𝓞 D.host.E), modT G t ≤ w.asIdeal ↔ w ∈ locPl G t := by
    intro w
    have hp := w.isPrime
    have hc : ∀ v, SqNum.condExp G.pl v ≠ 0 := fun v => by unfold SqNum.condExp; split_ifs <;> omega
    unfold modT condE
    rw [hp.mul_le, hp.prod_le, hp.prod_le]
    constructor
    · rintro (⟨v, hv, h⟩ | ⟨w', hw', h⟩)
      · have h1 : (G.pl.w v).asIdeal ≤ w.asIdeal := (Ideal.IsPrime.pow_le_iff (hc v)).1 h
        have h2 : G.pl.w v = w := HeightOneSpectrum.ext ((G.pl.w v).isMaximal.eq_of_le hp.ne_top h1)
        unfold locPl Places.W0
        exact Finset.mem_union_left _ (h2 ▸ Finset.mem_image_of_mem _ hv)
      · have h2 : w' = w := HeightOneSpectrum.ext (w'.isMaximal.eq_of_le hp.ne_top h)
        subst h2
        exact (Finset.mem_filter.1 hw').1
    · intro hw
      by_cases h0 : w ∈ G.pl.W0
      · unfold Places.W0 at h0
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h0
        exact Or.inl ⟨v, hv, Ideal.pow_le_self (hc v)⟩
      · exact Or.inr ⟨w, Finset.mem_filter.2 ⟨hw, h0⟩, le_rfl⟩
  unfold sfB
  simp only [Finset.mem_image, key]

end GlobalTheory.NormRatio
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem tl_free_finrank : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K), Module.Free ℤ_[l] (Tl l A) ∧ Module.Finite ℤ_[l] (Tl l A) ∧ Module.finrank ℤ_[l] (Tl l A) = 2 * A.dim ∧ Module.Finite ℚ_[l] (Vl l A) ∧ Module.finrank ℚ_[l] (Vl l A) = 2 * A.dim := by
  intro K _ l _ hl A
  have hc : ∀ n : ℕ, Nat.card {x : A.Pt // x ^ (l ^ n) = 1} = l ^ (2 * A.dim * n) := by
    intro n
    have h := GlobalTheory.T.card_torsion_geometricPoints_eq_pow_two_dim K A (l ^ n) (by push_cast; exact pow_ne_zero _ hl)
    rw [h, ← pow_mul, mul_comm n]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.TateFree.free_finite_finrank A.Pt l (2 * A.dim) hc
  refine ⟨h1, h2, h3, inferInstance, ?_⟩
  rw [Module.finrank_baseChange, h3]

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDimStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModule_free_finrank_two_mul_dim : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K), Module.Free ℤ_[l] (Tl l A) ∧ Module.Finite ℤ_[l] (Tl l A) ∧ Module.finrank ℤ_[l] (Tl l A) = 2 * A.dim ∧ Module.Finite ℚ_[l] (Vl l A) ∧ Module.finrank ℚ_[l] (Vl l A) = 2 * A.dim := by
  first | exact @GlobalTheory.AV.AbVar.tl_free_finrank | exact GlobalTheory.AV.AbVar.tl_free_finrank | (intros; apply GlobalTheory.AV.AbVar.tl_free_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStanding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStanding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FunObj

theorem squareTriple_of_standing {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) : SquareTriple W t i j := by
  intro M hM
  obtain ⟨S₀, Q, hSQ, hX⟩ := GlobalTheory.T.squareCharacters_isGood_gridPlaces hL t i j hst
  choose τf hτf using (GlobalTheory.T.exists_conj_tauE_comp_algebraMap_eq_embedding (D := D))
  obtain ⟨mα, mβ, hα, hβ, hκ⟩ := GlobalTheory.T.thetaGridCharacters_archExponents_gap_gt_rank hL t i j hst τf hτf
  obtain ⟨v₁, hv₁P, hv₁s, hv₁l, ⟨τ₁⟩⟩ := GlobalTheory.T.exists_splitCompletely_auxiliary_place_outside_finset (G := G) hL t (S₀ ∪ Q)
  have hτP : ∀ v : (S₀ ∪ Q : Finset (HeightOneSpectrum (𝓞 D.host.F))),
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) := fun v => (hSQ v v.2).2
  let B : Base D.host.F D.host.E :=
    ⟨W.ψ, fun w => ⟨_, hτf w⟩, mα, mβ, S₀ ∪ Q, fun v => (hτP v).some, v₁, τ₁⟩
  have hB : B.IsGood D.sp.cm.sig := GlobalTheory.T.isAdmissibleCMBaseData_of_squareTupleStanding hL W t hst B rfl fun v hv => (hSQ v hv).1
  have hemb : ∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  obtain ⟨e⟩ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.nonempty_num (G := G) (i := i) (j := j) hL (by omega) (by omega)
  obtain ⟨ΛV, basV, hV⟩ := GlobalTheory.T.exists_hermitian_lattice_local_bases hL W i j B τf hemb
  obtain ⟨ΛV', basV', hV'⟩ := GlobalTheory.T.exists_negConj_member_hermitianLatticeSpaceData hL W i j B τf hemb
  obtain ⟨ΛW, basW, hW⟩ := GlobalTheory.T.gridSquare_skewSumSpace_isSkewHermitianSelfDual hL W i j e B τf hemb
  obtain ⟨co, vac, dom, hMo⟩ := GlobalTheory.T.exists_goodSchrodingerModel_conjugateDoubled hL t i j M hM B hB _ _ rfl _ _ _ _ hV hW
  obtain ⟨co', vac', dom', hMo'⟩ := GlobalTheory.T.squareModel_negSpace_goodSchroedinger hL t i j M hM B hB _ _ rfl _ _ _ _ hV' hW
  obtain ⟨om, hom⟩ := GlobalTheory.T.exists_weilRep_dualPair_characters_beta_quotient hL t i j hst B hB _ _ _ _ _ _ hV hW _ hMo
  obtain ⟨om', hom'⟩ := GlobalTheory.T.exists_weilRep_squarePair_characters_alpha_quotient hL t i j hst B hB _ _ _ _ _ _ hV' hW _ hMo'
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.thetaGridSquare_rank_inequalities (G := G) hL i j
  refine ⟨e, B, ⟨(D.R.m - j - 1) / 2, (D.R.m - j) / 2, _, _, _, Model.mk co vac ((M.ν (.grid ((i : ℕ) + 1) ((j : ℕ) + 1))).map
      (conjU (spW G i j) (J := (1 : D.host.E) • (spW G i j).gram) 1 rfl)) dom,
    Model.mk co' vac' ((M.ν (.grid (i : ℕ) (j : ℕ))).map
      (conjU (spW₁ G i j) (J := (-1 : D.host.E) • (spW₁ G i j).gram) (-1) rfl)) dom'⟩,
    ⟨alpha G t i j, beta G i j, S₀, Q⟩, om, om', ?_, ?_, hv₁l⟩
  · exact ⟨rfl, rfl, rfl, rfl, fun w => ⟨τf w, fun _ => rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
  · exact ⟨hB, ⟨h1, h2, hκ, h3, h4, hV, hV', hW, hMo, hMo'⟩, hX B subset_rfl hv₁P hv₁s hα hβ, hom, hom'⟩

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStandingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareThetaTripleHypotheses_of_standing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → SquareTriple W t i j := by
  first | exact @GlobalTheory.FunObj.squareTriple_of_standing | exact GlobalTheory.FunObj.squareTriple_of_standing | (intros; apply GlobalTheory.FunObj.squareTriple_of_standing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIdealWeightSection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseOpenEqTopOfSmoothOfRelativeDimensionZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseOpenEqTopOfSmoothOfRelativeDimensionZero
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory

theorem dense_open_eq_top_of_smoothOfRelativeDimension_zero : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k), SmoothOfRelativeDimension 0 p → ∀ (U : Y.Opens), Dense (U : Set Y) → U = ⊤ := by
  intro k _ Y p hp U hU
  have he : Etale p := (Etale.iff_smoothOfRelativeDimension_zero p).2 hp
  have hq : LocallyQuasiFinite p := by
    refine ⟨fun {V} hV {W} hW e ↦ ?_⟩
    have h := p.etale_appLE hV hW e
    letI := (p.appLE V W e).hom.toAlgebra
    have : Algebra.Etale Γ(Sp k, V) Γ(Y, W) := h
    exact (inferInstance : Algebra.QuasiFinite Γ(Sp k, V) Γ(Y, W))
  have hsub : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hopen : ∀ y : Y, IsOpen ({y} : Set Y) := by
    intro y
    have hd : _root_.IsDiscrete (p ⁻¹' {p y}) := p.isDiscrete_preimage_singleton (p y)
    have huniv : p ⁻¹' {p y} = Set.univ := by
      ext z; simp [Subsingleton.elim (p z) (p y)]
    rw [huniv] at hd
    have : DiscreteTopology Y := by
      have h2 := hd.to_subtype
      exact (Homeomorph.Set.univ Y).symm.isEmbedding.discreteTopology
    exact isOpen_discrete _
  refine eq_top_iff.2 fun y _ ↦ ?_
  obtain ⟨z, hz1, hz2⟩ := hU.inter_open_nonempty {y} (hopen y) ⟨y, rfl⟩
  rw [Set.mem_singleton_iff] at hz1
  subst hz1
  exact hz2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseOpenEqTopOfSmoothOfRelativeDimensionZeroStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_open_eq_univ_of_smooth_relDim_zero : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k), SmoothOfRelativeDimension 0 p → ∀ (U : Y.Opens), Dense (U : Set Y) → U = ⊤ := by
  first | exact @GlobalTheory.dense_open_eq_top_of_smoothOfRelativeDimension_zero | exact GlobalTheory.dense_open_eq_top_of_smoothOfRelativeDimension_zero | (intros; apply GlobalTheory.dense_open_eq_top_of_smoothOfRelativeDimension_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIdealWeightSection
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogCanon

theorem restr_top_surj {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (h : O = ⊤)
    (x : H0 p B O) : ∃ g : H0 p B ⊤, H0.restr le_top g = x := by
  subst h
  refine ⟨x, ?_⟩
  show (LB.toMod B).presheaf.map (homOfLE (le_refl (⊤ : Y.Opens))).op x = x
  rw [show (homOfLE (le_refl (⊤ : Y.Opens))).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

theorem dimFlag_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (h : ¬ 1 ≤ Dw.p + Dw.q) : dimFlag Dw = 0 := by
  have : Dw.p + Dw.q = 0 := by omega
  simp [GlobalTheory.FlagTan.dimFlag, this]

theorem logCanon_iff : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z hF M ω b s hs m
  have hV : IsVariety₀ TF.X Z := GlobalTheory.T.flagSpace_component_smooth_projective_connected E H Dw l Xo c TF Z hF
  by_cases hpq : 1 ≤ Dw.p + Dw.q
  · have hKS : (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) := fun K _ _ y => GlobalTheory.T.kodaira_spencer_iso_flag_tangent hP hG E H Dw l Xo c K y hpq
    obtain ⟨ω₀⟩ := GlobalTheory.T.nonempty_kodairaSpencer_identification_offBoundary hP.p5 E H Dw l Xo c TF.Y TF.X Z (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) hKS
    exact (GlobalTheory.T.canonical_modification_ks_iso hP hG E H Dw l Xo c TF Z hF hKS hV ω₀ b s hs m).trans (GlobalTheory.T.canonical_modification_ks_iso_sec hP hG E H Dw l Xo c TF Z hF hKS hV ω₀ M ω b s hs m)
  · have h0 := dimFlag_eq_zero Dw hpq
    have hU : U₀ TF.X Z = ⊤ := GlobalTheory.T.dense_open_eq_univ_of_smooth_relDim_zero c.F _ (str₀ TF.X Z) (h0 ▸ hV.1) _ (dense_U₀ TF.X Z)
    have hall : ∀ y, y ∈ U₀ TF.X Z := fun y => hU.symm ▸ (Set.mem_univ y : y ∈ ((⊤ : (Y₀ TF.X Z).Opens) : Set _))
    have hoff : M.off = ⊤ := eq_top_iff.2 fun x _ => M.off_eq.ge (hall _)
    refine iff_of_true ?_ (restr_top_surj hoff _)
    obtain ⟨g, hg⟩ := restr_top_surj hU m
    refine ⟨g, fun y hy => (hy (hall y)).elim, hg⟩

end GlobalTheory.LogCanon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIdealWeightSectionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_ideal_weight_section : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw) (hs : FlagTan.kap Dw + b = s) (m : H0 (str₀ TF.X Z) (L₀ TF.X Z s) (U₀ TF.X Z)), (∃ g ∈ vanBd TF.X Z s, H0.restr le_top g = m) ↔ ∃ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, H0.restr le_top g = (((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs).mul ω.ω (M.pullOff m) := by
  first | exact @GlobalTheory.LogCanon.logCanon_iff | exact GlobalTheory.LogCanon.logCanon_iff | (intros; apply GlobalTheory.LogCanon.logCanon_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateBaseOfReciprocity
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)

theorem baseLat_le
    (hinj : ∀ (ρ : Setup D.ntw) (hρ : ρ.Good) (ν : ℂ), ν ≠ 0 → Function.Injective (rdAt p w j hρ ν))
    (hgen : ∀ (ρ : Setup D.ntw), ρ.Good → RealPin p.R p.cG ρ → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range h →
      P ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
        (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)))
    (hunit : ∀ (ρ ρ' : Setup D.ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ),
      RealPin p.R p.cG ρ → ρ.LevelOf D.nexp → RealPin p.R p.cG ρ' → SameBut ρ ρ' →
      IsNorm p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ν → IsNorm p.R p.v₀ (ρ'.B (ex.nch.twI w) j (ex.nch.sd w)) ν' →
      RatBase (rdAt p w j hρ ν) → RatBase (rdAt p w j hρ' ν') →
      ∀ s h P, ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h P → P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h →
        ∀ f f', rdAt p w j hρ ν f = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P →
          rdAt p w j hρ' ν' f' = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P →
          ∃ u : FractionRing (D.ntw.O (ex.nch.twI w)), (∃ n : ℕ, n ≠ 0 ∧ u ^ n = 1) ∧ f' = u • f)
    (ρ ρ' : Setup D.ntw) (hρ : ρ.Good) (hρ' : ρ'.Good) (ν ν' : ℂ) (hp : RealPin p.R p.cG ρ) (hL : ρ.LevelOf D.nexp) (hp' : RealPin p.R p.cG ρ')
    (hS : SameBut ρ ρ') (hN : IsNorm p.R p.v₀ (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) ν)
    (hN' : IsNorm p.R p.v₀ (ρ'.B (ex.nch.twI w) j (ex.nch.sd w)) ν')
    (hR : RatBase (rdAt p w j hρ ν)) (hR' : RatBase (rdAt p w j hρ' ν')) :
    baseLat p w j hρ ν ≤ baseLat p w j hρ' ν' := by
  have hbad := hS.2.2.1
  have hB := hS.2.2.2.1
  have hom := hS.2.2.2.2
  have hth : ∀ h P, ρ'.theta (ex.nch.twI w) j (ex.nch.sd w) h P = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h P := by
    intro h P
    simp only [Setup.theta, hB, hom]
  have hlat : ∀ O h, ρ'.lat (ex.nch.twI w) j (ex.nch.sd w) O h = ρ.lat (ex.nch.twI w) j (ex.nch.sd w) O h := by
    intro O h
    simp only [Setup.lat, hB]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨s, h, P, hd, hf⟩, rfl⟩
  have key : ∀ Q ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
      (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)),
      ∃ g, rdAt p w j hρ ν g = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h Q ∧
        ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] g) ∈ baseLat p w j hρ' ν' := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      have hd1 : ρ.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h Q :=
        ⟨hd.split, hd.off, hd.fin, hd.supp, lat_mono ρ _ j _ (smallInt_le hρ _ _) h hQ⟩
      have hd2 : ρ'.IsDatum (ex.nch.twI w) j (ex.nch.sd w) s h Q :=
        ⟨hd.split, by rw [hbad]; exact hd.off, hd.fin, hd.supp,
          lat_mono ρ' _ j _ (smallInt_le hρ' _ _) h (by rw [hlat]; exact hQ)⟩
      obtain ⟨g, hg⟩ := hR s h Q hd1
      obtain ⟨g', hg'⟩ := hR' s h Q hd2
      rw [hth] at hg'
      obtain ⟨u, ⟨n, hn, hu⟩, hgu⟩ := hunit ρ ρ' hρ hρ' ν ν' hp hL hp' hS hN hN' hR hR' s h Q hd1 hQ g g' hg hg'
      obtain ⟨o, ho⟩ := exists_inv_of_root u n hn hu
      have hu0 : u ≠ 0 := by
        rintro rfl
        rw [zero_pow hn] at hu
        exact zero_ne_one hu
      have hgo : g = o • g' := by
        rw [← algebraMap_smul (FractionRing (D.ntw.O (ex.nch.twI w))) o g', ho, hgu, smul_smul, inv_mul_cancel₀ hu0, one_smul]
      refine ⟨g, hg, ?_⟩
      rw [hgo, TensorProduct.tmul_smul]
      refine Submodule.smul_of_tower_mem _ o (Submodule.subset_span ⟨g', ⟨s, h, Q, hd2, ?_⟩, rfl⟩)
      rw [hg', hth]
    | zero =>
      refine ⟨0, ?_, by rw [TensorProduct.tmul_zero]; exact zero_mem _⟩
      rw [map_zero]
      exact (map_zero _).symm
    | add Q1 Q2 _ _ h1 h2 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨g2, e2, m2⟩ := h2
      refine ⟨g1 + g2, ?_, by rw [TensorProduct.tmul_add]; exact add_mem m1 m2⟩
      rw [map_add (f := _), e1, e2]
      exact (map_add _ _ _).symm
    | smul a Q _ h1 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨o, ho⟩ := a.2
      refine ⟨o • g1, ?_, by rw [TensorProduct.tmul_smul]; exact Submodule.smul_of_tower_mem _ o m1⟩
      rw [rd_smul, e1]
      change _ = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).theta (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) h ((a : ℂ) • Q)
      rw [map_smul, ← ho]
  obtain ⟨g, hg, hm⟩ := key P (hgen ρ hρ hp h P hd.mem)
  have : f = g := hinj ρ hρ ν hN.1 (hf.trans hg.symm)
  rw [this]
  exact hm

end Point

end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortOfInputs
set_option synthInstance.maxHeartbeats 400000

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.CovHt.ShortPf

theorem budget_arith {f r l b PP T d ρ s : ℝ} (hf : 1 ≤ f) (hr : 1 ≤ r) (hl : 1 ≤ l) (hP : (f * r * l) ^ 12 ≤ PP)
    (hd : 1 ≤ d) (hT : d ^ 2 * PP ≤ T) (hTb : T ≤ b) (hρ : 0 ≤ ρ) (hρ1 : d * ρ * PP ≤ 6 * r ^ 2) (hs : 0 ≤ s)
    (hs1 : T * s ≤ 8 * f * r * b) :
    ((f * r * l) ^ 3 * s + (f * r * l) ^ 5) * (6 * d + 10 + T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ)) ≤ 693 * (f * b) := by
  have hrZ : r ≤ f * r * l := by
    calc r = 1 * r * 1 := by ring
      _ ≤ _ := by gcongr
  generalize f * r * l = Z at *
  have hZ : 1 ≤ Z := hr.trans hrZ
  have h7 : Z ^ 7 ≤ PP := (pow_le_pow_right₀ hZ (by norm_num)).trans hP
  have hP0 : 0 < PP := lt_of_lt_of_le (by positivity) h7
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hb0 : 0 < b := hT0.trans_le hTb
  have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have e : T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ) = 7 * d ^ 2 + 7 * T * (d * ρ) + 2 * T * ρ := by field_simp
  have hF : (6 * d + 10 + T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ)) * PP ≤ 77 * (r ^ 2 * T) := by
    rw [e]
    have a1 : d ≤ d ^ 2 := le_self_pow₀ hd (by norm_num)
    have a2 : ρ ≤ d * ρ := le_mul_of_one_le_left hρ hd
    have a3 : 6 * d + 10 + (7 * d ^ 2 + 7 * T * (d * ρ) + 2 * T * ρ) ≤ 23 * d ^ 2 + 9 * T * (d * ρ) := by
      nlinarith [mul_le_mul_of_nonneg_left a2 hT0.le]
    have a4 := mul_le_mul_of_nonneg_right a3 hP0.le
    have a5 := mul_le_mul_of_nonneg_left hρ1 hT0.le
    have a6 : T ≤ r ^ 2 * T := le_mul_of_one_le_left hT0.le hr2
    nlinarith
  generalize 6 * d + 10 + T * (7 * (d ^ 2 / T + d * ρ) + 2 * ρ) = F at hF ⊢
  refine le_of_mul_le_mul_right ?_ hP0
  have b1 : (Z ^ 3 * s + Z ^ 5) * (F * PP) ≤ (Z ^ 3 * s + Z ^ 5) * (77 * (r ^ 2 * T)) :=
    mul_le_mul_of_nonneg_left hF (by positivity)
  have b2 : Z ^ 3 * r ^ 2 * (T * s) ≤ Z ^ 3 * r ^ 2 * (8 * f * r * b) := mul_le_mul_of_nonneg_left hs1 (by positivity)
  have b3 : Z ^ 3 * r ^ 3 ≤ PP := by
    calc Z ^ 3 * r ^ 3 ≤ Z ^ 3 * Z ^ 4 :=
          mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by linarith) hrZ 3).trans (pow_le_pow_right₀ hZ (by norm_num)))
            (by positivity)
      _ = Z ^ 7 := by ring
      _ ≤ _ := h7
  have b4 : Z ^ 5 * r ^ 2 ≤ PP := by
    calc Z ^ 5 * r ^ 2 ≤ Z ^ 5 * Z ^ 2 := by gcongr
      _ = Z ^ 7 := by ring
      _ ≤ _ := h7
  have b5 : Z ^ 3 * r ^ 3 * (f * b) ≤ PP * (f * b) := mul_le_mul_of_nonneg_right b3 (by positivity)
  have b6 : Z ^ 5 * r ^ 2 * T ≤ PP * (f * b) :=
    mul_le_mul b4 (hTb.trans (le_mul_of_one_le_left hb0.le hf)) hT0.le hP0.le
  nlinarith

theorem len_mul_l1_le {ι : Type} [Fintype ι] {N : ℕ} (W : GlobalTheory.MeanTop.Wts ι N) (hW : W.Hyp) (hD : W.IsDiv) :
    (W.T : ℝ) * GlobalTheory.MeanTop.l1 W.u1 ≤ Fintype.card ι * (N * (2 * W.b)) := by
  refine (GlobalTheory.MeanTop.divided_weight_size _ _ W hW hD).1.trans ?_
  have h : ∑ τ, ∑ k, (|(W.u τ k : ℝ)| + W.c0 + 4 * N) ≤ ∑ _τ : ι, ∑ _k : Fin N, 2 * W.b :=
    Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => hW.h5 τ k
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  unfold GlobalTheory.MeanTop.l1
  linarith

theorem fieldSz_host {D : D7} {L : SizeData₂ D} {PP A M : ℝ} (h : HostNum D L PP A M) : fieldSz D.host.E ≤ 3 * L.sc.L := by
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast h.f8
  have hr : (2 : ℝ) ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    exact_mod_cast (by unfold Ranks.r; omega : 2 ≤ D.R.r)
  unfold fieldSz
  rw [h.deg]
  push_cast
  have a1 : Real.log (2 * (D.R.f : ℝ)) ≤ Real.log ((D.R.f : ℝ) * D.R.r) := Real.log_le_log (by linarith) (by nlinarith)
  have a2 : Real.log |(discr D.host.E : ℝ)| / (2 * (D.R.f : ℝ)) ≤ 2 * L.sc.L := by
    rw [div_le_iff₀ (by linarith)]
    linarith [h.disc]
  linarith [h.logfr.1]

theorem log_level {D : D7} {L : SizeData₂ D} {PP A M : ℝ} (h : HostNum D L PP A M) :
    Real.log ((D.host.g 0 * D.host.g 1 * 15 ^ expL L.sc.L : ℕ) : ℝ) ≤ 30 * L.sc.L := by
  have hL := h.big.2.1
  have g0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have g1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have l3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have a1 : (expL L.sc.L : ℝ) * Real.log 3 ≤ 3 * L.sc.L :=
    (le_div_iff₀ l3).1 (Nat.floor_le (div_nonneg (by linarith) l3.le))
  have a2 : Real.log 15 ≤ 3 * Real.log 3 := by
    have : Real.log ((3 : ℝ) ^ 3) = 3 * Real.log 3 := by rw [Real.log_pow]; norm_num
    rw [← this]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have a3 := mul_le_mul_of_nonneg_left a2 (Nat.cast_nonneg (α := ℝ) (expL L.sc.L))
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul g0.ne' g1.ne', Real.log_pow]
  linarith [h.logg 0, h.logg 1]

section Point

open _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)


set_option maxHeartbeats 800000 in
theorem weight_rows {PP A : ℝ} (h : HostNum D L PP A 1) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m)
    (u1 : AllWt.Weight (dat p i)) (hq : Quo p i PP u1) :
    1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ (∀ τ, Antitone (u1 τ)) ∧
    (∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p →
      ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ u1 τ a - u1 τ b) ∧
    Real.log (∑ τ, ∑ k, |(u1 τ k : ℝ)|) ≤ 10 * L.sc.L ∧
    (((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 3 * (∑ τ, ∑ k, |(u1 τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 5) *
      (6 * dimFlag (dat p i) + 10 + lenT p i PP * (zed p i PP u1 + 2 * rhoB (dat p i) u1)) ≤ 693 * unitE p := by
  obtain ⟨h0, S, eta, -, -, -, -, hh, hH⟩ := hw.hyp hi
  have hW := hH u1
  have hD := (quo_iff p i PP h0 S eta u1).1 hq
  have m2 := D.R.two_le_m
  have k3 := D.R.m_add_three_le_k
  have f8 := h.f8
  have hL := h.big.2.1
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f8
  have hr : (2 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 2 ≤ D.R.r)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hcard : Fintype.card (Psi p.T.Q.H) = D.R.f := by rw [← hw.card, Nat.card_eq_fintype_card]
  have hDd : (1 : ℝ) ≤ dimFlag (dat p i) := by
    rw [hw.dim]
    exact_mod_cast Nat.mul_pos (by omega) (Nat.choose_pos (by unfold Ranks.r; omega))
  have hT : (1 : ℝ) ≤ lenT p i PP := by
    have : 4 * dimFlag (dat p i) + 4 ≤ lenT p i PP := hW.h1
    exact_mod_cast (by omega : 1 ≤ lenT p i PP)
  have hP : ((D.R.f : ℝ) * D.R.r * L.sc.L) ^ 12 ≤ PP := h.ppLow
  have hZ : (160 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * L.sc.L := by
    calc (160 : ℝ) = 8 * 2 * 10 := by norm_num
      _ ≤ _ := by gcongr
  have hP1 : 160 ≤ PP := hZ.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hP)
  have kp : (wtsAt p i PP h0 S eta u1).kc < (dat p i).p := hW.kc_lt
  have pq : (dat p i).p < (dat p i).p + (dat p i).q := hW.p_lt
  have s0 : 0 ≤ ∑ τ, ∑ k, |(u1 τ k : ℝ)| := by positivity
  have s1 : (lenT p i PP : ℝ) * ∑ τ, ∑ k, |(u1 τ k : ℝ)| ≤ 8 * D.R.f * D.R.r * L.sc.b := by
    have := len_mul_l1_le _ hW hD
    rw [hcard, show (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r by rw [hw.sig.2.2]] at this
    refine le_trans this (le_of_eq ?_)
    show (D.R.f : ℝ) * (D.R.r * (2 * (4 * L.sc.b))) = _
    ring
  have h1 : PP * lenT p i PP * D.R.r * D.R.f * dimFlag (dat p i) ≤ h0 := by
    refine le_trans ?_ hh
    have a1 : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
    have a2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := one_le_pow₀ hm
    calc _ = PP * lenT p i PP * D.R.r * D.R.f * 1 * 1 * dimFlag (dat p i) := by ring
      _ ≤ _ := by gcongr; linarith
  refine ⟨by omega, by omega, fun τ => (GlobalTheory.MeanTop.divided_strictAnti _ _ _ hW hD τ).1.antitone, fun τ a b hab hb' => ?_, ?_, ?_⟩
  · have g : h0 ≤ 2 * (lenT p i PP : ℤ) * (u1 τ a - u1 τ b) := ((GlobalTheory.MeanTop.divided_gaps _ _ _ hW hD τ a b hab).2.1 hb').1
    have g' : (h0 : ℝ) ≤ 2 * (lenT p i PP : ℝ) * ((u1 τ a : ℝ) - u1 τ b) := by exact_mod_cast g
    have a1 : 160 * lenT p i PP * D.R.r * D.R.f * 1 ≤ PP * lenT p i PP * D.R.r * D.R.f * dimFlag (dat p i) := by gcongr
    have a2 : 80 * ((D.R.f : ℝ) * D.R.r) ≤ (u1 τ a : ℝ) - u1 τ b := by
      refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < 2 * lenT p i PP by linarith)
      linarith
    have a3 : (16 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    have a4 : 8 * (D.R.f : ℝ) * D.R.r + 10 ≤ (u1 τ a : ℝ) - u1 τ b := by linarith
    exact_mod_cast a4
  · rcases s0.eq_or_lt with e | e
    · rw [← e, Real.log_zero]; linarith
    have a1 := Real.log_le_log e ((le_mul_of_one_le_left s0 hT).trans s1)
    rw [mul_assoc 8, Real.log_mul (by positivity) hb.ne', Real.log_mul (by norm_num) (by positivity),
      show Real.log L.sc.b = L.sc.L from Real.log_exp _] at a1
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num), h.logfr.1]
  · obtain ⟨r0, -, r2⟩ := GlobalTheory.CovTop.SizeRows.rho_bounds _ hW hD
    have er : rhoOf (wtsAt p i PP h0 S eta u1).u' (wtsAt p i PP h0 S eta u1).u1 = rhoB (dat p i) u1 := by
      unfold rhoB
      congr 1
      funext τ k
      rw [uPrime_apply]; rfl
    rw [er] at r0 r2
    have r3 : rhoB (dat p i) u1 * h0 ≤ 6 * D.R.f * (D.R.r : ℝ) ^ 3 * lenT p i PP := by
      rw [← hcard, ← hw.sig.2.2]; exact r2
    have r4 : dimFlag (dat p i) * rhoB (dat p i) u1 * PP ≤ 6 * (D.R.r : ℝ) ^ 2 := by
      refine le_of_mul_le_mul_right ?_ (show (0 : ℝ) < D.R.f * D.R.r * lenT p i PP by positivity)
      linarith [mul_le_mul_of_nonneg_left h1 r0]
    have hTl : (dimFlag (dat p i) : ℝ) ^ 2 * PP ≤ lenT p i PP := by
      refine le_trans ?_ (Nat.le_ceil _)
      rw [le_div_iff₀ (by linarith), mul_comm _ PP]
      have : PP ≤ PP ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
      gcongr
    have hTb : (lenT p i PP : ℝ) ≤ L.sc.b := by
      refine le_trans ?_ hw.what₂.2
      have a2 : (1 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2 := one_le_pow₀ hDd
      calc (lenT p i PP : ℝ) = 1 * lenT p i PP * 1 * 1 := by ring
        _ ≤ _ := by gcongr <;> linarith
    refine (budget_arith (by linarith) (by linarith) (by linarith) hP hDd hTl hTb r0 r4 s0 s1).trans ?_
    rw [hw.unit]
    have hll := h.big.2.2.2
    calc 693 * ((D.R.f : ℝ) * L.sc.b) = 693 * (D.R.f * 1 * L.sc.b * 1 * 1) := by ring
      _ ≤ _ := by gcongr; linarith

end Point


end GlobalTheory.CovHt.ShortPf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodAtOfAntitoneGapWeight
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.ShiftGood

variable {D : D7} {T : Core D} {j : ℕ}

theorem cuspW_eq_of_exZ {Y : Deep T j} {e : ℕ} {o : ℝ} (hY : Y.Good e o) {G G' : WTZ D.host.E}
    (h : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) G') : Y.V G = Y.V G' := by
  ext f
  rw [GlobalTheory.AllWt.mem_cuspW, GlobalTheory.AllWt.mem_cuspW, h]
  refine and_congr_right fun _ => forall₂_congr fun σ hσ => ?_
  rw [GlobalTheory.AllWt.modelWt_congr (Y.U σ) hσ (hY.unf σ hσ) h]

theorem goodAt_of_exZ {Y : Deep T j} {e : ℕ} {o : ℝ} (hY : Y.Good e o) {G G' : WTZ D.host.E}
    (h : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) G') (hG : Y.GoodAt G) : Y.GoodAt G' := by
  set_option synthInstance.maxHeartbeats 200000 in
  have hGram' : GlobalTheory.AllWt.HasGram (Y.nrm G') := by
    let φ : Y.V G ≃ₗ[Y.d.c₂.F] Y.V G' := LinearEquiv.ofEq _ _ (cuspW_eq_of_exZ hY h)
    let t : ℝ := GlobalTheory.AllWt.lieFacZ (T.Q.Dw j) (xiR D) G' / GlobalTheory.AllWt.lieFacZ (T.Q.Dw j) (xiR D) G
    have ht : 0 < t := div_pos (GlobalTheory.AllWt.lieFacZ_pos _ _) (GlobalTheory.AllWt.lieFacZ_pos _ _)
    have hscale : ∀ σ (f : Y.V G), Y.nrm G' σ (φ f) = t * Y.nrm G σ f := by
      intro σ f
      have hσ' : GoodEmb Y.d.c₂ (Formalism.L2.Pj.goodOf Y.d.c₂ σ) := Formalism.L2.Pj.goodEmb_goodOf _ _
      have hmw := GlobalTheory.AllWt.modelWt_congr (Y.U _) hσ' (hY.unf _ hσ') h
      change GlobalTheory.AllWt.petAt _ _ _ _ _ G' (f : Rul Y.d.Xo₂ Y.d.c₂) =
        t * GlobalTheory.AllWt.petAt _ _ _ _ _ G (f : Rul Y.d.Xo₂ Y.d.c₂)
      unfold GlobalTheory.AllWt.petAt
      rw [hmw]
      have hpos : GlobalTheory.AllWt.lieFacZ (T.Q.Dw j) (xiR D) G ≠ 0 := (GlobalTheory.AllWt.lieFacZ_pos _ _).ne'
      simp only [t]
      field_simp [hpos]
    obtain ⟨⟨n, ⟨b, X⟩, hX⟩⟩ := hG.1
    refine ⟨⟨n, ⟨(b.map φ, fun v => ((t : ℂ)⁻¹) • X v), fun v => ?_⟩⟩⟩
    have hk : ((t : ℂ)⁻¹) ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 ht.ne')
    have hdet := (hX v).1
    refine ⟨?_, fun y => ?_⟩
    · show IsUnit ((((t : ℂ)⁻¹) • X v).det)
      rw [Matrix.det_smul]
      exact (IsUnit.pow _ (Ne.isUnit hk)).mul hdet
    · show Formalism.HermitianLatticesTheory.normAt (b.map φ) (fun v => ((t : ℂ)⁻¹) • X v) v y = Y.nrm G' v.embedding y
      have := invertibleOfNonzero hk
      rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, Matrix.inv_smul _ _ hdet, invOf_eq_inv]
      have hvec : Formalism.HermitianLatticesTheory.vecAt (b.map φ) v y = Formalism.HermitianLatticesTheory.vecAt b v (φ.symm y) := by
        funext i; simp [Formalism.HermitianLatticesTheory.vecAt, Module.Basis.map_repr]
      rw [hvec, Matrix.smul_mulVec]
      have hcnorm : ∀ (a : ℂ) (u : Fin n → ℂ),
          Formalism.HermitianLatticesTheory.cnorm (a • u) = ‖a‖ * Formalism.HermitianLatticesTheory.cnorm u := by
        intro a u
        unfold Formalism.HermitianLatticesTheory.cnorm
        have hs : ∑ i, ‖(a • u) i‖ ^ 2 = ‖a‖ ^ 2 * ∑ i, ‖u i‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [Pi.smul_apply, mul_pow]
        rw [hs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      rw [hcnorm, ← Formalism.HermitianLatticesTheory.fcoord, ← Formalism.HermitianLatticesTheory.normAt, (hX v).2,
        ← φ.apply_symm_apply y, hscale, φ.apply_symm_apply, inv_inv, Complex.norm_real, Real.norm_of_nonneg ht.le]
  refine ⟨hGram', ?_⟩
  have key : ∀ C C' : Submodule Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂), C = C' →
      ((GlobalTheory.AllWt.supLat C).FG ∧ Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.supLat C : Set C) = ⊤) →
      ((GlobalTheory.AllWt.supLat C').FG ∧ Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.supLat C' : Set C') = ⊤) := by
    rintro C _ rfl; exact id
  exact key _ _ (cuspW_eq_of_exZ hY h) hG.2

end GlobalTheory.CovTop.ShiftGood

namespace GlobalTheory.CovTop.ShiftGood

end GlobalTheory.CovTop.ShiftGood

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
private theorem tate_nsmul_lev {p : ℕ} {M : Type} [CommGroup M]
    (s : _root_.GlobalTheory.HTLat.Tate p M) (k m : ℕ) :
    (k • s).lev m = s.lev m ^ k := by
  induction k with
  | zero => simp [_root_.GlobalTheory.HTLat.Tate.lev_zero]
  | succ k ih => rw [succ_nsmul, _root_.GlobalTheory.HTLat.Tate.lev_add, ih, pow_succ]


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.AV.AbVar.tl_lev_surj_ker : ∀ (K : Type) [Field K]
    (l : ℕ) [Fact l.Prime] (A : _root_.GlobalTheory.AV.AbVar K) (n : ℕ),
    (∀ x : A.Pt, x ^ l ^ n = 1 →
        ∃ t : _root_.GlobalTheory.AV.AbVar.Tl l A, t.lev n = x) ∧
      ∀ t : _root_.GlobalTheory.AV.AbVar.Tl l A, t.lev n = 1 ↔
        ∃ s : _root_.GlobalTheory.AV.AbVar.Tl l A, t = (l : ℤ_[l]) ^ n • s := by
  intro K _ l hl A n
  have hlpos : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  refine ⟨fun x hx => _root_.GlobalTheory.Published.tate_lev_surj l _
    (_root_.GlobalTheory.AV.AbVar.pt_divisible K A l hlpos) n x hx, fun t => ?_⟩
  have hcast : ∀ s : _root_.GlobalTheory.AV.AbVar.Tl l A,
      (l : ℤ_[l]) ^ n • s = (l ^ n : ℕ) • s := by
    intro s
    apply Subtype.ext
    funext m
    change ((l : ℤ_[l]) ^ n • s).lev m = ((l ^ n : ℕ) • s).lev m
    rw [_root_.GlobalTheory.HTLat.Tate.lev_smul, tate_nsmul_lev, ← Nat.cast_pow]
    exact _root_.GlobalTheory.PDiv.pow_digit_natCast (s.lev_pow m) (l ^ n)
  constructor
  · intro ht
    let u : ℕ → A.Pt := fun m => t.lev (m + n)
    have hu : ∀ m, u m ^ l ^ m = 1 ∧ u (m + 1) ^ l = u m := by
      intro m
      refine ⟨?_, ?_⟩
      · simp only [u]
        rw [Nat.add_comm, _root_.GlobalTheory.HTLat.Tate.lev_add_pow, ht]
      · simp only [u]
        rw [show m + 1 + n = m + n + 1 by omega, _root_.GlobalTheory.HTLat.Tate.lev_succ]
    refine ⟨_root_.GlobalTheory.HTLat.Tate.mk u hu, ?_⟩
    rw [hcast]
    apply Subtype.ext
    funext m
    change t.lev m = ((l ^ n : ℕ) • _root_.GlobalTheory.HTLat.Tate.mk u hu).lev m
    rw [tate_nsmul_lev,
      _root_.GlobalTheory.HTLat.Tate.lev_mk]
    simp only [u, _root_.GlobalTheory.HTLat.Tate.lev_add_pow]
  · rintro ⟨s, rfl⟩
    rw [hcast, tate_nsmul_lev, _root_.GlobalTheory.HTLat.Tate.lev_pow]

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypotheses
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypotheses
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.SqTop.BotT

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}

theorem nuH_eq (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    nuH G t i j = nuH G μ₀ i j * L.xiH t := by
  simp only [nuH, hL.xi_base, mul_one]
  exact mul_div_right_comm _ _ _

theorem alphaH_eq (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) :
    alphaH L t i j = alphaH L μ₀ i j * L.xiH t := by
  simp only [alphaH, hL.xi_base, mul_one]
  exact mul_right_comm _ _ _

theorem exists_heckeU_nuInv (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    ∃ χ : HeckeU D (botBig D i j + botSmall D i j), (∀ x, χ.f x = (nuH G t i j)⁻¹.1 (finIdl D x)) ∧
      ∀ τ, ((botBig D i j + botSmall D i j : ℕ) : ℤ) ≤ χ.n τ := by
  obtain ⟨χ₀, h₀, hw⟩ := GlobalTheory.BottomNu.exists_heckeU_nu_inv hL G i j
  obtain ⟨ξ, hξ, hn⟩ := GlobalTheory.XiSplit.exists_heckeU_xi hL t
  refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₀ (GlobalTheory.AlphaSplit.invU ξ) (by simp), fun x => ?_, fun τ => ?_⟩
  · rw [GlobalTheory.AlphaSplit.mulU_f, GlobalTheory.AlphaSplit.invU_f, h₀, hξ, nuH_eq hL G t, mul_inv]
    rfl
  · show _ ≤ χ₀.n τ + -ξ.n τ
    rw [hn, neg_zero, add_zero]; exact hw τ

theorem exists_heckeU_alpha (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    ∃ χ : HeckeU D (botSmall D i j), ∀ x, χ.f x = (alphaH L t i j).1 (finIdl D x) := by
  obtain ⟨χ₀, h₀⟩ := GlobalTheory.FunObj.SqNum.exists_heckeU_alphaH hL G i j
  obtain ⟨ξ, hξ, -⟩ := GlobalTheory.XiSplit.exists_heckeU_xi hL t
  refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₀ ξ (by simp), fun x => ?_⟩
  rw [GlobalTheory.AlphaSplit.mulU_f, h₀, hξ, alphaH_eq hL t]
  rfl

theorem pde_ne_q {large₂ : Formalism.BasicNotions.SizeData₂ D} (hR : GlobalTheory.SqTop.Rec large₂) : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
  obtain ⟨⟨P, -, -⟩, -⟩ := hR.size
  have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
  exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩

end GlobalTheory.SqTop.BotT

namespace GlobalTheory.SqTop

theorem botExT_holds (hI : ∀ D, GlobalTheory.NormSum.Inp D) : BotExT := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro δ t0 Q P t i j
  obtain ⟨hq, hq'⟩ := BotT.pde_ne_q hR
  obtain ⟨χν, hν, hw⟩ := BotT.exists_heckeU_nuInv hL G t i j
  obtain ⟨χβ, hβ⟩ := GlobalTheory.FunObj.SqNum.exists_betaInv_heckeU hL G i j
  obtain ⟨χα, hα⟩ := BotT.exists_heckeU_alpha hL G t i j
  obtain ⟨P₁, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_bottomPair_bigMember_twisted_tuple (hI D) hL hq hq' G t P.crv P.pt0 i j χβ hβ χν hν hw
  obtain ⟨P₂, h1', h2', h3', h4', h5'⟩ := GlobalTheory.T.exists_bottomPair_smallMember_twisted_tuple (hI D) hL hq hq' G t P.crv P.pt0 i j χα hα χν hν hw
  exact ⟨P₁, P₂, ⟨⟨h1, h1', h2, h2'.trans h2.symm⟩, h3, h3', h4, h4', ⟨h5, h5'⟩⟩⟩

end GlobalTheory.SqTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistEveryTupleOfCmThetaHypothesesStatement
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomPairsExistEveryTuple_of_cmThetaHypotheses : (∀ D, GlobalTheory.NormSum.Inp D) → BotExT := by
  first | exact @GlobalTheory.SqTop.botExT_holds | exact GlobalTheory.SqTop.botExT_holds | (intros; apply GlobalTheory.SqTop.botExT_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingSplitPrimeGridLocalTensorPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB alpha beta blk)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf HasExp SplitsFully)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.TripleSpaceW (conjSub)
open GlobalTheory.SkewLat (scLat pairLat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_embedding_splitPrime_gridLocalTensorPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (v : HeightOneSpectrum (𝓞 D.host.F)), (∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) →
    ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v → splitPrime τ = w := by
  first | exact @GlobalTheory.LocPlTau.exists_splitPrime_locPl | exact GlobalTheory.LocPlTau.exists_splitPrime_locPl | (intros; apply GlobalTheory.LocPlTau.exists_splitPrime_locPl <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtOverClosureIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory GlobalTheory.ZH
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PushEigen

def ptOverClosureIso (K : Type) [Field K] [IsAlgClosed K] :
    ptOver K (AlgebraicClosure K) ≅ 𝟙_ (Over (Sp K)) := by
  let σ : K ≃+* AlgebraicClosure K :=
    RingEquiv.ofBijective (algebraMap K (AlgebraicClosure K)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hI : IsIso (spMap (algebraMap K (AlgebraicClosure K))) := by
    change IsIso (Spec.map σ.toCommRingCatIso.hom)
    infer_instance
  exact Over.isoMk (asIso (spMap (algebraMap K (AlgebraicClosure K)))) (by
    change spMap _ ≫ 𝟙 _ = spMap _
    exact Category.comp_id _)

def ptClosureEquiv {K : Type} [Field K] [IsAlgClosed K] (B : AbVar K) :
    B.Pt ≃* (𝟙_ (Over (Sp K)) ⟶ B.X) where
  toFun x := (ptOverClosureIso K).inv ≫ x
  invFun y := (ptOverClosureIso K).hom ≫ y
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := MonObj.comp_mul _ x y

end GlobalTheory.PushEigen
end
end
