module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.OpenImmersionCompStructureEqGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingEvaluation
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormIffLevelCoverPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalDarbouxFixesThetaDistribution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingReal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemModelInteriorOfMemAbelianLocusPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemModelInteriorOfMemAbelianLocusPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.AbInterior

theorem mem_interior_of_mem_abLocus : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (S : Scheme.{0}) (f : S ⟶ Y.X) (G : SAB H S), SABMap G Y.t f → ∀ s : S, s ∈ abLocus G.G → f s ∈ (LogKS.interior Y : Set Y.X) := by
  intro E _ _ _ H Dw l Xo c Y S f G m s hs
  rw [LogKS.coe_interior]
  exact (OneArcCompare.mem_abLocus_pullback Y.t.semi m.cart.1 s).2 hs

end GlobalTheory.AbInterior
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemModelInteriorOfMemAbelianLocusPullbackStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_modelInterior_of_mem_abelianLocus_pullback : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (S : Scheme.{0}) (f : S ⟶ Y.X) (G : SAB H S), SABMap G Y.t f → ∀ s : S, s ∈ abLocus G.G → f s ∈ (LogKS.interior Y : Set Y.X) := by
  first | exact @GlobalTheory.AbInterior.mem_interior_of_mem_abLocus | exact GlobalTheory.AbInterior.mem_interior_of_mem_abLocus | (intros; apply GlobalTheory.AbInterior.mem_interior_of_mem_abLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveMapToAbelian
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

namespace GlobalTheory.ConjExpandRational

theorem evaluates_of_unif' {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (hu : R.LUnif) : fw.Evaluates := by
  intro i σ hσ hV
  refine fw.ev i σ hσ hV ?_
  by_contra hne
  have h0 := fw.ev0 i σ hσ hV hne
  have hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0 := fun x => by
    by_contra hx
    have h1 : LinearIndependent D.what₂.LL (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 hx
    have h2 := ((hu i σ).1 1 _ h1).ne_zero 0
    rw [h0] at h2
    exact h2 rfl
  refine hne ⟨0, fun f => ?_⟩
  have hf : f = 0 := (fw.e i).injective (Subtype.ext ((hx _).trans (hx _).symm))
  subst hf
  refine Eq.trans ?_ (GlobalTheory.phiC_zero_rule T hV (wtA (κ i))).symm
  rw [LinearMap.zero_apply, map_zero]
  rfl

end GlobalTheory.ConjExpandRational
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifyingMapUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifyingMapUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegUniq

theorem eq_of_siegPB : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0})
    (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s') (f f' : S ⟶ F.X), f ≫ F.s = s' → f' ≫ F.s = s' →
    SiegPB c F.univ f → SiegPB c F.univ f' → f = f' := by
  intro g n _ _ _ F S s' c f f' hf hf' h₁ h₂
  refine GlobalTheory.hom_ext_of_fromSpecStalk fun x => ?_
  haveI : IsLocalRing (S.presheaf.stalk x) := inferInstance
  obtain ⟨c', hc'⟩ := (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) S (Sp (S.presheaf.stalk x)) s'
    (S.fromSpecStalk x ≫ s') (S.fromSpecStalk x) c rfl).1
  have e : (S.fromSpecStalk x ≫ f) ≫ F.s = (S.fromSpecStalk x ≫ f') ≫ F.s := by
    simp only [Category.assoc, hf, hf']
  exact @SFam.inj g n _ _ _ F (S.presheaf.stalk x) _ this (S.fromSpecStalk x ≫ f) (S.fromSpecStalk x ≫ f') (S.fromSpecStalk x ≫ s') c' e
    (GlobalTheory.SiegelPullComp.pb_comp h₁ hc') (GlobalTheory.SiegelPullComp.pb_comp h₂ hc')

end GlobalTheory.SiegUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifyingMapUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_classifyingMap_unique : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s') (f f' : S ⟶ F.X), f ≫ F.s = s' → f' ≫ F.s = s' → SiegPB c F.univ f → SiegPB c F.univ f' → f = f' := by
  first | exact @GlobalTheory.SiegUniq.eq_of_siegPB | exact GlobalTheory.SiegUniq.eq_of_siegPB | (intros; apply GlobalTheory.SiegUniq.eq_of_siegPB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowNormHasGram
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.GramPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem embedding_eq_or {K : Type} [Field K] (σ₀ : K →+* ℂ) (v : InfinitePlace K) :
    (∀ a, sgAt σ₀ v a = v.embedding a) ∨ ∀ a, sgAt σ₀ v a = starRingEnd ℂ (v.embedding a) := by
  by_cases hv : v = InfinitePlace.mk σ₀
  · rw [sgAt_mk σ₀ hv]
    rcases InfinitePlace.embedding_mk_eq σ₀ with h | h
    · exact Or.inl fun a => by rw [hv, h]
    · exact Or.inr fun a => by rw [hv, h]; simp
  · exact Or.inl fun a => by simp [sgAt, hv]

theorem hasGram_of_unif {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hU : R.LUnif) (i : Fin D.R.m) :
    HasGram (nrmR R i) := by
  refine GlobalTheory.HSApp.hasGram_of_inner _ _ _ fun v => ?_
  refine ⟨(R.HW i (sgAt D.what₂.embLL v)).H, inferInstance, inferInstance,
    ((R.FW i).j (sgAt D.what₂.embLL v)).toAddMonoidHom, ?_, fun x => ?_, fun n e he => (hU i _).1 n e he⟩
  · refine (embedding_eq_or D.what₂.embLL v).imp (fun h a x => ?_) fun h a x => ?_
    · rw [← h]; exact map_smulₛₗ ((R.FW i).j (sgAt D.what₂.embLL v)) a x
    · rw [← h]; exact map_smulₛₗ ((R.FW i).j (sgAt D.what₂.embLL v)) a x
  · unfold nrmR
    rw [InfinitePlace.mk_embedding]
    rfl

end GlobalTheory.CovTop.GramPt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointOfCompactFlagSpaceOpenPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointOfCompactFlagSpaceOpenPart
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.CompHS

theorem exists_frPt_of_flagOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (K : Type) [Field K] (z : Sp K ⟶ X.YY), ⊤ ≤ z ⁻¹ᵁ flagOpen X → ∃ io : c.F →+* K, letI := io.toAlgebra; ∃ P : FrPt Xo c K, X.ptY P = z := by
  intro E _ _ _ H Dw l Xo c Y X K _ z hO
  obtain ⟨a, h⟩ := GlobalTheory.CompHS.exists_chartFr z hO
  obtain ⟨k, hz⟩ := GlobalTheory.FlagMod.exists_chart_of_isLocalRing X.F.cover z
  obtain ⟨Q, hQ⟩ := h k hz
  refine ⟨algebraMap c.F K, ?_⟩
  have e : (algebraMap c.F K).toAlgebra = a := Algebra.algebra_ext _ _ fun _ => rfl
  rw [e]
  exact ⟨Q, (FlagCover.eq_ptY hQ.lies).symm⟩

end GlobalTheory.CompHS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointOfCompactFlagSpaceOpenPartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedPoint_of_compactFlagSpaceOpenPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (K : Type) [Field K] (z : Sp K ⟶ X.YY), ⊤ ≤ z ⁻¹ᵁ flagOpen X → ∃ io : c.F →+* K, letI := io.toAlgebra; ∃ P : FrPt Xo c K, X.ptY P = z := by
  first | exact @GlobalTheory.CompHS.exists_frPt_of_flagOpen | exact GlobalTheory.CompHS.exists_frPt_of_flagOpen | (intros; apply GlobalTheory.CompHS.exists_frPt_of_flagOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsFiniteType
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.AbelianLimit

theorem abelianScheme_descends_to_fg_subring_anyDim :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A →
    ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧
      Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  intro R _ A _ F hA
  have := hA.comm
  have := hA.proper
  obtain ⟨k, A₀, _, _, φ₀, hF, hk, _, _, _, h₀⟩ :=
    smooth_grpScheme_descends_to_fg_subring R A F hA.smooth inferInstance inferInstance
  have : IsNoetherianRing k := Algebra.FiniteType.isNoetherianRing ℤ k
  have h₁ : IsPullback φ₀ A.hom A₀.hom (spMap (algebraMap k R)) := h₀.1
  have : UniversallyClosed (pullback.snd A₀.hom (spMap (algebraMap k R))) := by
    rw [← h₁.isoPullback_inv_snd]
    infer_instance
  obtain ⟨s, hs⟩ := ProperLimit.exists_finset_isProper k R A₀.hom
  let S : Subalgebra k R := Algebra.adjoin k (s : Set R)
  let t : Sp S.toSubring ⟶ Sp k := spMap (algebraMap k S)
  have e : spMap S.toSubring.subtype ≫ t = spMap k.subtype := Spread.spMap_algHom_comp S.val
  obtain ⟨φ, hφ⟩ := GoodVal.exists_isGrpPullback_of_comp A₀ t (spMap S.toSubring.subtype) (e ▸ h₀)
  have : Smooth ((Over.pullback t).obj A₀).hom := inferInstanceAs (Smooth (pullback.snd A₀.hom t))
  have : IsProper ((Over.pullback t).obj A₀).hom := hs
  have hd : IsDominant (spMap S.toSubring.subtype) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.toSubring.subtype).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
      exact bot_le)⟩
  exact ⟨S.toSubring, (Over.pullback t).obj A₀, inferInstance, φ, fun x hx => S.algebraMap_mem ⟨x, hF hx⟩,
    SpreadGroup.finiteType_of_fg hk (Subalgebra.fg_adjoin_finset s), isAbelianScheme_of_isDominant hφ hA, hφ⟩

end GlobalTheory.AbelianLimit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCuspFormPullbackGoodCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCuspFormPullbackGoodCover
open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop

namespace GlobalTheory.CoverPull

theorem cusp_pullback_existsUnique : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), ∃! g, g ∈ Y.V (wtZ a n) ∧ Y.Pull f g := by
  intro D T j Y e o hT hj hG hu hm a n hD f hf
  have hL := GlobalTheory.LevGeo.laws_core D T j hT hj
  obtain ⟨hL', hbc⟩ := GlobalTheory.T.moduliLaws_coefficientFieldChange D j _ _ _ _ _ Y.c' Y.hle _ _ hL
  obtain ⟨hf', -⟩ := hbc a n hD ⟨f, hf⟩
  obtain ⟨hL₂, -, hP⟩ := GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hT hj hG hu hm
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q ∧ 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  rw [cuspW_wtZ] at hf hf'
  have hs := cusp_le_sec _ _ _ a n hf
  have hs' := cusp_le_sec _ _ _ a n hf'
  obtain ⟨g, ⟨hg, hgP⟩, huniq⟩ := (GlobalTheory.CoverSec.section_pullback_existsUnique _ _ _ _ _ _ Y.d hpq.2 hG.lev.1
    (Or.inl ⟨hpq.1, hL.levA⟩) a n).1 _ hs'
  refine ⟨g, ⟨?_, (hP a n f hs g).2 hgP⟩, fun g' hg' => huniq g' ⟨?_, (hP a n f hs g').1 hg'.2⟩⟩
  · rw [Deep.V, cuspW_wtZ]
    exact (GlobalTheory.T.cuspForm_iff_levelCover_pullback D j _ _ _ _ _ _ _ Y.d _ _ hL' hL₂ hG.lev.1 a n hD hD.2 _ hs' g hg hgP).2 hf'
  · have h := hg'.1
    rw [Deep.V, cuspW_wtZ] at h
    exact cusp_le_sec _ _ _ a n h

end GlobalTheory.CoverPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCuspFormPullbackGoodCoverStatement
open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_cuspForm_pullback_goodCover : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), ∃! g, g ∈ Y.V (wtZ a n) ∧ Y.Pull f g := by
  first | exact @GlobalTheory.CoverPull.cusp_pullback_existsUnique | exact GlobalTheory.CoverPull.cusp_pullback_existsUnique | (intros; apply GlobalTheory.CoverPull.cusp_pullback_existsUnique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeOfSig
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaRatPair

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

theorem det_ne_of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r s : ℕ}
    (B : Base F E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ w, HasSig (J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_of_hasSig (h w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [← e, h0, map_zero]

theorem det_ne_of_sig' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r s : ℕ}
    (B : Base F E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ w, HasSig (Complex.I • J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_of_hasSig (h w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

end GlobalTheory.ThetaRatPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLatticeFinitelyGenerated
set_option synthInstance.maxHeartbeats 400000
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.LatAllFG

theorem fg_latOf_congr {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] {C C' : Submodule K R} (hC : C = C')
    (Vs : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (h : (latOf C Vs hV).FG) : (latOf C' Vs hV).FG := by
  subst hC; exact h

theorem latW_fg {D : D7} (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (hn : 0 < w.n) :
    (latW (T.U j) (wtZ (wtA w) w.n)).FG := by
  have h := (GlobalTheory.SupFull.fullAt_of_pins D T.toCore hT.pins j hj (hT.unf j hj _ T.good_σ₀) w hn).1
  unfold GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation.supLat GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation.latIn at h
  have h2 := Submodule.fg_of_fg_map_injective _ Subtype.val_injective h
  exact fg_latOf_congr (cuspW_wtZ (Xo := T.Q.Xo j) (c := T.Q.c) (U := T.U j) (wtA w) w.n).symm _ _ h2

theorem fg_span_image {K L V W : Type} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module L W] [Module (𝓞 L) W] [IsScalarTower (𝓞 L) L W]
    (ι : V →ₛₗ[algebraMap K L] W) (M : Submodule (𝓞 K) V) (hM : M.FG) :
    (Submodule.span (𝓞 L) (ι '' (M : Set V))).FG := by
  classical
  obtain ⟨s, hs⟩ := hM
  refine ⟨s.image ι, le_antisymm ?_ ?_⟩
  · rw [Finset.coe_image]
    exact Submodule.span_mono (Set.image_mono (hs ▸ Submodule.subset_span))
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      have e : ι (c • y) = (RingOfIntegers.mapRingHom (algebraMap K L) c) • ι y := by
        rw [← algebraMap_smul K c y, ι.map_smulₛₗ, ← algebraMap_smul L (RingOfIntegers.mapRingHom (algebraMap K L) c) (ι y)]
        rfl
      rw [e]
      exact Submodule.smul_mem _ _ hy

end GlobalTheory.CovTop.LatAllFG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefLatticeIndepCoefMapProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefLatticeIndepCoefMapProof
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.CoefIndepProof

theorem coefIndep : GlobalTheory.BaseCmp.CoefIndep := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i c0L hc h w hw
  obtain ⟨gramR', c0R', c0L', hT', P, hP, rfl⟩ := hw
  obtain ⟨gramR, c0R, hT⟩ := hc
  obtain ⟨c, ⟨γ, k, e⟩, -⟩ := (R.B.L i A.μ0).pres.reps (fin (Vc D i) h)
  have hst : Formalism.UG.bc (swapAE D) ((k : Bridge.Gf (Vc D i)) : GL (Fin (Vc D i).rank) _) ∈ St (R.βV i) :=
    Formalism.L2.DIV.parLev_St k.2.1
  obtain ⟨γE, hγ, hl⟩ := GlobalTheory.HLatMove.hLat_rat_mul_stab (Vc D i) (R.βV i) (R.ΛV i) (hR.lev.βV i) γ
  rw [e, hl _ _ hst, Formalism.L2.Col.nabAtr_gmap, MulEquiv.apply_symm_apply] at hP ⊢
  obtain ⟨P', hP', rfl⟩ := hP
  obtain ⟨e', -, h2', -, h4', -⟩ := hT'.coefL i A.μ0
  obtain ⟨e1, -, h2, -, h4, -⟩ := hT.coefL i A.μ0
  rw [← h4' c] at hP'
  obtain ⟨y, hy, rfl⟩ := hP'
  refine ⟨rhoVr (labLL D) (lamV D i) γE (e1 y), ⟨e1 y, ?_, rfl⟩, ?_⟩
  · rw [← h4 c]; exact ⟨y, hy, rfl⟩
  · have a1 := (hT'.mapL i).1 γ γE hγ (e' y)
    have a2 := (hT.mapL i).1 γ γE hγ (e1 y)
    change c0L' i (rhoVr (labLL D) (lamV D i) γE (e' y)) = c0L i (rhoVr (labLL D) (lamV D i) γE (e1 y))
    rw [a1, ← h2', h2]
    exact a2.symm

end GlobalTheory.CoefIndepProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefLatticeIndepCoefMapProofStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefLattice_indep_coefMap_proof : GlobalTheory.BaseCmp.CoefIndep := by
  first | exact @GlobalTheory.CoefIndepProof.coefIndep | exact GlobalTheory.CoefIndepProof.coefIndep | (intros; apply GlobalTheory.CoefIndepProof.coefIndep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationSectionFirstPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.MBLow.TrSec

variable {S : Scheme.{0}} (P : PolAV S)

lemma chart_le (j : Fin 1 → P.L.ι) :
    (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S)).U j ≤ (snd (baseOver S) P.A).left ⁻¹ᵁ P.L.U (j 0) :=
  LB.wchart_le P.L _ j 0

def thSec (s : P.L.Sec) : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S)) where
  f j := ReciprocityTheory.ChartRestriction.G.DVR.rs (chart_le P j) (((snd (baseOver S) P.A).left.app (P.L.U (j 0))).hom (s.f (j 0)))
  compat i j := by
    refine ReciprocityTheory.ChartRestriction.G.DVR.app_compat_generic (snd (baseOver S) P.A).left (chart_le P i) (chart_le P j)
      (s.f (i 0)) (s.f (j 0)) (P.L.g (i 0) (j 0)) (s.compat _ _) _ ?_
    simp only [LPow, LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
    rfl

lemma projectionPullbackSectionBaseProduct_isInverseImage (s : P.L.Sec) : IsPolAVSectionInverseImage P (baseOver S) s (thSec P s) := by
  intro i h
  rfl

lemma snd_inv (p : P.A.left) : (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) = p := by
  have e : (λ_ P.A).inv ≫ snd (baseOver S) P.A = 𝟙 P.A := (λ_ P.A).inv_hom_id
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e]
  rfl

lemma nonzero_thSec (s : P.L.Sec) (p : P.A.left) (hp : p ∈ nonzeroLocus s) :
    (λ_ P.A).inv.left.base p ∈ nonzeroLocus (thSec P s) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hp
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k, ?_⟩
  have hq : (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) = p := snd_inv P p
  show _ ∈ (baseOver S ⊗ P.A).left.basicOpen
    (((baseOver S ⊗ P.A).left.presheaf.map (homOfLE (chart_le P (fun _ => k))).op).hom
      (((snd (baseOver S) P.A).left.app (P.L.U k)).hom (s.f k)))
  rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
  refine ⟨?_, ?_⟩
  · show _ ∈ LB.wchart P.L _ _
    refine Set.mem_iInter.2 fun _ => ?_
    show (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) ∈ (P.L.U k : Set P.A.left)
    rw [hq]; exact P.A.left.basicOpen_le _ hk
  · show (snd (baseOver S) P.A).left.base ((λ_ P.A).inv.left.base p) ∈ P.A.left.basicOpen (s.f k)
    rw [hq]; exact hk

end GlobalTheory.MBLow.TrSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianMapModelOfIntegralFramedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianMapModelOfIntegralFramedPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sabMap_model_of_integral_frPt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y : FrPt Xo c T.Fr) (x : Sp T.V ⟶ Y.X), spMap (algebraMap T.V T.Fr) ≫ x = GlobalTheory.FlagMod.frX y ≫ Y.j → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t y.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), ∃ (ψ : SABMap G Y.t x) (ρ : t'.G.left ⟶ Y.oF.t.G.left), ρ ≫ Y.m0.toSABMap.φ = m1.φ ∧ ρ ≫ Y.oF.t.G.hom = t'.G.hom ≫ GlobalTheory.FlagMod.frX y ∧ ρ ≫ Y.m.φ = m2.φ ≫ ψ.φ := by
  intro E _ _ _ H Dw l Xo c O _ β Y T io
  letI := io.toAlgebra
  intro y x hx G t' m1 m2
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → ∀ m : SABMap s' s f,
      ∃ m' : SABMap s' s g, m'.φ = m.φ := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m, rfl⟩
  obtain ⟨m1', hm1⟩ := tr (GlobalTheory.FlagMod.frX_fst y).symm m1
  obtain ⟨ρ, hρ⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ Y.m0.toSABMap m1'
  obtain ⟨a, ha⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m ρ
  obtain ⟨a', ha'⟩ := tr hx.symm a
  obtain ⟨G₂, ⟨pull⟩⟩ : ∃ G₂ : SAB H (Sp T.V), Nonempty (SABMap G₂ Y.t x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull x Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨c2, hc2⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ pull a'
  obtain ⟨k, n, hk, hn⟩ := sab_extensions_iso E H Dw l Xo T.V T.Fr y.x G G₂ t' t' m1 m2 m1 c2
  have hk1 : k.φ = 𝟙 _ := by
    apply m1.cart.1.hom_ext
    · rw [Category.id_comp]; exact hk
    · rw [Category.id_comp]; exact k.cart.1.w.trans (Category.comp_id _)
  obtain ⟨b, hb⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ pull n
  obtain ⟨ψ, hψ⟩ := tr (Category.id_comp x) b
  refine ⟨ψ, ρ.φ, by rw [← hρ, hm1], ρ.cart.1.w, ?_⟩
  rw [← ha, ← ha', hc2, hψ, hb, ← Category.assoc, hn, hk1, Category.id_comp]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianMapModelOfIntegralFramedPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianMap_model_of_integralFramedPoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra; ∀ (y : FrPt Xo c T.Fr) (x : Sp T.V ⟶ Y.X), spMap (algebraMap T.V T.Fr) ≫ x = GlobalTheory.FlagMod.frX y ≫ Y.j → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t y.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), ∃ (ψ : SABMap G Y.t x) (ρ : t'.G.left ⟶ Y.oF.t.G.left), ρ ≫ Y.m0.toSABMap.φ = m1.φ ∧ ρ ≫ Y.oF.t.G.hom = t'.G.hom ≫ GlobalTheory.FlagMod.frX y ∧ ρ ≫ Y.m.φ = m2.φ ≫ ψ.φ := by
  first | exact @GlobalTheory.exists_sabMap_model_of_integral_frPt | exact GlobalTheory.exists_sabMap_model_of_integral_frPt | (intros; apply GlobalTheory.exists_sabMap_model_of_integral_frPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentLinearCombinationIsTangent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.SecJet GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.SecJet.TanComb

variable {R : Type} [CommRing R]

theorem zeroPt_w : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ (epsR R).hom = (𝟙_ (Over (Sp R))).hom := by
  show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [← Spec.map_id]
  congr 1

def zeroPt : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) zeroPt_w

variable {G : Over (Sp R)} [GrpObj G]

theorem isTangent_iff (v : epsR R ⟶ G) : IsTangent v ↔ zeroPt ≫ v = 1 := by
  have h1 : (1 : 𝟙_ (Over (Sp R)) ⟶ G) = η[G] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [h1, IsTangent]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    simpa [zeroPt] using h
  · intro h
    simpa [zeroPt] using congrArg (fun q => q.left) h

theorem zeroPt_epsScale (c : R) : zeroPt ≫ epsScale R c = zeroPt := by
  apply Over.OverMorphism.ext
  show spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (epsScaleR c) = spMap (TrivSqZeroExt.fstHom R R R).toRingHom
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro r
  simp [epsScaleR]

theorem zeroPt_prod (l : List (epsR R ⟶ G)) (hl : ∀ x ∈ l, zeroPt ≫ x = 1) : zeroPt ≫ l.prod = 1 := by
  induction l with
  | nil =>
    rw [List.prod_nil, Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (zeroPt ≫ toUnit _) (toUnit _)]
  | cons a l ih =>
    rw [List.prod_cons, MonObj.comp_mul, hl a (List.mem_cons_self ..), ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)), _root_.mul_one]

end GlobalTheory.SecJet.TanComb

namespace GlobalTheory.SecJet

theorem isTangent_tanComb (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (m : ℕ) (v : Fin m → (epsR R ⟶ G))
    (c : Fin m → R) : (∀ i, IsTangent (v i)) → IsTangent (tanComb c v) := by
  intro hv
  rw [TanComb.isTangent_iff, tanComb]
  refine TanComb.zeroPt_prod _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  rw [← Category.assoc, TanComb.zeroPt_epsScale, ← TanComb.isTangent_iff]
  exact hv i

end GlobalTheory.SecJet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosCombinationSmoothConeSymmIntForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosCombinationSmoothConeSymmIntForm
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.ConeInterior

section Help

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X]

theorem exists_nat_comb {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCone bar φ γ)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i)
    (h : toReal β = ∑ i, c i • toReal (γ i)) : ∃ n : Fin m → ℕ, β = ∑ i, n i • γ i := by
  classical
  obtain ⟨f, hf⟩ := hγ.basis.exists_dual
  have hz : ∀ i, c i = (f i ⟨β, hβ⟩ : ℤ) := fun i => by
    have h0 : ∑ o : Option (Fin m), (Option.elim o (-1) c) • toReal ((balForms bar X).subtype
        (Option.elim o (⟨β, hβ⟩ : balForms bar X) fun k => ⟨γ k, hγ.mem k⟩)) = 0 := by
      rw [Fintype.sum_option]
      simp only [Option.elim_none, Option.elim_some, Submodule.subtype_apply, h, neg_one_smul, neg_add_cancel]
    have := sum_mul_eq_zero_of_sum_toReal Subtype.val_injective (f i) h0
    rw [Fintype.sum_option] at this
    simp only [Option.elim_none, Option.elim_some, hf] at this
    simp at this
    linarith
  have hn : ∀ i, ∃ n : ℕ, c i = n := fun i => by
    have h1 : (0 : ℤ) ≤ f i ⟨β, hβ⟩ := by exact_mod_cast (hz i ▸ hc i : (0 : ℝ) ≤ (f i ⟨β, hβ⟩ : ℤ))
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h1
    exact ⟨n, by rw [hz i, hn, Int.cast_natCast]⟩
  choose n hn using hn
  refine ⟨n, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ h a b
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hn, nsmul_eq_mul] at this ⊢
  exact_mod_cast this

theorem exists_pos_comb (hP : IsPolFanOn bar φ X) {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X)
    (hp : toReal β ∈ psdCone (bar := bar) (X := X)) :
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (cf : Fin m → ℕ),
      IsCone bar φ γ ∧ (∀ j, 0 < cf j) ∧ β = ∑ j, cf j • γ j := by
  classical
  obtain ⟨m, γ, c, hγ, hc, h⟩ := hP.cover _ hp
  obtain ⟨n, hn⟩ := exists_nat_comb hγ hβ hc h
  let S : Finset (Fin m) := Finset.univ.filter fun i => 0 < n i
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hs : Finset.univ.map s = S := Finset.map_orderEmbOfFin_univ S rfl
  refine ⟨S.card, fun i => γ (s i), fun i => n (s i), hP.face _ _ γ s hγ, fun j => ?_, ?_⟩
  · exact (Finset.mem_filter.1 (S.orderEmbOfFin_mem rfl j)).2
  · rw [hn, ← Finset.sum_map Finset.univ s fun i => n i • γ i, hs]
    refine (Finset.sum_subset (Finset.subset_univ S) fun i _ hi => ?_).symm
    have : n i = 0 := by simpa [S] using hi
    rw [this, zero_smul]

end Help

theorem exists_pos_comb_int : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ r : ℕ, r ≤ g → ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) (cf : Fin m → ℕ), IsCone id φ γ ∧ (∀ j, 0 < cf j) ∧ b = ∑ j, cf j • γ j := by
  intro g φ hφ r hr b hb hp
  exact exists_pos_comb (hφ (Fin r → ℤ) (by simpa using hr)) (mem_balForms_int.2 hb) hp

end GlobalTheory.ConeInterior
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosCombinationSmoothConeSymmIntFormStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_combination_smoothCone_symmIntForm : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ r : ℕ, r ≤ g → ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) → ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ (Fin r → ℤ)) (cf : Fin m → ℕ), IsCone id φ γ ∧ (∀ j, 0 < cf j) ∧ b = ∑ j, cf j • γ j := by
  first | exact @GlobalTheory.ConeInterior.exists_pos_comb_int | exact GlobalTheory.ConeInterior.exists_pos_comb_int | (intros; apply GlobalTheory.ConeInterior.exists_pos_comb_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelChangeMap
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel

namespace GlobalTheory.LevelMapBase

theorem levelMap_coeff_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (hle : c.F ≤ c'.F),
    1 ≤ Dw.p + Dw.q → l.Dvd l' →
    ∃ (r : Xo'.XF c' ⟶ Xo.XF c)
      (h : r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
        pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ spMap (IntermediateField.inclusion hle).toRingHom)
      (r₀ : Xo'.X ⟶ Xo.X) (_ : SABMap Xo'.univ.t Xo.univ.t r₀),
      r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r₀ ∧ IsFinite (pullback.lift r _ h) ∧ Etale (pullback.lift r _ h) ∧
        Surjective (pullback.lift r _ h) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' hle hpq hd
  obtain ⟨r₀, jK, m, hk, -, -, -, -, hc⟩ := (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H Dw hpq).1 l l' Xo Xo' hd
  have hle₁ : KA l ≤ c'.F := fun x hx => by
    have := c'.le (jK ⟨x, hx⟩).2
    rwa [hk] at this
  let c₁ : Coeff l :=
    { F := c'.F
      fin := c'.fin
      conj := c'.conj
      zeta_mem := by
        obtain ⟨e, he⟩ := GlobalTheory.LevelExist.zeta_eq_pow_of_dvd (a := l.M') (GlobalTheory.LevelExist.M'_pos l')
          (Nat.lcm_dvd (hd.1.trans (Nat.dvd_lcm_left _ _)) (hd.2.2.trans (Nat.dvd_lcm_right _ _)) : l.M' ∣ l'.M')
        rw [he]
        exact pow_mem c'.zeta_mem e
      le := hle₁ }
  obtain ⟨rF, e1, e2, f1, f2, f3, -⟩ := hc c₁ c' rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c'.F)).toRingHom = 𝟙 (Sp c'.F) := by
    rw [← Spec.map_id]
    rfl
  have e2' : rF ≫ pullback.snd _ _ = pullback.snd _ _ := e2.trans ((congrArg _ hid).trans (Category.comp_id _))
  have hi : spMap (IntermediateField.inclusion hle).toRingHom ≫ spMap (IntermediateField.inclusion c.le).toRingHom =
      spMap (IntermediateField.inclusion c₁.le).toRingHom := by
    rw [← Spec.map_comp]
    rfl
  let b : Xo.XF c₁ ⟶ Xo.XF c :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom)
      (by rw [Category.assoc, hi, pullback.condition])
  have hb1 : b ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hb2 : b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom :=
    pullback.lift_snd _ _ _
  have hp : IsPullback b (pullback.snd _ _) (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
      (spMap (IntermediateField.inclusion hle).toRingHom) := by
    refine IsPullback.of_right ?_ hb2 (IsPullback.of_hasPullback _ _)
    rw [hb1, hi]
    exact IsPullback.of_hasPullback _ _
  have h : (rF ≫ b) ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
      pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫
        spMap (IntermediateField.inclusion hle).toRingHom := by
    rw [Category.assoc, hb2, reassoc_of% e2']
  have hlift : pullback.lift (rF ≫ b) _ h = rF ≫ hp.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, e2']
  refine ⟨rF ≫ b, h, r₀, m, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hb1, e1]
  · rw [hlift]; infer_instance
  · rw [hlift]; infer_instance
  · rw [hlift]; infer_instance

end GlobalTheory.LevelMapBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelTypePlaceThetaVectorLatticeFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelTypePlaceThetaVectorLatticeFixed
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerTypeVec

theorem typeVec_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg → IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) fg ∧ ∀ u ∈ latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i), (IsHalf eQ u ∨ IsHalf (cA D eQ) u) → heisO R.ψ (Vc D i) (Wc D i) u fg = fg := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _ i _ ξ χ ξR Q ω φ hK hQt eg eQ fg heg heQ hfg
  obtain ⟨t, hQt⟩ := hQt
  have sdV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sdW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hvac := hK.vecOf.1
  have hψ : IsStdChar D R.ψ (-1) := hvac.1
  have hth0 : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := hvac.2.theta
  have hlat := hvac.2.lat
  have fixQ := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac R.ψ hlat heQ
  have hQpl := hK.pl
  have hdisj : Disjoint R.Pg (R.Q t) := Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hC.lev t
  obtain ⟨⟨esg, hesg, hegs⟩, -⟩ := heg
  obtain ⟨⟨esQ, hesQ, heQs⟩, -⟩ := heQ
  have h1 : eQ * eg = 0 := by
    rw [hegs, heQs, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun P' hP' => Finset.sum_eq_zero fun P hP => ?_
    exact Formalism.IndefR.Fin.idem_orth ((hQpl P' hP').2 P' hP') (hesQ P' hP') (hesg P hP)
      (fun h => Finset.disjoint_left.1 hdisj hP (h ▸ hQt hP'))
  have h2 : eQ * cA D eg = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hegs, heQs, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun P' hP' => Finset.sum_eq_zero fun P hP => ?_
    refine Formalism.IndefR.Fin.idem_orth_conj ((hQpl P' hP').2 P' hP') (hesQ P' hP') (hesg P hP) fun hc => ?_
    obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hQpl P' hP'
    obtain ⟨k, hk⟩ := (hC.lev.Pg P).1 hP
    exact Formalism.IndefR.Fin.not_two_primes P.isPrime.ne_top hq (D.host.g_prime k) (hqg k)
      (Formalism.IndefR.Fin.nat_mem_of_conj hc (Formalism.IndefR.Fin.char_mem hq hcard))
      (Formalism.IndefR.Fin.g_mem_of_div R.toLevCh.C hk)
  have h3 : eg * cA D eQ = 0 := by
    have := congrArg (cA D) h2
    rwa [map_mul, Formalism.L2.Theta.cA_cA, map_zero, mul_comm] at this
  have h4 : cA D eg * cA D eQ = 0 := by rw [← map_mul, mul_comm, h1, map_zero]
  refine ⟨sdV, sdW, GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hvac.2.inf hfg hth0, fun u hu hh => ?_⟩
  refine GlobalTheory.VacFix.heisO_fix_of_isThetaAt D R.ψ _ _ (cA D eg) _ 1 (R.vacP i) _ fg u hfg
    (fun a b => ?_) (fun a b => ?_) (fixQ u hu hh)
  · rcases hh with hh | hh
    · rw [← hh a b, ← mul_assoc, mul_comm (cA D eg), h2, zero_mul]
    · rw [← hh a b, ← mul_assoc, h4, zero_mul]
  · rw [Formalism.L2.Theta.cA_cA]
    rcases hh with hh | hh
    · rw [← hh a b, ← mul_assoc, mul_comm eg, h1, zero_mul]
    · rw [← hh a b, ← mul_assoc, h3, zero_mul]

end GlobalTheory.KerTypeVec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelTypePlaceThetaVectorLatticeFixedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameKernel_typePlaceThetaVector_latticeFixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg → IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) fg ∧ ∀ u ∈ latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i), (IsHalf eQ u ∨ IsHalf (cA D eQ) u) → heisO R.ψ (Vc D i) (Wc D i) u fg = fg := by
  first | exact @GlobalTheory.KerTypeVec.typeVec_fixed | exact GlobalTheory.KerTypeVec.typeVec_fixed | (intros; apply GlobalTheory.KerTypeVec.typeVec_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigValD
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TanExp

def termV {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (J : (Sp (DualNumber R) ⟶ D.P.A.left) → D.P.L.ι)
    (g : GtPt D (epsR R)) {k : ℕ} {α : D.X} (f : D.SecB k α) : DualNumber R :=
  valR g.b.left (LB.wchart D.P.L (D.famφB α) fun i => J (g.b.left ≫ D.famφB α i))
      (f.f fun i => J (g.b.left ≫ D.famφB α i)) *
    valR (𝟙 (Sp (DualNumber R))) (LB.wchart D.P.L (DegPre.gtφT D (epsR R) g.b α) fun i => J (DegPre.gtφT D (epsR R) g.b α i))
      ((g.s α).s fun i => J (DegPre.gtφT D (epsR R) g.b α i)).val

def rigVal {S : Type} [CommRing S] {G : Over (Sp S)} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (j : L.L.ι) : S :=
  valR (𝟙 (Sp S)) ((L.L.pull (eSec G)).U fun _ => j) (L.rig.s fun _ => j).val

def rigValD {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (j : D.P.L.ι) : R :=
  valR (𝟙 (Sp R)) (LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) fun _ => j) (D.rig.s fun _ => j).val

end GlobalTheory.MBLow.TanExp

end
end
