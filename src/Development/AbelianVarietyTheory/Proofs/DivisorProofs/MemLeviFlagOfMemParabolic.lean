module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
public import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualFullLatticeShared

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLeviFlagOfMemParabolic
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodProjLevel

section Act

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G]

theorem mem_levi_flag_of_mem_parabolic (P : LevelP L.Pg L.r ℂ) {k : GA D V} (hk : k ∈ levG V β (flag1L L)) :
    k ∈ levG V β (withP L P) ∧ levChi V β (withP L P) k = levChi V β (flag1L L) k := by
  have h1 : rTup β L (finE V k) = 1 := by
    have : rTup β L (finE V k) ∈ (⊥ : Subgroup (G0 L.Pg L.r)) := hk.2.2
    exact Subgroup.mem_bot.1 this
  refine ⟨⟨hk.1, hk.2.1, ?_⟩, ?_⟩
  · show rTup β L (finE V k) ∈ P.H
    rw [h1]; exact P.H.one_mem
  · unfold levChi
    rw [levFn_withP, h1, blockDiagonalExtendByOnePrimeField_one, one_mul, levFn_flag1]

theorem isPLevel_of_hasType (hL : LiftsExist V β L) {P : LevelP L.Pg L.r ℂ} {F : GA D V → ℂ}
    (hF : HasType V β (withP L P) F) : IsPLevel V β L P F := by
  have h1 : HasType V β (flag1L L) F := fun k hk h => by
    rw [hF k (mem_levi_flag_of_mem_parabolic P hk).1, (mem_levi_flag_of_mem_parabolic P hk).2]
  refine ⟨h1, fun p => ?_⟩
  obtain ⟨κ, hκ⟩ := hL p.1
  have hp : rTup β L (finE V κ) ∈ P.H := by rw [hκ.2.2]; exact p.2
  have hm : κ ∈ levG V β (withP L P) := ⟨hκ.1, hκ.2.1, hp⟩
  have hc : levChi V β (withP L P) κ = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) κ := by
    unfold levChi
    rw [levFn_withP, hκ.2.2, extendOne_of_mem _ p.2, Units.val_mul]
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  funext h
  rw [level_action_spec h1 ⟨κ, hκ⟩ κ hκ h, hF κ hm, hc]
  field_simp

theorem postOn_actL_mem (g0 : G0 L.Pg L.r) {X : MMap M}
    (hT : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    postOn M (actL V β L g0) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
  have hU : ∀ v, postOn M (actL V β L g0) X v = actG0 V β L g0 (X v) := fun _ => rfl
  by_cases hex : ∃ κ, IsLevelLift V β L g0 κ
  · have hκ := hex.choose_spec
    have e : postOn M (actL V β L g0) X = (levChi V β (flagL L) hex.choose)⁻¹ • heckeOn M {hex.choose} X := by
      ext v g
      rw [hU, actG0, dite_eq_left hex]
      simp [heckeOn, postOn_apply, heckeLin_apply]
    rw [e]
    refine Submodule.smul_mem _ _ ?_
    rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
    refine GlobalTheory.SphericalOps.isMultMap_heckeOn hT (fun k hk => ?_) fun v k hk g => ?_
    · rw [Finset.mem_singleton.1 hk]
      exact hκ.1
    · obtain ⟨h1, h2⟩ := GlobalTheory.FlagAction.conj_mem_flag1 hκ hk
      simp only [heckeLin_apply, Finset.sum_singleton]
      rw [← h2, ← hT.lev v _ h1]
      group
  · have e : postOn M (actL V β L g0) X = 0 := by
      ext v g
      rw [hU, actG0, dite_eq_right hex]
      rfl
    rw [e]
    exact zero_mem _

theorem postOn_gaL_mem_goodPart (hL : LiftsExist V β L) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)
    (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g)
    (hcomm : ∀ g F, HasType V β (flag1L L) F →
      gaL V β L eG c (actL V β L (eG g) F) = actL V β L (eG g) (gaL V β L eG c F))
    (P : LevelP L.Pg L.r ℂ) {X : MMap M}
    (hX : X ∈ Mult θ M (levG V β (withP L P) : Set (GA D V)) (levChi V β (withP L P))) :
    postOn M (gaL V β L eG c) X ∈
      goodPart θ M (levG V β (withP L P) : Set (GA D V)) (levChi V β (withP L P)) (gaL V β L eG c) := by
  have hX1 : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) :=
    GlobalTheory.ProjectedLift.mult_mono (fun k hk => mem_levi_flag_of_mem_parabolic P hk) hX
  have hY : postOn M (gaL V β L eG c) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
    have e : postOn M (gaL V β L eG c) X = ∑ g, c g • postOn M (actL V β L (eG g)) X := by
      ext v h
      simp [gaL, postOn_apply]
    rw [e]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (postOn_actL_mem _ hX1)
  rw [mem_goodPart]
  refine ⟨?_, fun v => GlobalTheory.ProjectedLift.gaL_gaL hL eG c hc (GlobalTheory.hasType_of_mem_mult θ M β _ X hX1 v)⟩
  have hY' := (GlobalTheory.MultMem.mem_mult_iff ..).1 hY
  refine (GlobalTheory.MultMem.mem_mult_iff ..).2 ⟨hY'.aut, hY'.cusp, fun v => ?_, hY'.equiv, hY'.cont⟩
  have hP := isPLevel_of_hasType hL (GlobalTheory.hasType_of_mem_mult θ M β _ X hX v)
  have hQ : IsPLevel V β L P (gaL V β L eG c (X v)) := by
    refine ⟨hY'.lev v, fun p => ?_⟩
    have e1 : actL V β L p.1 (X v) = ((P.chi p : ℂˣ) : ℂ) • X v := hP.2 p
    have e2 := hcomm (eG.symm p.1) _ hP.1
    rw [MulEquiv.apply_symm_apply, e1, map_smul] at e2
    exact e2.symm
  exact hQ.hasType

end Act

theorem proj_mem_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.grp_record → A.v0 = InfinitePlace.mk D.what₂.embLL → ∀ (i : Fin D.R.m) (P : LevelP R.Pg D.R.r ℂ), ∀ U ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)), postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A)) U ∈ R.Wat i (sg0 D A) P := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h hr hv i P U hU
  have hL : LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
    obtain ⟨c, hc⟩ := h.βW i
    refine GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_) (Finset.disjoint_empty_right _)
    obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
    obtain ⟨k', hk'⟩ := (h.Pg PP').1 (hP'.resolve_right (Finset.notMem_empty _))
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ hv
  have hc : ∀ g, ∑ a, RealDat.eC (A := A) (sg0 D A) a * RealDat.eC (A := A) (sg0 D A) (a⁻¹ * g) =
      RealDat.eC (A := A) (sg0 D A) g := by
    rw [hs]; exact GlobalTheory.ProjectedLift.eC_conv R hr
  exact postOn_gaL_mem_goodPart (L := R.datWp i R.triv) hL R.eG _ hc
    ((GlobalTheory.ProjComm.proj_comm R h hr).2 i (sg0 D A)) P hU

end GlobalTheory.GoodProjLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteClPlusAndExistsCoords
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev GlobalTheory.ChiGrid
open Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField
open scoped ComplexOrder

namespace GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem UA_le_range_finE (V : HSp D) : UA D.sp.cm V.gram ≤ (finE V).range := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  intro x hx
  obtain ⟨b, hb⟩ := (GlobalTheory.Mass.swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram).surjective ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := hπ.surjective b
  refine ⟨g, Eq.trans ?_ (congrArg Subtype.val hb)⟩
  rw [GlobalTheory.Mass.coe_swapPts, hπ g]
  rfl

theorem map_levA (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))} (hK : K ≤ UA D.sp.cm V.gram) :
    (levA V K).map (finE V) = K := by
  have h0 : (GinfC V).map (finE V) = ⊥ := (Subgroup.map_eq_bot_iff _).2 fun g hg => by
    change Formalism.UG.bc (swapAE D) (finHom V g) = 1
    rw [show finHom V g = 1 from hg, map_one]
  have h := congrArg (Subgroup.map (finE V)) (GlobalTheory.Mass.Levels.comap_finE V K)
  rw [Subgroup.map_comap_eq_self (hK.trans (UA_le_range_finE V)), Subgroup.map_sup, h0, sup_bot_eq] at h
  exact h.symm

theorem congLev_relIndex_ne_zero (V : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) :
    (congLev D.sp.cm V.gram Λ 𝔪).relIndex (congLev D.sp.cm V.gram Λ ⊤) ≠ 0 := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have ho := (congLev_open_compact V hΛ h𝔪).1
  have hc := (congLev_open_compact V hΛ (𝔪 := ⊤) top_ne_bot).2
  rw [← map_levA V (K := congLev D.sp.cm V.gram Λ ⊤) fun _ h => h.1, ← Subgroup.relIndex_comap]
  haveI := isCompact_iff_compactSpace.1 hc
  haveI : CompactSpace (levA V (congLev D.sp.cm V.gram Λ ⊤)) := this
  haveI := Subgroup.quotient_finite_of_isOpen
    (((congLev D.sp.cm V.gram Λ 𝔪).comap (finE V)).subgroupOf (levA V (congLev D.sp.cm V.gram Λ ⊤)))
    (ho.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

private theorem selfDual_isFullLattice : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := fun V Λ hΛ => _root_.DedupShared.selfDual_isFullLattice V Λ hΛ

theorem finite_cl_congLev (V : HSp D) (hV : ∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) : Finite (Cl D.sp.cm V.gram (congLev D.sp.cm V.gram Λ 𝔪)) := by
  have hJ := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hfin := Formalism.UG.Final.ClassSetFiniteL D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram (cm_comp D.sp.cm)
    (Matrix.ext fun i j => hJ.1 i j) hJ.2.isUnit (GlobalTheory.DefiniteQuotient.isTotDef_of_posDef V fun τ => hV _) Λ
    (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top
  have e : Formalism.UG.levelAfL D.sp.cm.sig V.gram Λ = congLev D.sp.cm V.gram Λ ⊤ := congLev_top.symm
  rw [e] at hfin
  refine class_set_finite_of_finite_index _ _ _ _ ?_ ?_ hfin
  · exact fun x hx => Subgroup.mem_subgroupOf.2 (congLev_mono le_top (Subgroup.mem_subgroupOf.1 hx))
  · rw [Subgroup.relIndex_subgroupOf (show congLev D.sp.cm V.gram Λ ⊤ ≤ UA D.sp.cm V.gram from fun _ h => h.1)]
    exact congLev_relIndex_ne_zero V hΛ h𝔪

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GlobalTheory.ChiGrid.GridData L sc)

instance finite_clPlus : Finite G.ClPlus :=
  finite_cl_congLev (Xp G) (posDef_Xp G) (selfDual_isFullLattice _ _ (isV_Xp G).sd) (G.pl.modul_ne_bot sc)

theorem finite_testIx (h : (L.ΛY 0).FG) : Finite (TestIx G) :=
  haveI := G.finite_datum h
  inferInstance

theorem exists_coords (h : (L.ΛY 0).FG) :
    ∃ n, Nonempty (Fin n ≃ GlobalTheory.FunObj.TestIx G × VVIdx (GlobalTheory.FunObj.LaP G)) := by
  haveI := finite_testIx G h
  haveI : ∀ τ, Finite (Formalism.GradedWeylDivisibility.ssIdx (Xp G).rank (Xp G).rank (LaP G τ).natW) :=
    fun τ => (Formalism.GradedWeylDivisibility.sSIdxFinite _ _ _).to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (TestIx G × VVIdx (LaP G))
  exact ⟨n, ⟨e.symm⟩⟩

end GlobalTheory.FunObj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackCompFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackCompFactors
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.PullFactor

theorem objMap_factor : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S₀ S₁ T : Scheme.{0}) (s₀ : S₀ ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (t : T ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o : GlobalTheory.UPel.HT.Obj b N t) (g : S₁ ⟶ S₀) (h : T ⟶ S₁), GlobalTheory.UPel.HT.ObjMap o₁ o₀ g → GlobalTheory.UPel.HT.ObjMap o o₀ (h ≫ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o o₁ h) := by
  intro p _ D R _ b N S₀ S₁ T s₀ s₁ t o₀ o₁ o g h m₁ m
  exact GlobalTheory.UPel.HT.MapComp.cancel m m₁

end GlobalTheory.UPel.HT.PullFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackCompFactorsStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorPullback_comp_factors : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S₀ S₁ T : Scheme.{0}) (s₀ : S₀ ⟶ Sp R) (s₁ : S₁ ⟶ Sp R) (t : T ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N s₀) (o₁ : GlobalTheory.UPel.HT.Obj b N s₁) (o : GlobalTheory.UPel.HT.Obj b N t) (g : S₁ ⟶ S₀) (h : T ⟶ S₁), GlobalTheory.UPel.HT.ObjMap o₁ o₀ g → GlobalTheory.UPel.HT.ObjMap o o₀ (h ≫ g) → Nonempty (GlobalTheory.UPel.HT.ObjMap o o₁ h) := by
  first | exact @GlobalTheory.UPel.HT.PullFactor.objMap_factor | exact GlobalTheory.UPel.HT.PullFactor.objMap_factor | (intros; apply GlobalTheory.UPel.HT.PullFactor.objMap_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCanonicalAtIffOfIsLogCanonicalLocalEquation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCanonicalAtIffOfIsLogCanonicalLocalEquation
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem lcAt_iff_of_isLogEqn : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ : X → ℚ) (η : RatForms p n) (x : X) (m : ℕ) (g : X.functionFieldˣ), η ≠ 0 → 0 < m → IsLogEqn p Γ η x m g → (LcAt p n Γ x ↔ ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g) := by
  intro X _ _ _ p n hp hn Γ η x m g hη hm h
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  exact ⟨fun ⟨_, _, _, h₁, h₂, h₃, h₄⟩ E hE => discrep_eq hn h₁ hη h₂ hm h₃ h hE ▸ h₄ E hE,
    fun h' => ⟨η, m, g, hη, hm, h, h'⟩⟩

end GlobalTheory.PairStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCanonicalAtIffOfIsLogCanonicalLocalEquationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logCanonicalAt_iff_of_isLogCanonicalLocalEquation : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ : X → ℚ) (η : RatForms p n) (x : X) (m : ℕ) (g : X.functionFieldˣ), η ≠ 0 → 0 < m → IsLogEqn p Γ η x m g → (LcAt p n Γ x ↔ ∀ E : DivOver p, E.Through x → -1 ≤ discrep E η m g) := by
  first | exact @GlobalTheory.PairStep.lcAt_iff_of_isLogEqn | exact GlobalTheory.PairStep.lcAt_iff_of_isLogEqn | (intros; apply GlobalTheory.PairStep.lcAt_iff_of_isLogEqn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSmConnOfIsProper
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSmConnOfIsProper
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmConnProper

theorem isAbelianScheme_of_smConn_of_isProper (S : Scheme.{0}) (G : Over S) [GrpObj G]
    (h : GlobalTheory.SS.SmConn G) (hp : IsProper G.hom) : IsAbelianScheme G :=
  ⟨h.1, h.2.1, hp, h.2.2.2.2⟩

end GlobalTheory.SmConnProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSmConnOfIsProperStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_of_smConn_of_isProper' : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], GlobalTheory.SS.SmConn G → IsProper G.hom → IsAbelianScheme G := by
  first | exact @GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper | exact GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper | (intros; apply GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogEqnAddSmulIffOfOff
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]

theorem isLogEqn_add_smul_iff_of_off {p : X ⟶ Sp k} {n : ℕ} {Γ B : X → ℚ} (c : ℚ) {x : X}
    (hB : Off B x) (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ) :
    IsLogEqn p (Γ + c • B) η x m g ↔ IsLogEqn p Γ η x m g := by
  refine forall_congr' fun z => forall_congr' fun hz => ?_
  have : (Γ + c • B) z = Γ z := by simp [hB z hz]
  rw [this]

theorem off_add_smul (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ)
    (n : ℕ) (Γ B : X → ℚ) (c : ℚ) (x : X) (hB : Off B x) :
    (KltAt p n (Γ + c • B) x ↔ KltAt p n Γ x) ∧ (LcAt p n (Γ + c • B) x ↔ LcAt p n Γ x) ∧
      (IsNkltCentre p n (Γ + c • B) x ↔ IsNkltCentre p n Γ x) ∧ ∀ z, z ⤳ x → Off B z := by
  have e := isLogEqn_add_smul_iff_of_off (p := p) (n := n) (Γ := Γ) c hB
  refine ⟨?_, ?_, ?_, fun z hz w hw => hB w (hw.trans hz)⟩
  · unfold KltAt
    simp only [e]
  · unfold LcAt
    simp only [e]
  · unfold IsNkltCentre
    simp only [e]

end GlobalTheory.PairStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAmpleTwistNonvanishingFiniteSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAmpleTwistNonvanishingFiniteSet
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

namespace GlobalTheory.VolBr

theorem exists_sec_finite_subset_nonzeroLocus : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M A : HermLB p), IsAmpleLB A.B → ∀ S : Set X, S.Finite → ∃ b : ℕ, 0 < b ∧ ∃ u : (M.tens (A.pow b)).B.Sec, S ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p D hX M A hA S hS
  have := hX.isLocallyNoetherian
  have hEv : ∀ᶠ b : ℕ in atTop, ∀ (N : LB X) (hN : N.IsLB),
      CechPic.cls N hN = CechPic.cls M.B M.isLB + (b : ℤ) • CechPic.cls A.B hA.isLB →
        ∃ u : N.Sec, S ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u :=
    tendsto_natCast_atTop_atTop.eventually
      (hA.eventually_exists_finite_subset_nonzeroLocus M.isLB hS)
  obtain ⟨b, h₁, hb⟩ := (hEv.and (eventually_gt_atTop 0)).exists
  refine ⟨b, hb, ?_⟩
  have eA : CechPic.cls _ (A.pow b).isLB = (b : ℤ) • CechPic.cls A.B hA.isLB :=
    (CechPic.cls_lbPow hA.isLB b (A.pow b).isLB).trans (natCast_zsmul _ _).symm
  obtain ⟨u, hu⟩ := h₁ _ (M.tens (A.pow b)).isLB
    ((CechPic.cls_tens M.isLB (A.pow b).isLB (M.tens (A.pow b)).isLB).trans (congrArg _ eA))
  exact ⟨u, hu⟩

end GlobalTheory.VolBr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionAmpleTwistNonvanishingFiniteSetStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_ampleTwist_nonvanishing_finiteSet : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M A : HermLB p), IsAmpleLB A.B → ∀ S : Set X, S.Finite → ∃ b : ℕ, 0 < b ∧ ∃ u : (M.tens (A.pow b)).B.Sec, S ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  first | exact @GlobalTheory.VolBr.exists_sec_finite_subset_nonzeroLocus | exact GlobalTheory.VolBr.exists_sec_finite_subset_nonzeroLocus | (intros; apply GlobalTheory.VolBr.exists_sec_finite_subset_nonzeroLocus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleLevelSurjectiveOfDivisible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleLevelSurjectiveOfDivisible
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

theorem tate_lev_surj : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [CommGroup M], (∀ x : M, ∃ y, y ^ l = x) → ∀ (n : ℕ) (x : M), x ^ l ^ n = 1 → ∃ t : Tate l M, t.lev n = x := by
  intro l _ M _ hroot n x hx
  choose r hr using hroot
  have key : ∀ (m : ℕ) (y : M), (r^[m] y) ^ l ^ m = y := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, hr]
  refine ⟨GlobalTheory.HTLat.Tate.mk (fun m => (r^[m] x) ^ l ^ n) fun m => ⟨?_, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, key, hx]
  · rw [← pow_mul, mul_comm, pow_mul, Function.iterate_succ_apply', hr]
  · rw [GlobalTheory.HTLat.Tate.lev_mk, key]

end GlobalTheory.Published
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleLevelSurjectiveOfDivisibleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateModule_level_surjective_of_divisible : ∀ (l : ℕ) [Fact l.Prime] (M : Type) [CommGroup M], (∀ x : M, ∃ y, y ^ l = x) → ∀ (n : ℕ) (x : M), x ^ l ^ n = 1 → ∃ t : Tate l M, t.lev n = x := by
  first | exact @GlobalTheory.Published.tate_lev_surj | exact GlobalTheory.Published.tate_lev_surj | (intros; apply GlobalTheory.Published.tate_lev_surj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionOfGenericFibreDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionOfGenericFibreDvr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_lineBundle_extension_of_genericFibre_dvr :
    ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ N : LB (pullback G.hom (spMap (algebraMap W K'))), N.IsLB → ∃ (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), M.IsLB ∧ w.IsGen := by
  intro R K _ _ _ _ _ _ A _ hA N hN
  have hφ := IsPullback.of_hasPullback A.hom (spMap (algebraMap R K))
  have := hA.smooth
  have := hA.proper
  have hR : IsRegularRing R := inferInstance
  have : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth
      hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : GeometricallyIntegral (pullback.snd A.hom (spMap (algebraMap R K))) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) hφ inferInstance
  have : Smooth (pullback.snd A.hom (spMap (algebraMap R K))) :=
    MorphismProperty.of_isPullback (P := @Smooth) hφ inferInstance
  have : IsIntegral (pullback A.hom (spMap (algebraMap R K))) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian
      (pullback.snd A.hom (spMap (algebraMap R K)))
  have h1 : IsPreimmersion (spMap (algebraMap R K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h2 : Flat (spMap (algebraMap R K)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat K (nonZeroDivisors R))
  have : IsPreimmersion (pullback.fst A.hom (spMap (algebraMap R K))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hφ.flip h1
  have : Flat (pullback.fst A.hom (spMap (algebraMap R K))) :=
    MorphismProperty.of_isPullback (P := @Flat) hφ.flip h2
  have hst : ∀ x : A.left, UniqueFactorizationMonoid (A.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth R A.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  obtain ⟨L, hL, w, hw⟩ := exists_lineBundle_extension_of_generalizing A.left _
    (pullback.fst A.hom (spMap (algebraMap R K))) (Flat.generalizingMap _) hst N hN
  exact ⟨L, w, hL, hw⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionOfGenericFibreDvrStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_extension_of_genericFiber : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ N : LB (pullback G.hom (spMap (algebraMap W K'))), N.IsLB → ∃ (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), M.IsLB ∧ w.IsGen := by
  first | exact @GlobalTheory.exists_lineBundle_extension_of_genericFibre_dvr | exact GlobalTheory.exists_lineBundle_extension_of_genericFibre_dvr | (intros; apply GlobalTheory.exists_lineBundle_extension_of_genericFibre_dvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistCutInequalities
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistCutInequalities
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

private theorem finiteCohTwists_of_isProjOver' (k : Type) [Field k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k (X := X))) (F : X.Modules) [IsFiniteQC F] : FiniteCohTwists k F := by
  have hp' := hp
  unfold IsProjOver at hp'
  obtain ⟨N, i, hi, hcomp⟩ := hp'
  have hA : IsAmpleLB (ProjSpace.O1 k N) := isAmple_projective_O_one k N
  have hA' : IsAmpleLB ((ProjSpace.O1 k N).pull i) := IsAmpleLB.pull_of_isClosedImmersion hA i
  have hpr : IsProper (strHom k (X := X)) := by
    rw [← hcomp]
    have := isProper_str k N
    infer_instance
  exact IsAmpleLB.finiteCohTwists (f := strHom k X) (fun r => algebraMap_eq_strHom k X r) F hA'

theorem hdim_twist_cut_inequalities :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M M' : LB X) (hB : B.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (s : B.Sec), Mono (cutHom F hB s) → cls M hM = cls M' hM' + cls B hB → (∀ i, hdim k (twist F M) i ≤ hdim k (twist F M') i + hdim k (twist (cut F hB s) M) i) ∧ (∀ i, hdim k (twist F M') (i + 1) ≤ hdim k (twist (cut F hB s) M) i + hdim k (twist F M) (i + 1)) ∧ hdim k (twist F M') 0 ≤ hdim k (twist F M) 0 := by
  intro k _ _ X _ hp F _ B M M' hB hM hM' s hmono hcls
  have hS : (cutComplex F hB s).ShortExact := shortExact_cutComplex F hB s
  have := Twist.preservesFiniteLimits_twistFunctor hM
  have := Twist.preservesFiniteColimits_twistFunctor hM
  have hT := hS.map_of_exact (twistFunctor M)
  have hF : FiniteCohTwists k F := finiteCohTwists_of_isProjOver' k X hp F
  have hC : FiniteCohTwists k (cut F hB s) := FiniteCohTwists.cut (hL := hB) (s := s) (h := hF)
  have hBi : (lbZPow B (-1)).IsLB := isLB_lbZPow hB (-1)
  have hcls' : cls M' hM' = cls (lbZPow B (-1)) hBi + cls M hM := by
    rw [cls_lbZPow hB (-1) hBi, hcls]
    abel
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq F hBi hM hM' hcls'
  have f1 : ∀ n, Module.Finite k (coh (twist (twist F (lbZPow B (-1))) M) n) :=
    fun n => ((hF.twist hBi) M hM).finite n
  have f2 : ∀ n, Module.Finite k (coh (twist F M) n) := fun n => (hF M hM).finite n
  have f3 : ∀ n, Module.Finite k (coh (twist (cut F hB s) M) n) := fun n => (hC M hM).finite n
  have he : ∀ n, hdim k (twist (twist F (lbZPow B (-1))) M) n = hdim k (twist F M') n :=
    fun n => hdim_congr (k := k) (n := n) e
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · have h : hdim k (twist F M) i ≤ hdim k (twist (twist F (lbZPow B (-1))) M) i +
        hdim k (twist (cut F hB s) M) i := hdim₂_le k hT i (f1 i) (f3 i)
    rw [he i] at h
    exact h
  · have h : hdim k (twist (twist F (lbZPow B (-1))) M) (i + 1) ≤ hdim k (twist (cut F hB s) M) i +
        hdim k (twist F M) (i + 1) := hdim₁_le k hT i (f3 i) (f2 (i + 1))
    rw [he (i + 1)] at h
    exact h
  · have h0 := hdim₁_zero_le k hT (f2 0)
    have h : hdim k (twist (twist F (lbZPow B (-1))) M) 0 ≤ hdim k (twist F M) 0 := h0
    rw [he 0] at h
    exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistCutInequalitiesStatement
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M M' : LB X) (hB : B.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (s : B.Sec), Mono (cutHom F hB s) → cls M hM = cls M' hM' + cls B hB → (∀ i, hdim k (twist F M) i ≤ hdim k (twist F M') i + hdim k (twist (cut F hB s) M) i) ∧ (∀ i, hdim k (twist F M') (i + 1) ≤ hdim k (twist (cut F hB s) M) i + hdim k (twist F M) (i + 1)) ∧ hdim k (twist F M') 0 ≤ hdim k (twist F M) 0 := by
  first | exact @GlobalTheory.hdim_twist_cut_inequalities | exact GlobalTheory.hdim_twist_cut_inequalities | (intros; apply GlobalTheory.hdim_twist_cut_inequalities <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryConjSplitSupportedFiniteAdelicPoi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryConjSplitSupportedFiniteAdelicPoi
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ConjSplit

theorem sigR_incA (D : D7) (x : D.host.E) :
    cA D (incA D x) = incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := by
  simp [cA, sigR, incA, inclR]

def ratPt (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E)
    (hγ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram) : GA D V :=
  ⟨Formalism.UG.bc (incA D) γ, by
    show Formalism.UG.cT _ _ * _ * _ = _
    have hc : Formalism.UG.cT (cA D) ((γ : Matrix _ _ D.host.E).map (incA D)) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1).map (incA D) := by
      ext i j; simp [Formalism.UG.cT, sigR_incA]
    have := congrArg (fun M => M.map (incA D)) hγ
    simp only [Matrix.map_mul] at this
    simpa [Formalism.UG.bc, JR, hc] using this⟩

theorem finE_ratPt (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E) hγ :
    (Formalism.IndefR.Lev.finE V (ratPt D V γ hγ)).1 = γ.1.map (eToEAf D) := by
  ext i j
  change Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E
    (Algebra.TensorProduct.map (AlgHom.snd (↥D.host.F) (Ainf ↥D.host.F) (Af ↥D.host.F)) (AlgHom.id (↥D.host.F) D.host.E)
      (Algebra.TensorProduct.includeRight (γ.1 i j))) = _
  simp [eToEAf]

theorem mt_mul (D : D7) (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_mul_inv (D : D7) (V : HSp D) (a : GA D V) : mt V a * mt V a⁻¹ = 1 := by
  rw [← mt_mul, mul_inv_cancel]; simp [Formalism.L2.Theta.mt]

theorem suppAt_conj {D : D7} {V : HSp D} {e : AE D} {h : GA D V} (hs : SuppAt e V h) (g : GA D V) :
    SuppAt e V (g * h * g⁻¹) := by
  have hm : (e + cA D e) • (mt V h - 1) = mt V h - 1 := Matrix.ext fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]; exact hs i j
  have key : mt V (g * h * g⁻¹) - 1 = mt V g * (mt V h - 1) * mt V g⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  have hm' : (e + cA D e) • (mt V (g * h * g⁻¹) - 1) = mt V (g * h * g⁻¹) - 1 := by
    rw [key, ← Matrix.smul_mul, ← Matrix.mul_smul, hm]
  intro i j
  have := congrFun (congrFun hm' i) j
  rwa [Matrix.smul_apply, smul_eq_mul] at this

theorem finE_ratPt_units (D : D7) (V : HSp D) (γ : GL (Fin V.rank) D.host.E) hγ :
    Formalism.IndefR.Lev.finE V (ratPt D V γ hγ) = Formalism.UG.bc (eToEAf D) γ :=
  Units.ext (finE_ratPt D V γ hγ)

theorem conj_supp : ∀ (D : D7) (V : HSp D) (S : Finset ℕ) (γ : GL (Fin V.rank) D.host.E) (h : GA D V),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram → h ∈ GfC V →
    (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) →
    ∃ u : GA D V, u ∈ GfC V ∧ (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u ∧ ∀ w ∈ P, Off S w) ∧
      (Formalism.IndefR.Lev.finE V u).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (γ⁻¹).1.map (eToEAf D) := by
  intro D V S γ h hγ hh ⟨P, e, he, hs, hoff⟩
  refine ⟨ratPt D V γ hγ * h * (ratPt D V γ hγ)⁻¹, ?_, ⟨P, e, he, suppAt_conj hs _, hoff⟩, ?_⟩
  · exact (MonoidHom.normal_ker (infHom V)).conj_mem h hh _
  · rw [map_mul, map_mul, map_inv, finE_ratPt_units, Units.val_mul, Units.val_mul, ← map_inv]
    rfl

end GlobalTheory.ConjSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryConjSplitSupportedFiniteAdelicPoiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalUnitary_conj_splitSupported_finiteAdelicPoint : ∀ (D : D7) (V : HSp D) (S : Finset ℕ) (γ : GL (Fin V.rank) D.host.E) (h : GA D V),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1 = V.gram → h ∈ GfC V →
    (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V h ∧ ∀ w ∈ P, Off S w) →
    ∃ u : GA D V, u ∈ GfC V ∧ (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u ∧ ∀ w ∈ P, Off S w) ∧
      (Formalism.IndefR.Lev.finE V u).1 = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 * (γ⁻¹).1.map (eToEAf D) := by
  first | exact @GlobalTheory.ConjSplit.conj_supp | exact GlobalTheory.ConjSplit.conj_supp | (intros; apply GlobalTheory.ConjSplit.conj_supp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinsMerge
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Merge

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}

def comap {Tp Tp' : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (f : Tp' → Tp) : OMDat C R i Tp' (fun t => tup (f t)) where
  c' := O.c'
  hle := O.hle
  jL := O.jL
  hV := O.hV
  c0' := O.c0'
  lev := O.lev
  dδ := fun t => O.dδ (f t)
  Cl' := fun t => O.Cl' (f t)
  fCl := fun t => O.fCl (f t)
  bad := fun t => O.bad (f t)
  Lh := fun t => O.Lh (f t)
  La := fun t => O.La (f t)
  Nc := fun t => O.Nc (f t)
  gam := fun t => O.gam (f t)
  vol := fun t => O.vol (f t)
  ep := fun t => O.ep (f t)
  B := fun t => O.B (f t)
  epF := fun t => O.epF (f t)
  io := O.io
  hw := O.hw
  φ := fun t => O.φ (f t)
  w := fun t => O.w (f t)
  U₂ := fun t => O.U₂ (f t)
  dict₂ := fun t => O.dict₂ (f t)
  xi := fun t => O.xi (f t)
  thAd := fun t => O.thAd (f t)
  Plc := fun t => O.Plc (f t)

theorem pins_comap {Tp Tp' : Type} {tup : Tp → T0} {O : OMDat C R i Tp tup} (f : Tp' → Tp) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) : (comap O f).Pins κ v₀ ι x₀ :=
  ⟨h.lift, fun t => h.tuple (f t), h.act, fun t => h.bad (f t), fun t => h.reps (f t), fun t => h.ep (f t), h.io,
    fun t => h.w (f t), fun t => h.cov (f t), h.cxi.imp fun _ hc => ⟨hc.1, fun t => hc.2 (f t)⟩, fun t => h.model₂ (f t)⟩

variable {J : Type} {tup : J → T0} (src : ∀ j, OMDat C R i Unit (fun _ => tup j)) (c₃ : Coeff C.Q.l) (h₃ : C.Q.c.F ≤ c₃.F)
  (hs : ∀ j, (src j).c'.F ≤ c₃.F) (jL₃ : D.what₂.LL →+* c₃.F) (hV₃ : C.V ((i : ℕ) + 1) (sOv C c₃ h₃) = Wc D i)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (u : J → c₃.F) (h : ∀ j, (src j).Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)

def merge : OMDat C R i J tup where
  c' := c₃
  hle := h₃
  jL := jL₃
  hV := hV₃
  c0' := c0₃
  lev := lev
  dδ := fun j => covBC (hs j) ((src j).dδ ()) (u j)
  Cl' := fun j => (src j).Cl' ()
  fCl := fun j => (src j).fCl ()
  bad := fun j => (src j).bad ()
  Lh := fun j => (src j).Lh ()
  La := fun j => (src j).La ()
  Nc := fun j => (src j).Nc ()
  gam := fun j => (src j).gam ()
  vol := fun j => incF _ c₃ (hs j) ((src j).vol ())
  ep := fun j k => incF _ c₃ (hs j) ((src j).ep () k)
  B := fun j I => incF _ c₃ (hs j) ((src j).B () I)
  epF := fun j L => incF _ c₃ (hs j) ((src j).epF () L)
  io := io₃
  hw := hw₃
  φ := fun j x => incF _ c₃ (hs j) ((src j).φ () x)
  w := fun j k q => incF _ c₃ (hs j) ((src j).w () k q)
  U₂ := fun j => covUnf (hs j) ((src j).dδ ()) (u j) ((src j).U₂ ())
  dict₂ := fun j => (src j).dict₂ ()
  xi := fun j => (src j).xi ()
  thAd := fun j => thAdOf R i (tup j) (h j) c0₃ v₀
  Plc := fun j x => ∃ x₀, Place R i (tup j) (h j) c0₃ (jVx R i (tup j) x₀) x

theorem repsR_map {K K' : Type} [Field K] [Field K'] (j : K →+* K') {t : T0} {Cl : Type} {h : Cl → GA D (Vc D i)} {bad J' Lh gam}
    {vol : K} (hr : RepsR R i t h bad J' Lh gam vol) : RepsR R i t h bad J' Lh gam (j vol) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  exact ⟨h1, h2, h3, h4, by rw [h5, map_inv₀, map_natCast], h6⟩


end Merge

end GlobalTheory.OneMapAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorNefOfDimLeZero
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem isAmpleLB_tens_of_isNef_of_dim_le_zero : ∀ (k : Type) [Field k] [Infinite k], (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (0 : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) := by
  intro k _ _ Y _ hp hd A N hA hN
  have : AlgebraicGeometry.IsNoetherian Y := isNoetherian_of_isProjOver hp
  have hAN : (tens A N).IsLB := (IsNef.tens_of_isProjOver (IsAmpleLB.isNef (k := k) hA) hN hp).isLB
  have hlt : topologicalKrullDim Y < ((1 : ℕ) : WithBot ℕ∞) :=
    lt_of_le_of_lt hd (by exact_mod_cast Nat.zero_lt_one)
  refine isAmpleLB_of_subsingleton_coh_one Y (tens A N) hAN fun F _ => ⟨1, le_rfl, ?_⟩
  have : IsFiniteQC (twist F (lbPow (tens A N) 1)) := isFiniteQC_twist (isLB_lbPow hAN 1)
  exact hA.subsingleton_coh_of_dim_lt _ hlt

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotKltAtOfIsNkltCentre
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem not_kltAt_of_isNkltCentre (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ) (hp : IsProjOver p)
    (hn : topologicalKrullDim X = n) (Γ : X → ℚ) (z x : X) (h : IsNkltCentre p n Γ z)
    (hz : z ⤳ x) : ¬ KltAt p n Γ x := by
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  rintro ⟨η', m', g', h₁, h₂, h₃, h₄⟩
  obtain ⟨E, η, m, g, hη, hm, hg, hE, hd⟩ := h
  have h₅ : IsLogEqn p Γ η' z m' g' := fun w hw => h₃ w (hw.trans hz)
  have h₆ := h₄ E (hE.1.of_specializes hz)
  rw [discrep_eq hn h₁ hη h₂ hm h₅ hg hE.1] at h₆
  exact h₆.not_ge hd

end GlobalTheory.PairStep
end
