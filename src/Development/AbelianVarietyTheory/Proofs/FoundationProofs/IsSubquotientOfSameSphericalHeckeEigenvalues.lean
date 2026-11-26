module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfLevelCoefficients
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSubquotientOfSameSphericalHeckeEigenvalues
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSubquotientOfSameSphericalHeckeEigenvalues
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LGrp.Zonal

open GlobalTheory.LocGL

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {K : Subgroup G}

theorem heckeVec_dosetInd {σ : Representation ℂ G V} (hσ : IsSmooth σ) (hc : IsCompact (K : Set G))
    (hK : IsCommensurated K) {z : V} (hz : z ∈ fixed σ K) (g : G) :
    heckeVec σ K (dosetInd ℂ K g) z =
      ((P.finite_cosets_in_doset hK g).toFinset.card : ℂ) • idem hσ hc (σ g z) := by
  have hmem : ∀ c : G ⧸ K, c.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) ↔
      c ∈ (P.finite_cosets_in_doset hK g).toFinset := fun c => by
    rw [Set.Finite.mem_toFinset, DoubleCoset.mem_doubleCoset]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩, fun ⟨a, b, e⟩ => ⟨a, a.2, b, b.2, e⟩⟩
  rw [← idem_of_mem hσ hc (SatCompare.heckeVec_mem_fixed hK (Final.DosetIndMem G K ℂ g) hz)]
  unfold heckeVec
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_support_subset (s := (P.finite_cosets_in_doset hK g).toFinset), map_sum,
    Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
  · refine Finset.sum_congr rfl fun c hc' => ?_
    have h1 := (hmem c).2 hc'
    obtain ⟨a, b, e⟩ := (Set.Finite.mem_toFinset _).1 hc'
    rw [dosetInd, Set.indicator_of_mem h1, Pi.one_apply, one_smul, e, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, mem_fixed.1 hz b b.2, idem_apply_mem hσ hc a.2]
  · intro c hc'
    by_contra h
    exact hc' (by
      show dosetInd ℂ K g c.out • _ = 0
      rw [dosetInd, Set.indicator_of_notMem (fun h' => h ((hmem c).1 h')), zero_smul])


omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem card_ne_zero (hK : IsCommensurated K) (g : G) :
    ((P.finite_cosets_in_doset hK g).toFinset.card : ℂ) ≠ 0 := by
  refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), (Set.Finite.mem_toFinset _).2 ?_⟩)
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K g
  exact ⟨1, u, by simpa using hu⟩

theorem idem_orbitMap {π : Representation ℂ G V} {ρ : Representation ℂ G W} (hπ : IsSmooth π) (hρ : IsSmooth ρ)
    (hc : IsCompact (K : Set G)) {x : V} {y : W}
    (h : ∀ g, ∃ c : ℂ, idem hπ hc (π g x) = c • x ∧ idem hρ hc (ρ g y) = c • y) (a : MonoidAlgebra ℂ G) :
    ∃ c : ℂ, idem hπ hc (orbitMap π x a) = c • x ∧ idem hρ hc (orbitMap ρ y a) = c • y := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    obtain ⟨c, ha, hb⟩ := h g
    refine ⟨c, ?_, ?_⟩
    · show idem hπ hc (π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x) = _
      simpa using ha
    · show idem hρ hc (ρ.asAlgebraHom (MonoidAlgebra.of ℂ G g) y) = _
      simpa using hb
  | add a b ha hb =>
    obtain ⟨c, h1, h2⟩ := ha
    obtain ⟨d, h3, h4⟩ := hb
    exact ⟨c + d, by rw [map_add (f := _), map_add (f := _), h1, h3, add_smul], by rw [map_add (f := _), map_add (f := _), h2, h4, add_smul]⟩
  | smul r a ha =>
    obtain ⟨c, h1, h2⟩ := ha
    exact ⟨r * c, by rw [map_smul, map_smul, h1, mul_smul], by rw [map_smul, map_smul, h2, mul_smul]⟩

theorem isSubquot_of_hecke_eigenvalues (G V W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (ρ : Representation ℂ G W)
    (K : Subgroup G) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K) (hπ : IsIrrSmooth π) (hρ : IsSmooth ρ)
    (x : V) (hx : x ∈ fixed π K) (hx0 : x ≠ 0) (y : W) (hy : y ∈ fixed ρ K) (hy0 : y ≠ 0)
    (h : ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec π K h x = c • x ∧ heckeVec ρ K h y = c • y) : IsSubquot π ρ := by
  have h1 : ∀ g, ∃ c : ℂ, idem hπ.1 hc (π g x) = c • x ∧ idem hρ hc (ρ g y) = c • y := fun g => by
    obtain ⟨c, ha, hb⟩ := h _ (Final.DosetIndMem G K ℂ g)
    rw [heckeVec_dosetInd hπ.1 hc hK hx] at ha
    rw [heckeVec_dosetInd hρ hc hK hy] at hb
    have hn := card_ne_zero hK g
    refine ⟨((P.finite_cosets_in_doset hK g).toFinset.card : ℂ)⁻¹ * c, ?_, ?_⟩
    · rw [mul_smul, ← ha, inv_smul_smul₀ hn]
    · rw [mul_smul, ← hb, inv_smul_smul₀ hn]
  let T : Subrepresentation π :=
    ⟨⨅ g, LinearMap.ker (idem hπ.1 hc ∘ₗ π g), fun g v hv => by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hv ⊢
      intro g'
      simpa using hv (g' * g)⟩
  have hT : T = ⊥ := by
    haveI := hπ.2
    refine (eq_bot_or_eq_top T).resolve_right fun e => hx0 ?_
    have : x ∈ T := e ▸ trivial
    have h2 : idem hπ.1 hc (π 1 x) = 0 := (Submodule.mem_iInf _).1 this 1
    rwa [map_one, Module.End.one_apply, idem_of_mem hπ.1 hc hx] at h2
  have hker : LinearMap.ker (orbitMap ρ y).toLinearMap ≤ LinearMap.ker (orbitMap π x).toLinearMap := fun a h0 => by
    have h0' : orbitMap ρ y a = 0 := h0
    have : orbitMap π x a ∈ T := (Submodule.mem_iInf _).2 fun g => by
      show idem hπ.1 hc (π g (orbitMap π x a)) = 0
      obtain ⟨c, h2, h3⟩ := idem_orbitMap hπ.1 hρ hc h1 (Representation.leftRegular ℂ G g a)
      rw [(orbitMap ρ y).isIntertwining, h0', map_zero, map_zero] at h3
      rw [← (orbitMap π x).isIntertwining, h2,
        (smul_eq_zero.1 h3.symm).resolve_right hy0, zero_smul]
    rw [hT] at this
    exact this
  let f : (orbitMap ρ y).range.toSubmodule →ₗ[ℂ] V :=
    Submodule.liftQ _ _ hker ∘ₗ (orbitMap ρ y).toLinearMap.quotKerEquivRange.symm.toLinearMap
  have hf : ∀ a h, f ⟨orbitMap ρ y a, h⟩ = orbitMap π x a := fun a h => by
    have := (orbitMap ρ y).toLinearMap.quotKerEquivRange_symm_apply_image a h
    exact (congrArg (Submodule.liftQ _ _ hker) this).trans rfl
  refine ⟨(orbitMap ρ y).range, ⟨f, fun g => LinearMap.ext ?_⟩, fun v => ?_⟩
  · rintro ⟨_, a, rfl⟩
    have e := (orbitMap ρ y).isIntertwining _ _ g a
    have e' : (orbitMap ρ y).range.toRepresentation g ⟨orbitMap ρ y a, a, rfl⟩ =
        ⟨orbitMap ρ y (Representation.leftRegular ℂ G g a), _, rfl⟩ := Subtype.ext e.symm
    show f ((orbitMap ρ y).range.toRepresentation g ⟨orbitMap ρ y a, a, rfl⟩) = π g (f ⟨orbitMap ρ y a, a, rfl⟩)
    rw [e']
    exact (hf _ _).trans (((orbitMap π x).isIntertwining _ _ g a).trans (congrArg (π g) (hf _ _).symm))
  · obtain ⟨a, rfl⟩ := orbitMap_surjective hπ.2 hx0 v
    exact ⟨⟨_, a, rfl⟩, hf a _⟩

end GlobalTheory.LGrp.Zonal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSubquotientOfSameSphericalHeckeEigenvaluesStatement
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_of_same_spherical_hecke_eigenvalues : ∀ (G V W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (ρ : Representation ℂ G W) (K : Subgroup G), IsCompact (K : Set G) → IsCommensurated K → GlobalTheory.LGrp.IsIrrSmooth π → IsSmooth ρ → ∀ x ∈ fixed π K, x ≠ 0 → ∀ y ∈ fixed ρ K, y ≠ 0 → (∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec π K h x = c • x ∧ heckeVec ρ K h y = c • y) → GlobalTheory.LGrp.IsSubquot π ρ := by
  first | exact @GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues | exact GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues | (intros; apply GlobalTheory.LGrp.Zonal.isSubquot_of_hecke_eigenvalues <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignAtBasePlaceEqEmbedding
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCoord

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Cx
open GlobalTheory.FormTies GlobalTheory.OnTies
open GlobalTheory.OntoChain (coordMap thetaMat thetaOp liftLvl liftSub supLat Mir mirIncl uni mirToGL)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem chi_eq_one (hG : R.IsGrp F) (i : Fin D.R.m) {g : G} (hg : g ∈ F.P0) : (R.FW i).chi g = 1 := by
  obtain ⟨u, hu, rfl⟩ := (OntoChain.mem_base_iff hG.levels g).1 hg
  have h1 := (OntoChain.mem_pi_unip_iff R _).2 ⟨u, hu, rfl⟩
  refine Units.ext (D.what₂.embLL.injective ?_)
  rw [hG.chiW, Units.val_one, map_one, OntoChain.eG_mirIncl]
  refine Finset.prod_eq_one fun v _ => ?_
  have h2 := h1 v (Set.mem_univ v)
  have h3 : Matrix.GeneralLinearGroup.det (mirToGL R u v) = 1 := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular h2.1]
    exact Finset.prod_eq_one fun k _ => h2.2 k
  rw [h3, map_one, Units.val_one]

end Real

end GlobalTheory.OnCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankOneBaseWeightEqCmTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalfOfPrimesIffLevelPb
noncomputable section

namespace GlobalTheory.ParAtCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke

theorem isHalf_of_level (D : D7) (l : Level (hostOfRecord D)) (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) :
    HalfLevelCoefficients.IsHalf D l.Mb :=
  ⟨l.fromK, hl.1 ▸ l.prod, l.coprime⟩

theorem levelAt_spec (D : D7) (Mb : Ideal (𝓞 D.host.E)) (h : HalfLevelCoefficients.IsHalf D Mb) :
    (HalfLevelCoefficients.levelAt D Mb h).M = D.host.g 0 * D.host.g 1 ∧ (HalfLevelCoefficients.levelAt D Mb h).A = 1 :=
  ⟨rfl, rfl⟩

theorem levelPb_iff (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) :
    LevelPb D pb ↔ HalfLevelCoefficients.IsHalf D (HalfLevelCoefficients.halfOf D pb) := by
  constructor
  · rintro ⟨l, hl, hb⟩
    have h := isHalf_of_level D l hl
    rw [hb] at h
    exact h
  · intro h
    exact ⟨HalfLevelCoefficients.levelAt D _ h, levelAt_spec D _ h, rfl⟩

end GlobalTheory.ParAtCompare
end
end

noncomputable section

namespace GlobalTheory.HalfOnRecord

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Pj.LPb Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign GlobalTheory.HalfCompare GlobalTheory.CoverHalf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level)
open Formalism.L2.Host (PiBar)

variable {D : D7}

def designLevel (P : PiBar D.host) : Level (hostOfRecord D) :=
  IndefiniteRowSideFullHecke.HalfLevelCoefficients.levelAt D (IndefiniteRowSideFullHecke.HalfLevelCoefficients.halfOf D P.pb) ((ParAtCompare.levelPb_iff D P.pb).1 (levelPb_exists D P.pb P.pb_over))

theorem designLevel_Mb (P : PiBar D.host) :
    (designLevel P).Mb = ∏ k, (P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := rfl

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Rec

end GlobalTheory.HalfOnRecord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitarySatakeTransformIsLaurentPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitarySatakeTransformIsLaurentPolynomial
noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.SatCoef

open GlobalTheory.InertThetaCompare

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ : L}


open Classical in
def cellSum (ϖ : L) (h : GU σ n → ℂ) (a : Fin (n / 2) → ℤ) : ℂ :=
  ∑ᶠ x : GU σ n ⧸ KU σ n, if Cell ϖ a x then h x.out else 0

theorem exists_of_cellSum {h : GU σ n → ℂ} {a : Fin (n / 2) → ℤ} (ha : cellSum ϖ h a ≠ 0) :
    ∃ x : GU σ n ⧸ KU σ n, h x.out ≠ 0 ∧ Cell ϖ a x := by
  classical
  by_contra hne
  push Not at hne
  refine ha (finsum_eq_zero_of_forall_eq_zero fun x => ?_)
  split_ifs with hx
  · by_contra h0
    exact hne x h0 hx
  · rfl

theorem finite_supp (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) :
    {x : GU σ n ⧸ KU σ n | h x.out ≠ 0}.Finite :=
  P.finite_support_cosets (P.isCommensurated_integral_unitary_of_unramified hU n) hh.2

theorem finite_cellSum (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) :
    {a | cellSum ϖ h a ≠ 0}.Finite := by
  refine ((finite_supp hU hh).biUnion (t := fun x => {a | Cell ϖ a x}) fun x _ => Set.Subsingleton.finite ?_).subset ?_
  · rintro a ⟨u, hu, k, hk, e⟩ a' ⟨u', hu', k', hk', e'⟩
    exact P.fSatake_cell_unique hU (Nat.mul_div_le n 2) hu hu' hk hk' (e.symm.trans e')
  · intro a ha
    obtain ⟨x, hx⟩ := exists_of_cellSum ha
    exact Set.mem_biUnion hx.1 hx.2

theorem cellSum_dosetInd (hU : IsUnramInv ϖ σ q) (t : GU σ n) (ε : Fin (n / 2) → ℤ)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε) :
    cellSum ϖ (dosetInd ℂ (KU σ n) t) ε ≠ 0 := by
  classical
  have hf : {x : GU σ n ⧸ KU σ n | Cell ϖ ε x ∧ dosetInd ℂ (KU σ n) t x.out ≠ 0}.Finite :=
    (finite_supp hU (Final.DosetIndMem _ _ ℂ t)).subset fun x hx => hx.2
  have key : ∀ x : GU σ n ⧸ KU σ n, ∀ [Decidable (Cell ϖ ε x)],
      (if Cell ϖ ε x then dosetInd ℂ (KU σ n) t x.out else 0) = if x ∈ hf.toFinset then 1 else 0 := by
    intro x _
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    by_cases h1 : Cell ϖ ε x
    · by_cases h2 : dosetInd ℂ (KU σ n) t x.out = 0
      · simp [h1, h2]
      · rw [if_pos h1, if_pos ⟨h1, h2⟩]
        unfold dosetInd at h2 ⊢
        exact Set.indicator_of_mem (Set.mem_of_indicator_ne_zero h2) _
    · simp [h1]
  unfold cellSum
  rw [finsum_congr fun x => @key x _, finsum_eq_sum_of_support_subset (s := hf.toFinset) _ (fun x hx => by
    by_contra h
    exact hx (if_neg h)), Finset.sum_congr rfl fun x hx => if_pos hx]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
  refine Finset.ne_empty_of_mem (a := (QuotientGroup.mk t : GU σ n ⧸ KU σ n)) ?_
  rw [Set.Finite.mem_toFinset]
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KU σ n) t
  refine ⟨⟨1, ⟨P.fSatake_borel_one, fun i => by simp⟩, k, k.2, ?_⟩, ?_⟩
  · rw [hk]
    simp only [Subgroup.coe_mul, Units.val_mul, ht, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]
  · rw [hk]
    unfold dosetInd
    rw [Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, k.1, k.2, by rw [one_mul]⟩ :
      t * k.1 ∈ DoubleCoset.doubleCoset t (KU σ n : Set (GU σ n)) (KU σ n : Set (GU σ n)))]
    exact one_ne_zero

theorem satU_laurent : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ h ∈ Hecke ℂ (KU σ n), ∃ s : (Fin (n / 2) → ℤ) →₀ ℂ, (∀ α : Fin (n / 2) → ℂ, SatU ϖ q h α = s.sum fun a c => c * ∏ i, α i ^ a i) ∧ (∀ κ, s κ ≠ 0 → ∃ g : GU σ n, h g ≠ 0 ∧ ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧ ∀ (t : GU σ n) (ε : Fin (n / 2) → ℤ), ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε → h = dosetInd ℂ (KU σ n) t → s ε ≠ 0 := by
  intro L _ _ ϖ σ q n hU h hh
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  let f : (Fin (n / 2) → ℤ) → ℂ := fun a =>
    (∏ i : Fin (n / 2), (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) * cellSum ϖ h a
  have hf : (Function.support f).Finite := (finite_cellSum hU hh).subset fun a ha => right_ne_zero_of_mul ha
  refine ⟨Finsupp.ofSupportFinite f hf, fun α => ?_, fun κ hκ => ?_, fun t ε ht e => ?_⟩
  · have e : SatU ϖ q h α = ∑ᶠ a, f a * ∏ i, α i ^ a i := by
      unfold SatU
      refine finsum_congr fun a => ?_
      rw [Finset.prod_mul_distrib, mul_comm (∏ i, α i ^ a i), mul_right_comm]
      rfl
    rw [e, Finsupp.sum]
    exact finsum_eq_sum_of_support_subset _ fun a ha =>
      Finset.mem_coe.2 (Finsupp.mem_support_iff.2 (left_ne_zero_of_mul ha))
  · obtain ⟨x, h1, h2⟩ := exists_of_cellSum (right_ne_zero_of_mul (show f κ ≠ 0 from hκ))
    exact ⟨x.out, h1, h2⟩
  · subst e
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ hq) (cellSum_dosetInd hU t ε ht)

end GlobalTheory.LFun.SatCoef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitarySatakeTransformIsLaurentPolynomialStatement
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatakeTransform_isLaurentPolynomial : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ h ∈ Hecke ℂ (KU σ n), ∃ s : (Fin (n / 2) → ℤ) →₀ ℂ, (∀ α : Fin (n / 2) → ℂ, SatU ϖ q h α = s.sum fun a c => c * ∏ i, α i ^ a i) ∧ (∀ κ, s κ ≠ 0 → ∃ g : GU σ n, h g ≠ 0 ∧ ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧ ∀ (t : GU σ n) (ε : Fin (n / 2) → ℤ), ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε → h = dosetInd ℂ (KU σ n) t → s ε ≠ 0 := by
  first | exact @GlobalTheory.LFun.SatCoef.satU_laurent | exact GlobalTheory.LFun.SatCoef.satU_laurent | (intros; apply GlobalTheory.LFun.SatCoef.satU_laurent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualFrLatticeHolds
namespace GlobalTheory

theorem dualFrLattice_holds : Formalism.L2.DIV.DualFrLattice :=
  GlobalTheory.DualLat.dualFr_lattice_and_hdual.1

end GlobalTheory
end

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceClassRank

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies GlobalTheory.OnTies
open Formalism.HermitianLatticesTheory (localization₂)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

theorem fg_of_graph {R P X : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup P] [Module R P] [AddCommGroup X]
    [Module R X] {N : Submodule R P} (hN : N.FG) (Γ : Submodule R (P × X)) (hΓ : ∀ x, ((0 : P), x) ∈ Γ → x = 0)
    {s : Set X} (hs : ∀ x ∈ s, ∃ p ∈ N, (p, x) ∈ Γ) : (Submodule.span R s).FG := by
  have h1 : (Γ ⊓ N.comap (LinearMap.fst R P X)).FG := by
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.fst R P X) (hN.of_le ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · have : Γ ⊓ N.comap (LinearMap.fst R P X) ⊓ LinearMap.ker (LinearMap.fst R P X) = ⊥ := by
        refine eq_bot_iff.2 ?_
        rintro ⟨p, x⟩ ⟨⟨h, -⟩, hp⟩
        have hp' : p = 0 := hp
        subst hp'
        rw [hΓ x h]
        exact Submodule.zero_mem _
      rw [this]
      exact Submodule.fg_bot
  refine (h1.map (LinearMap.snd R P X)).of_le (Submodule.span_le.2 fun x hx => ?_)
  obtain ⟨p, hp, h⟩ := hs x hx
  exact ⟨(p, x), ⟨h, hp⟩, rfl⟩

variable {K : Type} [Field K] [NumberField K] {n n' : ℕ}

theorem localization_comap_le (v : HeightOneSpectrum (𝓞 K)) (f : (Fin n → K) →ₗ[K] (Fin n' → K))
    {A B : Submodule (𝓞 K) (Fin n' → K)} (h : localization₂ v.asIdeal A ≤ localization₂ v.asIdeal B) :
    localization₂ v.asIdeal (A.comap (f.restrictScalars (𝓞 K))) ≤ localization₂ v.asIdeal (B.comap (f.restrictScalars (𝓞 K))) := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, hy⟩ := h (x := f x) ⟨s, hs, (f.restrictScalars (𝓞 K)).map_smul s x ▸ (hx : (f.restrictScalars (𝓞 K)) (s • x) ∈ A)⟩
  exact ⟨t, ht, by rwa [Submodule.mem_comap, map_smul]⟩

end Lat

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Adelic

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def dataLevel (Q : Finset (Pl D.host.E)) : Subgroup (Bridge.Gf (Vc D i)) :=
  (levEnv (Vc D i) (R.βV i) (Lev.datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1)
    Lev.Frm.A)).J


variable {i} in
def MeetsClasses (J : Subgroup (Bridge.Gf (Vc D i))) {Cl : Type} (h : Cl → GA D (Vc D i)) : Prop :=
  (∀ c, h c ∈ GfC (Vc D i)) ∧
    ∀ x : Bridge.Gf (Vc D i), ∃ (c : Cl) (γ : GQ (Vc D i)) (k : J), x = Bridge.ratF (Vc D i) γ * fin (Vc D i) (h c) * k

def seriesAt (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (h : GA D (Vc D i)) : Set (Fin (R.nW i) → D.what₂.LL) :=
  {x | ∃ w, InCoefLat R i h w ∧ ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
    adForm R i x (fun ρ => v ρ) = ph • levelTrace R i U ψ (singleSeries R i ω φ h w v)}

def IsBaseKernel (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsKernel R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) (placesOver R (R.mu v) p) ω φ

def SpanOverClasses (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) : Prop :=
  ∀ ω φ, IsBaseKernel R i v p ω φ → ∀ (Cl : Type) (h : Cl → GA D (Vc D i)),
    MeetsClasses (dataLevel R i (placesOver R (R.mu v) p)) h →
      thetaBase R i U ψ ph v p = Submodule.span (𝓞 D.what₂.LL) (⋃ c, seriesAt R i U ψ ph ω φ (h c))

def FormsDetermined : Prop :=
  ∀ x, (∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i x (fun ρ => v ρ) = 0) → x = 0

def BaseKernelUnique (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) : Prop :=
  ∀ ω φ ω' φ', IsBaseKernel R i v p ω φ → IsBaseKernel R i v p ω' φ' → singleSeries R i ω φ = singleSeries R i ω' φ'

def KernelSpanOverClasses (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) : Prop :=
  ∀ ω φ, IsBaseKernel R i v p ω φ → ∀ (Cl : Type) (h : Cl → GA D (Vc D i)),
    MeetsClasses (dataLevel R i (placesOver R (R.mu v) p)) h →
      Submodule.span (𝓞 D.what₂.LL) (seriesSet R i U ψ ph ω φ) =
        Submodule.span (𝓞 D.what₂.LL) (⋃ c, seriesAt R i U ψ ph ω φ (h c))

variable {R i}

theorem spanOverClasses_of {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {p : ℕ}
    (h1 : BaseKernelUnique R i v p) (h2 : KernelSpanOverClasses R i U ψ ph v p) : SpanOverClasses R i U ψ ph v p := by
  intro ω φ hk Cl h hh
  rw [← h2 ω φ hk Cl h hh]
  unfold thetaBase
  congr 1
  ext x
  refine ⟨?_, fun hx => ⟨ω, φ, hk, hx⟩⟩
  rintro ⟨ω', φ', hk', hx⟩
  unfold seriesSet at hx ⊢
  rwa [h1 ω φ ω' φ' hk hk']

theorem formsDetermined_of (hres : GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInjAt R) (hW : R.models_HW) (hu : R.LUnif) : FormsDetermined R i := by
  intro x hx
  obtain ⟨h1, h2, -⟩ := hW i (sg0 D A)
  have h3 : adForm R i x = 0 := hres i _ (h2 ▸ LinearMap.mem_range_self _ _) hx
  have h4 : (R.FW i).j (sg0 D A) x = 0 := h1 (h3.trans (map_zero _).symm)
  by_contra h0
  have h5 := (hu i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)
  exact h5.ne_zero 0 h4

theorem levJ_le_dataLevel (t : T0) {Q : Finset (Pl D.host.E)} (hQ : Q ⊆ R.Q t) : levJ R i t ≤ dataLevel R i Q := by
  intro x hx
  exact ⟨⟨hx.1.1, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.1.2 PP) (hQ hP)⟩, hx.2⟩

theorem nabAtr_hLat_fg (g : Bridge.Gf (Vc D i)) : (nabAtr (labLL D) (lamV D i) (Bridge.hLat (Vc D i) g)).FG := by
  have hLat : Submodule.IsFullLattice D.host.E (Bridge.hLat (Vc D i) g) := by
    obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D (Vc D i)
    obtain ⟨Λ, hΛ, h1, h2, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E (Vc D i).rank (GlobalTheory.Member.latC (Vc D i)) g.1 hfg hsp
    rw [SetLike.coe_injective ((GlobalTheory.RepsCompare.coe_hLat (Vc D i) g).trans hΛ.symm)]
    letI : Submodule.IsLattice D.host.E Λ := Submodule.IsLattice.of_fg D.host.E h1
    exact { span_eq_top := h2 }
  exact (GlobalTheory.TransLattice.nabDelLattice _ _ _ _ _ fun τ => (GlobalTheory.dualFrLattice_holds D.what₂.LL _ 1 _ (by simp)
    (GlobalTheory.TauLat.tauLatLattice _ _ _ _ (labLL D) τ _ hLat)).1).1.fg

theorem coefTie_class {V : HSp D} {C : Bridge.CoefDat D V} {S : CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ}
    {P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ} {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W}
    {pair : VV D.what₂.LL lam →ₗ⋆[D.what₂.LL] VV D.what₂.LL lam →ₗ[D.what₂.LL] D.what₂.LL}
    {nab del : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) → Submodule (𝓞 D.what₂.LL) (VV D.what₂.LL lam)}
    (h : Bridge.CoefTie V C P lam c0 pair nab del) (c : S.Cl) :
    ((nab (Bridge.hLat V (P.y c))).FG → (S.Nab c).FG) ∧
      ∀ x ∈ nab (Bridge.hLat V (P.y c)), ∃ y ∈ S.Nab c, c0 x = P.coef y := by
  obtain ⟨e, -, h2, -, h4, -⟩ := h
  refine ⟨fun hf => ?_, fun x hx => ?_⟩
  · rw [← h4 c] at hf
    exact Submodule.fg_of_fg_map_injective (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) e.injective hf
  · rw [← h4 c] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, (h2 y).symm⟩

theorem exists_coef_fg (t : T0) (c : (A.MtCSD i t).Cl) {h : GA D (Vc D i)} (hh : fin (Vc D i) h = (R.B.L i t).pres.y c) :
    ∃ N : Submodule (𝓞 D.what₂.LL) (A.MtCSD i t).V, N.FG ∧
      ∀ w, InCoefLat R i h w → ∃ P ∈ N, w = (R.B.L i t).pres.coef P := by
  by_cases hex : ∃ w, InCoefLat R i h w
  · obtain ⟨-, gramR, c0R, c0L, hT, -⟩ := hex
    refine ⟨(A.MtCSD i t).Nab c, ?_, ?_⟩
    · exact (coefTie_class (hT.coefL i t) c).1 (nabAtr_hLat_fg _)
    · rintro w ⟨gramR', c0R', c0L', hT', P, hP, rfl⟩
      rw [hh] at hP
      exact (coefTie_class (hT'.coefL i t) c).2 P hP
  · exact ⟨⊥, Submodule.fg_bot, fun w hw => absurd ⟨w, hw⟩ hex⟩

theorem singleSeries_add (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (h : GA D (Vc D i)) (w w' : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    singleSeries R i ω φ h (w + w') v = singleSeries R i ω φ h w v + singleSeries R i ω φ h w' v := by
  funext g
  simp only [singleSeries, Datum.thetaKO, map_add (f := _), Pi.add_apply]

theorem singleSeries_smul (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (h : GA D (Vc D i)) (a : ℂ) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    singleSeries R i ω φ h (a • w) v = a • singleSeries R i ω φ h w v := by
  funext g
  simp only [singleSeries, Datum.thetaKO, map_smul, Pi.smul_apply]

theorem adForm_add (x y : Fin (R.nW i) → D.what₂.LL) : adForm R i (x + y) = adForm R i x + adForm R i y := by
  unfold adForm
  rw [map_add (f := _), map_add (f := _)]

theorem adForm_smul (a : D.what₂.LL) (x : Fin (R.nW i) → D.what₂.LL) : adForm R i (a • x) = D.what₂.embLL a • adForm R i x := by
  unfold adForm
  rw [LinearMap.map_smulₛₗ, map_smul]
  congr 1
  exact RingHom.congr_fun (sgAt_mk _ R.hv0) a

theorem seriesAt_fg (hd : FormsDetermined R i) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (ω : WeilRep D i)
    (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (t : T0) (c : (A.MtCSD i t).Cl) {h : GA D (Vc D i)}
    (hh : fin (Vc D i) h = (R.B.L i t).pres.y c) : (Submodule.span (𝓞 D.what₂.LL) (seriesAt R i U ψ ph ω φ h)).FG := by
  obtain ⟨N, hN, H⟩ := exists_coef_fg t c hh
  let cf : (A.MtCSD i t).V →ₛₗ[D.what₂.embLL] (R.cV i).W := (R.B.L i t).pres.coef
  let Γ : Submodule D.what₂.LL ((A.MtCSD i t).V × (Fin (R.nW i) → D.what₂.LL)) :=
    { carrier := {q | ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
        adForm R i q.2 (fun ρ => v ρ) = ph • levelTrace R i U ψ (singleSeries R i ω φ h (cf q.1) v)}
      add_mem' := fun {a b} ha hb v => by
        rw [Prod.fst_add, Prod.snd_add, adForm_add, map_add (f := _), singleSeries_add, map_add (f := _), smul_add, ← ha v, ← hb v]
        rfl
      zero_mem' := fun v => by
        have h1 := adForm_smul (R := R) (i := i) 0 0
        have h2 := singleSeries_smul (R := R) ω φ h 0 0 v
        rw [zero_smul, map_zero, zero_smul] at h1
        rw [zero_smul, zero_smul] at h2
        rw [Prod.fst_zero, Prod.snd_zero, h1, map_zero, h2, map_zero, smul_zero]
        rfl
      smul_mem' := fun a q hq v => by
        rw [Prod.smul_fst, Prod.smul_snd, adForm_smul, LinearMap.map_smulₛₗ, singleSeries_smul, map_smul, smul_comm, ← hq v]
        rfl }
  refine fg_of_graph hN (Γ.restrictScalars (𝓞 D.what₂.LL)) (fun x hx => hd x fun v => ?_) ?_
  · have h2 := singleSeries_smul (R := R) ω φ h 0 0 v
    rw [zero_smul, zero_smul] at h2
    have h3 : adForm R i x (fun ρ => v ρ) = ph • levelTrace R i U ψ (singleSeries R i ω φ h (cf 0) v) := hx v
    rw [h3, map_zero, h2, map_zero, smul_zero]
  · rintro x ⟨w, hw, hx⟩
    obtain ⟨P, hP, rfl⟩ := H w hw
    exact ⟨P, hP, hx⟩

theorem thetaBase_fg (hd : FormsDetermined R i) {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
    {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {p : ℕ} (hM : SpanOverClasses R i U ψ ph v p) : (thetaBase R i U ψ ph v p).FG := by
  classical
  by_cases hex : ∃ ω φ, IsBaseKernel R i v p ω φ
  · obtain ⟨ω, φ, hk⟩ := hex
    choose h hh using fun c => (GlobalTheory.RepsCompare.existsUnique_lift (Vc D i) ((R.B.L i (R.mu v)).pres.y c)).exists
    rw [hM ω φ hk _ h ⟨fun c => (hh c).1, fun x => ?_⟩, Submodule.span_iUnion]
    · exact Submodule.fg_iSup _ fun c => seriesAt_fg hd U ψ ph ω φ _ c (hh c).2
    · obtain ⟨c, γ, k, e⟩ := ((R.B.L i (R.mu v)).pres.reps x).exists
      exact ⟨c, γ, ⟨k, levJ_le_dataLevel (R.mu v) (Finset.filter_subset _ _) k.2⟩, by rw [(hh c).2]; exact e⟩
  · have : thetaBase R i U ψ ph v p = ⊥ := Submodule.span_eq_bot.2 fun x ⟨ω, φ, hk, _⟩ => absurd ⟨ω, φ, hk⟩ hex
    rw [this]
    exact Submodule.fg_bot

end Adelic

end GlobalTheory.TraceClassRank
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupSmoothCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupIsOpenIsCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupIsOpenIsCompact
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem grp_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsOpen (grp ψ) ∧ IsCompact (grp ψ) := by
  intro k _ _ _ _ n ψ hψ
  have hT := (triv_ev_props k).2.2.2.2.2.1
  have hS : ∀ i j, IsOpen {x : k | Triv (ψ i / ψ j) x} ∧ IsClosed {x : k | Triv (ψ i / ψ j) x} := fun i j => by
    refine hT _ ?_
    rw [div_eq_mul_inv]
    exact (hψ i).mul (hψ j).inv
  have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) k => g.val i j := fun i j =>
    by
    have h1 : Continuous fun g : GL (Fin n) k => (g.val : Matrix (Fin n) (Fin n) k) := Units.continuous_val
    exact (continuous_apply j).comp ((continuous_apply i).comp h1)
  have hE : grp ψ = (KO k (Fin n) : Set (GL (Fin n) k)) ∩
      ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), (fun g : GL (Fin n) k => g.val i j) ⁻¹' {x : k | Triv (ψ i / ψ j) x} := by
    ext g; simp [grp]
  rw [hE]
  refine ⟨GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_iInter_of_finite fun _ => (hS i j).1.preimage (hc i j)), ?_⟩
  exact GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => (hS i j).2.preimage (hc i j))

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupIsOpenIsCompactStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesCongruenceSubgroup_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsOpen (grp ψ) ∧ IsCompact (grp ψ) := by
  first | exact @GlobalTheory.PsType.grp_isOpen_isCompact | exact GlobalTheory.PsType.grp_isOpen_isCompact | (intros; apply GlobalTheory.PsType.grp_isOpen_isCompact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupSmoothCharacter
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem grp_theta_datum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Datum (grp ψ) (theta ψ) ∧ IsOpen (grp ψ) := by
  intro k _ _ _ _ n ψ hs ho
  have hoc := GlobalTheory.T.principalSeriesCongruenceSubgroup_isOpen_isCompact k n ψ hs
  have hnear := GlobalTheory.T.principalSeriesTypeCharacter_eq_one_near_one k n ψ hs
  have hone : (1 : GL (Fin n) k) ∈ grp ψ := by
    refine ⟨(KO k (Fin n)).one_mem, fun i j hij => ?_⟩
    have h0 : (1 : GL (Fin n) k).val i j = 0 := by
      simp [Matrix.one_apply_ne (ne_of_lt hij)]
    rw [h0]
    exact (GlobalTheory.T.isTrivialOnUnitsModConductor_unitCharacterValue_props k).2.2.1 _
  refine ⟨⟨hone, GlobalTheory.T.principalSeriesCongruenceSubgroup_mul_closed k n ψ ho, GlobalTheory.T.principalSeriesCongruenceSubgroup_inv_mem k n ψ ho, hoc.2, hnear.1,
    GlobalTheory.T.principalSeriesTypeCharacter_mul k n ψ ho, ?_⟩, hoc.1⟩
  obtain ⟨U, hU, hUt⟩ := hnear.2
  exact ⟨U, hU, fun g hg _ => hUt g hg⟩

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupSmoothCharacterStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesCongruenceSubgroup_smoothCharacterDatum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Datum (grp ψ) (theta ψ) ∧ IsOpen (grp ψ) := by
  first | exact @GlobalTheory.PsType.grp_theta_datum | exact GlobalTheory.PsType.grp_theta_datum | (intros; apply GlobalTheory.PsType.grp_theta_datum <;> assumption)
end
end
