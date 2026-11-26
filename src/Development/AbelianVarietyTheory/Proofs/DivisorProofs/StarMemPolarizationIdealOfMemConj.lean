module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolsOfEvaluatedColumnsHermitianMultSystem
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSide
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissible
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TestDataHaarFactorizationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermModerateGrowth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImageBirationalLinearSystemEqSelfInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

namespace GlobalTheory

open scoped Pointwise

namespace StarAAbar

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x :=
  D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])

theorem coe_smul {L : Type} [Field L] [NumberField L] (σ : Gal(L/ℚ)) (X : 𝓞 L) :
    ((σ • X : 𝓞 L) : L) = σ (X : L) := rfl

theorem bb_ne_bot {D : D7} : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h] at h1
  simp only [Submodule.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem conj_bb_ne_bot {D : D7} : D.host.conj • D.host.𝔟 ≠ ⊥ := by
  intro h
  apply bb_ne_bot (D := D)
  have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
  simpa using this

theorem conj_inv_smul {D : D7} (x : 𝓞 D.host.E) : D.host.conj⁻¹ • x = D.host.conj • x := by
  have h : D.host.conj⁻¹ = D.host.conj := by
    rw [inv_eq_iff_mul_eq_one]
    exact AlgEquiv.ext fun y => conj_conj D y
  rw [h]

end StarAAbar


set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 800000 in
theorem star_mem_AA_of_mem_AAbar : ∀ {D : D7} {c : D.host.E}, c ∈ D.host.AAbar → star c ∈ D.host.AA := by
  intro D c hc
  have hJ : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 StarAAbar.bb_ne_bot
  have hJc : ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 StarAAbar.conj_bb_ne_bot

  have h1 : ∀ y ∈ D.host.conj • D.host.𝔟, c * (y : D.host.E) ∈
      ((D.host.conj • D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro y hy
    have hyJ : (y : D.host.E) ∈ ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, rfl⟩
    have := FractionalIdeal.mul_mem_mul hc hyJ
    unfold Host.AAbar at this
    rwa [mul_assoc, inv_mul_cancel₀ hJc, mul_one] at this

  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) *
      ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤
      ((D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    obtain ⟨j', hj', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
    have hy : D.host.conj • j' ∈ D.host.conj • D.host.𝔟 := Ideal.smul_mem_pointwise_smul _ _ _ hj'
    obtain ⟨x, hx, hxe⟩ := (FractionalIdeal.mem_coeIdeal _).1 (h1 _ hy)
    have hxs : D.host.conj • x ∈ D.host.ccE := by
      have := (Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 hx
      rwa [StarAAbar.conj_inv_smul] at this
    have key : star c * algebraMap (𝓞 D.host.E) D.host.E j' = algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • x) := by
      show star c * (j' : D.host.E) = ((D.host.conj • x : 𝓞 D.host.E) : D.host.E)
      rw [StarAAbar.coe_smul, show ((x : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E x from rfl, hxe,
        map_mul, StarAAbar.coe_smul, StarAAbar.conj_conj, StarAAbar.star_eq_conj]
    rw [smul_mul_assoc, key]
    exact Submodule.smul_mem _ _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hxs, rfl⟩)
  have h3 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) ≤ D.host.AA := by
    unfold Host.AA Host.AA0
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c)
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) *
          ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
          ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hJ, mul_one]
      _ ≤ _ := by gcongr
  exact h3 (FractionalIdeal.mem_spanSingleton_self _ _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConjStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.star_mem_polarizationIdeal_of_mem_conj : ∀ {D : D7} {c : D.host.E}, c ∈ D.host.AAbar → star c ∈ D.host.AA := by
  first | exact @GlobalTheory.star_mem_AA_of_mem_AAbar | exact GlobalTheory.star_mem_AA_of_mem_AAbar | (intros; apply GlobalTheory.star_mem_AA_of_mem_AAbar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.QDom

open scoped Pointwise

theorem isFundamentalDomain_inf {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G}
    (hm : ∀ g : G, Measurable (g * ·)) (hinv : ∀ g : G, μ.map (g * ·) = μ)
    {Γ : Subgroup G} [Countable Γ] {D : Set G} (hD : IsFundamentalDomain Γ D μ) (S : Subgroup G) :
    ∃ 𝓓 : Set G, IsFundamentalDomain ↥(Γ ⊓ S) 𝓓 μ := by
  classical
  let Q' : Subgroup Γ := (Γ ⊓ S).subgroupOf Γ
  haveI : Countable (Γ ⧸ Q') := Function.Surjective.countable QuotientGroup.mk_surjective
  let rep : Γ ⧸ Q' → Γ := fun c => (Quotient.out c)⁻¹
  have hmp : ∀ g : G, MeasurePreserving (g * ·) μ μ := fun g => ⟨hm g, hinv g⟩
  have himg : ∀ (g : G) (s : Set G), g • s = (g⁻¹ * ·) ⁻¹' s := by
    intro g s; ext x; simp [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  have hnm : ∀ g : G, NullMeasurableSet (g • D) μ := fun g => by
    rw [himg]; exact hD.nullMeasurableSet.preimage (hmp g⁻¹).quasiMeasurePreserving
  refine ⟨⋃ c, ((rep c : Γ) : G) • D, ?_⟩
  refine IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_
  · exact NullMeasurableSet.iUnion fun c => hnm _
  · filter_upwards [hD.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Q' γ
    have hQ : ((h : Γ) : G) ∈ Γ ⊓ S := (Subgroup.mem_subgroupOf).1 h.2
    refine ⟨⟨((h : Γ) : G)⁻¹, inv_mem hQ⟩, Set.mem_iUnion.2 ⟨(γ : Γ ⧸ Q'), ?_⟩⟩
    rw [himg, Set.mem_preimage]
    have e1 : ((rep (γ : Γ ⧸ Q') : Γ) : G)⁻¹ = (γ : G) * ((h : Γ) : G) := by
      simp only [rep, inv_inv]
      have := congrArg (fun y : Γ => (y : G)) hh
      simpa using this
    rw [e1]
    have : (γ : G) * ((h : Γ) : G) * ((⟨((h : Γ) : G)⁻¹, inv_mem hQ⟩ : ↥(Γ ⊓ S)) • x) = γ • x := by
      rw [Subgroup.smul_def, Subgroup.smul_def]
      simp [smul_eq_mul, mul_assoc]
    rw [this]; exact hγ
  · intro g hg
    have hsm : g • ⋃ c, ((rep c : Γ) : G) • D = ⋃ c, ((g : G) * ((rep c : Γ) : G)) • D := by
      rw [Set.smul_set_iUnion]
      refine Set.iUnion_congr fun c => ?_
      rw [← smul_smul]; rfl
    rw [hsm, AEDisjoint.iUnion_left_iff]
    intro c
    rw [AEDisjoint.iUnion_right_iff]
    intro c'
    have hgΓ : (g : G) ∈ Γ := (Subgroup.mem_inf.1 g.2).1
    let γ₁ : Γ := ⟨g, hgΓ⟩ * rep c
    have hne : γ₁ ≠ rep c' := by
      intro heq
      have hmem : (Quotient.out c)⁻¹ * Quotient.out c' ∈ Q' := by
        rw [Subgroup.mem_subgroupOf]
        have : (Quotient.out c')⁻¹ = ⟨g, hgΓ⟩ * (Quotient.out c)⁻¹ := by
          simpa [γ₁, rep] using heq.symm
        have h2 : (Quotient.out c)⁻¹ * Quotient.out c' = (⟨g, hgΓ⟩ : Γ)⁻¹ := by
          rw [← inv_inj, mul_inv_rev, inv_inv, this, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
        rw [h2]
        simpa using inv_mem g.2
      have hcc : c = c' := by
        rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
        exact (QuotientGroup.eq).2 hmem
      subst hcc
      apply hg
      have : (⟨g, hgΓ⟩ : Γ) = 1 := by simpa [γ₁] using heq
      ext; simpa using congrArg Subtype.val this
    exact hD.aedisjoint hne
  · intro g
    exact (hmp (g : G)).quasiMeasurePreserving

end GlobalTheory.QDom

namespace GlobalTheory.QDom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem countable_numberField : Countable E :=
  Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  classical
  haveI := countable_numberField (E := E)
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  have hmat : Countable (GL (Fin n) E) := Function.Injective.countable (f := fun A : GL (Fin n) E => (A : Matrix (Fin n) (Fin n) E)) Units.val_injective
  have hpre : ∀ x : ratU σ J, ∃ A : GL (Fin n) E, Matrix.GeneralLinearGroup.map (inclR (AF F)) A = ((x : UA σ J) : GL (Fin n) (AE F E)) := by
    intro x
    have := x.2
    unfold ratU at this
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at this
    exact this
  choose f hf using hpre
  refine Function.Injective.countable (f := f) ?_
  intro x y hxy
  apply Subtype.ext; apply Subtype.ext
  rw [← hf x, ← hf y, hxy]

set_option synthInstance.maxHeartbeats 400000 in
theorem measurable_mul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) :
    Measurable (g * ·) := by
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  apply Continuous.measurable
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · simp only [Function.comp_def, Subgroup.coe_mul, Units.val_mul]
    exact continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  · simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul]
    exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_mul continuous_const

end GlobalTheory.QDom

namespace GlobalTheory.QDom

theorem exists_fundamentalDomain_ratStab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∃ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) 𝓓 G.M.μ := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' _ X om om' hT
  haveI := countable_ratU σ G.V.J
  have hgood := hT.geo.hM
  haveI := hgood.haar
  exact isFundamentalDomain_inf (measurable_mul_left σ G.V.J) (fun g => map_mul_left_eq_self G.M.μ g) hgood.dom _

end GlobalTheory.QDom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBlockCongruenceLevelSubgroupIffStabilizerEntr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBlockCongruenceLevelSubgroupIffStabilizerEntr
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.BlockMem

variable {D : D7}

theorem hatId_mul_mem (𝔪 : Ideal (𝓞 D.host.E)) {x y : AE D} (hx : x ∈ hatId D 𝔪) (hy : y ∈ OhE D) :
    x * y ∈ hatId D 𝔪 := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨b, hb, s * y, mul_mem hs hy, by ring⟩
  | zero => simp [zero_mem]
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_mul]; exact neg_mem hu

def hatIdeal (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) : Ideal (OhE D) where
  carrier := {x | (x : AE D) ∈ hatId D 𝔪}
  add_mem' := fun {x y} hx hy => by
    show ((x : AE D) + (y : AE D)) ∈ hatId D 𝔪
    exact add_mem hx hy
  zero_mem' := by
    show ((0 : OhE D) : AE D) ∈ hatId D 𝔪
    exact zero_mem _
  smul_mem' := fun c x hx => by
    show (c : AE D) * (x : AE D) ∈ hatId D 𝔪
    rw [mul_comm]; exact hatId_mul_mem 𝔪 hx c.2

def liftM {d : ℕ} (g : Matrix (Fin d) (Fin d) (AE D)) (hg : ∀ i j, g i j ∈ OhE D) :
    Matrix (Fin d) (Fin d) (OhE D) :=
  Matrix.of fun i j => ⟨g i j, hg i j⟩

theorem liftM_map {d : ℕ} (g : Matrix (Fin d) (Fin d) (AE D)) (hg : ∀ i j, g i j ∈ OhE D) :
    (liftM g hg).map (OhE D).subtype = g := by
  ext i j; rfl

def blk (a : ℕ) {d : ℕ} (i : Fin d) : ℕ := if a ≤ i.1 then 1 else 0

theorem blk_lt {a d : ℕ} (i j : Fin d) : blk a j < blk a i ↔ j.1 < a ∧ a ≤ i.1 := by
  unfold blk; split_ifs <;> omega

theorem cond_iff {d : ℕ} (𝔪 : Ideal (𝓞 D.host.E)) (a : ℕ) (g : Matrix (Fin d) (Fin d) (AE D))
    (hg : ∀ i j, g i j ∈ OhE D) :
    (∀ i j : Fin d, j.1 < a → a ≤ i.1 → g i j ∈ hatId D 𝔪) ↔
      ((liftM g hg).map (Ideal.Quotient.mk (hatIdeal D 𝔪))).BlockTriangular (blk a) := by
  constructor
  · intro h i j hij
    rw [blk_lt] at hij
    simp only [Matrix.map_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact h i j hij.1 hij.2
  · intro h i j hj hi
    have := h ((blk_lt i j).2 ⟨hj, hi⟩)
    simp only [Matrix.map_apply] at this
    exact (Ideal.Quotient.eq_zero_iff_mem).1 this

theorem bt_transfer {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    {X Y : Matrix (Fin d) (Fin d) R} (h : Y * X = 1) (b : Fin d → ℕ) (hX : (X.map f).BlockTriangular b) :
    (Y.map f).BlockTriangular b := by
  have h' : Y.map f * X.map f = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ f.map_zero f.map_one]
  letI : Invertible (X.map f) := ⟨Y.map f, h', mul_eq_one_comm.mp h'⟩
  have := Matrix.blockTriangular_inv_of_blockTriangular hX
  rwa [Matrix.inv_eq_left_inv h'] at this

theorem mem_iff (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) (h : GA D d) :
    h ∈ blockLev D 𝔪 d a ↔ h ∈ intG D d ∧ ∀ i j : Fin d, j.1 < a → a ≤ i.1 →
      ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪 := by
  refine ⟨fun hh => ?_, fun hh => Subgroup.subset_closure hh⟩
  induction hh using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one =>
    refine ⟨one_mem _, fun i j hj hi => ?_⟩
    have hne : i ≠ j := fun e => by subst e; omega
    simp [Matrix.one_apply_ne hne, zero_mem]
  | mul x y _ _ hx hy =>
    refine ⟨mul_mem hx.1 hy.1, fun i j hj hi => ?_⟩
    have ix := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    have iy := (GlobalTheory.NormSum.mem_intG y).1 hy.1
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    by_cases hl : l.1 < a
    · exact hatId_mul_mem 𝔪 (hx.2 i l hl hi) (iy l j).1
    · rw [mul_comm]
      exact hatId_mul_mem 𝔪 (hy.2 l j hj (not_lt.1 hl)) (ix i l).1
  | inv x _ hx =>
    refine ⟨inv_mem hx.1, ?_⟩
    have ix := (GlobalTheory.NormSum.mem_intG x).1 hx.1
    have hX : ∀ i j, ((x : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ OhE D :=
      fun i j => (ix i j).1
    have hY : ∀ i j, (((x⁻¹ : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ OhE D :=
      fun i j => by simpa using (ix i j).2
    rw [cond_iff 𝔪 a _ hY]
    have hXc := (cond_iff 𝔪 a _ hX).1 hx.2
    set X := liftM _ hX
    set Y := liftM _ hY
    have hYX : Y * X = 1 := by
      have key : (Y * X).map (OhE D).subtype = (1 : Matrix (Fin d) (Fin d) (OhE D)).map (OhE D).subtype := by
        rw [Matrix.map_mul, liftM_map, liftM_map, Matrix.map_one _ (map_zero _) (map_one _)]
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
        rfl
      exact Matrix.map_injective (fun u v huv => Subtype.ext huv) key
    exact bt_transfer (Ideal.Quotient.mk (hatIdeal D 𝔪)) hYX (blk a) hXc

end GlobalTheory.FunObj.StdDatum.BlockMem

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBlockCongruenceLevelSubgroupIffStabilizerEntrStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_blockCongruenceLevelSubgroup_iff_stabilizer_entries : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (d a : ℕ) (h : GA D d), h ∈ blockLev D 𝔪 d a ↔ h ∈ intG D d ∧ ∀ i j : Fin d, j.1 < a → a ≤ i.1 → ((h : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) i j ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff | exact GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff | (intros; apply GlobalTheory.FunObj.StdDatum.BlockMem.mem_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteCombinationMulLiftByDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteCombinationMulLiftByDegree
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SmallRoute

theorem setIntegral_mul_right_of_left_inv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] (Γ : Subgroup H) [Countable Γ] (ν : Measure H)
    [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] {fd : Set H} (hfd : IsFundamentalDomain Γ fd ν) {φ : H → ℂ}
    (hφ : ∀ γ ∈ Γ, ∀ u, φ (γ * u) = φ u) (hi : IntegrableOn φ fd ν) (k : H) :
    IntegrableOn (fun u => φ (u * k)) fd ν ∧ ∫ u in fd, φ (u * k) ∂ν = ∫ u in fd, φ u ∂ν := by
  have hmp : MeasurePreserving (· * k) ν ν := measurePreserving_mul_right ν k
  have hme : MeasurableEmbedding (· * k) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd' : IsFundamentalDomain Γ ((· * k⁻¹) ⁻¹' fd) ν := by
    refine hfd.preimage_of_equiv (measurePreserving_mul_right ν k⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ g : Γ, ∀ x, φ (g • x) = φ x := fun g x => hφ g g.2 x
  have hpre : (· * k) ⁻¹' ((· * k⁻¹) ⁻¹' fd) = fd := by
    ext u; simp
  refine ⟨?_, ?_⟩
  · have h1 : IntegrableOn φ ((· * k⁻¹) ⁻¹' fd) ν := (hfd'.integrableOn_iff hfd hinv).2 hi
    have h2 := (hmp.integrableOn_comp_preimage hme (f := φ) (s := (· * k⁻¹) ⁻¹' fd)).2 h1
    rw [hpre] at h2
    exact h2
  · have h3 := hmp.setIntegral_preimage_emb hme φ ((· * k⁻¹) ⁻¹' fd)
    rw [hpre] at h3
    rw [h3]
    exact hfd'.setIntegral_eq hfd hinv

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem mem_support_tensT (W : G.Weil) {X Y : Node} {p : Path T X Y} {τi : PolT G p →₀ ℂ} {τf : TotT G p} {d : PureT G p}
    (hd : d ∈ (tensT W τi τf).support) :
    ∃ d₀ ∈ τf.support, ∃ P, d = Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d₀ P := by
  classical
  unfold tensT at hd
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d₀, hd₀, h⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  exact ⟨d₀, hd₀, P, Finset.mem_singleton.1 (Finsupp.support_single_subset h)⟩

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem theta_of_matched {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (hΘ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeSmall t i j)} (hd : d ∈ Θ'.support) :
    IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 := by
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := mem_support_tensT W hd
  obtain ⟨h1, h2⟩ := hloc d₀ hd₀
  have v1 := ρ.vT_is t i j i.2.le j.2
  have v2 := ρ.vX_is i j i.2 j.2.le
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  have t2 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h2.2 v2.2.theta
  exact ⟨GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _,
    GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _⟩

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem outer_left (W : G.Weil) (M : Vol G) {t : T} {i j : Fin D.R.m} {d : PureT G (routeSmall t i j)}
    (h2 : IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2)
    (h1 : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2) (F : Fn G (.grid i (j + 1)))
    (g₁ : GA D (G.V (.grid (i + 1) j))) {γ : GA D (G.V (.grid i j))} (hγ : γ ∈ GQ (G.V (.grid i j)))
    (u : GA D (G.V (.grid i j))) : outer W M d F g₁ (γ * u) = outer W M d F g₁ u := by
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  have hm := W.om_is (.mu t (i : ℕ) j) ⟨i.2.le, j.2⟩
  unfold outer
  congr 1
  · show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (γ * u) d.2 = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u d.2
    unfold thetaKO
    have e : ((negGA _ g₁, γ * u) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) =
        (1, γ) * (negGA _ g₁, u) := by simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h2)
  · refine integral_congr_ae (.of_forall fun g => ?_)
    show thetaKO (W.om (.mu t (i : ℕ) j)) (γ * u) g d.1.2 * F g = thetaKO (W.om (.mu t (i : ℕ) j)) u g d.1.2 * F g
    unfold thetaKO
    have e : ((γ * u, g) : GA D (G.pS (.mu t (i : ℕ) j)) × GA D (G.pT (.mu t (i : ℕ) j))) = (γ, 1) * (u, g) := by simp
    rw [e, map_mul, Module.End.mul_apply, hm.om_aut γ hγ 1 (one_mem _) _ (hm.om_pres _ _ h1)]

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

theorem zdeg_mul_liftT : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j)))
    (z : GA D (G.V (.grid i j)) →₀ ℂ),
    (∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    zdeg z * liftT W M (routeSmall t i j) Θ' F g₁ =
      Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ F hF hB g₁ z
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid i j))
  haveI := hH
  haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ (M.ν (.grid i j)) hH
  have key : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j)) ∧
      ∫ u in M.fd (.grid i j), outer W M d F g₁ (u * k) ∂M.ν (.grid i j) =
        ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := fun d hd k => by
    obtain ⟨h2, h1⟩ := theta_of_matched hΘ hd
    refine setIntegral_mul_right_of_left_inv (GQ (G.V (.grid i j))) (M.ν (.grid i j)) hfd
      (fun γ hγ u => outer_left W M h2 h1 F g₁ hγ u) ?_ k
    exact (hB d hd).2 g₁
  refine ⟨fun d hd k => (key d hd k).1, ?_⟩
  rw [liftT_routeSmall, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have e : ∫ u in M.fd (.grid i j), translates z (outer W M d F g₁) u ∂M.ν (.grid i j) =
      zdeg z * ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := by
    unfold translates zdeg
    simp only [Finsupp.sum]
    rw [integral_finsetSum _ fun k _ => ((key d hd k).1.integrable.const_mul _),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, (key d hd k).2]
  rw [e]
  ring

end GlobalTheory.SmallRoute
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteCombinationMulLiftByDegreeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallRoute_combination_mul_lift_by_degree : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j)))
    (z : GA D (G.V (.grid i j)) →₀ ℂ),
    (∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    zdeg z * liftT W M (routeSmall t i j) Θ' F g₁ =
      Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j) := by
  first | exact @GlobalTheory.SmallRoute.zdeg_mul_liftT | exact GlobalTheory.SmallRoute.zdeg_mul_liftT | (intros; apply GlobalTheory.SmallRoute.zdeg_mul_liftT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleCoordinatesGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleCoordinatesGenericPoint
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points

namespace GlobalTheory.GenericCoords

theorem exists_affine_etale_coords : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧
      ∃ t : Fin D → Γ(X, U), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) t).Etale := by
  intro k _ X _ p D h
  obtain ⟨U, t, hU, hη, he⟩ := GlobalTheory.GenericEtale.exists_etale_coords h
  exact ⟨U, hU, hη, t, he⟩

end GlobalTheory.GenericCoords
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleCoordinatesGenericPointStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_etale_coordinates_generic_point : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ ∃ t : Fin D → Γ(X, U), (MvPolynomial.eval₂Hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U) t).Etale := by
  first | exact @GlobalTheory.GenericCoords.exists_affine_etale_coords | exact GlobalTheory.GenericCoords.exists_affine_etale_coords | (intros; apply GlobalTheory.GenericCoords.exists_affine_etale_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NullstellensatzPointOfSystem
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry CategoryTheory

open GlobalTheory.CompHt

namespace GlobalTheory.ConeOnto

theorem exists_rat_pt {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (f : X ⟶ Sp K) [LocallyOfFiniteType f]
    {Z : Set X} (hZ : IsLocallyClosed Z) {x : X} (hx : x ∈ Z) :
    ∃ a : Sp K ⟶ X, a ≫ f = 𝟙 _ ∧ ∀ w, a w ∈ Z := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ hZ
  replace hc : IsClosed {c} := hc
  exact ⟨pointOfClosedPoint f c hc, pointOfClosedPoint_comp _ _ _, fun w => by rw [pointOfClosedPoint_apply]; exact hcZ⟩

end GlobalTheory.ConeOnto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConj
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RealPlaceConj

theorem piInf_cA_eq_star : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piInf τ (cA σ z) = star (piInf τ z) := by
  intro F E _ _ _ _ _ σ hσ w τ z

  have hcomp : compInf F E w (cA σ z) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compInf F E w z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp [cA, compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

  change infEmb τ (compInf F E w (cA σ z)) = star (infEmb τ (compInf F E w z))
  rw [hcomp, ← GlobalTheory.AdelicU.infEmb_sigR hσ τ]
  rfl

end GlobalTheory.RealPlaceConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConjStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceComponent_adeleConjugation_eq_complexConj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), piInf τ (cA σ z) = star (piInf τ z) := by
  first | exact @GlobalTheory.RealPlaceConj.piInf_cA_eq_star | exact GlobalTheory.RealPlaceConj.piInf_cA_eq_star | (intros; apply GlobalTheory.RealPlaceConj.piInf_cA_eq_star <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

variable {D : D7} {T : Type} {A A' WW : HSp D}

def reRig (Y : Tri T A A' WW) (rA : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig A) (rA' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig A') (rW : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig WW)
    (f : T → WO A WW → ℂ) (f' : T → WO A' WW → ℂ) : Tri T A A' WW :=
  { Y with rA := rA, rA' := rA', rW := rW, f := f, f' := f' }

abbrev botAlpha (L : LevCh D T) (i j : Fin D.R.m) (t : T) : (AE D)ˣ →* Circle :=
  L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)

abbrev botBeta {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : Fin D.R.m) : (AE D)ˣ →* Circle :=
  G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)

theorem isStd_lat_eq {V : HSp D} {r r' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) (h' : r'.IsStd) : r.Λ = r'.Λ := by
  ext y
  rw [h.2.1, h'.2.1]

theorem isStd_s_eq {V : HSp D} {r r' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) (h' : r'.IsStd) : r.s = r'.s :=
  funext fun τ => (h.2.2 τ).1.trans (h'.2.2 τ).1.symm

theorem isStd_B_eq {V : HSp D} {r r' : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) (h' : r'.IsStd) : r.B = r'.B :=
  funext fun τ => (h.2.2 τ).2.trans (h'.2.2 τ).2.symm

end GlobalTheory.BotFrames

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTerms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTerms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem irrUnitary_trace_ne_zero_copyFinDS : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ (GfC V) W), σ.IsIrreducible ∧ IsAdmissible σ ∧ IsCopyFinDS σ M π ⊤ ∧ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c := by
  intro hDS hFl hHC hPC D V lam S M T U μa μf μ _ _ fa ff hTD ν hν H _ _ _ π hπ c hc hc0
  have hcomp : HasDSComp M π := GlobalTheory.T.discrete_series_spectral_side hDS hFl hHC hPC D V lam S M T U μa μf μ fa ff hTD H π hπ c hc hc0
  have hU : GlobalTheory.AutomorphicL2Unitary.IsSubrep π ⊤ := GlobalTheory.AutomorphicL2Unitary.isSubrep_top
  have hcopy := GlobalTheory.T.irreducibleUnitaryRep_eq_finiteSmoothPart_tensor_discreteSeries D V S M H π hπ hcomp hU
  obtain ⟨hirr, hadm⟩ := GlobalTheory.T.finite_part_irreducible_admissible hFl D V S M H π hπ hcomp hU
  haveI : ν.IsHaarMeasure := hν.1
  have hfam : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hTD.2.2.2.2.2.2.isFinFamily
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V ν ff hfam _ (finPartDSSm M hU) hadm
  have hπc' := GlobalTheory.T.test_data_haar_factorization D V lam S M T U μa μf μ fa ff hTD ν hν H π hπ _ (finPartDSSm M hU) hirr hadm hcopy c' hc'
  have hcc : c' = c := hπc'.2.symm.trans hc.2
  subst hcc
  exact ⟨_, _, _, finPartDSSm M hU, hirr, hadm, hcopy, hc'⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTermsStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_series_model_trace_terms : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (σ : Representation ℂ (GfC V) W), σ.IsIrreducible ∧ IsAdmissible σ ∧ IsCopyFinDS σ M π ⊤ ∧ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c := by
  first | exact @GlobalTheory.irrUnitary_trace_ne_zero_copyFinDS | exact GlobalTheory.irrUnitary_trace_ne_zero_copyFinDS | (intros; apply GlobalTheory.irrUnitary_trace_ne_zero_copyFinDS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagNeZeroOfLinearIndependent
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt

section Lat

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {n : ℕ}

theorem diag_ne_zero_of_linearIndependent {w : Fin n → U} {g : Matrix (Fin n) (Fin n) C}
    (hg : ∀ i j, i < j → g i j = 0) (h : LinearIndependent C fun i => ∑ j, g i j • w j) (i : Fin n) : g i i ≠ 0 := by
  have hl : LinearIndependent C g.row := LinearIndependent.of_comp (Fintype.linearCombination C w) h
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hl)
  rw [Matrix.det_of_lowerTriangular _ fun i j hij => hg i j hij] at hu
  exact Finset.prod_ne_zero_iff.1 hu.ne_zero i (Finset.mem_univ i)

theorem IsLatBasis.diag_le {v : Valuation C ℝ≥0} (hv : v.Integers O) {La : Submodule O U} {w : Fin n → U}
    {g g' : Matrix (Fin n) (Fin n) C} (hg : ∀ i j, i < j → g i j = 0) (hg' : ∀ i j, i < j → g' i j = 0)
    (h : IsLatBasis C La fun i => ∑ j, g i j • w j) (i : Fin n) (h' : ∑ j, g' i j • w j ∈ La) :
    v (g' i i) ≤ v (g i i) := by
  have hd : IsUnit g.det := lowerTri_isUnit_det g hg fun i => (diag_ne_zero_of_linearIndependent hg h.1 i).isUnit
  have e : (g' * g⁻¹) * g = g' := Matrix.nonsing_inv_mul_cancel_right _ _ hd
  have e1 : ∑ j, (g' * g⁻¹) i j • ∑ k, g j k • w k = ∑ k, g' i k • w k := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul, ← Matrix.mul_apply, e]
  obtain ⟨b, hb⟩ := (h.sum_mem_iff ((g' * g⁻¹) i)).1 (e1 ▸ h') i
  have e2 := lowerTri_mul_diag _ _ (lowerTri_mul _ _ hg' (lowerTri_inv g hg hd)) hg i
  rw [e] at e2
  rw [e2, map_mul, ← hb]
  exact mul_le_of_le_one_left' (hv.map_le_one b)

theorem IsLatBasis.mem {La : Submodule O U} {w : Fin n → U} (h : IsLatBasis C La w) (i : Fin n) : w i ∈ La :=
  (h.2.le (Submodule.subset_span ⟨i, rfl⟩)).1

end Lat

attribute [local instance] algPadicInt algPadicField towerPadic factPadic PadicComplexHost.isAdicComplete

end GlobalTheory.CompHt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementTorusPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Gen

variable {R : Type} [CommRing R] {n : ℕ} (c : R →+* R) (J : Matrix (Fin n) (Fin n) R)

def fR (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ (fun i => c (v i))

variable {c J}
variable {x y : Fin n → R} (hxx : fR c J x x = 0) (hyy : fR c J y y = 0) (hxy : fR c J x y = 1)
  (hyx : fR c J y x = -1)
include hxx hyy hxy hyx

end Gen

end GlobalTheory.AdelicPlaneLevi

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem sigma_invol {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

end Main

end GlobalTheory.AdelicPlaneLevi

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefAndIsBig
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

namespace GlobalTheory.BirationalBig

theorem isNef_and_isBig : Quoted → ∀ (F : Type) [Field F] [NumberField F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → IsNef F S.L ∧ IsBig F S.L := by
  intro Q F _ _ S hV hb hB
  have hstr : strHom F S.Y = S.str := strHom_eq fun _ => rfl
  have hproj : IsProjOver (strHom F (X := S.Y)) := hstr ▸ hV.proj
  have hnef : IsNef F S.L := IsGenerated.isNef_of_isProjOver ⟨S.N, S.b, hb⟩ hV.proj
  exact ⟨hnef, (Q.nef.2.2.isBig_iff hproj (GlobalTheory.ImageDegree.topologicalKrullDim_eq S hV) hnef).2
    (GlobalTheory.ImageDegree.degree_image_eq_topSelf Q F S hV hb hB).1⟩

end GlobalTheory.BirationalBig
end
