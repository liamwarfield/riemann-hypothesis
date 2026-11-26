module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHcharPrescribedTrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneRelUnique
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwChainWtSharpDivDe
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsQuadraticCharOfSplitTwoGroup
open scoped commutatorElement Pointwise

namespace GlobalTheory

theorem normal_of_commutator_le {G : Type} [Group G] (M : Subgroup G)
    (h : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ M) : M.Normal := by
  constructor
  intro n hn g
  have h1 : ⁅g, n⁆ ∈ M :=
    h (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
  have h2 := M.mul_mem h1 hn
  simpa [commutatorElement_def] using h2

end GlobalTheory

namespace GlobalTheory

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletion
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL GlobalTheory.SmGL

namespace GlobalTheory.AbStep

theorem loc_char : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v) (a : Weil h →* (v.adicCompletion F)ˣ), IsLocalArtin h a → ∀ χ : Dec (F := F) A →* ℂˣ, IsOpen (χ.ker : Set (Dec (F := F) A)) → ∃ θ : (v.adicCompletion F)ˣ →* ℂˣ, IsSmoothChar θ ∧ (∃ N : ℕ, 0 < N ∧ θ ^ N = 1) ∧ ∀ σ : Weil h, θ (a σ) = χ (Subgroup.inclusion (Weil_le_Dec h) σ) := by
  intro Ω _ F _ _ _ _ A v h a ha χ hχ
  classical
  let ξ : Weil h →* ℂˣ := χ.comp (Subgroup.inclusion (Weil_le_Dec h))
  have hξ : GlobalTheory.WeilDeligne.IsSmooth ξ := by
    have hc : Continuous (fun σ : Ine (F := F) A =>
        (⟨(σ : G F Ω), Weil_le_Dec h (Ine_le_Weil h σ.2)⟩ : Dec (F := F) A)) :=
      continuous_subtype_val.subtype_mk _
    exact hχ.preimage hc
  obtain ⟨θ, hθs, hθ⟩ := ha.factor ξ hξ
  have hfi : χ.ker.FiniteIndex := GlobalTheory.LocVec.finiteIndex_of_isOpen (Dec (F := F) A)
    (ReciprocityTheory.Gal.isClosed_Dec A).isCompact subset_rfl χ.ker hχ
  refine ⟨θ, hθs, ⟨χ.ker.index, Nat.pos_of_ne_zero hfi.index_ne_zero, ?_⟩, fun σ => ?_⟩
  · refine MonoidHom.ext fun x => ?_
    obtain ⟨σ, rfl⟩ := ha.surj x
    have hm := Subgroup.pow_index_mem χ.ker (Subgroup.inclusion (Weil_le_Dec h) σ)
    rw [MonoidHom.mem_ker, map_pow] at hm
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← MonoidHom.comp_apply θ a, ← hθ]
    exact hm
  · exact (DFunLike.congr_fun hθ σ).symm

theorem gal_char : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (art : Ideles F →* Gab F Ω), IsGlobalArtin art → ∀ η : HChar F, (∃ n : ℕ, 0 < n ∧ η.OrderDvd n) → (∀ u : InfinitePlace F, η.locInf u = 1) → ∃ ρ : Gab F Ω →* ℂˣ, IsOpen (ρ.ker : Set (Gab F Ω)) ∧ ∀ x, ρ (art x) = η.1 x := by
  intro F Ω _ _ _ _ art ha η hηf _
  obtain ⟨n, hn, hηn⟩ := hηf
  have hpow : ∀ x, η.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar F => ξ.1 x) hηn
  have hko : IsOpen (η.1.ker : Set (Ideles F)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow η.1 η.2.1 hn hpow
  have hinf : infConn F ≤ η.1.ker := by
    let ι : (InfiniteAdeleRing F)ˣ →* Ideles F :=
      Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
    have hιc : Continuous ι := Continuous.units_map _ (continuous_id.prodMk continuous_const)
    have hO : IsOpen ((η.1.ker.comap ι : Subgroup _) : Set (InfiniteAdeleRing F)ˣ) := hko.preimage hιc
    rintro _ ⟨y, hy, rfl⟩
    exact (IsClopen.connectedComponent_subset ⟨Subgroup.isClosed_of_isOpen _ hO, hO⟩
      (Subgroup.one_mem _)) hy
  have hker : art.ker ≤ η.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ hinf) (η.1.ker.isClosed_of_isOpen hko)
    rintro _ ⟨k, rfl⟩
    exact η.2.2 k
  have hs : Function.Surjective art := ha.quot.surjective
  let e := QuotientGroup.quotientKerEquivOfSurjective art hs
  let ρ : Gab F Ω →* ℂˣ := (QuotientGroup.lift art.ker η.1 hker).comp e.symm.toMonoidHom
  have hρ : ∀ x, ρ (art x) = η.1 x := fun x => by
    have he : e.symm (art x) = (x : Ideles F ⧸ art.ker) := e.symm_apply_eq.2 rfl
    show QuotientGroup.lift art.ker η.1 hker (e.symm (art x)) = _
    rw [he]
    rfl
  refine ⟨ρ, ?_, hρ⟩
  have hk : (ρ.ker : Set (Gab F Ω)) = art '' (η.1.ker : Set (Ideles F)) := by
    ext g
    obtain ⟨x, rfl⟩ := hs g
    constructor
    · intro hg
      exact ⟨x, by rw [SetLike.mem_coe, MonoidHom.mem_ker, ← hρ]; exact hg, rfl⟩
    · rintro ⟨y, hy, e'⟩
      show ρ _ = 1
      rw [← e', hρ]
      exact hy
  rw [hk]
  exact ha.quot.isOpenMap _ hko

end GlobalTheory.AbStep

namespace GlobalTheory.AbStep

theorem one_char (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v)
    (χ : Dec (F := F) A →* ℂˣ) (hχ : IsOpen (χ.ker : Set (Dec (F := F) A)))
    (T : Finset (HeightOneSpectrum (𝓞 F))) (hT : v ∉ T) :
    ∃ r : G F Ω →* ℂˣ, IsOpen (r.ker : Set (G F Ω)) ∧ (∀ g : Dec (F := F) A, r g = χ g) ∧
      (∀ (j : Ω →+* ℂ) (c : G F Ω), (∀ x, j (c x) = starRingEnd ℂ (j x)) → r c = 1) ∧
      ∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → ∀ g ∈ Dec (F := F) A', r g = 1 := by
  classical
  obtain ⟨art, ha⟩ := GlobalTheory.globalArtinReciprocity_holds F Ω
  obtain ⟨a, haL⟩ := GlobalTheory.localArtinExists_holds F Ω A v h
  obtain ⟨θ, hθs, hθf, hθ⟩ := loc_char Ω F A v h a haL χ hχ
  have hne : ∀ u ∈ T, u ≠ v := fun u hu e => hT (e ▸ hu)
  obtain ⟨η, hηf, hηi, hηl⟩ := GlobalTheory.DelEps.Twist.exists_hchar_prescribed F (insert v T)
    (Function.update (fun _ => 1) v θ)
    (fun w hw => by
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rw [Function.update_self]; exact hθs
      · rw [Function.update_of_ne (hne w hw)]
        unfold IsSmoothChar
        simp)
    (fun w hw => by
      rcases Finset.mem_insert.1 hw with rfl | hw
      · rw [Function.update_self]; exact hθf
      · rw [Function.update_of_ne (hne w hw)]
        exact ⟨1, one_pos, one_pow _⟩)
  have hηv : η.loc v = θ := by rw [hηl v (Finset.mem_insert_self _ _), Function.update_self]
  have hηT : ∀ u ∈ T, η.loc u = 1 := fun u hu => by
    rw [hηl u (Finset.mem_insert_of_mem hu), Function.update_of_ne (hne u hu)]
  obtain ⟨ρ, hρo, hρ⟩ := gal_char F Ω art ha η hηf hηi
  let r : G F Ω →* ℂˣ := ρ.comp (toAb F Ω)
  have hro : IsOpen (r.ker : Set (G F Ω)) :=
    hρo.preimage (QuotientGroup.isQuotientMap_mk _).continuous
  have hW : ∀ σ : Weil h, r σ = χ (Subgroup.inclusion (Weil_le_Dec h) σ) := fun σ => by
    show ρ (toAb F Ω σ) = _
    rw [← haL.glob art ha σ, hρ, ← hθ σ, ← hηv]
    rfl
  have hD : ∀ g : Dec (F := F) A, r g = χ g := by
    intro g
    obtain ⟨O, hOo, hO⟩ := isOpen_induced_iff.1 hχ
    have h1 : (1 : G F Ω) ∈ O := by
      have : (1 : Dec (F := F) A) ∈ (χ.ker : Set (Dec (F := F) A)) := χ.ker.one_mem
      rw [← hO] at this
      exact this
    obtain ⟨L, hLf, hLs⟩ := (krullTopology_mem_nhds_one_iff F Ω _).1
      ((hro.inter hOo).mem_nhds ⟨r.ker.one_mem, h1⟩)
    obtain ⟨τ, hτ⟩ := GlobalTheory.ConjWD.exists_weil_eq_on (h := h) g.2 L
    have hfix : (τ : G F Ω)⁻¹ * g ∈ L.fixingSubgroup := fun x => by
      show ((τ : G F Ω)⁻¹ * (g : G F Ω)) x = x
      rw [AlgEquiv.mul_apply, ← hτ x x.2]
      show ((τ : G F Ω)⁻¹ * τ) x = x
      simp
    obtain ⟨hr1, hO1⟩ := hLs hfix
    have hk : (Subgroup.inclusion (Weil_le_Dec h) τ)⁻¹ * g ∈ χ.ker := by
      have : (Subgroup.inclusion (Weil_le_Dec h) τ)⁻¹ * g ∈ (Subtype.val ⁻¹' O : Set (Dec (F := F) A)) := hO1
      rw [hO] at this
      exact this
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk
    have hr1' : r ((τ : G F Ω)⁻¹ * g) = 1 := hr1
    rw [map_mul, map_inv, inv_mul_eq_one] at hr1'
    rw [← hr1', hW τ, hk]
  refine ⟨r, hro, hD, fun j c hc => ?_, fun u hu A' hA' g hg => ?_⟩
  · show ρ (toAb F Ω c) = 1
    rw [← GlobalTheory.HilbertFromArtin.art_sign_eq ha j c hc, hρ]
    exact DFunLike.congr_fun (hηi _) (-1)
  · have hm : toAb F Ω g ∈ (art.comp (localIdele F u)).range.topologicalClosure := by
      rw [ha.dec u A' hA']
      exact ⟨g, hg, rfl⟩
    have hle : (art.comp (localIdele F u)).range ≤ ρ.ker := by
      rintro _ ⟨x, rfl⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hρ]
      exact DFunLike.congr_fun (hηT u hu) x
    exact Subgroup.topologicalClosure_minimal _ hle (ρ.ker.isClosed_of_isOpen hρo) hm

end GlobalTheory.AbStep

namespace GlobalTheory.AbStep

theorem exists_abelian_real_field : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v) (V : Subgroup (Dec (F := F) A)), IsOpen (V : Set (Dec (F := F) A)) → commutator (Dec (F := F) A) ≤ V → ∀ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T → ∃ F₁ : IntermediateField F Ω, FiniteDimensional F F₁ ∧ IsAbelianGalois F F₁ ∧ (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) ∧ (∀ g : Dec (F := F) A, (g : G F Ω) ∈ F₁.fixingSubgroup ↔ g ∈ V) ∧ ∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := F) A' ≤ F₁.fixingSubgroup := by
  intro Ω _ F _ _ _ _ _ A v h V hVo hVc T hvT
  haveI : V.Normal := GlobalTheory.normal_of_commutator_le V hVc
  haveI : V.FiniteIndex := GlobalTheory.LocVec.finiteIndex_of_isOpen (Dec (F := F) A) (ReciprocityTheory.Gal.isClosed_Dec A).isCompact subset_rfl V hVo
  letI : CommGroup (Dec (F := F) A ⧸ V) := { (inferInstance : Group (Dec (F := F) A ⧸ V)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply hVc
      have := Subgroup.commutator_mem_commutator (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹)
      show _ ∈ ⁅(⊤ : Subgroup (Dec (F := F) A)), ⊤⁆
      simpa [commutatorElement_def, mul_assoc] using this }
  have hsep : ∀ q : Dec (F := F) A ⧸ V, ∃ ψ : (Dec (F := F) A ⧸ V) →* ℂˣ, q ≠ 1 → ψ q ≠ 1 := fun q => by
    by_cases hq : q = 1
    · exact ⟨1, fun h => (h hq).elim⟩
    · obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Dec (F := F) A ⧸ V) ℂ hq
      exact ⟨ψ, fun _ => hψ⟩
  choose ψ hψ using hsep
  have hopen : ∀ q, IsOpen (((ψ q).comp (QuotientGroup.mk' V)).ker : Set (Dec (F := F) A)) := fun q =>
    Subgroup.isOpen_mono (fun g hg => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        (QuotientGroup.eq_one_iff g).2 hg, map_one]) hVo
  choose r hro hrD hrc hrT using fun q => one_char Ω F A v h ((ψ q).comp (QuotientGroup.mk' V)) (hopen q) T hvT
  let φ : G F Ω →* (Dec (F := F) A ⧸ V → ℂˣ) := Pi.monoidHom r
  have hφ : ∀ σ, φ σ = 1 ↔ ∀ q, r q σ = 1 := fun σ => funext_iff
  have hker : (φ.ker : Set (G F Ω)) = ⋂ q, (r q).ker := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter]
    exact hφ σ
  have ho : IsOpen (φ.ker : Set (G F Ω)) := by
    rw [hker]
    exact isOpen_iInter_of_finite hro
  obtain ⟨L, hLf, hLa, hL⟩ := GlobalTheory.RayFromArtin.exists_field φ ho
  have hmem : ∀ σ : G F Ω, σ ∈ L.fixingSubgroup ↔ ∀ q, r q σ = 1 := fun σ => by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, hL, hφ]
  refine ⟨L, hLf, hLa, ?_, ?_, ?_⟩
  · intro φ'
    haveI : Algebra.IsAlgebraic L Ω := Algebra.IsAlgebraic.tower_top (K := F) L
    haveI : IsGalois F Ω := {}
    let j : Ω →+* ℂ := ComplexEmbedding.lift Ω φ'
    have hj : j.comp (algebraMap L Ω) = φ' := ComplexEmbedding.lift_comp_algebraMap _ _
    have hreal : ComplexEmbedding.IsReal (j.comp (algebraMap F Ω)) := by
      exact IsTotallyReal.complexEmbedding_isReal _
    obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) j (ComplexEmbedding.conjugate j) (by
      rw [ComplexEmbedding.conjugate_comp, ComplexEmbedding.isReal_iff.1 hreal])
    have hc : ∀ x, j (σ.symm x) = starRingEnd ℂ (j x) := fun x => DFunLike.congr_fun hσ x
    have hfix : σ.symm ∈ L.fixingSubgroup := (hmem _).2 fun q => hrc q j σ.symm hc
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [← hj]
    show starRingEnd ℂ (j (x : Ω)) = j (x : Ω)
    rw [← hc]
    exact congrArg j (hfix x)
  · intro g
    rw [hmem]
    constructor
    · intro H
      by_contra hg
      have hq : (QuotientGroup.mk' V g) ≠ 1 := fun e => hg ((QuotientGroup.eq_one_iff g).1 e)
      exact hψ _ hq (by rw [← H (QuotientGroup.mk' V g), hrD]; rfl)
    · intro hg q
      rw [hrD, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg, map_one]
  · intro u hu A' hA' g hg
    exact (hmem g).2 fun q => hrT q u hu A' hA' g hg

end GlobalTheory.AbStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletionStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelian_totallyReal_ext_prescribedCompletion : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A v) (V : Subgroup (Dec (F := F) A)), IsOpen (V : Set (Dec (F := F) A)) → commutator (Dec (F := F) A) ≤ V → ∀ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T → ∃ F₁ : IntermediateField F Ω, FiniteDimensional F F₁ ∧ IsAbelianGalois F F₁ ∧ (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) ∧ (∀ g : Dec (F := F) A, (g : G F Ω) ∈ F₁.fixingSubgroup ↔ g ∈ V) ∧ ∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := F) A' ≤ F₁.fixingSubgroup := by
  first | exact @GlobalTheory.AbStep.exists_abelian_real_field | exact GlobalTheory.AbStep.exists_abelian_real_field | (intros; apply GlobalTheory.AbStep.exists_abelian_real_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemWeilGroupAtPlaceOfFixesExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemWeilGroupAtPlaceOfFixesExtension
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.WeilUp

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω]
  [Algebra K L] [IsScalarTower K L Ω] {A : ValuationSubring Ω}

theorem modEq_of_cong {v' : HeightOneSpectrum (𝓞 L)} (h' : IsPlaceOver A v') {Q a b : ℕ}
    (hc : ∀ ζ : 𝓞 L, A.valuation ((algebraMap L Ω (ζ : L)) ^ (Q ^ b) - (algebraMap L Ω (ζ : L)) ^ (Q ^ a)) < 1) :
    Q ^ a ≡ Q ^ b [MOD normV v' - 1] := by
  haveI := v'.isMaximal
  letI : Field (𝓞 L ⧸ v'.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 L ⧸ v'.asIdeal) := v'.asIdeal.finiteQuotientOfFreeOfNeBot v'.ne_bot
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (𝓞 L ⧸ v'.asIdeal)ˣ)
  have hord : orderOf u = normV v' - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units]; rfl
  rw [← hord, ← pow_eq_pow_iff_modEq]
  obtain ⟨ζ, hζ⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 L ⧸ v'.asIdeal)
  have hmem : ζ ^ (Q ^ b) - ζ ^ (Q ^ a) ∈ v'.asIdeal := by
    rw [← h']
    have e : algebraMap L Ω (((ζ ^ (Q ^ b) - ζ ^ (Q ^ a) : 𝓞 L)) : L) =
        (algebraMap L Ω (ζ : L)) ^ (Q ^ b) - (algebraMap L Ω (ζ : L)) ^ (Q ^ a) := by
      push_cast; simp [map_sub, map_pow]
    rw [e]; exact hc ζ
  have h0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  rw [map_sub, map_pow, map_pow, hζ, sub_eq_zero] at h0
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val]
  exact h0.symm

theorem dvd_of_modEq {q f n : ℕ} (hq : 1 < q) (h : q ^ n ≡ 1 [MOD q ^ f - 1]) : f ∣ n := by
  have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have hd : q ^ f - 1 ∣ q ^ n - 1 := (Nat.modEq_iff_dvd' h1).mp h.symm
  have hg := Nat.pow_sub_one_gcd_pow_sub_one q f n
  rw [Nat.gcd_eq_left hd] at hg
  have h2 : 1 ≤ q ^ f := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ (f.gcd n) := Nat.one_le_pow _ _ (by omega)
  have h4 : q ^ f = q ^ (f.gcd n) := by omega
  have h5 := Nat.pow_right_injective (Nat.succ_le_of_lt hq) h4
  rw [h5]; exact Nat.gcd_dvd_right f n

theorem actsAs_of_agree {q f a b : ℕ} {σ : G K Ω} {g : G L Ω} (hg : ∀ z : Ω, σ z = g z)
    (hσ : ActsAs A q σ (f * a) (f * b)) : ActsAs A (q ^ f) g a b := by
  have e : σ = (g.restrictScalars K : G K Ω) := AlgEquiv.ext hg
  subst e
  refine ⟨hσ.1, fun x hx => ?_⟩
  have := hσ.2 x hx
  rw [pow_mul, pow_mul] at this
  exact this

end GlobalTheory.AboveL.WeilUp

namespace GlobalTheory.AboveL


open GlobalTheory.AboveL.WeilUp in
theorem mem_weil_of_fix : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h) (g : G L Ω), (∀ z : Ω, (σ : G K Ω) z = g z) → g ∈ Weil h' := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' σ g hg
  obtain ⟨f, hf⟩ := normV_eq_pow v v' (comap_eq_of_placeOver h h')
  have hq : 1 < normV v := ReciprocityTheory.Gal.one_lt_normV v

  have hcong : ∀ a b : ℕ, ActsAs A (normV v) (σ : G K Ω) a b →
      normV v ^ a ≡ normV v ^ b [MOD normV v ^ f - 1] := by
    intro a b hab
    rw [← hf]
    refine modEq_of_cong h' fun ζ => ?_
    have hfix : (σ : G K Ω) (algebraMap L Ω (ζ : L)) = algebraMap L Ω (ζ : L) := by
      rw [hg]; exact g.commutes _
    have hint : A.valuation (algebraMap L Ω (ζ : L)) ≤ 1 := by
      rw [A.valuation_le_one_iff]
      exact mem_of_isIntegral_int A (ζ.2.algebraMap)
    have := hab.2 _ hint
    rwa [hfix] at this
  set d := deg σ with hd
  rcases le_total 0 d with hd0 | hd0
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hd0
    have hact := actsAs_of_deg (σ := σ) (a := n) (b := 0) (by rw [← hd, hn]; simp)
    have hdiv : f ∣ n := dvd_of_modEq hq (by simpa using hcong _ _ hact)
    obtain ⟨k, rfl⟩ := hdiv
    have hact' := actsAs_of_deg (σ := σ) (a := f * k) (b := f * 0) (by rw [← hd, hn]; simp)
    exact (mem_Weil h').mpr ⟨k, 0, hf ▸ actsAs_of_agree hg hact'⟩
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hd0
    have hact := actsAs_of_deg (σ := σ) (a := 0) (b := n) (by rw [← hd, hn]; simp)
    have hdiv : f ∣ n := dvd_of_modEq hq (by simpa using (hcong _ _ hact).symm)
    obtain ⟨k, rfl⟩ := hdiv
    have hact' := actsAs_of_deg (σ := σ) (a := f * 0) (b := f * k) (by rw [← hd, hn]; simp)
    exact (mem_Weil h').mpr ⟨0, k, hf ▸ actsAs_of_agree hg hact'⟩

end GlobalTheory.AboveL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemWeilGroupAtPlaceOfFixesExtensionStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_weilGroupAtPlace_of_fixes_extension : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h) (g : G L Ω), (∀ z : Ω, (σ : G K Ω) z = g z) → g ∈ Weil h' := by
  first | exact @GlobalTheory.AboveL.mem_weil_of_fix | exact GlobalTheory.AboveL.mem_weil_of_fix | (intros; apply GlobalTheory.AboveL.mem_weil_of_fix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharNormDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharNormDescent
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.RealNormChar

theorem conj_algebraMap {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : E) :
    IsCMField.complexConj M (algebraMap E M x) = algebraMap E M (IsCMField.complexConj E x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E M)) x).symm

theorem algebraMap_mem_real {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (x : maximalRealSubfield E) : algebraMap E M x ∈ maximalRealSubfield M := by
  refine (IsCMField.complexConj_eq_self_iff M _).1 ?_
  rw [conj_algebraMap, (IsCMField.complexConj_eq_self_iff E _).2 x.2]

def realHom (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] : maximalRealSubfield E →+* maximalRealSubfield M :=
  ((algebraMap E M).comp (maximalRealSubfield E).subtype).codRestrict _ algebraMap_mem_real

def normChar {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (χ : HChar K) :
    HChar L :=
  ⟨χ.1.comp (GroundTheory.Global.ideleNorm K L), χ.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg χ.1 (GroundTheory.Global.ideleNorm_diagonal (K := K) k)).trans (χ.2.2 _)⟩

theorem infIdele_eq {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K w x = GroundTheory.Global.IdeleGroup.infiniteEmbedding w x := by
  classical
  refine Units.ext (Prod.ext (funext fun u => ?_) rfl)
  change Pi.mulSingle w (x : w.Completion) u = GroundTheory.Global.IdeleGroup.infiniteAdeleSingle w (x : w.Completion) u
  rw [GroundTheory.Global.IdeleGroup.infiniteAdeleSingle_apply]

theorem normChar_locInf {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : HChar K) (u : InfinitePlace L) (hu : u.IsReal) :
    (normChar L χ).locInf u (-1) = χ.locInf (u.comap (algebraMap K L)) (-1) := by
  have hv := hu.comap (algebraMap K L)
  show χ.1 (GroundTheory.Global.ideleNorm K L (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L u (-1))) =
    χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele K (u.comap (algebraMap K L)) (-1))
  rw [infIdele_eq, infIdele_eq, GroundTheory.Global.ideleNorm_infiniteEmbedding]
  congr 2
  apply Units.ext
  apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective
  have := GroundTheory.Global.extensionEmbeddingOfIsReal_normUnits (K := K) u hu (-1)
  rw [this]
  simp


open scoped GroundTheory.Global.AdeleBaseChange in
open GlobalTheory.UnitaryHeckeBaseChange in
theorem ideleNorm_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (AdeleRing (𝓞 E) E)ˣ) :
    GlobalTheory.GalOfCusp.ideleNorm E x = GroundTheory.Global.ideleNorm (maximalRealSubfield E) E x := by
  apply Units.ext
  obtain ⟨z, hz⟩ := (adeleEquiv (isCMExt_real E)).surjective (x : AdeleRing (𝓞 E) E)
  have h : adeleNorm E (adeleEquiv (isCMExt_real E) z) = Algebra.norm _ z :=
    congrArg (Algebra.norm _) ((adeleEquiv (isCMExt_real E)).symm_apply_apply z)
  have h2 : ∀ z, toAdele (maximalRealSubfield E) E z =
      GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft (maximalRealSubfield E) E z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a l =>
      rw [toAdele_tmul, GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft_tmul]
      have hmap : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap
          (maximalRealSubfield E) E = GroundTheory.Global.AdeleBaseChange.adeleMap (maximalRealSubfield E) E := by
        ext a : 1
        apply Prod.ext
        · funext w
          open scoped NumberField.LiesOver in
          change AbsoluteValue.Completion.map _ _ _ = algebraMap _ _ _
          rw [AbsoluteValue.Completion.algebraMap_eq_of_liesOver]
        · apply FiniteAdeleRing.ext
          intro w
          change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap _ _ w _ =
            GroundTheory.Global.SemiLocal.completionMap _ w _
          rfl
      rw [hmap, mul_comm]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  change adeleNorm E (x : AdeleRing (𝓞 E) E) = _
  rw [GroundTheory.Global.coe_ideleNorm, ← hz, h]
  have h3 : adeleEquiv (isCMExt_real E) z = _ := h2 z
  rw [h3]
  exact (Algebra.norm_eq_of_algEquiv _ _).symm

theorem main : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] (a : ℕ) (χ : HChar (maximalRealSubfield K)), (∀ v : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = (-1) ^ a) → ∃ χ' : HChar (maximalRealSubfield M), (∀ u : InfinitePlace (maximalRealSubfield M), χ'.locInf u (-1) = (-1) ^ a) ∧ ∀ x : Ideles M, (compNorm M χ').1 x = (compNorm K χ).1 (GroundTheory.Global.ideleNorm K M x) := by
  intro K M _ _ _ _ _ _ _ a χ hsign
  letI : Algebra (maximalRealSubfield K) (maximalRealSubfield M) := (realHom K M).toAlgebra
  haveI : IsScalarTower (maximalRealSubfield K) (maximalRealSubfield M) M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (maximalRealSubfield K) K M :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨normChar (maximalRealSubfield M) χ,
    fun u => (normChar_locInf χ u (IsTotallyReal.isReal u)).trans (hsign _), fun x => ?_⟩
  show χ.1 (GroundTheory.Global.ideleNorm _ _ (GlobalTheory.GalOfCusp.ideleNorm M x)) =
    χ.1 (GlobalTheory.GalOfCusp.ideleNorm K (GroundTheory.Global.ideleNorm K M x))
  rw [ideleNorm_eq, ideleNorm_eq, GroundTheory.Global.ideleNorm_ideleNorm, GroundTheory.Global.ideleNorm_ideleNorm]

end GlobalTheory.RealNormChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharNormDescentStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_char_norm_descent : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Algebra K M] (a : ℕ) (χ : HChar (maximalRealSubfield K)), (∀ v : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = (-1) ^ a) → ∃ χ' : HChar (maximalRealSubfield M), (∀ u : InfinitePlace (maximalRealSubfield M), χ'.locInf u (-1) = (-1) ^ a) ∧ ∀ x : Ideles M, (compNorm M χ').1 x = (compNorm K χ).1 (GroundTheory.Global.ideleNorm K M x) := by
  first | exact @GlobalTheory.RealNormChar.main | exact GlobalTheory.RealNormChar.main | (intros; apply GlobalTheory.RealNormChar.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumInvariantCBHomTwistPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumInvariantCBHomTwistPrimes
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical

noncomputable section

namespace GlobalTheory.TopXiInvQ

open Formalism.L2.Col.LocE Formalism.L2.Col.Loc GlobalTheory.GO

theorem phiTopG_add {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (sharp : Bool) (i : ℕ) (hc : cOf R i = 0) (P : HeightOneSpectrum (𝓞 X.E))
    (x z : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0))
    (hz : ∀ s l, IntAt P (z (Pi.single s 1) l / (qOf P : X.E))) :
    PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P (x + z) = PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x := by
  unfold PhiTopG
  split_ifs
  · exact GlobalTheory.TopInv.PhiGS_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact GlobalTheory.TopInv.PhiG_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ _ _ _ _ hc x z hz
  · exact GlobalTheory.TopInv.PhiQ_add (GlobalTheory.TopInv.qOf_mem P) (GlobalTheory.TopInv.qOf_ne P) _ _ _ _ _ _ hc x z hz

theorem xiTop_invQ : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) x z, Y ∈ ybSet sel mu cst p.deco.1.N → z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst (m2 + 1) p Y p' (x + z) = XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  intro X Pr R Ch sel S mu cst L G m2 _hX hPr _hsel _hg _hT hL u p Y p' x z hY hz
  have hc := hL.cst_ok
  have hm := hL.hm
  have hc0 : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  obtain ⟨h1, h2⟩ := loc_of_mem_mulLat (cst := cst) hPr p p' x hz
  rw [XiTop_eq, XiTop_eq, h1]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have hq0 := GlobalTheory.TopInv.qOf_ne P.1
  rw [GlobalTheory.TopInv.inFr_add]
  have hZ := h2 P
  generalize inFr (frsF sel mu p P) (frsF sel mu p' P) z = Z at hZ ⊢
  unfold topDat
  rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
  refine congrArg₂ (· * ·) (phiTopG_add Ch mu _ (m2 + 1) hc0 P.1 _ _ fun s l => ?_)
    (GlobalTheory.TopInv.ftY_add sel mu cst hc P (hL.depthQ P) _ _ _ (fun s => ?_) fun l => ?_)
  · obtain ⟨s, rfl⟩ : ∃ t, s = Fin.castAdd _ t := ⟨⟨s.1, by have := s.2; omega⟩, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, GlobalTheory.TopStep.castAdd_single, ← pow_one (qOf P.1 : X.E)]
    refine GlobalTheory.TopInv.intAt_div_pow_le hq0 hc.B_pos ?_
    rw [div_eq_inv_mul]
    exact hZ s _
  · refine GlobalTheory.TopInv.atNL_int _ _ _ fun l => ?_
    rw [div_eq_inv_mul]
    exact hZ s l
  · have h3 := GlobalTheory.TopInv.repY_mem sel mu cst _ _ hY P
    rw [← (frsF sel mu p P).apply_symm_apply (_ • _)] at h3
    replace h3 := (GlobalTheory.TopStep.frsF_mem p P _).1 h3
    rw [map_smul] at h3
    exact (mem_localization_standardLattice _ _).1 h3 l

end GlobalTheory.TopXiInvQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumInvariantCBHomTwistPrimesStatement
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_datum_invariant_cB_hom_twist_primes : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : ChPt (R := R) sel mu u (m2 + 1 + 1)) x z, Y ∈ ybSet sel mu cst p.deco.1.N → z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst (m2 + 1) p Y p' (x + z) = XiTop Ch sel mu cst (m2 + 1) p Y p' x := by
  first | exact @GlobalTheory.TopXiInvQ.xiTop_invQ | exact GlobalTheory.TopXiInvQ.xiTop_invQ | (intros; apply GlobalTheory.TopXiInvQ.xiTop_invQ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsPlaceOverFiniteExtensionOfIsPlaceOver
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsPlaceOverFiniteExtensionOfIsPlaceOver
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL

private theorem coe_le_one {L Ω : Type} [Field Ω] [Field L] [NumberField L] [Algebra L Ω]
    (A : ValuationSubring Ω) (c : 𝓞 L) : A.valuation (algebraMap L Ω (c : L)) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr
    (ReciprocityTheory.Gal.mem_of_isIntegral_int A (map_isIntegral_int (algebraMap L Ω) c.isIntegral_coe))

theorem exists_isPlaceOver_of_tower : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → ∃ v' : HeightOneSpectrum (𝓞 L), IsPlaceOver A v' ∧ v'.under (𝓞 K) = v := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v h
  let m : Ideal (𝓞 L) :=
    { carrier := {y | A.valuation (algebraMap L Ω (y : L)) < 1}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add (f := _)] at ha hb ⊢
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c y hy
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hy ⊢
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (coe_le_one A c)) hy }
  have hmem : ∀ y : 𝓞 L, y ∈ m ↔ A.valuation (algebraMap L Ω (y : L)) < 1 := fun y => Iff.rfl
  have hprime : m.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hmem]; simp
    · intro x y hxy
      rw [hmem, hmem] at *
      have e : ((x * y : 𝓞 L) : L) = (x : L) * y := rfl
      rw [e, map_mul, map_mul] at hxy
      by_contra hc
      push_neg at hc
      exact absurd hxy (not_lt.mpr (one_le_mul hc.1 hc.2))
  have hK : ∀ x : 𝓞 K, (algebraMap (𝓞 K) (𝓞 L) x ∈ m ↔ x ∈ v.asIdeal) := by
    intro x
    rw [hmem, ← h x]
    have : algebraMap L Ω ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K Ω (x : K) := by
      have e : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
      rw [e, ← IsScalarTower.algebraMap_apply]
    rw [this]
  have hne : m ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    intro hb
    have h1 : algebraMap (𝓞 K) (𝓞 L) x ∈ m := (hK x).mpr hx
    rw [hb, Ideal.mem_bot] at h1
    apply hx0
    exact (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L)) (by rw [h1, map_zero])
  refine ⟨⟨m, hprime, hne⟩, ?_, ?_⟩
  · intro y
    exact (hmem y).symm.trans Iff.rfl
  · apply HeightOneSpectrum.ext
    ext x
    exact hK x

end GlobalTheory.AboveL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsPlaceOverFiniteExtensionOfIsPlaceOverStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPlaceOver_finiteExtension_of_isPlaceOver : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → ∃ v' : HeightOneSpectrum (𝓞 L), IsPlaceOver A v' ∧ v'.under (𝓞 K) = v := by
  first | exact @GlobalTheory.AboveL.exists_isPlaceOver_of_tower | exact GlobalTheory.AboveL.exists_isPlaceOver_of_tower | (intros; apply GlobalTheory.AboveL.exists_isPlaceOver_of_tower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlowUpFibreSemilocal
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL.LimAtLU

variable {a : ℕ}

theorem int_of_mem_inf {lam : DomWeight a} {x : ℂ} (hx : x ∈ infOfWeight lam) :
    ∃ j : ℤ, ((a : ℂ) - 1) / 2 - x = j := by
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  exact ⟨(k : ℤ) - lam.w k, by push_cast; ring⟩


open Classical in
noncomputable def jumpsOf (lam : DomWeight a) : Multiset ℤ :=
  (infOfWeight lam).map fun z => if h : ∃ n : ℤ, ((a : ℂ) - 1) / 2 - z = n then h.choose else 0

theorem jumpsOf_map (lam : DomWeight a) :
    (jumpsOf lam).map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
  rw [jumpsOf, Multiset.map_map]
  refine Multiset.map_congr rfl fun z hz => ?_
  have h := int_of_mem_inf hz
  simp only [Function.comp_apply, dif_pos h]
  exact h.choose_spec.symm

theorem eq_jumpsOf {lam : DomWeight a} {J : Multiset ℤ}
    (hJ : J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z)) : J = jumpsOf lam :=
  Multiset.map_injective Int.cast_injective (hJ.trans (jumpsOf_map lam).symm)

theorem norm_algHom {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : ‖σ x‖ = ‖(x : PadicAlgCl l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm,
    minpoly.algHom_eq σ σ.injective, ← minpoly.algHom_eq K.val K.val.injective]
  rfl

theorem overPl_of_induced {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ}
    [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω (Dec (F := E) A) O}
    (hj : GlobalTheory.Pst.Induces Bw) {τ : E →+* Qbar l} {LL' : FinExt l} {τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1}
    (hτ : GlobalTheory.Pst.IsInduced Bw τ τ') : OverPl ι (ι.toRingHom.comp τ) w := by
  intro x hx
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    RingEquiv.symm_apply_apply]
  rw [hτ]
  have h1 := norm_algHom (LL'.1.val.comp τ') ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩
  have h2 : ‖Bw.j (algebraMap E Ω x)‖ < 1 := (hj.valuation_lt_one_iff _).1 ((h x).2 hx)
  exact h1 ▸ h2

end GlobalTheory.CongL.LimAtLU


open Classical GlobalTheory.CongL.LimAtLU in
theorem GlobalTheory.CongL.crysDRU_of_linApprox : ClosedAtL → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → (∀ τ : E →+* ℂ, ∃ lam, HasWeightAt U τ lam) → ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Continuous r → IsSSRep r → ∀ C : Set (G E Ω →* GL (Fin a) (Qbar l)), LinApprox r C → (∀ ρ ∈ C, Continuous ρ ∧ ∃ U' : Submodule ℂ (UA E a → ℂ), SameWtAt ι w U U' ∧ CrysDRU U' ι ρ w) → CrysDRU U ι r w := by
  intro hC E Ω _ _ _ _ _ _ l _ ι a ha U _ hW r w hwl hr hss C hlin hCC
  intro P AI hT A hA O _ _ _ Bw hBw
  choose lamF hlamF using hW
  have key : ∀ lamG : (E →+* ℂ) → DomWeight a, (∀ σ, HasWeightAt U σ (lamG σ)) →
      (IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (jumpsOf (lamG (ι.toRingHom.comp τ)))) ∧
      ((∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype)) → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)) := by
    intro lamG hG
    refine hC E Ω l a ha P AI hT w A hA O Bw hBw (fun τ => jumpsOf (lamG (ι.toRingHom.comp τ))) r hr hss C hlin
      (fun ρ hρ => ?_)
    obtain ⟨hcont, U', hWW, hcd⟩ := hCC ρ hρ
    have h := hcd P AI hT A hA O Bw hBw
    exact ⟨hcont, GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI hT E Ω _ O Bw a _ h.1,
      fun τ LL' τ' hi => h.2.2 τ LL' τ' hi _ _ ((hWW _ (overPl_of_induced ι hA hBw hi) _).1 (hG _)) (jumpsOf_map _)⟩
  refine ⟨(key lamF hlamF).2 fun ρ hρ => ?_, (key lamF hlamF).1.1, fun τ LL' τ' hi lam J hl hJ => ?_⟩
  · obtain ⟨-, U', -, hcd⟩ := hCC ρ hρ
    exact (hcd P AI hT A hA O Bw hBw).1
  · let lamG := Function.update lamF (ι.toRingHom.comp τ) lam
    have hG : ∀ σ, HasWeightAt U σ (lamG σ) := by
      intro σ
      rcases eq_or_ne σ (ι.toRingHom.comp τ) with h | h
      · rw [h]
        simpa [lamG] using hl
      · show HasWeightAt U σ (Function.update lamF (ι.toRingHom.comp τ) lam σ)
        rw [Function.update_of_ne h]
        exact hlamF σ
    have e := (key lamG hG).1.2 τ LL' τ' hi
    rw [eq_jumpsOf hJ]
    simpa [lamG] using e
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOfNotApartOfNotSplit
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def intU (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) : Subgroup (UA E a) :=
  locU a w ⊓ ⨅ (u : HeightOneSpectrum (𝓞 E)) (_ : ¬ Apart u w), (GlobalTheory.LFun.KGL u (n := a)).comap (cLoc u)

def levelOf (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) :
    Subgroup (UA E a) :=
  finU (E := E) (n := a) ⊓ (⨅ (u : HeightOneSpectrum (𝓞 E)) (_ : ¬ Apart u w₀), (cLoc u).ker) ⊓
    ⨅ (w : HeightOneSpectrum (𝓞 E)) (_ : Apart w w₀), ((H w).map (cLoc w)).comap (cLoc w)

variable {a : ℕ}

theorem mem_intU {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} :
    x ∈ intU a w ↔ x ∈ locU a w ∧ ∀ u, ¬ Apart u w → cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a) := by
  simp only [intU, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem mem_levelOf {w₀ : HeightOneSpectrum (𝓞 E)} {H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)} {x : UA E a} :
    x ∈ levelOf a w₀ H ↔ x ∈ finU (E := E) (n := a) ∧ (∀ u, ¬ Apart u w₀ → cLoc u x = 1) ∧
      ∀ w, Apart w w₀ → ∃ y ∈ H w, cLoc w y = cLoc w x := by
  simp only [levelOf, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.mem_ker, Subgroup.mem_map, and_assoc]

theorem not_apart_symm {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart w u) : ¬ Apart u w := fun h' => h (Ne.symm h')

theorem not_apart_trans {w u v : HeightOneSpectrum (𝓞 E)} (h1 : ¬ Apart w u) (h2 : ¬ Apart u v) : ¬ Apart w v :=
  fun h => h ((not_not.1 h1).trans (not_not.1 h2))

theorem locU_congr {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) : locU a u = locU a w := by
  have e : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := not_not.1 h
  unfold locU
  rw [e]

theorem intU_congr {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) : intU a u = intU a w := by
  ext x
  rw [mem_intU, mem_intU, locU_congr h]
  exact and_congr_right fun _ => forall_congr' fun v =>
    ⟨fun h' hv => h' (not_apart_trans hv (not_apart_symm h)), fun h' hv => h' (not_apart_trans hv h)⟩

theorem intU_le_locU (w : HeightOneSpectrum (𝓞 E)) : intU a w ≤ locU a w := inf_le_left

theorem levelOf_le_finU (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) :
    levelOf a w₀ H ≤ finU (E := E) (n := a) := fun _ hx => (mem_levelOf.1 hx).1

theorem eq_of_not_apart_of_not_split {w u : HeightOneSpectrum (𝓞 E)} (hw : ¬ IsSplitAt w) (h : ¬ Apart u w) : u = w := by
  by_contra hne
  exact hw ⟨u, hne, not_not.1 h⟩

theorem cLoc_mem_KGL_of_not_apart {w u : HeightOneSpectrum (𝓞 E)} (h : ¬ Apart u w) (x : UA E a)
    (hx : cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a)) : cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a) := by
  rcases GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc (E := E) (not_not.1 h) with rfl | rfl
  · exact hx
  · exact GlobalTheory.BCT.GlobLev.integral_conjSrc x w hx

theorem mem_intU_of {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) (hk : cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a)) :
    x ∈ intU a w :=
  mem_intU.2 ⟨hx, fun _ hu => cLoc_mem_KGL_of_not_apart hu x hk⟩

theorem eq_one_of_cLoc_eq_one {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) (h1 : cLoc w x = 1) :
    x = 1 := by
  by_cases hw : IsSplitAt w
  · exact congrArg Subtype.val (GlobalTheory.SplitPts.eq_one_of_cLoc hw ⟨x, hx⟩ h1)
  · have hall : ∀ u, cLoc u x = 1 := by
      intro u
      by_cases hu : Apart u w
      · exact ((GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx).2 u hu
      · rw [eq_of_not_apart_of_not_split hw hu]; exact h1
    have hinf : cInf x = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).1
    refine Subtype.ext (ga_ext ?_ ?_)
    · exact hinf.trans (map_one _).symm
    · rw [Subgroup.coe_one, map_one]
      refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
      have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (hall u)
      simp only [Units.val_one, Matrix.one_apply] at this
      refine this.trans ?_
      split_ifs with hij <;> simp [hij] <;> rfl

theorem eq_of_cLoc_eq {w : HeightOneSpectrum (𝓞 E)} {x y : UA E a} (hx : x ∈ locU a w) (hy : y ∈ locU a w)
    (h : cLoc w x = cLoc w y) : x = y := by
  have := eq_one_of_cLoc_eq_one (mul_mem hx (inv_mem hy)) (by rw [map_mul, map_inv, h, mul_inv_cancel])
  exact mul_inv_eq_one.1 this

theorem coe_subgroupOf_image {G : Type} [Group G] {H L : Subgroup G} (h : H ≤ L) :
    Subtype.val '' ((H.subgroupOf L : Subgroup L) : Set L) = (H : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx; exact ⟨⟨x, h hx⟩, hx, rfl⟩

theorem isCompact_of_le {w : HeightOneSpectrum (𝓞 E)} {H : Subgroup (UA E a)} (hH : H ≤ intU a w)
    (ho : IsOpen ((H.subgroupOf (locU a w)) : Set (locU a w))) (hc : IsCompact (intU a w : Set (UA E a))) :
    IsCompact (H : Set (UA E a)) := by
  have hcl : IsClosed ((H.subgroupOf (locU a w)) : Set (locU a w)) := Subgroup.isClosed_of_isOpen _ ho
  have hc' : IsCompact (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff, coe_subgroupOf_image (intU_le_locU w)]
    exact hc
  have h2 := (hc'.of_isClosed_subset hcl fun x hx => hH hx).image continuous_subtype_val
  rwa [coe_subgroupOf_image (hH.trans (intU_le_locU w))] at h2

end GlobalTheory.Cong.AdaptLev
end
end
