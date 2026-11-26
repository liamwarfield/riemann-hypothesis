module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealSubstOfConstantCoeffZero
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryOneMapEqZero
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
open GlobalTheory.QLog.Window

namespace GlobalTheory.QLog.WindowMat

theorem integers_isIntegrallyClosedIn {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsIntegrallyClosedIn O C :=
  isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 h)⟩

theorem hasPeriod_zero {p : ℕ} {O B Q : Type} [CommRing O] [CommRing B] [CommRing Q] [Algebra B Q]
    {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d) {θ : B →+* O} (h : IsFrame p Q θ)
    (t : G.Tate) : c.HasPeriod θ t (0 : MvPowerSeries (Fin d) Q) 0 := by
  refine (c.hasPeriod_iff h t (0 : MvPowerSeries (Fin d) Q) 0).2 fun n z _ => ⟨0, fun m => ⟨0, fun N _ => ⟨0, ?_⟩⟩, 0, ?_⟩
  · have h0 : trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N) (0 : MvPowerSeries (Fin d) Q) = 0 :=
      map_zero _
    rw [h0, map_zero, sub_zero, mul_zero, map_zero]
  · simp

section Transfer

variable {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
  [Algebra O C] (θ : B →+* O) (Θ : Q →+* C)
  (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
include hΘ

theorem in_map_top {σ : Type} {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (⊤ : Ideal O) (map Θ f) := fun α => by
  obtain ⟨b, -, eb⟩ := hf α
  exact ⟨θ b, Submodule.mem_top, by rw [coeff_map, eb, hΘ]⟩

theorem map_eq_zero_of_in_ker {σ : Type} {f : MvPowerSeries σ Q} (hf : In (RingHom.ker θ) f) :
    map Θ f = 0 := by
  ext α
  obtain ⟨b, hb, eb⟩ := hf α
  rw [coeff_map, eb, hΘ, RingHom.mem_ker.1 hb, map_zero, map_zero]

theorem map_comb {σ ι : Type} [Finite σ] [Fintype ι] (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    map Θ (comb b e) = comb (fun i => θ (b i)) fun i => map Θ (e i) := by
  unfold comb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul', hΘ]

theorem lin_map {d : ℕ} (f : MvPowerSeries (Fin d) Q) (i : Fin d) : lin (map Θ f) i = Θ (lin f i) := by
  simp only [lin, coeff_map]

theorem up_map {d : ℕ} {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, map θ (μ' i) = μ i) (i : Fin d) :
    up C μ i = map Θ (up Q μ' i) := by
  ext α
  simp only [up, coeff_map, ← hμ, hΘ]

theorem ql_map {d : ℕ} {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, map θ (μ' i) = μ i)
    (h0 : ∀ i, constantCoeff (μ' i) = 0) {f : MvPowerSeries (Fin d) Q} (hf : QL μ' ⊤ f) :
    QL μ ⊤ (map Θ f) := by
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [constantCoeff_map, hf.1, map_zero]
  · obtain ⟨b, -, eb⟩ := hf.2.1 i
    exact ⟨θ b, Submodule.mem_top, by rw [lin_map θ Θ hΘ, eb, hΘ]⟩
  · have : up C μ = fun i => map Θ (up Q μ' i) := funext (up_map θ Θ hΘ hμ)
    rw [this, ← map_formalGroupLawCoboundaryOne_eq Θ _ (constantCoeff_up h0)]
    exact in_map_top θ Θ hΘ hf.2.2

theorem formalGroupLawCoboundaryOne_map_eq_zero {d : ℕ} {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, map θ (μ' i) = μ i)
    (h0 : ∀ i, constantCoeff (μ' i) = 0) {f : MvPowerSeries (Fin d) Q}
    (hf : In (RingHom.ker θ) (cob1 (up Q μ') f)) : cob1 (up C μ) (map Θ f) = 0 := by
  have : up C μ = fun i => map Θ (up Q μ' i) := funext (up_map θ Θ hΘ hμ)
  rw [this, ← map_formalGroupLawCoboundaryOne_eq Θ _ (constantCoeff_up h0)]
  exact map_eq_zero_of_in_ker θ Θ hΘ hf

end Transfer

theorem comb_sum {B Q σ ι κ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype ι] [Fintype κ]
    (R : κ → ι → B) (a : ι → B) (e : κ → MvPowerSeries σ Q) :
    comb (fun l => ∑ i, R l i * a i) e = ∑ i, algebraMap B Q (a i) • comb (fun l => R l i) e := by
  unfold comb
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem din_of_in {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] {f : MvPowerSeries σ Q}
    (hf : In (⊤ : Ideal B) f) : DIn (⊤ : Ideal B) f := fun α i => by
  obtain ⟨b, -, eb⟩ := hf α
  exact ⟨(α i : B) * b, Submodule.mem_top, by rw [eb, map_mul, map_natCast]⟩

end GlobalTheory.QLog.WindowMat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomAgreeLocusClosedSubscheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfIsOpenOfStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqNearFibreOfQuotContracts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

theorem eq_near_fibre_of_quot_contracts : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∀ t : S, (∀ x : A.left, A.hom x = t → (u * v⁻¹).left x = (η[B]).left t) → ∃ V : S.Opens, t ∈ V ∧ (A.hom ⁻¹ᵁ V).ι ≫ u.left = (A.hom ⁻¹ᵁ V).ι ≫ v.left := by
  intro S A B _ _ _ _ u v hA hB hu hv t ht
  have := hA.proper
  have hε : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S := Over.w η[A]
  obtain ⟨V, htV, hV⟩ := GlobalTheory.local_rigidity A.left S B.left A.hom (η[A] : 𝟙_ (Over S) ⟶ A).left
    (u * v⁻¹).left hε inferInstance
    (GlobalTheory.surjective_app_of_isAbelianScheme GlobalTheory.SemiRigid.globalFns A hA) t _ ht
  refine ⟨V, htV, ?_⟩
  have h1 : (η[A] : 𝟙_ (Over S) ⟶ A) ≫ (u * v⁻¹) = η[B] := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, IsMonHom.one_hom, IsMonHom.one_hom, mul_inv_cancel, Hom.one_def,
      toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  let i : Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ⟶ A := Over.homMk (A.hom ⁻¹ᵁ V).ι rfl
  have h2 : i ≫ (u * v⁻¹) = 1 := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Hom.one_def, Over.comp_left]
    change (A.hom ⁻¹ᵁ V).ι ≫ (u * v⁻¹).left = _
    rw [hV, ← Over.comp_left, h1]
    have e : (toUnit (Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom))).left = (A.hom ⁻¹ᵁ V).ι ≫ A.hom :=
      by simpa using Over.w (toUnit (Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom)))
    rw [e, Category.assoc]
  have h3 : i ≫ u = i ≫ v := by
    have := congrArg (· * (i ≫ v)) h2
    simpa [MonObj.comp_mul, GrpObj.comp_inv] using this
  exact congrArg (·.left) h3

end GlobalTheory.EndLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqUnitOfPullbackEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

theorem eq_unit_of_pullback_eq : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∀ (T : Scheme.{0}) (t : T ⟶ S)
    (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → φ' ≫ u.left = φ' ≫ v.left →
    ∀ τ : T, ∀ x : A.left, A.hom x = t τ → (u * v⁻¹).left x = (η[B]).left (t τ) := by
  intro S A B _ _ _ _ u v _ _ _ _ T t A' _ φ' hp he τ x hx
  have hw : φ' ≫ A.hom = A'.hom ≫ t := hp.1.w
  let P : Over.mk (A'.hom ≫ t) ⟶ A := Over.homMk φ' (by simpa using hw)
  have hPu : P ≫ u = P ≫ v := by
    ext1; simpa [P] using he
  have h1 : P ≫ (u * v⁻¹) = 1 := by
    rw [comp_mul, GrpObj.comp_inv, hPu, mul_inv_cancel]
  have h2 : φ' ≫ (u * v⁻¹).left = A'.hom ≫ t ≫ (η[B]).left := by
    have := congrArg CommaMorphism.left h1
    simpa [P, Hom.one_def] using this
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x τ hx
  have hf : (hp.1.isoPullback.inv ≫ φ') z = x := by rw [hp.1.isoPullback_inv_fst]; exact hz1
  have hs : (hp.1.isoPullback.inv ≫ A'.hom) z = τ := by rw [hp.1.isoPullback_inv_snd]; exact hz2
  rw [Scheme.Hom.comp_apply] at hf hs
  rw [← hf, ← Scheme.Hom.comp_apply, h2, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hs]

end GlobalTheory.EndLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDiffUnitSpecialises
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem hom_diff_unit_specialises : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∀ t s : S, s ∈ closure {t} → (∀ x : A.left, A.hom x = t → (u * v⁻¹).left x = (η[B]).left t) → ∀ x : A.left, A.hom x = s → (u * v⁻¹).left x = (η[B]).left s := by
  intro S A B _ _ _ _ u v hA hB hu hv t s hst H x hx
  haveI := hA.smooth
  haveI := hB.proper
  have hη : (η[B]).left ≫ B.hom = 𝟙 S := by simpa using Over.w (η[B])
  have hid : IsClosedImmersion (𝟙 S) := inferInstance
  haveI : IsClosedImmersion ((η[B]).left ≫ B.hom) := by rw [hη]; exact hid
  haveI : IsClosedImmersion (η[B]).left := IsClosedImmersion.of_comp _ B.hom
  have hF : IsClosed ((u * v⁻¹).left ⁻¹' Set.range (η[B]).left) :=
    (η[B]).left.isClosedEmbedding.isClosed_range.preimage (u * v⁻¹).left.continuous
  have hcl : x ∈ closure (A.hom ⁻¹' {t}) := by
    rw [mem_closure_iff]
    intro U hU hxU
    have hO : IsOpen (A.hom '' U) := A.hom.isOpenMap U hU
    obtain ⟨_, ⟨y, hyU, rfl⟩, hyt⟩ := mem_closure_iff.mp hst _ hO ⟨x, hxU, hx⟩
    exact ⟨y, hyU, hyt⟩
  have hmem : x ∈ (u * v⁻¹).left ⁻¹' Set.range (η[B]).left :=
    closure_minimal (fun z (hz : z ∈ A.hom ⁻¹' {t}) =>
      (⟨t, (H z hz).symm⟩ : (u * v⁻¹).left z ∈ Set.range (η[B]).left)) hF hcl
  obtain ⟨y, hy⟩ := hmem
  have hys : y = s := by
    have e1 := congrArg B.hom hy
    rw [← Scheme.Hom.comp_apply, hη, ← Scheme.Hom.comp_apply, Over.w] at e1
    simpa [hx] using e1
  subst hys
  exact hy.symm

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

theorem isClosed_of_isOpen_of_stable {S : Scheme.{0}} [IsLocallyNoetherian S] {L : Set S} (ho : IsOpen L)
    (hs : ∀ t ∈ L, ∀ s, s ∈ closure ({t} : Set S) → s ∈ L) : IsClosed L := by
  rw [← closure_subset_iff_isClosed]
  intro s hsc
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  have hUa : IsAffineOpen U := hU
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : TopologicalSpace.NoetherianSpace (U : Set S) := noetherianSpace_of_isAffineOpen U hUa
  haveI : QuasiSober (U : Set S) := U.isOpen.isOpenEmbedding_subtypeVal.quasiSober
  let s' : (U : Set S) := ⟨s, hsU⟩
  let L' : Set (U : Set S) := Subtype.val ⁻¹' L
  have hL'o : IsOpen L' := ho.preimage continuous_subtype_val
  have hs' : s' ∈ closure L' := by
    rw [mem_closure_iff]
    intro O hO hsO
    obtain ⟨O₀, hO₀, rfl⟩ := isOpen_induced_iff.mp hO
    obtain ⟨x, ⟨hxO, hxU⟩, hxL⟩ := mem_closure_iff.mp hsc (O₀ ∩ U) (hO₀.inter U.isOpen) ⟨hsO, hsU⟩
    exact ⟨⟨x, hxU⟩, hxO, hxL⟩
  let D : Set (U : Set S) := ⋃ Z ∈ {Z ∈ irreducibleComponents (U : Set S) | (Z ∩ L').Nonempty}, Z
  have hD : IsClosed D :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (by exact fun _ h => h.1)).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  have hLD : L' ⊆ D := fun y hy =>
    Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents y, y, mem_irreducibleComponent, hy⟩
      mem_irreducibleComponent
  obtain ⟨Z, ⟨hZ, hZL⟩, hsZ⟩ := Set.mem_iUnion₂.mp ((closure_minimal hLD hD) hs')
  have hZi : IsIrreducible Z := hZ.1
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hg : IsGenericPoint hZi.genericPoint Z := by
    have := hZi.isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  have hgL : hZi.genericPoint ∈ L' := (hg.mem_open_set_iff hL'o).mpr hZL
  have hsp : hZi.genericPoint ⤳ s' := by
    rw [specializes_iff_mem_closure, hg.def]; exact hsZ
  exact hs _ hgL s (specializes_iff_mem_closure.mp (hsp.map continuous_subtype_val))

theorem eqLocus_isClosedImmersion : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → (φ' ≫ u.left = φ' ≫ v.left ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro S _ A B _ _ u v hA hB hu hv
  haveI := hA.comm
  haveI := hB.comm
  let P : S → Prop := fun t => ∀ x : A.left, A.hom x = t → (u * v⁻¹).left x = (η[B]).left t
  have hloc : ∀ t, P t → ∃ V : S.Opens, t ∈ V ∧ (A.hom ⁻¹ᵁ V).ι ≫ u.left = (A.hom ⁻¹ᵁ V).ι ≫ v.left :=
    fun t ht => eq_near_fibre_of_quot_contracts S A B u v hA hB hu hv t ht
  have hagree : ∀ V : S.Opens, (A.hom ⁻¹ᵁ V).ι ≫ u.left = (A.hom ⁻¹ᵁ V).ι ≫ v.left → ∀ t ∈ V, P t := by
    intro V hV t htV x hx
    have hxV : x ∈ A.hom ⁻¹ᵁ V := by show A.hom x ∈ V; rw [hx]; exact htV
    obtain ⟨y, rfl⟩ : x ∈ Set.range (A.hom ⁻¹ᵁ V).ι := by rw [Scheme.Opens.range_ι]; exact hxV
    let Q : Over.mk ((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ⟶ A := Over.homMk (A.hom ⁻¹ᵁ V).ι rfl
    have hQ : Q ≫ u = Q ≫ v := by ext1; simpa [Q] using hV
    have h1 : Q ≫ (u * v⁻¹) = 1 := by rw [comp_mul, GrpObj.comp_inv, hQ, mul_inv_cancel]
    have h2 : (A.hom ⁻¹ᵁ V).ι ≫ (u * v⁻¹).left = ((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ≫ (η[B]).left := by
      have := congrArg CommaMorphism.left h1
      simpa [Q, Hom.one_def] using this
    have e1 : ((A.hom ⁻¹ᵁ V).ι ≫ (u * v⁻¹).left) y = (((A.hom ⁻¹ᵁ V).ι ≫ A.hom) ≫ (η[B]).left) y := by
      rw [h2]
    simp only [Scheme.Hom.comp_apply] at e1
    rw [e1, hx]
  let L : Set S := {t | P t}
  have hLo : IsOpen L := by
    rw [isOpen_iff_forall_mem_open]
    intro t ht
    obtain ⟨V, htV, hV⟩ := hloc t ht
    exact ⟨V, fun t' ht' => hagree V hV t' ht', V.isOpen, htV⟩
  have hLc : IsClosed L := isClosed_of_isOpen_of_stable hLo fun t ht s hs =>
    hom_diff_unit_specialises S A B u v hA hB hu hv t s hs ht
  let W : S.Opens := ⟨L, hLo⟩
  have hWi : IsClosedImmersion W.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hLc)
  refine ⟨W, W.ι, hWi, ?_⟩
  intro T t A' _ φ' hp
  constructor
  · intro he
    have hr : Set.range t ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨τ, rfl⟩
      exact eq_unit_of_pullback_eq S A B u v hA hB hu hv T t A' φ' hp he τ
    exact ⟨IsOpenImmersion.lift W.ι t hr, IsOpenImmersion.lift_fac _ _ _⟩
  · rintro ⟨z, hz⟩
    have hmem : ∀ y : A'.left, P (t (A'.hom y)) := by
      intro y
      have : t (A'.hom y) ∈ Set.range W.ι := ⟨z (A'.hom y), by rw [← hz, Scheme.Hom.comp_apply]⟩
      rw [Scheme.Opens.range_ι] at this
      exact this
    choose V hVt hV using fun y => hloc _ (hmem y)
    have hw : φ' ≫ A.hom = A'.hom ≫ t := hp.1.w
    let U : A'.left → A'.left.Opens := fun y => φ' ⁻¹ᵁ (A.hom ⁻¹ᵁ V y)
    have hyU : ∀ y, y ∈ U y := by
      intro y
      show A.hom (φ' y) ∈ V y
      rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
      exact hVt y
    have hU : TopologicalSpace.IsOpenCover U :=
      eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyU y⟩
    refine Scheme.Cover.hom_ext (Scheme.openCoverOfIsOpenCover _ U hU) _ _ fun y => ?_
    show (φ' ⁻¹ᵁ (A.hom ⁻¹ᵁ V y)).ι ≫ φ' ≫ u.left = (φ' ⁻¹ᵁ (A.hom ⁻¹ᵁ V y)).ι ≫ φ' ≫ v.left
    rw [← morphismRestrict_ι_assoc, ← morphismRestrict_ι_assoc, hV y]

end GlobalTheory.EndLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomAgreeLocusClosedSubscheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc

theorem agreeLocus_factors_closedSubscheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → (φ' ≫ u.left = φ' ≫ v.left ↔ ∃ z : T ⟶ Z, z ≫ i = t) :=
  GlobalTheory.EndLoc.eqLocus_isClosedImmersion

end GlobalTheory.EndLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomAgreeLocusClosedSubschemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_homAgreeLocus_closedSubscheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [GrpObj B] (u v : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → IsMonHom u → IsMonHom v → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → (φ' ≫ u.left = φ' ≫ v.left ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  first | (exact @GlobalTheory.EndLoc.agreeLocus_factors_closedSubscheme) | (exact GlobalTheory.EndLoc.agreeLocus_factors_closedSubscheme) | (intros; apply GlobalTheory.EndLoc.agreeLocus_factors_closedSubscheme  <;> assumption)
end
end
