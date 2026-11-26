module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V leviV)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.ChartGlue
open scoped ContDiff

namespace GlobalTheory.TrueGeo.OfLattice

section Rect

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {B : LB X} {α β : Type} [Fintype α] [Fintype β]

def combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) : Weight p σ B :=
  Weight.fs hB _ (fun _ => Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (secVal_mem _)) h

theorem combWeight_φ (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) (i : B.ι) (y : CxPts p σ) :
    (combWeight hB s A h).φ i y = Real.log (∑ a, ‖∑ j, A j a * valR y.1 (B.U i) ((s j).f i)‖ ^ 2) := by
  simp only [combWeight, Weight.fs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem isCInf_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) : (combWeight hB s A h).IsCInf := fun i y hy => by
  have hs : ContDiff ℝ ∞ fun v : α → ℂ => ∑ a, ‖∑ j, A j a * v j‖ ^ 2 :=
    ContDiff.sum fun a _ => (ContDiff.sum fun j _ =>
      contDiff_const.mul (contDiff_apply ℝ (fun _ => ℂ) j)).norm_sq ℂ
  refine ⟨B.U i, α, inferInstance, fun j => (s j).f i,
    fun v => Real.log (∑ a, ‖∑ j, A j a * v j‖ ^ 2), {v | ∑ a, ‖∑ j, A j a * v j‖ ^ 2 ≠ 0}, hy,
    isOpen_ne_fun hs.continuous continuous_const, ?_, hs.contDiffOn.log fun _ h => h,
    .of_forall fun z => combWeight_φ hB s A h i z⟩
  have := (h.sum_pos hy).ne'
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  exact this

theorem semiPosReg_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ : k →+* ℂ} (A : Matrix α β ℂ)
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j)) (D : ℕ) :
    (combWeight hB s A h).SemiPosReg D := fun i c y hy ξ => by
  let G (a : β) (v : V D) : ℂ := ∑ j, A j a * ev p σ _ ((s j).f i) (c.e.symm v)
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hG (a) : ContDiffAt ℂ 2 (G a) (c.e y) := ContDiffAt.sum fun j _ => contDiffAt_const.mul
    (((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho (c.holo _ ((s j).f i))).contDiffAt
      (ho.mem_nhds (mem_over c.e hy.1 hy.2))).of_le (by norm_cast))
  have e (v : V D) : ∑ a, Complex.normSq (G ((Fintype.equivFin β).symm a) v) = ∑ a, ‖G a v‖ ^ 2 :=
    (Equiv.sum_comp (Fintype.equivFin β).symm fun a => Complex.normSq (G a v)).trans
      (Finset.sum_congr rfl fun a _ => Complex.normSq_eq_norm_sq _)
  have h0 := h.sum_pos hy.2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
  have := ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg
    (u := fun a v => Complex.normSq (G ((Fintype.equivFin β).symm a) v))
    (fun a => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hG _))
    (fun a => ReciprocityTheory.L2DbarEstimates.logPshAt_normSq (hG _))
    (by rw [e]; simp only [G, c.e.left_inv hy.1]; exact h0) ξ
  simp only [e] at this
  simp only [combWeight_φ]
  exact this

variable [DecidableEq β]

theorem isConj_combWeight (hB : B.IsLB) (s : α → B.Sec) {σ σ' : k →+* ℂ} {A A' : Matrix α β ℂ}
    (h : Weight.NoCommonZero fun a => ∑ j, A j a • secVal p σ (s j))
    (h' : Weight.NoCommonZero fun a => ∑ j, A' j a • secVal p σ' (s j)) {U : Matrix β β ℂ}
    (hU : U ∈ Matrix.unitaryGroup β ℂ) (e : A' = A.map (starRingEnd ℂ) * U) :
    (combWeight hB s A h).IsConj (combWeight hB s A' h') := fun i y y' hy' hy => by
  rw [combWeight_φ, combWeight_φ]
  congr 1
  have hv (j : α) : valR y'.1 (B.U i) ((s j).f i) = starRingEnd ℂ (valR y.1 (B.U i) ((s j).f i)) :=
    CxPts.ev_conj hy' hy _
  have := sum_normSq_vecMul_unitary hU fun a =>
    starRingEnd ℂ (∑ j, A j a * valR y.1 (B.U i) ((s j).f i))
  simp only [RCLike.norm_conj] at this
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) this
  congr 2
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [e, hv, Matrix.mul_apply, Matrix.map_apply, Matrix.vecMul, dotProduct, map_sum, map_mul,
    Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

def combHerm (hB : B.IsLB) (s : α → B.Sec) (A : (k →+* ℂ) → Matrix α β ℂ)
    (h : ∀ σ, Weight.NoCommonZero fun a => ∑ j, A σ j a • secVal p σ (s j))
    (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup β ℂ, A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U) :
    HermLB p where
  B := B
  isLB := hB
  φ σ := combWeight hB s (A σ) (h σ)
  cInf σ := isCInf_combWeight hB s _ _
  conj σ σ' i y y' e hy := by
    obtain rfl := eq_conj_of_conj e
    obtain ⟨U, hU, e'⟩ := hc σ
    exact isConj_combWeight hB s (h σ) (h _) hU e' i y y' e hy

end Rect

theorem nefFib_of_isGenerated {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D)
    (L : HermLB p) (hL : IsGenerated L.B) : ArInt.NefFib L := by
  intro Z i _ _ κ _ _ _ hd
  have := hX.finite
  have : IsProper p := CommonModel.isProper_of_isProjOver hX.isProjOver
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hX.isProjOver
  have hA := hH.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ (X := Z)) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 ((hL.pull i).isNef (k := κ) hA)).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

variable {F : Type} [Field F] [NumberField F]

section Values

variable {K : Type} [Field K] {Y : Var F} (y : Sp K ⟶ Y.X) {τ : F →+* K}




end Values

theorem injective_emb (σ : 𝓞 F →+* ℂ) : Function.Injective σ :=
  (RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _))

def extEmb (σ : 𝓞 F →+* ℂ) : F →+* ℂ := IsFractionRing.lift (injective_emb σ)

theorem extEmb_comp (σ : 𝓞 F →+* ℂ) : (extEmb σ).comp (algebraMap (𝓞 F) F) = σ :=
  RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) (injective_emb σ) a

theorem extEmb_eq {σ : 𝓞 F →+* ℂ} {τ : F →+* ℂ} (h : τ.comp (algebraMap (𝓞 F) F) = σ) : extEmb σ = τ :=
  IsFractionRing.ringHom_ext (A := 𝓞 F) fun a => RingHom.congr_fun ((extEmb_comp σ).trans h.symm) a

variable [StarRing F]




end GlobalTheory.TrueGeo.OfLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.ModelDom

theorem ringKrullDim_le_of_isAlgebraic (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B]
    [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B] :
    ringKrullDim B ≤ ringKrullDim A := by
  classical
  have step : ∀ (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S] (f : R →+* S),
      Function.Injective f → ∀ x : S, Function.Surjective (Polynomial.eval₂RingHom f x) →
      (∃ g : Polynomial R, g ≠ 0 ∧ Polynomial.eval₂ f x g = 0) → ringKrullDim S ≤ ringKrullDim R := by
    intro R S _ _ _ _ _ f hf x hgen halg
    rw [ringKrullDim_le_iff_height_le]
    intro q hq
    have h := ReciprocityTheory.CA.height_le_height_comap_of_eval₂_surjective f hf x hgen halg q
    have h2 : ((q.comap f).height : WithBot ℕ∞) ≤ ringKrullDim R :=
      Ideal.height_le_ringKrullDim_of_ne_top (Ideal.IsPrime.ne_top inferInstance)
    exact (WithBot.coe_le_coe.2 h).trans h2
  have key : ∀ s : Finset B, ringKrullDim (Algebra.adjoin A (s : Set B)) ≤ ringKrullDim A := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine step A _ (algebraMap A _) (FaithfulSMul.algebraMap_injective _ _) 0 ?_
        ⟨Polynomial.X, Polynomial.X_ne_zero, by simp⟩
      rintro ⟨y, hy⟩
      rw [Finset.coe_empty, Algebra.adjoin_empty, Algebra.mem_bot] at hy
      obtain ⟨a, rfl⟩ := hy
      exact ⟨Polynomial.C a, Subtype.ext (by simp)⟩
    | insert x s _ ih =>
      have hle : Algebra.adjoin A (s : Set B) ≤ Algebra.adjoin A ((insert x s : Finset B) : Set B) :=
        Algebra.adjoin_mono (by simp)
      have : Algebra.FiniteType A (Algebra.adjoin A (s : Set B)) :=
        Algebra.FiniteType.adjoin_of_finite s.finite_toSet
      have : IsNoetherianRing (Algebra.adjoin A (s : Set B)) := Algebra.FiniteType.isNoetherianRing A _
      have hx : x ∈ Algebra.adjoin A ((insert x s : Finset B) : Set B) := Algebra.subset_adjoin (by simp)
      refine le_trans (step _ _ (Subalgebra.inclusion hle).toRingHom (Subalgebra.inclusion_injective hle) ⟨x, hx⟩
        ?_ ?_) ih
      · rintro ⟨y, hy⟩
        induction hy using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Finset.coe_insert] at hy
          rcases hy with rfl | hy
          · exact ⟨Polynomial.X, by simp⟩
          · exact ⟨Polynomial.C ⟨y, Algebra.subset_adjoin hy⟩, Subtype.ext (by simp)⟩
        | algebraMap a => exact ⟨Polynomial.C (algebraMap A _ a), Subtype.ext (by simp)⟩
        | add y z _ _ hy hz =>
          obtain ⟨p, hp⟩ := hy
          obtain ⟨q, hq⟩ := hz
          exact ⟨p + q, by rw [map_add (f := _), hp, hq]; rfl⟩
        | mul y z _ _ hy hz =>
          obtain ⟨p, hp⟩ := hy
          obtain ⟨q, hq⟩ := hz
          exact ⟨p * q, by rw [map_mul, hp, hq]; rfl⟩
      · obtain ⟨g, hg, h0⟩ := Algebra.IsAlgebraic.isAlgebraic (R := A) x
        refine ⟨g.map (algebraMap A _), (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective _ _)).2 hg, ?_⟩
        apply Subtype.ext
        rw [Polynomial.eval₂_map]
        have := Polynomial.hom_eval₂ g
          ((Subalgebra.inclusion hle).toRingHom.comp (algebraMap A (Algebra.adjoin A (s : Set B))))
          (Algebra.adjoin A ((insert x s : Finset B) : Set B)).val.toRingHom ⟨x, hx⟩
        exact this.trans h0
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := B)
  have := key s
  rw [hs] at this
  exact (ringKrullDim_eq_of_ringEquiv Subalgebra.topEquiv.toRingEquiv).ge.trans this

theorem dim_le_of_birational {N M : Scheme.{0}} [IsIntegral N] [IsIntegral M] [IsLocallyNoetherian M] (π : N ⟶ M)
    [LocallyOfFiniteType π] [IsDominant π] [IsIso (π.stalkMap (genericPoint N))] :
    topologicalKrullDim N ≤ topologicalKrullDim M := by
  have hd : ∀ {Z : Scheme.{0}} (U : Z.Opens), IsAffineOpen U →
      topologicalKrullDim (U : Set Z) = ringKrullDim Γ(Z, U) := fun {Z} U hU => by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Z, U))
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 M.isBasis_affineOpens (Opens.mem_top (π x))
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.1 N.isBasis_affineOpens (show x ∈ π ⁻¹ᵁ U from hxU)
  refine ⟨V, V.isOpen, hxV, ?_⟩
  refine le_trans ?_ (topologicalKrullDim_subspace_le M (U : Set M))
  rw [hd U hU, hd V hV]
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have : IsNoetherianRing Γ(M, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := (π.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(M, U) Γ(N, V) := π.finiteType_appLE hU hV hVU
  have hη := apply_genericPoint_of_isDominant π
  have hηV : genericPoint N ∈ V :=
    ((genericPoint_spec N).mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  have hyU : π (genericPoint N) ∈ U := hVU hηV
  letI := M.presheaf.algebra_section_stalk (U := U) ⟨_, hyU⟩
  have hfr := isFractionRing_stalk_of_eq_genericPoint hU _ hyU hη
  have hgerm (a : Γ(M, U)) : π.stalkMap (genericPoint N) (M.presheaf.germ U _ hyU a) =
      N.presheaf.germ V (genericPoint N) hηV (π.appLE U V hVU a) := by
    rw [π.germ_stalkMap_apply U _ hyU a, Scheme.Hom.appLE, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
  have hbij : Function.Bijective (π.stalkMap (genericPoint N)) := ConcreteCategory.bijective_of_isIso _
  have hinj : Function.Injective (algebraMap Γ(M, U) Γ(N, V)) := fun a a' h => by
    have h' : π.appLE U V hVU a = π.appLE U V hVU a' := h
    apply germ_injective_of_isIntegral M _ hyU
    apply hbij.1
    rw [hgerm, hgerm, h']
  have : FaithfulSMul Γ(M, U) Γ(N, V) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  let φ : Γ(N, V) ⟶ M.presheaf.stalk (π (genericPoint N)) :=
    N.presheaf.germ V (genericPoint N) hηV ≫ inv (π.stalkMap (genericPoint N))
  have hφ (c : Γ(N, V)) : π.stalkMap (genericPoint N) (φ c) = N.presheaf.germ V (genericPoint N) hηV c := by
    rw [← CommRingCat.comp_apply, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  let ψ : Γ(N, V) →ₐ[Γ(M, U)] M.presheaf.stalk (π (genericPoint N)) :=
    { φ.hom with
      commutes' := fun a ↦ hbij.1 ((hφ _).trans (hgerm a).symm) }
  have hψ : Function.Injective ψ := fun a b h => by
    apply germ_injective_of_isIntegral N _ hηV
    rw [← hφ, ← hφ]
    exact congrArg _ h
  have : Algebra.IsAlgebraic Γ(M, U) (M.presheaf.stalk (π (genericPoint N))) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(M, U))
  have : Algebra.IsAlgebraic Γ(M, U) Γ(N, V) := Algebra.IsAlgebraic.of_injective ψ hψ
  exact ringKrullDim_le_of_isAlgebraic _ _

theorem exists_isIso_restrict {Y N M : Scheme.{0}} [IsIntegral Y] [IsIntegral N] [IsIntegral M] (jN : Y ⟶ N)
    [IsDominant jN] (π : N ⟶ M) [IsSeparated π] [LocallyOfFiniteType π] (j : Y ⟶ M) [Flat j] [SurjectiveOnStalks j]
    (h : jN ≫ π = j) : ∃ U : M.Opens, (U : Set M).Nonempty ∧ IsIso (π ∣_ U) := by
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j (genericPoint Y)
  let φ : Spec (M.presheaf.stalk (j (genericPoint Y))) ⟶ N :=
    Spec.map (inv (j.stalkMap (genericPoint Y))) ≫ Y.fromSpecStalk (genericPoint Y) ≫ jN
  have hφ : φ ≫ π = M.fromSpecStalk (j (genericPoint Y)) ≫ 𝟙 M := by
    simp only [φ, Category.assoc, h, Category.comp_id]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id,
      Category.id_comp]
  obtain ⟨U, hU, g, hg₁, hg₂⟩ := spread_out_of_isGermInjective' (𝟙 M) π φ hφ
  rw [Category.comp_id] at hg₂
  have : IsDominant (Y.fromSpecStalk (genericPoint Y)) :=
    ⟨((dense_iff_closure_eq.2 (genericPoint_spec Y)).mono
      (Set.singleton_subset_iff.2 ⟨_, Scheme.fromSpecStalk_closedPoint⟩))⟩
  have : IsDominant φ := inferInstance
  have : IsDominant g := by
    rw [hg₁] at this
    exact IsDominant.of_comp (U.fromSpecStalkOfMem _ hU) g
  exact ⟨U, ⟨_, hU⟩, GlobalTheory.ZH.isIso_morphismRestrict_of_local_dominant_sections π U fun y hy =>
    ⟨U, U.ι, inferInstance, g, ⟨⟨y, hy⟩, rfl⟩, by simp, ‹_›, hg₂⟩⟩

theorem exists_normal_dominating (F : Type) [Field F] [NumberField F] (Y : Var F) (M M' : TrueGeo.Model Y) :
    ∃ (N : TrueGeo.Model Y) (π : N.X ⟶ M.X) (π' : N.X ⟶ M'.X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X ∧
      π ≫ M.p = N.p ∧ π' ≫ M'.p = N.p ∧ N.j ≫ π = M.j ∧ N.j ≫ π' = M'.j ∧
      (∃ U : M.X.Opens, (U : Set M.X).Nonempty ∧ IsIso (π ∣_ U)) ∧
      ∃ U : M'.X.Opens, (U : Set M'.X).Nonempty ∧ IsIso (π' ∣_ U) := by
  have H₀ := M.pb
  have := M.ar.isIntegral
  have := M'.ar.isIntegral
  have := M.ar.isLocallyNoetherian
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  have : IsProper M'.p := CommonModel.isProper_of_isProjOver M'.ar.isProjOver
  let r := pullback.fst M.p M'.p
  let h : Y.X ⟶ pullback M.p M'.p := pullback.lift M.j M'.j (M.pb.w.trans M'.pb.w.symm)
  have hr : h ≫ r = M.j := pullback.lift_fst _ _ _
  have hr' : h ≫ pullback.snd M.p M'.p = M'.j := pullback.lift_snd _ _ _
  have hW : IsProjOver (r ≫ M.p) := GlobalTheory.ProjSpace.isProjOver_pullback M.ar.isProjOver M'.ar.isProjOver
  have w : h ≫ r ≫ M.p = Y.str ≫ spMap (algebraMap (𝓞 F) F) := by rw [← Category.assoc, hr, H₀.w]
  have hb := IsPullback.of_hasPullback (r ≫ M.p) (spMap (algebraMap (𝓞 F) F))
  let f' : Y.X ⟶ pullback (r ≫ M.p) (spMap (algebraMap (𝓞 F) F)) := pullback.lift h Y.str w
  let ρ : pullback (r ≫ M.p) (spMap (algebraMap (𝓞 F) F)) ⟶ Y.X :=
    H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact hb.w)
  have hρ : ρ ≫ Y.str = pullback.snd _ _ := H₀.lift_snd _ _ _
  have hfρ : f' ≫ ρ = 𝟙 Y.X := by
    apply H₀.hom_ext
    · rw [Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]
    · rw [Category.assoc, hρ, pullback.lift_snd, Category.id_comp]
  have : IsSeparated (ρ ≫ Y.str) := by rw [hρ]; infer_instance
  have : IsSeparated ρ := IsSeparated.of_comp ρ Y.str
  have : IsClosedImmersion (f' ≫ ρ) := by rw [hfρ]; infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ρ
  have hh : h = f' ≫ 𝟙 _ ≫ pullback.fst _ _ := by rw [Category.id_comp, pullback.lift_fst]
  have : IsAffineHom (pullback.fst (r ≫ M.p) (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : IsAffineHom h := by rw [hh]; infer_instance
  have hpb := GlobalTheory.isPullback_toNormalization_of_isLocalization (M := nonZeroDivisors (𝓞 F)) hb f' (𝟙 _) h hh
  rw [Category.id_comp] at hpb
  have hfin : IsFinite h.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) h (r ≫ M.p) F Y.str w
  have : GlobalTheory.IsNormalScheme Y.X := Y.isNormalScheme
  have : GlobalTheory.IsNormalScheme h.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral h
  have hint : IsIntegral h.normalization := inferInstance
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat M.j := MorphismProperty.of_isPullback M.pb.flip ‹_›
  have : Flat M'.j := MorphismProperty.of_isPullback M'.pb.flip ‹_›
  have : IsPreimmersion M.j := MorphismProperty.of_isPullback M.pb.flip ‹_›
  have : IsPreimmersion M'.j := MorphismProperty.of_isPullback M'.pb.flip ‹_›
  have e₁ : h.toNormalization ≫ h.fromNormalization ≫ r = M.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr]
  have e₂ : h.toNormalization ≫ h.fromNormalization ≫ pullback.snd M.p M'.p = M'.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr']
  have hU := exists_isIso_restrict h.toNormalization (h.fromNormalization ≫ r) M.j e₁
  have hU' := exists_isIso_restrict h.toNormalization (h.fromNormalization ≫ pullback.snd M.p M'.p) M'.j e₂
  have hdim : topologicalKrullDim h.normalization = (Y.dim + 1 : ℕ) := by
    obtain ⟨U, hne, _⟩ := hU
    obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict (h.fromNormalization ≫ r) U hne.to_subtype
    have := surjective_of_isDominant_of_isClosed_range (h.fromNormalization ≫ r)
      (h.fromNormalization ≫ r).isClosedMap.isClosed_range
    rw [← M.ar.dim_eq]
    exact (dim_le_of_birational (h.fromNormalization ≫ r)).antisymm
      (PosBaseChange.dim_le_of_isClosedMap (h.fromNormalization ≫ r).isClosedMap
        (h.fromNormalization ≫ r).surjective)
  have hfl : Flat (h.fromNormalization ≫ r ≫ M.p) := GlobalTheory.flat_fromNormalization_comp h F (r ≫ M.p) Y.str w
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have hpb' := hpb.paste_vert hb
  rw [pullback.lift_snd] at hpb'
  refine ⟨⟨h.normalization, h.fromNormalization ≫ r ≫ M.p,
    ⟨M.ar.isDomain, M.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hW, inferInstance, hdim⟩,
    h.toNormalization, hpb'⟩, h.fromNormalization ≫ r, h.fromNormalization ≫ pullback.snd M.p M'.p,
    GlobalTheory.IsNormalScheme.pred _, Category.assoc _ _ _, ?_, e₁, e₂, hU, hU'⟩
  change (h.fromNormalization ≫ pullback.snd M.p M'.p) ≫ M'.p = h.fromNormalization ≫ r ≫ M.p
  rw [Category.assoc, ← pullback.condition]

end GlobalTheory.ModelDom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProjectedLift

open Formalism.IndefR.Lev


open scoped Pointwise in
theorem not_isConjPl {D : D7} (P : Formalism.L2.Host.PiBar D.host) {k k' : Fin 2} {w w' : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : P.Div k w) (hw' : P.Div k' w') : ¬ Lev.IsConjPl w w' := by
  intro hc
  have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hz, hzv⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext
      ((hzv.trans (bridge_star_holds D.R D.host _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
    exact e ▸ hz
  obtain ⟨v, hv, -⟩ := GlobalTheory.Mem.Chr.existsUnique_conjPl D.host.conj.toRingEquiv w
  have hv' := (GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj w v).1 hv
  have hvw : v = w' := HeightOneSpectrum.ext (v.isMaximal.eq_of_le w'.isPrime.ne_top (hv' ▸ hle))
  subst hvw
  obtain ⟨ho, hiff⟩ := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w
    (P.overP hw)).2.2.2 (P.pb k) (P.pb_over k) v hv
  have hk : k = k' := by
    by_contra hne
    have hg : D.host.g k ≠ D.host.g k' := by
      fin_cases k <;> fin_cases k'
      · exact absurd rfl hne
      · exact D.host.g_ne
      · exact D.host.g_ne.symm
      · exact absurd rfl hne
    obtain ⟨s, t, hst⟩ : IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) ((D.host.g k' : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime k) (D.host.g_prime k')).2 hg)
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hst]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ ho) (v.asIdeal.mul_mem_left _ (P.overP hw'))
  subst hk
  exact hiff.1 hw hw'

theorem conv_of_idem {H : Type} [Group H] [Fintype H] (z : MonoidAlgebra ℂ H) (hz : z * z = z) (g : H) :
    ∑ a, z.coeff a * z.coeff (a⁻¹ * g) = z.coeff g := by
  conv_rhs => rw [← hz]
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  simp

section Act

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank} {G : Type} [Group G] [Fintype G]

theorem mult_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) :
    Mult θ M J χ ≤ Mult θ M J' χ' :=
  Submodule.span_mono fun X hX => ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩

theorem postOn_gaL_mem (hθ : IsInfFam θ) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) {X : MMap M}
    (hX : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    postOn M (gaL V β L eG c) X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) := by
  have e : postOn M (gaL V β L eG c) X = ∑ g, c g • postOn M (actL V β L (eG g)) X := by
    ext v h
    simp [gaL, postOn_apply]
  rw [e]
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _
    (GlobalTheory.FlagAction.finiteGroupAction_preserves_principalFlagMultiplicity θ M hθ β L (eG g) X hX _ fun _ => rfl)

theorem gaL_gaL (hL : LiftsExist V β L) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g)
    {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) : gaL V β L eG c (gaL V β L eG c F) = gaL V β L eG c F := by
  letI : Fintype (G0 L.Pg L.r) := Fintype.ofEquiv G eG.toEquiv
  have e : ∀ F, gaL V β L eG c F = ∑ g, c (eG.symm g) • actG0 V β L g F := fun F => by
    unfold gaL
    rw [LinearMap.sum_apply]
    refine Fintype.sum_equiv eG.toEquiv _ _ fun g => ?_
    show c g • actG0 V β L (eG g) F = c (eG.symm (eG g)) • actG0 V β L (eG g) F
    rw [MulEquiv.symm_apply_apply]
  rw [e, e]
  refine GlobalTheory.FlagAction.convIdempotent_act V β L hL (fun g => c (eG.symm g)) (fun g => ?_) F hF
  rw [← hc]
  refine Fintype.sum_equiv eG.symm.toEquiv _ _ fun a => ?_
  show c (eG.symm a) * c (eG.symm (a⁻¹ * g)) = c (eG.symm a) * c ((eG.symm a)⁻¹ * eG.symm g)
  rw [map_mul, map_inv]

theorem postOn_gaL_mem_goodPart (hθ : IsInfFam θ) (hL : LiftsExist V β L) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)
    (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g) {X : MMap M}
    (hX : X ∈ Mult θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L))) :
    postOn M (gaL V β L eG c) X ∈
      goodPart θ M (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) (gaL V β L eG c) := by
  refine ⟨postOn_gaL_mem hθ eG c hX, ?_⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  ext1 v
  exact gaL_gaL hL eG c hc (GlobalTheory.hasType_of_mem_mult θ M β _ X hX v)

end Act

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem liftsExist_rows (h : R.toLevCh.Is A.μ0) : LiftsExist (Yc D 0) (R.βY 0) (R.dat0 R.triv) := by
  obtain ⟨c, hc⟩ := h.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_) (Finset.disjoint_empty_right _)
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  obtain ⟨k', hk'⟩ := (h.Pg PP').1 (hP'.resolve_right (Finset.notMem_empty _))
  exact not_isConjPl R.C.P hk hk'

theorem eC_conv (hr : R.grp_record) (g : G) :
    ∑ a, RealDat.eC (A := A) D.what₂.embLL a * RealDat.eC (A := A) D.what₂.embLL (a⁻¹ * g) =
      RealDat.eC (A := A) D.what₂.embLL g := by
  obtain ⟨eR, _, _, h, _⟩ := hr
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G eR.toEquiv
  unfold RealDat.eC
  simp only [h]
  rw [← conv_of_idem _ (GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D).2 (eR g)]
  refine Fintype.sum_equiv eR.toEquiv _ _ fun a => ?_
  show _ = D.ntypes.e0.coeff (eR a) * D.ntypes.e0.coeff ((eR a)⁻¹ * eR g)
  rw [map_mul, map_inv]

theorem thDn_mem_CC (t : T) (x : (R.HX t).H) : R.thDn t x ∈ R.CC t 0 :=
  (Lift.thetaDn (R.CC t) (R.ioY t) (D.R.m - 1) (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict x))).2

theorem thDn_mem (t : T) (x : (R.HX t).H) :
    PiTensorProduct.lift.symm (R.thDn t x) ∈
      Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
  have hr : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Ranks.rankY]
  have e0 := GlobalTheory.levG_twist_trivial_of_rank_eq (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) hr R.Pg (R.Q t) R.triv
    R.chi (R.xiR t)
  have e1 := e0.1
  have e2 := e0.2
  have h1 : R.thDn t x ∈ MultT R.θ (R.MY 0) (levS _ (R.βY 0) (R.datYt t 0 R.triv)) (levChi _ (R.βY 0) (R.datYt t 0 R.triv)) :=
    thDn_mem_CC R t x
  have h2 := (mem_multT R.θ (R.MY 0) _ _ _).1 h1
  have e1' : levG (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) = levG (Yc D 0) (R.βY 0) (R.dat0 R.triv) := e1
  have e2' : ∀ k ∈ levG (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv),
      levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) k = levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k := e2
  have h3 : ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 R.triv), k ∈ levS (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) ∧
      levChi (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) k = levChi (Yc D 0) (R.βY 0) (R.dat0 R.triv) k := fun k hk => by
    have hk' : k ∈ levG (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) := by rw [e1']; exact hk
    exact ⟨hk', e2' k hk'⟩
  exact mult_mono h3 h2

theorem proj_thDn_mem (h : R.toLevCh.Is A.μ0) (hθ : R.models_inf) (hr : R.grp_record) (t : T) (x : (R.HX t).H) :
    postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x)) ∈ R.EEat R.triv :=
  postOn_gaL_mem_goodPart (L := R.dat0 R.triv) hθ (liftsExist_rows R h) R.eG _ (eC_conv R hr) (thDn_mem R t x)

end Real

theorem exists_chain_Th : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → ∃ Th, ({ R with Th := Th } : RealDat D A Ks).chain_Th := by
  intro D G _ _ Pl0 T A Ks _ _ _ R h _ hM hr
  have key : ∀ t, ∃ y : (R.HX t).H →ₗ[ℂ] R.HE.H,
      ∀ x, R.HE.e (y x) = postOn (R.MY 0) R.e0 (PiTensorProduct.lift.symm (R.thDn t x)) := fun t =>
    GlobalTheory.HilbertModel.exists_lift hM.HE
      (postOn (R.MY 0) R.e0 ∘ₗ
        (PiTensorProduct.lift.symm : (SmT (R.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) ≃ₗ[ℂ] MMap (R.MY 0)).toLinearMap ∘ₗ R.thDn t)
      (proj_thDn_mem R h hM.inf hr t)
  choose Th hTh using key
  exact ⟨Th, hTh⟩

end GlobalTheory.ProjectedLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexSpanRationalLiftFormsEqBasePart
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexSpanRationalLiftFormsEqBasePart
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.RatSpan

theorem span_jW_wp : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix), Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL))) = (R.Wp3 i p).comap (Y.mj.eW i) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i p
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim

  have hpt : ∀ y : Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL,
      (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) =
        Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i (Z.jW i y)) := by
    intro y
    rw [Z.jW_read]
    refine (GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i y).trans ?_
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0))
      (congrArg ((R.FW i).j (sg0 D A3.A)) (Fintype.linearCombination_apply _ _ _)).symm
  have hmem : ∀ y, y ∈ (s0Of R F).Wp i p ↔ Z.jW i y ∈ (R.Wp3 i p).comap (Y.mj.eW i) := by
    intro y
    show (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y) ∈ (R.toCx3 F).Wp i p ↔ _
    exact (Iff.of_eq (congrArg (· ∈ (R.toCx3 F).Wp i p) (hpt y))).trans Iff.rfl
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact (hmem y).1 hy
  · intro x hx
    have hnP : 0 < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
    have hinj : Function.Injective (Y.mj.eW i) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro d hd
      have h1 : RealDat.nP F.lv2 false * ‖d‖ ^ 2 = 0 := by rw [← Y.mj.eW_norm i d, hd]; simp
      have h2 : ‖d‖ ^ 2 = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact absurd h hnP.ne'
        · exact h
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2)
    have hw := (R.toCx3 F).principal_form_injective false hR.kForm hR.ewNorm (hR.h4pos.2.2 false) i
    set U : Submodule ℂ ((R.toCx3 F).W i) := Submodule.span ℂ
      ((fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) '' ((R.toCx3 F).WpK false i p : Set _)) with hU
    have hUT : U = (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) := by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [hU, Submodule.span_le]
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨hy, LinearMap.mem_range_self _ _⟩
      · rw [← (R.toCx3 F).finrank_WpK F.cr false hR.h4pos hR.kForm hR.ewNorm hR.types0 hR.lifts0.1 hR.ratTh
          hR.liftHyp0.h3W hR.partsW i p]
        exact (finrank_le_cpt A3.A.v0.embedding ((R.toCx3 F).w0C false i) hw U ((R.toCx3 F).WpK false i p)
          (fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩)).trans (Submodule.finrank_mono inf_le_left)
    have hWS : Y.mj.eW i x ∈ R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
      rw [hH.aux.levelW false i (sg0 D A3.A), ← Y.mj.eW_range i]
      exact LinearMap.mem_range_self _ _
    rw [← GlobalTheory.Mem.LiftTheta.goodForm_span] at hWS
    have h1 : Tw.mk (twAt D.what₂.embLL A3.A.v0) (Y.mj.eW i x) ∈ U := by
      rw [hUT]
      refine ⟨hx, ?_⟩
      have h2 := Submodule.mem_map_of_mem (f := Tw.mkL (twAt D.what₂.embLL A3.A.v0) (R.HW i (sg0 D A3.A)).H) hWS
      rw [Submodule.map_span] at h2
      refine (Submodule.span_le.2 ?_) h2
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨Pi.single k 1, ?_⟩
      have h3 := GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i (Pi.single k 1)
      exact (congrArg ((R.toCx3 F).w0C false i) (cpt_single A3.A.v0.embedding k).symm).trans h3
    let outL : (R.toCx3 F).W i →ₛₗ[cj (twAt D.what₂.embLL A3.A.v0)] (R.HW i (sg0 D A3.A)).H :=
      { toFun := fun z => Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) z
        map_add' := fun a b => Tw.out_add (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) a b
        map_smul' := fun c a => Tw.out_smul (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) c a }
    have h4 : Y.mj.eW i x ∈ U.map outL := Submodule.mem_map_of_mem (f := outL) h1
    rw [hU, Submodule.map_span, ← Set.image_comp] at h4
    have h5 : Submodule.span ℂ ((outL ∘ fun y => (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y)) ''
        ((R.toCx3 F).WpK false i p : Set _)) ≤
        (Submodule.span ℂ ((Z.jW i) '' (((R.toCx3 F).WpK false i p : Set (Fin ((R.toCx3 F).dW false i) → D.what₂.LL)) :
          Set (Fin (((R.toCx3 F).data F.cr false).dW i) → D.what₂.LL)))).map (Y.mj.eW i) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨Z.jW i y, Submodule.subset_span ⟨y, hy, rfl⟩, ?_⟩
      show Y.mj.eW i (Z.jW i y) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)
        ((R.toCx3 F).w0C false i (cpt A3.A.v0.embedding y))
      exact (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H)) (hpt y)).symm
    obtain ⟨x', hx', hxx⟩ := h5 h4
    rw [← hinj hxx]
    exact hx'

end GlobalTheory.Mem.R3.RatSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexSpanRationalLiftFormsEqBasePartStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexSpan_rationalLiftForms_eq_basePart : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix), Submodule.span ℂ ((Z.jW i) '' ((s0Of R F).Wp i p : Set (Fin ((s0Of R F).dW i) → D.what₂.LL))) = (R.Wp3 i p).comap (Y.mj.eW i) := by
  first | exact @GlobalTheory.Mem.R3.RatSpan.span_jW_wp | exact GlobalTheory.Mem.R3.RatSpan.span_jW_wp | (intros; apply GlobalTheory.Mem.R3.RatSpan.span_jW_wp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousSplitCentre
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume GlobalTheory.HeckeOne Matrix

noncomputable section

namespace GlobalTheory.OneRep.SplitTwist

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_splitCentre : Continuous (splitCentre E a) := by
  have e : splitCentre E a = fun t : ℝ =>
      GeneralLinearGroup.scalar (Fin a) (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) :=
    funext splitCentre_eq_scalar
  rw [e]
  refine Continuous.units_map _ ?_ |>.comp ((continuous_infId E).comp
    (continuous_expU.comp (continuous_pi fun _ => Complex.continuous_ofReal)))
  change Continuous fun x : Ad E => Matrix.diagonal fun _ : Fin a => x
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

end GlobalTheory.OneRep.SplitTwist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.QCoh GlobalTheory.Twist RingTheory.Sequence
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Adelic

namespace GlobalTheory.CutDegree

section Sheaf

variable {X : Scheme.{0}} {L : LB X}

theorem injective_stalkLinear_cutHom (F : X.Modules) (hL : L.IsLB) (s : L.Sec) (i : L.ι) {x : X} (hx : x ∈ L.U i)
    (h : IsSMulRegular (F.presheaf.stalk x :) (X.presheaf.germ _ x hx (s.f i))) :
    Function.Injective (stalkLinear (cutHom F hL s) x) := by
  let e := stalkEquivOfLinear (F := twistZ F L (-1)) (G := F) (fun V hV => zchartEquiv hL (-1) i hV)
    (fun hV h' t => zchartEquiv_resM hL i hV h' t) hx
  have key : ⇑(stalkLinear (cutHom F hL s) x) = (X.presheaf.germ _ x hx (s.f i) • ·) ∘ e := funext fun u => by
    obtain ⟨V, hV, hxV, u, rfl⟩ := exists_germ_eq_of_mem hx u
    rw [stalkLinear_germ, cutHom_app F hL s i hV, QCoh.germ_smul, Function.comp_apply,
      stalkEquivOfLinear_germ _ _ hx hV]
    exact congrArg (· • _) (Cartier.germ_resG hV x hxV _)
  rw [key]
  exact h.comp e.injective

theorem nonempty_stalk_cut_equiv (F : X.Modules) (hL : L.IsLB) (s : L.Sec) (i : L.ι) {x : X} (hx : x ∈ L.U i) :
    Nonempty (QuotSMulTop (X.presheaf.germ _ x hx (s.f i)) (F.presheaf.stalk x :) ≃ₗ[X.presheaf.stalk x]
      ((cut F hL s).presheaf.stalk x :)) := by
  refine ⟨(Submodule.quotEquivOfEq _ _ ?_).trans
    ((stalkLinear (cutπ F hL s) x).quotKerEquivOfSurjective (stalkLinear_surjective _ x))⟩
  ext t
  rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker]
  refine Iff.trans ?_ ((isMulBy_cutHom F hL s).stalkLinear_π_eq_zero_iff i hx t).symm
  simp

theorem topologicalKrullDim_le_zero_of_subset {T : Type} [TopologicalSpace T] {S : Finset T}
    (hc : ∀ x ∈ S, IsClosed ({x} : Set T)) {s : Set T} (hs : s ⊆ S) : topologicalKrullDim s ≤ 0 := by
  have : Finite s := (S.finite_toSet.subset hs).to_subtype
  have : T1Space s := ⟨fun x => by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective] using
      (hc x.1 (hs x.2)).preimage (continuous_subtype_val (p := (· ∈ s)))⟩
  exact topologicalKrullDim_zero_of_discreteTopology s

variable {k : Type} [Field k] (f : X ⟶ Sp k)

theorem interNum_sub_eq (hf : IsProjOver f) {F G : X.Modules} [IsFiniteQC F] [IsFiniteQC G] (φ : G ⟶ F) {d : ℕ}
    {P : Fin d → LB X} (hP : ∀ i, (P i).IsLB) :
    letI := algebraΓOfHom f
    interNum k F P - interNum k G P = interNum k (cokernel φ) P - interNum k (kernel φ) P := by
  letI := algebraΓOfHom f
  have := isNoetherian_of_isProjOver hf
  have fin : ∀ (H : X.Modules) [IsFiniteQC H], FiniteCohTwists k H := fun H _ =>
    finiteCohTwists_of_isProjOver (fun _ => rfl) H hf
  have h₁ := interNum_cokernel (kernel.ι φ) hP (fin _) (fin _)
  have h₂ := interNum_cokernel (kernel.ι (cokernel.π φ)) hP (fin _) (fin _)
  have e₁ : cokernel (kernel.ι φ) ≅ kernel (cokernel.π φ) := Abelian.coimageIsoImage φ
  have e₂ : cokernel (kernel.ι (cokernel.π φ)) ≅ cokernel φ :=
    (cokernelIsCokernel _).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (cokernel.π φ)))
  rw [interNum_congr k e₁] at h₁
  rw [interNum_congr k e₂] at h₂
  omega

theorem interNum_eq_sum_length (hf : IsProjOver f) (hL : L.IsLB) (c : X → L.ι) (hc : ∀ x, x ∈ L.U (c x))
    (S : Finset X) (hS : ∀ x ∈ S, IsClosed ({x} : Set X)) (l : List L.Sec) (F : X.Modules) [IsFiniteQC F]
    (hz : ∀ x ∈ support F, (∀ s ∈ l, x ∉ nonzeroLocus s) → x ∈ S)
    (hr : ∀ x ∈ S, IsWeaklyRegular (F.presheaf.stalk x :) (l.map fun s => X.presheaf.germ _ x (hc x) (s.f (c x)))) :
    letI := algebraΓOfHom f
    interNum k F (fun _ : Fin l.length => L) = (∑ x ∈ S, (Module.length (X.presheaf.stalk x)
      ((F.presheaf.stalk x :) ⧸ (Ideal.ofList (l.map fun s => X.presheaf.germ _ x (hc x) (s.f (c x))) • ⊤ :
        Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :)))).toNat * f.residueDegree x : ℕ) := by
  letI := algebraΓOfHom f
  have := isNoetherian_of_isProjOver hf
  have := ((isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hf).1
  induction l generalizing F with
  | nil =>
    have hs : support F ⊆ S := fun x hx => hz x hx (by simp)
    have hd : suppDim F ≤ 0 := topologicalKrullDim_le_zero_of_subset hS hs
    have : IsEmpty (Fin ([] : List L.Sec).length) := inferInstanceAs (IsEmpty (Fin 0))
    rw [interNum_of_isEmpty, chi_eq_hdim_zero_of_suppDim_le_zero k hd, hdim_zero_eq_sum_toNat f hd hs]
    refine congrArg _ <| Finset.sum_congr rfl fun x _ => ?_
    rw [(Submodule.quotEquivOfEqBot (Ideal.ofList [] • ⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x :))
      (by simp only [Ideal.ofList_nil]; exact Submodule.bot_smul _)).length_eq.symm]
    rfl
  | cons s l ih =>
    have := isFiniteQC_twist (F := F) (isLB_lbZPow hL (-1))
    have e : (fun _ : Fin (s :: l).length => L) = (Fin.cons L (fun _ => L) : Fin (l.length + 1) → LB X) :=
      funext (Fin.cases rfl fun _ => rfl)
    have h0 : ∀ x ∈ S, Subsingleton ((kernel (cutHom F hL s)).presheaf.stalk x :) := fun x hx => by
      have h := injective_stalkLinear_cutHom F hL s (c x) (hc x) ((isWeaklyRegular_cons_iff _ _ _).1 (hr x hx)).1
      refine subsingleton_of_forall_eq 0 fun t => stalkLinear_injective (kernel.ι _) x (h ?_)
      rw [← LinearMap.comp_apply, ← stalkLinear_comp, kernel.condition, stalkLinear_zero, map_zero, map_zero]
      rfl
    have hK := ih (kernel (cutHom F hL s)) (fun x hx hl => ?_) fun x hx => ?_
    have hC := ih (cut F hL s) (fun x hx hl => ?_) fun x hx => ?_
    · rw [e, interNum_cons k F hL fun _ => hL, interNum_sub_eq f hf (cutHom F hL s) fun _ => hL, hK]
      rw [Finset.sum_eq_zero (fun x hx => ?_), Nat.cast_zero, sub_zero]
      · refine hC.trans (congrArg _ <| Finset.sum_congr rfl fun x _ => ?_)
        obtain ⟨q⟩ := nonempty_stalk_cut_equiv F hL s (c x) (hc x)
        rw [List.map_cons, (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner _ _ _).length_eq,
          (Submodule.Quotient.equiv _ _ q (by rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])).length_eq]
      · have := h0 x hx
        rw [Module.length_eq_zero]
        simp
    · rw [support_cut] at hx
      exact hz x hx.1 (List.forall_mem_cons.2 ⟨hx.2, hl⟩)
    · obtain ⟨q⟩ := nonempty_stalk_cut_equiv F hL s (c x) (hc x)
      exact (q.isWeaklyRegular_congr _).1 ((isWeaklyRegular_cons_iff _ _ _).1 (hr x hx)).2
    · have h₁ := support_subset_of_mono (kernel.ι (cutHom F hL s)) hx
      rw [support_twist (isLB_lbZPow hL (-1))] at h₁
      refine hz x h₁ (List.forall_mem_cons.2 ⟨fun hs => notMem_support_iff.2 ?_ hx, hl⟩)
      have hu := (X.mem_basicOpen _ x (hc x)).1 ((Cartier.mem_nonzeroLocus_iff s _ (hc x)).1 hs)
      have h := injective_stalkLinear_cutHom F hL s (c x) (hc x) (hu.isSMulRegular _)
      refine subsingleton_of_forall_eq 0 fun t => stalkLinear_injective (kernel.ι _) x (h ?_)
      rw [← LinearMap.comp_apply, ← stalkLinear_comp, kernel.condition, stalkLinear_zero, map_zero, map_zero]
      rfl
    · have := h0 x hx
      exact ⟨fun _ _ _ _ _ => Subsingleton.elim _ _⟩

end Sheaf

section Algebra

variable {K R : Type} [Field K] [CommRing R]

end Algebra

section BaseChange

variable {k K : Type} [Field k] [Field K] {X X' : Scheme.{0}} {f : X ⟶ Sp k} {f' : X' ⟶ Sp K} {π : X' ⟶ X}
  {φ : k →+* K}

theorem ringKrullDim_stalk {d : ℕ} (h : SmoothOfRelativeDimension d f') {z : X'} (hz : IsClosed ({z} : Set X')) :
    ringKrullDim (X'.presheaf.stalk z) = d := by
  have := (StabFlat.stalk_of_smooth_local K X' f' d h z hz _ (Spec.map_preimage _).symm inferInstance).2.2.2
  rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot] at this
  exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)).symm.trans this

end BaseChange

section Count

variable {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} {f : X ⟶ Sp K} {L : LB X}

end Count

section Cut

variable {F : Type} [Field F] (Y : Var F) {Δ : Y.Dv} {n : ℕ} (b : Fin n → Y.H0 Δ)


end Cut

end GlobalTheory.CutDegree
end
end
