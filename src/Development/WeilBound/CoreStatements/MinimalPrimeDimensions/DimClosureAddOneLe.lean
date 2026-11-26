module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.RangeOfMemSupportPush
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.VB

namespace ChowFormHeightComparison₂.CF.V

section Stalk

variable {X Y : Scheme.{0}} (i : Y ⟶ X) [IsClosedImmersion i] (G : Y.Modules)

def pushStalk (y : Y) :
    (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i y) :) →+ (G.presheaf.stalk y :) :=
  (TopCat.Presheaf.stalkPushforward Ab.{0} i.base G.presheaf y).hom

omit [IsClosedImmersion i] in
theorem pushStalk_germ (y : Y) (U : X.Opens) (h : i y ∈ U) (s : Γ((Scheme.Modules.pushforward i).obj G, U)) :
    pushStalk i G y (((Scheme.Modules.pushforward i).obj G).presheaf.germ U (i y) h s) =
      G.presheaf.germ (i ⁻¹ᵁ U) y h s :=
  TopCat.Presheaf.stalkPushforward_germ_apply Ab.{0} i.base G.presheaf U y h s

theorem pushStalk_bijective (y : Y) : Function.Bijective (pushStalk i G y) :=
  have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing Ab.{0} (f := i.base)
    i.isClosedEmbedding.isInducing G.presheaf y
  ConcreteCategory.bijective_of_isIso (TopCat.Presheaf.stalkPushforward Ab.{0} i.base G.presheaf y)

omit [IsClosedImmersion i] in
theorem pushStalk_smul (y : Y) (r : X.presheaf.stalk (i y))
    (t : (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i y) :)) :
    pushStalk i G y (r • t) = i.stalkMap y r • pushStalk i G y t := by
  obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hV, s, rfl⟩ := Twist.exists_germ_eq_of_mem hU t
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) (i y) hV a, ← QCoh.germ_smul, pushStalk_germ, pushStalk_germ,
    Scheme.Hom.germ_stalkMap_apply]
  exact QCoh.germ_smul (F := G) (U := i ⁻¹ᵁ V) y hV _ s

theorem length_push (y : Y) :
    Module.length (X.presheaf.stalk (i y)) (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i y) :) =
      Module.length (Y.presheaf.stalk y) (G.presheaf.stalk y :) := by
  letI := (i.stalkMap y).hom.toAlgebra
  letI : Module (X.presheaf.stalk (i y)) (G.presheaf.stalk y :) := Module.compHom _ (i.stalkMap y).hom
  haveI : IsScalarTower (X.presheaf.stalk (i y)) (Y.presheaf.stalk y) (G.presheaf.stalk y :) :=
    .of_algebraMap_smul fun _ _ => rfl
  let l : (((Scheme.Modules.pushforward i).obj G).presheaf.stalk (i y) :) →ₗ[X.presheaf.stalk (i y)]
      (G.presheaf.stalk y :) :=
    { toFun := pushStalk i G y, map_add' := map_add _, map_smul' := pushStalk_smul i G y }
  rw [(LinearEquiv.ofBijective l (pushStalk_bijective i G y)).length_eq]
  exact Module.length_eq_of_surjective (S := X.presheaf.stalk (i y)) (i.stalkMap_surjective y)

theorem mem_support_push (y : Y) :
    i y ∈ support ((Scheme.Modules.pushforward i).obj G) ↔ y ∈ support G :=
  (Equiv.ofBijective _ (pushStalk_bijective i G y)).nontrivial_congr

theorem range_of_mem_support_push {x : X} (hx : x ∈ support ((Scheme.Modules.pushforward i).obj G)) :
    x ∈ Set.range i := by
  by_contra hr
  rw [mem_support_iff, ← not_subsingleton_iff_nontrivial] at hx
  refine hx (subsingleton_of_forall_eq 0 fun t => ?_)
  let W : X.Opens := ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨V, hVW, hV, s, rfl⟩ := Twist.exists_germ_eq_of_mem (U := W) hr t
  have h0 : s = 0 := section_eq_zero_of_germ (F := G) _ fun z hz => absurd ⟨z, rfl⟩ (hVW hz)
  rw [h0, map_zero]

end Stalk

variable {κ : Type} [Field κ]

theorem interNum_of_genRank_eq {Z : Scheme.{0}} [IsIntegral Z] [Algebra κ Γ(Z, ⊤)] (hp : IsProjOver (strHom κ (X := Z)))
    {d : ℕ} (hd : topologicalKrullDim Z ≤ d) {P : Fin d → LB Z} (hL : ∀ j, (P j).IsLB) (r : ℕ) :
    ∀ (G : Z.Modules) [QCoh.IsFiniteQC G], genRank G = r →
      interNum κ G P = r * interNum κ (GlobalTheory.structureModule Z) P := by
  have hf := algebraMap_eq_strHom κ Z
  have h1 : ∀ {F : Z.Modules} [QCoh.IsFiniteQC F], FiniteCohTwists κ F :=
    fun {F} _ => finiteCohTwists_of_isProjOver hf F hp
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hp
  induction r with
  | zero =>
    intro G _ h
    have h0 := topologicalKrullDim_add_one_le (QCoh.isClosed_support G) isClosed_univ
      fun x _ => ⟨genericPoint Z, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
    have h2 : topologicalKrullDim (Set.univ : Set Z) = topologicalKrullDim Z :=
      (Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq
    have : QCoh.suppDim G < Fintype.card (Fin d) := by
      rw [Fintype.card_fin]
      by_contra hc
      rw [not_lt] at hc
      have h3 : ((d : ℕ) : WithBot ℕ∞) + 1 ≤ d := (add_le_add_left hc 1).trans (h0.trans (h2.le.trans hd))
      have h4 : d + 1 ≤ d := by exact_mod_cast h3
      omega
    rw [interNum_eq_zero_of_isProjOver hf G hp this hL]
    simp
  | succ r ih =>
    intro G _ h
    obtain ⟨n, hn⟩ := (hA.eventually_isGloballyGenerated_twist G).exists
    have hM := isLB_lbPow hA.isLB n
    have := Twist.isFiniteQC_twist (F := G) hM
    have hr : genRank (twist G (lbPow A n)) = r + 1 := (genRank_twist hM).trans h
    obtain ⟨s, hs⟩ := exists_germ_ne_zero hn (by omega)
    have := mono_sectionHom s hs
    have e₁ : interNum κ (twist G (lbPow A n)) P = interNum κ G P :=
      (diffVanish_chiPic_of_isProjOver (d := d) hf G hp
        ((QCoh.suppDim_le G).trans hd)).interNum_twist (by simp) hL hM
    have e₂ := interNum_cokernel (k := κ) (QCoh.sectionHom s) hL h1 h1
    have e₃ := genRank_cokernel (QCoh.sectionHom s)
    rw [(isVB_structureModule Z).genRank_eq, hr] at e₃
    rw [ih _ (by omega)] at e₂
    push_cast
    linarith

theorem interNum_eq_sum {X : Scheme.{0}} [Algebra κ Γ(X, ⊤)] (hp : IsProjOver (strHom κ (X := X))) {d : ℕ}
    {P : Fin d → LB X} (hL : ∀ j, (P j).IsLB) (S : Set X) (T : Finset X) (deg : X → ℤ)
    (hT : ∀ z ∈ T, topologicalKrullDim (closure {z} : Set X) = d)
    (hS : ∀ z ∈ S, z ∉ T → topologicalKrullDim (closure {z} : Set X) < d)
    (hdeg : ∀ (Y : Scheme.{0}) (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y] [Algebra κ Γ(Y, ⊤)],
      (∀ r : κ, i.appTop (algebraMap κ Γ(X, ⊤) r) = algebraMap κ Γ(Y, ⊤) r) → i (genericPoint Y) ∈ T →
      interNum κ (GlobalTheory.structureModule Y) (fun j => (P j).pull i) = deg (i (genericPoint Y)))
    (F : X.Modules) (hF : IsFiniteQC F) (hFS : support F ⊆ S) :
    (∀ z ∈ T, Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :) ≠ ⊤) ∧
      interNum κ F P = ∑ z ∈ T, ((Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :)).toNat : ℤ) * deg z := by
  classical
  have := isNoetherian_of_isProjOver hp
  have hf := algebraMap_eq_strHom κ X
  have hz : ∀ (E : X.Modules) (z : X), z ∉ support E →
      Module.length (X.presheaf.stalk z) (E.presheaf.stalk z :) = 0 := fun E z h =>
    have := notMem_support_iff.1 h
    Module.length_eq_zero
  revert hFS
  refine QCoh.devissage X (fun F => support F ⊆ S →
    (∀ z ∈ T, Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :) ≠ ⊤) ∧
      interNum κ F P = ∑ z ∈ T, ((Module.length (X.presheaf.stalk z) (F.presheaf.stalk z :)).toNat : ℤ) * deg z)
    (fun E hE _ => ?_) (fun C hC h₁ h₃ p₁ p₃ hs => ?_) (fun Z hZ ih G hG hs => ?_) F hF
  · have h0 : ∀ z, Module.length (X.presheaf.stalk z) (E.presheaf.stalk z :) = 0 := fun z =>
      hz E z (by rw [support_eq_empty_iff.2 hE]; exact Set.notMem_empty _)
    refine ⟨fun z _ => by rw [h0]; simp, ?_⟩
    rw [interNum_eq_zero_of_isZero κ hE hL]
    simp [h0]
  · rw [support_eq_union_of_shortExact hC] at hs
    obtain ⟨a₁, b₁⟩ := p₁ (Set.subset_union_left.trans hs)
    obtain ⟨a₃, b₃⟩ := p₃ (Set.subset_union_right.trans hs)
    have := hC.mono_f
    have := hC.epi_g
    have hl (z : X) := Module.length_eq_add_of_exact (stalkLinear C.f z) (stalkLinear C.g z)
      (stalkLinear_injective _ z) (stalkLinear_surjective _ z) ((exact_iff_stalkLinear C).1 hC.exact z)
    refine ⟨fun z h => by rw [hl]; exact WithTop.add_ne_top.2 ⟨a₁ z h, a₃ z h⟩ , ?_⟩
    rw [interNum_shortExact hC hL (finiteCohTwists_of_isProjOver hf _ hp) (finiteCohTwists_of_isProjOver hf _ hp),
      b₁, b₃, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z h => ?_
    rw [hl, ENat.toNat_add (a₁ z h) (a₃ z h)]
    push_cast
    ring
  · have := isIntegral_red hZ
    letI := algebraΓAlong κ (redι Z)
    have hi := appTop_algebraMap_along κ (redι Z)
    have hpZ : IsProjOver (strHom κ (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
      rw [← comp_strHom hi]
      exact ProjSpace.isProjOver_comp_of_isClosedImmersion _ hp
    have hsub : support ((Scheme.Modules.pushforward (redι Z)).obj G) ⊆ Z := fun x hx =>
      range_redι Z ▸ range_of_mem_support_push _ G hx
    set ξ := redι Z (genericPoint _) with hξ
    have hcl : closure {ξ} = (Z : Set X) := by
      have h₁ := (genericPoint_spec _).image (redι Z).continuous
      rw [Set.image_univ, range_redι, Z.isClosed.closure_eq] at h₁
      exact h₁.def
    by_cases hr : genRank G = 0
    · have hFQ : IsFiniteQC ((Scheme.Modules.pushforward (redι Z)).obj G) :=
        ⟨inferInstance, fun _ hV => QCoh.finite_sections_pushforward (redι Z) _ hV
          (hF := QCoh.finite_sections G (hV.preimage (redι Z)))⟩
      refine ih _ hFQ ⟨hsub, fun hle => ?_⟩ hs
      exact genRank_eq_zero_iff.1 hr ((mem_support_push _ G _).1 (hle (hcl ▸ subset_closure rfl)))
    have hξS : ξ ∈ S := hs ((mem_support_push _ G _).2 (by_contra fun h => hr (genRank_eq_zero_iff.2 h)))
    have hdZ := topologicalKrullDim_red Z
    have hPZ : ∀ j, ((P j).pull (redι Z)).IsLB := fun j => LB.isLB_pull (hL j) _
    have hle : topologicalKrullDim (Z : Set X) ≤ d := by
      by_cases h : ξ ∈ T
      · exact (hcl ▸ hT ξ h).le
      · exact (hcl ▸ hS ξ hξS h).le
    have hoff : ∀ z ∈ T, z ≠ ξ → z ∉ support ((Scheme.Modules.pushforward (redι Z)).obj G) := by
      intro z hzT hne hzs
      have hzZ := hsub hzs
      have hsp : ξ ⤳ z := specializes_iff_mem_closure.2 (hcl ▸ hzZ)
      have h1 := topologicalKrullDim_add_one_le (s := closure {z}) isClosed_closure Z.isClosed fun x hx =>
        ⟨ξ, hcl ▸ subset_closure rfl, fun h => hne (hsp.antisymm (specializes_iff_mem_closure.2 h)).eq.symm,
          hsp.trans (specializes_iff_mem_closure.2 hx)⟩
      rw [hT z hzT] at h1
      have h4 : d + 1 ≤ d := by exact_mod_cast h1.trans hle
      omega
    have hlen : Module.length (X.presheaf.stalk ξ) (((Scheme.Modules.pushforward (redι Z)).obj G).presheaf.stalk ξ :) =
        genRank G := (length_push _ G _).trans (Module.length_eq_finrank _ _)
    rw [interNum_pushforward_of_isClosedImmersion hi G hL]
    refine ⟨fun z h => ?_, ?_⟩
    · by_cases e : z = ξ
      · subst e; rw [hlen]; exact ENat.coe_ne_top _
      · rw [hz _ z (hoff z h e)]; simp
    · by_cases h : ξ ∈ T
      · rw [Finset.sum_eq_single ξ (fun z hzT e => by rw [hz _ z (hoff z hzT e)]; simp) (fun h' => absurd h h'),
          hlen, interNum_of_genRank_eq hpZ (hdZ.le.trans hle) hPZ _ G rfl, hdeg _ (redι Z) hi h, ENat.toNat_coe]
      · rw [Finset.sum_eq_zero fun z hzT => by rw [hz _ z (hoff z hzT fun e => h (e ▸ hzT))]; simp]
        refine interNum_eq_zero_of_isProjOver (algebraMap_eq_strHom κ _) G hpZ ?_ hPZ
        rw [Fintype.card_fin]
        exact (QCoh.suppDim_le G).trans_lt (hdZ.trans_lt (hcl ▸ hS ξ hξS h))

end ChowFormHeightComparison₂.CF.V
end
end

section -- merged from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FinrankEqOfDimZero
set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier
open GroundTheory.Heights₂.Heights (IsProjPrime IsHomogIdeal IsRelevant relComps localMult chowDegree reduceMod divCycle)

namespace ChowFormHeightComparison₂.CF.V

section Alg

variable {κ Ω : Type} [Field κ] [Field Ω] [Algebra κ Ω] {m : ℕ}

theorem ker_aeval_eq (τ : Fin m → Ω) (k : Fin m) (hk : τ k = 1) :
    RingHom.ker (aeval τ : MvPolynomial (Fin m) κ →ₐ[κ] Ω) = GlobalTheory.CompHt.coneIdeal κ τ ⊔ Ideal.span {X k - 1} := by
  have hcomp : ∀ g : MvPolynomial (Fin m) κ, aeval τ g =
      ∑ d ∈ Finset.range (g.totalDegree + 1), aeval τ (homogeneousComponent d g) := by
    intro g
    conv_lhs => rw [← sum_homogeneousComponent g]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  apply le_antisymm
  · intro g hg
    rw [RingHom.mem_ker] at hg
    set N := g.totalDegree
    set h := ∑ d ∈ Finset.range (N + 1), X k ^ (N - d) * homogeneousComponent d g with hh
    have hhom : h.IsHomogeneous N := by
      apply IsHomogeneous.sum
      intro d hd
      have hdN : N - d + d = N := by
        have := Finset.mem_range.mp hd
        omega
      have := (isHomogeneous_X_pow (R := κ) k (N - d)).mul (homogeneousComponent_isHomogeneous d g)
      rwa [hdN] at this
    have hh0 : aeval τ h = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hh, map_sum, map_mul, map_pow, aeval_X, hk, one_pow, one_mul]
      rw [← hcomp]
      exact hg
    have hdiff : g - h ∈ Ideal.span {X k - 1} := by
      have hg' : g = ∑ d ∈ Finset.range (N + 1), homogeneousComponent d g :=
        (sum_homogeneousComponent g).symm
      have : g - h = ∑ d ∈ Finset.range (N + 1), (1 - X k ^ (N - d)) * homogeneousComponent d g := by
        rw [hh, sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
        conv_lhs => rw [hg']
        refine Finset.sum_congr rfl fun d _ => ?_
        ring
      rw [this]
      refine Ideal.sum_mem _ fun d _ => Ideal.mul_mem_right _ _ ?_
      rw [Ideal.mem_span_singleton]
      have := sub_dvd_pow_sub_pow (X k : MvPolynomial (Fin m) κ) 1 (N - d)
      rw [one_pow] at this
      rw [← neg_sub (X k ^ (N - d)) (1 : MvPolynomial (Fin m) κ)]
      exact dvd_neg.mpr this
    have hcone : h ∈ GlobalTheory.CompHt.coneIdeal κ τ :=
      (GlobalTheory.CompHt.mem_coneIdeal_of_isHomogeneous τ hhom).mpr hh0
    have : g = h + (g - h) := by ring
    rw [this]
    exact Submodule.add_mem_sup hcone hdiff
  · refine sup_le ?_ ?_
    · intro g hg
      rw [GlobalTheory.CompHt.mem_coneIdeal_iff] at hg
      rw [RingHom.mem_ker, hcomp]
      exact Finset.sum_eq_zero fun d _ => hg d
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show _ ∈ RingHom.ker _
      rw [RingHom.mem_ker]
      simp [hk]

theorem le_ker_constantCoeff {P : Ideal (MvPolynomial (Fin m) κ)} (h : IsProjPrime P) :
    P ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) := by
  intro f hf
  rw [RingHom.mem_ker]
  by_contra hne
  have h0 := h.isHomog f hf 0
  rw [homogeneousComponent_zero, ← constantCoeff_eq] at h0
  exact h.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit hne).map C))

end Alg

variable {Z : Scheme.{0}} {B : LB Z} {m : ℕ}

theorem evaluation_resG {U V : Z.Opens} (h : V ≤ U) (z : Z) (hz : z ∈ V) (a : Γ(Z, U)) :
    Z.evaluation V z hz (resG Z h a) = Z.evaluation U z (h hz) a := by
  simp only [resG, ← Scheme.germ_residue, CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply (Z.presheaf.map (homOfLE h).op), TopCat.Presheaf.germ_res]

theorem evaluation_algX {R : Type} [CommRing R] (p : Z ⟶ Sp R) {U : Z.Opens} (z : Z) (hz : z ∈ U) (r : R) :
    Z.evaluation U z hz (algX p U r) = Z.evaluation ⊤ z trivial (algX p ⊤ r) := by
  rw [← TopForm.resG_comp_algX p (le_top : U ≤ ⊤), RingHom.comp_apply, evaluation_resG]

variable {κ : Type} [Field κ] {p : Z ⟶ Sp κ} {s : Fin m → B.Sec}

theorem ptIdeal_eq_coneIdeal (hB : B.IsLB) {k : Fin m} (t : Fin m → Γ(Z, nonzeroLocus (s k)))
    (ht : ∀ j i, resG Z (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) ((s j).f i) =
      resG Z (inf_le_left : nonzeroLocus (s k) ⊓ B.U i ≤ nonzeroLocus (s k)) (t j) *
        resG Z (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) ((s k).f i))
    (z : Z) (hz : z ∈ nonzeroLocus (s k)) :
    letI := ((Z.evaluation ⊤ z trivial).hom.comp (algX p ⊤)).toAlgebra
    ptIdeal p s z = GlobalTheory.CompHt.coneIdeal κ (fun j => Z.evaluation _ z hz (t j)) ∧ Z.evaluation _ z hz (t k) = 1 := by
  letI alg : Algebra κ (Z.residueField z) := ((Z.evaluation ⊤ z trivial).hom.comp (algX p ⊤)).toAlgebra
  set y : Fin m → Z.residueField z := fun j => Z.evaluation _ z hz (t j) with hy
  have key : ∀ i (hi : z ∈ B.U i) j, Z.evaluation (B.U i) z hi ((s j).f i) =
      y j * Z.evaluation (B.U i) z hi ((s k).f i) := by
    intro i hi j
    have := congrArg (fun x => Z.evaluation (nonzeroLocus (s k) ⊓ B.U i) z ⟨hz, hi⟩ x) (ht j i)
    dsimp only at this
    rw [map_mul] at this
    have e1 := evaluation_resG (Z := Z) (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) z ⟨hz, hi⟩ ((s j).f i)
    have e2 := evaluation_resG (Z := Z) (inf_le_left : nonzeroLocus (s k) ⊓ B.U i ≤ nonzeroLocus (s k)) z
      ⟨hz, hi⟩ (t j)
    have e3 := evaluation_resG (Z := Z) (inf_le_right : nonzeroLocus (s k) ⊓ B.U i ≤ B.U i) z ⟨hz, hi⟩ ((s k).f i)
    simp only [hy]
    rw [← e1, ← e2, ← e3]
    exact this
  have hcone : ∀ i (hi : z ∈ B.U i), coneHom p s z i hi =
      (Polynomial.aeval (Polynomial.C (Z.evaluation (B.U i) z hi ((s k).f i)) * Polynomial.X)).toRingHom.comp
        (GlobalTheory.CompHt.coneMap κ y).toRingHom := by
    intro i hi
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneHom, GlobalTheory.CompHt.coneMap, evaluation_algX, Polynomial.algebraMap_apply,
        RingHom.algebraMap_toAlgebra]
    · intro j
      simp [coneHom, GlobalTheory.CompHt.coneMap, key i hi j]
      ring
  have hz' := hz
  simp only [nonzeroLocus, Opens.mem_iSup] at hz'
  obtain ⟨i₀, hb⟩ := hz'
  have hi₀ : z ∈ B.U i₀ := Z.basicOpen_le _ hb
  have ha : Z.evaluation (B.U i₀) z hi₀ ((s k).f i₀) ≠ 0 :=
    by
    rw [Ne, Scheme.evaluation_eq_zero_iff_notMem_basicOpen, not_not]
    exact hb
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · intro g hg
    have hg' := Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hg i₀) hi₀
    rw [RingHom.mem_ker, hcone i₀ hi₀] at hg'
    show g ∈ RingHom.ker _
    rw [RingHom.mem_ker]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply] at hg'
    rw [← Polynomial.comp_eq_aeval, Polynomial.comp_eq_zero_iff] at hg'
    rcases hg' with h | ⟨_, h⟩
    · exact h
    · exfalso
      have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 1) h
      simp at this
      exact this hb
  · intro g hg
    have hg0 : GlobalTheory.CompHt.coneMap κ y g = 0 := hg
    simp only [ptIdeal, Ideal.mem_iInf, RingHom.mem_ker]
    intro i hi
    rw [hcone i hi]
    simp [hg0]
  · have := key i₀ hi₀ k
    have h1 : (1 : Z.residueField z) * Z.evaluation (B.U i₀) z hi₀ ((s k).f i₀) =
        y k * Z.evaluation (B.U i₀) z hi₀ ((s k).f i₀) := by
      rw [one_mul]
      exact this
    exact (mul_right_cancel₀ ha h1).symm

theorem isComb_single {R : Type} [CommRing R] (p : Z ⟶ Sp R) (s : Fin m → B.Sec) (k : Fin m) :
    IsComb p s (Pi.single k 1) (s k) := by
  intro i
  simp [Pi.single_apply, apply_ite, ite_mul]

theorem linForm_single {R : Type} [CommRing R] (k : Fin m) :
    GroundTheory.Heights₂.Heights.linForm (Pi.single k (1 : R)) = X k := by
  simp [GroundTheory.Heights₂.Heights.linForm, Pi.single_apply]

variable [IsIntegral Z]

theorem dim_add_one_le (h1 : StPts) (hE : Emb p s) :
    topologicalKrullDim Z + 1 ≤ ringKrullDim (MvPolynomial (Fin m) κ ⧸ ptIdeal p s (genericPoint Z)) := by
  classical
  set I := ptIdeal p s (genericPoint Z) with hIdef
  obtain ⟨hprime, hspec, -, -⟩ := h1 κ Z p B m s hE
  let gen : IrreducibleCloseds Z → Z := fun S => S.isIrreducible.genericPoint
  have hgen : ∀ S : IrreducibleCloseds Z, closure {gen S} = (S : Set Z) := by
    intro S
    have := S.isIrreducible.isGenericPoint_genericPoint_closure
    rw [S.isClosed.closure_eq] at this
    exact this
  have hle : ∀ S T : IrreducibleCloseds Z,
      (T : Set Z) ⊆ S ↔ ptIdeal p s (gen S) ≤ ptIdeal p s (gen T) := by
    intro S T
    rw [← hspec (gen S) (gen T), specializes_iff_closure_subset, hgen, hgen]
  have hI : ∀ S : IrreducibleCloseds Z, I ≤ ptIdeal p s (gen S) := fun S =>
    (hspec _ _).mp ((genericPoint_spec Z).specializes (Set.mem_univ _))
  have hM : ∀ S : IrreducibleCloseds Z,
      ptIdeal p s (gen S) < RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) := by
    intro S
    refine lt_of_le_of_ne (le_ker_constantCoeff (hprime _)) fun h => ?_
    obtain ⟨j, hj⟩ := (hprime (gen S)).isRelevant
    apply hj
    rw [h, RingHom.mem_ker, constantCoeff_X]
  have hMI : I ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) :=
    le_ker_constantCoeff (hprime _)
  haveI : Nonempty (IrreducibleCloseds Z) :=
    ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩⟩
  let g : WithTop (IrreducibleCloseds Z)ᵒᵈ →
      PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin m) κ) (I : Set (MvPolynomial (Fin m) κ)) :=
    fun x => WithTop.recTopCoe
      ⟨⟨RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ), RingHom.ker_isPrime _⟩,
        (PrimeSpectrum.mem_zeroLocus _ _).mpr hMI⟩
      (fun S => ⟨⟨ptIdeal p s (gen (OrderDual.ofDual S)), (hprime _).isPrime⟩,
        (PrimeSpectrum.mem_zeroLocus _ _).mpr (hI _)⟩) x
  have hg : StrictMono g := by
    intro a b hab
    induction a using WithTop.recTopCoe with
    | top => exact absurd hab (not_top_lt)
    | coe S =>
      induction b using WithTop.recTopCoe with
      | top =>
        show (⟨ptIdeal p s (gen (OrderDual.ofDual S)), _⟩ : PrimeSpectrum _) <
          ⟨RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ), _⟩
        exact hM _
      | coe T =>
        rw [WithTop.coe_lt_coe] at hab
        have hab' : OrderDual.ofDual T < OrderDual.ofDual S := hab
        show (⟨ptIdeal p s (gen (OrderDual.ofDual S)), _⟩ : PrimeSpectrum _) <
          ⟨ptIdeal p s (gen (OrderDual.ofDual T)), _⟩
        refine lt_of_le_not_ge ((hle _ _).mp hab'.le) fun h => ?_
        exact hab'.not_ge ((hle _ _).mpr h)
  calc topologicalKrullDim Z + 1 = Order.krullDim (WithTop (IrreducibleCloseds Z)ᵒᵈ) := by
        rw [Order.krullDim_WithTop, Order.krullDim_orderDual]
        rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin m) κ) (I : Set _)) :=
        Order.krullDim_le_of_strictMono g hg
    _ = ringKrullDim (MvPolynomial (Fin m) κ ⧸ I) := (ringKrullDim_quotient I).symm

private theorem algX_strHom_top {κ : Type} [Field κ] {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] :
    algX (strHom κ Z) ⊤ = algebraMap κ Γ(Z, ⊤) := by
  set_option backward.isDefEq.respectTransparency false in
    ext r
    rw [algebraMap_eq_strHom]
    simp [algX, Scheme.Hom.appLE, Scheme.Hom.appTop, homOfLE_refl]

private theorem evaluation_genericPoint_eq_zero_iff {Z : Scheme.{0}} [IsIntegral Z] {U : Z.Opens}
    (hU : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    Z.evaluation U (genericPoint Z) hU a = 0 ↔ a = 0 := by
  rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
  constructor
  · intro h
    by_contra ha
    apply h
    have hne : Z.basicOpen a ≠ ⊥ := by
      rwa [Ne, basicOpen_eq_bot_iff]
    show genericPoint Z ∈ (Z.basicOpen a : Set Z)
    rw [(genericPoint_spec Z).mem_open_set_iff (Z.basicOpen a).isOpen, Set.univ_inter]
    rwa [Ne, ← Opens.not_nonempty_iff_eq_bot, not_not] at hne
  · rintro rfl
    simp

private theorem resG_bijective_of_eq_top {Z : Scheme.{0}} {V : Z.Opens} (hV : V = ⊤) :
    Function.Bijective (resG Z (le_top : V ≤ ⊤)) := by
  subst hV
  have : (homOfLE (le_top : (⊤ : Z.Opens) ≤ ⊤)) = 𝟙 _ := Subsingleton.elim _ _
  simp only [resG, this, op_id, CategoryTheory.Functor.map_id]
  exact Function.bijective_id

theorem finrank_eq_of_dim_zero [Algebra κ Γ(Z, ⊤)] {s : Fin m → B.Sec} (hE : Emb (strHom κ Z) s)
    (hd : topologicalKrullDim Z ≤ 0) {k : Fin m} (hk : genericPoint Z ∈ nonzeroLocus (s k)) :
    Module.finrank κ (MvPolynomial (Fin m) κ ⧸ (ptIdeal (strHom κ Z) s (genericPoint Z) ⊔ Ideal.span {X k - 1})) =
      Module.finrank κ Γ(Z, ⊤) := by
  classical
  set η := genericPoint Z
  have hall : ∀ z : Z, z = η := by
    intro z
    have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp hd
    let Sz : IrreducibleCloseds Z := ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
    let U : IrreducibleCloseds Z := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩
    have h1 : Sz = U := (hmax Sz).eq_of_le (show (Sz : Set Z) ⊆ U from Set.subset_univ _)
    have h2 : IsGenericPoint z Set.univ := by
      have := congrArg (fun S : IrreducibleCloseds Z => (S : Set Z)) h1
      exact this
    exact h2.eq (genericPoint_spec Z)
  have hW : nonzeroLocus (s k) = ⊤ := eq_top_iff.mpr fun z _ => (hall z) ▸ hk
  obtain ⟨-, t, hsurj, ht⟩ := hE.chart k
  obtain ⟨hJ, htk⟩ := ptIdeal_eq_coneIdeal (p := strHom κ Z) hE.isLB t ht η hk
  letI alg : Algebra κ (Z.residueField η) :=
    ((Z.evaluation ⊤ η trivial).hom.comp (algX (strHom κ Z) ⊤)).toAlgebra
  have hinj : Function.Injective (Z.evaluation (nonzeroLocus (s k)) η hk).hom :=
    (injective_iff_map_eq_zero _).mpr fun a ha => (evaluation_genericPoint_eq_zero_iff hk a).mp ha
  have hker : RingHom.ker (eval₂Hom (algX (strHom κ Z) (nonzeroLocus (s k))) t) =
      ptIdeal (strHom κ Z) s η ⊔ Ideal.span {X k - 1} := by
    rw [hJ, ← ker_aeval_eq _ k htk]
    have hcomp : (Z.evaluation (nonzeroLocus (s k)) η hk).hom.comp (eval₂Hom (algX (strHom κ Z) (nonzeroLocus (s k))) t) =
        (aeval (fun j => Z.evaluation (nonzeroLocus (s k)) η hk (t j)) :
          MvPolynomial (Fin m) κ →ₐ[κ] Z.residueField η).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [evaluation_algX, RingHom.algebraMap_toAlgebra]
      · intro j
        simp
    rw [← RingHom.ker_comp_of_injective _ hinj, hcomp]
    rfl
  let ρ : Γ(Z, ⊤) ≃+* Γ(Z, nonzeroLocus (s k)) :=
    RingEquiv.ofBijective (resG Z (le_top : nonzeroLocus (s k) ≤ ⊤)) (resG_bijective_of_eq_top hW)
  let φ : (MvPolynomial (Fin m) κ ⧸ (ptIdeal (strHom κ Z) s η ⊔ Ideal.span {X k - 1})) ≃+* Γ(Z, ⊤) :=
    (Ideal.quotEquivOfEq hker.symm).trans ((RingHom.quotientKerEquivOfSurjective hsurj).trans ρ.symm)
  have hφ : ∀ c : κ, φ (algebraMap κ _ c) = algebraMap κ Γ(Z, ⊤) c := by
    intro c
    rw [← algX_strHom_top]
    simp only [φ, RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
    simp only [ρ, RingEquiv.ofBijective_apply, MvPolynomial.algebraMap_eq, eval₂Hom_C]
    rw [← TopForm.resG_comp_algX (strHom κ Z) (le_top : nonzeroLocus (s k) ≤ ⊤), RingHom.comp_apply]
  exact (AlgEquiv.ofRingEquiv (f := φ) hφ).toLinearEquiv.finrank_eq

end ChowFormHeightComparison₂.CF.V
end
end

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier
open GroundTheory.Heights₂.Heights (IsProjPrime IsHomogIdeal IsRelevant relComps localMult chowDegree reduceMod divCycle)

namespace ChowFormHeightComparison₂.CF.V

open GroundTheory.Heights₂.Heights.ObjectsChow (ChowDegreeSection.Statement ChowDegreeClosedPoint.Statement)

theorem dim_closure_add_one_le {Z : Scheme.{0}} {z z' : Z} (h : z' ⤳ z) (hne : z ≠ z') :
    topologicalKrullDim (closure {z} : Set Z) + 1 ≤ topologicalKrullDim (closure {z'} : Set Z) :=
  topologicalKrullDim_add_one_le isClosed_closure isClosed_closure fun x hx =>
    ⟨z', subset_closure rfl, fun h' => hne (h.antisymm (specializes_iff_mem_closure.2 h')).eq.symm,
      h.trans (specializes_iff_mem_closure.2 hx)⟩

theorem dim_closure_eq {Y Z : Scheme.{0}} [IsIntegral Y] (i : Y ⟶ Z) [IsClosedImmersion i] :
    topologicalKrullDim (closure {i (genericPoint Y)} : Set Z) = topologicalKrullDim Y := by
  have h₁ := (genericPoint_spec Y).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  exact topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding h₁.def.symm

theorem length_cut {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] {B : LB Z} (hB : B.IsLB) (s : B.Sec)
    (hs : genericPoint Z ∈ nonzeroLocus s) {z : Z} (hz : (divOfSec hB s hs).mult z ≠ 0) :
    ((Module.length (Z.presheaf.stalk z) ((cut (GlobalTheory.structureModule Z) hB s).presheaf.stalk z :)).toNat : ℤ) =
      (divOfSec hB s hs).mult z := by
  obtain ⟨i, hi⟩ := LB.mem_of_cover hB z
  obtain ⟨q⟩ := CutDegree.nonempty_stalk_cut_equiv (GlobalTheory.structureModule Z) hB s i hi
  rw [mult_divOfSec (CartierDiv.coheight_eq_one_of_mult_ne_zero hz) hi, ← q.length_eq]
  refine congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (Submodule.Quotient.equiv _ _ (QCoh.structureModuleStalkEquiv z) ?_).length_eq
  rw [Submodule.map_pointwise_smul, Submodule.map_top, LinearEquiv.range, ← Submodule.ideal_span_singleton_smul,
    smul_eq_mul, Ideal.mul_top]

variable {κ : Type} [Field κ] {m : ℕ}

theorem isRelevant_of_dim {W : Ideal (MvPolynomial (Fin m) κ)}
    (hW : W ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ))
    (hd : ringKrullDim (MvPolynomial (Fin m) κ ⧸ W) ≠ 0) : IsRelevant W := by
  by_contra h
  have hX : ∀ j, X j ∈ W := fun j => by_contra fun hj => h ⟨j, hj⟩
  have key (g : MvPolynomial (Fin m) κ) : g - C (constantCoeff g) ∈ W := by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add a b ha hb =>
      have := W.add_mem ha hb
      rwa [sub_add_sub_comm, ← map_add, ← map_add] at this
    | mul_X a j _ => simpa using W.mul_mem_left a (hX j)
  have e : W = RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) := le_antisymm hW fun g hg => by
    have := key g
    rwa [(RingHom.mem_ker).1 hg, map_zero, sub_zero] at this
  have : W.IsMaximal := e ▸ RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, by simp⟩
  exact hd (ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient W).1 this))

theorem field_case (h1 : StPts) (h2 : StPull) (h3 : StDiv) (hS : ChowDegreeSection.Statement)
    (hP : ChowDegreeClosedPoint.Statement) [PerfectField κ] (e : ℕ) :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)] (B : LB Z) (s : Fin m → B.Sec),
      IsProjOver (strHom κ (X := Z)) → Emb (strHom κ Z) s →
      ringKrullDim (MvPolynomial (Fin m) κ ⧸ ptIdeal (strHom κ Z) s (genericPoint Z)) = (e + 1 : ℕ) →
      topologicalKrullDim Z = e ∧
        topSelfIntersection κ B e = chowDegree (ptIdeal (strHom κ Z) s (genericPoint Z)) (e + 1) := by
  classical
  have hC := GroundTheory.Heights₂.Heights.ConeDimComponent.proof_closed
  induction e with
  | zero =>
    intro Z _ _ B s hp hE hd
    have := isNoetherian_of_isProjOver hp
    obtain ⟨a, b, c, d⟩ := h1 κ Z _ B m s hE
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hE.cover.ge (Opens.mem_top (genericPoint Z)))
    have hX := (d _ _ (isComb_single _ s k) _).1 hk
    rw [linForm_single] at hX
    have h0 : topologicalKrullDim Z ≤ 0 := ENat.WithBot.add_le_add_one_right_iff.1
      ((dim_add_one_le h1 hE).trans (hd.trans (by simp)).le)
    have : Nonempty (IrreducibleCloseds Z) := ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩⟩
    refine ⟨le_antisymm h0 Order.krullDim_nonneg, ?_⟩
    rw [hP κ m _ k (a _) hd hX, finrank_eq_of_dim_zero hE h0 hk, topSelf_def, interNum_of_isEmpty,
      chi_eq_hdim_zero_of_suppDim_le_zero κ (QCoh.suppDim_structureModule.trans_le h0),
      ← ((coh.zeroUnitEquiv Z).restrictScalars κ).finrank_eq]
    rfl
  | succ e ih =>
    intro Z _ _ B s hp hE hd
    have := isNoetherian_of_isProjOver hp
    obtain ⟨a, b, c, d⟩ := h1 κ Z _ B m s hE
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hE.cover.ge (Opens.mem_top (genericPoint Z)))
    have hu := isComb_single (strHom κ Z) s k
    have hX := (d _ _ hu _).1 hk
    obtain ⟨d₁, d₂⟩ := h3 κ Z _ B m s hE _ _ hu hk
    have hsec := hS κ m e _ _ (a _) hd hX
    have hcomp := fun W => hC κ m (e + 1) _ W _ (a _) hd hX
    generalize (Pi.single k 1 : Fin m → κ) = u at *
    set P := ptIdeal (strHom κ Z) s with hPdef
    set J := P (genericPoint Z) ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm u} with hJ
    let T := (divOfSec hE.isLB (s k) hk).finite_support_mult.toFinset
    have hT (z : Z) : z ∈ T ↔ (divOfSec hE.isLB (s k) hk).mult z ≠ 0 := Set.Finite.mem_toFinset _
    have inj {z z' : Z} (h : P z = P z') : z = z' := (((b _ _).2 h.le).antisymm ((b _ _).2 h.ge)).eq
    have hex (W) (hW : W ∈ relComps J) : ∃ z ∈ T, P z = W := by
      obtain ⟨z, rfl⟩ := c W (hcomp W hW).1 (le_sup_left.trans hW.1.1.2)
      exact ⟨z, (hT z).2 ((d₁ z).2 hW), rfl⟩
    have key : ∀ (Y : Scheme.{0}) (i : Y ⟶ Z) [IsClosedImmersion i] [IsIntegral Y] [Algebra κ Γ(Y, ⊤)],
        (∀ r : κ, i.appTop (algebraMap κ Γ(Z, ⊤) r) = algebraMap κ Γ(Y, ⊤) r) → i (genericPoint Y) ∈ T →
        topologicalKrullDim Y = e ∧ topSelfIntersection κ (B.pull i) e = chowDegree (P (i (genericPoint Y))) (e + 1) := by
      intro Y i _ _ _ hi hz
      obtain ⟨E', pt', -⟩ := h2 κ Z Y _ B m s i hE
      have hp' := ProjSpace.isProjOver_comp_of_isClosedImmersion i hp
      rw [comp_strHom hi] at E' pt' hp'
      have := ih Y _ _ hp' E' (by rw [pt']; exact (hcomp _ ((d₁ _).1 ((hT _).1 hz))).2)
      rwa [pt'] at this
    have hTd : ∀ z ∈ T, topologicalKrullDim (closure {z} : Set Z) = e := fun z hz => by
      obtain ⟨Y, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
      letI := algebraΓAlong κ i
      exact (dim_closure_eq i).trans (key Y i (appTop_algebraMap_along κ i) hz).1
    have hmem (z : Z) (hz : z ∉ nonzeroLocus (s k)) : J ≤ P z :=
      sup_le ((b _ _).1 (genericPoint_specializes z))
        ((Ideal.span_singleton_le_iff_mem _).2 (by_contra fun h => hz ((d _ _ hu z).2 h)))
    have hSd : ∀ z ∈ ((nonzeroLocus (s k) : Set Z)ᶜ), z ∉ T → topologicalKrullDim (closure {z} : Set Z) < e := by
      intro z hz hzT
      have := (a z).isPrime
      obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le (hmem z hz)
      obtain ⟨j, hj⟩ := (a z).isRelevant
      obtain ⟨z', hz', rfl⟩ := hex W ⟨hW, j, fun h => hj (hle h)⟩
      have h4 := dim_closure_add_one_le ((b _ _).2 hle) fun h => hzT (h ▸ hz')
      rw [hTd z' hz'] at h4
      by_contra hc
      rw [not_lt] at hc
      have h5 : e + 1 ≤ e := by exact_mod_cast (add_le_add_left hc 1).trans h4
      omega
    refine ⟨le_antisymm (ENat.WithBot.add_le_add_one_right_iff.1
      ((dim_add_one_le h1 hE).trans (hd.trans (Nat.cast_succ _)).le)) ?_, ?_⟩
    · have hm : J ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) :=
        sup_le (le_ker_constantCoeff (a _)) ((Ideal.span_singleton_le_iff_mem _).2 (by
          simp [RingHom.mem_ker, GroundTheory.Heights₂.Heights.linForm]))
      have := RingHom.ker_isPrime (constantCoeff : MvPolynomial (Fin m) κ →+* κ)
      have := (a (genericPoint Z)).isPrime
      obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le hm
      have h4 := ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup κ hX hW
      obtain ⟨z, hz, rfl⟩ := hex W ⟨hW, isRelevant_of_dim hle fun h0 => by
        rw [h0, hd] at h4
        have h5 : 0 + 1 = e + 1 + 1 := by exact_mod_cast h4
        omega⟩
      have h5 := dim_closure_add_one_le (genericPoint_specializes z) fun h =>
        hX (h ▸ hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
      rw [hTd z hz] at h5
      exact (Nat.cast_succ e).le.trans (h5.trans (topologicalKrullDim_subspace_le Z _))
    · have hf := algebraMap_eq_strHom κ Z
      have := (mono_cutHom_structureModule_iff hE.isLB (s k)).2 hk
      have e₁ : (fun _ : Fin (e + 1) => B) = (Fin.cons B (fun _ => B) : Fin (e + 1) → LB Z) :=
        funext (Fin.cases rfl fun _ => rfl)
      have e₂ := (interNum_eq_sum hp (P := fun _ : Fin e => B) (fun _ => hE.isLB) _ T
        (fun z => chowDegree (P z) (e + 1)) hTd hSd (fun Y i _ _ _ hi hz => (key Y i hi hz).2)
        (cut (GlobalTheory.structureModule Z) hE.isLB (s k)) inferInstance
        (by rw [support_cut]; exact fun x hx => hx.2)).2
      rw [topSelf_def, e₁, interNum_cons_eq_interNum_cut hE.isLB (s k) (fun _ => hE.isLB)
        (finiteCohTwists_of_isProjOver hf _ hp), e₂]
      show _ = ((chowDegree _ (e + 2) : ℕ) : ℤ)
      rw [hsec, Finsupp.sum, Nat.cast_sum]
      have hval (z : Z) (hz : z ∈ T) : ((divCycle (P (genericPoint Z)) u (P z) : ℕ) : ℤ) =
          (divOfSec hE.isLB (s k) hk).mult z := by
        rw [d₂ z ((hT z).1 hz), divCycle, GroundTheory.Heights₂.Heights.fundCycle, Finsupp.onFinset_apply,
          if_pos ((d₁ z).1 ((hT z).1 hz))]
      refine Finset.sum_bij (fun z _ => P z) (fun z hz => ?_) (fun _ _ _ _ h => inj h) (fun W hW => ?_)
        fun z hz => ?_
      · rw [Finsupp.mem_support_iff, ← Nat.cast_ne_zero (R := ℤ), hval z hz]
        exact (hT z).1 hz
      · obtain ⟨z, hz, rfl⟩ := hex W (by
          by_contra h
          rw [Finsupp.mem_support_iff, divCycle, GroundTheory.Heights₂.Heights.fundCycle, Finsupp.onFinset_apply,
            if_neg h] at hW
          exact hW rfl)
        exact ⟨z, hz, rfl⟩
      · rw [length_cut hE.isLB (s k) hk ((hT z).1 hz), Nat.cast_mul, hval z hz]

end ChowFormHeightComparison₂.CF.V
