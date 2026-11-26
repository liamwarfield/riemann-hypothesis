module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDim
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyDimensionInequality

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingNoetherian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace HomLocRingNoetherian

variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}

theorem component_form_mul {s : MRing ι R} {e : K → ℕ} (hs : IsMultiHomog s e) (d : K → ℕ)
    (h : MRing ι R) :
    weightedHomogeneousComponent (blockWeight ι) (e + d) (s * h) =
      s * weightedHomogeneousComponent (blockWeight ι) d h := by
  classical
  let _ := weightedGradedAlgebra R (blockWeight ι)
  have hmem : s ∈ weightedHomogeneousSubmodule R (blockWeight ι) e :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hs
  have := DirectSum.coe_decompose_mul_add_of_left_mem
    (𝒜 := weightedHomogeneousSubmodule R (blockWeight ι)) (j := d) (b := h) hmem
  rw [← weightedDecomposition.decompose'_apply R (blockWeight ι) (s * h) (e + d),
    ← weightedDecomposition.decompose'_apply R (blockWeight ι) h d]
  exact this

variable (P : Ideal (MRing ι R)) [P.IsPrime]

abbrev img : MRing ι R →+* FractionRing (MRing ι R ⧸ P) :=
  (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P))).comp (Ideal.Quotient.mk P)

variable {P}


omit [DecidableEq K] in
theorem img_eq_zero_iff {f : MRing ι R} : img P f = 0 ↔ f ∈ P := by
  simp [img, Ideal.Quotient.eq_zero_iff_mem]

theorem img_component_congr (hP : IsMultiHomogIdeal P) {u v : MRing ι R} (huv : img P u = img P v)
    (d : K → ℕ) :
    img P (weightedHomogeneousComponent (blockWeight ι) d u) =
      img P (weightedHomogeneousComponent (blockWeight ι) d v) := by
  rw [← sub_eq_zero, ← map_sub, img_eq_zero_iff] at huv ⊢
  rw [← map_sub]
  exact hP _ huv d


omit [DecidableEq K] in
theorem img_ne_zero {W : Ideal (MRing ι R)} (hPW : P ≤ W) {t : MRing ι R} (ht : t ∉ W) :
    img P t ≠ 0 := fun h0 => ht (hPW (img_eq_zero_iff.mp h0))

theorem quot_mem {W : Ideal (MRing ι R)} {b : K → ℕ} {f g : MRing ι R} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g b) (hgW : g ∉ W) : img P f / img P g ∈ homLocRing P W :=
  Subring.subset_closure ⟨b, f, g, hf, hg, hgW, rfl⟩

end HomLocRingNoetherian


open HomLocRingNoetherian in
theorem HomLocRingNoetherian.proof (hmem : HomLocRingMem.Statement.{u}) :
    HomLocRingNoetherian.Statement.{u} := by
  intro R _ _ K _ _ ι _ P W _ hP hW _ hPW
  classical
  set S := MRing ι R
  set D := S ⧸ P
  set F := FractionRing D

  let T : Submonoid S :=
    { carrier := {s | (∃ e, IsMultiHomog s e) ∧ s ∉ W}
      one_mem' := ⟨⟨0, isWeightedHomogeneous_one R _⟩, (Ideal.ne_top_iff_one W).mp hW.ne_top⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨⟨_, ha.1.choose_spec.mul hb.1.choose_spec⟩, hW.mul_notMem ha.2 hb.2⟩ }
  let T' : Submonoid D := T.map (Ideal.Quotient.mk P)
  have hT' : T' ≤ nonZeroDivisors D := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ht.2 (hPW ?_)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  let B : Subalgebra D F := Localization.subalgebra F T' hT'
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing T' B inferInstance

  have rep : ∀ y ∈ B, ∃ (h t : S) (e : K → ℕ), IsMultiHomog t e ∧ t ∉ W ∧ y * img P t = img P h := by
    rintro y ⟨a, s, ⟨t, ⟨⟨e, hte⟩, htW⟩, rfl⟩, rfl⟩
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨h, t, e, hte, htW, IsLocalization.mk'_spec _ _ _⟩
  have hAB : ∀ x ∈ homLocRing P W, x ∈ B := by
    intro x hx
    refine (Subring.closure_le (t := B.toSubring)).mpr ?_ hx
    rintro _ ⟨b, f, g, hf, hg, hgW, rfl⟩
    exact ⟨Ideal.Quotient.mk P f, Ideal.Quotient.mk P g, ⟨g, ⟨⟨b, hg⟩, hgW⟩, rfl⟩,
      by rw [IsFractionRing.mk'_eq_div]⟩
  let j : homLocRing P W →+* B :=
    { toFun := fun a => ⟨a, hAB a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

  have key : ∀ (I : Ideal (homLocRing P W)) (z : homLocRing P W), j z ∈ I.map j → z ∈ I := by
    intro I z hz
    let Q : F → Prop := fun y => ∀ (s : S) (e : K → ℕ) (h : S), IsMultiHomog s e → s ∉ W →
      y * img P s = img P h → ∀ (d : K → ℕ) (t : S), IsMultiHomog t d → t ∉ W →
        ∃ a ∈ I, (a : F) = img P (weightedHomogeneousComponent (blockWeight ι) d h) / img P t
    have Q0 : Q 0 := by
      intro s e h _ _ hy d t _ _
      refine ⟨0, I.zero_mem, ?_⟩
      rw [zero_mul, eq_comm, img_eq_zero_iff] at hy
      rw [img_eq_zero_iff.mpr (hP h hy d), zero_div]
      rfl
    have Qadd : ∀ y₁ ∈ B, ∀ y₂ ∈ B, Q y₁ → Q y₂ → Q (y₁ + y₂) := by
      intro y₁ hy₁ y₂ hy₂ Q₁ Q₂ s e h hs hsW hy d t ht htW
      obtain ⟨h₁, t₁, e₁, ht₁, ht₁W, hb₁⟩ := rep y₁ hy₁
      obtain ⟨h₂, t₂, e₂, ht₂, ht₂W, hb₂⟩ := rep y₂ hy₂
      have hσ : IsMultiHomog (s * t₁ * t₂) (e + e₁ + e₂) := (hs.mul ht₁).mul ht₂
      have hσW : s * t₁ * t₂ ∉ W := hW.mul_notMem (hW.mul_notMem hsW ht₁W) ht₂W
      have hτ : IsMultiHomog (t₁ * t₂ * t) ((e₁ + e₂) + d) := (ht₁.mul ht₂).mul ht
      have hτW : t₁ * t₂ * t ∉ W := hW.mul_notMem (hW.mul_notMem ht₁W ht₂W) htW
      obtain ⟨a₁, ha₁I, ha₁⟩ := Q₁ _ _ (h₁ * (s * t₂)) hσ hσW
        (by simp only [map_mul]; rw [← hb₁]; ring) _ _ hτ hτW
      obtain ⟨a₂, ha₂I, ha₂⟩ := Q₂ _ _ (h₂ * (s * t₁)) hσ hσW
        (by simp only [map_mul]; rw [← hb₂]; ring) _ _ hτ hτW
      refine ⟨a₁ + a₂, I.add_mem ha₁I ha₂I, ?_⟩
      have hsum : img P (h₁ * (s * t₂) + h₂ * (s * t₁)) = img P ((t₁ * t₂) * h) := by
        simp only [map_mul, map_add (f := _)]; rw [← hb₁, ← hb₂, ← hy]; ring
      have hc := img_component_congr hP hsum ((e₁ + e₂) + d)
      rw [component_form_mul (ht₁.mul ht₂), map_add (f := _), map_add (f := _)] at hc
      have h1 := img_ne_zero hPW ht₁W
      have h2 := img_ne_zero hPW ht₂W
      have h3 := img_ne_zero hPW htW
      rw [Subring.coe_add, ha₁, ha₂, ← add_div, hc]
      simp only [map_mul]
      field_simp
    have Qgen : ∀ b ∈ B, ∀ a ∈ I, Q (b * (a : F)) := by
      intro b hb a haI s e h hs hsW hy d t ht htW
      obtain ⟨h₁, t₁, e₁, ht₁, ht₁W, hb₁⟩ := rep b hb
      obtain ⟨c, f, g, hf, hg, hgW, hfg⟩ := (hmem R K ι P W hW hPW a).mp a.2
      have hfg' : (a : F) = img P f / img P g := hfg
      have hg0 := img_ne_zero hPW hgW
      have hfa : img P f = a * img P g := by rw [hfg', div_mul_cancel₀ _ hg0]
      have hrel : img P (f * (h₁ * s)) = img P ((t₁ * g) * h) := by
        simp only [map_mul]; rw [hfa, ← hy, ← hb₁]; ring
      have hc := img_component_congr hP hrel (c + (d + e₁))
      rw [component_form_mul hf, show c + (d + e₁) = (e₁ + c) + d by abel,
        component_form_mul (ht₁.mul hg)] at hc
      have ha' := quot_mem (P := P) (W := W)
        (weightedHomogeneousComponent_isWeightedHomogeneous (d + e₁) (h₁ * s)) (ht.mul ht₁)
        (hW.mul_notMem htW ht₁W)
      refine ⟨a * ⟨_, ha'⟩, I.mul_mem_right _ haI, ?_⟩
      have h1 := img_ne_zero hPW ht₁W
      have h3 := img_ne_zero hPW htW
      rw [Subring.coe_mul, hfg']
      simp only [map_mul] at hc ⊢
      field_simp
      linear_combination hc
    have hspan : ∀ y ∈ I.map j, ∀ b : B, Q ((b : F) * (y : F)) := by
      intro y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨a, haI, rfl⟩ b
        exact Qgen b b.2 a haI
      · intro b
        simpa using Q0
      · intro y₁ y₂ _ _ Q₁ Q₂ b
        have := Qadd _ (b * y₁).2 _ (b * y₂).2 (Q₁ b) (Q₂ b)
        simpa [mul_add] using this
      · intro c y _ Qy b
        have := Qy (b * c)
        simpa [mul_assoc] using this
    obtain ⟨c, f, g, hf, hg, hgW, hfg⟩ := (hmem R K ι P W hW hPW z).mp z.2
    have hfg' : (z : F) = img P f / img P g := hfg
    have hg0 := img_ne_zero hPW hgW
    obtain ⟨a, haI, ha⟩ := hspan _ hz 1 g c f hg hgW
      (by show 1 * (z : F) * img P g = img P f; rw [one_mul, hfg', div_mul_cancel₀ _ hg0])
      c g hg hgW
    rw [hf.weightedHomogeneousComponent_same, ← hfg'] at ha
    exact (Subtype.ext ha : a = z) ▸ haI
  have hinj : Function.Injective (fun I : Ideal (homLocRing P W) => I.map j) := by
    intro I₁ I₂ h12
    have e : ∀ I : Ideal (homLocRing P W), (I.map j).comap j = I := fun I =>
      le_antisymm (fun z hz => key I z hz) Ideal.le_comap_map
    rw [← e I₁, ← e I₂]
    exact congrArg (Ideal.comap j) h12
  have hmono' : Monotone (fun I : Ideal (homLocRing P W) => I.map j) := fun _ _ h => Ideal.map_mono h
  have hmono : StrictMono (fun I : Ideal (homLocRing P W) => I.map j) :=
    hmono'.strictMono_of_injective hinj
  have : WellFoundedGT (Ideal B) := isNoetherian_iff'.mp (isNoetherianRing_iff.mp inferInstance)
  exact isNoetherianRing_iff.mpr (isNoetherian_iff'.mpr hmono.wellFoundedGT)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinTwoModels
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcIdeal joinCoord fnField)

namespace JoinTwoModels

section Field

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}

theorem ratio_mem {K' : Type} {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : fnField O (joinCoord x z) = fnField O x) (k : K') (i j : ι' k) :
    z ⟨k, i⟩ / z ⟨k, j⟩ ∈ fnField O x := by
  rw [← h]
  exact Subfield.subset_closure (Or.inr ⟨⟨.inr k, (i, j)⟩, rfl⟩)

theorem fnField_join_two {K₁ : Type} {ι₁ : K₁ → Type} {K₂ : Type} {ι₂ : K₂ → Type} (x : (Σ k, ι k) → Ω)
    (z₁ : (Σ k, ι₁ k) → Ω) (z₂ : (Σ k, ι₂ k) → Ω) (h₁ : fnField O (joinCoord x z₁) = fnField O x)
    (h₂ : fnField O (joinCoord x z₂) = fnField O x) :
    fnField O (joinCoord x (joinCoord z₁ z₂)) = fnField O x := by
  apply le_antisymm
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨kk, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    · rcases kk with k | k | k
      · exact Subfield.subset_closure (Or.inr ⟨⟨k, (i, j)⟩, rfl⟩)
      · exact ratio_mem x z₁ h₁ k i j
      · exact ratio_mem x z₂ h₂ k i j
  · refine (Subfield.closure_le).2 ?_
    rintro _ (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    · exact Subfield.subset_closure (Or.inr ⟨⟨.inl k, (i, j)⟩, rfl⟩)

end Field

section Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]

theorem exists_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω)
    {d : ℕ} (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by
  classical
  rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff] at h
  obtain ⟨j, hj⟩ := h.2.multiProj.relevant k
  refine ⟨j, fun h0 => hj ?_⟩
  rw [pointIdeal, RingHom.mem_ker]
  simp [pointConeMap, h0]

end Model

end JoinTwoModels


open JoinTwoModels in
theorem JoinTwoModels.proof (hC : ConeTrdegFnField.Statement) : JoinTwoModels.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d hx K₁ _ ι₁ _ z₁ K₂ _ ι₂ _ z₂ h₁ hf₁ h₂ hf₂
  classical
  have hf := fnField_join_two x z₁ z₂ hf₁ hf₂
  refine ⟨?_, hf⟩
  have hy : ∀ k, ∃ i, joinCoord x (joinCoord z₁ z₂) ⟨k, i⟩ ≠ 0 := by
    rintro (k | k | k)
    · exact exists_ne_zero x hx k
    · exact exists_ne_zero _ h₁ (.inr k)
    · exact exists_ne_zero _ h₂ (.inr k)
  have hx' : ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0 := exists_ne_zero x hx
  have hxW := hx
  rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff] at hxW
  obtain ⟨hK, hW⟩ := hxW
  have hinj : Function.Injective (algebraMap O Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O x).comap (C : O →+* MRing ι O) := by
      simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C,
        MvPolynomial.algebraMap_apply, ha, map_zero]
    rw [hW.noTorsion] at hmem
    exact hmem
  rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff]
  have hP := GenericProjClosureDim.isMultiProjPrime_pointIdeal (R := O) _ hy
  have hPC : (pointIdeal O (joinCoord x (joinCoord z₁ z₂))).comap
      (C : O →+* MRing (Sum.elim ι (Sum.elim ι₁ ι₂)) O) = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [← hW.noTorsion]
    simp only [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C,
      MvPolynomial.algebraMap_apply, C_eq_zero] at ha ⊢
    exact ha
  refine ⟨inferInstance, ⟨hP, hPC, ?_⟩⟩

  have hdW := DvrConeDimTrdeg.proof O K ι (pointIdeal O x) hW.multiProj hW.noTorsion
  have hdJ := DvrConeDimTrdeg.proof O (K ⊕ (K₁ ⊕ K₂)) (Sum.elim ι (Sum.elim ι₁ ι₂)) _ hP hPC
  have htW := hC O Ω hinj K ι x hx'
  have htJ := hC O Ω hinj (K ⊕ (K₁ ⊕ K₂)) (Sum.elim ι (Sum.elim ι₁ ι₂)) _ hy
  rw [hf] at htJ
  rw [BundleExamples.mcIdeal_eq_pointIdeal] at htW htJ
  set T := Algebra.trdeg O (Algebra.adjoin O (fnField O x : Set Ω))
  rw [hW.dim] at hdW
  erw [htW] at hdW
  erw [hdJ, htJ]
  rw [map_add (f := _), map_natCast] at hdW ⊢
  have hT : Cardinal.toENat T = d := by
    have h1 : ((Cardinal.toENat T + (Fintype.card K : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) =
        ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by exact_mod_cast hdW.symm
    have h2 : Cardinal.toENat T + ((Fintype.card K + 1 : ℕ) : ℕ∞) = (d : ℕ∞) + ((Fintype.card K + 1 : ℕ) : ℕ∞) := by
      have := WithBot.coe_injective h1
      push_cast at this ⊢
      rw [← add_assoc, this]; ring
    exact (WithTop.add_right_cancel (ENat.natCast_ne_top _) h2)
  rw [hT, Fintype.card_sum, Fintype.card_sum]
  have e : ((d : ℕ∞) + ((Fintype.card K + (Fintype.card K₁ + Fintype.card K₂) : ℕ) : ℕ∞) + 1) =
      ((d + 1 + (Fintype.card K + (Fintype.card K₁ + Fintype.card K₂)) : ℕ) : ℕ∞) := by
    push_cast; ring
  rw [e]
  norm_cast

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagClosureTrdeg

theorem sum_flagCoord {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
    [Algebra Ω Φ] {N k : ℕ} (hkN : k ≤ N) (w e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ) (a : Fin N → Φ) :
    ∑ j, flagCoord w e t k j * a j =
      ∑ j : Fin k, flagCoord w e t k (Fin.castLE hkN j) * a (Fin.castLE hkN j) := by
  calc ∑ j, flagCoord w e t k j * a j
      = ∑ j ∈ Finset.univ.map (Fin.castLEEmb hkN), flagCoord w e t k j * a j :=
        (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    _ = _ := Finset.sum_map _ _ _
  intro j _ hj
  have hjk : ¬ (j : ℕ) < k := fun h => hj (Finset.mem_map.2 ⟨⟨j, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  simp [flagCoord, hjk]

theorem flagCoord_indep {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
    [Algebra Ω Φ] {N k : ℕ} (hkN : k ≤ N) (w e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ)
    (ht : AlgebraicIndependent Ω t) :
    AlgebraicIndependent Ω (fun j : Fin k => flagCoord w e t k (Fin.castLE hkN j)) := by
  classical
  let _ := w.invertibleToMatrix e
  have hS := PairConeLinesIndep.linearChange_indep (w.toMatrix e) (isUnit_of_invertible _) t ht
  have h := hS.comp (Fin.castLE hkN) (Fin.castLE_injective hkN)
  convert h using 1
  funext j
  simp [flagCoord, Module.Basis.toMatrix_apply, j.isLt]

end SegreFlagClosureTrdeg


open SegreFlagClosureTrdeg in
theorem SegreFlagClosureTrdeg.proof (halg : SegreFlagConeAlg.Statement) : SegreFlagClosureTrdeg.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht
    k hk hkN
  obtain ⟨l, m', hl, hm', hal⟩ :=
    halg O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk hkN
  set z := flagClosurePt y w e φ φ' t k with hzdef

  let gV : (Σ k, ι k) → MvPolynomial (Option (Option K)) Φ :=
    fun q => C (algebraMap Ω Φ (y q)) * X (some (some q.1))
  let gZ : (Σ o, bundleIdx (bundleIdx ι M) M' o) → MvPolynomial (Option (Option K)) Φ :=
    fun p => C (z p) * X p.1
  let xs : Fin k ⊕ Unit → MvPolynomial (Option (Option K)) Φ :=
    Sum.elim (fun i : Fin k => C (z ⟨some none, l i⟩) * X (some none))
      (fun _ : Unit => C (z ⟨none, m'⟩) * X none)

  have hOΩ : Function.Injective (algebraMap O Ω) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hmem : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hmem
    simpa using hmem
  have hOL : Function.Injective (algebraMap O (MvPolynomial (Option (Option K)) Φ)) := by
    rw [IsScalarTower.algebraMap_eq O Φ (MvPolynomial (Option (Option K)) Φ), IsScalarTower.algebraMap_eq O Ω Φ,
      MvPolynomial.algebraMap_eq]
    exact (C_injective _ _).comp ((algebraMap Ω Φ).injective.comp hOΩ)

  have hZ : Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O z) =
      Algebra.trdeg O (Algebra.adjoin O (Set.range gZ)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O z)).trdeg_eq
    have e2 : (pointConeMap O z).range = Algebra.adjoin O (Set.range gZ) := aeval_range _
    rw [e2] at e1
    exact e1

  have hw : AlgebraicIndependent Ω (fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    ((algebraicIndependent_X (Option (Option K)) Φ).restrictScalars (algebraMap Ω Φ).injective).comp _
      ((Option.some_injective _).comp (Option.some_injective _))
  let j : MvPolynomial K Ω →ₐ[O] MvPolynomial (Option (Option K)) Φ :=
    (aeval fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)).restrictScalars O
  have hjc : j.comp (pointConeMap O y) = aeval gV := by
    apply MvPolynomial.algHom_ext
    intro q
    simp [j, gV, pointConeMap, MvPolynomial.algebraMap_apply]
  have hV' : Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) = Algebra.trdeg O (Algebra.adjoin O (Set.range gV)) := by
    have e1 := (Ideal.quotientKerEquivRange (pointConeMap O y)).trdeg_eq
    have e2 := ((pointConeMap O y).range.equivMapOfInjective j hw).trdeg_eq
    rw [← AlgHom.range_comp, hjc, aeval_range] at e2
    exact e1.trans e2

  have hVZ : Set.range gV ⊆ Set.range gZ := by
    rintro _ ⟨q, rfl⟩
    exact ⟨⟨some (some q.1), q.2⟩, rfl⟩
  have hxZ : Set.range xs ⊆ Set.range gZ := by
    rintro _ ⟨i | _, rfl⟩
    · exact ⟨⟨some none, l i⟩, rfl⟩
    · exact ⟨⟨none, m'⟩, rfl⟩

  let b := Pi.basisFun Ω (Fin k)
  let ψ : Fin k → Module.Dual Ω (Fin k → Ω) :=
    fun i => b.dualBasis.equivFun.symm (fun j => φ (l i) (w (Fin.castLE hkN j)))
  have hψb : ∀ i j, ψ i (b j) = φ (l i) (w (Fin.castLE hkN j)) := by
    intro i j
    rw [← Module.Basis.dualBasis_equivFun]
    simp [ψ, Finsupp.single_apply]
  have hψ : LinearIndependent Ω ψ := hl.map' b.dualBasis.equivFun.symm.toLinearMap b.dualBasis.equivFun.symm.ker
  have hind' := PairConeLinesIndep.proof Ω Φ K k (Fin k → Ω) b ψ hψ
    (fun j => flagCoord w e t k (Fin.castLE hkN j)) (flagCoord_indep hkN w e t ht) _ hm'
  have hxs : xs = Sum.elim
      (fun i : Fin k => C (∑ j, flagCoord w e t k (Fin.castLE hkN j) * algebraMap Ω Φ (ψ i (b j))) * X (some none))
      (fun _ : Unit => (C (z ⟨none, m'⟩) * X none : MvPolynomial (Option (Option K)) Φ)) := by
    funext i
    rcases i with i | _
    · simp only [xs, Sum.elim_inl, hψb]
      congr 2
      exact sum_flagCoord hkN w e t _
    · rfl
  rw [← hxs] at hind'
  have hle : ∀ a ∈ Algebra.adjoin O (Set.range gV),
      a ∈ Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
    intro a ha
    refine Algebra.adjoin_le (S := (Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))).restrictScalars O) ?_ ha
    rintro _ ⟨q, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
    have hc : (C (algebraMap Ω Φ (y q)) : MvPolynomial (Option (Option K)) Φ) ∈
        Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) := by
      rw [← MvPolynomial.algebraMap_apply]
      exact Subalgebra.algebraMap_mem _ _
    exact Subalgebra.mul_mem _ hc (Algebra.subset_adjoin ⟨q.1, rfl⟩)
  let fr : Algebra.adjoin O (Set.range gV) →+*
      Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)) :=
    { toFun := fun a => ⟨a, hle a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) :=
    fr.toAlgebra
  have : IsScalarTower (Algebra.adjoin O (Set.range gV))
      (Algebra.adjoin Ω (Set.range fun k : K => (X (some (some k)) : MvPolynomial (Option (Option K)) Φ)))
      (MvPolynomial (Option (Option K)) Φ) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxind : AlgebraicIndependent (Algebra.adjoin O (Set.range gV)) xs :=
    hind'.restrictScalars (K := Algebra.adjoin Ω (Set.range fun k : K =>
      (X (some (some k)) : MvPolynomial (Option (Option K)) Φ))) fun a b h => Subtype.ext (congrArg Subtype.val h :)

  have key := AdjoinTrdegAdd.proof O (MvPolynomial (Option (Option K)) Φ) hOL (Set.range gV) (Set.range gZ)
    (Fin k ⊕ Unit) xs hxZ hxind (by rintro _ ⟨p, rfl⟩; exact hal p)
  rw [Set.union_eq_right.mpr hVZ] at key
  rw [hZ, hV', key, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinPointModel
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord joinCoord mcMap)

namespace JoinPointModel

section Split

variable {K : Type} {ι : K → Type}

def varEquiv : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≃ Option (Σ k, ι k) where
  toFun
    | ⟨.inl k, i⟩ => some ⟨k, i⟩
    | ⟨.inr _, _⟩ => none
  invFun
    | some p => ⟨.inl p.1, p.2⟩
    | none => ⟨.inr (), (0 : Fin 1)⟩
  left_inv := by
    rintro ⟨k | u, i⟩
    · rfl
    · cases u
      change Fin 1 at i
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      rfl
  right_inv := by
    rintro (_ | ⟨k, i⟩) <;> rfl

variable (K) (Ω : Type*) [CommRing Ω]

def tgtEquiv : MvPolynomial (K ⊕ Unit) Ω ≃ₐ[Ω] Polynomial (MvPolynomial K Ω) :=
  (renameEquiv Ω (Equiv.optionEquivSumPUnit.{0, 0} K).symm).trans (optionEquivLeft Ω K)

variable {K} (O : Type*) [CommRing O]

def srcEquiv : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O ≃ₐ[O]
    Polynomial (MvPolynomial (Σ k, ι k) O) :=
  (renameEquiv O varEquiv).trans (optionEquivLeft O _)

end Split

section Cone

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem tgtEquiv_mcMap (y : (Σ k, ι k) → Ω) (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    tgtEquiv K Ω (mcMap O (joinCoord y (ptCoord (Ω := Ω))) p) =
      Polynomial.map (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω) (srcEquiv O p) := by
  have h : ((tgtEquiv K Ω : MvPolynomial (K ⊕ Unit) Ω →+* Polynomial (MvPolynomial K Ω)).comp
      (mcMap O (joinCoord y (ptCoord (Ω := Ω))) : _ →+* MvPolynomial (K ⊕ Unit) Ω)) =
      (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω)).comp
        (srcEquiv (K := K) (ι := ι) O).toRingEquiv.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tgtEquiv, srcEquiv, mcMap, optionEquivLeft_C]
    · rintro ⟨k | u, i⟩
      · simp [tgtEquiv, srcEquiv, varEquiv, mcMap, joinCoord, optionEquivLeft_X_some, optionEquivLeft_C]
      · simp [tgtEquiv, srcEquiv, varEquiv, mcMap, joinCoord, ptCoord, optionEquivLeft_X_none]
  exact RingHom.congr_fun h p

theorem mem_pointIdeal_join_iff (y : (Σ k, ι k) → Ω)
    (p : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O) :
    p ∈ pointIdeal O (joinCoord y (ptCoord (Ω := Ω))) ↔
      srcEquiv O p ∈ RingHom.ker
        (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω)) := by
  rw [← BundleExamples.mcIdeal_eq_pointIdeal, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal, RingHom.mem_ker, RingHom.mem_ker,
    Polynomial.coe_mapRingHom, ← tgtEquiv_mcMap, map_eq_zero_iff _ (tgtEquiv K Ω).injective]

theorem ringKrullDim_join [IsNoetherianRing O] (y : (Σ k, ι k) → Ω) :
    ringKrullDim (MRing (Sum.elim ι ptIdx) O ⧸ pointIdeal O (joinCoord y (ptCoord (Ω := Ω)))) =
      ringKrullDim (MRing ι O ⧸ pointIdeal O y) + 1 := by
  let J := RingHom.ker (Polynomial.mapRingHom (mcMap O y : MvPolynomial (Σ k, ι k) O →+* MvPolynomial K Ω))
  let Φ : MvPolynomial (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) O →+* Polynomial (MvPolynomial (Σ k, ι k) O) ⧸ J :=
    (Ideal.Quotient.mk J).comp (srcEquiv (K := K) (ι := ι) O).toRingEquiv.toRingHom
  have hΦ : Function.Surjective Φ := Ideal.Quotient.mk_surjective.comp (srcEquiv O).surjective
  have hker : pointIdeal O (joinCoord y (ptCoord (Ω := Ω))) = RingHom.ker Φ := by
    ext p
    rw [mem_pointIdeal_join_iff, RingHom.mem_ker (f := Φ)]
    change _ ↔ Ideal.Quotient.mk J (srcEquiv O p) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
  have hJ : J = (pointIdeal O y).map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) := by
    simp only [J]
    rw [Polynomial.ker_mapRingHom]
    rfl
  have hq : ringKrullDim (MRing (Sum.elim ι ptIdx) O ⧸ RingHom.ker Φ) =
      ringKrullDim (Polynomial (MvPolynomial (Σ k, ι k) O) ⧸ J) :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hΦ)
  have hp : ringKrullDim (Polynomial (MRing ι O ⧸ pointIdeal O y)) =
      ringKrullDim (Polynomial (MRing ι O) ⧸ (pointIdeal O y).map (Polynomial.C : MRing ι O →+* _)) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.polynomialQuotientEquivQuotientPolynomial (pointIdeal O y))
  rw [hker, hq, hJ, ← hp, Polynomial.ringKrullDim_of_isNoetherianRing]

end Cone

end JoinPointModel


open JoinPointModel in
theorem JoinPointModel.proof : JoinPointModel.Statement := by
  intro O _ _ _ Ω _ _ K _ _ ι _ y d hW
  rw [BundleExamples.isModelOver_iff]
  refine ⟨inferInstance, ⟨?_, ?_, ?_⟩⟩
  · apply GenericProjClosureDim.isMultiProjPrime_pointIdeal
    rintro (k | u)
    · obtain ⟨j, hj⟩ := hW.multiProj.relevant k
      refine ⟨j, fun h0 => hj ?_⟩
      change y ⟨k, j⟩ = 0 at h0
      rw [pointIdeal, RingHom.mem_ker]
      simp [pointConeMap, h0]
    · exact ⟨(0 : Fin 1), by simp [joinCoord, ptCoord]⟩
  · rw [eq_bot_iff]
    intro a ha
    rw [← hW.noTorsion]
    simp only [Ideal.mem_comap, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal, pointIdeal, RingHom.mem_ker,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, C_eq_zero] at ha ⊢
    exact ha
  · rw [BundleExamples.mcIdeal_eq_pointIdeal, ringKrullDim_join, hW.dim, Fintype.card_sum, Fintype.card_unit,
      show d + 1 + (Fintype.card K + 1) = (d + 1 + Fintype.card K) + 1 by omega]
    norm_cast

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutContraction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagCutContraction

theorem pullDeg_comp_of_eq_zero {K K' : Type*} (j : K ↪ K') (b : K' → ℤ)
    (hb : ∀ o, o ∉ Set.range j → b o = 0) : FieldNumbers.pullDeg j (b ∘ j) = b := by
  funext o
  by_cases ho : ∃ a, j a = o
  · obtain ⟨a, rfl⟩ := ho
    exact j.injective.extend_apply (b ∘ j) 0 a
  · rw [FieldNumbers.pullDeg, Function.extend_apply' _ _ _ ho, Pi.zero_apply]
    exact (hb o (by simpa [Set.mem_range] using ho)).symm

theorem withBot_le_of_lt_succ (a : WithBot ℕ∞) (m : ℕ) (h : a < ((m + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ ((m : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) < (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      exact absurd (WithBot.coe_lt_coe.mp h') (by simp)
    | coe c =>
      have h' : (((c : ℕ) : ℕ∞) : WithBot ℕ∞) < (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := h
      have hc : c < m + 1 := by exact_mod_cast WithBot.coe_lt_coe.mp h'
      show (((c : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((m : ℕ) : ℕ∞) : WithBot ℕ∞)
      exact WithBot.coe_le_coe.mpr (by exact_mod_cast (by omega : c ≤ m))

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type} [∀ o, Fintype (ι' o)]


omit [IsDomain O] [IsDiscreteValuationRing O] [∀ o, Fintype (ι' o)] in
theorem ratDiv_support {P W : Ideal (MRing ι' O)} (hPm : IsMultiHomogIdeal P) {cs ch : K' → ℕ}
    {s h : MRing ι' O} (hs : IsMultiHomog s cs) (hh : IsMultiHomog h ch) (hW : ratDiv P s h W ≠ 0) :
    W.IsPrime ∧ P ≤ W ∧ IsMultiHomogIdeal W := by
  have key : ∀ {c : K' → ℕ} {u : MRing ι' O}, IsMultiHomog u c → divCycle P u W ≠ 0 →
      W.IsPrime ∧ P ≤ W ∧ IsMultiHomogIdeal W := by
    intro c u hu hne
    unfold divCycle at hne
    split_ifs at hne with hW'
    · exact ⟨hW'.1.1.1, le_sup_left.trans hW'.1.1.2,
        MinimalPrimeMultiHomog.full O K' ι' _ W (SupSpanMultiHomog.full O K' ι' P u c hPm hu) hW'.1⟩
    · exact absurd rfl hne
  by_cases h1 : divCycle P s W = 0
  · exact key hh fun h2 => hW (by simp [ratDiv, h1, h2])
  · exact key hs h1

theorem vNumL_eq_zero_of_contract {ϖ : O} (hϖ : Irreducible ϖ) {P W : Ideal (MRing ι' O)} {n : ℕ}
    (hP : IsModelOver P n) [hWp : W.IsPrime] (hPW : P ≤ W) (hWm : IsMultiHomogIdeal W)
    (hϖW : (C ϖ : MRing ι' O) ∈ W) {K : Type} [Fintype K] [DecidableEq K] (j : K ↪ K')
    (hcon : FieldNumbers.relDim (FieldNumbers.contractPrime j (specialIdeal W)) < ((n : ℕ) : WithBot (WithTop ℤ)))
    (l : List (K' → ℤ)) (hl : l.length = n) (hlj : ∀ b ∈ l, ∀ o, o ∉ Set.range j → b o = 0) :
    vNumL W l = 0 := by
  subst hl
  have : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι' O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι' O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  have hlt : P < W := lt_of_le_of_ne hPW (fun h => hϖP (h ▸ hϖW))
  have hdrop := DimStrictDrop.full (MRing ι' O) P W hlt
  rw [hP.dim] at hdrop
  obtain ⟨hQp, -, -, -⟩ := SpecialIdealCorresp.full O ϖ hϖ K' ι' P W hWp hϖW
  have hQm := SpecialIdealMultiHomog.full O K' ι' W hWm
  have hdimQ : ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + Fintype.card K' + 1 : ℕ) : WithBot ℕ∞) := by
    rw [SpecialQuotDim.full O ϖ hϖ K' ι' W hϖW]
    refine lt_natCast_of_add_one_le ?_
    have e : l.length + Fintype.card K' + 1 = l.length + 1 + Fintype.card K' := by omega
    rw [e]
    exact hdrop
  change intNum (IsLocalRing.ResidueField O) (specialIdeal W) l.get = 0
  by_cases hcase : ¬ IsRelevant (specialIdeal W) ∨ ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) <
      ((l.length + Fintype.card K' : ℕ) : WithBot ℕ∞)
  · exact IntNumVanish.full (IsLocalRing.ResidueField O) K' ι' l.length (specialIdeal W) hQp hQm hcase l.get
  · push Not at hcase
    obtain ⟨hrel, hge⟩ := hcase
    have hdimEq : ringKrullDim (MRing ι' (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
        ((l.length + Fintype.card K' : ℕ) : WithBot ℕ∞) :=
      le_antisymm (withBot_le_of_lt_succ _ _ hdimQ) hge
    have hrelQ : FieldNumbers.relDim (specialIdeal W) = ((l.length : ℕ) : WithBot (WithTop ℤ)) := by
      rw [FieldNumbers.relDim, hdimEq]
      have : (((l.length + Fintype.card K' : ℕ) : ℤ) - Fintype.card K') = l.length := by push_cast; ring
      exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this
    have hz := FieldNumbers.ProjectionFormulaContracted.full (IsLocalRing.ResidueField O) K K' j ι' (specialIdeal W)
      ⟨hQp, hQm, hrel⟩ l.length hrelQ hcon (fun i => l.get i ∘ j)
    rw [← hz]
    congr 1
    funext i
    exact (pullDeg_comp_of_eq_zero j _ (hlj _ (List.get_mem l i))).symm

end SegreFlagCutContraction


open SegreFlagCutContraction in
theorem SegreFlagCutContraction.proof (hModel : SegreFlagClosureModel.Statement)
    (hProj : SegreFlagCutProjection.Statement) : SegreFlagCutContraction.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk
  have hH : IsModelOver (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) (d + k) := by
    have h := (hModel O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
      Φ e t ht (k + 1) (by omega) (by omega)).1
    simpa using h
  obtain ⟨hp1, hp2⟩ := hProj O ϖ hϖ Ω K ι y d hV N E B B' hsame w w' x x' f g hflag M M' a₀ a₀' φ φ' hφ hφ'
    Φ e t ht k hk
  refine ⟨fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW l hl hl0 => ?_,
    fun cs ch s h hs hh hdeg hsP hhP hval W hϖW hW l hl hl0 => ?_⟩
  · obtain ⟨hWp, hPW, hWm⟩ := ratDiv_support hH.multiProj.multiHomog hs hh hW
    refine vNumL_eq_zero_of_contract hϖ hH hPW hWm hϖW Function.Embedding.some
      (hp1 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW) l hl fun b hb o ho => ?_
    cases o with
    | none => exact hl0 b hb
    | some o => exact absurd ⟨o, rfl⟩ ho
  · obtain ⟨hWp, hPW, hWm⟩ := ratDiv_support hH.multiProj.multiHomog hs hh hW
    refine vNumL_eq_zero_of_contract hϖ hH hPW hWm hϖW secondFactorBlocks
      (hp2 cs ch s h hs hh hdeg hsP hhP hval W hϖW hW) l hl fun b hb o ho => ?_
    rcases o with _ | _ | o
    · exact absurd ⟨none, rfl⟩ ho
    · exact hl0 b hb
    · exact absurd ⟨some o, rfl⟩ ho

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpFibreSemilocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem length_quot_span_ringEquiv {R R' : Type*} [CommRing R] [CommRing R'] (ψ : R ≃+* R') (r : R) :
    Module.length R (R ⧸ Ideal.span {r}) = Module.length R' (R' ⧸ Ideal.span {ψ r}) := by
  let _ : Algebra R R' := ψ.toRingHom.toAlgebra
  let e : (R ⧸ Ideal.span {r}) ≃ₐ[R] R' ⧸ Ideal.span {ψ r} :=
    Ideal.quotientEquivAlg _ _ (AlgEquiv.ofRingEquiv (f := ψ) fun _ => rfl)
      (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  rw [e.toLinearEquiv.length_eq, Module.length_eq_of_surjective ψ.surjective]


set_option maxHeartbeats 2000000 in
theorem BlowUpFibreSemilocal.proof (ha : HomLocRingLocal.Statement.{u})
    (hb : DivCycleHomLoc.Statement.{u}) (hiso : BlowUpLocRingIso.Statement.{u})
    (hfin : BlowUpOverLocFinite.Statement.{u}) (hmax : BlowUpOverLocMax.Statement.{u}) :
    BlowUpFibreSemilocal.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel g hg hgW hz
  have := hP.multiProj.isPrime
  obtain ⟨hfinite, hrank⟩ := hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  obtain ⟨e, he⟩ := hmax O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have hbl : IsModelOver (blowUpOf P u) n := BlowUpModel.full O K ι J P n hP N u hu hu'
  refine ⟨blowUpOverLoc P W u, inferInstance, inferInstance, inferInstance, hfinite,
    Subring.inclusion_injective _, hrank, e, fun 𝔫 => ⟨?_, (he 𝔫).2⟩⟩
  obtain ⟨h, hloc⟩ := (he 𝔫).1
  generalize e 𝔫 = Q at h hloc ⊢
  obtain ⟨Q, hQmin, hQrel, hQW⟩ := Q
  dsimp only at h hloc ⊢
  have hblQ : blowUpOf P u ≤ Q := le_trans le_sup_left hQmin.1.2
  have hxl : IsMultiHomog (liftForm (J := J) x) (liftMDeg c) := isMultiHomog_liftForm hx
  have hgl : IsMultiHomog (liftForm (J := J) g) (liftMDeg c) := isMultiHomog_liftForm hg
  have hgQ : liftForm (J := J) g ∉ Q := fun hm => hgW (by rw [← hQW]; exact hm)
  have hxbl : liftForm (J := J) x ∉ blowUpOf P u := liftForm_not_mem_blowUpOf hxP
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  have hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
        (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm x)) /
      algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
        (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g)) ∈
      homLocRing (blowUpOf P u) Q :=
    Subring.subset_closure ⟨liftMDeg c, _, _, hxl, hgl, hgQ, rfl⟩
  obtain ⟨φ, hφ⟩ := hiso O K ι J P u Q hblQ

  have hlen : Module.length (homLocRing (blowUpOf P u) Q)
      (homLocRing (blowUpOf P u) Q ⧸ Ideal.span {(⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q)}) =
        ((divCycle (blowUpOf P u) (liftForm x) Q).toNat : ℕ∞) := by
    have hinj := IsFractionRing.injective (MRing (extIdx ι J) O ⧸ blowUpOf P u)
      (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u))
    have hne : ∀ y : MRing (extIdx ι J) O, y ∉ blowUpOf P u →
        algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
          (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ y) ≠ 0 := by
      intro y hy
      rw [Ne, map_eq_zero_iff _ hinj, Ideal.Quotient.eq_zero_iff_mem]
      exact hy
    have hz0 : (⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q) ≠ 0 := fun h0 =>
      div_ne_zero (hne _ hxbl) (hne _ fun hm => hgQ (hblQ hm)) (congrArg Subtype.val h0)
    have hQp : Q.IsPrime := hQmin.1.1
    have hmult := hb O (Option K) (extIdx ι J) (blowUpOf P u) hbl.multiProj (liftMDeg c) (liftForm x) hxl
      hxbl Q hQmin hQrel (liftForm g) hgl hgQ hz'
    have hloc' := ha O (Option K) (extIdx ι J) (blowUpOf P u) hbl.multiProj (liftMDeg c)
      (liftForm x) hxl hxbl Q hQmin hQrel
    have hn : IsNoetherianRing (homLocRing (blowUpOf P u) Q) := hloc'.2.1
    have hd : ringKrullDim (homLocRing (blowUpOf P u) Q) = 1 := hloc'.2.2
    have hdivQ : divCycle (blowUpOf P u) (liftForm x) Q =
        ((multAt (blowUpOf P u ⊔ Ideal.span {liftForm x}) Q).toNat : ℤ) := by
      unfold divCycle
      rw [dite_eq_left ⟨hQmin, hQrel⟩]
    have : Ring.KrullDimLE 1 (homLocRing (blowUpOf P u) Q) := by
      rw [Ring.krullDimLE_iff, hd]
      rfl
    have hfinl : Module.length (homLocRing (blowUpOf P u) Q)
        (homLocRing (blowUpOf P u) Q ⧸ Ideal.span {(⟨_, hz'⟩ : homLocRing (blowUpOf P u) Q)}) ≠ ⊤ :=
      Module.length_ne_top_iff.mpr
        (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero hz0))
    rw [hdivQ, Int.toNat_natCast, hmult, ENat.natCast_toNat hfinl]

  let _ := (Subring.inclusion h).toAlgebra
  have := 𝔫.2.isPrime
  have := hloc
  let ψ₁ : Localization.AtPrime 𝔫.1 ≃ₐ[blowUpOverLoc P W u] blowUpLocRing P u Q :=
    IsLocalization.algEquiv 𝔫.1.primeCompl _ _
  let ψ : Localization.AtPrime 𝔫.1 ≃+* homLocRing (blowUpOf P u) Q := ψ₁.toRingEquiv.trans φ.symm
  have hψ : ψ (algebraMap (blowUpOverLoc P W u) (Localization.AtPrime 𝔫.1)
      (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩)) = ⟨_, hz'⟩ := by
    apply φ.injective
    simp only [ψ, RingEquiv.trans_apply, RingEquiv.apply_symm_apply, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes]
    apply Subtype.ext
    rw [hφ (liftMDeg c) _ _ hxl hgl hgQ, blowUpEval_liftForm, blowUpEval_liftForm]
    rfl
  rw [length_quot_span_ringEquiv ψ, hψ]
  exact hlen

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
