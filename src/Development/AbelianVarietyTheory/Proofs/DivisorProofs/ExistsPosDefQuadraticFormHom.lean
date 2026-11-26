module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.NefEffectiveCones.EventuallyEvalNegOfCoeffNeg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmplePullbackIntersectionDegreePosOfNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveDivisorPosDegreeAmpleClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveDivisorPosDegreeAmpleClass
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.EffPos

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Cartier

theorem exists_coheight_eq_one_notMem {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {M : LB X}
    (hM : M.IsLB) (s : M.Sec) (hs : genericPoint X ∈ nonzeroLocus s) {x : X} (hx : x ∉ nonzeroLocus s) :
    ∃ w : X, Order.coheight w = 1 ∧ w ∉ nonzeroLocus s := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ M.U i := by
    have : x ∈ (⨆ i, M.U i : X.Opens) := by rw [hM.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  set g := X.presheaf.germ _ x hi (s.f i) with hgdef
  have hg0 : g ≠ 0 := GlobalTheory.MixHt.CycLoc.germ_ne_zero hs hi
  have hgu : ¬ IsUnit g := fun h =>
    hx ((Cartier.mem_nonzeroLocus_iff s i hi).2 ((Scheme.mem_basicOpen _ _ _ _).2 h))
  have hle : Ideal.span {g} ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (Ideal.span_singleton_le_iff_mem _).2 ((IsLocalRing.mem_maximalIdeal _).2 hgu)
  obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le hle
  have hPp : P.IsPrime := hP.1.1
  have h1 : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
  have hgP : g ∈ P := hP.1.2 (Ideal.subset_span rfl)
  have hP0 : (⊥ : Ideal (X.presheaf.stalk x)) < P := bot_lt_iff_ne_bot.2 fun h =>
    hg0 (by rw [h] at hgP; simpa using hgP)
  have e0 := Ideal.height_add_one_le_of_lt_of_isPrime hP0
  rw [Ideal.height_bot, zero_add] at e0
  refine ⟨X.fromSpecStalk x ⟨P, hPp⟩, ?_, ?_⟩
  · rw [GlobalTheory.MixHt.CycLoc.coheight_fromSpecStalk]
    exact le_antisymm h1 e0
  · rw [GlobalTheory.MixHt.CycLoc.mem_nonzeroLocus_iff_notMem s hi, not_not]
    exact hgP

end GlobalTheory.AV.EffPos

namespace GlobalTheory.AV.EffPos

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.Cartier

theorem interNumRed_pos {K : Type} [Field K] (A : AbVar K) (n : ℕ) (hdim : A.dim = n + 1)
    (L : LB A.X.left) (hL : L.IsLB) (hLa : IsAmpleLB L) {w : A.X.left} (hw : Order.coheight w = 1) :
    letI := A.algΓ
    0 < interNumRed K (⟨closure {w}, isClosed_closure⟩ : Closeds A.X.left) (fun _ : Fin n => L) := by
  letI := A.algΓ
  obtain ⟨hint, hnoeth, -⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  obtain ⟨hstr, hproj⟩ := AbVarProj.strHom_eq_and_isProjOver K A
  have hp : IsProjOver (strHom K (X := A.X.left)) := hstr ▸ hproj
  have hX : topologicalKrullDim A.X.left = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_dim, hdim]
  have : LocallyOfFiniteType (strHom K (X := A.X.left)) := by
    obtain ⟨N, j, _, h⟩ := hp
    exact h ▸ inferInstance
  set C : Closeds A.X.left := ⟨closure {w}, isClosed_closure⟩ with hC
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  letI := algebraΓAlong K (redι C)
  rw [interNumRed_def, interNumSub_def,
    interNumOn_eq_interNum_pull (k := K) (f := redι C) (fun _ => rfl) (fun _ => hL)]
  have hd : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal C).subscheme = (n : WithBot ℕ∞) := by
    rw [topologicalKrullDim_red]
    exact VdmRec.CutSec.dim_closure_of_coheight_field (strHom K A.X.left) hX hw
  exact CompanionTheory.NefKleiman.interNum_top_pos_of_isAmpleLB K _ (PullVanish.isProjOver_red hp C) n hd _
    (hLa.pull_of_isClosedImmersion (redι C))

theorem inter_cons_pos : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left), IsAmpleCls c → ∀ (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), Out.nonzeroLocus s ≠ ⊥ → Out.nonzeroLocus s ≠ ⊤ → 0 < inter A (Fin.cons (cls M hM) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  intro K _ A n hdim c hc M hM s hbot htop
  obtain ⟨L, hL, hrel, rfl⟩ := hc
  have hLa : IsAmpleLB L := (AmpleClsIff.isAmpleCls_cls_iff K A L hL).1 ⟨L, hL, hrel, rfl⟩
  letI := A.algΓ
  obtain ⟨hint, hnoeth, hcpt⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  obtain ⟨hstr, hproj⟩ := AbVarProj.strHom_eq_and_isProjOver K A
  have hp : IsProjOver (strHom K (X := A.X.left)) := hstr ▸ hproj
  have hX : topologicalKrullDim A.X.left = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_dim, hdim]
  have hcons : ∀ j, ((Fin.cons M (fun _ : Fin n => L) : Fin (n + 1) → LB A.X.left) j).IsLB :=
    fun j => Fin.cases hM (fun _ => hL) j
  have hfam : (Fin.cons (cls M hM) (fun _ : Fin n => cls L hL) : Fin (n + 1) → Pic A.X.left) =
      fun j => cls ((Fin.cons M (fun _ : Fin n => L) : Fin (n + 1) → LB A.X.left) j) (hcons j) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp
  rw [hfam, T.abelianVariety_intersection_eq_lineBundleIntersection K A (Fin (n + 1)) _ hcons]
  have hs : genericPoint A.X.left ∈ nonzeroLocus s := by
    obtain ⟨y, hy⟩ : (nonzeroLocus s : Set A.X.left).Nonempty := by
      by_contra h
      exact hbot (TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.1 h))
    exact ((genericPoint_spec A.X.left).mem_open_set_iff (nonzeroLocus s).isOpen).2 ⟨y, trivial, hy⟩
  rw [SecCycle.interNum_cons_eq_finsum_mult K A.X.left hp n hX.le M hM (fun _ => L) (fun _ => hL) s hs]
  obtain ⟨x, hx⟩ : ∃ x, x ∉ nonzeroLocus s := by
    by_contra h
    push_neg at h
    exact htop (eq_top_iff.2 fun x _ => h x)
  obtain ⟨w, hw1, hws⟩ := exists_coheight_eq_one_notMem hM s hs hx
  have hfs := (divOfSec hM s hs).finite_support_mult
  have hterm : ∀ v, 0 ≤ (divOfSec hM s hs).mult v *
      interNumRed K (⟨closure {v}, isClosed_closure⟩ : Closeds A.X.left) (fun _ : Fin n => L) := by
    intro v
    by_cases hv : (divOfSec hM s hs).mult v = 0
    · rw [hv, zero_mul]
    · exact mul_nonneg (mult_divOfSec_nonneg v)
        (interNumRed_pos A n hdim L hL hLa (CartierDiv.coheight_eq_one_of_mult_ne_zero hv)).le
  have hmw : (divOfSec hM s hs).mult w ≠ 0 := SecCycle.mult_divOfSec_ne_zero hM s hs hw1 hws
  have hw0 : 0 < (divOfSec hM s hs).mult w *
      interNumRed K (⟨closure {w}, isClosed_closure⟩ : Closeds A.X.left) (fun _ : Fin n => L) :=
    mul_pos (lt_of_le_of_ne (mult_divOfSec_nonneg w) (Ne.symm hmw)) (interNumRed_pos A n hdim L hL hLa hw1)
  rw [finsum_eq_sum_of_support_subset _ (s := hfs.toFinset) ?_]
  · exact Finset.sum_pos' (fun v _ => hterm v) ⟨w, by simpa using hmw, hw0⟩
  · intro v hv
    simpa using Function.support_mul_subset_left _ _ hv

end GlobalTheory.AV.EffPos
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveDivisorPosDegreeAmpleClassStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effectiveDivisor_pos_degree_ampleClass : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left), IsAmpleCls c → ∀ (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), Out.nonzeroLocus s ≠ ⊥ → Out.nonzeroLocus s ≠ ⊤ → 0 < inter A (Fin.cons (cls M hM) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  first | exact @GlobalTheory.AV.EffPos.inter_cons_pos | exact GlobalTheory.AV.EffPos.inter_cons_pos | (intros; apply GlobalTheory.AV.EffPos.inter_cons_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackAmpleVanishingOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyNeOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyNeOrigin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem eq_comp_section_of_apply_eq {K L : Type} [Field K] [Field L] {X : Scheme.{0}} (t : X ⟶ Sp K)
    (e : Sp K ⟶ X) (he : e ≫ t = 𝟙 _) (q : Sp L ⟶ Sp K) (y : Sp L ⟶ X) (hy : y ≫ t = q)
    (p : Sp L) (p' : Sp K) (h : y p = e p') : y = q ≫ e := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective y
  obtain ⟨⟨z', α⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective e
  simp only [Scheme.SpecToEquivOfField_symm_apply] at he hy h ⊢
  have hz : z = z' := by simpa using h
  subst hz
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField z ≫ t)
  rw [Category.assoc, ← hc, ← Spec.map_comp, ← Spec.map_id] at he
  rw [Category.assoc, ← hc, ← Spec.map_comp] at hy
  have h₁ := Spec.map_injective he
  have e₁ : ∀ k, α.hom (c.hom k) = k := fun k => congrArg (fun r => r.hom k) h₁
  subst hy
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  ext w
  have e₂ : c.hom (α.hom w) = w := α.hom.injective (e₁ _)
  simp [e₂]

theorem exists_apply_ne_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), f ≠ 0 →
    ∃ a : A.X.left, f.hom.left a ≠ B.origin := by
  intro K _ A B f hf
  by_contra hcon
  push_neg at hcon
  apply hf
  refine ext_of_pt_eq K A B f 0 fun x => ?_
  rw [zero_hom]
  let e : Sp K ⟶ B.X.left := (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left
  have he : e ≫ B.X.hom = 𝟙 _ := Over.w (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X)
  have h1 : (x ≫ (1 : A.X ⟶ B.X)).left = (ptOver K (AlgebraicClosure K)).hom ≫ e := by
    have hP : (toUnit (ptOver K (AlgebraicClosure K))).left = (ptOver K (AlgebraicClosure K)).hom := by
      simpa using Over.w (toUnit (ptOver K (AlgebraicClosure K)))
    have hU : toUnit (Over.mk (𝟙 (Sp K))) = 𝟙 _ := toUnit_unique _ _
    simp only [e, Hom.one_def, ← Category.assoc, comp_toUnit, hU, Category.id_comp, Over.comp_left, hP]
  apply Over.OverMorphism.ext
  rw [h1]
  exact eq_comp_section_of_apply_eq B.X.hom e he _ _ (Over.w (x ≫ f.hom))
    (IsLocalRing.closedPoint _) (IsLocalRing.closedPoint K) (hcon _)

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApplyNeOriginStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_apply_ne_origin' : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), f ≠ 0 → ∃ a : A.X.left, f.hom.left a ≠ B.origin := by
  first | exact @GlobalTheory.AV.AbVar.exists_apply_ne_origin | exact GlobalTheory.AV.AbVar.exists_apply_ne_origin | (intros; apply GlobalTheory.AV.AbVar.exists_apply_ne_origin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionsVanishingOriginSeparating
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionsVanishingOriginSeparating
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RelAmpleSep

theorem mem_iff_of_gen {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {κ : Type} (r : κ → R) (c : κ → A)
    (I : Ideal R) (hI : ∀ j, r j - φ (c j) ∈ I) (p : MvPolynomial κ A) :
    MvPolynomial.eval₂Hom φ r p ∈ I ↔ φ (MvPolynomial.eval c p) ∈ I := by
  have hr : (Ideal.Quotient.mk I) ∘ r = ((Ideal.Quotient.mk I).comp φ) ∘ c := by
    funext j; exact Ideal.Quotient.eq.2 (hI j)
  have e : Ideal.Quotient.mk I (MvPolynomial.eval₂Hom φ r p) = Ideal.Quotient.mk I (φ (MvPolynomial.eval c p)) := by
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, hr, MvPolynomial.eval,
      MvPolynomial.coe_eval₂Hom, ← RingHom.comp_apply, MvPolynomial.eval₂_comp_left]
    rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem (I := I), e]

theorem ideal_eq_of_gen {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {κ : Type} (r : κ → R) (c : κ → A)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom φ r)) (P Q : Ideal R)
    (hP : ∀ j, r j - φ (c j) ∈ P) (hQ : ∀ j, r j - φ (c j) ∈ Q) (hPQ : ∀ x, φ x ∈ P ↔ φ x ∈ Q) : P = Q := by
  ext a
  obtain ⟨p, rfl⟩ := hs a
  rw [mem_iff_of_gen φ r c P hP, mem_iff_of_gen φ r c Q hQ]
  exact hPQ _

theorem mem_basicOpen_iff_prime {Y : Scheme.{0}} {D : Y.Opens} (hD : IsAffineOpen D) {y : Y} (hy : y ∈ D)
    (a : Γ(Y, D)) : y ∈ Y.basicOpen a ↔ a ∉ (hD.primeIdealOf ⟨y, hy⟩).asIdeal := by
  have h := hD.fromSpec_primeIdealOf ⟨y, hy⟩
  have h2 : hD.primeIdealOf ⟨y, hy⟩ ∈ hD.fromSpec ⁻¹ᵁ Y.basicOpen a ↔ y ∈ Y.basicOpen a := by
    show hD.fromSpec (hD.primeIdealOf ⟨y, hy⟩) ∈ Y.basicOpen a ↔ y ∈ Y.basicOpen a
    rw [h]
  rw [← h2, hD.fromSpec_preimage_basicOpen]
  rfl

variable {K : Type} [Field K]

theorem one_left_comp_hom (B : AbVar K) : (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left ≫ B.X.hom = 𝟙 _ := Over.w _

theorem sp_pt_eq (a b : Sp K) : a = b := by
  have h : ∀ p : PrimeSpectrum K, p.asIdeal = ⊥ := fun p => Ideal.eq_bot_of_prime _
  exact PrimeSpectrum.ext ((h a).trans (h b).symm)

theorem top_le_preimage_unit (B : AbVar K) : (⊤ : (Over.mk (𝟙 (Sp K))).left.Opens) ≤
    (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left ⁻¹ᵁ (B.X.hom ⁻¹ᵁ ⊤) := fun _ _ => trivial

def unitU (B : AbVar K) : (⊤ : (Sp K).Opens).toScheme ⟶ (B.X.hom ⁻¹ᵁ ⊤).toScheme :=
  (1 : Over.mk (𝟙 (Sp K)) ⟶ B.X).left.resLE (B.X.hom ⁻¹ᵁ ⊤) (⊤ : (Over.mk (𝟙 (Sp K))).left.Opens)
    (top_le_preimage_unit B)

theorem unitU_comp (B : AbVar K) : unitU B ≫ (B.X.hom ∣_ ⊤) = 𝟙 _ := by
  rw [← cancel_mono (⊤ : (Sp K).Opens).ι, Category.assoc, morphismRestrict_ι, unitU,
    Scheme.Hom.resLE_comp_ι_assoc, one_left_comp_hom, Category.comp_id, Category.id_comp]

theorem unitU_ι (B : AbVar K) (t : (⊤ : (Sp K).Opens).toScheme) :
    (B.X.hom ⁻¹ᵁ ⊤).ι (unitU B t) = B.origin := by
  rw [← Scheme.Hom.comp_apply, unitU, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply, AbVar.origin]
  exact congrArg _ (sp_pt_eq _ _)

theorem topU_pt_eq (a b : (⊤ : (Sp K).Opens).toScheme) : a = b := Subtype.ext (sp_pt_eq _ _)

theorem isUnit_sub_mul_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {a b : R} (c : R) (ha : IsUnit a)
    (hb : ¬ IsUnit b) : IsUnit (a - c * b) := by
  by_contra h
  have hb' : b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hb
  have h' : a - c * b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 h
  have h'' := Ideal.add_mem _ h' (Ideal.mul_mem_left _ c hb')
  rw [sub_add_cancel] at h''
  exact (IsLocalRing.mem_maximalIdeal _).1 h'' ha

theorem gs_secSubScale {Y : Scheme.{0}} {P : LB Y} (a b : P.Sec) (c : Γ(Y, ⊤)) (y : Y) (k : P.ι) (hk : y ∈ P.U k) :
    gs (𝟙 Y) y _ ((DVR.SecOps.secAdd a (DVR.SecOps.secNeg (DVR.SecOps.secScale c b))).f k) =
      gs (𝟙 Y) y _ (a.f k) - gs (𝟙 Y) y ⊤ c * gs (𝟙 Y) y _ (b.f k) := by
  have e : (DVR.SecOps.secAdd a (DVR.SecOps.secNeg (DVR.SecOps.secScale c b))).f k =
      a.f k - Out.resTop _ c * b.f k := by
    simp only [DVR.SecOps.secAdd, DVR.SecOps.secNeg, DVR.SecOps.secScale, sub_eq_add_neg]
  rw [e, LBGerm.gs_sub _ y _ hk, gs_mul _ y _ hk, Out.resTop, gs_res _ y _ hk]

theorem exists_sep_of_chart {Y T : Scheme.{0}} (π : Y ⟶ T) (u : T ⟶ Y) (hu : u ≫ π = 𝟙 T) (hT : ∀ a b : T, a = b)
    {P : LB Y} (hP : P.IsLB) {n : ℕ} (s : Fin n → P.Sec) (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (i : Fin n) (hD : IsAffineOpen (Out.nonzeroLocus (s i)))
    (r : Fin n → Γ(Y, Out.nonzeroLocus (s i)))
    (hr : ∀ j k, (Y.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ P.U k)).op).hom ((s j).f k) =
            (Y.presheaf.map (homOfLE (inf_le_left :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ Out.nonzeroLocus (s i))).op).hom (r j) *
            (Y.presheaf.map (homOfLE (inf_le_right :
              Out.nonzeroLocus (s i) ⊓ P.U k ≤ P.U k)).op).hom ((s i).f k))
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (π.appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom r))
    (t₀ : T) (hi : u t₀ ∈ Out.nonzeroLocus (s i)) :
    ∃ t : Fin n → P.Sec, (∀ j, u t₀ ∉ Out.nonzeroLocus (t j)) ∧
      ∀ y, y ≠ u t₀ → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  classical
  have hTle : ⊤ ≤ u ⁻¹ᵁ Out.nonzeroLocus (s i) := fun t _ => by rw [hT t t₀]; exact hi
  let c : Fin n → Γ(T, ⊤) := fun j => (u.appLE (Out.nonzeroLocus (s i)) ⊤ hTle).hom (r j)
  let φ := (π.appLE ⊤ (Out.nonzeroLocus (s i)) le_top).hom
  have hc : ∀ (y : Y) (x : Γ(T, ⊤)), gs (𝟙 Y) y ⊤ (π.appTop.hom x) = gs π y ⊤ x := fun y x =>
    (gs_pull (𝟙 Y) π y ⊤ trivial x).trans (by rw [Category.id_comp])
  have hφ : ∀ y ∈ Out.nonzeroLocus (s i), ∀ x, gs (𝟙 Y) y _ (φ x) = gs π y ⊤ x := fun y hy x =>
    (gs_appLE π ⊤ _ le_top (𝟙 Y) y hy x).trans (by rw [Category.id_comp])
  have hrel : ∀ j k y, y ∈ Out.nonzeroLocus (s i) → y ∈ P.U k →
      gs (𝟙 Y) y _ ((s j).f k) = gs (𝟙 Y) y _ (r j) * gs (𝟙 Y) y _ ((s i).f k) := by
    intro j k y hyD hk
    have hm : y ∈ Out.nonzeroLocus (s i) ⊓ P.U k := ⟨hyD, hk⟩
    have e := congrArg (gs (𝟙 Y) y (Out.nonzeroLocus (s i) ⊓ P.U k)) (hr j k)
    rwa [gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
  have hkey : ∀ y ∈ Out.nonzeroLocus (s i), ∀ j k, y ∈ P.U k →
      gs (𝟙 Y) y _ ((DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg
        (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i)))).f k) =
        gs (𝟙 Y) y _ (r j - φ (c j)) * gs (𝟙 Y) y _ ((s i).f k) := by
    intro y hy j k hk
    rw [gs_secSubScale _ _ _ y k hk, hrel j k y hy hk, hc, LBGerm.gs_sub _ y _ hy, hφ y hy]
    ring
  have hiff : ∀ y ∈ Out.nonzeroLocus (s i), ∀ j,
      y ∈ Out.nonzeroLocus (DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg
        (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i)))) ↔ y ∈ Y.basicOpen (r j - φ (c j)) := by
    intro y hy j
    obtain ⟨k, hk⟩ := exists_chart hP y
    rw [GlobalTheory.mem_nonzeroLocus_iff_isUnit _ hk, hkey y hy j k hk, IsUnit.mul_iff,
      ← GlobalTheory.mem_nonzeroLocus_iff_isUnit (s i) hk, LBGerm.isUnit_gs_iff (𝟙 Y) y _ hy]
    exact and_iff_left hy
  have h0 : ∀ j, u t₀ ∉ Y.basicOpen (r j - φ (c j)) := by
    intro j h
    have hu1 := (LBGerm.isUnit_gs_iff u t₀ _ hi _).2 h
    have e1 : gs u t₀ _ (r j) = gs (𝟙 T) t₀ ⊤ (c j) :=
      ((gs_appLE u _ ⊤ hTle (𝟙 T) t₀ trivial (r j)).trans (by rw [Category.id_comp])).symm
    have e2 : gs u t₀ _ (φ (c j)) = gs (𝟙 T) t₀ ⊤ (c j) :=
      (gs_appLE π ⊤ _ le_top u t₀ hi (c j)).trans (by rw [hu])
    rw [LBGerm.gs_sub u t₀ _ hi, e1, e2, sub_self] at hu1
    exact not_isUnit_zero hu1
  refine ⟨fun j => DVR.SecOps.secAdd (s j) (DVR.SecOps.secNeg (DVR.SecOps.secScale (π.appTop.hom (c j)) (s i))),
    fun j h => h0 j ((hiff _ hi j).1 h), fun y hy => ?_⟩
  by_cases hyD : y ∈ Out.nonzeroLocus (s i)
  · by_contra hno
    push_neg at hno
    have hPy : ∀ j, r j - φ (c j) ∈ (hD.primeIdealOf ⟨y, hyD⟩).asIdeal := fun j => by
      by_contra h
      exact hno j ((hiff y hyD j).2 ((mem_basicOpen_iff_prime hD hyD _).2 h))
    have hQ : ∀ j, r j - φ (c j) ∈ (hD.primeIdealOf ⟨u t₀, hi⟩).asIdeal := fun j => by
      by_contra h
      exact h0 j ((mem_basicOpen_iff_prime hD hi _).2 h)
    have hb : ∀ z ∈ Out.nonzeroLocus (s i), ∀ x, z ∈ Y.basicOpen (φ x) ↔ π z ∈ T.basicOpen x := fun z hz x =>
      (LBGerm.isUnit_gs_iff (𝟙 Y) z _ hz (φ x)).symm.trans (by rw [hφ z hz]; exact LBGerm.isUnit_gs_iff π z ⊤ trivial x)
    have hPQ : ∀ x, φ x ∈ (hD.primeIdealOf ⟨y, hyD⟩).asIdeal ↔ φ x ∈ (hD.primeIdealOf ⟨u t₀, hi⟩).asIdeal := by
      intro x
      rw [← not_iff_not, ← mem_basicOpen_iff_prime hD hyD, ← mem_basicOpen_iff_prime hD hi, hb y hyD, hb _ hi,
        hT (π y) (π (u t₀))]
    have hE := ideal_eq_of_gen φ r c hs _ _ hPy hQ hPQ
    have e1 := hD.fromSpec_primeIdealOf ⟨y, hyD⟩
    have e2 := hD.fromSpec_primeIdealOf ⟨u t₀, hi⟩
    rw [PrimeSpectrum.ext hE] at e1
    exact hy (e1.symm.trans e2)
  · have hy' : y ∈ (⨆ i, Out.nonzeroLocus (s i)) := by rw [hcov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
    obtain ⟨k, hk⟩ := exists_chart hP y
    refine ⟨j, ?_⟩
    rw [GlobalTheory.mem_nonzeroLocus_iff_isUnit _ hk, gs_secSubScale _ _ _ y k hk]
    exact isUnit_sub_mul_of_not_isUnit _ ((GlobalTheory.mem_nonzeroLocus_iff_isUnit (s j) hk).1 hj)
      fun h => hyD ((GlobalTheory.mem_nonzeroLocus_iff_isUnit (s i) hk).2 h)

theorem exists_sec_sep_origin : ∀ (K : Type) [Field K] (B : AbVar K) (L : LB B.X.left), L.IsLB →
    Out.RelAmple B.X L → ∃ N : ℕ, 1 ≤ N ∧ ∃ (M : ℕ) (t : Fin M → LB.Sec (Out.powOver B.X L ⊤ N)),
      (∀ j y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y ∉ Out.nonzeroLocus (t j)) ∧
      ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y ≠ B.origin → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  intro K _ B L hL hA
  obtain ⟨N, hN, M, s, hcov, hs⟩ := hA ⊤ (isAffineOpen_top _)
  obtain ⟨t₀⟩ : Nonempty (⊤ : (Sp K).Opens).toScheme := ⟨⟨IsLocalRing.closedPoint K, trivial⟩⟩
  have hmem : unitU B t₀ ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  obtain ⟨hD, r, hr, hsurj⟩ := hs i
  obtain ⟨t, h1, h2⟩ := exists_sep_of_chart (B.X.hom ∣_ ⊤) (unitU B) (unitU_comp B) topU_pt_eq
    (LB.isLB_linComb hL _ _) s hcov i hD r hr hsurj t₀ hi
  have hinj : ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y = unitU B t₀ := fun y hy =>
    Subtype.ext ((Scheme.Opens.ι_apply _ _).symm.trans
      (hy.trans ((unitU_ι B t₀).symm.trans (Scheme.Opens.ι_apply _ _))))
  exact ⟨N, hN, M + 1, t, fun j y hy => hinj y hy ▸ h1 j, fun y hy => h2 y fun h => hy (h ▸ unitU_ι B t₀)⟩

end GlobalTheory.RelAmpleSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionsVanishingOriginSeparatingStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ampleSections_vanishing_origin_separating : ∀ (K : Type) [Field K] (B : AbVar K) (L : LB B.X.left), L.IsLB → Out.RelAmple B.X L → ∃ N : ℕ, 1 ≤ N ∧ ∃ (M : ℕ) (t : Fin M → LB.Sec (Out.powOver B.X L ⊤ N)), (∀ j y, (B.X.hom ⁻¹ᵁ ⊤).ι y = B.origin → y ∉ Out.nonzeroLocus (t j)) ∧ ∀ y, (B.X.hom ⁻¹ᵁ ⊤).ι y ≠ B.origin → ∃ j, y ∈ Out.nonzeroLocus (t j) := by
  first | (exact @GlobalTheory.RelAmpleSep.exists_sec_sep_origin) | (exact GlobalTheory.RelAmpleSep.exists_sec_sep_origin) | (intros; apply GlobalTheory.RelAmpleSep.exists_sec_sep_origin  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackAmpleVanishingOrigin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_left_origin {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) : f.hom.left A.origin = B.origin := by
  have e : (1 : Over.mk (𝟙 (Sp K)) ⟶ A.X) ≫ f.hom = 1 := by
    rw [CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, IsMonHom.one_hom]
  unfold origin
  rw [← e, Over.comp_left]
  rfl

theorem exists_sec_pull_ample_vanish_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left),
    IsAmpleCls d → f ≠ 0 → ∃ (m : ℕ) (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), 0 < m ∧
      cls M hM = m • CechPic.pull f.hom.left d ∧ Out.nonzeroLocus s ≠ ⊥ ∧ A.origin ∉ Out.nonzeroLocus s := by
  intro K _ A B f d hd hf
  obtain ⟨L, hL, amp, rfl⟩ := hd
  obtain ⟨N, hN, M, t, h0, h1⟩ := GlobalTheory.T.exists_ampleSections_vanishing_origin_separating K B L hL amp
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_apply_ne_origin' K A B f hf
  let ιB := (B.X.hom ⁻¹ᵁ ⊤).ι
  let h : A.X.left ⟶ (B.X.hom ⁻¹ᵁ ⊤).toScheme := IsOpenImmersion.lift ιB f.hom.left (by
    rw [Scheme.Opens.range_ι]; intro x _; trivial)
  have hh : h ≫ ιB = f.hom.left := IsOpenImmersion.lift_fac _ _ _
  have hpt : ∀ x, ιB (h x) = f.hom.left x := fun x => by rw [← hh]; rfl
  obtain ⟨j, hj⟩ := h1 (h a) (by rw [hpt]; exact ha)
  let s := ReciprocityTheory.ChartRestriction.G.DVR.pullSec L (fun _ : Fin N => ιB) (fun _ => 1) (t j) h
  have hs : Out.nonzeroLocus s = h ⁻¹ᵁ Out.nonzeroLocus (t j) := GlobalTheory.nonzeroLocus_pullSec _ _ (t j) h
  refine ⟨N, _, LB.isLB_linComb hL _ _, s, hN, ?_, ?_, ?_⟩
  · rw [cls_linComb hL]
    simp only [hh, one_zsmul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  · intro e
    have : a ∈ Out.nonzeroLocus s := by rw [hs]; exact hj
    rw [e] at this; exact this
  · intro ho
    rw [hs] at ho
    exact h0 j (h A.origin) (by rw [hpt, hom_left_origin]) ho

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackAmpleVanishingOriginStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_pullbackAmple_vanishing_origin : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left), IsAmpleCls d → f ≠ 0 → ∃ (m : ℕ) (M : LB A.X.left) (hM : M.IsLB) (s : LB.Sec M), 0 < m ∧ cls M hM = m • CechPic.pull f.hom.left d ∧ Out.nonzeroLocus s ≠ ⊥ ∧ A.origin ∉ Out.nonzeroLocus s := by
  first | (exact @GlobalTheory.AV.AbVar.exists_sec_pull_ample_vanish_origin) | (exact GlobalTheory.AV.AbVar.exists_sec_pull_ample_vanish_origin) | (intros; apply GlobalTheory.AV.AbVar.exists_sec_pull_ample_vanish_origin  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmplePullbackIntersectionDegreePosOfNeZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_pull_ample_pos : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left) (d : Pic B.X.left), IsAmpleCls c → IsAmpleCls d → ∀ f : A ⟶ B, f ≠ 0 → 0 < inter A (Fin.cons (CechPic.pull f.hom.left d) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  intro K _ A B n hdim c d hc hd f hf
  obtain ⟨m, M, hM, s, hm, hcls, hne, horig⟩ := GlobalTheory.T.exists_section_pullbackAmple_vanishing_origin K A B f d hd hf
  have htop : Out.nonzeroLocus s ≠ ⊤ := by
    intro h
    apply horig
    rw [h]
    trivial
  have hpos := GlobalTheory.T.effectiveDivisor_pos_degree_ampleClass K A n hdim c hc M hM s hne htop
  obtain ⟨⟨Φ, hΦ⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin (n + 1)) (by simp [hdim])
  set x := CechPic.pull f.hom.left d
  have hcons : (Fin.cons (cls M hM) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left)
      = Function.update (Fin.cons x (fun _ : Fin n => c)) 0 ((m : ℤ) • x) := by
    rw [hcls]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [natCast_zsmul]
    · simp [Function.update, Fin.succ_ne_zero]
  rw [← hΦ, hcons, Φ.map_update_smul, Fin.update_cons_zero, smul_eq_mul] at hpos
  rw [← hΦ]
  exact pos_of_mul_pos_right hpos (by simpa using Int.ofNat_nonneg m)

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmplePullbackIntersectionDegreePosOfNeZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_pullback_intersection_degree_pos_of_ne_zero : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℕ), A.dim = n + 1 → ∀ (c : Pic A.X.left) (d : Pic B.X.left), IsAmpleCls c → IsAmpleCls d → ∀ f : A ⟶ B, f ≠ 0 → 0 < inter A (Fin.cons (CechPic.pull f.hom.left d) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left) := by
  first | (exact @GlobalTheory.AV.AbVar.inter_pull_ample_pos) | (exact GlobalTheory.AV.AbVar.inter_pull_ample_pos) | (intros; apply GlobalTheory.AV.AbVar.inter_pull_ample_pos  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDimEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDimEqZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AV.AbVar

theorem isIso_hom_of_dim_eq_zero {K : Type} [Field K] (A : AbVar K) (h : A.dim = 0) : IsIso A.X.hom := by
  have hA := A.ab
  have : IsProper A.X.hom := hA.proper
  have hs : SmoothOfRelativeDimension 0 A.X.hom := h ▸ A.smooth
  have : Etale A.X.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hs
  let e : Sp K ⟶ A.X.left := (1 : 𝟙_ (Over (Sp K)) ⟶ A.X).left
  have he : e ≫ A.X.hom = 𝟙 _ := Over.w (1 : 𝟙_ (Over (Sp K)) ⟶ A.X)
  have : IsOpenImmersion e := isOpenImmersion_of_section_of_etale A.X.hom e he
  have : IsClosedImmersion e := by
    have : IsClosedImmersion (e ≫ A.X.hom) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp e A.X.hom
  obtain ⟨hI, -, -⟩ := isIntegral_isLocallyNoetherian_compactSpace K A
  have : ConnectedSpace A.X.left := inferInstance
  have hne : (Set.range e).Nonempty := ⟨_, (default : PrimeSpectrum K), rfl⟩
  have hsurj : Function.Surjective e := Set.range_eq_univ.1
    (IsClopen.eq_univ ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩ hne)
  have : Surjective e := ⟨hsurj⟩
  have : IsIso e := IsOpenImmersion.isIso e
  have : IsIso (e ≫ A.X.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e A.X.hom

theorem hom_eq_of_isIso {K : Type} [Field K] {A : AbVar K} (h : IsIso A.X.hom) {T : Over (Sp K)}
    (g₁ g₂ : T ⟶ A.X) : g₁ = g₂ := by
  ext
  rw [← cancel_mono A.X.hom, Over.w, Over.w]

theorem eq_zero_of_dim_eq_zero :
    ∀ (K : Type) [Field K] (A B : AbVar K), (A.dim = 0 ∨ B.dim = 0) → ∀ f : A ⟶ B, f = 0 := by
  intro K _ A B h f
  rcases h with h | h
  · have hi := isIso_hom_of_dim_eq_zero A h
    apply Subtype.ext
    change f.hom = (0 : A ⟶ B).hom
    rw [zero_hom]
    have e1 : f.hom = (1 : A.X ⟶ A.X) ≫ f.hom := by
      rw [hom_eq_of_isIso hi (1 : A.X ⟶ A.X) (𝟙 A.X), Category.id_comp]
    rw [e1, CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, IsMonHom.one_hom]
  · have hi := isIso_hom_of_dim_eq_zero B h
    apply Subtype.ext
    exact hom_eq_of_isIso hi _ _

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDimEqZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_dim_eq_zero' : ∀ (K : Type) [Field K] (A B : AbVar K), (A.dim = 0 ∨ B.dim = 0) → ∀ f : A ⟶ B, f = 0 := by
  first | exact @GlobalTheory.AV.AbVar.eq_zero_of_dim_eq_zero | exact GlobalTheory.AV.AbVar.eq_zero_of_dim_eq_zero | (intros; apply GlobalTheory.AV.AbVar.eq_zero_of_dim_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefQuadraticFormHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem pull_add_add_pull_sub {K : Type} [Field K] {A B : AbVar K} (d : Pic B.X.left)
    (hd : CechPic.pull (Hom.hom (-(𝟙 B))).left d = d) (f g : A ⟶ B) :
    CechPic.pull (f + g).hom.left d + CechPic.pull (f - g).hom.left d
      = (2 : ℤ) • CechPic.pull f.hom.left d + (2 : ℤ) • CechPic.pull g.hom.left d := by
  have hl := (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K B d A.X f.hom g.hom g.hom (-1)).2.2.2.2
  have hq := (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K A B d hd g (-1)).2
  rw [zpow_neg_one] at hl
  rw [neg_one_zsmul] at hq
  norm_num at hq
  have e1 : CechPic.pull (f + g).hom.left d
      = lam d f.hom g.hom + CechPic.pull f.hom.left d + CechPic.pull g.hom.left d := by
    rw [lam, add_hom]; abel
  have e2 : CechPic.pull (f - g).hom.left d
      = lam d f.hom (g.hom⁻¹) + CechPic.pull f.hom.left d + CechPic.pull g.hom.left d := by
    rw [sub_eq_add_neg, ← hq, lam, add_hom, neg_hom]; abel
  rw [e1, e2, hl]
  simp only [neg_one_smul, two_smul]
  abel

theorem exists_posDef_quadratic_hom : ∀ (K : Type) [Field K] (A B : AbVar K), ∃ Q : (A ⟶ B) → ℤ,
    (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) ∧ (∀ f, 0 ≤ Q f) ∧ ∀ f, Q f = 0 → f = 0 := by
  intro K _ A B
  obtain ⟨d, hdA, hd⟩ := GlobalTheory.AV.AbVar.exists_symm_ample K B
  obtain ⟨c, hc⟩ := GlobalTheory.AV.exists_isAmpleCls K A
  rcases hA : A.dim with _ | n
  · refine ⟨fun _ => 0, fun _ _ => by simp, fun _ => le_rfl, fun f _ => GlobalTheory.T.eq_zero_of_dim_eq_zero' K A B (Or.inl hA) f⟩
  · obtain ⟨⟨M, hM⟩, -⟩ := GlobalTheory.T.intersection_number_multilinear_symm K A (Fin (n + 1)) (by simp [hA])
    refine ⟨fun f => inter A (Fin.cons (CechPic.pull f.hom.left d) (fun _ : Fin n => c) : Fin (n + 1) → Pic A.X.left), ?_, ?_, ?_⟩
    · intro f g
      simp only [← hM]
      rw [← MultilinearMap.cons_add, pull_add_add_pull_sub d hd f g, MultilinearMap.cons_add,
        MultilinearMap.cons_smul, MultilinearMap.cons_smul]
      simp [two_mul]
    · intro f
      by_cases hf : f = 0
      · subst hf
        have h0 := (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K A B d hd (0 : A ⟶ B) 0).2
        rw [zero_smul] at h0
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul] at h0
        show 0 ≤ inter A _
        rw [← hM, h0, M.map_coord_zero (0 : Fin (n + 1)) (by simp)]
      · exact (GlobalTheory.T.ample_pullback_intersection_degree_pos_of_ne_zero K A B n hA c d hc hdA f hf).le
    · intro f hf0
      by_contra hf
      exact (GlobalTheory.T.ample_pullback_intersection_degree_pos_of_ne_zero K A B n hA c d hc hdA f hf).ne' hf0

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefQuadraticFormHomStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_posDef_quadraticForm_hom : ∀ (K : Type) [Field K] (A B : AbVar K), ∃ Q : (A ⟶ B) → ℤ, (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) ∧ (∀ f, 0 ≤ Q f) ∧ ∀ f, Q f = 0 → f = 0 := by
  first | (exact @GlobalTheory.AV.AbVar.exists_posDef_quadratic_hom) | (exact GlobalTheory.AV.AbVar.exists_posDef_quadratic_hom) | (intros; apply GlobalTheory.AV.AbVar.exists_posDef_quadratic_hom  <;> assumption)
end
