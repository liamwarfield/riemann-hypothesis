module

public import Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.SpreadOf
public import Development.EtaleCohomology.EtaleSheaves.LeafVanStalk
public import Development.EtaleCohomology.EtaleSheaves.LeafNormalModelPf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.EtStagePf
noncomputable section
open CategoryTheory Limits TensorProduct

namespace LateralTheory.E.EtStagePf

theorem exists_model {A T : CommRingCat.{0}} (f : A ⟶ T) (hf : f.hom.Etale) :
    ∃ (A₀ B₀ : CommRingCat.{0}) (a : A₀ ⟶ A) (f₀ : A₀ ⟶ B₀) (b : B₀ ⟶ T),
      (Int.castRingHom A₀).FinitePresentation ∧ f₀.hom.Etale ∧ IsPushout a f₀ f b := by
  let _ := f.hom.toAlgebra
  have h : Algebra.Etale A T := hf
  obtain ⟨A₀, B₀, _, _, hfg, het, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℤ A T
  have hft : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  have hfp : Algebra.FinitePresentation ℤ A₀ := Algebra.FinitePresentation.of_finiteType.mp hft
  refine ⟨CommRingCat.of A₀, CommRingCat.of B₀, CommRingCat.ofHom (algebraMap A₀ A),
    CommRingCat.ofHom (algebraMap A₀ B₀),
    CommRingCat.ofHom (e.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom), ?_, ?_, ?_⟩
  · have := RingHom.finitePresentation_algebraMap.mpr hfp
    rwa [RingHom.ext_int (algebraMap ℤ A₀) (Int.castRingHom A₀)] at this
  · exact RingHom.etale_algebraMap.mpr het
  · refine (CommRingCat.isPushout_tensorProduct A₀ A B₀).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      e.symm.toRingEquiv.toCommRingCatIso (by simp) (by simp) ?_ ?_
    · ext x
      exact e.symm.commutes x
    · ext x
      rfl

theorem EtStage_of : LateralTheory.E.SpreadPf.Cut.EtStage := by
  intro J _ _ D c hc _ _ T _ f _ _ _ hf
  obtain ⟨A₀, B₀, a, f₀, b, hfp, het, hP⟩ := exists_model f hf
  let α : (Functor.const J).obj (CommRingCat.of ℤ) ⟶ D :=
    { app := fun i => CommRingCat.ofHom (Int.castRingHom _)
      naturality := fun _ _ _ => CommRingCat.hom_ext (RingHom.ext_int _ _) }
  obtain ⟨k, a', -, ha⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit (CommRingCat.of ℤ) D α
    (CommRingCat.ofHom (Int.castRingHom A₀)) c hc hfp a
    (fun _ => CommRingCat.hom_ext (RingHom.ext_int _ _))
  subst ha
  have hQ := IsPushout.of_hasPushout a' f₀
  have hw : a' ≫ c.ι.app k ≫ f = f₀ ≫ b := by rw [← hP.w, Category.assoc]
  refine ⟨k, pushout a' f₀, pushout.inl a' f₀, pushout.desc (c.ι.app k ≫ f) b hw, ?_, ?_⟩
  · refine IsPushout.of_left ?_ (pushout.inl_desc _ _ _).symm hQ
    rw [pushout.inr_desc]
    exact hP
  · have := (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff (P := @RingHom.Etale)).mpr
      RingHom.Etale.isStableUnderBaseChange
    exact this.of_isPushout hQ het

end LateralTheory.E.EtStagePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.A9OfA0A1EigenbasisA6
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafClosedSH0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafVanBPf

def LeafSHSieve : Prop := ∀ (X : Scheme.{0}) [IsAffine X], SH Γ(X, ⊤) →
  ∀ S ∈ Scheme.etaleTopology X, S (𝟙 X)

def LeafSHQuot : Prop := ∀ (A : Type) [CommRing A], SH A → ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  IsEmpty W' ∨ SH Γ(W', ⊤)

def LeafEmptySec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}), IsEmpty X → Subsingleton (Sec F X)

def LeafPrimLift : Prop := ∀ (q : ℕ) (B C : Type) [CommRing B] [CommRing C] [HenselianLocalRing B] [Nontrivial C]
  (f : B →+* C), Function.Surjective f → Function.Surjective (Prim.map (q := q) f)

theorem a9_of_a0_a1_eigenbasis_a6 (hy : Hyps) : A9 := hy.2.2.2.2.2.2.2.1

theorem twF_surj (hP : LeafPrimLift) (q : ℕ) (i : ℤ) {B C : CommRingCat.{0}} [HenselianLocalRing B] [Nontrivial C]
    (f : B ⟶ C) (hf : Function.Surjective f) : Function.Surjective ((twF q i).map f) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x', rfl⟩ := Finsupp.mapDomain_surjective (hP q B C f.hom hf) x
  exact ⟨Submodule.Quotient.mk x', rfl⟩

theorem secSurj (hS : LeafSHSieve) (hQ : LeafSHQuot) (hE : LeafEmptySec) (hP : LeafPrimLift) (q : ℕ) (i : ℤ)
    (A : Type) [CommRing A] (hA : SH A) {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'] :
    Function.Surjective (Sec.res ι' : Sec (tw q i) (Sp A) → Sec (tw q i) W') := by
  rcases hQ A hA ι' with hW | hW
  · have := hE (ZMod q) (tw q i) W' hW
    exact fun y => ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  have hW0 := hW
  obtain ⟨_, _⟩ := hW
  obtain ⟨_, _⟩ := hA
  intro s
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q i
  have hmem := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) s
  obtain ⟨t, ht⟩ := hS W' hW0 _ hmem
  let g : CommRingCat.of A ⟶ Γ(W', ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ι'.appTop
  have hg : Function.Surjective g := hsurj.comp (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective
  obtain ⟨t', rfl⟩ := twF_surj hP q i g hg t
  refine ⟨(toSheafify Scheme.etaleTopology P).app (op (Sp A)) ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t'), ?_⟩
  have e1 := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology P) ι'.op
    ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t')
  have e2 : P.map ι'.op ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t') = (twF q i).map g t' := by
    simp only [P, g, Functor.comp_map, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl
  rw [e2, ht] at e1
  simp only [op_id] at e1
  refine Eq.trans ?_ (e1.symm.trans ?_)
  · rfl
  · simp
    rfl

theorem LeafClosedSH0_of (hS : LeafSHSieve) (hQ : LeafSHQuot) (hE : LeafEmptySec) (hP : LeafPrimLift) :
    LeafClosedSH0 := by
  intro hy q _ i A _ _ hA hq W' ι' _
  obtain ⟨-, e, he, -⟩ := a9_of_a0_a1_eigenbasis_a6 hy (ZMod q) (tw q i)
  intro y
  obtain ⟨s, rfl⟩ := (e W').surjective y
  obtain ⟨t, rfl⟩ := secSurj hS hQ hE hP q i A hA ι' s
  exact ⟨e _ t, he _ t⟩

end LateralTheory.E.LeafClosedSH0Pf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.TruncBijPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open CochainComplex.HomComplex

namespace LateralTheory.E.TruncBijPf

section General
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] {K K' L : CochainComplex C ℤ}

def preC (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) : Cochain K L j := (Cochain.ofHom g).comp z (zero_add j)

theorem preC_v (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) (p q : ℤ) (h : p + j = q) :
    (preC g z).v p q h = g.f p ≫ z.v p q h := by
  simp [preC]

theorem δ_preC (g : K ⟶ K') {j : ℤ} (z : Cochain K' L j) (k : ℤ) : δ j k (preC g z) = preC g (δ j k z) :=
  δ_ofHom_comp g z k

theorem preC_zero (g : K ⟶ K') (j : ℤ) : preC g (0 : Cochain K' L j) = 0 := by
  simp [preC]

theorem preC_inj (g : K ⟶ K') (n : ℤ) (hg : ∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p))
    (hL : ∀ q : ℤ, q < 0 → IsZero (L.X q)) {j : ℤ} (hj : j ≤ n + 1) {x y : Cochain K' L j}
    (h : preC g x = preC g y) : x = y := by
  ext p q hpq
  by_cases hq : q < 0
  · exact (hL q hq).eq_of_tgt _ _
  · have := hg p (by omega)
    have h' := congrArg (fun z : Cochain K L j => z.v p q hpq) h
    simp only [preC_v] at h'
    exact (cancel_epi (g.f p)).1 h'

theorem preC_surj (g : K ⟶ K') (n : ℤ) (hg : ∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p))
    (hL : ∀ q : ℤ, q < 0 → IsZero (L.X q)) {j : ℤ} (hj : j ≤ n + 1) (y : Cochain K L j) :
    ∃ x : Cochain K' L j, preC g x = y := by
  refine ⟨Cochain.mk fun p q hpq =>
    if h : -(n + 1) ≤ p then (haveI := hg p h; inv (g.f p)) ≫ y.v p q hpq else 0, ?_⟩
  ext p q hpq
  by_cases hq : q < 0
  · exact (hL q hq).eq_of_tgt _ _
  · have hp : -(n + 1) ≤ p := by omega
    rw [preC_v, Cochain.mk_v, dite_eq_left hp, IsIso.hom_inv_id_assoc]

end General

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (q : ℤ) (hq : q < 0) : IsZero ((res R F).X q) :=
  CochainComplex.isZero_of_isStrictlyGE (injectiveResolution F).cochainComplex 0 q hq

theorem pull_mk (R : Type) [CommRing R] (F : Shv R) {K K' : Cx R} (g : K ⟶ K') (m : ℤ) (x : Cocycle K' (res R F) m) :
    ∃ y : Cocycle K (res R F) m, HK.pull R g F m (CohomologyClass.mk x) = CohomologyClass.mk y ∧
      (y : Cochain K (res R F) m) = preC g (x : Cochain K' (res R F) m) :=
  ⟨_, rfl, rfl⟩

end LateralTheory.E.TruncBijPf

open LateralTheory.E.TruncBijPf in
theorem LateralTheory.E.TruncPf.TruncBij_of : LateralTheory.E.TruncPf.TruncBij := by
  intro R _ F K K' g n hg m hm
  have hL := res_isZero R F
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, hy, hy'⟩ := pull_mk R F g m x
    rw [hy, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)] at hx
    obtain ⟨β, hβ⟩ := hx
    obtain ⟨β', rfl⟩ := preC_surj g n hg hL (by omega) β
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)]
    refine ⟨β', preC_inj g n hg hL (by omega) ?_⟩
    rw [← δ_preC, hβ, hy']
  · intro y
    obtain ⟨y, rfl⟩ := y.mk_surjective
    obtain ⟨x, hx⟩ := preC_surj g n hg hL (j := m) (by omega) (y : Cochain K (res R F) m)
    have hδ : δ m (m + 1) x = 0 := by
      apply preC_inj g n hg hL (by omega)
      rw [← δ_preC, hx, preC_zero, Cocycle.δ_eq_zero]
    obtain ⟨y', hy, hy'⟩ := pull_mk R F g m (Cocycle.mk x (m + 1) rfl hδ)
    refine ⟨_, hy.trans (congrArg CohomologyClass.mk (Cocycle.ext ?_))⟩
    rw [hy', ← hx]
    rfl
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafIntClosureAlgPf
noncomputable section
open Polynomial

namespace LateralTheory.E.LeafIntClosureAlgPf
open LateralTheory.E.LeafNormalModelPf

variable {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L]

theorem isAlgebraic_of_mem_adjoin (u x : L) (hx : x ∈ IntermediateField.adjoin Ω {u}) :
    IsAlgebraic (Algebra.adjoin Ω {u}) x := by
  obtain ⟨r, s, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff (F := Ω) (α := u) x).1 hx
  set R := Algebra.adjoin Ω {u}
  have hr : aeval u r ∈ R := by rw [show R = _ from Algebra.adjoin_singleton_eq_range_aeval Ω u]; exact ⟨r, rfl⟩
  have hs : aeval u s ∈ R := by rw [show R = _ from Algebra.adjoin_singleton_eq_range_aeval Ω u]; exact ⟨s, rfl⟩
  by_cases h0 : aeval u s = 0
  · rw [h0, div_zero]; exact isAlgebraic_zero
  refine ⟨C (⟨aeval u s, hs⟩ : R) * X - C ⟨aeval u r, hr⟩, ?_, ?_⟩
  · intro h
    have := congrArg (fun p => p.coeff 1) h
    simp only [coeff_sub, coeff_C_mul, coeff_X_one, mul_one, coeff_C, one_ne_zero, if_false,
      sub_zero, coeff_zero] at this
    exact h0 (congrArg Subtype.val this)
  · simp only [map_sub, map_mul, aeval_C, aeval_X]
    change aeval u s * (aeval u r / aeval u s) - aeval u r = 0
    rw [mul_div_cancel₀ _ h0, sub_self]

variable (Ω) in
theorem isAlgebraic_adjoin (u : L) [FiniteDimensional (IntermediateField.adjoin Ω {u}) L] :
    Algebra.IsAlgebraic (Algebra.adjoin Ω {u}) L := by
  constructor
  intro z
  set K := IntermediateField.adjoin Ω {u}
  have h1 : IsAlgebraic K z := Algebra.IsAlgebraic.isAlgebraic z
  have h2 : IsAlgebraic K.toSubalgebra z := h1
  have h3 : IsAlgebraic (Algebra.adjoin Ω (K : Set L)) z :=
    h2.tower_top_of_subalgebra_le (fun y hy => Algebra.subset_adjoin hy)
  refine IsAlgebraic.adjoin_of_forall_isAlgebraic (fun y hy => ?_) h3
  exact isAlgebraic_of_mem_adjoin u y hy.1

variable (Ω) in
theorem isFractionRing_intClosure (u : L) [FiniteDimensional (IntermediateField.adjoin Ω {u}) L] :
    IsFractionRing (integralClosure (Algebra.adjoin Ω {u}) L) L := by
  have := isAlgebraic_adjoin Ω u
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨y, hy, hint⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin Ω {u}) z).exists_integral_multiple
  have hy' : (y : L) ≠ 0 := fun h => hy (Subtype.ext h)
  refine ⟨⟨y • z, hint⟩, ⟨(y : L), isIntegral_algebraMap (R := Algebra.adjoin Ω {u}) (x := y)⟩, ?_⟩
  change z = y • z / (y : L)
  rw [Algebra.smul_def]
  change z = (y : L) * z / (y : L)
  field_simp

variable (Ω) in
theorem isIntegrallyClosed_intClosure (u : L) [FiniteDimensional (IntermediateField.adjoin Ω {u}) L] :
    IsIntegrallyClosed (integralClosure (Algebra.adjoin Ω {u}) L) := by
  have := isFractionRing_intClosure Ω u
  rw [isIntegrallyClosed_iff L]
  intro x hx
  set_option synthInstance.maxHeartbeats 200000 in
    exact ⟨⟨x, isIntegral_trans (A := integralClosure (Algebra.adjoin Ω {u}) L) x hx⟩, rfl⟩

theorem ringKrullDim_intClosure (u : L) (hu : Transcendental Ω u) :
    ringKrullDim (integralClosure (Algebra.adjoin Ω {u}) L) = 1 := by
  have h1 := ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (A := Algebra.adjoin Ω {u})
    (B := integralClosure (Algebra.adjoin Ω {u}) L) (fun a b h => Subtype.ext (congrArg (Subtype.val : integralClosure (Algebra.adjoin Ω {u}) L → L) h))
  have h2 := ringKrullDim_eq_of_ringEquiv (Polynomial.algEquivOfTranscendental Ω u hu).toRingEquiv
  rw [h1, ← h2]
  exact IsPrincipalIdealRing.ringKrullDim_eq_one _ (Polynomial.not_isField Ω)

def LeafIntClFinite : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (u : L),
  Transcendental Ω u → FiniteDimensional (IntermediateField.adjoin Ω {u}) L →
    Module.Finite (Algebra.adjoin Ω {u}) (integralClosure (Algebra.adjoin Ω {u}) L)

theorem finiteType_intCl (u : L) (h : Module.Finite (Algebra.adjoin Ω {u}) (integralClosure (Algebra.adjoin Ω {u}) L)) :
    Algebra.FiniteType Ω (intCl Ω u) := by
  have h1 : Algebra.FiniteType Ω (Algebra.adjoin Ω {u}) :=
    (Subalgebra.fg_iff_finiteType _).1 ⟨{u}, by rw [Finset.coe_singleton]⟩
  have h2 : Algebra.FiniteType (Algebra.adjoin Ω {u}) (integralClosure (Algebra.adjoin Ω {u}) L) := inferInstance
  have h3 : Algebra.FiniteType Ω (integralClosure (Algebra.adjoin Ω {u}) L) :=
    Algebra.FiniteType.trans (S := Algebra.adjoin Ω {u}) h1 h2
  exact h3

theorem LeafIntClosureAlg_of (h : LeafIntClFinite) : LeafIntClosureAlg := by
  intro Ω L _ _ _ u hu hfd
  refine ⟨finiteType_intCl u (h Ω L u hu hfd), ?_, ?_, ?_⟩
  · exact isIntegrallyClosed_intClosure Ω u
  · exact ringKrullDim_intClosure u hu
  · exact isFractionRing_intClosure Ω u

end LateralTheory.E.LeafIntClosureAlgPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.EtaleStandingHypothesesImplyRestrictionAxiom
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafInj0WPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf

theorem fgtInj0 (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E)
    (hU : Subsingleton (H R U F (-1))) (y : Hrel R f F 0) (hy : fgt R f F 0 y = 0) : y = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  obtain ⟨β, hβ⟩ : ∃ β : Cochain ((chains R).obj E) (res R F) (-1), δ (-1) 0 β = (Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp z.1 (zero_add 0) := by
    have := hy
    change CohomologyClass.mk _ = 0 at this
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (-1) (by omega)] at this
    obtain ⟨β, hβ⟩ := this
    exact ⟨β, by rw [hβ]; rfl⟩
  have hdec : z.1 = mappingCone.descCochain ((chains R).map f) ((mappingCone.inl ((chains R).map f)).comp z.1 (show -1 + 0 = -1 by omega))
      ((Cochain.ofHom (mappingCone.inr ((chains R).map f))).comp z.1 (zero_add 0)) (show (-1 : ℤ) + 1 = 0 by omega) := by
    rw [mappingCone.ext_cochain_from_iff _ (-1) 0 (by omega)]
    simp [mappingCone.inl_descCochain]
  have hz : δ 0 1 z.1 = 0 := Cocycle.δ_eq_zero z 1
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ (by omega)] at hz
  rw [mappingCone.ext_cochain_from_iff _ 0 1 (by omega)] at hz
  obtain ⟨hz1, -⟩ := hz
  simp only [Cochain.comp_zero, Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, add_zero] at hz1
  have hw : δ (-1) 0 ((mappingCone.inl ((chains R).map f)).comp z.1 (show -1 + 0 = -1 by omega) - (Cochain.ofHom ((chains R).map f)).comp β (zero_add (-1))) = 0 := by
    rw [δ_sub, δ_ofHom_comp, hβ, sub_eq_zero]
    rw [show Int.negOnePow 1 = -1 by decide] at hz1
    simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul, ← sub_eq_add_neg, sub_eq_zero] at hz1
    exact hz1
  obtain ⟨γ, hγ⟩ : ∃ γ : Cochain ((chains R).obj U) (res R F) (-2), δ (-2) (-1) γ = (mappingCone.inl ((chains R).map f)).comp z.1 (show -1 + 0 = -1 by omega) - (Cochain.ofHom ((chains R).map f)).comp β (zero_add (-1)) := by
    have h0 : CohomologyClass.mk (Cocycle.mk _ 0 (by omega) hw) = 0 := Subsingleton.elim _ _
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (-2) (by omega)] at h0
    obtain ⟨γ, hγ⟩ := h0
    exact ⟨γ, by rw [hγ]; rfl⟩
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (-1) (by omega)]
  refine ⟨mappingCone.descCochain ((chains R).map f) γ β (show (-2 : ℤ) + 1 = -1 by omega), ?_⟩
  rw [mappingCone.δ_descCochain _ _ _ _ _ (by omega), hγ, hβ, show Int.negOnePow 0 = 1 by decide, one_smul, sub_add_cancel]
  conv_rhs => rw [hdec]
  rfl

theorem fgtPull (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (y : Hrel R f F n) :
    pull R f F n (fgt R f F n y) = 0 := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk _ = 0
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨n.negOnePow • (mappingCone.inl ((chains R).map f)).comp y.1 (by omega), ?_⟩
  rw [δ_units_smul]
  rw [δ_comp (mappingCone.inl ((chains R).map f)) y.1 (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) (by omega)]
  simp [zcomp, mappingCone.δ_inl, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, smul_smul, Int.units_mul_self]

theorem fgtNat (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U)
  (e : E' ⟶ E) (comm : f' ≫ e = u ≫ f) (n : ℤ) (y : Hrel R f F n) :
  fgt R f' F n (rpull R f f' u e comm F n y) = pull R e F n (fgt R f F n y) := by
  obtain ⟨y, rfl⟩ := y.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  have key : mappingCone.inr ((chains R).map f') ≫ mappingCone.map ((chains R).map f') ((chains R).map f) ((chains R).map u) ((chains R).map e) (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) = (chains R).map e ≫ mappingCone.inr ((chains R).map f) := by
    simp [mappingCone.map]
  simp [zcomp, rmap]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, key]

theorem leafRelNat : LeafRelNat := fgtNat

def LeafSecTw : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (s : Sec (tw q i) U.left),
  Sec.res (prB ι U) s = 0 → ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Sec.res a.left s = 0

def LeafSec0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (h : Ht q (sch.obj U.left) 0 i),
  pull (ZMod q) (sch.map (prB ι U)) (tw q i) 0 h = 0 → ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ pull (ZMod q) (sch.map a.left) (tw q i) 0 h = 0

theorem etale_standing_hypotheses_imply_restriction_axiom (hH : Hyps) : A9 := by
  unfold Hyps at hH
  exact hH.2.2.2.2.2.2.2.1

theorem LeafSec0W_of (hT : LeafSecTw) : LeafSec0W := by
  intro hH q _ k _ hq i B W s ι _ U h h0 x hx
  obtain ⟨e, hnat, -⟩ := ((etale_standing_hypotheses_imply_restriction_axiom hH) (ZMod q) (tw q i)).2
  obtain ⟨t, rfl⟩ := (e U.left).surjective h
  rw [hnat] at h0
  have h1 : Sec.res (prB ι U) t = 0 := (e _).injective (by rw [h0, map_zero])
  obtain ⟨U', a, y, hy, h2⟩ := hT q k hq i s ι U t h1 x hx
  exact ⟨U', a, y, hy, by rw [hnat, h2, map_zero]⟩

theorem LeafInj0W_of (hT : LeafSecTw) : LeafInj0W := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV p g1 g2 hp1 hp2 hp3 hS U c x hx
  obtain ⟨U', a, y, hy, hz⟩ := LeafSec0W_of hT hH q k hq i s ι U _ (fgtPull (ZMod q) (tw q i) (sch.map (prB ι U)) 0 c) x hx
  refine ⟨U', a, y, hy, Cov.all ?_⟩
  intro U'' b
  apply fgtInj0 (ZMod q) (tw q i) (sch.map (prB ι U''))
  · exact ((etale_standing_hypotheses_imply_restriction_axiom hH) (ZMod q) (tw q i)).1 _ (-1) (by norm_num)
  · rw [fgtNat]
    have e : (b ≫ a).left = b.left ≫ a.left := rfl
    rw [e, Functor.map_comp, pull_comp, hz, map_zero]

end LateralTheory.E.LeafInj0WPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.Truncation
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf LateralTheory.E.TruncPf
open CochainComplex.HomComplex

namespace LateralTheory.E.TruncationInclusionIso

section Gen
open ComplexShape renaming embeddingUpIntGE → eG

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

abbrev sT (K : CochainComplex C ℤ) (a : ℤ) : CochainComplex C ℤ := (K.restriction (eG a)).extend (eG a)

def comp (K : CochainComplex C ℤ) (a : ℤ) {k : ℕ} {i : ℤ} (hk : (eG a).f k = i) : (sT K a).X i ⟶ K.X i :=
  ((K.restriction (eG a)).extendXIso (eG a) hk).hom ≫ (K.restrictionXIso (eG a) hk).hom

theorem comp_indep (K : CochainComplex C ℤ) (a : ℤ) {k k' : ℕ} {i : ℤ} (hk : (eG a).f k = i)
    (hk' : (eG a).f k' = i) : comp K a hk = comp K a hk' := by
  obtain rfl : k = k' := (eG a).injective_f (hk.trans hk'.symm)
  rfl

theorem sq (K : CochainComplex C ℤ) (a : ℤ) {k : ℕ} {i j : ℤ} (hi : (eG a).f k = i) (hj : (eG a).f (k + 1) = j) :
    comp K a hi ≫ K.d i j = (sT K a).d i j ≫ comp K a hj := by
  rw [HomologicalComplex.extend_d_eq _ _ hi hj, HomologicalComplex.restriction_d_eq _ _ hi hj]
  simp only [comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem le_of_f {a : ℤ} {k : ℕ} {i : ℤ} (hk : (eG a).f k = i) : a ≤ i := by
  change a + (k : ℤ) = i at hk; omega

theorem f_toNat {a i : ℤ} (h : a ≤ i) : (eG a).f (i - a).toNat = i := by
  change a + ((i - a).toNat : ℤ) = i; omega

theorem zero_below (K : CochainComplex C ℤ) {a i : ℤ} (h : i < a) : IsZero ((sT K a).X i) :=
  HomologicalComplex.isZero_extend_X _ _ i (fun _ hk => by have := le_of_f hk; omega)

def ιT (K : CochainComplex C ℤ) (a : ℤ) : sT K a ⟶ K where
  f i := if h : a ≤ i then comp K a (f_toNat h) else 0
  comm' i j hij := by
    change i + 1 = j at hij
    by_cases h : a ≤ i
    · rw [dite_eq_left h, dite_eq_left (by omega)]
      have hj : (eG a).f ((i - a).toNat + 1) = j := by
        change a + (((i - a).toNat + 1 : ℕ) : ℤ) = j; push_cast; omega
      rw [sq K a (f_toNat h) hj]
      congr 1
      apply comp_indep
    · exact (zero_below K (by omega)).eq_of_src _ _

theorem ιT_f (K : CochainComplex C ℤ) (a : ℤ) {k : ℕ} {i : ℤ} (hk : (eG a).f k = i) :
    (ιT K a).f i = comp K a hk := by
  dsimp only [ιT]
  rw [dite_eq_left (le_of_f hk)]
  apply comp_indep

instance (K : CochainComplex C ℤ) (a : ℤ) {k : ℕ} {i : ℤ} (hk : (eG a).f k = i) : IsIso (comp K a hk) := by
  dsimp only [comp]; infer_instance

theorem isIso_ιT (K : CochainComplex C ℤ) {a i : ℤ} (h : a ≤ i) : IsIso ((ιT K a).f i) := by
  rw [ιT_f K a (f_toNat h)]; infer_instance

def sTMap {K L : CochainComplex C ℤ} (f : K ⟶ L) (a : ℤ) : sT K a ⟶ sT L a :=
  HomologicalComplex.extendMap (HomologicalComplex.restrictionMap f (eG a)) (eG a)

theorem ιT_nat {K L : CochainComplex C ℤ} (f : K ⟶ L) (a : ℤ) : sTMap f a ≫ ιT L a = ιT K a ≫ f := by
  ext i
  simp only [HomologicalComplex.comp_f]
  by_cases h : a ≤ i
  · have hk := f_toNat h
    rw [ιT_f K a hk, ιT_f L a hk]
    rw [sTMap, HomologicalComplex.extendMap_f _ _ hk, HomologicalComplex.restrictionMap_f' _ _ hk]
    simp only [comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  · exact (zero_below K (by omega)).eq_of_src _ _

end Gen

def TruncData' : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  ∃ (P : ℕ) (K' L' : Cx R) (f' : K' ⟶ L') (g : K' ⟶ K) (h : L' ⟶ L),
    (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K'.X i) ∧ IsZero (L'.X i)) ∧ f' ≫ h = g ≫ f ∧
    (∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p) ∧ IsIso (h.f p)) ∧
    (∀ p : ℤ, p < -(n + 1) → IsZero (K'.X p) ∧ IsZero (L'.X p))

theorem truncData' : TruncData' := by
  intro R _ K L f n hz
  refine ⟨(n + 1).toNat, sT K (-(n + 1)), sT L (-(n + 1)), sTMap f _, ιT K _, ιT L _, fun i hi => ?_, ιT_nat f _,
    fun p hp => ⟨isIso_ιT K hp, isIso_ιT L hp⟩, fun p hp => ⟨zero_below K hp, zero_below L hp⟩⟩
  by_cases h : -(n + 1) ≤ i
  · have hi' : 0 < i := by omega
    have := isIso_ιT K h
    have := isIso_ιT L h
    exact ⟨(hz i hi').1.of_iso (asIso ((ιT K _).f i)), (hz i hi').2.of_iso (asIso ((ιT L _).f i))⟩
  · exact ⟨zero_below K (by omega), zero_below L (by omega)⟩

variable (R : Type) [CommRing R] (F : Shv R)

theorem relK_of_square' {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L') (g : K' ⟶ K) (h : L' ⟶ L)
    (w : f' ≫ h = g ≫ f) (n : ℤ)
    (hg : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R g F m))
    (hh : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R h F m))
    (hf' : RelK R F n f') : RelK R F n f := by
  have key : ∀ (m : ℤ) (z : HK R L F m),
      HK.pull R f' F m (HK.pull R h F m z) = HK.pull R g F m (HK.pull R f F m z) := by
    intro m z
    rw [← LateralTheory.E.TruncPf.pull_comp, ← LateralTheory.E.TruncPf.pull_comp, w]
  refine ⟨fun m hm y => ?_, fun x1 x2 hx => ?_⟩
  · obtain ⟨z', hz'⟩ := hf'.1 m hm (HK.pull R g F m y)
    obtain ⟨z, rfl⟩ := (hh m (by omega)).2 z'
    exact ⟨z, (hg m (by omega)).1 ((key m z).symm.trans hz')⟩
  · apply (hh n le_rfl).1
    apply hf'.2
    rw [key, key, hx]

theorem Trunc_of (hB : TruncBij) : LateralTheory.E.FiltPf.Trunc := by
  intro R _ F K L f n hz
  obtain ⟨P, K', L', f', g, h, hb, w, hiso, hzero⟩ := truncData' R f n hz
  refine ⟨P, K', L', f', hb, fun hp p => ?_, relK_of_square' R F f f' g h w n
    (hB R F g n fun q hq => (hiso q hq).1) (hB R F h n fun q hq => (hiso q hq).2)⟩
  by_cases hq : -(n + 1) ≤ -(p : ℤ)
  · have := (hiso _ hq).1
    have := (hiso _ hq).2
    refine relK_of_square R F (pieceC R f' p) (pieceC R f p)
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (g.f _))
      ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (h.f _)) ?_ n
      (fun m _ => pull_bij_of_iso R F _ m) (fun m _ => pull_bij_of_iso R F _ m) (hp p)
    simp only [pieceC, ← Functor.map_comp]
    congr 1
    have := congrArg (fun φ => HomologicalComplex.Hom.f φ (-(p : ℤ))) w
    simp only [HomologicalComplex.comp_f] at this
    exact this.symm
  · exact relK_of_isZero R F _ n
      (Functor.map_isZero _ (hzero _ (by omega)).1) (Functor.map_isZero _ (hzero _ (by omega)).2)

end LateralTheory.E.TruncationInclusionIso
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LZARStepOf
namespace LateralTheory.E.LZARFacts

theorem LZARStep_of : LateralTheory.E.LZIdemSumNoetherian.LZARStep := by
  intro A _ _ _ M _ _ N P hN
  have : Module.Finite A N := Module.Finite.iff_fg.mpr hN
  set I := IsLocalRing.maximalIdeal A
  set Q : Submodule A N := P.comap N.subtype
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I Q
  refine ⟨c + 1, by omega, ?_⟩
  have hQ : I ^ (c + 1) • (⊤ : Submodule A N) ⊓ Q ≤ I • Q := by
    rw [hc (c + 1) (by omega), show c + 1 - c = 1 by omega, pow_one]
    exact Submodule.smul_mono (le_refl _) inf_le_right
  intro x ⟨hx, hxP⟩
  have hmap : I ^ (c + 1) • N = (I ^ (c + 1) • (⊤ : Submodule A N)).map N.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [hmap] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyQ : y ∈ Q := hxP
  have := hQ ⟨hy, hyQ⟩
  have h2 : (I • Q).map N.subtype ≤ I • P := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono (le_refl _) (Submodule.map_comap_le _ _)
  exact h2 ⟨y, this, rfl⟩

end LateralTheory.E.LZARFacts
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LocPowPf
noncomputable section
open Polynomial IsLocalRing

namespace LateralTheory.E.LocPowPf

theorem pow_eq_one_of_aeval {q : ℕ} {A : Type} [CommRing A] (ξ : A) (h : aeval ξ (cyclotomic q ℤ) = 0) : ξ ^ q = 1 := by
  obtain ⟨p, hp⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval ξ) hp
  rw [map_mul, h, zero_mul, map_sub, map_pow, aeval_X, map_one] at this
  exact sub_eq_zero.1 this

theorem prim_res {q : ℕ} {A : Type} [CommRing A] [IsLocalRing A] (ξ : GlobalTheory.EtC.Prim q A) :
    IsPrimitiveRoot (residue A ξ.1) q := by
  have hu : IsUnit ((q : ResidueField A)) := by simpa using ξ.2.1.map (residue A)
  have : NeZero (q : ResidueField A) := ⟨hu.ne_zero⟩
  obtain ⟨x, -, hx⟩ := ξ
  change IsPrimitiveRoot (residue A x) q
  rw [← isRoot_cyclotomic_iff, IsRoot, ← map_cyclotomic_int, eval_map]
  change aeval ((residue A).toIntAlgHom x) (cyclotomic q ℤ) = 0
  rw [aeval_algHom_apply, hx, map_zero]

theorem LocPow_of : LateralTheory.E.AugBijPf.LocPow := by
  intro q A _ _ ξ ζ
  have hq : IsUnit (q : A) := ξ.2.1
  have hz := prim_res ζ
  have hx := prim_res ξ
  have : NeZero q := ⟨by rintro rfl; simp at hq⟩
  obtain ⟨i, hi, he⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hcop : i.Coprime q := (hz.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (he ▸ hx)
  refine ⟨ZMod.unitOfCoprime i hcop, ?_⟩
  have hval : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
    simp [ZMod.unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  rw [hval]
  set η := ζ.1 ^ i with hη
  have h1 : ξ.1 ^ q = 1 := pow_eq_one_of_aeval ξ.1 ξ.2.2
  have h2 : η ^ q = 1 := by rw [hη, ← pow_mul, mul_comm, pow_mul, pow_eq_one_of_aeval ζ.1 ζ.2.2, one_pow]
  have hres : residue A ξ.1 = residue A η := by rw [hη, map_pow]; exact he.symm
  have hηu : residue A η ≠ 0 := hres ▸ hx.ne_zero (NeZero.ne q)
  have hS : IsUnit (∑ j ∈ Finset.range q, ξ.1 ^ j * η ^ (q - 1 - j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_mul, map_pow, hres]
    rw [geom_sum₂_self]
    exact mul_ne_zero (by simpa using (hq.map (residue A)).ne_zero) (pow_ne_zero _ hηu)
  have key := (Commute.all ξ.1 η).geom_sum₂_mul q
  rw [h1, h2, sub_self] at key
  exact sub_eq_zero.1 ((hS.mul_right_eq_zero).1 key)

end LateralTheory.E.LocPowPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.FlatMonoLimPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.FlatMonoLimPf

theorem exists_lift {X Y T : Scheme.{0}} (m : X ⟶ Y) [Mono m] [Flat m] [QuasiCompact m] (t : T ⟶ Y)
    (h : Set.range t ⊆ Set.range m) : ∃ b : T ⟶ X, b ≫ m = t := by
  have hs : Surjective (pullback.fst t m) := by
    constructor
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst]
    exact Set.eq_univ_of_forall fun x => h ⟨x, rfl⟩
  have : IsIso (pullback.fst t m) := Flat.isIso_of_surjective_of_mono _
  refine ⟨inv (pullback.fst t m) ≫ pullback.snd t m, ?_⟩
  rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

theorem FlatMonoLim_of : LateralTheory.E.NbIsoPf.FlatMonoLim := by
  intro Y J _ _ D ι hι hc X m hm hf hq hr c hl
  have ho : ∀ j, IsOpenImmersion (ι j) := fun j => (hι j).1
  have hsub : ∀ j, Set.range m ⊆ Set.range (ι j) := fun j => hr ▸ Set.iInter_subset _ j
  have hind : ∀ j k, c.π.app j ≫ ι j = c.π.app k ≫ ι k := by
    intro j k
    rw [← c.w (IsCofiltered.minToLeft j k), ← c.w (IsCofiltered.minToRight j k), Category.assoc, Category.assoc,
      hc, hc]
  obtain ⟨j0⟩ : Nonempty J := IsCofiltered.nonempty
  have hp : Set.range (c.π.app j0 ≫ ι j0) ⊆ Set.range m := by
    rw [hr]
    refine Set.subset_iInter fun j => ?_
    rw [hind j0 j]
    rintro _ ⟨x, rfl⟩
    exact ⟨c.π.app j x, (Scheme.Hom.comp_apply _ _ _).symm⟩
  obtain ⟨b, hb⟩ := exists_lift m _ hp
  let s : Cone D :=
    { pt := X
      π :=
        { app := fun j => IsOpenImmersion.lift (ι j) m (hsub j)
          naturality := fun j k f => by
            rw [← cancel_mono (ι k)]
            simp [hc] } }
  have hs : ∀ j, hl.lift s ≫ c.π.app j ≫ ι j = m := by
    intro j
    rw [hl.fac_assoc]
    exact IsOpenImmersion.lift_fac _ _ _
  refine ⟨⟨b, hl.lift s, ?_, ?_⟩⟩
  · refine hl.hom_ext fun j => ?_
    rw [← cancel_mono (ι j)]
    simp only [Category.assoc]
    erw [hs j, hb, Category.id_comp]
    exact hind j0 j
  · rw [← cancel_mono m, Category.assoc, hb, hs, Category.id_comp]

end LateralTheory.E.FlatMonoLimPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafStalkSmoothClosedPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 Order

namespace LateralTheory.E.LeafStalkSmoothClosedPf

theorem coheight_le_topDim {X : Scheme.{0}} (x : X) :
    (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let := specializationOrder X
  have h := coheight_le_krullDim
    (irreducibleSetEquivPoints.symm x : TopologicalSpace.IrreducibleCloseds X)
  rwa [coheight_orderIso] at h

theorem stalk_not_isField {X : Scheme.{0}} [IsIntegral X] (y : X) (hy : y ≠ genericPoint X) :
    ¬ IsField (X.presheaf.stalk y) := by
  intro hF
  let := hF.toField
  have h0 : ringKrullDim (X.presheaf.stalk y) = 0 := ringKrullDim_eq_zero_of_field _
  rw [ringKrullDim_stalk_eq_coheight] at h0
  have hc : coheight y = 0 := by exact_mod_cast h0
  rw [coheight_eq_zero] at hc
  have h1 : y ≤ genericPoint X := genericPoint_specializes y
  have h2 : genericPoint X ≤ y := hc h1
  exact hy (Specializes.antisymm (h2 : y ⤳ genericPoint X) (h1 : genericPoint X ⤳ y)).eq

theorem stalk_dvr {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (y : X)
    (hn : IsIntegrallyClosed (X.presheaf.stalk y)) (hd : topologicalKrullDim X = 1)
    (hy : y ≠ genericPoint X) : IsDiscreteValuationRing (X.presheaf.stalk y) := by
  have hc : coheight y ≤ 1 := by
    have := (coheight_le_topDim y).trans hd.le
    exact_mod_cast this
  have : Ring.KrullDimLE 1 (X.presheaf.stalk y) := krullDimLE_of_coheight_le hc
  have : Ring.DimensionLEOne (X.presheaf.stalk y) :=
    ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩
  have : IsDedekindDomain (X.presheaf.stalk y) := {}
  exact ((IsDiscreteValuationRing.TFAE _ (stalk_not_isField y hy)).out 3 1).mp this

set_option backward.isDefEq.respectTransparency false in
theorem LeafStalkSmoothClosed_of : LateralTheory.E.LeafSmoothOfNormalPf.LeafStalkSmoothClosed := by
  intro Ω _ _ C c _ hc hn hd y hy
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  have := hn y
  have : IsDiscreteValuationRing (C.presheaf.stalk y) := stalk_dvr y (hn y) hd hy
  have hE := LocallyOfFiniteType.stalkMap c y
  algebraize [(c.stalkMap y).hom]
  let p : Spec (CommRingCat.of Ω) := c y
  let K' := (Spec.structureSheaf Ω).presheaf.stalk p
  let e : Ω ≃ₐ[Ω] K' := IsLocalization.atUnits _ p.asIdeal.primeCompl
      (fun x hx ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic Ω K' := .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField Ω)).toField
  let : Field ((Sp Ω).presheaf.stalk (c y)) := this
  have : PerfectField ((Sp Ω).presheaf.stalk (c y)) :=
    Algebra.IsAlgebraic.perfectField (K := Ω) (L := (Spec.structureSheaf Ω).presheaf.stalk p)
  exact GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField _ _

end LateralTheory.E.LeafStalkSmoothClosedPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafVanVPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafVanVPf

theorem free_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] : IsZero ((free R).obj (yoneda.obj X)) := by
  have key : ∀ (F : Shv R) (f g : (freeP R).obj (yoneda.obj X) ⟶ F.obj), f = g := by
    intro F f g
    ext1
    funext U
    by_cases hU : IsEmpty U.unop
    · have hb : ⊥ ∈ Scheme.etaleTopology U.unop := Scheme.bot_mem_grothendieckTopology _
      exact (Sheaf.isTerminalOfBotCover F U.unop hb).hom_ext _ _
    · apply ModuleCat.free_hom_ext
      rintro ⟨x⟩
      exfalso
      apply hU
      exact ⟨fun u => IsEmpty.false ((show U.unop ⟶ X from x) u)⟩
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective
  exact key _ _ _

theorem chains_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] (n : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X n) := by
  by_cases h : n ≤ 0
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
    exact (free_empty R X).of_iso (chainsXIso R _ p)
  · refine HomologicalComplex.isZero_extend_X ((chainsN R).obj (sch.obj X)) ComplexShape.embeddingDownNat n ?_
    intro i hi
    change -(i : ℤ) = n at hi
    omega

theorem isIso_inr {C : Type*} [Category C] [Abelian C] {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (h : ∀ n, IsZero (K.X n)) : IsIso (mappingCone.inr φ) := by
  have : ∀ n, IsIso ((mappingCone.inr φ).f n) := fun n =>
    ⟨(mappingCone.snd φ).v n n (add_zero n), by simp, by
      rw [← mappingCone.id_X φ n (n + 1) rfl, (h (n + 1)).eq_of_tgt ((mappingCone.fst φ).1.v n (n + 1) rfl) 0]
      simp⟩
  exact HomologicalComplex.Hom.isIso_of_components _

theorem subsingleton_of_iso {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) [IsIso f] (F : Shv R) (m : ℤ)
    (h : Subsingleton (HK R K F m)) : Subsingleton (HK R L F m) := by
  have key : ∀ x : HK R L F m, HK.pull R (inv f) F m (HK.pull R f F m x) = x := by
    intro x
    obtain ⟨x, rfl⟩ := x.mk_surjective
    refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
    simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, IsIso.inv_hom_id, Cochain.id_comp]
  exact ⟨fun x y => by rw [← key x, ← key y, Subsingleton.elim (HK.pull R f F m x) (HK.pull R f F m y)]⟩

theorem LeafVanV_of : LateralTheory.E.LeafVan0Pf.LeafVanV := by
  intro _ q _ i B W Y S ι p s hs m hm
  have he : IsEmpty ↥(pullback (pullback.snd p s ≫ s) ι : Scheme.{0}) := ⟨fun z => by
    refine hs (pullback.snd p s (pullback.fst (pullback.snd p s ≫ s) ι z)) ⟨pullback.snd (pullback.snd p s ≫ s) ι z, ?_⟩
    have hc := congrArg (fun f => f z) (pullback.condition (f := pullback.snd p s ≫ s) (g := ι))
    simpa using hc.symm⟩
  have := isIso_inr ((chains (ZMod q)).map (sch.map (LateralTheory.E.LeafVan0Pf.prS p ι s))) (chains_empty _ _)
  exact subsingleton_of_iso (mappingCone.inr _) _ m hm

end LateralTheory.E.LeafVanVPf
end
end
