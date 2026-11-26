module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveEtaleSectionBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveEtaleSectionBaseChange
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem yoneda_map_isLocallySurjective_of_etale_surjective (Y X : Scheme.{0}) (f : Y ⟶ X)
    (hf : Etale f) (hs : Surjective f) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f) where
  imageSieve_mem {U} s := by
    refine Scheme.mem_grothendieckTopology_iff.2 ⟨Scheme.Cover.mkOfCovers PUnit (fun _ => pullback f s) (fun _ => pullback.snd f s)
      (fun x => ?_) (fun _ => inferInstance), ?_⟩
    · obtain ⟨y, hy⟩ := (inferInstance : Surjective (pullback.snd f s)).surj x
      exact ⟨⟨⟩, y, hy⟩
    · rintro V g ⟨j⟩
      exact ⟨pullback.fst f s, by simp; exact pullback.condition⟩

theorem isLocallySurjective_of_section {P Q : PSh} (f : P ⟶ Q) (s : Q ⟶ P) (h : s ≫ f = 𝟙 Q) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f :=
  Presheaf.isLocallySurjective_of_surjective _ f fun U q =>
    ⟨s.app U q, by simpa using ConcreteCategory.congr_hom (NatTrans.congr_app h U) q⟩

theorem isLocallySurjective_of_isPullback {P Q P' Q' : PSh} (a : P' ⟶ P) (f' : P' ⟶ Q')
    (f : P ⟶ Q) (b : Q' ⟶ Q) (hpb : IsPullback a f' f b)
    (hf : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f) :
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f' where
  imageSieve_mem {U} y := by
    refine Scheme.etaleTopology.superset_covering ?_ (Presheaf.imageSieve_mem _ f (b.app _ y))
    rintro V i ⟨t, ht⟩
    have hV := hpb.map ((evaluation _ _).obj (op V))
    obtain ⟨x, hx1, hx2⟩ := Types.exists_of_isPullback hV t (Q'.map i.op y)
      (by simpa [NatTrans.naturality_apply] using ht)
    exact ⟨x, hx2⟩

theorem locallySurjective_etale_section_baseChange :
    (∀ (Y X : Scheme.{0}) (f : Y ⟶ X), Etale f → Surjective f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f)) ∧ (∀ (P Q : PSh) (f : P ⟶ Q) (s : Q ⟶ P), s ≫ f = 𝟙 Q → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f) ∧ ∀ (P Q P' Q' : PSh) (a : P' ⟶ P) (f' : P' ⟶ Q') (f : P ⟶ Q) (b : Q' ⟶ Q), IsPullback a f' f b → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f' :=
  ⟨yoneda_map_isLocallySurjective_of_etale_surjective,
   fun _ _ f s h => isLocallySurjective_of_section f s h,
   fun _ _ _ _ a f' f b h hf => isLocallySurjective_of_isPullback a f' f b h hf⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveEtaleSectionBaseChangeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallySurjective_etale_baseChange : (∀ (Y X : Scheme.{0}) (f : Y ⟶ X), Etale f → Surjective f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (yoneda.map f)) ∧ (∀ (P Q : PSh) (f : P ⟶ Q) (s : Q ⟶ P), s ≫ f = 𝟙 Q → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f) ∧ ∀ (P Q P' Q' : PSh) (a : P' ⟶ P) (f' : P' ⟶ Q') (f : P ⟶ Q) (b : Q' ⟶ Q), IsPullback a f' f b → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f → Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f' := by
  first | (exact @GlobalTheory.EtC.locallySurjective_etale_section_baseChange) | (exact GlobalTheory.EtC.locallySurjective_etale_section_baseChange) | (intros; apply GlobalTheory.EtC.locallySurjective_etale_section_baseChange  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantApply
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GalSec

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

abbrev LCRing (k : ℕ) : Type := LocallyConstant (Fin k → (Ω ≃ₐ[K] Ω)) Ω

theorem isLocallyConstant_apply [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin k) (a : Ω) :
    IsLocallyConstant (fun g : Fin k → (Ω ≃ₐ[K] Ω) => g i a) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  have hfd : FiniteDimensional K (IntermediateField.adjoin K {a}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  have hopen : IsOpen {σ : Ω ≃ₐ[K] Ω | (g₀ i)⁻¹ * σ ∈ (IntermediateField.adjoin K {a}).fixingSubgroup} :=
    (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const.mul continuous_id)
  have hmem : ∀ᶠ g in nhds g₀, g i ∈ {σ : Ω ≃ₐ[K] Ω | (g₀ i)⁻¹ * σ ∈ (IntermediateField.adjoin K {a}).fixingSubgroup} :=
    ((continuous_apply i).tendsto g₀).eventually (hopen.mem_nhds (by simp [one_mem]))
  filter_upwards [hmem] with g hg
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg a (IntermediateField.mem_adjoin_simple_self K a)
  have h2 := congrArg (g₀ i) h1
  simpa [AlgEquiv.mul_apply] using h2

def coord [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin k) : Ω →+* LCRing K Ω k where
  toFun a := ⟨fun g => g i a, isLocallyConstant_apply K Ω k i a⟩
  map_one' := LocallyConstant.ext fun g => by simp
  map_mul' a b := LocallyConstant.ext fun g => by simp
  map_zero' := LocallyConstant.ext fun g => by simp
  map_add' a b := LocallyConstant.ext fun g => by simp

@[simp] theorem coord_apply [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin k) (a : Ω) (g : Fin k → (Ω ≃ₐ[K] Ω)) :
    coord K Ω k i a g = g i a := rfl

def legHom [Algebra.IsAlgebraic K Ω] (k : ℕ) : Fin (k + 1) → (Ω →+* LCRing K Ω k) :=
  Fin.cases LocallyConstant.constRingHom (coord K Ω k)

def baseHom (k : ℕ) : K →+* LCRing K Ω k := LocallyConstant.constRingHom.comp (algebraMap K Ω)

theorem legHom_comp [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin (k + 1)) :
    (legHom K Ω k i).comp (algebraMap K Ω) = baseHom K Ω k := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · ext c g
    simp [legHom, baseHom]

def tailG (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) : Fin k → (Ω ≃ₐ[K] Ω) := fun i => (σ 0)⁻¹ * σ i.succ

def ptHom (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) : LCRing K Ω k →+* Ω :=
  ((σ 0 : Ω ≃ₐ[K] Ω) : Ω →+* Ω).comp (LocallyConstant.evalRingHom (tailG K Ω k σ))

theorem ptHom_legHom [Algebra.IsAlgebraic K Ω] (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) (i : Fin (k + 1)) :
    (ptHom K Ω k σ).comp (legHom K Ω k i) = ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · ext a; simp [ptHom, legHom]
  · ext a; simp [ptHom, legHom, tailG, AlgEquiv.mul_apply]

end GlobalTheory.EtC.GalSec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceSimplicesOverSubComposite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceSimplicesOverSubComposite
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SubSub

theorem hom_ext_val' {a b : ℕ} (f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (h : ∀ v : Fin (a + 1), ((f.toOrderHom v : Fin (b + 1)) : ℕ) = (g.toOrderHom v : Fin (b + 1))) : f = g :=
  SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun v => Fin.ext (h v)))

theorem along_along' {E : Spc} {U : Scheme.{0}} {N p r : ℕ} (x : Sx E N U) (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N)
    (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p) : (x.along a).along b = x.along (b ≫ a) := by
  unfold Sx.along
  rw [op_comp, E.map_comp]
  rfl

theorem sub_eq_along {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    x.sub j l h = x.along (SimplexCategory.subinterval j l h) := rfl

theorem res_along {E : Spc} {U V : Scheme.{0}} {N p : ℕ} (x : Sx E N U) (g : V ⟶ U)
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.res g).along a = (x.along a).res g := by
  unfold Sx.along Sx.res
  have h1 := congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) ((E.map a.op).naturality g.op)) x
  simpa only [ConcreteCategory.comp_apply] using h1

theorem map_along {E E' : Spc} {U : Scheme.{0}} {N p : ℕ} (x : Sx E N U) (f : E ⟶ E')
    (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : (x.map f).along a = (x.along a).map f := by
  unfold Sx.along Sx.map
  have := f.naturality a.op
  have h2 := congrArg (fun φ => φ.app (op U)) this
  simp only [NatTrans.comp_app] at h2
  exact (congrFun (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)) h2) x).symm

theorem main : ∀ {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U), (∀ (j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l), (x.sub j l h).sub j' l' h' = x.sub (j + j') l' (by omega)) ∧ x.sub 0 N (by omega) = x ∧ (∀ (j l : ℕ) (h : j + l ≤ N), (∀ {V : Scheme.{0}} (g : V ⟶ U), (x.res g).sub j l h = (x.sub j l h).res g) ∧ (∀ {E' : Spc} (f : E ⟶ E'), (x.map f).sub j l h = (x.sub j l h).map f) ∧ x.sub j l h = x.along (SimplexCategory.subinterval j l h)) ∧ ∀ {p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p), (x.along a).along b = x.along (b ≫ a) := by
  intro E U N x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j l j' l' h h'
    rw [sub_eq_along, sub_eq_along, sub_eq_along, along_along']
    congr 1
    exact hom_ext_val' _ _ fun v => by
      show ((v : ℕ) + j') + j = v + (j + j')
      omega
  · have : SimplexCategory.subinterval (n := N) 0 N (by omega) = 𝟙 _ :=
      hom_ext_val' _ _ fun v => by
        show (v : ℕ) + 0 = v
        omega
    rw [sub_eq_along, this]
    unfold Sx.along
    simp
  · intro j l h
    refine ⟨fun g => res_along x g _, fun f => map_along x f _, rfl⟩
  · intro p r a b
    exact along_along' x a b

end GlobalTheory.EtC.SubSub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceSimplicesOverSubCompositeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite : ∀ {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U), (∀ (j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l), (x.sub j l h).sub j' l' h' = x.sub (j + j') l' (by omega)) ∧ x.sub 0 N (by omega) = x ∧ (∀ (j l : ℕ) (h : j + l ≤ N), (∀ {V : Scheme.{0}} (g : V ⟶ U), (x.res g).sub j l h = (x.sub j l h).res g) ∧ (∀ {E' : Spc} (f : E ⟶ E'), (x.map f).sub j l h = (x.sub j l h).map f) ∧ x.sub j l h = x.along (SimplexCategory.subinterval j l h)) ∧ ∀ {p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p), (x.along a).along b = x.along (b ≫ a) := by
  first | (exact @GlobalTheory.EtC.SubSub.main) | (exact GlobalTheory.EtC.SubSub.main) | (intros; apply GlobalTheory.EtC.SubSub.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency false in
instance instWEqLBEtRings (R : Type) [CommRing R] : (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _


set_option backward.isDefEq.respectTransparency false in
theorem etale_affine_of_mem {U : Scheme.{0}} {S : Sieve U} (hS : S ∈ Scheme.etaleTopology U) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ S j := by
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  have : Scheme.JointlySurjective (Scheme.precoverage.{0} @Etale) :=
    Scheme.instJointlySurjectivePrecoverage
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
  obtain ⟨k, w, hw⟩ := (𝒰.X i).affineCover.exists_eq y
  have hi : S (𝒰.f i) := hle _ _ (Presieve.ofArrows.mk i)
  have he : Etale (𝒰.f i) := 𝒰.map_prop i
  refine ⟨_, (𝒰.X i).affineCover.f k ≫ 𝒰.f i, w, inferInstance, inferInstance, ?_, S.downward_closed hi _⟩
  rw [Scheme.Hom.comp_apply, hw, hy]

set_option backward.isDefEq.respectTransparency false in
theorem ofRings_loc : ∀ (R : Type) [CommRing R]
    (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}),
    (∀ (x : Sec (ofRings R M) U) (u : U),
      ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (m : M.obj Γ(V, ⊤)),
        IsAffine V ∧ Etale j ∧ j v = u ∧ ofRings.sec M V m = Sec.res j x) ∧
    (∀ m : M.obj Γ(U, ⊤), ofRings.sec M U m = 0 → ∀ u : U,
      ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V),
        IsAffine V ∧ Etale j ∧ j v = u ∧ (M.map j.appTop).hom m = 0) ∧
    ∀ (V : Scheme.{0}) (j : V ⟶ U) (m : M.obj Γ(U, ⊤)),
      Sec.res j (ofRings.sec M U m) = ofRings.sec M V ((M.map j.appTop).hom m) := by
  intro R _ M U
  refine ⟨fun x u => ?_, fun m hm u => ?_, fun V j m => ?_⟩
  · have hS := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op U) x
    obtain ⟨V, j, v, hV, hj, hv, ⟨m, hm⟩⟩ := etale_affine_of_mem hS u
    exact ⟨V, j, v, m, hV, hj, hv, hm⟩
  · have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M))
      (X := op U) m 0 (hm.trans (map_zero _).symm)
    obtain ⟨V, j, v, hV, hj, hv, h⟩ := etale_affine_of_mem hS u
    refine ⟨V, j, v, hV, hj, hv, ?_⟩
    have h' : ((Scheme.Γ ⋙ M).map j.op).hom m = ((Scheme.Γ ⋙ M).map j.op).hom 0 := h
    rw [map_zero] at h'
    exact h'
  · have := congrArg (fun f => f.hom m) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op)
    exact this.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem _root_.GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}), (∀ (x : Sec (ofRings R M) U) (u : U), ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (m : M.obj Γ(V, ⊤)), IsAffine V ∧ Etale j ∧ j v = u ∧ ofRings.sec M V m = Sec.res j x) ∧ (∀ m : M.obj Γ(U, ⊤), ofRings.sec M U m = 0 → ∀ u : U, ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ (M.map j.appTop).hom m = 0) ∧ ∀ (V : Scheme.{0}) (j : V ⟶ U) (m : M.obj Γ(U, ⊤)), Sec.res j (ofRings.sec M U m) = ofRings.sec M V ((M.map j.appTop).hom m) := by
  intro R _ M U
  refine ⟨fun x u => ?_, fun m hm u => ?_, fun V j m => ?_⟩
  · have hS := Presheaf.imageSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op U) x
    obtain ⟨V, j, v, hV, hj, hv, ⟨m, hm⟩⟩ := GlobalTheory.etale_affine_of_mem hS u
    exact ⟨V, j, v, m, hV, hj, hv, hm⟩
  · have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (X := op U) m 0
      (hm.trans (map_zero _).symm)
    obtain ⟨V, j, v, hV, hj, hv, h⟩ := GlobalTheory.etale_affine_of_mem hS u
    refine ⟨V, j, v, hV, hj, hv, ?_⟩
    have h' : ((Scheme.Γ ⋙ M).map j.op).hom m = ((Scheme.Γ ⋙ M).map j.op).hom 0 := h
    rw [map_zero] at h'
    exact h'
  · have h := congrArg (fun f => f.hom m)
      ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op)
    exact h.symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HCXBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HCXBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.HCTerms

variable (R : Type) [CommRing R]

theorem chainsXIso_inv_map {E E' : Spc} (f : E ⟶ E') (k : ℕ) :
    (chainsXIso R E k).inv ≫ ((chains R).map f).f (-(k : ℤ)) =
      (free R).map (f.app (op (SimplexCategory.mk k))) ≫ (chainsXIso R E' k).inv := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := k) (i' := -(k : ℤ)) rfl
  change (chainsXIso R E k).inv ≫ (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(k : ℤ)) = _
  rw [h]
  erw [Iso.inv_hom_id_assoc]
  rfl

theorem isZero_chains_X (E : Spc) (p : ℤ) (hp : 0 < p) : IsZero (((chains R).obj E).X p) := by
  apply HomologicalComplex.isZero_extend_X
  intro i h
  change -(i : ℤ) = p at h
  omega

def termEval (F : Shv R) (n : ℤ) (k : ℕ) :
    (HC R F ⋙ HomologicalComplex.eval _ _ n) ⟶ ((evaluation _ PSh).obj (op (SimplexCategory.mk k))).op ⋙ (free R).op ⋙
      preadditiveYoneda.obj ((res R F).X (n - k)) where
  app E := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun β : Cochain ((chains R).obj E.unop) (res R F) n => (chainsXIso R E.unop k).inv ≫ β.v (-(k : ℤ)) (n - k) (by omega))
    (fun a b => by simp only [Cochain.add_v, Preadditive.comp_add]; rfl))
  naturality E E' f := by
    ext β
    revert β
    change ∀ β : Cochain ((chains R).obj E.unop) (res R F) n,
      (chainsXIso R E'.unop k).inv ≫ ((Cochain.ofHom ((chains R).map f.unop)).comp β (zero_add n)).v (-(k : ℤ)) (n - k) (by omega) =
      (free R).map (f.unop.app (op (SimplexCategory.mk k))) ≫ (chainsXIso R E.unop k).inv ≫ β.v (-(k : ℤ)) (n - k) (by omega)
    intro β
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chainsXIso_inv_map, Category.assoc]

variable {R}

def blk {E : Spc} {F : Shv R} {n : ℤ} (g : ∀ k : ℕ, (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (res R F).X (n - k))
    (p q : ℤ) (m : ℕ) (h1 : p = -(m : ℤ)) (h2 : n - m = q) : ((chains R).obj E).X p ⟶ (res R F).X q :=
  (((chains R).obj E).XIsoOfEq h1).hom ≫ (chainsXIso R E m).hom ≫ g m ≫ ((res R F).XIsoOfEq h2).hom

theorem blk_eq {E : Spc} {F : Shv R} {n : ℤ} (g : ∀ k : ℕ, (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (res R F).X (n - k))
    (k m : ℕ) (hm : m = k) (h1 : -(k : ℤ) = -(m : ℤ)) (h2 : n - m = n - k) :
    blk g (-(k : ℤ)) (n - k) m h1 h2 = (chainsXIso R E k).hom ≫ g k := by
  subst hm
  simp [blk]

def ofFam {E : Spc} {F : Shv R} {n : ℤ} (g : ∀ k : ℕ, (free R).obj (E.obj (op (SimplexCategory.mk k))) ⟶ (res R F).X (n - k)) :
    Cochain ((chains R).obj E) (res R F) n :=
  Cochain.mk fun p q hpq => if hp : p ≤ 0 then blk g p q (-p).toNat (by omega) (by omega) else 0

theorem HC_X_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ), ∃ π : ∀ k : ℕ, (HC R F ⋙ HomologicalComplex.eval _ _ n) ⟶ ((evaluation _ PSh).obj (op (SimplexCategory.mk (k)))).op ⋙ (free R).op ⋙ preadditiveYoneda.obj ((res R F).X (n - k)), ∀ E : Spcᵒᵖ, Function.Bijective (fun (x : ((HC R F).obj E).X n) (k : ℕ) => (π k).app E x) := by
  intro R _ F n
  refine ⟨termEval R F n, fun E => ⟨fun x y hxy => ?_, fun g => ?_⟩⟩
  · revert x y
    change ∀ x y : Cochain ((chains R).obj E.unop) (res R F) n, _ → x = y
    intro x y hxy
    apply Cochain.ext
    intro p q hpq
    by_cases hp : 0 < p
    · exact (isZero_chains_X R E.unop p hp).eq_of_src _ _
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨p.natAbs, by omega⟩
      obtain rfl : q = n - k := by omega
      have h := congrFun hxy k
      change (chainsXIso R E.unop k).inv ≫ x.v (-(k : ℤ)) (n - k) _ = (chainsXIso R E.unop k).inv ≫ y.v (-(k : ℤ)) (n - k) _ at h
      exact (cancel_epi _).1 h
  · refine ⟨(ofFam (E := E.unop) g : Cochain ((chains R).obj E.unop) (res R F) n), funext fun k => ?_⟩
    change (chainsXIso R E.unop k).inv ≫ (ofFam g).v (-(k : ℤ)) (n - k) (by omega) = g k
    simp only [ofFam, Cochain.mk_v]
    rw [dite_eq_left (by omega), blk_eq g k _ (by omega)]
    erw [Iso.inv_hom_id_assoc]

end GlobalTheory.EtC.HCTerms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HCXBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_HC_component_eval_of_maps : ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ), ∃ π : ∀ k : ℕ, (HC R F ⋙ HomologicalComplex.eval _ _ n) ⟶ ((evaluation _ PSh).obj (op (SimplexCategory.mk (k)))).op ⋙ (free R).op ⋙ preadditiveYoneda.obj ((res R F).X (n - k)), ∀ E : Spcᵒᵖ, Function.Bijective (fun (x : ((HC R F).obj E).X n) (k : ℕ) => (π k).app E x) := by
  first | (exact @GlobalTheory.EtC.HCTerms.HC_X_bijective) | (exact GlobalTheory.EtC.HCTerms.HC_X_bijective) | (intros; apply GlobalTheory.EtC.HCTerms.HC_X_bijective  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeSeqExact
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeSeq

variable {R : Type} [CommRing R]

theorem cls_eq {K I : Cx R} {n : ℤ} (x y : Cocycle K I n) (m : ℤ) (hm : m + 1 = n) (β : Cochain K I m)
    (h : (x : Cochain K I n) = (y : Cochain K I n) + δ m n β) :
    CohomologyClass.mk x = CohomologyClass.mk y := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ m hm]
  exact ⟨β, by simp [h]⟩

end GlobalTheory.EtC.ConeSeq

theorem GlobalTheory.EtC.coneSeq_exact : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ), Function.Exact (cpull (mappingCone.inr f) I n) (cpull f I n) ∧ Function.Exact (cpull f I n) (cpre (mappingCone.fst f) I n (n + 1) (by omega)) ∧ Function.Exact (cpre (mappingCone.fst f) I n (n + 1) (by omega)) (cpull (mappingCone.inr f) I (n + 1)) := by
  intro R _ K L f I n
  refine ⟨?_, ?_, ?_⟩
  · intro y
    constructor
    · intro hb
      obtain ⟨b, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ b _) = 0 at hb
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hb
      obtain ⟨β, hβ⟩ := hb
      refine ⟨CohomologyClass.mk (mappingCone.descCocycle f (n.negOnePow • β) b (by omega) ?_), ?_⟩
      · rw [δ_units_smul, hβ]; simp [zcomp]
      · change CohomologyClass.mk (zcomp _ _ _) = _
        congr 1; ext1; simp [zcomp]
    · rintro ⟨z, rfl⟩
      obtain ⟨c, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ c _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
      refine ⟨n.negOnePow • (mappingCone.inl f).comp (c : Cochain _ I n) (by omega), ?_⟩
      rw [δ_units_smul, δ_comp _ _ _ 0 (n + 1) n (by omega) (by omega) rfl]
      simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, smul_smul]
  · intro y
    constructor
    · intro ha
      obtain ⟨a, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ a _) = 0 at ha
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)] at ha
      obtain ⟨γ, hγ⟩ := ha
      have hβ : δ n (n + 1) ((Cochain.ofHom (mappingCone.inr f)).comp γ (zero_add n)) = 0 := by
        rw [δ_ofHom_comp, hγ]; simp [zcomp]
      refine ⟨CohomologyClass.mk (Cocycle.mk (-(n.negOnePow • (Cochain.ofHom (mappingCone.inr f)).comp γ (zero_add n))) (n + 1) rfl (by rw [δ_neg, δ_units_smul, hβ]; simp)), ?_⟩
      change CohomologyClass.mk (zcomp _ _ _) = _
      refine ConeSeq.cls_eq _ _ (n - 1) (by omega) (-((mappingCone.inl f).comp γ (by omega))) ?_
      have key := δ_comp (mappingCone.inl f) γ (show -1 + n = n - 1 by omega) 0 (n + 1) n (by omega) (by omega) rfl
      rw [hγ] at key
      simp [zcomp] at key
      simp [zcomp, key, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
    · rintro ⟨z, rfl⟩
      obtain ⟨b, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ b _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)]
      refine ⟨-(n.negOnePow • (mappingCone.snd f).comp (b : Cochain _ I n) (zero_add n)), ?_⟩
      rw [δ_neg, δ_units_smul, δ_comp _ _ _ 1 (n + 1) (n + 1) rfl (zero_add 1) rfl]
      simp [zcomp, smul_smul, Cochain.comp_assoc_of_second_is_zero_cochain]
  · intro y
    constructor
    · intro hc
      obtain ⟨c, rfl⟩ := y.mk_surjective
      change CohomologyClass.mk (zcomp _ c _) = 0 at hc
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)] at hc
      obtain ⟨β, hβ⟩ := hc
      set a : Cochain K I n := (mappingCone.inl f).comp (c : Cochain _ I (n + 1)) (by omega) +
        n.negOnePow • (Cochain.ofHom f).comp β (zero_add n) with ha_def
      have hsnd := δ_comp (mappingCone.snd f) β (zero_add n) 1 (n + 1) (n + 1) rfl (zero_add 1) rfl
      rw [hβ] at hsnd
      simp [zcomp] at hsnd
      have hdec : (c : Cochain _ I (n + 1)) = (mappingCone.fst f).1.comp a (by omega) +
          δ n (n + 1) ((mappingCone.snd f).comp β (zero_add n)) := by
        rw [mappingCone.ext_cochain_from_iff f n (n + 1) rfl]
        constructor
        · simp [ha_def, hsnd, Cochain.comp_assoc_of_second_is_zero_cochain]
        · simp [ha_def, hsnd, Cochain.comp_assoc_of_second_is_zero_cochain]
      have hcoc : δ n (n + 1) a = 0 := by
        have h1 := congrArg (δ (n + 1) (n + 2)) hdec
        rw [δ_add, δ_δ, add_zero, Cocycle.δ_eq_zero c (n + 2)] at h1
        rw [δ_comp _ _ _ 2 (n + 1) (n + 2) (by omega) rfl rfl] at h1
        simp at h1
        have h2 := congrArg (fun x => (mappingCone.inl f).comp x (show -1 + (n + 2) = n + 1 by omega)) h1
        simpa using h2.symm
      refine ⟨CohomologyClass.mk (Cocycle.mk a (n + 1) rfl hcoc), ?_⟩
      change CohomologyClass.mk (zcomp _ _ _) = _
      refine ConeSeq.cls_eq _ _ n rfl (-((mappingCone.snd f).comp β (zero_add n))) ?_
      simp [zcomp, hdec]
    · rintro ⟨z, rfl⟩
      obtain ⟨a, rfl⟩ := z.mk_surjective
      change CohomologyClass.mk (zcomp _ (zcomp _ a _) _) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n (by omega)]
      exact ⟨0, by simp [zcomp]⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QConjTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexAutomorphismWeierstrassTorsionQCoeffs
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.CoeffConj

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private theorem vmul_dg_apply_zero_and_one {N : ℕ} (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ) :
    _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) 0 = x 0 ∧
      _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) 1 = (a : ZMod N) * x 1 := by
  simp [_root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private theorem ringEquiv_cG_eq (N : ℕ) (g : ℂ ≃+* ℂ) (k : ℕ) :
    g (_root_.GlobalTheory.WpFam.cG N k) = _root_.GlobalTheory.WpFam.cG N k := by
  unfold _root_.GlobalTheory.WpFam.cG
  split_ifs <;> simp [map_ofNat]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private theorem ringEquiv_cSum_eq_cSum_vmul_dg (N : ℕ) (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ)
    (hg : _root_.GlobalTheory.WpFam.ZetaAct g N a) (e : ℕ) (s : ℂ) (hs : g s = s) (x : Fin 2 → ZMod N)
    (k : ℕ) :
    g (_root_.GlobalTheory.WpFam.cSum N e s x k) =
      _root_.GlobalTheory.WpFam.cSum N e s (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
  obtain ⟨h0, h1⟩ := vmul_dg_apply_zero_and_one x a
  unfold _root_.GlobalTheory.WpFam.ZetaAct at hg
  unfold _root_.GlobalTheory.WpFam.cSum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [h0, h1]
  simp only [map_mul, map_pow, map_natCast, map_add (f := _), apply_ite g, map_zero, hs, hg]
  rw [mul_neg, mul_left_comm (a : ZMod N)]


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.CoeffConj.main : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.ZetaAct g N a → ∀ (x : Fin 2 → ZMod N) (k : ℕ), g (_root_.GlobalTheory.WpFam.cB N x k) = _root_.GlobalTheory.WpFam.cB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k ∧ g (_root_.GlobalTheory.WpFam.cD N x k) = _root_.GlobalTheory.WpFam.cD N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k ∧ g (_root_.GlobalTheory.WpFam.cG N k) = _root_.GlobalTheory.WpFam.cG N k ∧ g (_root_.GlobalTheory.WpFam.cP N x k) = _root_.GlobalTheory.WpFam.cP N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
  intro N _ g a hg x k
  obtain ⟨h0, h1⟩ := vmul_dg_apply_zero_and_one x a
  have hζ := hg
  unfold _root_.GlobalTheory.WpFam.ZetaAct at hζ
  have hG := ringEquiv_cG_eq N g k
  have hB : g (_root_.GlobalTheory.WpFam.cB N x k) =
      _root_.GlobalTheory.WpFam.cB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
    unfold _root_.GlobalTheory.WpFam.cB
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [if_true, h0, h1]
      split_ifs
      · simp only [map_div₀, map_pow, map_sub, map_one, hζ]
      · exact map_zero g
    · simp only [hk, if_false]
      exact ringEquiv_cSum_eq_cSum_vmul_dg N g a hg 1 1 (map_one g) x k
  have hD : g (_root_.GlobalTheory.WpFam.cD N x k) =
      _root_.GlobalTheory.WpFam.cD N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) k := by
    unfold _root_.GlobalTheory.WpFam.cD
    rcases eq_or_ne k 0 with rfl | hk
    · simp only [if_true, h0, h1]
      split_ifs
      · simp only [map_div₀, map_pow, map_sub, map_add (f := _), map_mul, map_one, hζ]
      · exact map_zero g
    · simp only [hk, if_false]
      exact ringEquiv_cSum_eq_cSum_vmul_dg N g a hg 2 (-1) (by simp) x k
  refine ⟨hB, hD, hG, ?_⟩
  have hzero := (_root_.GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x (_root_.GlobalTheory.WpFam.dg a)
  unfold _root_.GlobalTheory.WpFam.cP
  by_cases hx : x = 0
  · rw [if_pos hx, if_pos (hzero.2 hx), map_zero]
  · have hx' : _root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a) ≠ 0 := fun h => hx (hzero.1 h)
    simp only [hx, hx', if_false, map_sub, hB, hG]

end GlobalTheory.WpFam.CoeffConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QConjTorsion
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ConjExp


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.ConjExp.qConj_torsion : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), _root_.GlobalTheory.WpFam.ZetaAct g N a → ∀ x : Fin 2 → ZMod N, _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wp N x) (_root_.GlobalTheory.WpFam.wp N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a))) ∧ _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wpd N x) (_root_.GlobalTheory.WpFam.wpd N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a))) ∧ (x ≠ 0 → _root_.GlobalTheory.QFam.QConj g N (_root_.GlobalTheory.WpFam.wB N x) (_root_.GlobalTheory.WpFam.wB N (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)))) := by
  intro N _ g a hg x
  have hc := _root_.GlobalTheory.WpFam.CoeffConj.main N g a hg x
  refine ⟨⟨_, _root_.GlobalTheory.WpFam.ExpP.main N x, ?_⟩,
    ⟨_, _root_.GlobalTheory.WpFam.DerivExpansion.main N x, ?_⟩, fun hx => ⟨_,
      _root_.GlobalTheory.WpFam.ExpansionB.main N x hx, ?_⟩⟩
  · rw [show (fun n => g (_root_.GlobalTheory.WpFam.cP N x n)) = _root_.GlobalTheory.WpFam.cP N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).2.2.2]
    exact _root_.GlobalTheory.WpFam.ExpP.main N _
  · rw [show (fun n => g (_root_.GlobalTheory.WpFam.cD N x n)) = _root_.GlobalTheory.WpFam.cD N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).2.1]
    exact _root_.GlobalTheory.WpFam.DerivExpansion.main N _
  · have hzero := (_root_.GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x (_root_.GlobalTheory.WpFam.dg a)
    rw [show (fun n => g (_root_.GlobalTheory.WpFam.cB N x n)) = _root_.GlobalTheory.WpFam.cB N
      (_root_.GlobalTheory.WpFam.vmul x (_root_.GlobalTheory.WpFam.dg a)) from funext fun n => (hc n).1]
    exact _root_.GlobalTheory.WpFam.ExpansionB.main N _ fun h => hx (hzero.1 h)

end GlobalTheory.WpFam.ConjExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QConjTorsionStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qConj_torsion_points : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ), ZetaAct g N a → ∀ x : Fin 2 → ZMod N, QConj g N (wp N x) (wp N (vmul x (dg a))) ∧ QConj g N (wpd N x) (wpd N (vmul x (dg a))) ∧ (x ≠ 0 → QConj g N (wB N x) (wB N (vmul x (dg a)))) := by
  first | exact @GlobalTheory.WpFam.ConjExp.qConj_torsion | exact GlobalTheory.WpFam.ConjExp.qConj_torsion | (intros; apply GlobalTheory.WpFam.ConjExp.qConj_torsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsCechNerveQuasiIsoOfSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsQuasiIsoOfSections
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

theorem chains_quasiIso_of_sections : ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E'), (∀ U : Scheme.{0}, QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).map (((SimplicialObject.whiskering _ _).obj ((evaluation _ _).obj (op U) ⋙ uliftFunctor.{1} ⋙ ModuleCat.free (ULift.{1} R))).map f))) → QuasiIso ((chains R).map f) := by
  intro R _ E E' f hf
  let g := ((SimplicialObject.whiskering _ _).obj (freeP R)).map f
  let φ := (AlgebraicTopology.alternatingFaceMapComplex _).map g
  have hφ : QuasiIso φ := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro t
    have e := Arrow.isoOfNatIso (eqToIso (AlgebraicTopology.map_alternatingFaceMapComplex ((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj t))) (Arrow.mk g)
    exact (quasiIso_iff_of_arrow_mk_iso _ _ e).2 (hf t.unop)
  have e := Arrow.isoOfNatIso (eqToIso (AlgebraicTopology.map_alternatingFaceMapComplex (presheafToSheaf (Scheme.etaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R))))) (Arrow.mk g)
  have h2 : QuasiIso ((chainsN R).map f) := by
    have : QuasiIso (((presheafToSheaf (Scheme.etaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R))).mapHomologicalComplex _).map φ) := inferInstance
    exact (quasiIso_iff_of_arrow_mk_iso _ _ e).1 this
  change QuasiIso (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat)
  infer_instance

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsCechNerveQuasiIsoOfSurjective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
open Simplicial SimplicialObject.Augmented
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.EtC.CechSplit

variable {P Q : PSh} (φ : P ⟶ Q) (hφ : ∀ U, Function.Surjective (φ.app U)) (U : Scheme.{0})

def lft (c : yoneda.obj U ⟶ Q) : yoneda.obj U ⟶ P :=
  yonedaEquiv.symm (hφ (op U) (yonedaEquiv c)).choose

lemma lft_comp (c : yoneda.obj U ⟶ Q) : lft φ hφ U c ≫ φ = c := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, lft, Equiv.apply_symm_apply]
  exact (hφ (op U) (yonedaEquiv c)).choose_spec

def sf (n : ℕ) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n⦌)) :
    yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n + 1⦌) :=
  WidePullback.lift (x ≫ WidePullback.base _)
    (Fin.cases (lft φ hφ U (x ≫ WidePullback.base _)) (fun i => x ≫ WidePullback.π _ i))
    (fun i => by cases i using Fin.cases <;> simp [lft_comp])

def sf' (c : yoneda.obj U ⟶ Q) : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋0⦌) :=
  lft φ hφ U c ≫ WidePullback.lift φ (fun _ => 𝟙 P) (by simp)

lemma sf'_comp_aug (c : yoneda.obj U ⟶ Q) : sf' φ hφ U c ≫ (Arrow.mk φ).augmentedCechNerve.hom.app (op ⦋0⦌) = c := by
  simp [sf', lft_comp]

lemma sf_zero_comp_δ_one (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋0⦌)) :
    sf φ hφ U 0 x ≫ (Arrow.mk φ).cechNerve.δ 1 =
      sf' φ hφ U (x ≫ (Arrow.mk φ).augmentedCechNerve.hom.app (op ⦋0⦌)) := by
  dsimp [SimplicialObject.δ, SimplexCategory.δ, sf, sf']
  apply WidePullback.hom_ext
  · intro j
    fin_cases j
    simp
  · simp [lft_comp]

lemma sf_comp_δ_zero (n : ℕ) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n⦌)) :
    sf φ hφ U n x ≫ (Arrow.mk φ).cechNerve.δ 0 = x := by
  dsimp [SimplicialObject.δ, SimplexCategory.δ, sf]
  ext j
  · simp
  · simp

lemma sf_succ_comp_δ_succ (n : ℕ) (i : Fin (n + 2)) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n + 1⦌)) :
    sf φ hφ U (n + 1) x ≫ (Arrow.mk φ).cechNerve.δ i.succ = sf φ hφ U n (x ≫ (Arrow.mk φ).cechNerve.δ i) := by
  dsimp [SimplicialObject.δ, SimplexCategory.δ, sf]
  ext j
  · induction j using Fin.cases <;> simp
  · simp

lemma sf_comp_σ_succ (n : ℕ) (i : Fin (n + 1)) (x : yoneda.obj U ⟶ (Arrow.mk φ).cechNerve.obj (op ⦋n⦌)) :
    sf φ hφ U n x ≫ (Arrow.mk φ).cechNerve.σ i.succ = sf φ hφ U (n + 1) (x ≫ (Arrow.mk φ).cechNerve.σ i) := by
  dsimp [SimplicialObject.σ, SimplexCategory.σ, sf]
  ext j
  · induction j using Fin.cases <;> simp
  · simp

def ed : ExtraDegeneracy (((whiskering _ _).obj (coyoneda.obj (op (yoneda.obj U)))).obj
    (Arrow.mk φ).augmentedCechNerve) where
  s' := TypeCat.ofHom (sf' φ hφ U)
  s n := TypeCat.ofHom (sf φ hφ U n)
  s'_comp_ε := by ext c; exact sf'_comp_aug φ hφ U c
  s₀_comp_δ₁ := by ext x; exact sf_zero_comp_δ_one φ hφ U x
  s_comp_δ₀ n := by ext x; exact sf_comp_δ_zero φ hφ U n x
  s_comp_δ n i := by ext x; exact sf_succ_comp_δ_succ φ hφ U n i x
  s_comp_σ n i := by ext x; exact sf_comp_σ_succ φ hφ U n i x

def toConst : (Arrow.mk φ).augmentedCechNerve ⟶ SimplicialObject.Augmented.const.obj Q where
  left := (Arrow.mk φ).augmentedCechNerve.hom
  right := 𝟙 Q
  w := by ext : 1; simp

include hφ in
theorem free_sections_quasiIso (R : Type) [CommRing R] :
    QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).map
      (((SimplicialObject.whiskering _ _).obj ((evaluation _ _).obj (op U) ⋙ uliftFunctor.{1} ⋙
        ModuleCat.free (ULift.{1} R))).map
          (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from (Arrow.mk φ).augmentedCechNerve.hom))) := by
  let G : PSh ⥤ ModuleCat.{1} (ULift.{1} R) :=
    (evaluation _ _).obj (op U) ⋙ uliftFunctor.{1} ⋙ ModuleCat.free (ULift.{1} R)
  let X := (Arrow.mk φ).augmentedCechNerve
  let e1 : coyoneda.obj (op (yoneda.obj U)) ⋙ ModuleCat.free (ULift.{1} R) ≅ G :=
    Functor.isoWhiskerRight (largeCurriedYonedaLemma.app (op U)) (ModuleCat.free (ULift.{1} R))
  let ed0 : ExtraDegeneracy (((whiskering _ _).obj (coyoneda.obj (op (yoneda.obj U)) ⋙
      ModuleCat.free (ULift.{1} R))).obj X) := (ed φ hφ U).map (ModuleCat.free (ULift.{1} R))
  let ed1 : ExtraDegeneracy (((whiskering _ _).obj G).obj X) :=
    ed0.ofIso (((whiskering _ _).mapIso e1).app X)
  have h1 := ed1.homotopyEquiv.quasiIso_hom
  have h2 := ((ExtraDegeneracy.const Q).map G).homotopyEquiv.quasiIso_hom
  have nat := (AlgebraicTopology.AlternatingFaceMapComplex.ε (C := ModuleCat.{1} (ULift.{1} R))).naturality
    (((whiskering _ _).obj G).map (toConst φ))
  have hp : (point ⋙ ChainComplex.single₀ _).map (((whiskering _ _).obj G).map (toConst φ)) = 𝟙 _ := by
    change (ChainComplex.single₀ _).map (G.map (𝟙 Q)) = 𝟙 _
    rw [G.map_id, CategoryTheory.Functor.map_id]
  rw [hp, Category.comp_id] at nat
  haveI : QuasiIso (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
      (((whiskering _ _).obj G).obj (SimplicialObject.Augmented.const.obj Q))) := h2
  rw [← quasiIso_iff_comp_right _ (AlgebraicTopology.AlternatingFaceMapComplex.ε.app
    (((whiskering _ _).obj G).obj (SimplicialObject.Augmented.const.obj Q)))]
  have key : QuasiIso ((drop ⋙ AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).map
        (((whiskering _ _).obj G).map (toConst φ)) ≫
      AlgebraicTopology.AlternatingFaceMapComplex.ε.app
        (((whiskering _ _).obj G).obj (SimplicialObject.Augmented.const.obj Q))) := by
    rw [nat]; exact h1
  exact key

end GlobalTheory.EtC.CechSplit

namespace GlobalTheory.EtC

theorem chains_cechNerve_quasiIso_of_surjective : ∀ (R : Type) [CommRing R] {P Q : PSh} (φ : P ⟶ Q),
    (∀ U, Function.Surjective (φ.app U)) →
      QuasiIso ((chains R).map (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from
        (Arrow.mk φ).augmentedCechNerve.hom)) := by
  intro R _ P Q φ hφ
  exact chains_quasiIso_of_sections R _ (fun U => CechSplit.free_sections_quasiIso φ hφ U R)

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsCechNerveQuasiIsoOfSurjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiIso_chains_cechNerve_of_surjective : ∀ (R : Type) [CommRing R] {P Q : PSh} (φ : P ⟶ Q), (∀ U, Function.Surjective (φ.app U)) → QuasiIso ((chains R).map (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from (Arrow.mk φ).augmentedCechNerve.hom)) := by
  first | (exact @GlobalTheory.EtC.chains_cechNerve_quasiIso_of_surjective) | (exact GlobalTheory.EtC.chains_cechNerve_quasiIso_of_surjective) | (intros; apply GlobalTheory.EtC.chains_cechNerve_quasiIso_of_surjective  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFactorOfIndEt
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_etale_factor_of_indEt : ∀ (A O : Type) [CommRing A] [CommRing O] [Algebra A O], IndEt A O → ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] (φ : B →ₐ[A] O), ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.Etale A C) (ψ : B →ₐ[A] C) (χ : C →ₐ[A] O), χ.comp ψ = φ := by
  intro A O _ _ _ hO B _ _ _ φ
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := hO
  have hp : MorphismProperty.isFinitelyPresentable.{0} CommRingCat.{0}
      (CommRingCat.ofHom (algebraMap A B)) :=
    CommRingCat.isFinitelyPresentable_hom _ (RingHom.finitePresentation_algebraMap.2 inferInstance)
  obtain ⟨j, q, hq1, hq2⟩ := MorphismProperty.exists_hom_of_isFinitelyPresentable hs hp t
    (CommRingCat.ofHom φ.toRingHom) (fun j => by
      rw [(hst j).2]; ext a; simp)
  letI : Algebra A (D.obj j) := (t.app j).hom.toAlgebra
  haveI : Algebra.Etale A (D.obj j) := (hst j).1
  have h1 : ∀ a : A, q.hom (algebraMap A B a) = algebraMap A (D.obj j) a := fun a =>
    congrArg (fun f => f.hom a) hq1
  have h2 : ∀ a : A, (s.app j).hom (algebraMap A (D.obj j) a) = algebraMap A O a := fun a =>
    congrArg (fun f => f.hom a) (hst j).2
  have h3 : ∀ b : B, (s.app j).hom (q.hom b) = φ b := fun b =>
    congrArg (fun f => f.hom b) hq2
  refine ⟨D.obj j, inferInstance, inferInstance, inferInstance, ⟨q.hom, h1⟩, ⟨(s.app j).hom, h2⟩, ?_⟩
  ext b
  exact h3 b

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraMapEqOfFaithfullyFlatIncludeLeftEqI
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraMapEqOfFaithfullyFlatIncludeLeftEqI
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_algebraMap_eq_of_includeLeft_eq_includeRight :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] (b : B),
      (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) b =
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) b →
      ∃ a : A, algebraMap A B a = b := by
  intro A B _ _ _ _ b hb
  have h := Algebra.IsEffective.of_faithfullyFlat A B
  have h0 : Algebra.TensorProduct.includeLeftSubRight A B b = 0 := by
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
    simpa using hb
  obtain ⟨a, ha⟩ := (h b).mp h0
  exact ⟨a, by simpa using ha⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraMapEqOfFaithfullyFlatIncludeLeftEqIStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B] (b : B), (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) b = (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) b → ∃ a : A, algebraMap A B a = b := by
  first | (exact @GlobalTheory.EtC.exists_algebraMap_eq_of_includeLeft_eq_includeRight) | (exact GlobalTheory.EtC.exists_algebraMap_eq_of_includeLeft_eq_includeRight) | (intros; apply GlobalTheory.EtC.exists_algebraMap_eq_of_includeLeft_eq_includeRight  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiCofanIsColimitOfRingEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiCofanIsColimitOfRingEquiv
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem spec_pi_cofan_isColimit : ∀ (ι : Type) [Finite ι] (T : ι → Type) [∀ i, CommRing (T i)] (B : Type) [CommRing B] (e : B ≃+* (∀ i, T i)), Nonempty (IsColimit (Cofan.mk (Spec (CommRingCat.of B)) (fun i => Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))))) := by
  intro ι _ T _ B _ e
  let R : ι → CommRingCat := fun i => CommRingCat.of (T i)
  let eB : CommRingCat.of B ≅ CommRingCat.of (∀ i, T i) := e.toCommRingCatIso
  let φ : (∐ fun i => Spec (R i)) ≅ Spec (CommRingCat.of B) :=
    asIso (sigmaSpec R) ≪≫ Scheme.Spec.mapIso eB.op
  refine ⟨IsColimit.ofIsoColimit (coproductIsCoproduct _) (Cofan.ext φ ?_)⟩
  intro i
  simp only [φ, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.op_hom, Cofan.inj, Cofan.mk_ι_app]
  erw [ι_sigmaSpec_assoc]
  simp only [Scheme.Spec_map, Quiver.Hom.unop_op, ← Spec.map_comp]
  rfl

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecPiCofanIsColimitOfRingEquivStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_pi_cofan_isColimit_of_ringEquiv : ∀ (ι : Type) [Finite ι] (T : ι → Type) [∀ i, CommRing (T i)] (B : Type) [CommRing B] (e : B ≃+* (∀ i, T i)), Nonempty (IsColimit (Cofan.mk (Spec (CommRingCat.of B)) (fun i ↦ Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))))) := by
  first | exact @GlobalTheory.EtC.spec_pi_cofan_isColimit | exact GlobalTheory.EtC.spec_pi_cofan_isColimit | (intros; apply GlobalTheory.EtC.spec_pi_cofan_isColimit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeFieldStrictlyHenselian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeFieldStrictlyHenselian
open GlobalTheory.EtC

namespace GlobalTheory

theorem field_finiteType_algClosed_SH : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B], IsField B → SH B := by
  intro k B _ _ _ _ _ hB
  letI : Field B := hB.toField
  haveI : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
  have hbk : Function.Bijective (algebraMap k B) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsAlgClosed B := IsAlgClosed.of_ringEquiv k B
    (RingEquiv.ofBijective (algebraMap k B) hbk)
  refine ⟨Field.henselian B, ?_⟩
  have hbij : Function.Bijective (IsLocalRing.residue B) :=
    ⟨(IsLocalRing.residue B).injective, Ideal.Quotient.mk_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField B) :=
    IsAlgClosed.of_ringEquiv B _ (RingEquiv.ofBijective _ hbij)
  exact IsSepClosed.of_isAlgClosed _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeFieldStrictlyHenselianStatement
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B], IsField B → SH B := by
  first | (exact @GlobalTheory.field_finiteType_algClosed_SH) | (exact GlobalTheory.field_finiteType_algClosed_SH) | (intros; apply GlobalTheory.field_finiteType_algClosed_SH  <;> assumption)
end
end
