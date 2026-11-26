module

public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.CechLevels.CechLevelsOf
section -- merged from Development.EtaleCohomology.EtaleSheaves.CechLevels
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechLevelsPf
open PrimeSpectrum

theorem qm_comp {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) :
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map φ)).comp φ := Ideal.quotientMap_comp_mk _

theorem qm_integral {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) (h : φ.IsIntegral) :
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).IsIntegral := by
  apply RingHom.IsIntegral.tower_top (Ideal.Quotient.mk I)
  rw [qm_comp]
  exact RingHom.IsIntegral.trans _ _ h (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)

theorem qm_surj {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A)
    (hs : Function.Surjective (PrimeSpectrum.comap φ)) :
    Function.Surjective (PrimeSpectrum.comap (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) := by
  intro P
  obtain ⟨Q, hQ⟩ := hs (PrimeSpectrum.comap (Ideal.Quotient.mk I) P)
  have hmem : Q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I.map φ))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    show I.map φ ≤ Q.asIdeal
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have : x ∈ (PrimeSpectrum.comap φ Q).asIdeal := by
      rw [hQ]; show Ideal.Quotient.mk I x ∈ P.asIdeal; rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact zero_mem _
    exact this
  obtain ⟨Q', rfl⟩ := hmem
  refine ⟨Q', comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ?_⟩
  rw [← hQ, ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, qm_comp]

theorem spec_surj {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hs : Function.Surjective (PrimeSpectrum.comap f)) : Surjective (Spec.map (CommRingCat.ofHom f)) := by
  rw [surjective_iff]; exact hs

theorem part1 {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) (h : φ.IsIntegral)
    (hs : Function.Surjective (PrimeSpectrum.comap φ)) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
    IsIntegralHom (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) ∧
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) :=
  ⟨IsIntegralHom.SpecMap_iff.2 h, spec_surj _ hs, IsIntegralHom.SpecMap_iff.2 (qm_integral φ I h),
    spec_surj _ (qm_surj φ I hs)⟩

end LateralTheory.E.CechLevelsPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechLevelsPf

abbrev qm {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) : A ⧸ I →+* A' ⧸ I.map φ :=
  Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map

theorem spec_sq {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))) ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom (qm φ I)) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, qm_comp]

def sqA {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) :
    Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (qm φ I)))) ⟶ Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom φ))) :=
  Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ)))))
    (yoneda.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) (by
      simp only [Arrow.mk_hom]; rw [← yoneda.map_comp, ← yoneda.map_comp, spec_sq])

def psi {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) :
    cech (Spec.map (CommRingCat.ofHom (qm φ I))) ⟶ cech (Spec.map (CommRingCat.ofHom φ)) :=
  Arrow.mapCechNerve (sqA φ I)

theorem psi_aug {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) :
    psi φ I ≫ cechAug _ = cechAug _ ≫ spMap (Ideal.Quotient.mk I) := by
  ext n : 1
  change (psi φ I).app n ≫ (cechAug _).app n = (cechAug _).app n ≫ (spMap (Ideal.Quotient.mk I)).app n
  simp only [psi, cechAug, Arrow.augmentedCechNerve_hom_app, Arrow.mapCechNerve_app, WidePullback.lift_base, sqA,
    Arrow.homMk_right]
  erw [WidePullback.lift_base]
  rfl

def Levels : Prop := ∀ (A A' : Type) [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A), φ.IsIntegral →
  ∀ p, ∃ (B : Type) (_ : CommRing B) (χ : A →+* B), χ.IsIntegral ∧ Nonempty (Arrow.mk ((psi φ I).app p) ≅
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map χ))))))

def Level0 : Prop := ∀ (A A' : Type) [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A),
  Nonempty (Arrow.mk ((psi φ I).app (op (SimplexCategory.mk 0))) ≅
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ))))))

theorem CechLevels_of (hL : Levels) (h0 : Level0) : LateralTheory.E.t_E1Cut.CechLevels := by
  intro A A' _ _ φ I hi hs
  exact ⟨part1 φ I hi hs, psi φ I, psi_aug φ I, fun p => hL A A' φ I hi p, h0 A A' φ I⟩

end LateralTheory.E.CechLevelsPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CechLevelsGeneration.LevelsOfGen
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsPf
open LateralTheory.E.CechLevelsPf

theorem int_of_gen {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (hφ : φ.IsIntegral)
    (χ : A →+* B) {ι : Type} (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ)
    (hc : Subring.closure (⋃ i, Set.range (l i)) = ⊤) : χ.IsIntegral := by
  let _ := χ.toAlgebra
  have hle : Subring.closure (⋃ i, Set.range (l i)) ≤ (integralClosure A B).toSubring := by
    rw [Subring.closure_le]
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, y, rfl⟩ := hx
    obtain ⟨p, hm, hp⟩ := hφ y
    refine ⟨p, hm, ?_⟩
    show Polynomial.eval₂ χ (l i y) p = 0
    rw [← hl i, ← Polynomial.hom_eval₂, hp, map_zero]
  intro b
  have : b ∈ (integralClosure A B).toSubring := hle (hc ▸ Subring.mem_top b)
  exact this

def LevelsGen : Prop := ∀ (A A' : Type) [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) (p : SimplexCategoryᵒᵖ),
  ∃ (B : Type) (_ : CommRing B) (χ : A →+* B) (ι : Type) (l : ι → (A' →+* B)), (∀ i, (l i).comp φ = χ) ∧
    Subring.closure (⋃ i, Set.range (l i)) = ⊤ ∧ Nonempty (Arrow.mk ((psi φ I).app p) ≅
      Arrow.mk (yoneda.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map χ))))))

theorem Levels_of_gen (hG : LevelsGen) : LateralTheory.E.CechLevelsPf.Levels := by
  intro A A' _ _ φ I hφ p
  obtain ⟨B, _, χ, ι, l, hl, hc, he⟩ := hG A A' φ I p
  exact ⟨B, inferInstance, χ, int_of_gen φ hφ χ l hl hc, he⟩

end LateralTheory.E.LevelsPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SpectrumLimits
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

def IsCop {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
    (l : ι → (A' →+* B)) : Prop :=
  ∀ (R : Type) [CommRing R] (g : ι → (A' →+* R)) (c : A →+* R), (∀ i, (g i).comp φ = c) →
    ∃! h : B →+* R, (∀ i, h.comp (l i) = g i) ∧ h.comp χ = c

theorem le_l {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B)
    (f : A' →+* B) (hf : f.comp φ = χ) (I : Ideal A) : I.map φ ≤ (I.map χ).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, hf]

abbrev lq {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B)
    (f : A' →+* B) (hf : f.comp φ = χ) (I : Ideal A) : A' ⧸ I.map φ →+* B ⧸ I.map χ :=
  Ideal.quotientMap (I.map χ) f (le_l φ χ f hf I)

def coneOf {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
    (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) :
    Cone (WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
      (fun _ : ι => yoneda.obj (Spec (CommRingCat.of A'))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom φ)))) :=
  WidePullbackShape.mkCone (yoneda.map (Spec.map (CommRingCat.ofHom χ))) (fun i => yoneda.map (Spec.map (CommRingCat.ofHom (l i))))
    (fun i => by
      change yoneda.map _ ≫ yoneda.map (Spec.map (CommRingCat.ofHom φ)) = _
      rw [← yoneda.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hl i])

def SpecLim : Prop := ∀ (A A' B : Type) [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) (n : ℕ)
  (l : Fin (n + 1) → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ), IsCop φ χ l → Nonempty (IsLimit (coneOf φ χ l hl))

def TensCop : Prop := ∀ (A A' : Type) [CommRing A] [CommRing A'] (φ : A →+* A') (n : ℕ),
  ∃ (B : Type) (_ : CommRing B) (χ : A →+* B) (l : Fin (n + 1) → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ),
    Subring.closure (⋃ i, Set.range (l i)) = ⊤ ∧ IsCop φ χ l

def QuotCop : Prop := ∀ (A A' B : Type) [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
  (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) (I : Ideal A), IsCop φ χ l →
    IsCop (qm φ I) (qm χ I) (fun i => lq φ χ (l i) (hl i) I)

theorem lq_hl {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* A') (χ : A →+* B) {ι : Type}
  (l : ι → (A' →+* B)) (hl : ∀ i, (l i).comp φ = χ) (I : Ideal A) (i : ι) :
    (lq φ χ (l i) (hl i) I).comp (qm φ I) = qm χ I := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  simp [qm, lq, ← hl i]

theorem ysq {R S S' T : Type} [CommRing R] [CommRing S] [CommRing S'] [CommRing T] (f : R →+* S) (g : S →+* T)
    (f' : R →+* S') (g' : S' →+* T) (h : g.comp f = g'.comp f') :
    yoneda.map (Spec.map (CommRingCat.ofHom g)) ≫ yoneda.map (Spec.map (CommRingCat.ofHom f)) =
      yoneda.map (Spec.map (CommRingCat.ofHom g')) ≫ yoneda.map (Spec.map (CommRingCat.ofHom f')) := by
  rw [← yoneda.map_comp, ← yoneda.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, h]

theorem LevelsGen_of (hT : TensCop) (hQ : QuotCop) (hS : SpecLim) : LevelsGen := by
  intro A A' _ _ φ I p
  obtain ⟨B, _, χ, l, hl, hc, hcop⟩ := hT A A' φ (p.unop.len)
  refine ⟨B, inferInstance, χ, _, l, hl, hc, ?_⟩
  obtain ⟨L⟩ := hS A A' B φ χ _ l hl hcop
  obtain ⟨Lr⟩ := hS _ _ _ (qm φ I) (qm χ I) _ _ (lq_hl φ χ l hl I) (hQ A A' B φ χ l hl I hcop)
  let e : (cech (Spec.map (CommRingCat.ofHom φ))).obj p ≅
      yoneda.obj (Spec (CommRingCat.of B)) := (limit.isLimit _).conePointUniqueUpToIso L
  let er : (cech (Spec.map (CommRingCat.ofHom (qm φ I)))).obj p ≅
      yoneda.obj (Spec (CommRingCat.of (B ⧸ I.map χ))) := (limit.isLimit _).conePointUniqueUpToIso Lr
  refine ⟨Arrow.isoMk er e ?_⟩
  simp only [Arrow.mk_hom]
  apply L.hom_ext
  rintro (_|i)
  · have h1 : er.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (qm χ I))) = (WidePullback.base _ : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp Lr none
    have h2 : e.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ)) = (WidePullback.base _ : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp L none
    change (er.hom ≫ _) ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ)) =
      ((psi φ I).app p ≫ e.hom) ≫ yoneda.map (Spec.map (CommRingCat.ofHom χ))
    rw [Category.assoc, Category.assoc, h2, ysq χ (Ideal.Quotient.mk (I.map χ)) (Ideal.Quotient.mk I) (qm χ I) (qm_comp χ I).symm,
      ← Category.assoc, h1]
    simp only [psi, Arrow.mapCechNerve_app, sqA, Arrow.homMk_right]
    erw [WidePullback.lift_base]
    all_goals rfl
  · have h1 : er.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (lq φ χ (l i) (hl i) I))) = (WidePullback.π _ i : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp Lr (some i)
    have h2 : e.hom ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i))) = (WidePullback.π _ i : (cech _).obj p ⟶ _) :=
      (limit.isLimit _).conePointUniqueUpToIso_hom_comp L (some i)
    change (er.hom ≫ _) ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i))) =
      ((psi φ I).app p ≫ e.hom) ≫ yoneda.map (Spec.map (CommRingCat.ofHom (l i)))
    rw [Category.assoc, Category.assoc, h2, ysq (l i) (Ideal.Quotient.mk (I.map χ)) (Ideal.Quotient.mk (I.map φ))
      (lq φ χ (l i) (hl i) I) (Ideal.quotientMap_comp_mk _).symm, ← Category.assoc, h1]
    simp only [psi, Arrow.mapCechNerve_app, sqA, Arrow.homMk_left]
    erw [WidePullback.lift_π]
    all_goals rfl

end LateralTheory.E.LevelsGenPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.LevelsGenOfSpecLim
section -- merged from Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.QuotCop
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

theorem quotCop : QuotCop := by
  intro A A' B _ _ _ φ χ ι l hl I hcop R _ g c hg
  have hg' : ∀ i, ((g i).comp (Ideal.Quotient.mk (I.map φ))).comp φ = c.comp (Ideal.Quotient.mk I) := by
    intro i
    rw [RingHom.comp_assoc, ← qm_comp, ← RingHom.comp_assoc, hg i]
  obtain ⟨h', ⟨h'l, h'c⟩, h'u⟩ := hcop R _ _ hg'
  have hk : ∀ b ∈ I.map χ, h' b = 0 := by
    intro b hb
    have : I.map χ ≤ RingHom.ker h' := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change h' (χ a) = 0
      rw [← RingHom.comp_apply, h'c, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
    exact this hb
  refine ⟨Ideal.Quotient.lift _ h' hk, ⟨fun i => ?_, ?_⟩, fun h2 ⟨h2l, h2c⟩ => ?_⟩
  · apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, lq, Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply h' (l i), h'l i, RingHom.comp_apply]
  · apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.comp_apply, qm, Ideal.quotientMap_mk, Ideal.Quotient.lift_mk]
    rw [← RingHom.comp_apply h' χ, h'c, RingHom.comp_apply]
  · apply Ideal.Quotient.ringHom_ext
    have : h2.comp (Ideal.Quotient.mk _) = h' := by
      apply h'u
      refine ⟨fun i => ?_, ?_⟩
      · rw [RingHom.comp_assoc, ← Ideal.quotientMap_comp_mk (le_l φ χ (l i) (hl i) I), ← RingHom.comp_assoc]
        exact congrArg (fun f => RingHom.comp f (Ideal.Quotient.mk (I.map φ))) (h2l i)
      · rw [RingHom.comp_assoc, ← qm_comp, ← RingHom.comp_assoc, h2c]
    rw [this]
    ext x
    simp

end LateralTheory.E.LevelsGenPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.TensCop
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LevelsGenPf
open LateralTheory.E.CechLevelsPf LateralTheory.E.LevelsPf

open PiTensorProduct in
theorem tensCop : TensCop := by
  intro A A' _ _ φ n
  letI : Algebra A A' := φ.toAlgebra
  refine ⟨PiTensorProduct A (fun _ : Fin (n + 1) => A'), inferInstance, algebraMap A _, fun i => (singleAlgHom (A := fun _ => A') i).toRingHom,
    fun i => ?_, ?_, ?_⟩
  · exact (singleAlgHom (A := fun _ => A') i).comp_algebraMap
  · rw [eq_top_iff]
    intro x _
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      rw [Algebra.smul_def]
      refine Subring.mul_mem _ ?_ ?_
      · rw [← (singleAlgHom (A := fun _ => A') 0).commutes r]
        exact Subring.subset_closure (Set.mem_iUnion.2 ⟨0, _, rfl⟩)
      · have : tprod A f = ∏ i, singleAlgHom (A := fun _ => A') i (f i) := by
          simp only [singleAlgHom_apply, ← tprod_prod]
          congr 1
          exact (Finset.univ_prod_mulSingle f).symm
        rw [this]
        exact Subring.prod_mem _ fun i _ => Subring.subset_closure (Set.mem_iUnion.2 ⟨i, _, rfl⟩)
    | add x y hx hy => exact Subring.add_mem _ (hx trivial) (hy trivial)
  · intro R _ g c hg
    letI : Algebra A R := c.toAlgebra
    have hc : ∀ i r, g i (algebraMap A A' r) = algebraMap A R r := fun i r => by
      change g i (φ r) = c r
      rw [← RingHom.comp_apply, hg i]
    let ga : Fin (n + 1) → (A' →ₐ[A] R) := fun i => AlgHom.mk (g i) (hc i)
    let F : (Π _ : Fin (n + 1), A') →ₘₗ[A] R :=
      (MultilinearMap.mkPiAlgebra A (Fin (n + 1)) R).compLinearMap (fun i => (ga i).toLinearMap)
    let H := liftAlgHom F (by simp [F]) (by intro x y; simp [F, Finset.prod_mul_distrib])
    have hH : ∀ i a, H (singleAlgHom (A := fun _ => A') i a) = g i a := by
      intro i a
      change lift F (tprod A (MonoidHom.mulSingle (fun _ => A') i a)) = _
      rw [lift.tprod]
      simp only [F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
      rw [Finset.prod_eq_single i]
      · simp [ga]
      · intro j _ hj
        simp [ga, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
      · simp
    refine ⟨H.toRingHom, ⟨fun i => ?_, ?_⟩, fun h2 ⟨h2l, h2c⟩ => ?_⟩
    · ext a
      exact hH i a
    · ext a
      exact H.commutes a
    · have hc2 : ∀ r, h2 (algebraMap A (PiTensorProduct A (fun _ : Fin (n + 1) => A')) r) = algebraMap A R r := fun r => by
        change h2 (algebraMap A _ r) = c r
        rw [← RingHom.comp_apply, h2c]
      let H2 : (PiTensorProduct A (fun _ : Fin (n + 1) => A')) →ₐ[A] R := AlgHom.mk h2 hc2
      have : H2 = H := by
        apply PiTensorProduct.algHom_ext
        intro i
        ext a
        change h2 (singleAlgHom (A := fun _ => A') i a) = H (singleAlgHom (A := fun _ => A') i a)
        rw [hH]
        exact RingHom.congr_fun (h2l i) a
      exact congrArg AlgHom.toRingHom this

end LateralTheory.E.LevelsGenPf
end
end

namespace LateralTheory.E.LevelsGenPf

theorem LevelsGen_of_specLim (hS : SpecLim) : LateralTheory.E.LevelsPf.LevelsGen := LevelsGen_of tensCop quotCop hS

end LateralTheory.E.LevelsGenPf
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SpecLimPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.SpecLimPf
open LateralTheory.E.LevelsGenPf

def gam {T : Scheme.{0}} {R : Type} [CommRing R] (x : T ⟶ Spec (CommRingCat.of R)) : R →+* Γ(T, ⊤) :=
  ((ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm x).unop.hom

def uns {T : Scheme.{0}} {R : Type} [CommRing R] (h : R →+* Γ(T, ⊤)) : T ⟶ Spec (CommRingCat.of R) :=
  ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R)) (CommRingCat.ofHom h).op

theorem gam_uns {T : Scheme.{0}} {R : Type} [CommRing R] (h : R →+* Γ(T, ⊤)) : gam (uns h) = h := by
  have e := (ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm_apply_apply (CommRingCat.ofHom h).op
  simp only [gam, uns]
  erw [e]
  rfl

theorem gam_inj {T : Scheme.{0}} {R : Type} [CommRing R] {x y : T ⟶ Spec (CommRingCat.of R)}
    (h : gam x = gam y) : x = y := by
  apply (ΓSpec.adjunction.homEquiv T (op (CommRingCat.of R))).symm.injective
  apply Opposite.unop_injective
  exact CommRingCat.hom_ext h

theorem gam_comp {T : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (x : T ⟶ Spec (CommRingCat.of S)) : gam (x ≫ Spec.map (CommRingCat.ofHom f)) = (gam x).comp f := by
  have := ΓSpec.adjunction.homEquiv_naturality_right_symm x (CommRingCat.ofHom f).op
  simp only [gam]
  erw [this]
  rfl

theorem SpecLim_of : SpecLim := by
  intro A A' B _ _ _ φ χ n l hl hcop
  refine ⟨evaluationJointlyReflectsLimits _ fun k => ?_⟩
  obtain ⟨T⟩ := k

  let F := WidePullbackShape.wideCospan (yoneda.obj (Spec (CommRingCat.of A)))
      (fun _ : Fin (n + 1) => yoneda.obj (Spec (CommRingCat.of A'))) (fun _ => yoneda.map (Spec.map (CommRingCat.ofHom φ)))
  have key : ∀ (s : Cone (F ⋙ (evaluation _ _).obj (op T))) (p : s.pt),
      ∀ i, (gam (s.π.app (some i) p)).comp φ = gam (s.π.app none p) := by
    intro s p i
    have h : (s.π.app none p : T ⟶ Spec (CommRingCat.of A)) =
        (s.π.app (some i) p : T ⟶ Spec (CommRingCat.of A')) ≫ Spec.map (CommRingCat.ofHom φ) :=
      (types_congr_hom (s.w (WidePullbackShape.Hom.term i)) p).symm
    rw [h]
    exact (gam_comp φ _).symm
  refine IsLimit.mk (fun s => TypeCat.ofHom fun p => uns (hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p))
      (key s p)).exists.choose) ?_ ?_
  · intro s j
    ext p
    have hs := (hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p)) (key s p)).exists.choose_spec
    rcases j with _ | i
    · apply gam_inj
      change gam (uns _ ≫ Spec.map (CommRingCat.ofHom χ)) = _
      rw [gam_comp, gam_uns, hs.2]
      rfl
    · apply gam_inj
      change gam (uns _ ≫ Spec.map (CommRingCat.ofHom (l i))) = _
      rw [gam_comp, gam_uns, hs.1 i]
      rfl
  · intro s m hm
    ext p
    have H := hcop Γ(T, ⊤) (fun i => gam (s.π.app (some i) p)) (gam (s.π.app none p)) (key s p)
    change (m p : T ⟶ Spec (CommRingCat.of B)) = uns _
    apply gam_inj
    rw [gam_uns]
    refine H.unique ⟨fun i => ?_, ?_⟩ H.exists.choose_spec
    · have e : (s.π.app (some i) p : T ⟶ Spec (CommRingCat.of A')) =
          (m p : T ⟶ Spec (CommRingCat.of B)) ≫ Spec.map (CommRingCat.ofHom (l i)) :=
        (types_congr_hom (hm (some i)) p).symm
      change _ = gam (s.π.app (some i) p)
      rw [e]
      exact (gam_comp _ _).symm
    · have e : (s.π.app none p : T ⟶ Spec (CommRingCat.of A)) =
          (m p : T ⟶ Spec (CommRingCat.of B)) ≫ Spec.map (CommRingCat.ofHom χ) :=
        (types_congr_hom (hm none) p).symm
      rw [e]
      exact (gam_comp _ _).symm

end LateralTheory.E.SpecLimPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.CechLevels.Cech0Iso
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechLevelsPf

def cech0Iso (f : Arrow PSh) : f.cechNerve.obj (op (SimplexCategory.mk 0)) ≅ f.left where
  hom := WidePullback.π _ 0
  inv := WidePullback.lift f.hom (fun _ => 𝟙 _) (by simp)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j; rw [Fin.fin_one_eq_zero j]; rw [Category.assoc]; erw [WidePullback.lift_π, Category.comp_id]
    · rw [Category.assoc]; erw [WidePullback.lift_base, Category.id_comp]; exact WidePullback.π_arrow _ 0
  inv_hom_id := by erw [WidePullback.lift_π]

theorem level0 : Level0 := by
  intro A A' _ _ φ I
  refine ⟨Arrow.isoMk (cech0Iso _) (cech0Iso _) ?_⟩
  simp only [cech0Iso, psi, Arrow.mk_hom, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_π]
  rfl

theorem CechLevels_of' (hL : Levels) : LateralTheory.E.t_E1Cut.CechLevels := CechLevels_of hL level0

end LateralTheory.E.CechLevelsPf
end
end

namespace UpperTheory.Et.CechLevelsEtaleAxioms

theorem a0 : LateralTheory.E.LevelsGenPf.SpecLim := LateralTheory.E.SpecLimPf.SpecLim_of
theorem a1 : LateralTheory.E.LevelsPf.LevelsGen := LateralTheory.E.LevelsGenPf.LevelsGen_of_specLim a0
theorem a2 : LateralTheory.E.CechLevelsPf.Levels := LateralTheory.E.LevelsPf.Levels_of_gen a1
theorem a3 : LateralTheory.E.t_E1Cut.CechLevels := LateralTheory.E.CechLevelsPf.CechLevels_of' a2

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.CechLevels := a3

end UpperTheory.Et.CechLevelsEtaleAxioms
