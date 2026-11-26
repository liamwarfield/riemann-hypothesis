module

public import Development.WeilBound.CoreStatements.SesquilinearFractions.GModel

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.SpMapMonoOfFraction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace PositivityTheory.Xgf.BaseChangeTangents

section Comb

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S}

theorem isComb_iff {n : ℕ} (c : Fin n → R) (v : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) :
    IsComb c v w ↔ w = (List.ofFn fun i => LieTangent.epsScale x (c i) ≫ v i).prod := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine congrArg (fun f => (List.ofFn f).prod) (funext fun i => ?_)
    apply Over.OverMorphism.ext
    rw [hu i]
    rfl
  · intro hw
    exact ⟨_, fun i => rfl, hw⟩

theorem prod_pt {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) :
    ∀ {n : ℕ} (c : Fin n → R) (z : Fin n → E),
      (List.ofFn fun i => LieTangent.epsScale x (c i) ≫ M.pt (z i)).prod = M.pt (∑ i, c i • z i)
  | 0, c, z => by simp [LieModel.pt_zero]
  | n + 1, c, z => by
    rw [List.ofFn_succ, List.prod_cons, prod_pt M (fun i => c i.succ) (fun i => z i.succ), Fin.sum_univ_succ, M.add,
      LieModel.pt_smul]

end Comb

section BC

variable {V K : Type} [CommRing V] [CommRing K] (VK : V →+* K) {G : Over (Sp V)} [GrpObj G] {G' : Over (Sp K)}
  [GrpObj G'] {φ' : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap VK) φ')

private theorem bc_cond_lemma :
    spMap (dualMap VK) ≫ (epsAt (𝟙 (Sp V))).hom = (epsAt (𝟙 (Sp K))).hom ≫ spMap VK := by
  simp only [epsAt, Over.mk_hom, Category.comp_id, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem bc_cond (w : epsAt (𝟙 (Sp V)) ⟶ G) :
    (spMap (dualMap VK) ≫ w.left) ≫ G.hom = (epsAt (𝟙 (Sp K))).hom ≫ spMap VK := by
  rw [Category.assoc, Over.w]
  exact bc_cond_lemma VK

def bcTan (w : epsAt (𝟙 (Sp V)) ⟶ G) : epsAt (𝟙 (Sp K)) ⟶ G' :=
  Over.homMk (h.1.lift (spMap (dualMap VK) ≫ w.left) (epsAt (𝟙 (Sp K))).hom (bc_cond VK w)) (h.1.lift_snd _ _ _)

theorem bcTan_left (w : epsAt (𝟙 (Sp V)) ⟶ G) : (bcTan VK h w).left ≫ φ' = spMap (dualMap VK) ≫ w.left :=
  h.1.lift_fst _ _ _

theorem bcTan_unique (w : epsAt (𝟙 (Sp V)) ⟶ G) (s : epsAt (𝟙 (Sp K)) ⟶ G')
    (hs : s.left ≫ φ' = spMap (dualMap VK) ≫ w.left) : s = bcTan VK h w := by
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · rw [hs, bcTan_left]
  · rw [Over.w s, Over.w (bcTan VK h w)]

theorem bcTan_mul (w w' : epsAt (𝟙 (Sp V)) ⟶ G) :
    bcTan VK h (w * w') = bcTan VK h w * bcTan VK h w' := by
  symm
  apply bcTan_unique
  let g : Over.mk ((epsAt (𝟙 (Sp K))).hom ≫ spMap VK) ⟶ epsAt (𝟙 (Sp V)) :=
    Over.homMk (spMap (dualMap VK)) (bc_cond_lemma VK)
  have := h.2 (epsAt (𝟙 (Sp K))) (bcTan VK h w) (bcTan VK h w') (g ≫ w) (g ≫ w')
    (bcTan_left VK h w).symm (bcTan_left VK h w').symm
  rw [← this, ← MonObj.comp_mul]
  rfl

theorem bcTan_one : bcTan VK h (1 : epsAt (𝟙 (Sp V)) ⟶ G) = 1 := by
  have := bcTan_mul VK h 1 1
  rw [_root_.mul_one] at this
  exact mul_eq_left.1 this.symm

private theorem scale_lemma (c : V) :
    (GlobalTheory.CompanionTheory.Ar.epsMul (VK c)).comp (dualMap VK) = (dualMap VK).comp (GlobalTheory.CompanionTheory.Ar.epsMul c) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul]
  · simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, smul_eq_mul, map_mul, mul_comm]

theorem bcTan_scale (c : V) (w : epsAt (𝟙 (Sp V)) ⟶ G) :
    bcTan VK h (LieTangent.epsScale _ c ≫ w) = LieTangent.epsScale _ (VK c) ≫ bcTan VK h w := by
  symm
  apply bcTan_unique
  rw [Over.comp_left, Over.comp_left, Category.assoc, bcTan_left]
  simp only [LieTangent.epsScale, Over.homMk_left, spMap, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, scale_lemma]

theorem bcTan_comb {n : ℕ} (c : Fin n → V) (w : Fin n → (epsAt (𝟙 (Sp V)) ⟶ G)) :
    bcTan VK h (List.ofFn fun i => LieTangent.epsScale _ (c i) ≫ w i).prod =
      (List.ofFn fun i => LieTangent.epsScale _ (VK (c i)) ≫ bcTan VK h (w i)).prod := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil]
    exact bcTan_one VK h
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [bcTan_mul, bcTan_scale, ih (fun i => c i.succ) (fun i => w i.succ)]

private theorem prime_lemma_2 {R : Type} [CommRing R] (p : PrimeSpectrum (DualNumber R)) :
    PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom
      (PrimeSpectrum.comap (algebraMap R (DualNumber R)) p) = p := by
  ext x
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  show algebraMap R (DualNumber R) x.fst ∈ p.asIdeal ↔ x ∈ p.asIdeal
  have hn : (x - algebraMap R (DualNumber R) x.fst) ^ 2 = 0 := by
    ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
  have hmem : x - algebraMap R (DualNumber R) x.fst ∈ p.asIdeal :=
    p.isPrime.mem_of_pow_mem 2 (by rw [hn]; exact p.asIdeal.zero_mem)
  constructor
  · intro hx
    simpa using p.asIdeal.add_mem hmem hx
  · intro hx
    simpa using p.asIdeal.sub_mem hx hmem

private theorem cancel_lemma {R B : Type} [CommRing R] [CommRing B] {X : Scheme.{0}} (j : R →+* B)
    (hj : Function.Injective j) (a b : Spec (CommRingCat.of R) ⟶ X) (c : Spec (CommRingCat.of R))
    (hc : a c = b c) (hsp : ∀ p : Spec (CommRingCat.of R), p ⤳ c)
    (e : Spec.map (CommRingCat.ofHom j) ≫ a = Spec.map (CommRingCat.ofHom j) ≫ b) : a = b := by
  obtain ⟨U, hU, hcU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show a c ∈ (⊤ : X.Opens) from trivial)
  haveI : IsAffine U := hU
  have ha : Set.range a ⊆ Set.range (Scheme.Opens.ι U) := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact ((hsp p).map a.continuous).mem_open U.isOpen hcU
  have hb : Set.range b ⊆ Set.range (Scheme.Opens.ι U) := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact ((hsp p).map b.continuous).mem_open U.isOpen (hc ▸ hcU)
  rw [← IsOpenImmersion.lift_fac (Scheme.Opens.ι U) a ha, ← IsOpenImmersion.lift_fac (Scheme.Opens.ι U) b hb]
  congr 1
  apply ext_of_isAffine
  have e' : Spec.map (CommRingCat.ofHom j) ≫ IsOpenImmersion.lift (Scheme.Opens.ι U) a ha =
      Spec.map (CommRingCat.ofHom j) ≫ IsOpenImmersion.lift (Scheme.Opens.ι U) b hb := by
    rw [← cancel_mono (Scheme.Opens.ι U), Category.assoc, Category.assoc, IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac, e]
  haveI : Mono (CommRingCat.ofHom j) := ConcreteCategory.mono_of_injective _ hj
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom j)
  haveI : Mono ((Spec.map (CommRingCat.ofHom j)).appTop ≫ (Scheme.ΓSpecIso _).hom) := by
    rw [hnat]
    infer_instance
  haveI : Mono (Spec.map (CommRingCat.ofHom j)).appTop := mono_of_mono _ (Scheme.ΓSpecIso _).hom
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom j)).appTop]
  have := congrArg Scheme.Hom.appTop e'
  simpa using this

theorem bcTan_inj [IsLocalRing V] (hVK : Function.Injective VK) {w w' : epsAt (𝟙 (Sp V)) ⟶ G}
    (hw : IsTanAt G _ w) (hw' : IsTanAt G _ w') (e : bcTan VK h w = bcTan VK h w') : w = w' := by
  have hl : spMap (dualMap VK) ≫ w.left = spMap (dualMap VK) ≫ w'.left := by
    rw [← bcTan_left VK h w, ← bcTan_left VK h w', e]
  have ht := hw.trans hw'.symm
  apply Over.OverMorphism.ext
  refine cancel_lemma (dualMap VK) (LieTangent.dualMap_injective hVK) w.left w'.left
    (PrimeSpectrum.comap (TrivSqZeroExt.fstHom V V V).toRingHom (IsLocalRing.closedPoint V)) ?_ ?_ hl
  · exact congrArg (fun f => f.base (IsLocalRing.closedPoint V)) ht
  · intro p
    rw [← prime_lemma_2 p]
    exact (IsLocalRing.specializes_closedPoint _).map (PrimeSpectrum.continuous_comap _)

theorem bcTan_act (α' : G' ⟶ G') (α : G ⟶ G) (hα : α'.left ≫ φ' = φ' ≫ α.left) (w : epsAt (𝟙 (Sp V)) ⟶ G) :
    bcTan VK h (w ≫ α) = bcTan VK h w ≫ α' := by
  symm
  apply bcTan_unique
  simp only [Over.comp_left, Category.assoc, hα]
  rw [← Category.assoc, bcTan_left, Category.assoc]

omit [GrpObj G] [GrpObj G'] in
theorem spMap_mono_of_fraction [IsDomain V] [Algebra V K] [IsFractionRing V K] (hVK : VK = algebraMap V K)
    {A : Type} [CommRing A] (f₁ f₂ : Sp A ⟶ Sp K) (e : f₁ ≫ spMap VK = f₂ ≫ spMap VK) : f₁ = f₂ := by
  subst hVK
  haveI : Epi (CommRingCat.ofHom (algebraMap V K)) := IsLocalization.epi (nonZeroDivisors V) K
  haveI : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap V K)).op) := inferInstance
  exact (cancel_mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap V K)).op)).1 e

theorem eq_bcTan_left [IsDomain V] [Algebra V K] [IsFractionRing V K] (hVK : VK = algebraMap V K)
    (w : epsAt (𝟙 (Sp V)) ⟶ G) (s : Sp (DualNumber K) ⟶ G'.left)
    (hs : s ≫ φ' = spMap (dualMap VK) ≫ w.left) : s = (bcTan VK h w).left := by
  apply h.1.hom_ext
  · rw [hs, bcTan_left]
  · apply spMap_mono_of_fraction VK hVK
    rw [Category.assoc, ← h.1.w, ← Category.assoc, hs, bc_cond, Over.w]

end BC

section Push

variable {S : Scheme.{0}} {K : Type} [CommRing K] {G : Over S} [GrpObj G] {G' : Over (Sp K)} [GrpObj G']
  {y₀ : Sp K ⟶ S} {φ : G'.left ⟶ G.left} (hp : IsGrpPullback G' G y₀ φ)

include hp

theorem push_cond (s : epsAt (𝟙 (Sp K)) ⟶ G') : (s.left ≫ φ) ≫ G.hom = (epsAt y₀).hom := by
  rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w s]
  show (Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) ≫ 𝟙 _) ≫ y₀ = _
  rw [Category.comp_id]
  rfl

def push (s : epsAt (𝟙 (Sp K)) ⟶ G') : epsAt y₀ ⟶ G := Over.homMk (s.left ≫ φ) (push_cond hp s)

theorem push_left (s : epsAt (𝟙 (Sp K)) ⟶ G') : (push hp s).left = s.left ≫ φ := rfl

theorem push_mul (s s' : epsAt (𝟙 (Sp K)) ⟶ G') : push hp (s * s') = push hp s * push hp s' := by
  let g : Over.mk ((epsAt (𝟙 (Sp K))).hom ≫ y₀) ⟶ epsAt y₀ := Over.homMk (𝟙 _) (by simp [epsAt])
  have := hp.2 (epsAt (𝟙 (Sp K))) s s' (g ≫ push hp s) (g ≫ push hp s') (by simp [g, push_left])
    (by simp [g, push_left])
  rw [← MonObj.comp_mul] at this
  apply Over.OverMorphism.ext
  rw [push_left, ← this]
  simp [g]

theorem push_inj {s s' : epsAt (𝟙 (Sp K)) ⟶ G'} (e : push hp s = push hp s') : s = s' := by
  apply Over.OverMorphism.ext
  apply hp.1.hom_ext
  · exact congrArg (·.left) e
  · rw [Over.w s, Over.w s']

theorem push_scale (c : K) (s : epsAt (𝟙 (Sp K)) ⟶ G') :
    push hp (LieTangent.epsScale _ c ≫ s) = LieTangent.epsScale _ c ≫ push hp s := by
  apply Over.OverMorphism.ext
  rw [push_left, Over.comp_left, Over.comp_left, push_left, Category.assoc]
  rfl

theorem push_act (α' : G' ⟶ G') (α : G ⟶ G) (hα : α'.left ≫ φ = φ ≫ α.left) (s : epsAt (𝟙 (Sp K)) ⟶ G') :
    push hp (s ≫ α') = push hp s ≫ α := by
  apply Over.OverMorphism.ext
  rw [push_left, Over.comp_left, Over.comp_left, push_left, Category.assoc, hα, Category.assoc]

def pushHom : (epsAt (𝟙 (Sp K)) ⟶ G') →* (epsAt y₀ ⟶ G) where
  toFun := push hp
  map_one' := by
    have := push_mul hp 1 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  map_mul' := push_mul hp

theorem push_comb {n : ℕ} (c : Fin n → K) (w : Fin n → (epsAt (𝟙 (Sp K)) ⟶ G')) :
    push hp (List.ofFn fun i => LieTangent.epsScale _ (c i) ≫ w i).prod =
      (List.ofFn fun i => LieTangent.epsScale _ (c i) ≫ push hp (w i)).prod := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil]
    exact (pushHom hp).map_one
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [push_mul, push_scale, ih (fun i => c i.succ) (fun i => w i.succ)]

end Push

end PositivityTheory.Xgf.BaseChangeTangents
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

private theorem isTanAt_iff_epsScale_zero_comp_eq_one {R : Type} [CommRing R] {S : Scheme} (x : Sp R ⟶ S) (G : Over S) [GrpObj G]
    (v : epsAt x ⟶ G) : IsTanAt G x v ↔ LieTangent.epsScale x 0 ≫ v = 1 := by
  have one_left : ∀ (Y : Over S), (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
    intro Y
    rw [Hom.one_def, Over.comp_left]
    congr 1
  have hmul : Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro a
    ext <;> simp [CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have hid : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    apply RingHom.ext
    intro a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hsec : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hid, CommRingCat.ofHom_id, Spec.map_id]
  unfold IsTanAt
  constructor
  · intro h
    apply Over.OverMorphism.ext
    rw [Over.comp_left, one_left]
    change Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) ≫ v.left = _
    rw [hmul, Category.assoc, h, one_left]
    simp [epsAt]
  · intro h
    rw [one_left]
    have h2 := congrArg Over.Hom.left h
    rw [Over.comp_left, one_left] at h2
    change Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) ≫ v.left = _ at h2
    rw [hmul, Category.assoc] at h2
    have h3 := congrArg (fun q => Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ q) h2
    simp only [epsAt, Over.mk_hom, ← Category.assoc, hsec, Category.id_comp] at h3
    rw [h3]
    simp

open BaseChangeTangents in
theorem lie_model_extends_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (K : Type) [Field K] (V : Subring K) [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] (y : Sp K ⟶ Xo.XF c) (T : SAB H (Sp V)) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K))) (U : Type) [AddCommGroup U] [Module K U] (M : LieModel Xo.univ.t.G (under y) U) (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (I : Type) [Fintype I] (n r : ℕ) (e : Fin n ≃ I) (uV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (u : I → U) (v : Fin r → U), M.IsActOf Xo.univ.t.act.act ρ → (∀ a : 𝓞 E, σ (a : E) ∈ V) → (∀ k, IsTanAt T.G _ (uV k)) → (∀ w, IsTanAt T.G _ w → ∃! cc : Fin n → V, IsComb cc uV w) → (∀ k, ∃ s : Sp (DualNumber K) ⟶ tK.G.left, s ≫ m.φ = (M.pt (u (e k))).left ∧ s ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (uV k).left) → LinearIndependent K v → Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V = Submodule.span V (Set.range v) → LinearIndependent K u ∧ IsIntFrame m m' (σ.comp (algebraMap (𝓞 E) E)) (fun a => M.pt (v a)) := by
  intro E _ _ _ H D l Xo c K _ V _ _ _ y T tK m m' U _ _ M ρ σ I _ n r e uV u v hρ hσ huVt huVb hcorr hv hspan
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  let P : (epsAt (𝟙 (Sp V)) ⟶ T.G) → (epsAt (under y) ⟶ Xo.univ.t.G) :=
    fun w => BaseChangeTangents.push m.cart (BaseChangeTangents.bcTan (algebraMap V K) m'.cart w)
  have hP1 : P 1 = 1 := by
    simp only [P, BaseChangeTangents.bcTan_one]
    exact map_one (BaseChangeTangents.pushHom m.cart)
  have hPscale : ∀ (a : V) w, P (LieTangent.epsScale (𝟙 (Sp V)) a ≫ w) =
      LieTangent.epsScale (under y) (algebraMap V K a) ≫ P w := by
    intro a w
    simp only [P, BaseChangeTangents.bcTan_scale, BaseChangeTangents.push_scale]
  have hPcomb : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)),
      P (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod =
        (List.ofFn fun i => LieTangent.epsScale (under y) (algebraMap V K (cc i)) ≫ P (w i)).prod := by
    intro N cc w
    simp only [P, BaseChangeTangents.bcTan_comb, BaseChangeTangents.push_comb]
  have hPact : ∀ (a : 𝓞 E) w, P (w ≫ T.act.act a) = P w ≫ Xo.univ.t.act.act a := by
    intro a w
    simp only [P]
    rw [BaseChangeTangents.bcTan_act _ m'.cart (tK.act.act a) (T.act.act a) (m'.act a),
      BaseChangeTangents.push_act m.cart (tK.act.act a) (Xo.univ.t.act.act a) (m.act a)]
  have tprod : ∀ (L : List (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ w ∈ L, IsTanAt T.G (𝟙 (Sp V)) w) →
      IsTanAt T.G (𝟙 (Sp V)) L.prod := by
    intro L
    induction L with
    | nil =>
      intro _
      simpa using LieTangent.isTanAt_one
    | cons a L ih =>
      intro h
      rw [List.prod_cons]
      exact LieTangent.isTanAt_mul (h a (by simp)) (ih fun w hw => h w (by simp [hw]))
  have tcomb : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)),
      (∀ k, IsTanAt T.G (𝟙 (Sp V)) (w k)) →
        IsTanAt T.G (𝟙 (Sp V)) (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod := by
    intro N cc w hw
    apply tprod
    intro z hz
    simp only [List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    exact LieTangent.isTanAt_scale _ (hw i)
  have hPinj : ∀ w w', IsTanAt T.G (𝟙 (Sp V)) w → IsTanAt T.G (𝟙 (Sp V)) w' → P w = P w' → w = w' := by
    intro w w' hw hw' h
    exact BaseChangeTangents.bcTan_inj _ m'.cart hinj hw hw' (BaseChangeTangents.push_inj m.cart h)
  have hM0 : M.pt 0 = 1 := by
    have h := M.add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hMscale : ∀ (a : K) (z : U), M.pt (a • z) = LieTangent.epsScale (under y) a ≫ M.pt z := by
    intro a z
    apply Over.OverMorphism.ext
    rw [M.smul, Over.comp_left]
    rfl
  have hPu : ∀ k, P (uV k) = M.pt (u (e k)) := by
    intro k
    obtain ⟨s, hs1, hs2⟩ := hcorr k
    have hs := BaseChangeTangents.eq_bcTan_left (algebraMap V K) m'.cart rfl (uV k) s hs2
    apply Over.OverMorphism.ext
    simp only [P]
    rw [BaseChangeTangents.push_left, ← hs]
    exact hs1
  have hPsum : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (z : Fin N → U),
      (∀ k, P (w k) = M.pt (z k)) →
        P (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod =
          M.pt (∑ i, algebraMap V K (cc i) • z i) := by
    intro N cc w z hwz
    rw [hPcomb]
    simp only [hwz]
    exact BaseChangeTangents.prod_pt M _ z
  have hsmul : ∀ (a : V) (z : U), a • z = algebraMap V K a • z := fun a z => (algebraMap_smul K a z).symm
  have hliV : LinearIndependent V u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let cc : Fin n → V := fun k => g (e k)
    have hsum : ∑ k, algebraMap V K (cc k) • u (e k) = 0 := by
      calc ∑ k, algebraMap V K (cc k) • u (e k) = ∑ k, g (e k) • u (e k) :=
            Finset.sum_congr rfl fun k _ => (hsmul _ _).symm
        _ = ∑ i, g i • u i := Equiv.sum_comp e (fun i => g i • u i)
        _ = 0 := hg
    have hcomb1 : P (List.ofFn fun k => LieTangent.epsScale (𝟙 (Sp V)) (cc k) ≫ uV k).prod = P 1 := by
      rw [hPsum cc uV (fun k => u (e k)) hPu]
      simp only [hsum, hM0, hP1]
    have heq1 := hPinj _ _ (tcomb cc uV huVt) LieTangent.isTanAt_one hcomb1
    obtain ⟨c0, _, huniq⟩ := huVb 1 LieTangent.isTanAt_one
    have hc1 : IsComb cc uV 1 := by
      rw [BaseChangeTangents.isComb_iff]
      exact heq1.symm
    have hc0 : IsComb (fun _ => (0 : V)) uV 1 := by
      rw [BaseChangeTangents.isComb_iff]
      have h0 : ∀ k, LieTangent.epsScale (𝟙 (Sp V)) (0 : V) ≫ uV k = 1 :=
        fun k => (isTanAt_iff_epsScale_zero_comp_eq_one _ _ _).mp (huVt k)
      simp only [h0, List.ofFn_const, List.prod_replicate, one_pow]
    have hcc := (huniq cc hc1).trans (huniq _ hc0).symm
    have hk := congrFun hcc (e.symm i)
    simpa [cc] using hk
  have hliK : LinearIndependent K u := LinearIndependent.localization K (nonZeroDivisors V) hliV
  refine ⟨hliK, ?_⟩
  let σV : 𝓞 E →+* V := (σ.comp (algebraMap (𝓞 E) E)).codRestrict V (fun a => hσ a)
  have hσV : ∀ a, algebraMap V K (σV a) = σ (a : E) := fun a => rfl
  have hvmem : ∀ a, v a ∈ Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V := by
    intro a
    rw [hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  choose d hd using fun a => (Submodule.mem_span_range_iff_exists_fun V).mp (hvmem a).1
  let vV : Fin r → (epsAt (𝟙 (Sp V)) ⟶ T.G) :=
    fun a => (List.ofFn fun k => LieTangent.epsScale (𝟙 (Sp V)) (d a (e k)) ≫ uV k).prod
  have hPv : ∀ a, P (vV a) = M.pt (v a) := by
    intro a
    rw [hPsum (fun k => d a (e k)) uV (fun k => u (e k)) hPu, ← hd a]
    congr 1
    rw [← Equiv.sum_comp e (fun i => d a i • u i)]
    exact Finset.sum_congr rfl fun k _ => (hsmul _ _).symm
  have hvVt : ∀ a, IsTanAt T.G (𝟙 (Sp V)) (vV a) := fun a => tcomb _ uV huVt
  have heig : ∀ w (z : U), IsTanAt T.G (𝟙 (Sp V)) w → P w = M.pt z →
      (IsEigVec T.act (𝟙 (Sp V)) σV w ↔ z ∈ HT.eigSp ρ σ) := by
    intro w z hw hwz
    have key : ∀ a : 𝓞 E, (Over.Hom.left (w ≫ T.act.act a) = spMap (CompanionTheory.Ar.epsMul (σV a)) ≫ Over.Hom.left w) ↔
        ρ a z = σ (a : E) • z := by
      intro a
      have e1 : (Over.Hom.left (w ≫ T.act.act a) = spMap (CompanionTheory.Ar.epsMul (σV a)) ≫ Over.Hom.left w) ↔
          w ≫ T.act.act a = LieTangent.epsScale (𝟙 (Sp V)) (σV a) ≫ w := by
        constructor
        · intro h
          apply Over.OverMorphism.ext
          rw [h, Over.comp_left]
          rfl
        · intro h
          rw [h, Over.comp_left]
          rfl
      rw [e1]
      haveI := T.act.hom a
      constructor
      · intro h
        have h2 := congrArg P h
        rw [hPact, hPscale, hwz, hσV] at h2
        apply M.inj
        rw [hMscale, ← h2]
        exact hρ a z
      · intro h
        apply hPinj _ _ (TransportLieModel.isTanAt_comp hw _) (LieTangent.isTanAt_scale _ hw)
        rw [hPact, hPscale, hwz, hσV, ← hMscale, ← h]
        exact (hρ a z).symm
    simp only [IsEigVec, hw, true_and, key]
    simp only [HT.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  refine ⟨σV, vV, ?_, ?_, ?_⟩
  · exact RingHom.ext fun a => rfl
  · refine ⟨?_, ?_⟩
    · intro a
      exact (heig (vV a) (v a) (hvVt a) (hPv a)).mpr ((Submodule.restrictScalars_mem _ _ _).mp (hvmem a).2)
    · intro w hw
      have hwt : IsTanAt T.G (𝟙 (Sp V)) w := hw.1
      obtain ⟨cc, hcc, _⟩ := huVb w hwt
      rw [BaseChangeTangents.isComb_iff] at hcc
      have hPw : P w = M.pt (∑ k, algebraMap V K (cc k) • u (e k)) := by
        rw [hcc]
        exact hPsum cc uV (fun k => u (e k)) hPu
      have hzE := (heig w _ hwt hPw).mp hw
      have hzU : (∑ k, algebraMap V K (cc k) • u (e k)) ∈ Submodule.span V (Set.range u) := by
        apply Submodule.sum_mem
        intro k _
        rw [← hsmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e k, rfl⟩)
      have hzv : (∑ k, algebraMap V K (cc k) • u (e k)) ∈ Submodule.span V (Set.range v) := by
        rw [← hspan]
        exact ⟨hzU, hzE⟩
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun V).mp hzv
      have hPg : P (List.ofFn fun a => LieTangent.epsScale (𝟙 (Sp V)) (g a) ≫ vV a).prod =
          M.pt (∑ k, algebraMap V K (cc k) • u (e k)) := by
        rw [hPsum g vV v hPv, ← hg]
        exact congrArg M.pt (Finset.sum_congr rfl fun a _ => (hsmul _ _).symm)
      refine ⟨g, ?_, ?_⟩
      · show Fl.IsComb g vV w
        rw [BaseChangeTangents.isComb_iff]
        exact hPinj _ _ hwt (tcomb g vV hvVt) (hPw.trans hPg.symm)
      · intro g' hg'
        change Fl.IsComb g' vV w at hg'
        rw [BaseChangeTangents.isComb_iff] at hg'
        have h1 : M.pt (∑ a, algebraMap V K (g' a) • v a) = M.pt (∑ a, algebraMap V K (g a) • v a) := by
          rw [← hPsum g' vV v hPv, ← hg', hPw, ← hg]
          exact congrArg M.pt (Finset.sum_congr rfl fun a _ => hsmul _ _)
        have h2 := M.inj h1
        funext a
        apply hinj
        have h3 := Fintype.linearIndependent_iff.mp hv (fun a => algebraMap V K (g' a) - algebraMap V K (g a))
          (by simp only [sub_smul, Finset.sum_sub_distrib, h2, sub_self]) a
        exact sub_eq_zero.mp h3
  · intro a
    refine ⟨(BaseChangeTangents.bcTan (algebraMap V K) m'.cart (vV a)).left, ?_, BaseChangeTangents.bcTan_left _ _ _⟩
    exact (BaseChangeTangents.push_left m.cart _).symm.trans (congrArg Over.Hom.left (hPv a))

end PositivityTheory.Xgf
