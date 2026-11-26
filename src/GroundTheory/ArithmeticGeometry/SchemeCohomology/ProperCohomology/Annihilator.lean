module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SegreGlue

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Annihilator
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {X : Scheme.{u}}

def annihilatorIdeal (F : X.Modules) (U : X.Opens) : Ideal Γ(X, U) :=
  Module.annihilator Γ(X, U) Γ(F, U)

lemma mem_annihilatorIdeal {F : X.Modules} {U : X.Opens} {a : Γ(X, U)} :
    a ∈ annihilatorIdeal F U ↔ ∀ m : Γ(F, U), a • m = 0 :=
  Module.mem_annihilator

lemma eq_zero_of_isUnit_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {a : R}
    (ha : IsUnit a) {m : M} (h : a • m = 0) : m = 0 := by
  rw [← one_smul R m, ← ha.unit.inv_mul, mul_smul, IsUnit.unit_spec, h, smul_zero]

lemma exists_pow_mul_mem_annihilatorIdeal (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) [Module.Finite Γ(X, U) Γ(F, U)] (f a : Γ(X, U))
    (h : ∀ m : Γ(F, U), resF F (X.basicOpen_le f) (a • m) = 0) :
    ∃ E : ℕ, f ^ E * a ∈ annihilatorIdeal F U := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Γ(X, U)) (M := Γ(F, U))
  have : ∀ m ∈ s, ∃ e : ℕ, f ^ e • (a • m) = 0 := fun m _ =>
    qcoh_exists_pow_smul_eq_zero F hU f (a • m) (h m)
  choose! e he using this
  refine ⟨s.sup e, ?_⟩
  rw [annihilatorIdeal, ← Submodule.annihilator_top, ← hs, Submodule.mem_annihilator_span]
  rintro ⟨m, hm⟩
  have hle : e m ≤ s.sup e := Finset.le_sup hm
  change (f ^ s.sup e * a) • m = 0
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, mul_smul, mul_smul, he m hm, smul_zero]

theorem map_annihilatorIdeal_basicOpen (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) [Module.Finite Γ(X, U) Γ(F, U)] (f : Γ(X, U)) :
    (annihilatorIdeal F U).map (resO (X.basicOpen_le f)) = annihilatorIdeal F (X.basicOpen f) := by
  have hunit : IsUnit (resO (X.basicOpen_le f) f) := X.toRingedSpace.isUnit_res_basicOpen f
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_annihilatorIdeal]
    intro m
    obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq F hU f m
    refine eq_zero_of_isUnit_smul (hunit.pow e) ?_
    rw [smul_smul, mul_comm, ← smul_smul, ← hm', ← resF_smul, mem_annihilatorIdeal.1 ha m',
      map_zero]
  · intro b hb
    rw [mem_annihilatorIdeal] at hb
    have := hU.isLocalization_basicOpen f
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, hab⟩ := IsLocalization.surj (Submonoid.powers f) b
    change b * resO (X.basicOpen_le f) (f ^ k) = resO (X.basicOpen_le f) a at hab
    obtain ⟨E, hE⟩ := exists_pow_mul_mem_annihilatorIdeal F hU f a (fun m => by
      rw [resF_smul, ← hab, mul_smul, hb])
    have hmem : resO (X.basicOpen_le f) (f ^ E * a) ∈
        (annihilatorIdeal F U).map (resO (X.basicOpen_le f)) := Ideal.mem_map_of_mem _ hE
    have hu : IsUnit (resO (X.basicOpen_le f) (f ^ (E + k))) := by
      rw [map_pow]; exact hunit.pow _
    have hb' : b = resO (X.basicOpen_le f) (f ^ E * a) * ↑hu.unit⁻¹ := by
      rw [Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec, pow_add, map_mul, map_mul, ← hab]
      ring
    rw [hb']
    exact Ideal.mul_mem_right _ _ hmem

def annihilatorIdealSheaf (F : X.Modules) (hF : IsCoherent F) : X.IdealSheafData where
  ideal U := annihilatorIdeal F U
  map_ideal_basicOpen U f := by
    have := hF.1
    have := hF.2 U U.2
    exact map_annihilatorIdeal_basicOpen F U.2 f

theorem support_annihilatorIdealSheaf_subset (F : X.Modules) (hF : IsCoherent F) {T : Set X}
    (hT : IsClosed T) (hFT : Scheme.Modules.SupportedIn F T) :
    ((annihilatorIdealSheaf F hF).support : Set X) ⊆ T := by
  intro x hx
  by_contra hxT
  have := hF.1
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U : X.affineOpens := ⟨U₀, hU₀⟩
  have := hF.2 U U.2
  let V : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  obtain ⟨f, hfV, hxf⟩ := U.2.exists_basicOpen_le (V := V) ⟨x, hxT⟩ hxU
  obtain ⟨E, hE⟩ := exists_pow_mul_mem_annihilatorIdeal F U.2 f 1 (fun m =>
    hFT _ (Set.disjoint_left.2 fun y hy hyT => hfV hy hyT) _)
  rw [mul_one] at hE
  have hE' : f ^ (E + 1) ∈ (annihilatorIdealSheaf F hF).ideal U := by
    rw [pow_succ]; exact Ideal.mul_mem_right _ _ hE
  have hx' : x ∈ (annihilatorIdealSheaf F hF).support := hx
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (show x ∈ U.1 from hxU),
    Scheme.mem_zeroLocus_iff] at hx'
  exact hx' _ hE' (by rwa [Scheme.basicOpen_pow _ _ (Nat.succ_pos E)])

end

end GroundTheory.Arith.SchemeCoh
end

section -- merged from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.AppLEFromOfGlobalSectionsChartHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite HomogeneousLocalization MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

lemma appTop_appLE {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens}
    (e : ⊤ ≤ g ⁻¹ᵁ U) (e' : ⊤ ≤ (f ≫ g) ⁻¹ᵁ U) (s : Γ(Z, U)) :
    f.appTop (g.appLE U ⊤ e s) = (f ≫ g).appLE U ⊤ e' s := by
  have h1 : f.appTop = f.appLE ⊤ ⊤ (f.preimage_top).ge := (Scheme.Hom.appLE_eq_app _).symm
  rw [h1]
  exact congr($(Scheme.Hom.appLE_comp_appLE f g U ⊤ ⊤ _ _) s)

variable {A : Type u} [CommRing A]

lemma appLE_fromOfGlobalSections_chartHom {N : ℕ} {O : Scheme.{u}}
    (φ : MvPolynomial (Fin (N + 1)) A →+* Γ(O, ⊤))
    (hφ : (HomogeneousIdeal.irrelevant (grading A N)).toIdeal.map φ = ⊤) (z : Fin (N + 1))
    (hz : φ (X z) = 1)
    (h : ⊤ ≤ Proj.fromOfGlobalSections (grading A N) φ hφ ⁻¹ᵁ Proj.basicOpen (grading A N) (X z))
    {t : ℕ} {a : MvPolynomial (Fin (N + 1)) A} (ha : a ∈ grading A N t) :
    (Proj.fromOfGlobalSections (grading A N) φ hφ).appLE _ ⊤ h (chartHom z a) = φ a := by
  have hV : O.basicOpen (φ (X z)) = ⊤ := by
    rw [hz]
    exact Scheme.basicOpen_of_isUnit _ isUnit_one
  have ha' : a ∈ grading A N (t • 1) := by rwa [smul_eq_mul, mul_one]
  have key := ProjHom.corr_fromOfGlobalSections' (grading A N) φ hφ one_pos (X_mem z) ⊤ hV h t a ha'
  rw [hz, map_one, one_pow, mul_one, ProjHom.corr_apply, ProjHom.ι_appTop_eq] at key
  have key' := (⊤ : O.Opens).topIso.commRingCatIsoToRingEquiv.symm.injective key
  rw [chartHom_of_mem z ha]
  refine key'.trans ?_
  rw [show (homOfLE (le_top : (⊤ : O.Opens) ≤ ⊤)).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl

lemma appLE_congr_hom {X Z : Scheme.{u}} {g g' : X ⟶ Z} (hg : g = g') {U : Z.Opens}
    (e : ⊤ ≤ g ⁻¹ᵁ U) (e' : ⊤ ≤ g' ⁻¹ᵁ U) (s : Γ(Z, U)) :
    g.appLE U ⊤ e s = g'.appLE U ⊤ e' s := by
  subst hg
  rfl

variable (A)
variable {n m : ℕ}

abbrev segreChart (k : Fin (n + 1)) (l : Fin (m + 1)) :
    (projectiveSpace A (n * m + n + m)).Opens :=
  Proj.basicOpen (grading A _) (X (segreIndex n m (k, l)))

def segreZeta (k : Fin (n + 1)) (l : Fin (m + 1)) (a : Fin (n + 1)) (b : Fin (m + 1)) :
    Γ(segreChart A k l, ⊤) :=
  (segreChart A k l).ι.appLE (segreChart A k l) ⊤ (Scheme.Opens.ι_preimage_self _).ge
    (chartHom (segreIndex n m (k, l)) (X (segreIndex n m (a, b))))

lemma segreZeta_self (k : Fin (n + 1)) (l : Fin (m + 1)) : segreZeta A k l k l = 1 := by
  rw [segreZeta, chartHom_X_self, map_one]

def segreChartConst (k : Fin (n + 1)) (l : Fin (m + 1)) : A →+* Γ(segreChart A k l, ⊤) :=
  ((segreChart A k l).ι.appLE (segreChart A k l) ⊤ (Scheme.Opens.ι_preimage_self _).ge).hom.comp
    ((chartHom (segreIndex n m (k, l))).comp C)

def retrRing₁ (k : Fin (n + 1)) (l : Fin (m + 1)) :
    MvPolynomial (Fin (n + 1)) A →+* Γ(segreChart A k l, ⊤) :=
  eval₂Hom (segreChartConst A k l) fun a => segreZeta A k l a l

def retrRing₂ (k : Fin (n + 1)) (l : Fin (m + 1)) :
    MvPolynomial (Fin (m + 1)) A →+* Γ(segreChart A k l, ⊤) :=
  eval₂Hom (segreChartConst A k l) fun b => segreZeta A k l k b

lemma retrRing₁_irrelevant (k : Fin (n + 1)) (l : Fin (m + 1)) :
    (HomogeneousIdeal.irrelevant (grading A n)).toIdeal.map (retrRing₁ A k l) = ⊤ :=
  map_irrelevant_eq_top _ k (by rw [retrRing₁, eval₂Hom_X', segreZeta_self]; exact isUnit_one)

lemma retrRing₂_irrelevant (k : Fin (n + 1)) (l : Fin (m + 1)) :
    (HomogeneousIdeal.irrelevant (grading A m)).toIdeal.map (retrRing₂ A k l) = ⊤ :=
  map_irrelevant_eq_top _ l (by rw [retrRing₂, eval₂Hom_X', segreZeta_self]; exact isUnit_one)

def segreRetr (k : Fin (n + 1)) (l : Fin (m + 1)) : (segreChart A k l).toScheme ⟶ prodP A n m :=
  pullback.lift
    (Proj.fromOfGlobalSections (grading A n) (retrRing₁ A k l) (retrRing₁_irrelevant A k l))
    (Proj.fromOfGlobalSections (grading A m) (retrRing₂ A k l) (retrRing₂_irrelevant A k l)) (by
      rw [fromOfGlobalSections_toSpecBase, fromOfGlobalSections_toSpecBase]
      congr 3
      ext r
      simp [retrRing₁, retrRing₂])

lemma segreRetr_preimage (k : Fin (n + 1)) (l : Fin (m + 1)) :
    segreRetr A k l ⁻¹ᵁ segreOpen A k l = ⊤ := by
  rw [segreOpen, Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    segreRetr, pullback.lift_fst, pullback.lift_snd,
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos (X_mem k),
    Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos (X_mem l),
    retrRing₁, retrRing₂, eval₂Hom_X', eval₂Hom_X', segreZeta_self,
    Scheme.basicOpen_of_isUnit _ isUnit_one, top_inf_eq]

lemma ι_segre_preimage_segreChart (k : Fin (n + 1)) (l : Fin (m + 1)) :
    ((segreOpen A k l).ι ≫ segre A n m) ⁻¹ᵁ segreChart A k l = ⊤ := by
  rw [ι_segre, segreLocal, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ one_pos (X_mem _),
    segreRing_X, segreU_self, segreV_self, mul_one]
  exact Scheme.basicOpen_of_isUnit _ isUnit_one

lemma preimage_segreChart (k : Fin (n + 1)) (l : Fin (m + 1)) :
    segre A n m ⁻¹ᵁ segreChart A k l = segreOpen A k l := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨⟨i, j⟩, hij⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show x ∈ ⨆ c : Fin (n + 1) × Fin (m + 1), segreOpen A c.1 c.2 by
        rw [iSup_segreOpen]; trivial)
    have hx' : (⟨x, hij⟩ : segreOpen A i j) ∈ (segreOpen A i j).toScheme.basicOpen
        (segreRing A i j (X (segreIndex n m (k, l)))) := by
      rw [← Proj.fromOfGlobalSections_preimage_basicOpen _ _ (segreRing_irrelevant A i j) one_pos
        (X_mem _), ← segreLocal, ← ι_segre]
      exact hx
    rw [segreRing_X, Scheme.basicOpen_mul, segreU, segreV, Scheme.basicOpen_appLE,
      Scheme.basicOpen_appLE, basicOpen_chartHom_X, basicOpen_chartHom_X] at hx'
    exact ⟨hx'.1.2.2, hx'.2.2.2⟩
  · have : (⟨x, hx⟩ : segreOpen A k l) ∈
        ((segreOpen A k l).ι ≫ segre A n m) ⁻¹ᵁ segreChart A k l := by
      rw [ι_segre_preimage_segreChart]
      trivial
    exact this

lemma const_compat (k : Fin (n + 1)) (l : Fin (m + 1)) (V : (prodP A n m).Opens)
    (hk : V ≤ pullback.fst (toSpecBase A n) (toSpecBase A m) ⁻¹ᵁ Proj.basicOpen (grading A n) (X k))
    (hl : V ≤ pullback.snd (toSpecBase A n) (toSpecBase A m) ⁻¹ᵁ Proj.basicOpen (grading A m) (X l))
    (r : A) :
    (V.ι ≫ pullback.fst (toSpecBase A n) (toSpecBase A m)).appLE _ ⊤
        (top_le_preimage_ι_comp _ _ hk) (chartHom k (C r)) =
      (V.ι ≫ pullback.snd (toSpecBase A n) (toSpecBase A m)).appLE _ ⊤
        (top_le_preimage_ι_comp _ _ hl) (chartHom l (C r)) := by
  have e₁ := eq_fromOfGlobalSections_of_preimage_eq_top
    (V.ι ≫ pullback.fst (toSpecBase A n) (toSpecBase A m)) k
    (top_unique (top_le_preimage_ι_comp _ _ hk))
  have e₂ := eq_fromOfGlobalSections_of_preimage_eq_top
    (V.ι ≫ pullback.snd (toSpecBase A n) (toSpecBase A m)) l
    (top_unique (top_le_preimage_ι_comp _ _ hl))
  have h : (V.ι ≫ pullback.fst (toSpecBase A n) (toSpecBase A m)) ≫ toSpecBase A n =
      (V.ι ≫ pullback.snd (toSpecBase A n) (toSpecBase A m)) ≫ toSpecBase A m := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  conv_lhs at h => rw [e₁]
  conv_rhs at h => rw [e₂]
  rw [fromOfGlobalSections_toSpecBase, fromOfGlobalSections_toSpecBase] at h
  have key : ∀ φ : A →+* Γ(V, ⊤), (Scheme.ΓSpecIso (.of A)).inv ≫
      (V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)).appTop = CommRingCat.ofHom φ := by
    intro φ
    have := ProjHom.specCorr_comp V.toScheme.toSpecΓ
      (CommRingCat.ofHom φ : CommRingCat.of A ⟶ Γ(V.toScheme, ⊤))
    rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id] at this
    exact this.trans (Category.comp_id _)
  have h' := congrArg (fun g => (Scheme.ΓSpecIso (.of A)).inv ≫ Scheme.Hom.appTop g) h
  have hφ := (key _).symm.trans (h'.trans (key _))
  exact congr(($hφ).hom r)

lemma segre_resLE_appTop_chart (k : Fin (n + 1)) (l : Fin (m + 1))
    {t : ℕ} {p : MvPolynomial (Fin (n * m + n + m + 1)) A} (hp : p ∈ grading A _ t) :
    ((segre A n m).resLE (segreChart A k l) (segreOpen A k l) (preimage_segreChart A k l).ge).appTop
      ((segreChart A k l).ι.appLE (segreChart A k l) ⊤ (Scheme.Opens.ι_preimage_self _).ge
        (chartHom (segreIndex n m (k, l)) p)) = segreRing A k l p := by
  have hσ : (segre A n m).resLE (segreChart A k l) (segreOpen A k l)
      (preimage_segreChart A k l).ge ≫ (segreChart A k l).ι = segreLocal A k l := by
    rw [Scheme.Hom.resLE_comp_ι, ι_segre]
  have hL : ⊤ ≤ segreLocal A k l ⁻¹ᵁ segreChart A k l := by
    rw [← ι_segre]
    exact (ι_segre_preimage_segreChart A k l).ge
  rw [appTop_appLE _ _ _ (by rw [hσ]; exact hL), appLE_congr_hom hσ _ hL]
  refine appLE_fromOfGlobalSections_chartHom (segreRing A k l) (segreRing_irrelevant A k l) _ ?_ hL hp
  rw [segreRing_X, segreU_self, segreV_self, mul_one]

lemma segre_resLE_comp_segreRetr (k : Fin (n + 1)) (l : Fin (m + 1)) :
    (segre A n m).resLE (segreChart A k l) (segreOpen A k l) (preimage_segreChart A k l).ge ≫
      segreRetr A k l = (segreOpen A k l).ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, segreRetr, pullback.lift_fst,
      ProjHom.comp_fromOfGlobalSections _ _ (fun a => X a) (fun _ => 1) (fun _ => one_pos)
        (fun a => X_mem a) iSup_basicOpen_X,
      eq_fromOfGlobalSections_of_preimage_eq_top
        ((segreOpen A k l).ι ≫ pullback.fst (toSpecBase A n) (toSpecBase A m)) k
        (top_unique (top_le_preimage_ι_comp _ _ inf_le_left))]
    congr 1
    ext r
    · simp only [RingHom.comp_apply, retrRing₁, eval₂Hom_C, segreChartConst]
      rw [segre_resLE_appTop_chart A k l (isHomogeneous_C _ r), segreRing, eval₂Hom_C]
      rfl
    · simp only [RingHom.comp_apply, retrRing₁, eval₂Hom_X', segreZeta]
      rw [segre_resLE_appTop_chart A k l (X_mem _), segreRing_X, segreV_self, mul_one]
      rfl
  · rw [Category.assoc, segreRetr, pullback.lift_snd,
      ProjHom.comp_fromOfGlobalSections _ _ (fun b => X b) (fun _ => 1) (fun _ => one_pos)
        (fun b => X_mem b) iSup_basicOpen_X,
      eq_fromOfGlobalSections_of_preimage_eq_top
        ((segreOpen A k l).ι ≫ pullback.snd (toSpecBase A n) (toSpecBase A m)) l
        (top_unique (top_le_preimage_ι_comp _ _ inf_le_right))]
    congr 1
    ext r
    · simp only [RingHom.comp_apply, retrRing₂, eval₂Hom_C, segreChartConst]
      rw [segre_resLE_appTop_chart A k l (isHomogeneous_C _ r), segreRing, eval₂Hom_C]
      exact const_compat A k l _ inf_le_left inf_le_right r
    · simp only [RingHom.comp_apply, retrRing₂, eval₂Hom_X', segreZeta]
      rw [segre_resLE_appTop_chart A k l (X_mem _), segreRing_X, segreU_self, one_mul]
      rfl


variable (n m) in
instance isClosedImmersion_segre : IsClosedImmersion (segre A n m) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion)
    (fun c => Proj.basicOpen (grading A (n * m + n + m)) (X c)) iSup_basicOpen_X]
  intro c
  obtain ⟨⟨k, l⟩, rfl⟩ := (segreIndex n m).surjective c
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  suffices key : ∀ (V : (prodP A n m).Opens) (_ : V = segreOpen A k l)
      (e : V ≤ segre A n m ⁻¹ᵁ segreChart A k l),
      IsClosedImmersion ((segre A n m).resLE (segreChart A k l) V e) from
    key _ (preimage_segreChart A k l) le_rfl
  rintro _ rfl _
  have hrange : Set.range (segreRetr A k l) ⊆ Set.range (segreOpen A k l).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : y ∈ segreRetr A k l ⁻¹ᵁ segreOpen A k l := by
      rw [segreRetr_preimage]
      trivial
    exact this
  have : IsAffine (segreChart A k l).toScheme :=
    Proj.isAffineOpen_basicOpen _ _ (X_mem _) one_pos
  have hσρ : (segre A n m).resLE (segreChart A k l) (segreOpen A k l)
      (preimage_segreChart A k l).ge ≫
        IsOpenImmersion.lift (segreOpen A k l).ι (segreRetr A k l) hrange = 𝟙 _ := by
    rw [← cancel_mono (segreOpen A k l).ι, Category.assoc, IsOpenImmersion.lift_fac,
      Category.id_comp]
    exact segre_resLE_comp_segreRetr A k l
  have : IsClosedImmersion ((segre A n m).resLE (segreChart A k l) (segreOpen A k l)
      (preimage_segreChart A k l).ge ≫
        IsOpenImmersion.lift (segreOpen A k l).ι (segreRetr A k l) hrange) := by
    rw [hσρ]
    infer_instance
  exact IsClosedImmersion.of_comp _ (IsOpenImmersion.lift (segreOpen A k l).ι (segreRetr A k l) hrange)

end ProjSpace
end
end GroundTheory.Arith.SchemeCoh
end
