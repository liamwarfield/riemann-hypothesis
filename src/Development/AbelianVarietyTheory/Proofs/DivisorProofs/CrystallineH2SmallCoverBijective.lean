module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevIffIsEtLevOver
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoMorphismRestrictOfLocalDominantSections
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.TransportC

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineH2SmallCoverBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalization
open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.ThickLoc

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}}
  {s : X ⟶ Sp R} (T : Thick κ s) (b : T.B)

abbrev locJ : Ideal (Localization.Away b) := T.J.map (algebraMap T.B (Localization.Away b))

def locφ₀ : T.B₀ →+* Localization.Away b ⧸ locJ T b :=
  T.π.liftOfSurjective T.surj
    ⟨(Ideal.Quotient.mk (locJ T b)).comp (algebraMap T.B (Localization.Away b)), fun x hx ↦ by
      rw [RingHom.mem_ker] at hx ⊢
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ((T.ker x).1 hx))⟩

theorem locφ₀_π (x : T.B) :
    locφ₀ T b (T.π x) = Ideal.Quotient.mk (locJ T b) (algebraMap T.B (Localization.Away b) x) := by
  unfold locφ₀
  exact RingHom.liftOfSurjective_comp_apply _ _ _ x

@[reducible] def loc : Thick κ s where
  B := Localization.Away b
  J := locJ T b
  δ := DPLoc.dp (Submonoid.powers b) T.δ
  nil := DPLoc.isNilDP _ _ T.nil
  dp := by
    rw [IsScalarTower.algebraMap_eq R T.B (Localization.Away b)]
    exact IsDPMorphism.comp _ (DPLoc.isDPMorphism _ T.δ) T.dp
  B₀ := Localization.Away b ⧸ locJ T b
  π := Ideal.Quotient.mk _
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := spMap (locφ₀ T b) ≫ T.x
  w := by
    rw [Category.assoc, T.w, ← Cris.spMap_comp]
    congr 1
    ext r
    simp only [RingHom.comp_apply, locφ₀_π]
    rw [← IsScalarTower.algebraMap_apply]

def toLoc : T ⟶ loc T b where
  φ := IsScalarTower.toAlgHom R T.B (Localization.Away b)
  φ₀ := locφ₀ T b
  comm := locφ₀_π T b
  dp := DPLoc.isDPMorphism (S := Localization.Away b) (Submonoid.powers b) T.δ
  pt := rfl

variable {T b} {S : Thick κ s} (u : T ⟶ S) (hu : IsUnit (u.φ b))

def liftφ : Localization.Away b →ₐ[R] S.B where
  toRingHom := IsLocalization.Away.lift b (g := (u.φ : T.B →+* S.B)) hu
  commutes' r := by
    rw [IsScalarTower.algebraMap_apply R T.B (Localization.Away b)]
    exact (IsLocalization.Away.lift_eq b (g := (u.φ : T.B →+* S.B)) hu _).trans (u.φ.commutes r)

theorem liftφ_algebraMap (x : T.B) :
    liftφ u hu (algebraMap T.B (Localization.Away b) x) = u.φ x := by
  show IsLocalization.Away.lift b (g := (u.φ : T.B →+* S.B)) hu
      (algebraMap T.B (Localization.Away b) x) = u.φ x
  exact IsLocalization.Away.lift_eq b hu x

theorem liftφ_dp : IsDPMorphism (DPLoc.dp (S := Localization.Away b) (Submonoid.powers b) T.δ) S.δ
    (liftφ u hu : Localization.Away b →+* S.B) := by
  have h : (liftφ u hu : Localization.Away b →+* S.B).comp (algebraMap T.B (Localization.Away b)) =
      (u.φ : T.B →+* S.B) :=
    RingHom.ext fun x => liftφ_algebraMap u hu x
  exact DPLoc.isDPMorphism_of_comp (S := Localization.Away b) (Submonoid.powers b) T.δ S.δ _
    (by rw [h]; exact u.dp)

def liftφ₀ : Localization.Away b ⧸ locJ T b →+* S.B₀ :=
  Ideal.Quotient.lift _ (S.π.comp (liftφ u hu : Localization.Away b →+* S.B)) fun _ ha ↦
    (S.ker _).2 ((liftφ_dp u hu).1 (Ideal.mem_map_of_mem _ ha))

def lift : loc T b ⟶ S where
  φ := liftφ u hu
  φ₀ := liftφ₀ u hu
  comm _ := rfl
  dp := liftφ_dp u hu
  pt := by
    have : (liftφ₀ u hu).comp (locφ₀ T b) = u.φ₀ := RingHom.ext fun x ↦ by
      obtain ⟨x, rfl⟩ := T.surj x
      rw [RingHom.comp_apply, locφ₀_π, u.comm, ← liftφ_algebraMap u hu]
      rfl
    change spMap (liftφ₀ u hu) ≫ spMap (locφ₀ T b) ≫ T.x = S.x
    rw [← Category.assoc, ← Cris.spMap_comp, this, u.pt]

theorem exists_localization : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (s : X ⟶ Sp R) (T : Thick κ s) (b : T.B), ∃ (T' : Thick κ s) (l : T ⟶ T'), IsUnit (l.φ b) ∧ (∀ y : T'.B, ∃ (n : ℕ) (x : T.B), y * l.φ b ^ n = l.φ x) ∧ (∀ x : T.B, l.φ x = 0 → ∃ n : ℕ, b ^ n * x = 0) ∧ ∀ (S : Thick κ s) (u : T ⟶ S), IsUnit (u.φ b) → ∃! v : T' ⟶ S, l ≫ v = u := by
  intro R _ I κ X s T b
  refine ⟨loc T b, toLoc T b, ?_, ?_, ?_, ?_⟩
  · exact IsLocalization.Away.algebraMap_isUnit b
  · intro y
    obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers b) y
    obtain ⟨n, hn⟩ := m.2
    refine ⟨n, a, ?_⟩
    change y * algebraMap T.B (Localization.Away b) b ^ n = algebraMap T.B (Localization.Away b) a
    rw [← map_pow, show b ^ n = ↑m from hn]
    exact hm
  · intro x hx
    change algebraMap T.B (Localization.Away b) x = 0 at hx
    obtain ⟨⟨_, n, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers b) (Localization.Away b) x).1 hx
    exact ⟨n, hm⟩
  · intro S u hu
    refine ⟨lift u hu, ?_, ?_⟩
    · apply Thick.Hom.ext'
      ext c
      simp only [Thick.comp_φ]
      exact liftφ_algebraMap u hu c
    · intro v hv
      have h : (v.φ : Localization.Away b →+* S.B).comp (algebraMap T.B (Localization.Away b)) =
          (liftφ u hu : Localization.Away b →+* S.B).comp (algebraMap T.B (Localization.Away b)) := by
        ext c
        have hc : (toLoc T b ≫ v).φ c = u.φ c := by rw [hv]
        simp only [Thick.comp_φ] at hc
        show v.φ (algebraMap T.B (Localization.Away b) c) =
          liftφ u hu (algebraMap T.B (Localization.Away b) c)
        exact hc.trans (liftφ_algebraMap u hu c).symm
      apply Thick.Hom.ext'
      exact AlgHom.ext fun y ↦
        RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers b) h) y

end GlobalTheory.ThickLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfMemSmallCover
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
private theorem isNilpotent_of_mem_of_isNilDP {B : Type} [CommRing B]
    {J : Ideal B} (δ : DividedPowers J) (hδ : _root_.GlobalTheory.Cris.IsNilDP δ) {x : B} (hx : x ∈ J) :
    IsNilpotent x := by
  obtain ⟨N, hN⟩ := hδ
  refine ⟨N, ?_⟩
  have h := hN [(N, x)] (by simpa using hx) (by simp)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [← δ.factorial_mul_dpow_eq_pow hx, h, mul_zero]


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
theorem _root_.GlobalTheory.Cris.exists_finite_small_cover (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (K : Type) (U : K → X.Opens) (hU : ⨆ i, U i = ⊤)
    (T : _root_.GlobalTheory.Cris.Thick κ s) : ∃ (n : ℕ) (b : Fin n → T.B),
      Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : _root_.GlobalTheory.Cris.Thick κ s) (u : T ⟶ S),
        IsUnit (u.φ (b i)) → _root_.GlobalTheory.Cris.IsSmall κ s U S := by
  classical
  let G : Set T.B₀ := {f | ∃ k, ∀ p : PrimeSpectrum T.B₀,
    f ∉ p.asIdeal → T.x.base p ∈ U k}
  have hG : Ideal.span G = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    let p : PrimeSpectrum T.B₀ := ⟨m, hm.isPrime⟩
    have hp : T.x.base p ∈ (⨆ i, U i : X.Opens) := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := (TopologicalSpace.Opens.mem_iSup).1 hp
    obtain ⟨_, ⟨f, rfl⟩, hpf, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (a := p) (u := (fun q : PrimeSpectrum T.B₀ ↦ T.x.base q) ⁻¹' (U k))
        hk ((U k).isOpen.preimage T.x.continuous)
    exact hpf (hle (Ideal.subset_span ⟨k, fun q hq ↦ hsub hq⟩))
  obtain ⟨t, htG, htspan⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  let e := t.equivFin
  have hlift : ∀ i : Fin t.card, ∃ y, T.π y = (e.symm i : T.B₀) :=
    fun i ↦ T.surj _
  choose b hb using hlift
  refine ⟨t.card, b, ?_, ?_⟩
  · have hmap : Ideal.map T.π (Ideal.span (Set.range b)) = ⊤ := by
      rw [Ideal.map_span, ← htspan]
      congr 1
      ext f
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        rw [hb]
        exact (e.symm i).2
      · intro hf
        exact ⟨b (e ⟨f, hf⟩), ⟨_, rfl⟩, by rw [hb, Equiv.symm_apply_apply]⟩
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective _ T.surj).1
      (hmap ▸ Submodule.mem_top : (1 : T.B₀) ∈ _)
    have hJ : 1 - y ∈ T.J := by
      rw [← T.ker, map_sub, map_one, hy1, sub_self]
    have hunit : IsUnit y := by
      have := (isNilpotent_of_mem_of_isNilDP _ T.nil hJ).isUnit_one_sub
      simpa using this
    exact Ideal.eq_top_of_isUnit_mem _ hy hunit
  · intro i S u hu
    obtain ⟨k, hk⟩ := htG (e.symm i).2
    refine ⟨k, fun q _ ↦ ?_⟩
    show S.x.base q ∈ U k
    rw [← u.pt, Scheme.Hom.comp_apply]
    apply hk
    intro hq
    have h1 : u.φ₀ (e.symm i : T.B₀) ∈ q.asIdeal := hq
    rw [← hb, u.comm] at h1
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (hu.map S.π))

end GlobalTheory.Cris
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineH2SmallCoverBijective
open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

theorem small_descent_H2_bijective (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (s : X ⟶ Sp R) (K : Type) (U : K → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Function.Bijective (CoefMap.restrict (O κ s) (IsSmall κ s U).ι).pull2 := by
  refine GlobalTheory.CatCoh.Desc.pull2_bijective (O κ s) ?_ (IsSmall κ s U) ?_ ?_
  · intro T b
    obtain ⟨T', l, h1, h2, h3, h4⟩ := GlobalTheory.ThickLoc.exists_localization R I κ X s T b
    exact ⟨T', l, by simpa only [mp_O] using h1, by simpa only [mp_O] using h2,
      by simpa only [mp_O] using h3, by simpa only [mp_O] using h4⟩
  · rintro S S' φ ⟨i, hi⟩
    exact ⟨i, GlobalTheory.Cris.Thick.Hom.le_preimage φ hi⟩
  · intro T
    obtain ⟨n, b, hb, h⟩ := exists_finite_small_cover R I κ X s K U hU T
    exact ⟨n, b, hb, fun i S u hu => h i S u (by simpa only [mp_O] using hu)⟩

end GlobalTheory.Cris
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineH2SmallCoverBijectiveStatement
open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_H2_small_cover_bijective : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (s : X ⟶ Sp R) (K : Type) (U : K → X.Opens), ⨆ i, U i = ⊤ → Function.Bijective (CoefMap.restrict (O κ s) (IsSmall κ s U).ι).pull2 := by
  first | exact @GlobalTheory.Cris.small_descent_H2_bijective | exact GlobalTheory.Cris.small_descent_H2_bijective | (intros; apply GlobalTheory.Cris.small_descent_H2_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourFRLeMinGOfSizeG
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem four_f_r_le_k_pow_eight (R : Ranks) : 4 * R.f * R.r ≤ R.k ^ 8 := by
  have hf : R.f ≤ R.k := by
    unfold Ranks.f Ranks.n
    exact R.f_le_k
  have h2 := R.two_le_m
  have h3 := R.m_add_three_le_k
  have hr : R.r ≤ 2 * R.k := by
    unfold Ranks.r
    omega
  have hk : 2 ≤ R.k := by omega
  have h6 : 8 ≤ R.k ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left hk 6)
  calc 4 * R.f * R.r ≤ 4 * R.k * (2 * R.k) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hf) hr
    _ = 8 * R.k ^ 2 := by ring
    _ ≤ R.k ^ 6 * R.k ^ 2 := Nat.mul_le_mul_right _ h6
    _ = R.k ^ 8 := by ring

theorem four_f_r_le_min_g_of_sizeG {D : D7} (L : SizeData₂ D) (h : SizeG L) : Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D := by
  have hb : (1 : ℝ) ≤ L.sc.b := by
    unfold Scale.b Scale.L
    exact Real.one_le_exp (Real.rpow_nonneg (le_trans zero_le_one L.sc.one_lt_alt.le) _)
  have key : ∀ i : Fin 2, 4 * D.R.f * D.R.r ≤ D.host.g i := by
    intro i
    have h1 := (h i i).1
    have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have h2 : (D.R.k : ℝ) ^ 8 ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 :=
      pow_le_pow_left₀ hk (le_mul_of_one_le_right hk hb) 8
    have h3 : D.R.k ^ 8 ≤ D.host.g i := by exact_mod_cast h2.trans h1
    exact (four_f_r_le_k_pow_eight D.R).trans h3
  unfold Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound
  exact le_min (key 0) (key 1)

theorem four_f_r_le_min_g_family : ∀ (eps : ℝ) (Fm : FamP eps), ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x →
    ∀ i : Fm.Ix x, Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound (Fm.D x i) := by
  intro eps Fm
  refine ⟨0, fun x _ hx i => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := Fm.sizes x hx i
  exact four_f_r_le_min_g_of_sizeG _ hG

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalRingMapIndEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalRingMapIndEtale
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.LocGlobRing

noncomputable def pbIso (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    pullback g (Spec.map (CommRingCat.ofHom (algebraMap A O))) ≅ Spec (CommRingCat.of (O ⊗[A] X)) :=
  pullback.congrHom hg rfl ≪≫ pullbackSymmetry _ _ ≪≫ pullbackSpecIso A O X

theorem pbIso_inv_fst (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    (pbIso A X O g hg).inv ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : X →ₐ[A] O ⊗[A] X).toRingHom) := by
  subst hg
  simp [pbIso, pullback.congrHom_inv, pullbackSpecIso_inv_snd]

theorem pbIso_inv_snd (A X O : Type) [CommRing A] [CommRing X] [CommRing O] [Algebra A X] [Algebra A O]
    (g : Spec (CommRingCat.of X) ⟶ Spec (CommRingCat.of A)) (hg : g = Spec.map (CommRingCat.ofHom (algebraMap A X))) :
    (pbIso A X O g hg).inv ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : O →+* O ⊗[A] X)) := by
  subst hg
  simp [pbIso, pullback.congrHom_inv, pullbackSpecIso_inv_fst]

end GlobalTheory.LocGlobRing

namespace GlobalTheory.LocGlobRing

theorem square (A B C O : Type) [CommRing A] [CommRing B] [CommRing C] [CommRing O] [Algebra A B] [Algebra A C] [Algebra A O]
    (φ : B →ₐ[A] C)
    (hC : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = Spec.map (CommRingCat.ofHom (algebraMap A C)))
    (h₁ h₂) :
    (pbIso A C O _ hC).inv ≫ pullback.map (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A O))) (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A O))) (Spec.map (CommRingCat.ofHom φ.toRingHom)) (𝟙 _) (𝟙 _) h₁ h₂ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A O) φ).toRingHom) ≫ (pbIso A B O _ rfl).inv := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pbIso_inv_fst, Category.assoc, pbIso_inv_fst,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, pbIso_inv_snd, Category.assoc, pbIso_inv_snd,
      ← Spec.map_comp]
    congr 1
    ext x
    simp

end GlobalTheory.LocGlobRing

theorem GlobalTheory.LocGlobRing.main : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (φ : B →ₐ[A] C), (∀ (O : Type) [CommRing O] [Algebra A O], SH O → IndEt A O → Eqv R (spMap (Algebra.TensorProduct.map (AlgHom.id A O) φ).toRingHom) F) → Eqv R (spMap φ.toRingHom) F := by
  intro R _ F hF A B C _ _ _ _ _ φ hyp
  have hC : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp
  refine GlobalTheory.T.etaleEquivalence_scheme_of_strictlyHenselian_stalks R F hF (Spec (CommRingCat.of C)) (Spec (CommRingCat.of B)) (Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) (Spec.map (CommRingCat.ofHom (algebraMap A B))) ?_
  intro O _ s hs
  obtain ⟨inst, hSH, hInd, rfl⟩ := GlobalTheory.T.isIndEtaleAlgebra_of_strictlyHenselianEtaleStalk_affine A O s hs
  have h := @hyp O _ inst hSH hInd
  have eb := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  rw [← Iso.hom_inv_id_assoc (GlobalTheory.LocGlobRing.pbIso A C O _ hC) (pullback.map _ _ _ _ _ _ _ _ _),
    GlobalTheory.LocGlobRing.square A B C O φ hC, Functor.map_comp, Functor.map_comp]
  exact (eb.2.1 _ _ _ _ _).1 (eb.1 _ _ _ inferInstance) ((eb.2.1 _ _ _ _ _).1 h (eb.1 _ _ _ inferInstance))
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalRingMapIndEtaleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C] (φ : B →ₐ[A] C), (∀ (O : Type) [CommRing O] [Algebra A O], SH O → IndEt A O → Eqv R (spMap (Algebra.TensorProduct.map (AlgHom.id A O) φ).toRingHom) F) → Eqv R (spMap φ.toRingHom) F := by
  first | (exact @GlobalTheory.LocGlobRing.main) | (exact GlobalTheory.LocGlobRing.main) | (intros; apply GlobalTheory.LocGlobRing.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtIteratedFDerivSliceAndFderiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtIteratedFDerivSliceAndFderiv
open Filter Topology

namespace GlobalTheory

open Filter Topology in
private lemma iteratedFDeriv_slice_eq_compContinuousLinearMap_inl {E F : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (H : E × F → ℂ) {w : F}
    (hH : AnalyticAt ℂ H (0, w)) (k : ℕ) :
    iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 =
      (iteratedFDeriv ℂ k H (0, w)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inl ℂ E F) := by
  obtain ⟨U, hU, hUo, hwU⟩ := eventually_nhds_iff.1 hH.eventually_analyticAt
  set s : Set (E × F) := (fun q ↦ q + (0, w)) ⁻¹' U with hs
  have hso : IsOpen s := hUo.preimage (continuous_id.add continuous_const)
  have h0s : (0 : E × F) ∈ s := by simpa [hs] using hwU
  have hf : AnalyticOnNhd ℂ (fun q : E × F ↦ H (q + (0, w))) s := fun q hq ↦
    (hU _ hq).comp (f := fun q : E × F ↦ q + (0, w)) (analyticAt_id.add analyticAt_const)
  have hslice : (fun z : E ↦ H (z, w)) =
      (fun q : E × F ↦ H (q + (0, w))) ∘ ContinuousLinearMap.inl ℂ E F := by
    ext z; simp
  have hpre : IsOpen (ContinuousLinearMap.inl ℂ E F ⁻¹' s) :=
    hso.preimage (ContinuousLinearMap.continuous _)
  have h0s' : ContinuousLinearMap.inl ℂ E F 0 ∈ s := by rw [map_zero]; exact h0s
  have h0pre : (0 : E) ∈ ContinuousLinearMap.inl ℂ E F ⁻¹' s := h0s'
  rw [hslice, ← iteratedFDerivWithin_of_isOpen k hpre h0pre,
    ContinuousLinearMap.iteratedFDerivWithin_comp_right _ (hf.contDiffOn (n := k) hso.uniqueDiffOn)
      hso.uniqueDiffOn hpre.uniqueDiffOn h0s' le_rfl,
    iteratedFDerivWithin_of_isOpen k hso h0s', iteratedFDeriv_comp_add_right]
  simp

open Filter Topology in
private lemma fin_snoc_eq_cons_comp_finRotate {X : Type} {k : ℕ} (u : Fin k → X) (a : X) :
    (Fin.snoc u a : Fin (k + 1) → X) = Fin.cons a u ∘ finRotate (k + 1) := by
  funext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp
  · simp


open Filter Topology in
theorem _root_.GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv :
    ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (H : E × F → ℂ) (w₀ : F) (k : ℕ) (v : Fin k → E), AnalyticAt ℂ H (0, w₀) → AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ ∧ ∀ e : F, fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ e = iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ H (z, w₀) (0, e)) 0 v := by
  intro E F _ _ _ _ _ _ H w₀ k v hH
  set u : Fin k → E × F := fun i ↦ (v i, 0) with hu
  have hev : ∀ᶠ w in 𝓝 w₀, AnalyticAt ℂ H (0, w) :=
    ((continuous_const.prodMk continuous_id).tendsto w₀).eventually hH.eventually_analyticAt
  have heq : (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) =ᶠ[𝓝 w₀]
      fun w ↦ iteratedFDeriv ℂ k H (0, w) u :=
    hev.mono fun w hw ↦ by dsimp only; rw [iteratedFDeriv_slice_eq_compContinuousLinearMap_inl H hw k]; rfl
  obtain ⟨U, hU, hUo, hwU⟩ := eventually_nhds_iff.1 hH.eventually_analyticAt
  have hiter : AnalyticAt ℂ (iteratedFDeriv ℂ k H) (0, w₀) :=
    (AnalyticOnNhd.iteratedFDeriv_of_isOpen hU hUo k) _ hwU
  have hA : AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k H (0, w) u) w₀ :=
    ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).analyticAt _).comp
      (hiter.comp (f := fun w : F ↦ ((0 : E), w)) (analyticAt_const.prod analyticAt_id))
  refine ⟨hA.congr heq.symm, fun e ↦ ?_⟩
  have hD : HasFDerivAt (fun w ↦ iteratedFDeriv ℂ k H (0, w) u)
      ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).comp
        ((fderiv ℂ (iteratedFDeriv ℂ k H) (0, w₀)).comp (ContinuousLinearMap.inr ℂ E F))) w₀ :=
    (ContinuousMultilinearMap.apply ℂ (fun _ : Fin k ↦ E × F) ℂ u).hasFDerivAt.comp w₀
      (hiter.differentiableAt.hasFDerivAt.comp w₀ (hasFDerivAt_prodMk_right (0 : E) w₀))
  have hG : AnalyticAt ℂ (fun y ↦ fderiv ℂ H y (0, e)) (0, w₀) :=
    ((ContinuousLinearMap.apply ℂ ℂ ((0 : E), e)).analyticAt _).comp hH.fderiv
  rw [heq.fderiv_eq, hD.fderiv, iteratedFDeriv_slice_eq_compContinuousLinearMap_inl _ hG k]
  have hcomp : (fun y ↦ fderiv ℂ H y (0, e)) =
      (ContinuousLinearMap.apply ℂ ℂ ((0 : E), e)) ∘ fderiv ℂ H := rfl
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_left _ (hH.fderiv.contDiffAt (n := k)) le_rfl]
  have hperm := (hH.contDiffAt (n := ⊤)).iteratedFDeriv_comp_perm (Fin.cons ((0 : E), e) u)
    (finRotate (k + 1))
  rw [← fin_snoc_eq_cons_comp_finRotate, iteratedFDeriv_succ_apply_right,
    iteratedFDeriv_succ_apply_left] at hperm
  simpa [u] using hperm.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtIteratedFDerivSliceAndFderivStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticAt_iteratedFDeriv_slice_and_fderiv_eq : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (H : E × F → ℂ) (w₀ : F) (k : ℕ) (v : Fin k → E), AnalyticAt ℂ H (0, w₀) → AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ ∧ ∀ e : F, fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ e = iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ H (z, w₀) (0, e)) 0 v := by
  first | exact @GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv | exact GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv | (intros; apply GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEqZeroOfSuccLe
open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem prod_eq_zero_of_succ_le {I : Type} {D : Type} [CommRing D] (N : ℕ) (t : I → D)
    (h : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (k : ℕ) (hk : N + 1 ≤ k) (s : Fin k → I) :
    ∏ a, t (s a) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Fin.prod_univ_add, h (fun a => s (Fin.castAdd j a)), zero_mul]

theorem taylor_eq_of_le : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (N' : ℕ), N ≤ N' → ∀ f : (I → ℂ) → ℂ, GlobalTheory.PeriodFamily.taylor N' t f = GlobalTheory.PeriodFamily.taylor N t f := by
  intro I _ _ D _ _ N t h N' hN f
  induction N', hN using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [← ih]
    unfold taylor
    rw [Finset.sum_range_succ _ (n + 1)]
    simp [prod_eq_zero_of_succ_le N t h (n + 1) (by omega)]

end GlobalTheory.PeriodFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedSubalgebraRestrict
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedSubalgebraRestrict
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RegAlg

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ U : A.left.Opens, (∀ a : ℂ, IsReg u.ex U fun _ => a) ∧ (∀ k k', IsReg u.ex U k → IsReg u.ex U k' → IsReg u.ex U (k + k') ∧ IsReg u.ex U (k - k') ∧ IsReg u.ex U (k * k')) ∧ (∀ k k', IsReg u.ex U k → (∀ z ∈ pre u.ex U, k' z = k z) → IsReg u.ex U k') ∧ (∀ V, V ≤ U → ∀ k, IsReg u.ex U k → IsReg u.ex V k) ∧ (∀ k, IsReg u.ex U k → DifferentiableOn ℂ k (pre u.ex U)) ∧ ∀ (n : ℕ) (k : Fin n → (Fin g → ℂ) → ℂ), (∀ i, IsReg u.ex U (k i)) → IsReg u.ex U (fun z => ∑ i, k i z) := by
  intro A _ g L u U
  refine ⟨fun a => ?_, fun k k' hk hk' => ?_, fun k k' hk he => ?_, fun V hV k hk => ?_, fun k hk => ?_, fun n k hk => ?_⟩
  · refine ⟨constFn A.hom U a, fun z hz => ?_⟩
    have hp : (u.ex z).left ≫ A.hom = 𝟙 _ := by
      simpa using Over.w (u.ex z)
    exact (GlobalTheory.valAt'_constFn (u.ex z).left A.hom hp U a hz).symm
  · obtain ⟨b, hb⟩ := hk
    obtain ⟨b', hb'⟩ := hk'
    refine ⟨⟨b + b', fun z hz => ?_⟩, ⟨b - b', fun z hz => ?_⟩, ⟨b * b', fun z hz => ?_⟩⟩
    · simp only [Pi.add_apply, CechPer.val, GlobalTheory.valAt'_add, hb z hz, hb' z hz]
    · simp only [Pi.sub_apply, CechPer.val, GlobalTheory.valAt'_sub, hb z hz, hb' z hz]
    · simp only [Pi.mul_apply, CechPer.val, GlobalTheory.valAt'_mul, hb z hz, hb' z hz]
  · obtain ⟨b, hb⟩ := hk
    exact ⟨b, fun z hz => (he z hz).trans (hb z hz)⟩
  · obtain ⟨b, hb⟩ := hk
    refine ⟨resG A.left hV b, fun z hz => ?_⟩
    have hzU : z ∈ pre u.ex U := GlobalTheory.top_le_preimage_mono _ hV hz
    rw [hb z hzU]
    exact (GlobalTheory.valAt'_res (u.ex z).left hV b hz).symm
  · obtain ⟨b, hb⟩ := hk
    exact (u.hol U b).2.congr fun z hz => hb z hz
  · choose b hb using hk
    refine ⟨∑ i, b i, fun z hz => ?_⟩
    simp only [CechPer.val, GlobalTheory.valAt'_sum]
    exact Finset.sum_congr rfl fun i _ => hb i z hz

end GlobalTheory.RegAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularOnOpenUniformisedSubalgebraRestrictStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularOnOpenUniformised_subalgebra_restrict : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ U : A.left.Opens, (∀ a : ℂ, IsReg u.ex U fun _ => a) ∧ (∀ k k', IsReg u.ex U k → IsReg u.ex U k' → IsReg u.ex U (k + k') ∧ IsReg u.ex U (k - k') ∧ IsReg u.ex U (k * k')) ∧ (∀ k k', IsReg u.ex U k → (∀ z ∈ pre u.ex U, k' z = k z) → IsReg u.ex U k') ∧ (∀ V, V ≤ U → ∀ k, IsReg u.ex U k → IsReg u.ex V k) ∧ (∀ k, IsReg u.ex U k → DifferentiableOn ℂ k (pre u.ex U)) ∧ ∀ (n : ℕ) (k : Fin n → (Fin g → ℂ) → ℂ), (∀ i, IsReg u.ex U (k i)) → IsReg u.ex U (fun z => ∑ i, k i z) := by
  first | exact @GlobalTheory.RegAlg.main | exact GlobalTheory.RegAlg.main | (intros; apply GlobalTheory.RegAlg.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealAffineOpenEqVanishingUniformisationP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealAffineOpenEqVanishingUniformisationP
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MaxPoints

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (U : A.left.Opens), IsAffineOpen U → ∀ m : Ideal Γ(A.left, U), m.IsMaximal →
      ∃ z ∈ pre u.ex U, ∀ b, b ∈ m ↔ val u.ex U b z = 0 := by
  intro A _ g L u hA U hU m hm
  haveI : Smooth A.hom := hA.smooth
  have hft : LocallyOfFiniteType A.hom := inferInstance
  let c : ℂ →+* Γ(A.left, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ A.hom.appLE ⊤ U (fun _ _ => trivial)).hom
  have hc : c.FiniteType := by
    have h1 : (A.hom.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType A.hom hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  letI : Algebra ℂ Γ(A.left, U) := c.toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(A.left, U) := hc
  haveI : IsJacobsonRing Γ(A.left, U) := isJacobsonRing_of_finiteType (A := ℂ)
  letI : Field (Γ(A.left, U) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (Γ(A.left, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(A.left, U) ⧸ m)
  have hb : Function.Bijective (algebraMap ℂ (Γ(A.left, U) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : ℂ ≃ₐ[ℂ] (Γ(A.left, U) ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ _) hb
  let e : Γ(A.left, U) →ₐ[ℂ] ℂ := (i.symm : (Γ(A.left, U) ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)
  have he : ∀ a, e.toRingHom (constFn A.hom U a) = a := fun a => e.commutes a
  obtain ⟨x, ⟨hxU, hx⟩, -⟩ := GlobalTheory.existsUnique_point_of_ringHom A U hU e.toRingHom he
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨z, hxU, fun b => ?_⟩
  change b ∈ m ↔ valAt' (u.ex z).left U b = 0
  rw [hx b]
  change b ∈ m ↔ i.symm (Ideal.Quotient.mk m b) = 0
  rw [← map_zero i.symm, i.symm.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.MaxPoints
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealAffineOpenEqVanishingUniformisationPStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalIdeal_affineOpen_eq_vanishing_uniformisationPoint : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens), IsAffineOpen U → ∀ m : Ideal Γ(A.left, U), m.IsMaximal → ∃ z ∈ pre u.ex U, ∀ b, b ∈ m ↔ val u.ex U b z = 0 := by
  first | exact @GlobalTheory.MaxPoints.main | exact GlobalTheory.MaxPoints.main | (intros; apply GlobalTheory.MaxPoints.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsHomId
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsHomId
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem exists_isIso_morphismRestrict_of_isHom_id : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω) (q : Y.Z ⟶ M.Z), M.IsHom Y (AlgHom.id o Ω) q → ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ IsIso (q ∣_ U) := by
  intro o Ω _ _ _ Y M q hq
  have := M.sep
  have : IsSeparated (q ≫ M.s) := hq.inducedModelMorphism_comp_structureMap.symm ▸ Y.sep
  have : IsSeparated q := IsSeparated.of_comp q M.s
  obtain ⟨U, hU, hgU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := genericPoint Y.Z) trivial
  obtain ⟨S, hS⟩ := fg_ringOn hU ⟨_, hgU⟩
  have hop : IsOpen (⋂ x ∈ S, {z | x ∈ M.O z}) :=
    isOpen_biInter_finset fun x _ => M.isOpen_setOf_mem_O x
  obtain ⟨V, hV, hzV, hle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨_, hop⟩) (x := genericPoint M.Z)
      (Set.mem_iInter₂.2 fun x _ => by
        show x ∈ M.O _
        rw [O_genericPoint]
        exact Algebra.mem_top)
  have hR : Y.ringOn U ≤ M.ringOn V := by
    rw [← hS]
    exact Algebra.adjoin_le fun x hx => mem_ringOn.2 fun w hw => Set.mem_iInter₂.1 (hle hw) x hx
  refine ⟨V, ⟨_, hzV⟩, isIso_morphismRestrict_of_local_dominant_sections q V fun z hz => ?_⟩
  obtain ⟨g, hg⟩ := exists_hom_of_map_ringOn (φ := AlgHom.id o Ω) hU
    ⟨genericPoint Y.Z, hgU⟩ (V := V) ⟨z, hz⟩ fun x hx => hR hx
  have hp := specMap_valMap_fromSpec hV M.pt (M.top_le_preimage_pt ⟨z, hz⟩)
  have hid : ∀ {X : Scheme.{0}} (a : Spec (CommRingCat.of Ω) ⟶ X),
      Spec.map (CommRingCat.ofHom (AlgHom.id o Ω).toRingHom) ≫ a = a := fun a =>
    (congrArg (· ≫ a) (Spec.map_id _)).trans (Category.id_comp _)
  have hdom : IsDominant (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hz⟩)) ≫ g) := by
    rw [hg, hid]
    infer_instance
  refine ⟨_, hV.fromSpec, inferInstance, g, hV.range_fromSpec ▸ hz, hV.range_fromSpec ▸ fun w hw => hw,
    IsDominant.of_comp (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hz⟩))) g, ?_⟩
  refine hom_ext_of_isOpenImmersion (φ := AlgHom.id o Ω) hV.fromSpec hp ?_ (hp.trans (hid _).symm)
  rw [← Category.assoc, hg, hid]
  exact hq

end GlobalTheory.ZH.RatModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsHomIdStatement
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonempty_isIso_morphismRestrict_of_isHom_id : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω) (q : Y.Z ⟶ M.Z), M.IsHom Y (AlgHom.id o Ω) q → ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ IsIso (q ∣_ U) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isHom_id | exact GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isHom_id | (intros; apply GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isHom_id <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamPeriodsLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamPeriodsLinear
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer


open Opposite in
theorem periods_linear : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ x y q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ y q' → IsPer u.ex u.Λ (x + y) (q + q') ∧ IsPer u.ex u.Λ (x - y) (q - q')) ∧ ∀ (a : ℂ) x q, IsPer u.ex u.Λ x q → IsPer u.ex u.Λ (a • x) (a • q) := by
  intro A _ g L u
  have hO : ∀ U : A.left.Opens, IsOpen (pre u.ex U) := fun U ↦ (u.hol U 0).1
  have vadd : ∀ (U : A.left.Opens) (b b' : Γ(A.left, U)) z, val u.ex U (b + b') z = val u.ex U b z + val u.ex U b' z :=
    fun U b b' z ↦ valAt'_add _ _ _ _
  have vsub : ∀ (U : A.left.Opens) (b b' : Γ(A.left, U)) z, val u.ex U (b - b') z = val u.ex U b z - val u.ex U b' z :=
    fun U b b' z ↦ valAt'_sub _ _ _ _
  have vsmul : ∀ (U : A.left.Opens) (a : ℂ) (b : Sec (str A) U), ∀ z ∈ pre u.ex U,
      val u.ex U (a • b) z = a * val u.ex U b z := by
    intro U a b z hz
    have e : (u.ex z).left ≫ str A = 𝟙 (Sp ℂ) := by
      rw [str, Category.comp_id]; exact Over.w (u.ex z)
    have k : valAt' (u.ex z).left U ((secMap (str A) U).hom a) = a :=
      (valAt'_appLE (u.ex z).left (str A) ⊤ U le_top _ hz).trans
        ((congrArg (fun p ↦ valAt' p ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) e).trans (valAt'_id_top a))
    exact (valAt'_mul (u.ex z).left U ((secMap (str A) U).hom a) b).trans (congrArg (· * val u.ex U b z) k)
  have dA : ∀ (k : A.left.affineOpens → (Fin g → ℂ) → ℂ) (U : A.left.affineOpens),
      DifferentiableOn ℂ (k U) (pre u.ex U.1) → ∀ z ∈ pre u.ex U.1, DifferentiableAt ℂ (k U) z :=
    fun k U hk z hz ↦ hk.differentiableAt ((hO _).mem_nhds hz)
  refine ⟨fun x y q q' hx hy ↦ ?_, fun a x q hx ↦ ?_⟩
  · obtain ⟨c, h, rfl, ⟨h1, h2, h3⟩, hp⟩ := hx
    obtain ⟨c', h', rfl, ⟨h1', h2', h3'⟩, hp'⟩ := hy
    constructor
    · refine ⟨c + c', fun U z ↦ h U z + h' U z, map_add _ _ _,
        ⟨fun U ↦ (h1 U).add (h1' U), fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
      · change h V z + h' V z = (h U z + h' U z) + val u.ex V.1 (c.1.1 (op U) (op V) f + c'.1.1 (op U) (op V) f) z
        refine Eq.trans ?_ (congrArg _ (vadd V.1 _ _ z).symm)
        rw [h2 U V f z hz, h2' U V f z hz]; ring
      · change fderiv ℂ (fun z ↦ h U z + h' U z) z = evForm u.ex U.1 z (c.1.2 (op U) + c'.1.2 (op U))
        rw [fderiv_fun_add (dA h U (h1 U) z hz) (dA h' U (h1' U) z hz), map_add (f := _), h3 U z hz, h3' U z hz]
      · simp only [Pi.add_apply]
        rw [hp U l z hz, hp' U l z hz]; ring
    · refine ⟨c - c', fun U z ↦ h U z - h' U z, map_sub _ _ _,
        ⟨fun U ↦ (h1 U).sub (h1' U), fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
      · change h V z - h' V z = (h U z - h' U z) + val u.ex V.1 (c.1.1 (op U) (op V) f - c'.1.1 (op U) (op V) f) z
        refine Eq.trans ?_ (congrArg _ (vsub V.1 _ _ z).symm)
        rw [h2 U V f z hz, h2' U V f z hz]; ring
      · change fderiv ℂ (fun z ↦ h U z - h' U z) z = evForm u.ex U.1 z (c.1.2 (op U) - c'.1.2 (op U))
        rw [fderiv_fun_sub (dA h U (h1 U) z hz) (dA h' U (h1' U) z hz), map_sub, h3 U z hz, h3' U z hz]
      · simp only [Pi.sub_apply]
        rw [hp U l z hz, hp' U l z hz]; ring
  · obtain ⟨c, h, rfl, ⟨h1, h2, h3⟩, hp⟩ := hx
    refine ⟨a • c, fun U z ↦ a * h U z, map_smul _ _ _,
      ⟨fun U ↦ (h1 U).const_mul a, fun U V f z hz ↦ ?_, fun U z hz ↦ ?_⟩, fun U l z hz ↦ ?_⟩
    · change a * h V z = a * h U z + val u.ex V.1 (a • c.1.1 (op U) (op V) f) z
      refine Eq.trans ?_ (congrArg _ (vsmul V.1 a _ z hz).symm)
      rw [h2 U V f z hz]; ring
    · change fderiv ℂ (fun z ↦ a * h U z) z = evForm u.ex U.1 z (a • c.1.2 (op U))
      rw [fderiv_const_mul (dA h U (h1 U) z hz), map_smul, h3 U z hz]
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [hp U l z hz]; ring

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamPeriodsLinearStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechDeRhamPeriods_linear : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ x y q q', IsPer u.ex u.Λ x q → IsPer u.ex u.Λ y q' → IsPer u.ex u.Λ (x + y) (q + q') ∧ IsPer u.ex u.Λ (x - y) (q - q')) ∧ ∀ (a : ℂ) x q, IsPer u.ex u.Λ x q → IsPer u.ex u.Λ (a • x) (a • q) := by
  first | exact @GlobalTheory.CechPer.periods_linear | exact GlobalTheory.CechPer.periods_linear | (intros; apply GlobalTheory.CechPer.periods_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemRangeNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemRangeNorm
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp.NormIndex

open Neutral.B1

theorem mul_eq_one_of_card_two {G : Type} [Group G] [Finite G] (h : Nat.card G = 2) {a b : G}
    (ha : a ≠ 1) (hb : b ≠ 1) : a * b = 1 := by
  classical
  have hab : b = a := by
    by_contra hne
    haveI := Fintype.ofFinite G
    have : ({1, a, b} : Finset G).card ≤ Nat.card G := by
      rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb]),
      Finset.card_pair (Ne.symm hne), h] at this
    omega
  subst hab
  have := pow_card_eq_one' (G := G) (x := b)
  rw [h, pow_two] at this
  exact this

theorem mul_mem_range_norm (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (x y : Fˣ)
    (hx : x ∉ (Units.map (Algebra.norm F : E →* F)).range)
    (hy : y ∉ (Units.map (Algebra.norm F : E →* F)).range) :
    x * y ∈ (Units.map (Algebra.norm F : E →* F)).range := by
  obtain ⟨b, -, -⟩ := hE.basis
  have h2 : Module.finrank F E = 2 := by rw [Module.finrank_eq_card_basis b]; simp
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : IsGalois F E := Algebra.IsQuadraticExtension.isGalois F E
  let φ : E →ₐ[F] AlgebraicClosure F := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let L : IntermediateField F (AlgebraicClosure F) := φ.fieldRange
  let e : E ≃ₐ[F] L := AlgEquiv.ofInjectiveField φ
  haveI : FiniteDimensional F L := LinearEquiv.finiteDimensional e.toLinearEquiv
  haveI : IsGalois F L := IsGalois.of_algEquiv e
  have hL2 : Module.finrank F L = 2 := e.toLinearEquiv.finrank_eq.symm.trans h2
  have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by
    rw [← hL2, ← IsGalois.card_aut_eq_finrank]
  have hab : IsFiniteAbelian F L :=
    { finiteDimensional := inferInstance
      isGalois := inferInstance
      comm := fun a b' => by
        haveI : Fact (Nat.card (L ≃ₐ[F] L)).Prime := ⟨hcard ▸ Nat.prime_two⟩
        haveI := isCyclic_of_prime_card (α := L ≃ₐ[F] L) (p := Nat.card (L ≃ₐ[F] L)) rfl
        exact IsCyclic.commGroup.mul_comm a b' }
  obtain ⟨Art, hArt⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.artin_reciprocity_char_zero F
  obtain ⟨-, hker⟩ := hArt.2.2.2.2 L hab
  have hN : (Units.map (Algebra.norm F : E →* F)).range = normGroup F L := by
    ext z
    simp only [normGroup, MonoidHom.mem_range]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨Units.map (e : E →* L) w, Units.ext (Algebra.norm_eq_of_algEquiv e (w : E))⟩
    · rintro ⟨w, rfl⟩
      exact ⟨Units.map (e.symm : L →* E) w, Units.ext (Algebra.norm_eq_of_algEquiv e.symm (w : L))⟩
  rw [hN, ← hker] at hx hy ⊢
  rw [MonoidHom.mem_ker] at hx hy ⊢
  rw [map_mul]
  haveI : Finite (L ≃ₐ[F] L) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact mul_eq_one_of_card_two hcard hx hy

end GlobalTheory.KSp.NormIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemRangeNormStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_mem_range_norm_of_not_mem : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (x y : Fˣ), x ∉ (Units.map (Algebra.norm F : E →* F)).range → y ∉ (Units.map (Algebra.norm F : E →* F)).range → x * y ∈ (Units.map (Algebra.norm F : E →* F)).range := by
  first | exact @GlobalTheory.KSp.NormIndex.mul_mem_range_norm | exact GlobalTheory.KSp.NormIndex.mul_mem_range_norm | (intros; apply GlobalTheory.KSp.NormIndex.mul_mem_range_norm <;> assumption)
end
end
