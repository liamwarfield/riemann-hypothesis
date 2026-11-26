module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationVanishingConstants

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AppLEBasicOpenIsStandardSmooth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpChart

theorem res_top_isStandardSmooth (X : Scheme.{0}) [IsAffine X] (t : Γ(X, ⊤)) (D : X.Opens) (hD : D = X.basicOpen t) :
    (X.presheaf.map (homOfLE (le_top : D ≤ ⊤)).op).hom.IsStandardSmooth := by
  subst hD
  have := (isAffineOpen_top X).isLocalization_basicOpen t
  exact RingHom.isStandardSmooth_holdsForLocalizationAway _ t

theorem appLE_basicOpen_isStandardSmooth {X Y : Scheme.{0}} (p : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    {V : Y.Opens} (hV : IsAffineOpen V) (e : V ≤ p ⁻¹ᵁ U) (h : (p.appLE U V e).hom.IsStandardSmooth) (a : Γ(X, U))
    (e' : Y.basicOpen (p.appLE U V e a) ≤ p ⁻¹ᵁ X.basicOpen a) :
    (p.appLE (X.basicOpen a) (Y.basicOpen (p.appLE U V e a)) e').hom.IsStandardSmooth := by
  have := hV.isLocalization_basicOpen (p.appLE U V e a)
  have := hU.isLocalization_basicOpen a
  rw [hU.appLE_eq_away_map p hV]
  exact RingHom.isStandardSmooth_localizationPreserves.away _ _ _ _ h

theorem exists_chart : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (φ : R →+* ℂ), Smooth G.hom →
  ∃ (V : G.left.Opens) (r : R), IsAffineOpen V ∧ φ r ≠ 0 ∧ (GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.cst G.hom V).IsStandardSmooth ∧
    ⊤ ≤ (spMap (algebraMap R (Localization.Away r)) ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left) ⁻¹ᵁ V := by
  intro R _ G _ φ hsm
  set s : Sp R ⟶ G.left := (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left with hsdef
  have hs : s ≫ G.hom = 𝟙 (Sp R) := Over.w (1 : Over.mk (𝟙 (Sp R)) ⟶ G)
  let x : Sp R := (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum R)
  obtain ⟨U, hU, V, hV, e, hxU, -, hUs, h⟩ :=
    GlobalTheory.LieChart.exists_isStandardSmooth_section G.hom s hs x ⊤ trivial
  obtain ⟨_, ⟨r, rfl⟩, hxr, hsub⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
    (show (x : PrimeSpectrum R) ∈ (SetLike.coe U : Set (PrimeSpectrum R)) from hxU)
    (show IsOpen (SetLike.coe U : Set (PrimeSpectrum R)) from U.isOpen)
  have hr : φ r ≠ 0 := fun h0 => hxr (show r ∈ RingHom.ker φ from h0)
  let t : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv r
  have htr : (Sp R).basicOpen t = PrimeSpectrum.basicOpen r :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) r
  have hle : (Sp R).basicOpen t ≤ U := by
    rw [htr]; exact hsub
  let a : Γ(Sp R, U) := (Sp R).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t
  have hat : (Sp R).basicOpen a = (Sp R).basicOpen t := by
    rw [Scheme.basicOpen_res]; exact inf_eq_right.2 hle
  have e' : G.left.basicOpen (G.hom.appLE U V e a) ≤ G.hom ⁻¹ᵁ (Sp R).basicOpen a := by
    simp [Scheme.Hom.appLE]
  have h1 := appLE_basicOpen_isStandardSmooth G.hom hU hV e h a e'
  have h2 := res_top_isStandardSmooth (Sp R) t _ hat
  refine ⟨G.left.basicOpen (G.hom.appLE U V e a), r, hV.basicOpen _, hr, ?_, ?_⟩
  · have h3 : (G.hom.appLE ⊤ (G.left.basicOpen (G.hom.appLE U V e a)) (fun _ _ => trivial)).hom.IsStandardSmooth := by
      have := Scheme.Hom.map_appLE G.hom e' (homOfLE (le_top : (Sp R).basicOpen a ≤ ⊤)).op
      have e3 := congrArg CommRingCat.Hom.hom this
      rw [CommRingCat.hom_comp] at e3
      rw [← e3]
      exact h1.comp h2
    exact RingHom.isStandardSmooth_respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h3
  · intro y _
    have hz : (spMap (algebraMap R (Localization.Away r))) y ∈ (Sp R).basicOpen t := by
      rw [htr]
      have := PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
      exact this.subset ⟨y, rfl⟩
    set z := (spMap (algebraMap R (Localization.Away r))) y with hzdef
    have hps : G.hom (s z) = z := by rw [← Scheme.Hom.comp_apply, hs]; rfl
    have h1 : s z ∈ V := hUs (hle hz)
    have h2 : s z ∈ G.hom ⁻¹ᵁ (Sp R).basicOpen a := by
      show G.hom (s z) ∈ (Sp R).basicOpen a
      rw [hps, hat]; exact hz
    show (spMap (algebraMap R (Localization.Away r)) ≫ s) y ∈ G.left.basicOpen (G.hom.appLE U V e a)
    rw [Scheme.Hom.comp_apply]
    show s z ∈ G.left.basicOpen (G.hom.appLE U V e a)
    simpa [Scheme.Hom.appLE, ← Scheme.preimage_basicOpen] using And.intro h1 h2

end GlobalTheory.CompanionTheory.Ar.Flat.ExpChart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualElements
open Filter Topology Metric

namespace GlobalTheory.CompanionTheory.ExpChart.DualElements

theorem exists_det_ne_zero {X : Type} {g : ℕ} (w : X → Fin g → ℂ)
    (h : ∀ c : Fin g → ℂ, (∀ x, ∑ a, c a * w x a = 0) → c = 0) :
    ∃ a : Fin g → X, (Matrix.of fun i j => w (a i) j).det ≠ 0 := by
  have hspan : Submodule.span ℂ (Set.range w) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    have hfx : ∀ y : Fin g → ℂ, f y = ∑ a, f (fun j => if a = j then 1 else 0) * y a := by
      intro y
      rw [LinearMap.pi_apply_eq_sum_univ f y]
      exact Finset.sum_congr rfl fun a _ => by rw [smul_eq_mul, mul_comm]
    have hc := h (fun a => f (fun j => if a = j then 1 else 0)) (fun x => by
      rw [← hfx]
      exact hf (Submodule.subset_span ⟨x, rfl⟩))
    refine LinearMap.ext fun y => ?_
    rw [hfx y, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun a _ => by
      rw [show f (fun j => if a = j then 1 else 0) = 0 from congrFun hc a, zero_mul]
  obtain ⟨b, hb, hbs, hli⟩ := exists_linearIndependent ℂ (Set.range w)
  let B := Module.Basis.mk hli (by rw [Subtype.range_coe, hbs, hspan])
  have : Fintype b := FiniteDimensional.fintypeBasisIndex B
  have hcard : Fintype.card b = g := by
    rw [← Module.finrank_eq_card_basis B]
    simp
  let e : Fin g ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hex : ∀ i, ∃ x, w x = (e i : Fin g → ℂ) := fun i => hb (e i).2
  choose a ha using hex
  refine ⟨a, ?_⟩
  have hrow : LinearIndependent ℂ (Matrix.of fun i j => w (a i) j).row := by
    have hEq : (Matrix.of fun i j => w (a i) j).row = Subtype.val ∘ e := by
      ext i j
      simp [Matrix.row, ha]
    rw [hEq]
    exact hli.comp _ e.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.1 hrow
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero

theorem exists_dual_elements :
    ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (r : R) (g : ℕ)
      (E : A →+* Localization.Away r) (v : Fin g → (A →+* DualNumber (Localization.Away r)))
      (φ : Localization.Away r →+* ℂ),
      (∀ x : R, E (algebraMap R A x) = algebraMap R (Localization.Away r) x) →
      (∀ a (x : R), TrivSqZeroExt.snd (v a (algebraMap R A x)) = 0) →
      (∀ a x, TrivSqZeroExt.fst (v a x) = E x) →
      (∀ c : Fin g → ℂ, (∀ x, ∑ a, c a * φ (TrivSqZeroExt.snd (v a x)) = 0) → c = 0) →
      ∃ (ρ : R) (t : Fin g → A), φ (algebraMap R (Localization.Away r) ρ) ≠ 0 ∧
        (∀ c, E (t c) = 0) ∧
        ∀ a c, TrivSqZeroExt.snd (v a (t c)) =
          if a = c then algebraMap R (Localization.Away r) ρ else 0 := by
  intro R A _ _ _ r g E v φ h1 h2 h3 h4
  let D : Fin g → A →+ Localization.Away r := fun a =>
    AddMonoidHom.mk' (fun x => TrivSqZeroExt.snd (v a x)) (fun x y => by
      rw [map_add (f := _), TrivSqZeroExt.snd_add])
  have hD : ∀ a x, D a x = TrivSqZeroExt.snd (v a x) := fun _ _ => rfl
  have hDmul : ∀ a x y, D a (x * y) = E x * D a y + E y * D a x := by
    intro a x y
    rw [hD, hD, hD, map_mul, TrivSqZeroExt.snd_mul, h3, h3, smul_eq_mul, op_smul_eq_mul, mul_comm (TrivSqZeroExt.snd (v a x))]
  have hDalg : ∀ a (s : R), D a (algebraMap R A s) = 0 := fun a s => h2 a s
  have hDs : ∀ a (s : R) x, D a (algebraMap R A s * x) =
      algebraMap R (Localization.Away r) s * D a x := by
    intro a s x
    rw [hDmul, hDalg, h1, mul_zero, add_zero]
  obtain ⟨a, ha⟩ := exists_det_ne_zero (X := A) (fun x i => φ (D i x)) h4
  obtain ⟨⟨b, hbm⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers r) (fun c => E (a c))
  have hbu : IsUnit (algebraMap R (Localization.Away r) b) :=
    IsLocalization.map_units _ (⟨b, hbm⟩ : Submonoid.powers r)
  have hb' : ∀ c, ∃ s, algebraMap R (Localization.Away r) s =
      algebraMap R (Localization.Away r) b * E (a c) := fun c => by
    obtain ⟨s, hs⟩ := hb c
    exact ⟨s, by rw [hs, Algebra.smul_def]⟩
  choose s hs using hb'
  let t' : Fin g → A := fun c => algebraMap R A b * a c - algebraMap R A (s c)
  have hEt' : ∀ c, E (t' c) = 0 := by
    intro c
    simp only [t', map_sub, map_mul, h1, hs, sub_self]
  have hDt' : ∀ i c, D i (t' c) = algebraMap R (Localization.Away r) b * D i (a c) := by
    intro i c
    simp only [t', map_sub, hDs, hDalg, sub_zero]
  let N : Matrix (Fin g) (Fin g) (Localization.Away r) := Matrix.of fun c i => D i (t' c)
  have hN : φ N.det ≠ 0 := by
    have hN0 : N = algebraMap R (Localization.Away r) b •
        Matrix.of (fun c i => D i (a c)) := by
      ext c i
      simp [N, hDt']
    rw [hN0, Matrix.det_smul, map_mul, map_pow, RingHom.map_det]
    refine mul_ne_zero (pow_ne_zero _ (hbu.map φ).ne_zero) ?_
    have hM : φ.mapMatrix (Matrix.of fun c i => D i (a c)) =
        Matrix.of fun i j => φ (D j (a i)) := by
      ext i j
      simp
    rw [hM]
    exact ha
  obtain ⟨⟨b2, hb2m⟩, hb2⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers r)
    (fun o : Option (Fin g × Fin g) => o.elim N.det (fun p => N.adjugate p.1 p.2))
  have hb2u : IsUnit (algebraMap R (Localization.Away r) b2) :=
    IsLocalization.map_units _ (⟨b2, hb2m⟩ : Submonoid.powers r)
  have hρ : ∃ ρ, algebraMap R (Localization.Away r) ρ =
      algebraMap R (Localization.Away r) b2 * N.det := by
    obtain ⟨s, hs⟩ := hb2 none
    exact ⟨s, by rw [hs, Algebra.smul_def]; rfl⟩
  have hn : ∀ c c', ∃ n, algebraMap R (Localization.Away r) n =
      algebraMap R (Localization.Away r) b2 * N.adjugate c c' := fun c c' => by
    obtain ⟨s, hs⟩ := hb2 (some (c, c'))
    exact ⟨s, by rw [hs, Algebra.smul_def]; rfl⟩
  obtain ⟨ρ, hρ⟩ := hρ
  choose n hn using hn
  refine ⟨ρ, fun c => ∑ c', algebraMap R A (n c c') * t' c', ?_, ?_, ?_⟩
  · rw [hρ, map_mul]
    exact mul_ne_zero (hb2u.map φ).ne_zero hN
  · intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun c' _ => by rw [map_mul, hEt', mul_zero]
  · intro i c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hD, map_sum]
    have hsum : ∑ c', D i (algebraMap R A (n c c') * t' c') =
        algebraMap R (Localization.Away r) b2 * (N.adjugate * N) c i := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [hDs, hn, mul_assoc]
      rfl
    rw [hsum, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hic : i = c
    · subst hic
      simp [hρ]
    · simp [hic, Ne.symm hic]

end GlobalTheory.CompanionTheory.ExpChart.DualElements
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartStandardSmooth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords

open GlobalTheory.HolHom GlobalTheory.CompanionTheory.Ar.Flat.ExpChart

variable {R C D : Type} [CommRing R] [CommRing C] [CommRing D]

theorem surj_fstC (q : Sp (DualNumber C)) :
    ∃ p : Sp C, spMap (TrivSqZeroExt.fstHom C C C).toRingHom p = q := by
  refine ⟨PrimeSpectrum.comap (algebraMap C (DualNumber C)) q, ?_⟩
  show PrimeSpectrum.comap (TrivSqZeroExt.fstHom C C C).toRingHom
    (PrimeSpectrum.comap (algebraMap C (DualNumber C)) q) = q
  apply PrimeSpectrum.ext
  ext x
  have hn : TrivSqZeroExt.inr x.snd ∈ q.asIdeal := by
    have h2 : (TrivSqZeroExt.inr x.snd : DualNumber C) * TrivSqZeroExt.inr x.snd = 0 := by simp
    have : (TrivSqZeroExt.inr x.snd : DualNumber C) * TrivSqZeroExt.inr x.snd ∈ q.asIdeal := by
      rw [h2]; exact zero_mem _
    exact (q.isPrime.mem_or_mem this).elim id id
  have hx : x = algebraMap C (DualNumber C) x.fst + TrivSqZeroExt.inr x.snd := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  show algebraMap C (DualNumber C) x.fst ∈ q.asIdeal ↔ x ∈ q.asIdeal
  constructor
  · intro h; rw [hx]; exact add_mem h hn
  · intro h
    have : algebraMap C (DualNumber C) x.fst = x - TrivSqZeroExt.inr x.snd := eq_sub_of_add_eq hx.symm
    rw [this]; exact sub_mem h hn

theorem le_dual {X : Scheme.{0}} {v : Sp (DualNumber C) ⟶ X} {x : Sp C ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v = x) {U : X.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ U) : ⊤ ≤ v ⁻¹ᵁ U := by
  intro q _
  obtain ⟨p, rfl⟩ := surj_fstC q
  subst h
  have h1 := hx (Set.mem_univ p)
  change (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v) p ∈ U at h1
  change v _ ∈ U
  rwa [Scheme.Hom.comp_apply] at h1

theorem spMap_comp' (β : R →+* C) (κ : C →+* D) : spMap (κ.comp β) = spMap κ ≫ spMap β := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp (β : R →+* C) (κ : C →+* D) : dualMap (κ.comp β) = (dualMap κ).comp (dualMap β) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

variable (G : Over (Sp R)) [GrpObj G]

abbrev ptU (β : R →+* C) : Sp C ⟶ G.left := spMap β ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left

variable {G} {E : Type} [AddCommGroup E] [Module R E]

abbrev ptV (M : LieModel G (𝟙 (Sp R)) E) (β : R →+* C) (w : E) : Sp (DualNumber C) ⟶ G.left :=
  spMap (dualMap β) ≫ (M.pt w).left

theorem ptU_over (β : R →+* C) : ptU G β ≫ G.hom = spMap β := by
  have e : (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left ≫ G.hom = 𝟙 (Sp R) := Over.w _
  rw [Category.assoc, e, Category.comp_id]

theorem ptV_over (M : LieModel G (𝟙 (Sp R)) E) (β : R →+* C) (w : E) :
    ptV M β w ≫ G.hom = spMap ((algebraMap C (DualNumber C)).comp β) := by
  have e : (M.pt w).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R) := Over.w (M.pt w)
  rw [Category.assoc, e, Category.comp_id, ← spMap_comp']
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']

theorem ptV_fst (M : LieModel G (𝟙 (Sp R)) E) (β : R →+* C) (w : E) :
    spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ ptV M β w = ptU G β := by
  rw [ptU, ← M.tan w, ← Category.assoc, ← Category.assoc]
  congr 1
  show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [← spMap_comp', ← spMap_comp']
  congr 1
  refine RingHom.ext fun x => ?_
  show TrivSqZeroExt.fst (dualMap β x) = β (TrivSqZeroExt.fst x)
  simp [dualMap]

theorem one_left_comp (β : R →+* C) (θ : C →+* ℂ) :
    (1 : Over.mk (spMap (θ.comp β)) ⟶ G).left = spMap θ ≫ ptU G β := by
  rw [one_left_spMap, spMap_comp', Category.assoc]

theorem le_one_left (β : R →+* C) (θ : C →+* ℂ) {V : G.left.Opens} (h : ⊤ ≤ ptU G β ⁻¹ᵁ V) :
    ⊤ ≤ (1 : Over.mk (spMap (θ.comp β)) ⟶ G).left ⁻¹ᵁ V := by
  rw [one_left_comp]
  exact fun p _ => h (x := spMap θ p) trivial

theorem val_one_left (β : R →+* C) (θ : C →+* ℂ) {V : G.left.Opens} (h : ⊤ ≤ ptU G β ⁻¹ᵁ V) (f : Γ(G.left, V)) :
    valAt' (1 : Over.mk (spMap (θ.comp β)) ⟶ G).left V f = θ (valR (ptU G β) V f) := by
  rw [one_left_comp, valAt'_eq_valR, valR_spMap _ _ _ h]

theorem snd_val_comp (M : LieModel G (𝟙 (Sp R)) E) (β : R →+* C) (θ : C →+* ℂ) (w : E) {V : G.left.Opens}
    (h : ⊤ ≤ ptV M β w ⁻¹ᵁ V) (f : Γ(G.left, V)) :
    TrivSqZeroExt.snd (valR (spMap (dualMap (θ.comp β)) ≫ (M.pt w).left) V f) =
      θ (TrivSqZeroExt.snd (valR (ptV M β w) V f)) := by
  rw [dualMap_comp, spMap_comp', Category.assoc, valR_spMap _ _ _ h]
  simp [dualMap]

theorem fst_val (M : LieModel G (𝟙 (Sp R)) E) (β : R →+* C) (w : E) {V : G.left.Opens}
    (h : ⊤ ≤ ptV M β w ⁻¹ᵁ V) (f : Γ(G.left, V)) :
    TrivSqZeroExt.fst (valR (ptV M β w) V f) = valR (ptU G β) V f := by
  have := valR_spMap (TrivSqZeroExt.fstHom C C C).toRingHom (ptV M β w) V h f
  rw [ptV_fst] at this
  exact this.symm

theorem exists_lift (r : R) (θ : R →+* ℂ) (h : θ r ≠ 0) :
    ∃ θ' : Localization.Away r →+* ℂ, θ'.comp (algebraMap R (Localization.Away r)) = θ :=
  ⟨IsLocalization.Away.lift r (isUnit_iff_ne_zero.2 h), IsLocalization.Away.lift_comp r _⟩

theorem res_cst {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (cst p U a) = cst p V a := by
  have e := Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op
  exact congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) e

theorem isStandardSmooth_basicOpen {X : Scheme.{0}} (p : X ⟶ Sp R) {U : X.Opens} (hU : IsAffineOpen U)
    (h : (cst p U).IsStandardSmooth) (s : Γ(X, U)) : (cst p (X.basicOpen s)).IsStandardSmooth := by
  have := hU.isLocalization_basicOpen s
  have h1 : (algebraMap Γ(X, U) Γ(X, X.basicOpen s)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway s
  have h2 := RingHom.IsStandardSmooth.comp (RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth 0 _ h1) h
  have e : (algebraMap Γ(X, U) Γ(X, X.basicOpen s)).comp (cst p U) = cst p (X.basicOpen s) :=
    RingHom.ext fun a => res_cst p (X.basicOpen_le s) a
  rwa [e] at h2

end GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords

open GlobalTheory.HolHom GlobalTheory.CompanionTheory.Ar.Flat.ExpChart

theorem exists_coords : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (φ : R →+* ℂ), Smooth G.hom →
  ∃ (V : G.left.Opens) (t : Fin g → Γ(G.left, V)) (ρ : R), IsAffineOpen V ∧ φ ρ ≠ 0 ∧ (GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.cst G.hom V).IsStandardSmooth ∧
    (∀ θ : R →+* ℂ, θ ρ ≠ 0 → ⊤ ≤ (1 : Over.mk (spMap θ) ⟶ G).left ⁻¹ᵁ V ∧ (∀ c, valAt' (1 : Over.mk (spMap θ) ⟶ G).left V (t c) = 0) ∧
      ∀ a c, TrivSqZeroExt.snd (valR (spMap (dualMap θ) ≫ (M.pt (Pi.single a 1)).left) V (t c)) = if a = c then 1 else 0) ∧
    ∀ f : Γ(G.left, V), ∃ (u : R) (k : ℕ), ∀ θ : R →+* ℂ, θ ρ ≠ 0 → valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f * θ ρ ^ k = θ u := by
  intro R _ G _ g M φ hs
  obtain ⟨V₁, r, hV₁, hφr, hss, hle⟩ := GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.exists_chart R G φ hs
  let β : R →+* Localization.Away r := algebraMap R (Localization.Away r)
  obtain ⟨φ', rfl⟩ : ∃ φ' : Localization.Away r →+* ℂ, φ'.comp β = φ := exists_lift r φ hφr
  have hle' : ⊤ ≤ ptU G β ⁻¹ᵁ V₁ := hle
  letI alg : Algebra R Γ(G.left, V₁) := (cst G.hom V₁).toAlgebra
  have hv : ∀ a : Fin g, ⊤ ≤ ptV M β (Pi.single a 1) ⁻¹ᵁ V₁ := fun a => le_dual (ptV_fst M β _) hle'
  let E := evalHom (ptU G β) V₁ hle'
  let v : Fin g → (Γ(G.left, V₁) →+* DualNumber (Localization.Away r)) :=
    fun a => evalHom (ptV M β (Pi.single a 1)) V₁ (hv a)
  have hEv : ∀ f, E f = valR (ptU G β) V₁ f := fun f => (valR_eq _ _ hle' f).symm
  have hvv : ∀ a f, v a f = valR (ptV M β (Pi.single a 1)) V₁ f := fun a f => (valR_eq _ _ (hv a) f).symm
  have h1 : ∀ x : R, E (algebraMap R Γ(G.left, V₁) x) = β x :=
    fun x => valR_cst G.hom V₁ β (ptU G β) (ptU_over β) hle' x
  have h2 : ∀ a (x : R), TrivSqZeroExt.snd (v a (algebraMap R Γ(G.left, V₁) x)) = 0 := fun a x => by
    have := valR_cst G.hom V₁ ((algebraMap _ (DualNumber (Localization.Away r))).comp β)
      (ptV M β (Pi.single a 1)) (ptV_over M β _) (hv a) x
    show TrivSqZeroExt.snd (evalHom (ptV M β (Pi.single a 1)) V₁ (hv a) (cst G.hom V₁ x)) = 0
    rw [this]
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have h3 : ∀ a x, TrivSqZeroExt.fst (v a x) = E x := fun a x => by
    rw [hvv, hEv, fst_val M β _ (hv a)]
  have h4 : ∀ c : Fin g → ℂ, (∀ x, ∑ a, c a * φ' (TrivSqZeroExt.snd (v a x)) = 0) → c = 0 := by
    intro c hc
    obtain ⟨c₀, -, hu⟩ := GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis R G g M (φ'.comp β) hs V₁ hV₁ (le_one_left β φ' hle') 0
      (fun _ => rfl) (fun f f' => by simp)
    have e1 := hu c fun f => by
      have := hc f
      simp only [hvv] at this
      simp only [snd_val_comp M β φ' _ (hv _)]
      exact this.symm
    have e2 := hu 0 fun f => by simp
    exact e1.trans e2.symm
  obtain ⟨ρ', t', hρ', hE, hvt⟩ := GlobalTheory.CompanionTheory.ExpChart.DualElements.exists_dual_elements R Γ(G.left, V₁) r g E v φ' h1 h2 h3 h4
  let s : Γ(G.left, V₁) := cst G.hom V₁ (r * ρ')
  have hVle : G.left.basicOpen s ≤ V₁ := G.left.basicOpen_le s
  let res : Γ(G.left, V₁) →+* Γ(G.left, G.left.basicOpen s) := (G.left.presheaf.map (homOfLE hVle).op).hom
  have hloc := hV₁.isLocalization_basicOpen s
  have hunit : IsUnit (res s) := IsLocalization.Away.algebraMap_isUnit s
  have hfac : res s = res (cst G.hom V₁ r) * res (cst G.hom V₁ ρ') := by
    show res (cst G.hom V₁ (r * ρ')) = _
    rw [map_mul, map_mul]
  obtain ⟨w, hw⟩ : ∃ w, res (cst G.hom V₁ ρ') * w = 1 :=
    (isUnit_of_mul_isUnit_right (hfac ▸ hunit)).exists_right_inv
  have key : ∀ θ' : Localization.Away r →+* ℂ, (θ'.comp β) (r * ρ') ≠ 0 →
      ⊤ ≤ (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left ⁻¹ᵁ G.left.basicOpen s ∧
      (∀ f, valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (res f) = θ' (E f)) ∧
      (∀ a b, valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (a * b) =
        valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) a *
          valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) b) ∧
      (∀ a (n : ℕ), valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (a ^ n) =
        valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) a ^ n) ∧
      θ' (β ρ') * valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) w = 1 := by
    intro θ' hθ
    have hx1 := le_one_left β θ' hle'
    have hx : ⊤ ≤ (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left ⁻¹ᵁ G.left.basicOpen s :=
      (le_basicOpen_iff _ hx1 s).2 (by
        show valAt' _ V₁ (cst G.hom V₁ (r * ρ')) ≠ 0
        rw [val_cst V₁ (1 : Over.mk (spMap (θ'.comp β)) ⟶ G) hx1]
        exact hθ)
    have hval : ∀ f, valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (res f) = θ' (E f) := by
      intro f
      have e : valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (res f) =
          valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left V₁ f := valR_res _ hVle f hx
      rw [e, val_one_left β θ' hle', hEv]
    have hmul : ∀ a b, valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (a * b) =
        valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) a *
          valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) b := fun a b => by
      simp only [valAt'_eq_valR, valR_eq _ _ hx, map_mul]
    refine ⟨hx, hval, hmul, fun a n => ?_, ?_⟩
    · simp only [valAt'_eq_valR, valR_eq _ _ hx, map_pow]
    · have e := congrArg (valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s)) hw
      rw [hmul, hval] at e
      have e1 : valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) 1 = 1 := by
        simp only [valAt'_eq_valR, valR_eq _ _ hx, map_one]
      rw [e1] at e
      have e2 : E (cst G.hom V₁ ρ') = β ρ' := h1 ρ'
      rwa [e2] at e
  have hsplit : ∀ θ : R →+* ℂ, θ (r * ρ') ≠ 0 → ∃ θ' : Localization.Away r →+* ℂ, θ'.comp β = θ :=
    fun θ hθ => exists_lift r θ (left_ne_zero_of_mul (by rwa [map_mul] at hθ))
  refine ⟨G.left.basicOpen s, fun c => res (t' c) * w, r * ρ', hV₁.basicOpen s, ?_,
    isStandardSmooth_basicOpen G.hom hV₁ hss s, ?_, ?_⟩
  · rw [map_mul]
    exact mul_ne_zero hφr hρ'
  · intro θ hθ
    obtain ⟨θ', rfl⟩ := hsplit θ hθ
    obtain ⟨hx, hval, hmul, -, hwv⟩ := key θ' hθ
    refine ⟨hx, fun c => ?_, fun a c => ?_⟩
    · beta_reduce
      rw [hmul, hval, hE, map_zero, zero_mul]
    · beta_reduce
      obtain ⟨D, hD, hL⟩ := tan_der (tan_base M (θ'.comp β) (Pi.single a 1)) hx
      have hy : ⊤ ≤ (spMap (dualMap (θ'.comp β)) ≫ (M.pt (Pi.single a 1)).left) ⁻¹ᵁ G.left.basicOpen s :=
        (le_preimage_dual_iff (tan_base M (θ'.comp β) (Pi.single a 1)) _).2 hx
      have e : valR (spMap (dualMap (θ'.comp β)) ≫ (M.pt (Pi.single a 1)).left) (G.left.basicOpen s) (res (t' c)) =
          valR (spMap (dualMap (θ'.comp β)) ≫ (M.pt (Pi.single a 1)).left) V₁ (t' c) := valR_res _ hVle _ hy
      have e' : D (res (t' c)) = θ' (TrivSqZeroExt.snd (v a (t' c))) := by
        rw [hD, e, snd_val_comp M β θ' _ (hv a), hvv]
      rw [← hD, hL, hval, hE, map_zero, zero_mul, zero_add, e', hvt]
      split_ifs
      · rw [mul_comm]; exact hwv
      · simp
  · intro f
    obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj s f
    obtain ⟨l, u, hu⟩ := IsLocalization.Away.surj r (E a)
    refine ⟨u * ρ' ^ l, m + l, fun θ hθ => ?_⟩
    obtain ⟨θ', rfl⟩ := hsplit θ hθ
    obtain ⟨hx, hval, hmul, hpow, -⟩ := key θ' hθ
    have hs' : valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) (res s) =
        (θ'.comp β) (r * ρ') := by
      rw [hval]
      have e2 : E (cst G.hom V₁ (r * ρ')) = β (r * ρ') := h1 _
      show θ' (E (cst G.hom V₁ (r * ρ'))) = _
      rw [e2]
      rfl
    have e1 : valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s) f *
        ((θ'.comp β) (r * ρ')) ^ m = θ' (E a) := by
      rw [← hs', ← hpow, ← hmul, ← hval]
      exact congrArg (valAt' (1 : Over.mk (spMap (θ'.comp β)) ⟶ G).left (G.left.basicOpen s)) ha
    have e2 : θ' (E a) * θ' (β r) ^ l = θ' (β u) := by
      rw [← map_pow, ← map_mul]
      exact congrArg θ' hu
    have e3 : (θ'.comp β) (r * ρ') = θ' (β r) * θ' (β ρ') := by
      simp only [RingHom.comp_apply, map_mul]
    have e4 : (θ'.comp β) (u * ρ' ^ l) = θ' (β u) * θ' (β ρ') ^ l := by
      simp only [RingHom.comp_apply, map_mul, map_pow]
    rw [e4, ← e2, ← e1, e3]
    ring

end GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartStandardSmoothStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_exp_chart_standard_smooth : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (φ : R →+* ℂ), Smooth G.hom →
  ∃ (V : G.left.Opens) (t : Fin g → Γ(G.left, V)) (ρ : R), IsAffineOpen V ∧ φ ρ ≠ 0 ∧ (GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.cst G.hom V).IsStandardSmooth ∧
    (∀ θ : R →+* ℂ, θ ρ ≠ 0 → ⊤ ≤ (1 : Over.mk (spMap θ) ⟶ G).left ⁻¹ᵁ V ∧ (∀ c, valAt' (1 : Over.mk (spMap θ) ⟶ G).left V (t c) = 0) ∧
      ∀ a c, TrivSqZeroExt.snd (valR (spMap (dualMap θ) ≫ (M.pt (Pi.single a 1)).left) V (t c)) = if a = c then 1 else 0) ∧
    ∀ f : Γ(G.left, V), ∃ (u : R) (k : ℕ), ∀ θ : R →+* ℂ, θ ρ ≠ 0 → valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f * θ ρ ^ k = θ u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords.exists_coords | exact GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords.exists_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.Coords.exists_coords <;> assumption)
end
