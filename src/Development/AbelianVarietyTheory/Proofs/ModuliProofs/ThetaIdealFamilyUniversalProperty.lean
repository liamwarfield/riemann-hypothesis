module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelIsoUniqueOfDenseCommonFibres
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianVarietyCutOutBoundedDegreeTorsion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionsVeryAmplePeriodic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomogeneousPolynomialVolumePullbackCombina

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalProperty
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalProperty
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FamRep

theorem spMap_surj {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R' ⟶ Sp R) : ∃ β : R →+* R', spMap β = x :=
  ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap f = spMap (h.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f f' : R →+* R'} (h : spMap f = spMap f') : f = f' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)


open MvPolynomial in
theorem eval₂_scale {σ R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (c : A) (x : σ → A) {F : MvPolynomial σ R}
    {e : ℕ} (hF : F.IsHomogeneous e) : eval₂ φ (fun j => c * x j) F = c ^ e * eval₂ φ x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ j ∈ a.support, a j = e := by
    have := hF (mem_support_iff.1 ha)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {s : S ⟶ Sp o}

theorem isTM_unique (hL : Out.Laws) (hL2 : Out.Laws2) {m : ℕ} (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] [IsReduced R] (z : Sp R ⟶ S) (sw : Sp R ⟶ Sp o)
    (e : z ≫ s = sw) (w : TObj g (N' ^ 2) J b sw) (φ φ' : w.A.left ⟶ t.A.left) (h : IsTM w t z φ)
    (h' : IsTM w t z φ') : φ = φ' := by
  obtain ⟨β, rfl⟩ := spMap_surj sw
  obtain ⟨w', hw'⟩ := tObj_pull o g _ J b _ _ s _ z t e
  obtain ⟨ψ, hψ⟩ := tMap_iff.1 hw'
  obtain ⟨χ, rfl, hχ⟩ := hψ.cancel (h.congr (Category.id_comp z).symm rfl)
  obtain ⟨χ', rfl, hχ'⟩ := hψ.cancel (h'.congr (Category.id_comp z).symm rfl)
  rw [(GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β w w' hm hd ho ?_).2 χ χ' hχ.1 hχ'.1 hχ.2.1 hχ'.2.1
    fun i => (hχ.2.2.1 i).trans (hχ'.2.2.1 i).symm]
  refine Dense.mono (fun p _ => ?_) dense_univ
  obtain ⟨u, hu⟩ := tObj_pull o g _ J b _ _ _ _ ((Sp R).fromSpecResidueField p) w rfl
  refine ⟨(Sp R).residueField p, inferInstance, (Sp R).fromSpecResidueField p, u, ?_, hu, ?_⟩
  · exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply _ _⟩
  · have := tMap_comp hu (tMap_iff.2 ⟨_, hχ⟩)
    rwa [Category.comp_id] at this

theorem exists_hasTh_field (hL : Out.Laws) (hL2 : Out.Laws2) (ho : Odd N') (t : TObj g (N' ^ 2) J b s)
    (K : Type) [Field K] (y : Sp K ⟶ S) : ∃ v, t.HasTh y v := by
  obtain ⟨R, _, x, v, hx, hp, hv⟩ := ThetaLocal.exists_hasTh hL hL2 o g N' J b S s t ho (y (IsLocalRing.closedPoint K))
  have hr : Set.range y ⊆ Set.range x := by
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum K) q (IsLocalRing.closedPoint K)]
  obtain ⟨ρ, hρ⟩ := spMap_surj (IsOpenImmersion.lift x y hr)
  have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R K ρ x v hv
  rw [hρ, IsOpenImmersion.lift_fac] at this
  exact ⟨_, this⟩

theorem eval_eq_zero_of_fromC (hL : Out.Laws) (hL2 : Out.Laws2) {n : ℕ} (hn : 2 ≤ n) (hd : n ∣ N') (ho : Odd N')
    {em : o →+* ℂ} (hem : Function.Injective em) {C : TObj g (N' ^ 2) J b (spMap em) → Prop}
    (t : TObj g (N' ^ 2) J b s) {K : Type} [Field K] (y : Sp K ⟶ S) (hy : FromC em C t y) (β : o →+* K)
    (hβ : y ≫ s = spMap β) (v : Ix g (N' ^ 2) → K) (hv : t.HasTh y v) :
    ∀ F ∈ thIdeal em C, MvPolynomial.eval₂ β v F = 0 := by
  obtain ⟨K₀, _, β₀, i, j, t₀, tx, tc, hj, hi, h1, h2, h3, hC⟩ := hy
  obtain ⟨v₀, hv₀⟩ := exists_hasTh_field hL hL2 ho t₀ K₀ (𝟙 _)
  have a1 : tx.HasTh (𝟙 _) v := (hasTh_iff_of_tmap o g N' J b _ _ t _ _ tx y K _ v h1).2 (by rwa [Category.id_comp])
  have a2 : tx.HasTh (𝟙 _) (fun a => i (v₀ a)) := (hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tx _ K _ _ h2).2 (by
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ K i _ v₀ hv₀
    rwa [Category.comp_id, ← Category.id_comp (spMap i)] at this)
  have a3 : tc.HasTh (𝟙 _) (fun a => j (v₀ a)) := (hasTh_iff_of_tmap o g N' J b _ _ t₀ _ _ tc _ ℂ _ _ h3).2 (by
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b _ _ t₀ K₀ ℂ j _ v₀ hv₀
    rwa [Category.comp_id, ← Category.id_comp (spMap j)] at this)
  obtain ⟨c, hc⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b _ _ tx n K _ _ ⊥ hn hd a2 Ideal.isPrime_bot 0
  obtain ⟨u, hu⟩ := hasTh_unique_unit hL hL2 o g N' J b _ _ tx K _ _ _ a2 a1
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, rfl⟩) (Ne.isUnit (by simpa using hc)))
  obtain rfl : β = i.comp β₀ := spMap_inj (hβ.symm.trans (hi.trans (spMap_comp_eq _ _)))
  obtain rfl : v = fun a => (u : K) * i (v₀ a) := funext hu
  intro F hF
  rw [← F.sum_homogeneousComponent, MvPolynomial.eval₂_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  have hG := (GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g N' J b em C hem).2.1 F hF e
  have h0 : MvPolynomial.eval₂ em (fun a => j (v₀ a)) (MvPolynomial.homogeneousComponent e F) = 0 := by
    simp only [thIdeal, Ideal.mem_iInf] at hG
    exact hG tc _ ⟨hC, a3⟩
  have h4 : MvPolynomial.eval₂ β₀ v₀ (MvPolynomial.homogeneousComponent e F) = 0 := by
    apply j.injective
    rw [MvPolynomial.eval₂_comp_left, hj, map_zero]
    exact h0
  rw [eval₂_scale _ _ _ (MvPolynomial.homogeneousComponent_isHomogeneous e F)]
  have h5 := congrArg i h4
  rw [MvPolynomial.eval₂_comp_left, map_zero] at h5
  exact mul_eq_zero_of_right _ h5

theorem dense_affine {k : ℕ} {b : TBase o k} {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {t : TObj g k J b s}
    (hD : Dense (fromSet em C t)) {R : Type} [CommRing R] (x : Sp R ⟶ S) [IsOpenImmersion x] :
    Dense {p : Sp R | ∃ (K : Type) (_ : Field K) (ψ : R →+* K), p ∈ Set.range (spMap ψ) ∧ FromC em C t (spMap ψ ≫ x)} := by
  refine Dense.mono (fun p hp => ?_) (hD.preimage x.isOpenEmbedding.isOpenMap)
  obtain ⟨K, _, y, ⟨q, hq⟩, hy⟩ := hp
  have hr : Set.range y ⊆ Set.range x := by
    rintro _ ⟨q', rfl⟩
    rw [Subsingleton.elim (α := PrimeSpectrum K) q' q, hq]
    exact ⟨p, rfl⟩
  obtain ⟨ρ, hρ⟩ := spMap_surj (IsOpenImmersion.lift x y hr)
  have e : spMap ρ ≫ x = y := by rw [hρ, IsOpenImmersion.lift_fac]
  refine ⟨K, inferInstance, ρ, ⟨q, x.isOpenEmbedding.injective ?_⟩, by rwa [e]⟩
  rw [← Scheme.Hom.comp_apply, e, hq]

theorem inMM_of_dense (hL : Out.Laws) (hL2 : Out.Laws2) {n : ℕ} (hn : 2 ≤ n) (hd : n ∣ N') (ho : Odd N')
    {em : o →+* ℂ} (hem : Function.Injective em) {C : TObj g (N' ^ 2) J b (spMap em) → Prop}
    {t : TObj g (N' ^ 2) J b s} (hD : Dense (fromSet em C t)) {R : Type} [CommRing R] [IsReduced R] (x : Sp R ⟶ S)
    [IsOpenImmersion x] (β : o →+* R) (hβ : x ≫ s = spMap β) (v : Ix g (N' ^ 2) → R) (hv : t.HasTh x v) :
    InMM n N' (thIdeal em C) β v := by
  refine ⟨fun F hF => ?_, fun q hq => GlobalTheory.T.thetaCosetNonvanishing_of_hasTh hL hL2 o g N' J b S s t n R x v q hn hd hv hq⟩
  by_contra hne
  have hb : PrimeSpectrum.basicOpen (MvPolynomial.eval₂ β v F) ≠ ⊥ := fun h =>
    hne ((PrimeSpectrum.basicOpen_eq_bot_iff _).1 h).eq_zero
  obtain ⟨p, ⟨K, _, ψ, ⟨q, rfl⟩, hy⟩, hp⟩ := (dense_affine hD x).exists_mem_open
    (PrimeSpectrum.basicOpen (MvPolynomial.eval₂ β v F)).isOpen
    ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hb)
  have h0 := eval_eq_zero_of_fromC hL hL2 hn hd ho hem t _ hy (ψ.comp β)
    (by rw [Category.assoc, hβ, spMap_comp_eq]) _ (GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R K ψ x v hv) F hF
  refine hp (show ψ (MvPolynomial.eval₂ β v F) ∈ (show PrimeSpectrum K from q).asIdeal from ?_)
  rw [MvPolynomial.eval₂_comp_left]
  exact (show MvPolynomial.eval₂ (ψ.comp β) (ψ ∘ v) F = 0 from h0) ▸ Ideal.zero_mem _

theorem tMap_affine (hL : Out.Laws) (hL2 : Out.Laws2) {m : ℕ} (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    {em : o →+* ℂ} {C : TObj g (N' ^ 2) J b (spMap em) → Prop} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ}
    (w₀ : J) (hC : ∀ t, C t → t.Shape Mat κ) {M : Scheme.{0}} {sM : M ⟶ Sp o} (u : TObj g (N' ^ 2) J b sM)
    (hu : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ M) (t' : TObj g (N' ^ 2) J b (x ≫ sM)) v,
      t'.Shape Mat κ → t'.HasTh (𝟙 _) v → u.HasTh x v → TMap t' u x)
    {t : TObj g (N' ^ 2) J b s} (hD : Dense (fromSet em C t)) {R : Type} [CommRing R] [IsReduced R] (x : Sp R ⟶ S)
    [IsOpenImmersion x] (y : Sp R ⟶ M) (hxy : y ≫ sM = x ≫ s) (v : Ix g (N' ^ 2) → R) (hv : t.HasTh x v)
    (hv' : u.HasTh y v) (w : TObj g (N' ^ 2) J b (x ≫ s)) (hw : TMap w t x) : TMap w u y := by
  obtain ⟨β, hβ⟩ := spMap_surj (x ≫ s)
  obtain ⟨tx, htx⟩ := tObj_pull o g _ J b _ _ s _ x t hβ.symm
  obtain ⟨ux, hux⟩ := tObj_pull o g _ J b _ _ sM _ y u (hxy.trans hβ.symm)
  have key : TMap tx ux (𝟙 _) := by
    refine (GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β tx ux hm hd ho (Dense.mono (fun p hp => ?_) (dense_affine hD x))).1
    obtain ⟨K, _, ψ, ⟨q, rfl⟩, K₀, _, β₀, i, j, t₀, tK, tc, -, -, h1, h2, h3, hc⟩ := hp
    let a := algebraMap K (AlgebraicClosure K)
    have ez : spMap a ≫ spMap ψ = spMap (a.comp ψ) := spMap_comp_eq _ _
    obtain ⟨t', ht'⟩ := tObj_pull o g _ J b _ _ _ ((spMap (a.comp ψ) ≫ y) ≫ sM) (spMap (a.comp ψ)) tx
      (by rw [Category.assoc, hxy, hβ])
    obtain ⟨u', hu'⟩ := tObj_pull o g _ J b _ _ _ _ (spMap (a.comp ψ)) tx rfl
    have s0 : t₀.Shape Mat κ := ((GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ t₀ tc h3).2.2 K₀ rfl
      inferInstance inferInstance).1 (hC tc hc)
    have s1 : tK.Shape Mat κ := (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ t₀ tK h2).1 s0
    have m1 : TMap t' t (spMap (a.comp ψ) ≫ x) := tMap_comp ht' htx
    have m2 : TMap t' tK (spMap a) := tMap_cancel h1 (by rwa [← Category.assoc, ez])
    have s2 : t'.Shape Mat κ := (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w₀ w₀ _ _ _ _ _ tK t' m2).1 s1
    have m3 : TMap t' u (spMap (a.comp ψ) ≫ y) := hu _ _ t' _ s2
      ((hasTh_iff_of_tmap o g N' J b _ _ t _ _ t' _ _ _ _ m1).2 (by
        rw [Category.id_comp]; exact GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b S s t R _ (a.comp ψ) x v hv))
      (GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g N' J b M sM u R _ (a.comp ψ) y v hv')
    have m4 : TMap u' t' (𝟙 _) := tMap_cancel ht' (by rwa [Category.id_comp])
    have m5 := tMap_comp m4 m3
    rw [Category.id_comp] at m5
    refine ⟨AlgebraicClosure K, inferInstance, spMap (a.comp ψ), u', ⟨IsLocalRing.closedPoint _, ?_⟩, hu',
      tMap_cancel hux m5⟩
    rw [← ez]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Subsingleton.elim (α := PrimeSpectrum K) _ _))
  have m : TMap w tx (𝟙 _) := tMap_cancel htx (by rwa [Category.id_comp])
  have := tMap_comp (tMap_comp m key) hux
  rwa [Category.id_comp, Category.id_comp] at this

theorem family_universal : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (Y : MMPre n (n ^ j) (thIdeal em C)) (u : TObj g ((n ^ j) ^ 2) J b Y.s), (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g ((n ^ j) ^ 2) J b (x ≫ Y.s)) v, t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v → TMap t' u x) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → ∃! f : S ⟶ Y.MM, f ≫ Y.s = s' ∧ TMap t u f := by
  intro hL hL2 g J _ Mat κ n w w' hn hodd
  refine ⟨2, fun j hj o _ b em C d hem hC Y u hu hq S s' t hS hD => ?_⟩
  have ho : Odd (n ^ j) := hodd.pow
  have hd : n ^ 2 ∣ n ^ j := pow_dvd_pow n hj
  have hd1 : n ∣ n ^ j := dvd_pow_self n (by omega)
  have hred : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ S), IsOpenImmersion x → _root_.IsReduced R := fun R _ x _ =>
    (affine_isReduced_iff (CommRingCat.of R)).1 (isReduced_of_isOpenImmersion x)
  have uniq : ∀ (R : Type) [CommRing R] (y y' : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), y ≫ Y.s = y' ≫ Y.s →
      u.HasTh y v → u.HasTh y' v → y = y' := by
    intro R _ y y' v e h h'
    obtain ⟨β, hβ⟩ := spMap_surj (y ≫ Y.s)
    exact (Y.pts R β v (Y.loc R β y v hβ.symm ((hu R y v).1 h))).unique ⟨hβ.symm, (hu R y v).1 h⟩
      ⟨e.symm.trans hβ.symm, (hu R y' v).1 h'⟩
  choose R cR x v hx hp hv using ThetaLocal.exists_hasTh hL hL2 o g _ J b S s' t ho
  have loc : ∀ p, ∃ y : Sp (R p) ⟶ Y.MM, y ≫ Y.s = x p ≫ s' ∧ u.HasTh y (v p) := fun p => by
    have := hx p
    have := hred _ _ (hx p)
    obtain ⟨β, hβ⟩ := spMap_surj (x p ≫ s')
    obtain ⟨y, ⟨h1, h2⟩, -⟩ := Y.pts _ β _ (inMM_of_dense hL hL2 hn.two_le hd1 ho hem.2.2 hD (x p) β hβ.symm _ (hv p))
    exact ⟨y, h1.trans hβ, (hu _ _ _).2 h2⟩
  choose y hy hy' using loc
  choose tx htx using fun p => tObj_pull o g _ J b _ _ s' _ (x p) t rfl
  have hty : ∀ p, TMap (tx p) u (y p) := fun p =>
    haveI := hx p
    haveI := hred _ _ (hx p)
    tMap_affine hL hL2 hn.two_le hd ho w (fun t ht => (hC.shape t ht).1) u
      (fun K _ _ x t' v h1 h2 h3 => hq K x t' v h1 h2 ((hu _ _ _).1 h3)) hD (x p) (y p) (hy p) (v p) (hv p) (hy' p)
      (tx p) (htx p)
  have tr : ∀ p (T : Type) [CommRing T] (a : Sp T ⟶ Sp (R p)) (c : Ix g ((n ^ j) ^ 2) → T),
      t.HasTh (a ≫ x p) c → u.HasTh (a ≫ y p) c := fun p T _ a c h =>
    (hasTh_iff_of_tmap o g _ J b _ _ u _ _ (tx p) _ T a c (hty p)).1
      ((hasTh_iff_of_tmap o g _ J b _ _ t _ _ (tx p) _ T a c (htx p)).2 h)
  obtain ⟨f, hf⟩ := exists_glue _ x y hx (fun p => ⟨p, hp p⟩) fun i i' q hq => by
    have := hx i
    have := hx i'
    obtain ⟨T, z, hz, ⟨r, hr⟩, hs⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (U := (x i).opensRange ⊓ (x i').opensRange) (x := x i q) ⟨⟨q, rfl⟩, hq⟩
    obtain ⟨a, e1⟩ : ∃ a : Sp T ⟶ Sp (R i), a ≫ x i = z :=
      ⟨_, IsOpenImmersion.lift_fac (x i) z (fun p hp => (hs hp).1)⟩
    obtain ⟨a', e2⟩ : ∃ a' : Sp T ⟶ Sp (R i'), a' ≫ x i' = z :=
      ⟨_, IsOpenImmersion.lift_fac (x i') z (fun p hp => (hs hp).2)⟩
    have : IsOpenImmersion (a ≫ x i) := by rw [e1]; exact hz
    refine ⟨_, a, a', IsOpenImmersion.of_comp a (x i), ⟨r, (x i).isOpenEmbedding.injective ?_⟩, e1.trans e2.symm, ?_⟩
    · rw [← Scheme.Hom.comp_apply, e1, hr]
    · obtain ⟨ρ, hρ⟩ := spMap_surj (R' := T) a
      have h := GlobalTheory.T.hasThetaConstants_ring_baseChange hL2 o g _ J b S s' t _ T ρ (x i) (v i) (hv i)
      rw [hρ] at h
      refine uniq T _ _ _ ?_ (tr i T a _ h) (tr i' T a' _ (by rw [e2, ← e1]; exact h))
      rw [Category.assoc, Category.assoc, hy, hy, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ s') (e1.trans e2.symm)
  have hfs : f ≫ Y.s = s' := hom_ext_loc fun p => ⟨_, x p, hx p, hp p, by rw [← Category.assoc, hf, hy]⟩
  refine ⟨f, ⟨hfs, ?_⟩, fun f' hf' => hom_ext_loc fun p => ⟨_, x p, hx p, hp p, ?_⟩⟩
  · obtain ⟨u', hu'⟩ := tObj_pull o g _ J b _ _ Y.s s' f u hfs
    have := tMap_comp (tMap_of_loc hL.globalFns t u'
      (fun p => ⟨_, x p, tx p, hx p, hp p, htx p, tMap_cancel hu' (by rw [hf]; exact hty p)⟩)
      (fun t T _ z => tObj_pull o g _ J b _ _ s' _ z t rfl)
      (fun t T _ z w φ φ' hz h h' => haveI := hred T z hz
        isTM_unique hL hL2 hn.two_le hd ho t T z _ rfl w φ φ' h h')) hu'
    rwa [Category.id_comp] at this
  · rw [hf]
    exact uniq _ _ _ (v p) (by rw [Category.assoc, hf'.1, hy])
      ((hasTh_iff_of_tmap o g _ J b _ _ u _ _ t f' _ (x p) (v p) hf'.2).1 (hv p)) (hy' p)

end GlobalTheory.FamRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalPropertyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIdealFamily_universal_property : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (Y : MMPre n (n ^ j) (thIdeal em C)) (u : TObj g ((n ^ j) ^ 2) J b Y.s), (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g ((n ^ j) ^ 2) J b (x ≫ Y.s)) v, t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v → TMap t' u x) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → ∃! f : S ⟶ Y.MM, f ≫ Y.s = s' ∧ TMap t u f := by
  first | exact @GlobalTheory.FamRep.family_universal | exact GlobalTheory.FamRep.family_universal | (intros; apply GlobalTheory.FamRep.family_universal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddedAbelianVarietyCutOutByTorsionForms
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddedAbelianVarietyCutOutByTorsionForms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.ZV

namespace GlobalTheory.EmbCut

theorem powIsLB {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) : (lbPow L n).IsLB :=
  DVR.linComb_isLB L hL _ _

theorem isoPullAlong {X Y : Scheme.{0}} {L M : LB X} (h : LBIso L M) (j : Y ⟶ X) : LBIso (L.pull j) (M.pull j) :=
  LBIso.chartPull (Geo.Tor.chartPullPull L j j rfl) (Geo.Tor.chartPullPull M j j rfl) h

theorem symB_of_iso {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left} (hL : L.IsLB) (hs : SymB L)
    {Y : Scheme.{0}} (e : Y ≅ A.left) {M : LB Y} (hM : M.IsLB) (N : ℕ) (h : LBIso M ((lbPow L N).pull e.hom)) :
    SymB (A := A) (M.pull e.inv) := by
  have h1 : LBIso (M.pull e.inv) (lbPow L N) :=
    LBIso.chartPull (Geo.Tor.chartPullPull M e.inv e.inv rfl) (Geo.Tor.chartPullSec _ e.hom e.inv e.inv_hom_id) h
  have hN := powIsLB hL N
  have hM' := LB.isLB_pull hM e.inv
  obtain ⟨-, a, -, -, c, -⟩ := GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K A.left A.hom L hL
  exact LBIso.trans hM' hN (LB.isLB_pull hM' _) h1 (LBIso.trans hN (LB.isLB_pull hN _) (LB.isLB_pull hM' _)
    (LBIso.trans hN (powIsLB (LB.isLB_pull hL _) N) (LB.isLB_pull hN _) ((a _ (LB.isLB_pull hL _) hs).2 N) (c _ _ N))
    (isoPullAlong h1.symm _))

theorem sectionsHaveFiniteDimension_of_iso_pulled_pow {K : Type} [Field K] {X Y : Scheme.{0}} (p : X ⟶ Sp K) {L : LB X} (hL : L.IsLB)
    (e : Y ≅ X) {M : LB Y} (hM : M.IsLB) (N : ℕ) (h : LBIso M ((lbPow L N).pull e.hom)) (n r : ℕ)
    (hr : SectionsHaveFiniteDimension p (lbPow L (N * n)) r) : SectionsHaveFiniteDimension (e.hom ≫ p) (lbPow M n) r := by
  have hN := powIsLB hL N
  have h1 : SectionsHaveFiniteDimension p (lbPow (lbPow L N) n) r :=
    ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p _ (powIsLB hL (N * n))).2.1 _ (powIsLB hN n)
      ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p L hL).2.2.1 N n).symm).1 r hr
  have h2 := ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p _ (powIsLB hN n)).2.2.2.2.2 Y e r).1 h1
  have h3 : LBIso (lbPow M n) ((lbPow (lbPow L N) n).pull e.hom) :=
    LBIso.trans (powIsLB hM n) (powIsLB (LB.isLB_pull hN _) n) (LB.isLB_pull (powIsLB hN n) _)
      (((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K Y (e.hom ≫ p) M hM).2.1 _ (LB.isLB_pull hN _) h).2 n)
      ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p _ hN).2.2.2.2.1 Y e.hom n)
  exact ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K Y (e.hom ≫ p) _ (LB.isLB_pull (powIsLB hN n) _)).2.1 _ (powIsLB hM n) h3.symm).1 r h2

end GlobalTheory.EmbCut

namespace GlobalTheory


open EmbCut in
theorem cutBy_embedded_abelian : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)), ∃ (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p : Hh → Ix g ((n ^ j) ^ 2) → K), t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab (hh h) ^ n ^ j)).left (p h)) → CutBy (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) Q d p := by
  intro H H2 g J _ Mat κ n hn hodd
  have hn2 := hn.two_le
  haveI : NeZero ((n ^ 2) ^ 2) := ⟨by positivity⟩
  obtain ⟨d, k₀, hd⟩ := GlobalTheory.T.abelianVariety_cut_out_bounded_degree_torsion H H2 g ((n ^ 2) ^ 2) (Ix g ((n ^ 2) ^ 2))
  refine ⟨max 2 k₀, fun j hj o _ b => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨by positivity⟩
  have hdvd : n ^ 2 ∣ n ^ j := pow_dvd_pow n (le_of_max_le_left hj)
  have hdvd' : (n ^ 2) ^ 2 ∣ (n ^ j) ^ 2 := pow_dvd_pow_of_dvd hdvd 2
  obtain ⟨Q, hQ⟩ := hd _ le_rfl (Ix g ((n ^ j) ^ 2)) (fun a i => ZMod.castHom hdvd' (ZMod ((n ^ 2) ^ 2)) (a i))
    (fun c => by
      choose a ha using fun i => ZMod.castHom_surjective hdvd' (c i)
      exact ⟨a, funext ha⟩)
  refine ⟨Ix g ((n ^ j) ^ 2), inferInstance, id, Q, d, fun K _ _ β t σ p hE hp => ?_⟩
  obtain ⟨hiso, hM, hV, hL, hmod, -, hlab⟩ := GlobalTheory.T.thetaSections_veryAmple_periodic H H2 o g (n ^ j) J b K β t (n ^ 2) σ hodd.pow hdvd
    (by nlinarith) hE
  let e : (Over.mk (𝟙 (Sp K)) ⊗ t.A).left ≅ t.A.left := asIso (snd (Over.mk (𝟙 (Sp K))) t.A).left
  have he : e.hom ≫ t.A.hom = (fst (Over.mk (𝟙 (Sp K))) t.A).left :=
    pullback.condition.symm.trans (Category.comp_id _)
  have hk : ((n ^ j : ℕ) : K) ≠ 0 := fun h => by
    have := (b.unit.map β).ne_zero
    rw [map_natCast, Nat.cast_pow, h] at this
    exact this (by simp)
  have key := hQ K t.pol rfl _ e _ σ (n ^ j) _ (fun h => t.lab h ^ n ^ j) p hM
    (symB_of_iso t.isLB (GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample H H2 K t.pol).2.2.1 e hM _ hL) (he.symm ▸ hV)
    (fun a a' h => hmod a a' fun i => by
      have := congrFun h i
      rw [← ZMod.natCast_eq_natCast_iff]
      simpa only [ZMod.castHom_apply, ZMod.natCast_val] using this)
    (fun m hm => sectionsHaveFiniteDimension_of_iso_pulled_pow t.A.hom t.isLB e hM _ hL m _ (by
      rw [← mul_pow]
      exact PowSec.exists_basis_sections H.globalSectionsRank K t.pol _ (Nat.mul_pos (by positivity) hm)))
    ((le_of_max_le_right hj).trans (Nat.lt_pow_self hn2).le) hk hlab
    (fun h => by
      have : (t.lab h ^ n ^ j).left ≫ e.inv = (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j)).left := by
        rw [Iso.comp_inv_eq]
        exact (congrArg (fun q => q.left) (lift_snd (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab h ^ n ^ j))).symm
      exact this.symm ▸ hp h)
  exact he ▸ key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddedAbelianVarietyCutOutByTorsionFormsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddedAbelianVariety_cutOut_by_torsionForms : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)), ∃ (Hh : Type) (_ : Finite Hh) (hh : Hh → Ix g ((n ^ j) ^ 2)) (Q : Polynomial ℚ) (d : ℕ), ∀ (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap β)) σ (p : Hh → Ix g ((n ^ j) ^ 2) → K), t.Emb (n ^ 2) (Over.mk (𝟙 _)) σ → (∀ h, SecCoord _ σ (lift (𝟙 (Over.mk (𝟙 (Sp K)))) (t.lab (hh h) ^ n ^ j)).left (p h)) → CutBy (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) Q d p := by
  first | exact @GlobalTheory.cutBy_embedded_abelian | exact GlobalTheory.cutBy_embedded_abelian | (intros; apply GlobalTheory.cutBy_embedded_abelian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SumMonomialAddSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.VolPoly

theorem eval_eq_of_eventually {r r' : ℕ} (Ψ : MvPolynomial (Fin (r + 1)) ℚ) (Ψ' : MvPolynomial (Fin (r' + 1)) ℚ)
    (a : Fin (r + 1) → ℤ) (a' : Fin (r' + 1) → ℤ)
    (h : ∀ᶠ t : ℕ in Filter.atTop,
      MvPolynomial.eval (fun i => (((a + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i : ℤ) : ℚ)) Ψ =
        MvPolynomial.eval (fun i => (((a' + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i : ℤ) : ℚ)) Ψ') :
    MvPolynomial.eval (fun i => (a i : ℚ)) Ψ = MvPolynomial.eval (fun i => (a' i : ℚ)) Ψ' := by
  have key : ∀ {r : ℕ} (Ψ : MvPolynomial (Fin (r + 1)) ℚ) (a : Fin (r + 1) → ℤ), ∃ p : Polynomial ℚ,
      ∀ t : ℕ, p.eval (t : ℚ) =
        MvPolynomial.eval (fun i => (((a + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i : ℤ) : ℚ)) Ψ := by
    intro r Ψ a
    refine ⟨MvPolynomial.aeval (fun i => Polynomial.C (a i : ℚ) + if i = 0 then Polynomial.X else 0) Ψ, fun t => ?_⟩
    rw [← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval]
    congr 2
    funext i
    by_cases hi : i = 0 <;> simp [hi, Pi.single_apply]
  obtain ⟨p, hp⟩ := key Ψ a
  obtain ⟨p', hp'⟩ := key Ψ' a'
  have e : p = p' := by
    obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1 h
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite t₀).image (f := fun t : ℕ => (t : ℚ)) Nat.cast_injective.injOn)
    rintro _ ⟨t, ht, rfl⟩
    show p.eval (t : ℚ) = p'.eval (t : ℚ)
    rw [hp, hp', ht₀ t ht]
  have h0 := (hp 0).symm.trans (e ▸ hp' 0)
  simpa using h0

theorem sum_monomial_add_single {r : ℕ} (a : Fin (r + 1) → ℤ) (t : ℕ) :
    ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) ((a + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i) =
      ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) (a i) + (t : Polynomial ℤ) := by
  simp only [Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
  congr 1
  rw [Fin.sum_univ_succ]
  simp

theorem exists_poly_extension (g : ℕ) (A : Polynomial ℤ → Prop) (V : Polynomial ℤ → ℚ → Prop)
    (hV : ∀ F x y, V F x → V F y → x = y)
    (hΨ : ∀ r : ℕ, ∃ Ψ : MvPolynomial (Fin r) ℚ, Ψ.IsHomogeneous g ∧ ∀ a : Fin r → ℤ,
      A (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) →
        V (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) (MvPolynomial.eval (fun i => (a i : ℚ)) Ψ))
    (hA : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, A (F + t)) :
    ∃ D : Polynomial ℤ → ℚ, (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous g ∧ ∀ a : Fin r → ℤ,
      D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) ∧
      ∀ F, A F → V F (D F) := by
  choose Ψ hh hΨ using hΨ
  have hF : ∀ F : Polynomial ℤ,
      ∑ i : Fin (F.natDegree + 1), Polynomial.monomial (i : ℕ) (F.coeff i) = F := fun F => by
    rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (F.coeff i))]
    exact (F.as_sum_range).symm
  refine ⟨fun F => MvPolynomial.eval (fun i : Fin (F.natDegree + 1) => (F.coeff i : ℚ)) (Ψ _), fun r => ?_,
    fun F h => ?_⟩
  · refine ⟨MvPolynomial.aeval (Fin.snoc (α := fun _ => MvPolynomial (Fin r) ℚ) MvPolynomial.X 0) (Ψ (r + 1)), ?_,
      fun a => ?_⟩
    · have := (hh (r + 1)).aeval (n := 1) (Fin.snoc (α := fun _ => MvPolynomial (Fin r) ℚ) MvPolynomial.X 0)
        (fun i => by
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using MvPolynomial.isHomogeneous_zero _ _ _
          · simpa using MvPolynomial.isHomogeneous_X _ _)
      simpa using this
    · set F := ∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i) with hFa
      have e : ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) (Fin.snoc (α := fun _ => ℤ) a 0 i) = F := by
        rw [Fin.sum_univ_castSucc]
        simp [hFa]
      have e₂ := eval_eq_of_eventually (Ψ (F.natDegree + 1)) (Ψ (r + 1)) (fun i => F.coeff i)
        (Fin.snoc (α := fun _ => ℤ) a 0) ((hA F).mono fun t ht => by
          have h₁ := hΨ _ ((fun i : Fin (F.natDegree + 1) => F.coeff i) + Pi.single (M := fun _ => ℤ) 0 (t : ℤ))
          have h₂ := hΨ _ (Fin.snoc (α := fun _ => ℤ) a 0 + Pi.single (M := fun _ => ℤ) 0 (t : ℤ))
          rw [sum_monomial_add_single, hF] at h₁
          rw [sum_monomial_add_single, e] at h₂
          exact hV _ _ _ (h₁ ht) (h₂ ht))
      refine e₂.trans ?_
      rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply]
      congr 2
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  · have := hΨ _ (fun i : Fin (F.natDegree + 1) => F.coeff i)
    rw [hF] at this
    exact this h

theorem relAmple_of_cls_eq {K : Type} [Field K] (P : Out.PolAV (Sp K)) {M N : LB P.A.left} (hM : M.IsLB) (hN : N.IsLB)
    (e : CechPic.cls M hM = CechPic.cls N hN) (h : Out.RelAmple P.A M) : Out.RelAmple P.A N := by
  haveI : IsProper P.A.hom := P.isAb.proper
  rw [relAmple_iff_isAmpleLB_of_isAffine P.A hM] at h
  rw [relAmple_iff_isAmpleLB_of_isAffine P.A hN]
  exact h.of_lbIso hN ((CechPic.cls_eq_iff hN hM).1 e.symm)

theorem exists_vol_poly : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → FormIs P M s → ∀ (ev : Polynomial ℤ → (P.A ⟶ P.A)), ev 1 = 𝟙 P.A → (∀ F G, ev (F + G) = ev F * ev G) → (∀ F, ev (Polynomial.X * F) = ev F ≫ s) → ∃ D : Polynomial ℤ → ℚ, (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous P.g ∧ ∀ a : Fin r → ℤ, D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) ∧ (∀ F, Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) → Vol P.A.hom (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) P.g ((D F : ℚ) : ℝ)) ∧ ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (F + t)] P.L) ∧ IsFinite (ev (F + t)).left := by
  intro h₁ h₂ K _ _ P M s hM hs ev e₁ eadd eX
  obtain ⟨-, emul, hform, -, hdiv, hone, -⟩ := (GlobalTheory.T.polarisationForm_intPolynomial_bundles h₁ h₂ K P M s hM hs).2 ev e₁ eadd eX
  have hB : ∀ F, (cubeLB P.A ![𝟙 P.A, ev F] P.L).IsLB := fun F => LB.isLB_linComb P.isLB _ _
  let b : Polynomial ℤ →+ CechPic.Pic P.A.left := AddMonoidHom.mk' (fun F => CechPic.cls _ (hB F)) fun F G => by
    have := (CechPic.cls_eq_iff (LB.isLB_div (hB _) (hB _)) (hB _)).2 (hdiv F G)
    rw [CechPic.cls_div (hB _) (hB _)] at this
    exact (sub_eq_iff_eq_add'.1 this)
  have hb : ∀ F, b F = CechPic.cls _ (hB F) := fun _ => rfl
  have hp : ∀ n, (lbPow P.L n).IsLB := fun n => LB.isLB_linComb P.isLB _ _
  have b₁ : b 1 = 2 • CechPic.cls _ P.isLB :=
    ((CechPic.cls_eq_iff (hB 1) (hp 2)).2 hone).trans (CechPic.cls_lbPow P.isLB 2 _)
  have hA : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (F + t)] P.L) := fun F => by
    have h := GlobalTheory.T.eventually_section_and_relAmple_pow_div K P P.L _ P.isLB (hB (-F)) P.ample
    have ht : Filter.Tendsto (fun t : ℕ => t * 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun t => by show t ≤ t * 2; omega) Filter.tendsto_id
    refine (ht.eventually h).mono fun t h => relAmple_of_cls_eq P (LB.isLB_div (hp _) (hB _)) (hB _) ?_ h.2
    rw [CechPic.cls_div (hp _) (hB _), CechPic.cls_lbPow P.isLB, ← hb, ← hb, map_neg, map_add (f := _), ← nsmul_one t,
      map_nsmul, b₁, mul_smul, sub_neg_eq_add, add_comm]
  obtain ⟨D, hD, hD'⟩ := exists_poly_extension P.g (fun F => Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev F] P.L))
    (fun F x => Vol P.A.hom (cubeLB P.A ![𝟙 P.A, ev F] P.L) P.g (x : ℝ))
    (fun F x y hx hy => by exact_mod_cast (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g (hB F)).2.1 _ _ hx hy)
    (fun r => by
      let φ : Fin r × ULift.{0} (Finset (Fin 2)) → (P.A.left ⟶ P.A.left) := fun p =>
        (psum P.A ![𝟙 P.A, ev (Polynomial.monomial (p.1 : ℕ) 1)] p.2.down).left
      obtain ⟨Φ, hΦ, hv⟩ := GlobalTheory.T.exists_homogeneousPolynomial_volume_pullback_combinations h₁ h₂ K P _ φ
      refine ⟨MvPolynomial.aeval (fun p : Fin r × ULift.{0} (Finset (Fin 2)) =>
        MvPolynomial.C ((-1 : ℚ) ^ (2 - p.2.down.card)) * MvPolynomial.X p.1) Φ, ?_, fun a ha => ?_⟩
      · simpa using hΦ.aeval (n := 1) (fun p : Fin r × ULift.{0} (Finset (Fin 2)) =>
          MvPolynomial.C ((-1 : ℚ) ^ (2 - p.2.down.card)) * MvPolynomial.X p.1)
          fun p => (MvPolynomial.isHomogeneous_X ℚ p.1).C_mul _
      · let ε : Fin r × ULift.{0} (Finset (Fin 2)) → ℤ := fun p => a p.1 * (-1) ^ (2 - p.2.down.card)
        have hC : (LB.LinComb P.L φ ε).IsLB := LB.isLB_linComb P.isLB _ _
        have e : CechPic.cls _ (hB (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i))) = CechPic.cls _ hC := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [← hb, map_sum, CechPic.cls_linComb P.isLB, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun i _ => ?_
          have : Polynomial.monomial (i : ℕ) (a i) = a i • Polynomial.monomial (i : ℕ) (1 : ℤ) := by
            rw [Polynomial.smul_monomial, smul_eq_mul, _root_.mul_one]
          rw [this, map_zsmul, hb]
          refine (congrArg (a i • ·) (CechPic.cls_linComb P.isLB _ _ _)).trans ?_
          simp only [Finset.smul_sum, ε, φ, mul_smul]
        have := (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hC).2.2.1 _ _ (hB _) ((CechPic.cls_eq_iff _ _).1 e.symm)
          (hv ε (relAmple_of_cls_eq P (hB _) hC e ha))
        convert this using 2
        rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply]
        congr 2
        funext p
        simp [ε, mul_comm])
    hA
  refine ⟨D, hD, hD', fun F => (hA F).mono fun t ht => ⟨ht, ?_⟩⟩
  have hf := (GlobalTheory.FormFinite.isFinite_and_surjective_of_formIs h₁ h₂ K P _ _ (hB _) ht (hform _)).1
  rw [mul_comm, emul, Over.comp_left] at hf
  haveI : IsProper P.A.hom := P.isAb.proper
  haveI : IsSeparated ((ev 2).left ≫ P.A.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated (ev 2).left := IsSeparated.of_comp _ P.A.hom
  exact IsFinite.of_comp _ (ev 2).left

end GlobalTheory.VolPoly

end
end
