module

public import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafDescPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

abbrev resO (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (V : X.Opens) (n i : ℤ) :
    Hs q (opn U) n i →+ Hs q (opn (V.ι ⁻¹ᵁ U)) n i :=
  Hs.pull q (opnMap V.ι (V.ι ⁻¹ᵁ U) U le_rfl) n i

def LocVanO (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop := ∀ (x : X) (W : X.Opens), x ∈ W →
  ∃ V : X.Opens, V ≤ W ∧ x ∈ V ∧ ∀ n < m, Subsingleton (Hs q (opn (V.ι ⁻¹ᵁ U)) n i)

def SepO (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop := ∀ s : Hs q (opn U) m i,
  (∀ x : X, x ∉ U → ∃ V : X.Opens, x ∈ V ∧ resO q U V m i s = 0) → s = 0

def GlueO (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop :=
  ∀ (A : Type) (V : A → X.Opens) (s : ∀ a, Hs q (opn ((V a).ι ⁻¹ᵁ U)) m i), (∀ x : X, x ∉ U → ∃ a, x ∈ V a) →
  (∀ a b, ∀ x ∈ V a, x ∈ V b → x ∉ U → ∃ (T : X.Opens) (ha : T ≤ V a) (hb : T ≤ V b)
    (ha' : T.ι ⁻¹ᵁ U ≤ X.homOfLE ha ⁻¹ᵁ ((V a).ι ⁻¹ᵁ U)) (hb' : T.ι ⁻¹ᵁ U ≤ X.homOfLE hb ⁻¹ᵁ ((V b).ι ⁻¹ᵁ U)),
    x ∈ T ∧ Hs.pull q (opnMap (X.homOfLE ha) _ _ ha') m i (s a) = Hs.pull q (opnMap (X.homOfLE hb) _ _ hb') m i (s b)) →
  ∃ c, ∀ a, resO q U (V a) m i c = s a

def LeafDescOSep : Prop := LeafDict → LeafFlq → ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ),
  LocVanO q U m i → SepO q U m i

def LeafDescOGlue : Prop := LeafDict → LeafFlq → ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ),
  LocVanO q U m i → GlueO q U m i

def LeafPcVan : Prop := ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ), LocVan q U m i → LocVanO q U m i

def LeafPcSep : Prop := ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ), SepO q U m i → Sep q U m i

def LeafPcGlue : Prop := ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ), GlueO q U m i → Glue q U m i

theorem opnMap_id {X : Scheme.{0}} (U : X.Opens) (h) : opnMap (𝟙 X) U U h = 𝟙 _ := by
  apply Arrow.hom_ext
  · change sch.map _ = sch.map (𝟙 _)
    congr 1
    exact (Scheme.Hom.resLE_id (X := X) (V := U) (V' := U) le_rfl).trans (Scheme.homOfLE_rfl _ _)
  · exact sch.map_id X

theorem dbl_id (P : Arrow Spc) : dbl.map (𝟙 P) = 𝟙 _ := by
  set_option synthInstance.maxHeartbeats 200000 in
   apply pushout.hom_ext
  · change dbl.inl _ ≫ _ = _
    rw [inl_map]; erw [Category.id_comp]
  · change dbl.inr _ ≫ _ = _
    rw [dbl.inr_map]; erw [Category.id_comp]

theorem Hs_pull_id (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (h) (n i : ℤ) (c : Hs q (opn U) n i) :
    Hs.pull q (opnMap (𝟙 X) U U h) n i c = c := by
  apply Subtype.ext
  rw [opnMap_id]
  change pull _ (dbl.map _) _ n c.1 = c.1
  rw [dbl_id, pull_id]

section
variable {q : ℕ} {X : Scheme.{0}} {U : X.Opens}

instance (p : Pc U) : IsOpenImmersion p.j := p.op

theorem pc_le (p : Pc U) : p.V ≤ p.j.isoOpensRange.hom ⁻¹ᵁ (p.j.opensRange.ι ⁻¹ᵁ U) := by
  rw [p.hV]
  intro y hy
  change (p.j.isoOpensRange.hom ≫ p.j.opensRange.ι) y ∈ U
  rw [Scheme.Hom.isoOpensRange_hom_ι]; exact hy

theorem pc_le' (p : Pc U) : p.j.opensRange.ι ⁻¹ᵁ U ≤ p.j.isoOpensRange.inv ⁻¹ᵁ p.V := by
  rw [p.hV]
  intro y hy
  change (p.j.isoOpensRange.inv ≫ p.j) y ∈ U
  rw [Scheme.Hom.isoOpensRange_inv_comp]; exact hy

theorem pc_bij (p : Pc U) (n i : ℤ) :
    Function.Bijective (Hs.pull q (opnMap p.j.isoOpensRange.hom p.V _ (pc_le p)) n i) := by
  refine ⟨Function.LeftInverse.injective (g := Hs.pull q (opnMap p.j.isoOpensRange.inv _ _ (pc_le' p)) n i) ?_,
    Function.RightInverse.surjective (g := Hs.pull q (opnMap p.j.isoOpensRange.inv _ _ (pc_le' p)) n i) ?_⟩
  · intro c
    exact (pull_pull _ _ p.j.isoOpensRange.inv_hom_id _ _ _ _ _ (fun _ hy => hy) n i c).trans (Hs_pull_id q _ _ n i c)
  · intro c
    exact (pull_pull _ _ p.j.isoOpensRange.hom_inv_id _ _ _ _ _ (fun _ hy => hy) n i c).trans (Hs_pull_id q _ _ n i c)

theorem pc_res (p : Pc U) (n i : ℤ) (s : Hs q (opn U) n i) :
    p.res q n i s = Hs.pull q (opnMap p.j.isoOpensRange.hom p.V _ (pc_le p)) n i (resO q U p.j.opensRange n i s) :=
  (pull_pull _ _ (Scheme.Hom.isoOpensRange_hom_ι p.j) _ _ _ _ _ _ n i s).symm
end

theorem LeafPcVan_pf : LeafPcVan := by
  intro q X U m i hL x W hx
  obtain ⟨p, hxp, hpW, hs⟩ := hL x W hx
  refine ⟨p.j.opensRange, fun y hy => hpW hy, hxp, fun n hn => ?_⟩
  have := hs n hn
  exact (pc_bij p n i).1.subsingleton

theorem LeafPcSep_pf : LeafPcSep := by
  intro q X U m i hS s hs
  apply hS s
  intro x hx
  obtain ⟨p, hxp, h0⟩ := hs x hx
  refine ⟨p.j.opensRange, hxp, ?_⟩
  apply (pc_bij p m i).1
  rw [← pc_res, h0, map_zero]

theorem LeafDesc_of (hD : LeafDict) (hF : LeafFlq) (hS : LeafDescOSep) (hG : LeafDescOGlue) (hPG : LeafPcGlue) :
    LeafDesc := by
  intro q X U m i hL
  have hO := LeafPcVan_pf q U m i hL
  exact ⟨LeafPcSep_pf q U m i (hS hD hF q U m i hO), hPG q U m i (hG hD hF q U m i hO)⟩

end LateralTheory.CohomologicalPurity.Cl
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafGeoPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.GeoPf

theorem vec_map_comp {N k : ℕ} {Z Y X : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (v : Vec N k X) :
    (Vec.map N k (g ≫ f)).obj v = (Vec.map N k g).obj ((Vec.map N k f).obj v) := by
  apply Subtype.ext
  funext i
  change (g ≫ f).appTop.hom (v.1 i) = g.appTop.hom (f.appTop.hom (v.1 i))
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem sch_map_pt {N k : ℕ} {Y X : Scheme.{0}} (f : Y ⟶ X) (v : Vec N k X) :
    sch.map f ≫ Pj.pt v = Pj.pt ((Vec.map N k f).obj v) := by
  ext n U g
  change (Functor.const (Fin (n.unop.len + 1))).obj ((Vec.map N k (g ≫ f)).obj v) =
    (Functor.const (Fin (n.unop.len + 1))).obj ((Vec.map N k g).obj ((Vec.map N k f).obj v))
  exact congrArg (Functor.const (Fin (n.unop.len + 1))).obj (vec_map_comp (show U.unop ⟶ Y from g) f v)

theorem part3 (d : ℕ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (x : Fin d → A) :
    spMap φ ≫ Pj.pt (vec1 x) = Pj.pt (vec1 (φ ∘ x)) := by
  change sch.map _ ≫ _ = _
  rw [sch_map_pt]
  congr 1
  apply Subtype.ext
  funext i
  change (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) i)) =
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom ((Fin.cons 1 (φ ∘ x) : Fin (d + 1) → B) i)
  have key := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  have := congrArg (fun g => g.hom ((Fin.cons 1 x : Fin (d + 1) → A) i)) key
  refine this.symm.trans ?_
  change (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (φ ((Fin.cons 1 x : Fin (d + 1) → A) i)) = _
  congr 1
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem part2 (q N k : ℕ) (R : Type) [CommRing R] (hq : IsUnit (q : R)) : Inv q (PR N k R) := by
  intro U ⟨y⟩
  let f : U ⟶ Spec (CommRingCat.of R) := ((prod.snd : PR N k R ⟶ sp R).app _).app (op U) y
  have h := (hq.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map f.appTop.hom
  rwa [map_natCast, map_natCast] at h

theorem comp_val {N k : ℕ} {U : Scheme.{0}} {a b c : Vec N k U} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).1 = g.1 * f.1 := rfl

theorem eqToHom_val {N k : ℕ} {U : Scheme.{0}} {a b : Vec N k U} (e : a = b) : (eqToHom e).1 = 1 := by
  subst e; rfl

theorem incl_map_val {N : ℕ} {U : Scheme.{0}} {a b : Vec N 1 U} (u : a ⟶ b) : ((Vec.incl N U).map u).1 = u.1 := rfl

theorem incl_cancel {N : ℕ} {U : Scheme.{0}} {J : Type} [Category J] (F G : J ⥤ Vec N 1 U)
    (h : F ⋙ Vec.incl N U = G ⋙ Vec.incl N U) : F = G := by
  have hobj : ∀ j, F.obj j = G.obj j := fun j => Subtype.ext (by have := congrArg Subtype.val (Functor.congr_obj h j); exact this)
  refine CategoryTheory.Functor.ext hobj (fun a b f => ?_)
  apply Subtype.ext
  have h2 := congrArg Subtype.val (Functor.congr_hom h f)
  simp only [Functor.comp_map, comp_val, eqToHom_val, incl_map_val, mul_one, one_mul] at h2 ⊢
  exact h2

theorem incl_mono (N : ℕ) : Mono (Pj.incl N) := by
  have : ∀ n, Mono ((Pj.incl N).app n) := fun n => by
    have : ∀ U, Mono (((Pj.incl N).app n).app U) := fun U => by
      rw [mono_iff_injective]
      intro F G h
      exact incl_cancel (U := U.unop) F G h
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

theorem part1 (d : ℕ) (R : Type) [CommRing R] : Mono (pr d R).hom := by
  have := incl_mono (d + 1)
  change Mono (prod.map _ _)
  infer_instance

theorem pt_incl {N : ℕ} {X : Scheme.{0}} (v : Vec N 1 X) :
    Pj.pt v ≫ Pj.incl N = Pj.pt ((Vec.incl N X).obj v) := rfl

theorem part4 (d : ℕ) (A : Type) [CommRing A] (I : Ideal A) (x : Fin d → A) (hI : Ideal.span (Set.range x) = I) :
    ∃ Φ : opn (off A I) ⟶ pr d A, Φ.right = chart x := by
  let w : Vec (d + 1) 1 (off A I).toScheme := ⟨((Vec.map (d + 1) 0 (off A I).ι).obj (vec1 x)).1, fun p => by
    have hp : ¬ (Ideal.span (Set.range x) ≤ ((off A I).ι p).asIdeal) := by rw [hI]; exact p.2
    rw [Ideal.span_le] at hp
    obtain ⟨j, hj⟩ : ∃ j, x j ∉ ((off A I).ι p).asIdeal := by
      by_contra hc
      push Not at hc
      exact hp (by rintro _ ⟨j, rfl⟩; exact hc j)
    refine ⟨j.succ, by simp, ?_⟩
    change p ∈ (off A I).toScheme.basicOpen ((off A I).ι.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((Fin.cons 1 x : Fin (d + 1) → A) j.succ)))
    rw [← Scheme.preimage_basicOpen_top]
    change (off A I).ι p ∈ (Spec (CommRingCat.of A)).basicOpen _
    rw [basicOpen_eq_of_affine]
    simp only [Fin.cons_succ]
    exact hj⟩
  refine ⟨Arrow.homMk (prod.lift (Pj.pt w) (sch.map (off A I).ι)) (chart x) ?_, rfl⟩
  apply prod.hom_ext
  · change prod.lift (Pj.pt w) (sch.map (off A I).ι) ≫ prod.map (Pj.incl (d + 1)) (𝟙 _) ≫ prod.fst =
      sch.map (off A I).ι ≫ chart x ≫ prod.fst
    rw [prod.map_fst, prod.lift_fst_assoc, chart, prod.lift_fst, pt_incl, sch_map_pt]
    rfl
  · change prod.lift (Pj.pt w) (sch.map (off A I).ι) ≫ prod.map (Pj.incl (d + 1)) (𝟙 _) ≫ prod.snd =
      sch.map (off A I).ι ≫ chart x ≫ prod.snd
    rw [prod.map_snd, prod.lift_snd_assoc, chart, prod.lift_snd]

end LateralTheory.CohomologicalPurity.Thom.GeoPf

namespace LateralTheory.CohomologicalPurity.Thom

theorem LeafGeo_of : LeafGeo :=
  ⟨GeoPf.part1, GeoPf.part2, GeoPf.part3, GeoPf.part4⟩

end LateralTheory.CohomologicalPurity.Thom

namespace LateralTheory.CohomologicalPurity.Thom.GeoPf

end LateralTheory.CohomologicalPurity.Thom.GeoPf
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafNbhdPf
noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

theorem chart_of_data (hS : LeafSec) {d : ℕ} {A T : Type} [CommRing A] [CommRing T] (I : Ideal A) (x : Fin d → A)
    (ι : A →+* T) (κ : MvPolynomial (Fin d) (A ⧸ I) →+* T) (μ : T →+* A ⧸ I)
    (hι : ι.Etale) (hκ : κ.Etale) (hμι : μ.comp ι = Ideal.Quotient.mk I)
    (hμκ : μ.comp κ = MvPolynomial.constantCoeff) (hx : ∀ j, ι (x j) = κ (MvPolynomial.X j))
    (hI : I = Ideal.span (Set.range x)) : Chart d A I := by
  obtain ⟨t, ht1, ht⟩ := hS A T ι I μ hι hμι
  have hu : IsUnit (algebraMap T (Localization.Away t) t) := IsLocalization.Away.algebraMap_isUnit t
  have hloc : (algebraMap T (Localization.Away t)).Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway t)
  have hμι' : ∀ a, μ (ι a) = Ideal.Quotient.mk I a := fun a => RingHom.congr_fun hμι a
  have hμκ' : ∀ q, μ (κ q) = MvPolynomial.constantCoeff q := fun q => RingHom.congr_fun hμκ q
  have key : ∀ s : T, μ s = 0 →
      algebraMap T (Localization.Away t) s ∈ I.map ((algebraMap T (Localization.Away t)).comp ι) := by
    intro s hs
    have h1 := Ideal.mem_map_of_mem (algebraMap T (Localization.Away t)) (ht s hs)
    rw [Ideal.map_map, map_mul] at h1
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h1
  have hut : IsUnit (μ t) := by rw [ht1]; exact isUnit_one
  let μB : Localization.Away t →+* A ⧸ I := IsLocalization.Away.lift t hut
  have hμB : ∀ a, μB ((algebraMap T (Localization.Away t)).comp ι a) = Ideal.Quotient.mk I a := by
    intro a
    simp only [RingHom.comp_apply, μB, IsLocalization.Away.lift_eq, hμι']
  refine ⟨Localization.Away t, inferInstance, (algebraMap T (Localization.Away t)).comp ι,
    (algebraMap T (Localization.Away t)).comp κ, ⟨RingHom.Etale.stableUnderComposition _ _ hι hloc, ?_, ?_⟩,
    RingHom.Etale.stableUnderComposition _ _ hκ hloc, ?_, ?_⟩
  · apply Ideal.quotientMap_injective'
    intro a ha
    have hker : I.map ((algebraMap T (Localization.Away t)).comp ι) ≤ RingHom.ker μB := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker, hμB, Ideal.Quotient.eq_zero_iff_mem]
      exact hb
    have := hker (Ideal.mem_comap.mp ha)
    rw [RingHom.mem_ker, hμB, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  · intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨s, ⟨_, n, rfl⟩⟩, hbn⟩ := IsLocalization.surj (Submonoid.powers t) b
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (μ s)
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk]
    have e1 : Ideal.Quotient.mk (I.map ((algebraMap T (Localization.Away t)).comp ι))
        (algebraMap T (Localization.Away t) t) = 1 := by
      rw [← map_one (Ideal.Quotient.mk _)]
      refine Ideal.Quotient.eq.mpr ?_
      have := key (t - 1) (by rw [map_sub, map_one, ht1, sub_self])
      simpa [map_sub] using this
    have e2 : Ideal.Quotient.mk (I.map ((algebraMap T (Localization.Away t)).comp ι))
        (algebraMap T (Localization.Away t) s) =
        Ideal.Quotient.mk _ (((algebraMap T (Localization.Away t)).comp ι) a) := by
      refine Ideal.Quotient.eq.mpr ?_
      have := key (s - ι a) (by rw [map_sub, hμι', ha, sub_self])
      simpa [map_sub] using this
    simp only at hbn
    rw [← e2, ← hbn, map_mul, map_pow, map_pow, e1, one_pow, mul_one]
  · rw [show I.map ((algebraMap T (Localization.Away t)).comp ι) =
        (Ideal.span (Set.range x)).map ((algebraMap T (Localization.Away t)).comp ι) by rw [← hI],
      Ideal.map_span, ← Set.range_comp]
    congr 2
    funext j
    simp [hx]
  · intro a
    have := key (ι a - κ (MvPolynomial.C (Ideal.Quotient.mk I a)))
      (by rw [map_sub, hμι', hμκ', MvPolynomial.constantCoeff_C, sub_self])
    simpa [map_sub] using this

theorem chart_of_tensor (hS : LeafSec) {d : ℕ} {P A Q : Type} [CommRing P] [CommRing A] [CommRing Q] [Algebra P A]
    [Algebra P Q] (I : Ideal A) (x : Fin d → A) (c : MvPolynomial (Fin d) (A ⧸ I) ≃+* Q) [Algebra.Etale P A]
    [Algebra.Etale P Q]
    (hcomm : ∀ p, MvPolynomial.constantCoeff (c.symm (algebraMap P Q p)) = Ideal.Quotient.mk I (algebraMap P A p))
    (px : Fin d → P) (hpx1 : ∀ j, algebraMap P A (px j) = x j)
    (hpx2 : ∀ j, algebraMap P Q (px j) = c (MvPolynomial.X j))
    (hI : I = Ideal.span (Set.range x)) : Chart d A I := by
  let f : A →ₐ[P] A ⧸ I := Ideal.Quotient.mkₐ P I
  have hg : ∀ p, (MvPolynomial.constantCoeff.comp c.symm.toRingHom) (algebraMap P Q p) =
      algebraMap P (A ⧸ I) p := fun p => by
    rw [RingHom.comp_apply, ← Ideal.Quotient.mk_algebraMap]; exact hcomm p
  let g : Q →ₐ[P] A ⧸ I := { MvPolynomial.constantCoeff.comp c.symm.toRingHom with commutes' := hg }
  let μ := (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
  let ι := algebraMap A (A ⊗[P] Q)
  let κ := ((Algebra.TensorProduct.comm P Q A).toRingHom.comp (algebraMap Q (Q ⊗[P] A))).comp c.toRingHom
  have hκa : ∀ q, κ q = (1 : A) ⊗ₜ c q := fun q => by
    simp [κ, Algebra.TensorProduct.comm_tmul]
  refine chart_of_data hS I x ι κ μ (RingHom.etale_algebraMap.mpr inferInstance) ?_ ?_ ?_ ?_ hI
  · exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective c.bijective)
      (RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.mpr inferInstance)
        (RingHom.Etale.of_bijective (Algebra.TensorProduct.comm P Q A).bijective))
  · ext a; simp [μ, ι, f, g]
  · apply RingHom.ext; intro q; simp [μ, hκa, f, g]
  · intro j
    rw [hκa]
    show x j ⊗ₜ 1 = _
    rw [← hpx1, ← hpx2, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := Q),
      TensorProduct.smul_tmul]

theorem LeafNbhd_of (hS : LeafSec) (hP : LeafPoly) : LeafNbhd := by
  intro e d R A _ _ φ I x y hc
  have hπ := hP e d R A φ I x y hc
  set α := MvPolynomial.eval₂Hom φ (Sum.elim x y) with hα
  set π := (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp
    ((Ideal.Quotient.mk I).comp φ)) (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i))))
    with hπdef
  have hxI : ∀ j, x j ∈ I := fun j => hc.2 ▸ Ideal.subset_span ⟨j, rfl⟩
  have hcomm : MvPolynomial.constantCoeff.comp π = (Ideal.Quotient.mk I).comp α := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [π, α]
    · intro i
      rcases i with j | i
      · simp [π, α, Ideal.Quotient.eq_zero_iff_mem.mpr (hxI j)]
      · simp [π, α]
  exact @chart_of_tensor hS d _ A _ _ _ _ α.toAlgebra π.toAlgebra I x (RingEquiv.refl _) hc.1.toAlgebra hπ.toAlgebra
    (fun p => RingHom.congr_fun hcomm p) (fun j => MvPolynomial.X (Sum.inl j)) (fun j => by show α _ = x j; rw [hα]; simp)
    (fun j => by show π _ = _; rw [hπdef]; simp) hc.2

end LateralTheory.CohomologicalPurity.ChartCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafPolyPf
noncomputable section
open MvPolynomial TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafPolyPf

theorem one_tmul_algebraMap {P S A : Type} [CommRing P] [CommRing S] [CommRing A] [Algebra P S] [Algebra P A]
    (p : P) : (1 : S) ⊗ₜ[P] algebraMap P A p = algebraMap P S p ⊗ₜ[P] (1 : A) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

def kap (d e : ℕ) (R : Type) [CommRing R] :
    MvPolynomial (Fin d ⊕ Fin e) R →+* MvPolynomial (Fin d) (MvPolynomial (Fin e) R) :=
  eval₂Hom (C.comp C) (Sum.elim 0 fun i => C (X i))

theorem leafPoly : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := by
  intro e d R A _ _ φ I x y h
  obtain ⟨hψ, hI⟩ := h
  set ψ := MvPolynomial.eval₂Hom φ (Sum.elim x y) with hψdef
  let P := MvPolynomial (Fin d ⊕ Fin e) R
  let S := MvPolynomial (Fin d) (MvPolynomial (Fin e) R)
  let Cc := MvPolynomial (Fin d) (A ⧸ I)
  letI : Algebra P A := ψ.toAlgebra
  letI : Algebra P S := (kap d e R).toAlgebra
  letI : Algebra S (S ⊗[P] A) := Algebra.TensorProduct.leftAlgebra (R := P) (A := S) (B := A)
  have hb : (algebraMap S (S ⊗[P] A)).Etale :=
    RingHom.IsStableUnderBaseChange.tensorProduct RingHom.Etale.isStableUnderBaseChange S hψ
  have hx : ∀ j, x j ∈ I := fun j => hI ▸ Ideal.subset_span ⟨j, rfl⟩
  have hψX : ∀ i, ψ (X i) = Sum.elim x y i := fun i => by simp [ψ]
  let gy : MvPolynomial (Fin e) R →+* A ⧸ I := eval₂Hom ((Ideal.Quotient.mk I).comp φ) fun i => Ideal.Quotient.mk I (y i)
  let FS : S →+* Cc := eval₂Hom ((C : A ⧸ I →+* Cc).comp gy) X
  let ρ : P →+* Cc := (C : A ⧸ I →+* Cc).comp ((Ideal.Quotient.mk I).comp ψ)
  letI : Algebra P Cc := ρ.toAlgebra
  have hFSC : ∀ p, FS (C p) = C (gy p) := fun p => MvPolynomial.eval₂Hom_C _ _ _
  have hFSX : ∀ j, FS (X j) = X j := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have hgC : ∀ r, gy (C r) = Ideal.Quotient.mk I (φ r) := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have hgX : ∀ i, gy (X i) = Ideal.Quotient.mk I (y i) := fun i => MvPolynomial.eval₂Hom_X' _ _ _
  have kC : ∀ r, kap d e R (C r) = C (C r) := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have kl : ∀ j, kap d e R (X (Sum.inl j)) = 0 := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have kr : ∀ i, kap d e R (X (Sum.inr i)) = C (X i) := fun i => MvPolynomial.eval₂Hom_X' _ _ _
  have ψC : ∀ r, ψ (C r) = φ r := fun r => MvPolynomial.eval₂Hom_C _ _ _
  have hFS : FS.comp (kap d e R) = ρ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show FS (kap d e R (C r)) = C (Ideal.Quotient.mk I (ψ (C r)))
      rw [kC, hFSC, hgC, ψC]
    · rintro (j | i)
      · show FS (kap d e R (X (Sum.inl j))) = C (Ideal.Quotient.mk I (ψ (X (Sum.inl j))))
        rw [kl, hψX, map_zero]; simp [Ideal.Quotient.eq_zero_iff_mem.mpr (hx j)]
      · show FS (kap d e R (X (Sum.inr i))) = C (Ideal.Quotient.mk I (ψ (X (Sum.inr i))))
        rw [kr, hFSC, hgX, hψX]; rfl
  let fS : S →ₐ[P] Cc := { FS with commutes' := fun p => RingHom.congr_fun hFS p }
  let fA : A →ₐ[P] Cc := { (C : A ⧸ I →+* Cc).comp (Ideal.Quotient.mk I) with commutes' := fun _ => rfl }
  let F : S ⊗[P] A →+* Cc := (Algebra.TensorProduct.productMap fS fA).toRingHom
  have hk : I ≤ RingHom.ker (Algebra.TensorProduct.includeRight (R := P) (A := S) (B := A)).toRingHom := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : x j = algebraMap P A (X (Sum.inl j)) := by
      rw [RingHom.algebraMap_toAlgebra, hψX]; rfl
    have h2 : algebraMap P S (X (Sum.inl j)) = 0 := by
      rw [RingHom.algebraMap_toAlgebra]; exact kl j
    simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply]
    rw [h1, one_tmul_algebraMap, h2, TensorProduct.zero_tmul]
  let G : Cc →+* S ⊗[P] A :=
    eval₂Hom (Ideal.Quotient.lift I (Algebra.TensorProduct.includeRight (R := P) (A := S) (B := A)).toRingHom
      fun a ha => hk ha) fun j => X j ⊗ₜ[P] (1 : A)
  have hF1 : ∀ s : S, F (s ⊗ₜ[P] (1 : A)) = FS s := fun s => by simp [F, fS, fA]
  have hGC : ∀ a, G (C (Ideal.Quotient.mk I a)) = (1 : S) ⊗ₜ[P] a := fun a => by
    erw [MvPolynomial.eval₂Hom_C]; rfl
  have hGX : ∀ j, G (X j) = X j ⊗ₜ[P] (1 : A) := fun j => MvPolynomial.eval₂Hom_X' _ _ _
  have hFG : F.comp G = RingHom.id Cc := by
    apply MvPolynomial.ringHom_ext
    · intro r
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      simp [F, G, fS, fA]
    · intro j
      show F (G (X j)) = X j
      rw [hGX, hF1, hFSX]
  have hS : (G.comp F).comp (Algebra.TensorProduct.includeLeftRingHom (R := P) (A := S) (B := A)) =
      Algebra.TensorProduct.includeLeftRingHom := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r
        show G (F (C (C r) ⊗ₜ[P] (1 : A))) = C (C r) ⊗ₜ[P] (1 : A)
        have e1 : φ r = algebraMap P A (C r) := by
          rw [RingHom.algebraMap_toAlgebra]; exact (MvPolynomial.eval₂Hom_C _ _ _).symm
        have e2 : algebraMap P S (C r) = C (C r) := by
          rw [RingHom.algebraMap_toAlgebra]; exact MvPolynomial.eval₂Hom_C _ _ _
        rw [hF1, hFSC, hgC, hGC, e1, one_tmul_algebraMap, e2]
      · intro i
        show G (F (C (X i) ⊗ₜ[P] (1 : A))) = C (X i) ⊗ₜ[P] (1 : A)
        have e1 : y i = algebraMap P A (X (Sum.inr i)) := by rw [RingHom.algebraMap_toAlgebra, hψX]; rfl
        have e2 : algebraMap P S (X (Sum.inr i)) = C (X i) := by
          rw [RingHom.algebraMap_toAlgebra]; exact MvPolynomial.eval₂Hom_X' _ _ _
        rw [hF1, hFSC, hgX, hGC, e1, one_tmul_algebraMap, e2]
    · intro j
      show G (F (X j ⊗ₜ[P] (1 : A))) = X j ⊗ₜ[P] (1 : A)
      rw [hF1, hFSX, hGX]
  have hGF : G.comp F = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      have hs := RingHom.congr_fun hS s
      simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply] at hs
      have ha : G (F ((1 : S) ⊗ₜ[P] a)) = (1 : S) ⊗ₜ[P] a := by
        simp [F, G, fS, fA]; erw [MvPolynomial.eval₂Hom_C]; rfl
      have hm : s ⊗ₜ[P] a = (s ⊗ₜ[P] (1 : A)) * ((1 : S) ⊗ₜ[P] a) := by simp
      rw [RingHom.id_apply, RingHom.comp_apply, hm, map_mul, map_mul, hs, ha]
    | add u v hu hv => simp only [RingHom.comp_apply, RingHom.id_apply, map_add (f := _)] at hu hv ⊢; rw [hu, hv]
  let E : S ⊗[P] A ≃+* Cc := RingEquiv.ofRingHom F G hFG hGF
  let σ : P ≃+* S := (MvPolynomial.sumAlgEquiv R (Fin d) (Fin e)).toRingEquiv
  have s1 : ∀ r, σ (C r) = C (C r) := fun r => MvPolynomial.sumAlgEquiv_C_inl (R := R) (S₁ := Fin d) (S₂ := Fin e) r
  have s2 : ∀ j, σ (X (Sum.inl j)) = X j := fun j => MvPolynomial.sumAlgEquiv_X_inl (R := R) (S₁ := Fin d) (S₂ := Fin e) j
  have s3 : ∀ i, σ (X (Sum.inr i)) = C (X i) := fun i => MvPolynomial.sumAlgEquiv_X_inr (R := R) (S₁ := Fin d) (S₂ := Fin e) i
  have key : (MvPolynomial.eval₂Hom ((MvPolynomial.C : A ⧸ I →+* MvPolynomial (Fin d) (A ⧸ I)).comp
      ((Ideal.Quotient.mk I).comp φ)) (Sum.elim MvPolynomial.X fun i => MvPolynomial.C (Ideal.Quotient.mk I (y i)))) =
      (E.toRingHom.comp (algebraMap S (S ⊗[P] A))).comp σ.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (C r)); rw [s1]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_C]; simp [gy]
    · rintro (j | i)
      · change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (X (Sum.inl j))); rw [s2]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_X']
      · change _ = (E.toRingHom.comp (algebraMap S (S ⊗[P] A))) (σ (X (Sum.inr i))); rw [s3]; simp [E, F, fS]; erw [MvPolynomial.eval₂Hom_C]; simp [gy]
  rw [key]
  exact RingHom.Etale.respectsIso.2 _ σ (RingHom.Etale.respectsIso.1 _ E hb)

theorem LeafPoly_of : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := leafPoly

end LateralTheory.CohomologicalPurity.LeafPolyPf
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafSpanPf
noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.LeafSpanPf

theorem span_of_subsingleton {R P B ι : Type} [CommRing R] [CommRing P] [CommRing B] [Algebra R P]
    [Algebra R B] [Algebra P B] [IsScalarTower R P B] [Subsingleton Ω[B⁄P]] (z : ι → P)
    (hz : Submodule.span P (Set.range fun i => KaehlerDifferential.D R P (z i)) = ⊤) :
    Submodule.span B (Set.range fun i => KaehlerDifferential.D R B (algebraMap P B (z i))) = ⊤ := by
  set T := Submodule.span B (Set.range fun i => KaehlerDifferential.D R B (algebraMap P B (z i)))
  have hmap : ∀ m : Ω[P⁄R], KaehlerDifferential.map R R P B m ∈ T := by
    intro m
    have hm : m ∈ Submodule.span P (Set.range fun i => KaehlerDifferential.D R P (z i)) := by
      rw [hz]; trivial
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨i, rfl⟩ := hm
      rw [KaehlerDifferential.map_D]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact T.add_mem ha hb
    | smul c m _ hm =>
      rw [LinearMap.map_smul, ← algebraMap_smul B c]
      exact T.smul_mem _ hm
  rw [eq_top_iff]
  intro ω _
  have hk : ω ∈ LinearMap.ker (KaehlerDifferential.map R P B B) := by
    rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
  have hbc : ∀ t, KaehlerDifferential.mapBaseChange R P B t ∈ T := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      rw [KaehlerDifferential.mapBaseChange_tmul]
      exact T.smul_mem _ (hmap m)
    | add a b ha hb => rw [map_add (f := _)]; exact T.add_mem ha hb
  obtain ⟨t, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R P B (ω)).mp hk
  exact hbc t

theorem annih {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (S : Submodule A M) (p : Ideal A) (hp : p.IsPrime) (f : A) (hf : f ∉ p)
    (h : ∀ ω : M, f • ω ∈ S ⊔ p • ⊤) : ∃ g : A, g ∉ p ∧ ∀ ω : M, g • ω ∈ S := by
  let φ : Module.End A (M ⧸ S) := algebraMap A (Module.End A (M ⧸ S)) f
  have hφ : LinearMap.range φ ≤ p • ⊤ := by
    rintro _ ⟨n, rfl⟩
    obtain ⟨ω, rfl⟩ := S.mkQ_surjective n
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (h ω)
    have e1 : φ (S.mkQ ω) = S.mkQ t := by
      simp only [φ, Module.algebraMap_end_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, ← hst,
        Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero S).mpr hs, zero_add]
    rw [e1]
    exact (Submodule.smul_mono (le_refl p) (le_top : Submodule.map S.mkQ ⊤ ≤ ⊤)) (by rw [← Submodule.map_smul'']; exact Submodule.mem_map_of_mem ht)
  obtain ⟨q, hmon, -, hcoef, hq⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero _ φ p hφ
  refine ⟨Polynomial.aeval f q, ?_, ?_⟩
  · intro hmem
    apply hf
    apply hp.mem_of_pow_mem q.natDegree
    have hsum : Polynomial.aeval f q = f ^ q.natDegree + ∑ k ∈ Finset.range q.natDegree, q.coeff k * f ^ k := by
      rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree]
      simp [add_comm, smul_eq_mul]
    have hlow : ∑ k ∈ Finset.range q.natDegree, q.coeff k * f ^ k ∈ p :=
      Ideal.sum_mem _ fun k hk => Ideal.mul_mem_right _ _
        (Ideal.pow_le_self (by have := Finset.mem_range.mp hk; omega) (hcoef k))
    have := p.sub_mem hmem hlow
    rwa [hsum, add_sub_cancel_right] at this
  · intro ω
    have e2 : Polynomial.aeval φ q = algebraMap A (Module.End A (M ⧸ S)) (Polynomial.aeval f q) :=
      Polynomial.aeval_algebraMap_apply _ _ _
    have := LinearMap.congr_fun hq (S.mkQ ω)
    rw [e2, Module.algebraMap_end_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    exact this


open KaehlerDifferential in
theorem key {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) {e d : ℕ}
    (x : Fin d → A) (y : Fin e → A) (f : A) (hx : ∀ j, x j ∈ I)
    (hfI : ∀ a ∈ I, f * a ∈ Ideal.span (Set.range x))
    (hspan : Submodule.span (A ⧸ I) (Set.range fun k => D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) = ⊤)
    (ω : Ω[A⁄R]) :
    f • ω ∈ Submodule.span A (Set.range fun k => D R A (Sum.elim x y k)) ⊔ I • ⊤ := by
  set S := Submodule.span A (Set.range fun k => D R A (Sum.elim x y k))
  have hSx : ∀ j, D R A (x j) ∈ S := fun j => Submodule.subset_span ⟨Sum.inl j, rfl⟩
  have hSy : ∀ k, D R A (y k) ∈ S := fun k => Submodule.subset_span ⟨Sum.inr k, rfl⟩
  have hI : ∀ a ∈ I, ∀ m : Ω[A⁄R], a • m ∈ S ⊔ I • ⊤ := fun a ha m =>
    Submodule.mem_sup_right (Submodule.smul_mem_smul ha trivial)
  have hDa : ∀ a ∈ I, f • D R A a ∈ S ⊔ I • ⊤ := by
    intro a ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hfI a ha)
    have e1 : D R A (f * a) = f • D R A a + a • D R A f := Derivation.leibniz _ _ _
    have e2 : D R A (f * a) = ∑ j, (b j • D R A (x j) + x j • D R A (b j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hb, map_sum]; simp only [Derivation.leibniz]
    have e3 : f • D R A a = ∑ j, (b j • D R A (x j) + x j • D R A (b j)) - a • D R A f := by
      rw [← e2, e1]; abel
    rw [e3]
    refine Submodule.sub_mem _ (Submodule.sum_mem _ fun j _ => Submodule.add_mem _ ?_ ?_) (hI a ha _)
    · exact Submodule.mem_sup_left (S.smul_mem _ (hSx j))
    · exact hI _ (hx j) _
  have hω : map R R A (A ⧸ I) ω ∈
      Submodule.span (A ⧸ I) (Set.range fun k => D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) := by
    rw [hspan]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun _ |>.mp hω
  choose c' hc' using fun k => Ideal.Quotient.mk_surjective (c k)
  set ω' := ω - ∑ k, c' k • D R A (y k) with hω'
  have hck : ∀ k, c' k • D R (A ⧸ I) (algebraMap A (A ⧸ I) (y k)) =
      c k • D R (A ⧸ I) (Ideal.Quotient.mk I (y k)) := by
    intro k
    rw [← algebraMap_smul (A ⧸ I) (c' k), Ideal.Quotient.algebraMap_eq, hc']
  have h0 : mapBaseChange R A (A ⧸ I) (1 ⊗ₜ ω') = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [mapBaseChange_tmul, one_smul, hω', map_sub, map_sum]
    simp only [LinearMap.map_smul_of_tower, map_D, hck, hc, sub_self]
  obtain ⟨t, ht⟩ := (exact_kerCotangentToTensor_mapBaseChange R A (A ⧸ I)
    Ideal.Quotient.mk_surjective (1 ⊗ₜ ω')).mp h0
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective _ t
  rw [kerCotangentToTensor_toCotangent] at ht
  have haI : (a : A) ∈ I := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp a.2
  have hdiff : ω' - D R A a ∈ I • (⊤ : Submodule A Ω[A⁄R]) := by
    have h1 : (1 : A ⧸ I) ⊗ₜ[A] (ω' - D R A a) = 0 := by rw [tmul_sub, ← ht, sub_self]
    have := congrArg (TensorProduct.quotTensorEquivQuotSMul Ω[A⁄R] I) h1
    rwa [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at this
  have e4 : f • ω = f • (ω' - D R A a) + f • ∑ k, c' k • D R A (y k) + f • D R A a := by
    rw [← smul_add, ← smul_add, hω']; congr 1; abel
  rw [e4]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) (hDa a haI)
  · exact Submodule.mem_sup_right (Submodule.smul_mem _ f hdiff)
  · exact Submodule.mem_sup_left (S.smul_mem _ (Submodule.sum_mem _ fun k _ => S.smul_mem _ (hSy k)))

theorem LeafSpan_of : LateralTheory.CohomologicalPurity.ChartCut.LeafSpan := by
  intro e d R A _ _ _ _ I p hp hIp hB x f hx hf hfI
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial (n := e) R (A ⧸ I)
  choose y hy using fun k : Fin e => Ideal.Quotient.mk_surjective (g (MvPolynomial.X k))
  have hspan : Submodule.span (A ⧸ I)
      (Set.range fun k => KaehlerDifferential.D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) = ⊤ := by
    let _ : Algebra (MvPolynomial (Fin e) R) (A ⧸ I) := g.toRingHom.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin e) R) (A ⧸ I) := hg
    have : IsScalarTower R (MvPolynomial (Fin e) R) (A ⧸ I) :=
      IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
    have h := span_of_subsingleton (R := R) (P := MvPolynomial (Fin e) R) (B := A ⧸ I)
      MvPolynomial.X (by
        rw [← (KaehlerDifferential.mvPolynomialBasis R (Fin e)).span_eq]
        congr 2; funext i; simp [KaehlerDifferential.mvPolynomialBasis_apply])
    have e5 : (fun k => KaehlerDifferential.D R (A ⧸ I) (Ideal.Quotient.mk I (y k))) =
        fun k => KaehlerDifferential.D R (A ⧸ I)
          (algebraMap (MvPolynomial (Fin e) R) (A ⧸ I) (MvPolynomial.X k)) := by
      funext k; rw [hy]; rfl
    rw [e5]; exact h
  obtain ⟨g', hg'p, hg'⟩ := annih
    (Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (Sum.elim x y k))) p hp f hf
    (fun ω => (show _ ⊔ I • (⊤ : Submodule A Ω[A⁄R]) ≤ _ ⊔ p • ⊤ from
      sup_le_sup_left (Submodule.smul_mono_left hIp) _) (key I x y f hx hfI hspan ω))
  exact ⟨y, g', hg'p, hg'⟩

end LateralTheory.CohomologicalPurity.LeafSpanPf
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafActPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom
namespace ActPf

variable {d : ℕ} {A : Type} [CommRing A]

def φ {U : Scheme.{0}} (s : U ⟶ Spec (CommRingCat.of A)) : A →+* Γ(U, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ s.appTop).hom

theorem φ_comp {V U : Scheme.{0}} (f : V ⟶ U) (s : U ⟶ Spec (CommRingCat.of A)) :
    φ (f ≫ s) = f.appTop.hom.comp (φ s) := rfl

def actV (M : Matrix (Fin d) (Fin d) A) {U : Scheme.{0}} (s : U ⟶ Spec (CommRingCat.of A))
    (v : Fin (d + 1) → Γ(U, ⊤)) : Fin (d + 1) → Γ(U, ⊤) :=
  Fin.cons (v 0) ((M.map (φ s)).mulVec (Fin.tail v))

theorem actV_mem (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {U : Scheme.{0}}
    (s : U ⟶ Spec (CommRingCat.of A)) (v : Fin (d + 1) → Γ(U, ⊤)) (p : U)
    (h : ∃ i : Fin (d + 1), k ≤ i.val ∧ p ∈ U.basicOpen (v i)) :
    ∃ i : Fin (d + 1), k ≤ i.val ∧ p ∈ U.basicOpen (actV M s v i) := by
  obtain ⟨i, hi, hp⟩ := h
  by_contra hc
  push Not at hc
  have hM' : IsUnit (M.map (φ s)).det := by
    have h := hM.map (φ s); rw [RingHom.map_det] at h; exact h
  have hz : ∀ j : Fin d, (U.Γevaluation p).hom ((M.map (φ s)).mulVec (Fin.tail v) j) = 0 := by
    intro j
    have := hc j.succ (by simp; omega)
    simp only [actV, Fin.cons_succ] at this
    exact (Scheme.evaluation_eq_zero_iff_notMem_basicOpen _ _ _ _).2 this
  have ht : ∀ j : Fin d, (U.Γevaluation p).hom (Fin.tail v j) = 0 := by
    intro j
    have hinv : (M.map (φ s))⁻¹.mulVec ((M.map (φ s)).mulVec (Fin.tail v)) = Fin.tail v := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM', Matrix.one_mulVec]
    rw [← hinv, RingHom.map_mulVec]
    have : ((U.Γevaluation p).hom ∘ (M.map (φ s)).mulVec (Fin.tail v)) = 0 := funext hz
    rw [this, Matrix.mulVec_zero]; rfl
  cases i using Fin.cases with
  | zero =>
    have := hc 0 (by simp at hi; omega)
    simp only [actV, Fin.cons_zero] at this
    exact this hp
  | succ j =>
    exact ((Scheme.evaluation_eq_zero_iff_notMem_basicOpen _ _ _ _).1 (ht j)) hp

def actF (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {U : Scheme.{0}}
    (s : U ⟶ Spec (CommRingCat.of A)) : Vec (d + 1) k U ⥤ Vec (d + 1) k U where
  obj v := ⟨actV M s v.1, fun p => actV_mem M hM hk s v.1 p (v.2 p)⟩
  map {v w} u := ⟨u.1, fun i => by
    cases i using Fin.cases with
    | zero => simp only [actV, Fin.cons_zero]; exact u.2 0
    | succ j =>
      simp only [actV, Fin.cons_succ]
      have : Fin.tail v.1 = (u.1 : Γ(U, ⊤)) • Fin.tail w.1 := funext fun l => by
        simp only [Fin.tail, Pi.smul_apply, smul_eq_mul]; exact u.2 l.succ
      rw [this, Matrix.mulVec_smul]; rfl⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem comp_val {N k : ℕ} {U : Scheme.{0}} {X Y Z : Vec N k U} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (a ≫ b).1 = b.1 * a.1 := rfl

theorem eqToHom_val {N k : ℕ} {U : Scheme.{0}} {X Y : Vec N k U} (h : X = Y) : (eqToHom h).1 = 1 := by
  subst h; rfl

theorem actV_map (M : Matrix (Fin d) (Fin d) A) {V U : Scheme.{0}} (f : V ⟶ U) (s : U ⟶ Spec (CommRingCat.of A))
    (v : Fin (d + 1) → Γ(U, ⊤)) :
    (fun i => f.appTop.hom (actV M s v i)) = actV M (f ≫ s) (fun i => f.appTop.hom (v i)) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [actV]
  | succ j =>
    simp only [actV, Fin.cons_succ]
    rw [RingHom.map_mulVec, φ_comp, Matrix.map_map]
    rfl

theorem actF_map (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {V U : Scheme.{0}}
    (f : V ⟶ U) (s : U ⟶ Spec (CommRingCat.of A)) :
    actF M hM hk s ⋙ Vec.map (d + 1) k f = Vec.map (d + 1) k f ⋙ actF M hM hk (f ≫ s) := by
  refine CategoryTheory.Functor.ext (fun v => Subtype.ext (actV_map M f s v.1)) (fun v w u => ?_)
  apply Subtype.ext
  simp only [comp_val, eqToHom_val, one_mul]
  erw [eqToHom_val, mul_one]
  rfl

def actSp (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {E : Spc}
    (a : E ⟶ Pj (d + 1) k) (b : E ⟶ sp A) : E ⟶ Pj (d + 1) k where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        ((show Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U.unop from (a.app n).app U x) ⋙
          actF M hM hk (show U.unop ⟶ Spec (CommRingCat.of A) from (b.app n).app U x) :
          Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U.unop)
      naturality := fun U U' f => by
        ext x
        have h1 := ConcreteCategory.congr_hom ((a.app n).naturality f) x
        have h2 := ConcreteCategory.congr_hom ((b.app n).naturality f) x
        refine (congrArg₂ (fun (F : Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U'.unop)
          (s : U'.unop ⟶ Spec (CommRingCat.of A)) => (F ⋙ actF M hM hk s : Fin (n.unop.len + 1) ⥤ _)) h1 h2).trans ?_
        exact congrArg (fun G => (show Fin (n.unop.len + 1) ⥤ Vec (d + 1) k U.unop from (a.app n).app U x) ⋙ G)
          (actF_map M hM hk f.unop (show U.unop ⟶ Spec (CommRingCat.of A) from (b.app n).app U x)).symm }
  naturality n m f := by
    ext U x
    have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (a.naturality f) U) x
    have h2 := ConcreteCategory.congr_hom (NatTrans.congr_app (b.naturality f) U) x
    exact (congrArg₂ (fun (F : Fin (m.unop.len + 1) ⥤ Vec (d + 1) k U.unop)
          (s : U.unop ⟶ Spec (CommRingCat.of A)) => (F ⋙ actF M hM hk s : Fin (m.unop.len + 1) ⥤ _)) h1 h2).trans rfl

theorem actSp_comp (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {E' E : Spc}
    (g : E' ⟶ E) (a : E ⟶ Pj (d + 1) k) (b : E ⟶ sp A) :
    g ≫ actSp M hM hk a b = actSp M hM hk (g ≫ a) (g ≫ b) := by
  ext n U x; rfl

theorem actSp_incl (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {E : Spc}
    (a : E ⟶ Pj (d + 1) 1) (b : E ⟶ sp A) :
    actSp M hM le_rfl a b ≫ Pj.incl (d + 1) = actSp M hM (Nat.zero_le 1) (a ≫ Pj.incl (d + 1)) b := by
  ext n U x; rfl

theorem actSp_line (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) {k : ℕ} (hk : k ≤ 1) {E : Spc}
    (a : E ⟶ Pj (d + 1) k) (b : E ⟶ sp A) :
    actSp M hM hk a b ≫ Pj.line (d + 1) k = a ≫ Pj.line (d + 1) k := by
  ext n U x; rfl

theorem actSp_pt (M : Matrix (Fin d) (Fin d) A) (hM : IsUnit M.det) (x : Fin d → A) :
    actSp M hM (Nat.zero_le 1) (Pj.pt (vec1 x)) (𝟙 (sp A)) = Pj.pt (vec1 (M.mulVec x)) := by
  ext n U f
  refine CategoryTheory.Functor.ext (fun _ => Subtype.ext ?_) (fun _ _ _ => ?_)
  · funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j =>
      show ((M.map (φ _)).mulVec _) j = φ _ ((M.mulVec x) j)
      rw [RingHom.map_mulVec]
      rfl
  · apply Subtype.ext
    erw [comp_val, comp_val, eqToHom_val, eqToHom_val]
    simp only [one_mul, mul_one]
    erw [eqToHom_val]
    rfl

end ActPf

open ActPf in
theorem LeafAct_of : LeafAct := by
  intro d A _ M hM
  let gR : PR (d + 1) 0 A ⟶ PR (d + 1) 0 A :=
    prod.lift (actSp M hM (Nat.zero_le 1) prod.fst prod.snd) prod.snd
  let gL : PR (d + 1) 1 A ⟶ PR (d + 1) 1 A := prod.lift (actSp M hM le_rfl prod.fst prod.snd) prod.snd
  have hw : gL ≫ (pr d A).hom = (pr d A).hom ≫ gR := by
    apply prod.hom_ext
    · simp only [pr, Arrow.mk_hom, Category.assoc, prod.map_fst, prod.lift_fst, gL, gR]
      rw [prod.lift_fst_assoc, actSp_incl, actSp_comp, prod.map_fst, prod.map_snd, Category.comp_id]
    · simp only [pr, Arrow.mk_hom, Category.assoc, prod.map_snd, Category.comp_id, prod.lift_snd, gL, gR]
  refine ⟨Arrow.homMk gL gR hw, ?_, ?_, ?_⟩
  · change gR ≫ prod.fst ≫ Pj.line (d + 1) 0 = _
    rw [prod.lift_fst_assoc, actSp_line]
  · change gR ≫ prod.snd = _
    exact prod.lift_snd _ _
  · intro x
    change chart x ≫ gR = _
    apply prod.hom_ext
    · rw [Category.assoc, prod.lift_fst, actSp_comp, chart, prod.lift_fst, prod.lift_snd, actSp_pt, chart, prod.lift_fst]
    · rw [Category.assoc, prod.lift_snd, chart, chart, prod.lift_snd, prod.lift_snd]

end LateralTheory.CohomologicalPurity.Thom
end
end
