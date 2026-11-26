module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.G3

private noncomputable def geomPt (X : Scheme.{0}) (x : X) : sp (AlgebraicClosure (X.residueField x)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
    X.fromSpecResidueField x

private theorem geomPt_apply (X : Scheme.{0}) (x : X)
    (s : sp (AlgebraicClosure (X.residueField x))) : geomPt X x s = x := by
  exact Scheme.fromSpecResidueField_apply x _

private theorem surj_of_pts {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ Z), ∃! y : sp Ω ⟶ Y, y ≫ f = z) : Surjective f := by
  constructor
  intro z
  obtain ⟨y, hy, -⟩ := h (AlgebraicClosure (Z.residueField z)) (geomPt Z z)
  obtain ⟨s⟩ : Nonempty (sp (AlgebraicClosure (Z.residueField z))) := ⟨IsLocalRing.closedPoint _⟩
  have key : (y ≫ f) s = geomPt Z z s := by rw [hy]
  rw [Scheme.Hom.comp_apply, geomPt_apply] at key
  exact ⟨y s, key⟩

private theorem diag_surj {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ Z), ∃! y : sp Ω ⟶ Y, y ≫ f = z) :
    Surjective (pullback.diagonal f) := by
  constructor
  intro p
  obtain ⟨y, hy, huniq⟩ := h _ (geomPt (pullback f f) p ≫ pullback.fst f f ≫ f)
  have e1 : geomPt (pullback f f) p ≫ pullback.fst f f = geomPt (pullback f f) p ≫ pullback.snd f f := by
    rw [huniq (geomPt (pullback f f) p ≫ pullback.fst f f) (by dsimp only; rw [Category.assoc]),
      huniq (geomPt (pullback f f) p ≫ pullback.snd f f)
        (by dsimp only; rw [Category.assoc, pullback.condition])]
  have e2 : (geomPt (pullback f f) p ≫ pullback.fst f f) ≫ pullback.diagonal f = geomPt (pullback f f) p := by
    apply pullback.hom_ext
    · simp
    · simp [e1]
  obtain ⟨s⟩ : Nonempty (sp (AlgebraicClosure ((pullback f f).residueField p))) :=
    ⟨IsLocalRing.closedPoint _⟩
  have key : ((geomPt (pullback f f) p ≫ pullback.fst f f) ≫ pullback.diagonal f) s =
      geomPt (pullback f f) p s := by rw [e2]
  rw [Scheme.Hom.comp_apply, geomPt_apply] at key
  exact ⟨_, key⟩

theorem UpperTheory.Gal.G3.pIsoPts :
    IsoPts := by
  intro Y Z f _ h
  have hd : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, diag_surj f h⟩
  have : Mono f := (pullback.isIso_diagonal_iff f).1 hd
  have : IsOpenImmersion f := IsOpenImmersion.of_flat_of_mono f
  exact (isIso_iff_isOpenImmersion_and_surjective f).2 ⟨this, surj_of_pts f h⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem exists_factor {W : Scheme.{0}} {J : Type} (Ω : Type) [Field Ω]
    (p : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : J => W)) :
    ∃ (j : J) (x : UpperTheory.Gal.G3.sp Ω ⟶ W), p = x ≫ Sigma.ι (fun _ : J => W) j := by
  haveI : Subsingleton ↑(UpperTheory.Gal.G3.sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have pt : ↑(UpperTheory.Gal.G3.sp Ω) := show PrimeSpectrum Ω from ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨⟨j, y⟩, hq⟩ : ∃ q, (sigmaMk (fun _ : J => W)).symm (p pt) = q := ⟨_, rfl⟩
  have hy : Sigma.ι (fun _ : J => W) j y = p pt := by
    rw [← sigmaMk_mk, ← hq, Homeomorph.apply_symm_apply]
  refine ⟨j, IsOpenImmersion.lift (Sigma.ι (fun _ : J => W) j) p ?_,
    (IsOpenImmersion.lift_fac _ _ _).symm⟩
  rintro _ ⟨z, rfl⟩
  obtain rfl : z = pt := Subsingleton.elim _ _
  exact ⟨y, hy⟩

theorem UpperTheory.Gal.G3.pSplitsPts :
    IsoPts → SplitsPts := by
  intro hIso Z Y W s _ _ c J _ σ hσ hpts
  refine ⟨hσ, ?_⟩
  let e := Limits.Sigma.desc (fun j : J =>
    pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j))
  have hι : ∀ j, Sigma.ι (fun _ : J => W) j ≫ e =
      pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) :=
    fun j => Sigma.ι_desc _ _
  have hlift : ∀ j, Etale (pullback.lift (σ j) (𝟙 W)
      (by rw [Category.id_comp]; exact hσ j) : W ⟶ pullback s c) := by
    intro j
    haveI : Etale (pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) ≫
        pullback.snd s c) := by
      rw [pullback.lift_snd]; infer_instance
    exact Etale.of_comp _ (pullback.snd s c)
  haveI : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  haveI : Etale e := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hlift
  show IsIso e
  apply hIso e
  intro Ω _ _ z
  obtain ⟨j, hj, huniq⟩ := hpts Ω (z ≫ pullback.snd s c) (z ≫ pullback.fst s c)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  have hz : (z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j ≫ e = z := by
    rw [hι]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [← Category.assoc]
      exact hj
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  refine ⟨(z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j,
    by rw [Category.assoc]; exact hz, fun q hq => ?_⟩
  obtain ⟨j', x', rfl⟩ := exists_factor Ω q
  rw [Category.assoc, hι] at hq
  have hs := congrArg (· ≫ pullback.snd s c) hq
  have hf := congrArg (· ≫ pullback.fst s c) hq
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hs hf
  have hjj : j' = j := huniq j' (by rw [← hs]; exact hf)
  rw [hjj, hs]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem sp_subsingleton (Ω : Type) [Field Ω] : Subsingleton ↑(UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

private theorem exists_factor_ι {J : Type} {W : Scheme.{0}} (Ω : Type) [Field Ω]
    (u : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : J => W)) :
    ∃ (j : J) (x : UpperTheory.Gal.G3.sp Ω ⟶ W), x ≫ Sigma.ι (fun _ : J => W) j = u := by
  haveI := sp_subsingleton Ω
  have p : ↑(UpperTheory.Gal.G3.sp Ω) := show PrimeSpectrum Ω from ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨⟨j, y⟩, hq⟩ : ∃ q, (sigmaMk (fun _ : J => W)).symm (u p) = q := ⟨_, rfl⟩
  have hy : Sigma.ι (fun _ : J => W) j y = u p := by
    rw [← sigmaMk_mk, ← hq, Homeomorph.apply_symm_apply]
  refine ⟨j, IsOpenImmersion.lift (Sigma.ι (fun _ : J => W) j) u ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨z, rfl⟩
  obtain rfl : z = p := Subsingleton.elim _ _
  exact ⟨y, hy⟩

private theorem index_eq_of_ι {J : Type} {W : Scheme.{0}} (Ω : Type) [Field Ω] {j j' : J}
    {x x' : UpperTheory.Gal.G3.sp Ω ⟶ W}
    (h : x ≫ Sigma.ι (fun _ : J => W) j = x' ≫ Sigma.ι (fun _ : J => W) j') : j = j' := by
  by_contra hne
  have he := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : J => W) ⟨h⟩ hne
  exact he.false (show PrimeSpectrum Ω from ⟨⊥, Ideal.isPrime_bot⟩)

theorem UpperTheory.Gal.G3.pPtsOfSplits :
    PtsOfSplits := by
  intro Z Y W s c J σ hs Ω _ x y hxy
  obtain ⟨hσ, hiso⟩ := hs
  haveI := hiso
  let e := Limits.Sigma.desc (fun j : J =>
    pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j))
  have hι : ∀ j, Sigma.ι (fun _ : J => W) j ≫ e =
      pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) :=
    fun j => Sigma.ι_desc _ _
  obtain ⟨j, x', hx'⟩ := exists_factor_ι Ω (pullback.lift y x hxy ≫ inv e)
  have h1 : x' ≫ Sigma.ι (fun _ : J => W) j ≫ e = pullback.lift y x hxy := by
    rw [← Category.assoc, hx', Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hι] at h1
  have hsnd := congrArg (· ≫ pullback.snd s c) h1
  have hfst := congrArg (· ≫ pullback.fst s c) h1
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hsnd hfst
  rw [hsnd] at hfst
  refine ⟨j, hfst, fun j' hj' => ?_⟩
  have hj'' : x ≫ σ j' = y := hj'
  apply index_eq_of_ι Ω (x := x) (x' := x')
  rw [hx']
  apply (cancel_mono e).mp
  rw [Category.assoc, hι, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hj'']
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.GalV

namespace UpperTheory.Gal.G3

private theorem splits_restrict (hS : SplitsPts) (hP : PtsOfSplits) {Z Y W W' : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s]
    (c : W ⟶ Z) (J : Type) [Finite J] (σ : J → (W ⟶ Y)) (g : W' ⟶ W) (h : Splits s c σ) :
    Splits s (g ≫ c) fun j => g ≫ σ j := by
  have h0 := h
  obtain ⟨hc, -⟩ := h
  refine hS s (g ≫ c) J (fun j => g ≫ σ j) (fun j => by simp [hc j]) ?_
  intro Ω _ _ x y hy
  have hy' : y ≫ s = (x ≫ g) ≫ c := by simpa using hy
  obtain ⟨j, hj, huniq⟩ := hP s c J σ h0 Ω (x ≫ g) y hy'
  exact ⟨j, by simpa using hj, fun i hi => huniq i (by simpa using hi)⟩

private theorem splits_down (hS : SplitsPts) (hP : PtsOfSplits) {P Y Z' Z W : Scheme.{0}} {v : P ⟶ Y} {s' : P ⟶ Z'} {s : Y ⟶ Z}
    {g : Z' ⟶ Z} [IsFinite s] [Etale s] (sq : IsPullback v s' s g) (c : W ⟶ Z') (J : Type) [Finite J] (σ : J → (W ⟶ P))
    (hσ : ∀ j, σ j ≫ s' = c) (h : Splits s' c σ) : Splits s (c ≫ g) fun j => σ j ≫ v := by
  refine hS s (c ≫ g) J (fun j => σ j ≫ v)
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, hσ j]) ?_
  intro Ω _ _ x y hy
  have hw : y ≫ s = (x ≫ c) ≫ g := by simpa using hy
  obtain ⟨j, hj, huniq⟩ := hP s' c J σ h Ω x (sq.lift y (x ≫ c) hw) (by simp)
  refine ⟨j, ?_, ?_⟩
  · simp only
    rw [← Category.assoc, hj, sq.lift_fst]
  · intro i hi
    apply huniq
    apply sq.hom_ext
    · simpa using hi
    · simp [hσ i]

private theorem splits_up (hS : SplitsPts) (hP : PtsOfSplits) {P Y Z' Z W : Scheme.{0}} {v : P ⟶ Y} {s' : P ⟶ Z'} {s : Y ⟶ Z}
    {g : Z' ⟶ Z} [IsFinite s] [Etale s] (sq : IsPullback v s' s g) (c : W ⟶ Z') (J : Type) [Finite J] (σ : J → (W ⟶ P))
    (hσ : ∀ j, σ j ≫ s' = c) (h : Splits s (c ≫ g) fun j => σ j ≫ v) : Splits s' c σ := by
  have : IsFinite s' := MorphismProperty.of_isPullback (P := @IsFinite) sq ‹_›
  have : Etale s' := MorphismProperty.of_isPullback (P := @Etale) sq ‹_›
  refine hS s' c J σ hσ ?_
  intro Ω _ _ x y hy
  have hw : (y ≫ v) ≫ s = x ≫ c ≫ g := by
    rw [Category.assoc, sq.w, ← Category.assoc, hy, Category.assoc]
  obtain ⟨j, hj, huniq⟩ := hP s (c ≫ g) J (fun j => σ j ≫ v) h Ω x (y ≫ v) hw
  refine ⟨j, ?_, ?_⟩
  · apply sq.hom_ext
    · simpa using hj
    · simp [hσ j, hy]
  · intro i hi
    apply huniq
    rw [← Category.assoc, hi]

theorem pSplitsBasic : SplitsPts → PtsOfSplits → SplitsBasic := fun hS hP =>
  ⟨fun s _ _ c J _ σ g h => splits_restrict hS hP s c J σ g h,
   fun _ _ _ _ _ _ sq c J _ σ hσ => ⟨splits_down hS hP sq c J σ hσ, splits_up hS hP sq c J σ hσ⟩⟩

end UpperTheory.Gal.G3

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem fib_finite {V U : Scheme.{0}} (r : V ⟶ U) [IsFinite r] (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ U) : Finite {y : Spec (CommRingCat.of K) ⟶ V // y ≫ r = x} :=
  (UpperTheory.Gal.TranscendenceTraces.fibFin_of UpperTheory.Gal.TranscendenceTraces.chart_of r K x).to_subtype

private theorem fEt_of_pullback {P Y Z' Z : Scheme.{0}} (v : P ⟶ Y) (s' : P ⟶ Z') (s : Y ⟶ Z) (g : Z' ⟶ Z)
    (d : ℕ) (h : IsPullback v s' s g) (hs : FEt s d) : FEt s' d := by
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) h hs.1,
    MorphismProperty.of_isPullback (P := @Etale) h hs.2.1, fun K _ _ x => ?_⟩
  let eqv : {y' : Spec (CommRingCat.of K) ⟶ P // y' ≫ s' = x} ≃
      {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x ≫ g} :=
    { toFun := fun y' => ⟨y'.1 ≫ v, by rw [Category.assoc, h.w, ← Category.assoc, y'.2]⟩
      invFun := fun y => ⟨h.lift y.1 x y.2, h.lift_snd _ _ _⟩
      left_inv := fun y' => Subtype.ext (h.hom_ext (by rw [h.lift_fst]) (by rw [h.lift_snd, y'.2]))
      right_inv := fun y => Subtype.ext (h.lift_fst _ _ _) }
  rw [Nat.card_congr eqv]
  exact hs.2.2 K (x ≫ g)

private theorem fEt_comp {W Y Z : Scheme.{0}} (r : W ⟶ Y) (s : Y ⟶ Z) (d e : ℕ) (hr : FEt r e) (hs : FEt s d) :
    FEt (r ≫ s) (d * e) := by
  haveI := hr.1
  haveI := hr.2.1
  haveI := hs.1
  haveI := hs.2.1
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  haveI : Fintype {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x} :=
    @Fintype.ofFinite _ (fib_finite s K x)
  haveI hfin : ∀ y : {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x},
      Finite {w : Spec (CommRingCat.of K) ⟶ W // w ≫ r = y.1} := fun y => fib_finite r K y.1
  let eqv : {w : Spec (CommRingCat.of K) ⟶ W // w ≫ r ≫ s = x} ≃
      Σ y : {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x},
        {w : Spec (CommRingCat.of K) ⟶ W // w ≫ r = y.1} :=
    { toFun := fun w => ⟨⟨w.1 ≫ r, by rw [Category.assoc]; exact w.2⟩, ⟨w.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [← Category.assoc, p.2.2, p.1.2]⟩
      left_inv := fun w => rfl
      right_inv := by
        intro p
        rcases p with ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
        dsimp only at hw
        subst hw
        rfl }
  rw [Nat.card_congr eqv, Nat.card_sigma, Finset.sum_congr rfl (fun y _ => hr.2.2 K y.1),
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hs.2.2 K x, smul_eq_mul]

private theorem fEt_galois (hp : PtsOfSplits) {W Z : Scheme.{0}} (c : W ⟶ Z) (G : Type) [Group G] [Finite G]
    (a : G → (W ⟶ W)) (h : IsGalois c G a) : FEt c (Nat.card G) := by
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2.1
  refine ⟨inferInstance, inferInstance, fun Ω _ _ x => ?_⟩
  obtain ⟨w, hw⟩ := Surjective.surj (f := c) (UpperTheory.Gal.TranscendenceTraces.pt x)
  obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_of c Ω x w hw
  have hsp := h.2.2.2.2.2
  have hac : ∀ g, a g ≫ c = c := hsp.1
  have key : ∀ y : Spec (CommRingCat.of Ω) ⟶ W, y ≫ c = x → ∃! g : G, z ≫ a g = y :=
    fun y hy => hp c c G a hsp Ω z y (by rw [hy, hz])
  let f : G → {y : Spec (CommRingCat.of Ω) ⟶ W // y ≫ c = x} :=
    fun g => ⟨z ≫ a g, by rw [Category.assoc, hac, hz]⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro g g' hgg
      have hv : z ≫ a g = z ≫ a g' := congrArg Subtype.val hgg
      obtain ⟨g0, _, hu⟩ := key (z ≫ a g) (f g).2
      exact (hu g rfl).trans (hu g' hv.symm).symm
    · rintro ⟨y, hy⟩
      obtain ⟨g, hg, _⟩ := key y hy
      exact ⟨g, Subtype.ext hg⟩
  exact (Nat.card_congr (Equiv.ofBijective f hbij)).symm

theorem UpperTheory.Gal.G3.pFEtBasic :
    PtsOfSplits → FEtBasic := by
  intro hp
  exact ⟨fun v s' s g d h hs => fEt_of_pullback v s' s g d h hs, fun r s d e hr hs => fEt_comp r s d e hr hs,
    fun c G _ _ a h => fEt_galois hp c G a h⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtGood
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pEtGood :
    EtnGood → EtGood := by
  intro hE l _ B hl
  have hn := fun n => hE l B hl n 0
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hgal x y hxy
    refine DFinsupp.ext fun n => ?_
    have h1 := congrArg (fun v : Htot l (sch.obj W) => v n) hxy
    exact (hn n).inj p r c hc G a hgal h1
  · intro Z Y p q s _ _ hs
    choose tr htr using fun n => (hn n).tr p q s hs
    let tr' : ∀ n, HQ l (sch.obj Y) n 0 →ₗ[ℚ_[l]] HQ l (sch.obj Z) n 0 := fun n => tr n
    refine ⟨DirectSum.lmap tr', ?_⟩
    intro W r c hc J _ σ hσ hsp
    refine fun (x : Htot l (sch.obj Y)) => DFinsupp.ext fun n => ?_
    have h1 := htr n W r c hc J σ hσ hsp (x n)
    exact h1.trans (DirectSum.sum_apply Finset.univ
      (fun j => ((et l B).pull (σ j) (hσ j)) x) n).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpTr
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pOpTr :
    OpTr.{u} := by
  intro B R _ T hT Z Y Z' p q p' s t hs ht tr htr A
  have key : ∀ (W : Scheme) (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y))
      (hσ : ∀ j, σ j ≫ q = c ≫ p), Splits s c σ → ∀ x,
      T.pull c rfl ((tr ∘ₗ T.pull t ht) x) = ∑ j, T.pull (σ j ≫ t)
        (by rw [Category.assoc, ht]; exact hσ j) x := by
    intro W c J _ σ hσ hspl x
    rw [LinearMap.comp_apply, htr W (c ≫ p) c rfl J σ hσ hspl]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (T.pull_comp (σ j) t (hσ j) ht _ x).symm
  constructor
  · rintro ⟨W, c, G, _, _, a, J, _, σ, h, hgal, hspl, hA⟩
    have hσ : ∀ j, σ j ≫ q = c ≫ p := fun j => by
      rw [← ht, ← Category.assoc]
      exact h j
    apply LinearMap.ext
    intro x
    apply hT.inj p (c ≫ p) c rfl G a hgal
    rw [hA x, key W c J σ hσ hspl x]
  · rintro ⟨W, c, G, _, _, a, J, _, σ, hgal, hspl⟩ rfl
    have hσ : ∀ j, σ j ≫ q = c ≫ p := fun j => by
      rw [← hs, ← Category.assoc, hspl.1 j]
    refine ⟨W, c, G, inferInstance, inferInstance, a, J, inferInstance, σ,
      fun j => by rw [Category.assoc, ht]; exact hσ j, hgal, hspl, fun x => ?_⟩
    exact key W c J σ hσ hspl x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem bc_isPullback {B B' Z Y : Scheme.{0}} (g : B ⟶ B') (p : Z ⟶ B') (s : Y ⟶ Z) :
    IsPullback (pullback.fst (s ≫ p) g) (bcMap g s rfl) s (pullback.fst p g) := by
  refine IsPullback.of_bot ?_ (bcMap_fst g s rfl).symm (IsPullback.of_hasPullback p g)
  rw [bcMap_snd]
  exact IsPullback.of_hasPullback (s ≫ p) g

theorem UpperTheory.Gal.G3.pBcSplits :
    SplitsBasic → BcSplits := by
  intro hb B B' Z Y W g p q r s hs c hc J _ σ hσ _ _
  subst hs
  subst hc
  have sq := bc_isPullback g p s
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) sq ‹_›,
    MorphismProperty.of_isPullback (P := @Etale) sq ‹_›, fun h => ?_⟩
  obtain ⟨h0, -⟩ := id h
  have hcomp : ∀ j, bcMap g (σ j) (hσ j) ≫ bcMap g s rfl = bcMap g c rfl := by
    intro j
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst g s rfl, ← Category.assoc, bcMap_fst g (σ j) (hσ j), Category.assoc, h0 j,
        bcMap_fst g c rfl]
    · rw [Category.assoc, bcMap_snd g s rfl, bcMap_snd g (σ j) (hσ j), bcMap_snd g c rfl]
  have e1 : bcMap g c rfl ≫ pullback.fst p g = pullback.fst (c ≫ p) g ≫ c := bcMap_fst g c rfl
  have e2 : (fun j => bcMap g (σ j) (hσ j) ≫ pullback.fst (s ≫ p) g) = fun j => pullback.fst (c ≫ p) g ≫ σ j :=
    funext fun j => bcMap_fst g (σ j) (hσ j)
  have h2 : Splits s (bcMap g c rfl ≫ pullback.fst p g)
      (fun j => bcMap g (σ j) (hσ j) ≫ pullback.fst (s ≫ p) g) := by
    rw [e1, e2]
    exact hb.1 s c J σ (pullback.fst (c ≫ p) g) h
  exact (hb.2 (pullback.fst (s ≫ p) g) (bcMap g s rfl) s (pullback.fst p g) sq (bcMap g c rfl) J
    (fun j => bcMap g (σ j) (hσ j)) hcomp).2 h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtTr
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pEtTr :
    EtTr := by
  intro l _ B hl n i Z Y p q s _ _ W r c hc J _ σ hσ hsp x
  obtain ⟨hsc, hiso⟩ := hsp
  have hT := UpperTheory.Gal.TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2
  let e := Fintype.equivFin J
  have hiso' : IsIso (Sigma.desc fun k : Fin (Fintype.card J) =>
      pullback.lift (σ (e.symm k)) (𝟙 W) (by rw [hsc, Category.id_comp])) := by
    have hEq : (Sigma.desc fun k : Fin (Fintype.card J) =>
        pullback.lift (σ (e.symm k)) (𝟙 W) (by rw [hsc, Category.id_comp])) =
        (Sigma.reindex e.symm (fun _ : J => W)).hom ≫
          Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hsc, Category.id_comp]) := by
      refine Sigma.hom_ext _ _ (fun k => ?_)
      rw [Sigma.ι_desc]
      have h4 := Sigma.ι_reindex_hom_assoc (ε := e.symm) (f := fun _ : J => W) (b := k)
        (h := Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hsc, Category.id_comp]))
      rw [Sigma.ι_desc] at h4
      exact h4.symm
    rw [hEq]
    infer_instance
  have hlZ : IsUnit ((l : Γ(Z, ⊤))) := by
    simpa using hl.map (Scheme.Hom.appTop p).hom
  have h1 := hT l n i s hlZ W c (Fintype.card J) (fun k => σ (e.symm k)) (fun k => hsc _) hiso'
  have h2 : ∀ y : HQ l (sch.obj Y) n i, pullHQ l (sch.map c) n i
      (TranscendenceTraces.trHQ l s (TranscendenceTraces.Wt.const Y 1) n i y) = ∑ j, pullHQ l (sch.map (σ j)) n i y := by
    intro y
    have h3 := LinearMap.congr_fun h1 y
    rw [LinearMap.comp_apply, LinearMap.sum_apply] at h3
    rw [h3]
    exact Equiv.sum_comp e.symm (fun j => pullHQ l (sch.map (σ j)) n i y)
  exact h2 x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtnGood
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem push_one_eq {W Z : Scheme.{0}} (c : W ⟶ Z) (d : ℕ) (hd : d ≠ 0) (h : FEt c d) :
    (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1).push c = UpperTheory.Gal.TranscendenceTraces.Wt.const Z (d : ℤ) := by
  funext Ω _ _ x
  have hx := h.2.2 Ω x
  simp only [UpperTheory.Gal.TranscendenceTraces.Wt.push, UpperTheory.Gal.TranscendenceTraces.Wt.const]
  have hne : Nat.card {y // y ≫ c = x} ≠ 0 := by rw [hx]; exact hd
  have hfin : Finite {y // y ≫ c = x} := Nat.finite_of_card_ne_zero hne
  have hs : (UpperTheory.Gal.TranscendenceTraces.fib c x).Finite := Set.finite_coe_iff.mp hfin
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Set.ncard_eq_toFinset_card _ hs, ← Nat.card_coe_set_eq]
  exact_mod_cast hx

theorem UpperTheory.Gal.G3.pEtnGood :
    FEtBasic → EtTr → EtnGood := by
  intro hF hT l _ B hl n i
  obtain ⟨hW, -, hA⟩ := UpperTheory.Gal.TranscendenceTraces.all_holds
  have hFlat : UpperTheory.Gal.TranscendenceTraces.WtFlat := hW.2.2.2.2.2.2.2.2.2.1
  have hMult : UpperTheory.Gal.TranscendenceTraces.MultBasic := hW.2.2.2.2.2.2.2.1
  have hDeg : UpperTheory.Gal.TranscendenceTraces.TrDegQ := hA.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hG
    have hd : FEt c (Nat.card G) := hF.2.2 c G a hG
    have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have hpush := push_one_eq c _ hpos hd
    obtain ⟨hfin, het, -⟩ := hd
    have hwt : UpperTheory.Gal.TranscendenceTraces.IsWt c (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1) := by
      have h1 := hFlat c
      rwa [hMult.2.2 c] at h1
    have hlZ : IsUnit ((l : ℕ) : Γ(Z, ⊤)) := by
      have := hl.map p.appTop.hom
      simpa using this
    have key := hDeg l n i c _ _ hwt hlZ hpush
    have hne : (((Nat.card G : ℕ) : ℤ) : ℚ_[l]) ≠ 0 := by
      exact_mod_cast hpos
    intro x y hxy
    have hxy' : pullHQ l (sch.map c) n i x = pullHQ l (sch.map c) n i y := hxy
    have e : ∀ t, UpperTheory.Gal.TranscendenceTraces.trHQ l c (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1) n i (pullHQ l (sch.map c) n i t) =
        (((Nat.card G : ℕ) : ℤ) : ℚ_[l]) • t := fun t => LinearMap.congr_fun key t
    have ex := e x
    rw [hxy', e y] at ex
    exact smul_right_injective _ hne ex.symm
  · intro Z Y p q s _ _ _
    exact ⟨_, hT l B hl n i p q s⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdStep
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem mem_range_diagonal_iff {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsOpenImmersion (pullback.diagonal s)]
    (Ω : Type) [Field Ω] (y : UpperTheory.Gal.G3.sp Ω ⟶ pullback s s) :
    y (IsLocalRing.closedPoint Ω) ∈ Set.range (pullback.diagonal s) ↔
      y ≫ pullback.fst s s = y ≫ pullback.snd s s := by
  constructor
  · rintro ⟨z, hz⟩
    have hsub : Set.range y ⊆ Set.range (pullback.diagonal s) := by
      rintro _ ⟨q, rfl⟩
      have hq : q = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
      rw [hq]
      exact ⟨z, hz⟩
    have hfac := IsOpenImmersion.lift_fac (pullback.diagonal s) y hsub
    rw [← hfac, Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
  · intro h
    refine ⟨(y ≫ pullback.fst s s) (IsLocalRing.closedPoint Ω), ?_⟩
    have hy : (y ≫ pullback.fst s s) ≫ pullback.diagonal s = y := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, h]
    conv_rhs => rw [← hy]
    rfl

theorem UpperTheory.Gal.G3.pOrdStep :
    OrdStep := by
  intro Z Y W s _ _ c d σ hσ
  have hc : ∀ j, pullback.fst s c ≫ s = (pullback.snd s c ≫ σ j) ≫ s := fun j => by
    rw [Category.assoc, hσ j, pullback.condition]
  let φ : Fin d → (pullback s c ⟶ pullback s s) := fun j =>
    pullback.lift (pullback.fst s c) (pullback.snd s c ≫ σ j) (hc j)
  have hopen : ∀ j, IsOpen ((φ j) ⁻¹' Set.range (pullback.diagonal s)) := fun j =>
    (pullback.diagonal s).isOpenEmbedding.isOpen_range.preimage (φ j).continuous
  have hclosed : ∀ j, IsClosed ((φ j) ⁻¹' Set.range (pullback.diagonal s)) := fun j =>
    (pullback.diagonal s).isClosedEmbedding.isClosed_range.preimage (φ j).continuous
  refine ⟨⟨(⋃ j, (φ j) ⁻¹' Set.range (pullback.diagonal s))ᶜ,
    (isClosed_iUnion_of_finite hclosed).isOpen_compl⟩, (isOpen_iUnion hopen).isClosed_compl, ?_⟩
  intro Ω _ x
  have key : ∀ j, (x ≫ φ j) (IsLocalRing.closedPoint Ω) ∈ Set.range (pullback.diagonal s) ↔
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j := by
    intro j
    rw [mem_range_diagonal_iff s Ω (x ≫ φ j)]
    simp only [Category.assoc, φ, pullback.lift_fst, pullback.lift_snd]
  show x (IsLocalRing.closedPoint Ω) ∈ (⋃ j, (φ j) ⁻¹' Set.range (pullback.diagonal s))ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, not_exists]
  refine forall_congr' (fun j => ?_)
  exact (not_congr (key j)).trans ⟨fun h e => h e.symm, fun h e => h e.symm⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClosD
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

namespace UpperTheory.Gal.G3

private theorem fibre_finite {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] (Ω : Type) [Field Ω] (x : sp Ω ⟶ Z) :
    Finite {y : sp Ω ⟶ Y // y ≫ s = x} := by
  have h := UpperTheory.Gal.TranscendenceTraces.fibFin_of UpperTheory.Gal.TranscendenceTraces.chart_of s Ω x
  exact h.to_subtype

private theorem epi_of_field {Ω Ω' : Type} [Field Ω] [Field Ω'] (x : sp Ω' ⟶ sp Ω) : Epi x := by
  exact Flat.epi_of_flat_of_surjective x

private theorem point_over {Z : Scheme.{0}} (z : Z) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (x : sp Ω ⟶ Z), x (IsLocalRing.closedPoint Ω) = z := by
  refine ⟨AlgebraicClosure (Z.residueField z), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z)))) ≫
      Z.fromSpecResidueField z, ?_⟩
  exact Scheme.fromSpecResidueField_apply z _

end UpperTheory.Gal.G3

private theorem exists_comp_sigma_eq_of_comp_eq_comp {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] {d : ℕ}
    (hd : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ Z),
      Nat.card {y // y ≫ s = x} = d)
    (c : W ⟶ Z) (σ : Fin d → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c)
    (hinj : ∀ (Ω : Type) [Field Ω] (x : UpperTheory.Gal.G3.sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : UpperTheory.Gal.G3.sp Ω ⟶ W) (y : UpperTheory.Gal.G3.sp Ω ⟶ Y)
    (hy : y ≫ s = x ≫ c) :
    ∃ j, x ≫ σ j = y := by
  have hfin := UpperTheory.Gal.G3.fibre_finite s Ω (x ≫ c)
  let f : Fin d → {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x ≫ c} :=
    fun j => ⟨x ≫ σ j, by rw [Category.assoc, hσ]⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact hinj Ω x (congrArg Subtype.val hij)
  have hb := hf.bijective_of_nat_card_le (by rw [hd Ω (x ≫ c), Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨j, hj⟩ := hb.2 ⟨y, hy⟩
  exact ⟨j, congrArg Subtype.val hj⟩

theorem UpperTheory.Gal.G3.pGalClosD :
    SplitsPts → OrdEx → GalClosD := by
  intro hS hO Z Y s d hF
  obtain ⟨hfin, het, hd⟩ := hF
  obtain ⟨W, c, σ, hcf, hce, hσ, hinj, huniv⟩ := hO s d
  have hex : ∀ g : Equiv.Perm (Fin d), ∃! w : W ⟶ W, w ≫ c = c ∧ ∀ j, w ≫ σ j = σ (g j) := by
    intro g
    refine huniv W c (fun j => σ (g j)) (fun j => hσ (g j)) ?_
    intro Ω _ x i j hij
    exact g.injective (hinj Ω x hij)
  choose a ha using fun g => (hex g).exists
  have hone : a 1 = 𝟙 W :=
    (hex 1).unique (ha 1) ⟨Category.id_comp c, fun j => by simp⟩
  have hmul : ∀ g h, a (g * h) = a g ≫ a h := by
    intro g h
    refine (hex (g * h)).unique (ha (g * h)) ⟨?_, fun j => ?_⟩
    · rw [Category.assoc, (ha h).1, (ha g).1]
    · rw [Category.assoc, (ha h).2 j, (ha g).2 (h j)]
      rfl
  have hspl : Splits s c σ := by
    refine hS s c (Fin d) σ hσ ?_
    intro Ω _ _ x y hy
    obtain ⟨j, hj⟩ := exists_comp_sigma_eq_of_comp_eq_comp s hd c σ hσ hinj Ω x y hy
    exact ⟨j, hj, fun j' hj' => hinj Ω x (hj'.trans hj.symm)⟩
  have hsur : Surjective c := by
    constructor
    intro z
    obtain ⟨Ω, _, _, x, hx⟩ := UpperTheory.Gal.G3.point_over z
    have hfF := UpperTheory.Gal.G3.fibre_finite s Ω x
    have hcard : Nat.card {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x} = d := hd Ω x
    let e := Finite.equivFin {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x}
    let yy : Fin d → (UpperTheory.Gal.G3.sp Ω ⟶ Y) := fun j => (e.symm (Fin.cast hcard.symm j)).1
    have hyy : ∀ j, yy j ≫ s = x := fun j => (e.symm (Fin.cast hcard.symm j)).2
    have hinj' : ∀ (Ω' : Type) [Field Ω'] (x' : UpperTheory.Gal.G3.sp Ω' ⟶ UpperTheory.Gal.G3.sp Ω),
        Function.Injective fun j => x' ≫ yy j := by
      intro Ω' _ x' i j hij
      haveI := UpperTheory.Gal.G3.epi_of_field x'
      have h1 : yy i = yy j := (cancel_epi x').1 hij
      have h2 := Subtype.val_injective h1
      exact Fin.cast_injective _ (e.symm.injective h2)
    obtain ⟨w, ⟨hw, _⟩, _⟩ := huniv (UpperTheory.Gal.G3.sp Ω) x yy hyy hinj'
    refine ⟨w (IsLocalRing.closedPoint Ω), ?_⟩
    rw [← hx, ← hw]
    rfl
  have hgal : Splits c c a := by
    refine hS c c (Equiv.Perm (Fin d)) a (fun g => (ha g).1) ?_
    intro Ω _ _ x y hy
    have hpt : ∀ j, ∃ k, x ≫ σ k = y ≫ σ j := by
      intro j
      exact exists_comp_sigma_eq_of_comp_eq_comp s hd c σ hσ hinj Ω x (y ≫ σ j) (by rw [Category.assoc, hσ, hy])
    choose p hp using hpt
    have hpi : Function.Injective p := by
      intro i j hij
      apply hinj Ω y
      simp only
      rw [← hp i, ← hp j, hij]
    let g := Equiv.ofBijective p (Finite.injective_iff_bijective.1 hpi)
    have hinjy : ∀ (Ω' : Type) [Field Ω'] (x' : UpperTheory.Gal.G3.sp Ω' ⟶ UpperTheory.Gal.G3.sp Ω),
        Function.Injective fun j => x' ≫ (y ≫ σ j) := by
      intro Ω' _ x' i j hij
      apply hinj Ω' (x' ≫ y)
      simpa only [Category.assoc] using hij
    refine ⟨g, ?_, ?_⟩
    · refine (huniv (UpperTheory.Gal.G3.sp Ω) (x ≫ c) (fun j => y ≫ σ j)
        (fun j => by rw [Category.assoc, hσ, hy]) hinjy).unique ⟨?_, fun j => ?_⟩ ⟨hy, fun j => rfl⟩
      · rw [Category.assoc, (ha g).1]
      · rw [Category.assoc, (ha g).2 j]
        exact hp j
    · intro g' hg'
      refine Equiv.ext fun j => ?_
      apply hinj Ω x
      simp only
      rw [← (ha g').2 j, ← Category.assoc, hg', ← hp j]
      rfl
  exact ⟨W, c, Equiv.Perm (Fin d), inferInstance, inferInstance, a, σ,
    ⟨hcf, hce, hsur, hone, hmul, hgal⟩, hspl⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdEx
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Gal.G3

private theorem ordExStep (hS : OrdStep) {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (d : ℕ)
    (c : W ⟶ Z) (σ : Fin d → (W ⟶ Y)) (hcf : IsFinite c) (hce : Etale c) (hσ : ∀ j, σ j ≫ s = c)
    (hinj : ∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j)
    (huniv : ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin d → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
      (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
      ∃! w : U ⟶ W, w ≫ c = z ∧ ∀ j, w ≫ σ j = y j) :
    ∃ (W' : Scheme.{0}) (c' : W' ⟶ Z) (σ' : Fin (d + 1) → (W' ⟶ Y)), IsFinite c' ∧ Etale c' ∧
      (∀ j, σ' j ≫ s = c') ∧
      (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W'), Function.Injective fun j => x ≫ σ' j) ∧
      ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin (d + 1) → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
        (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
        ∃! w : U ⟶ W', w ≫ c' = z ∧ ∀ j, w ≫ σ' j = y j := by
  haveI := hcf
  haveI := hce
  let P := pullback s c
  have hsq : ∀ j, σ j ≫ s = 𝟙 W ≫ c := fun j => by rw [hσ j, Category.id_comp]
  let sec : Fin d → (W ⟶ P) := fun j => pullback.lift (σ j) (𝟙 W) (hsq j)
  have hsec1 : ∀ j, sec j ≫ pullback.fst s c = σ j := fun j => pullback.lift_fst _ _ _
  have hsec2 : ∀ j, sec j ≫ pullback.snd s c = 𝟙 W := fun j => pullback.lift_snd _ _ _
  haveI hOP : MorphismProperty.HasOfPostcompProperty (@IsOpenImmersion : MorphismProperty Scheme)
      (@Etale : MorphismProperty Scheme) := by
    apply MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2
    intro X Y f hf
    haveI : Etale f := hf
    exact inferInstanceAs <| IsOpenImmersion (pullback.diagonal f)
  have hopen : ∀ j, IsOpenImmersion (sec j) := fun j =>
    MorphismProperty.of_postcomp (W := (@IsOpenImmersion : MorphismProperty Scheme))
      (W' := (@Etale : MorphismProperty Scheme)) (sec j) (pullback.snd s c)
      (inferInstanceAs (Etale (pullback.snd s c)))
      (by rw [hsec2]; exact inferInstanceAs (IsOpenImmersion (𝟙 W)))
  have hclosed : ∀ j, IsClosedImmersion (sec j) := fun j => by
    haveI : IsClosedImmersion (sec j ≫ pullback.snd s c) := by
      rw [hsec2]; infer_instance
    exact IsClosedImmersion.of_comp (sec j) (pullback.snd s c)
  let S : Set P := ⋃ j, Set.range (sec j).base
  have hSc : IsClosed S := isClosed_iUnion_of_finite fun j => (hclosed j).isClosedEmbedding.isClosed_range
  have hSo : IsOpen S := isOpen_iUnion fun j => (hopen j).base_open.isOpen_range
  let O : P.Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  have hOr : Set.range O.ι.base = Sᶜ := O.range_ι
  haveI : IsClosedImmersion O.ι := .of_isPreimmersion _ (by rw [hOr]; exact hSo.isClosed_compl)
  have hpt : ∀ (j : Fin d) (Ω : Type) [Field Ω] (x : sp Ω ⟶ P),
      x.base (IsLocalRing.closedPoint Ω) ∈ Set.range (sec j).base →
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j := by
    intro j Ω _ x hx
    have hr : Set.range x.base ⊆ Set.range (sec j).base := by
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim p (IsLocalRing.closedPoint Ω)]
    haveI := hopen j
    have hf := IsOpenImmersion.lift_fac (sec j) x hr
    rw [← hf, Category.assoc, Category.assoc, hsec1, reassoc_of% hsec2]
  have hback : ∀ (j : Fin d) {T : Scheme.{0}} (x : T ⟶ P),
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j → x = (x ≫ pullback.snd s c) ≫ sec j := by
    intro j T x hx
    apply pullback.hom_ext
    · rw [Category.assoc, hsec1, hx, Category.assoc]
    · rw [Category.assoc, hsec2, Category.comp_id]
  refine ⟨O, O.ι ≫ pullback.snd s c ≫ c,
    Fin.snoc (α := fun _ => ((O : Scheme) ⟶ Y)) (fun j => O.ι ≫ pullback.snd s c ≫ σ j)
      (O.ι ≫ pullback.fst s c), inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [Fin.snoc_last, Category.assoc, pullback.condition]
    · simp only [Fin.snoc_castSucc, Category.assoc, hσ j]
  · intro Ω _ x
    have key : ∀ j : Fin d, x ≫ O.ι ≫ pullback.fst s c ≠ x ≫ O.ι ≫ pullback.snd s c ≫ σ j := by
      intro j h
      have h2 := hback j (x ≫ O.ι) (by simpa only [Category.assoc] using h)
      have hin : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ S := by
        rw [h2]
        exact Set.mem_iUnion.2 ⟨j, _, rfl⟩
      have hO : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ Set.range O.ι.base :=
        ⟨x.base (IsLocalRing.closedPoint Ω), rfl⟩
      rw [hOr] at hO
      exact hO hin
    intro a b hab
    simp only at hab
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab (key j)
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab.symm (key i)
      | cast j =>
        simp only [Fin.snoc_castSucc] at hab
        exact congrArg Fin.castSucc (hinj Ω (x ≫ O.ι ≫ pullback.snd s c) (by simpa only [Category.assoc] using hab))
  · intro U z y hy hinjU
    obtain ⟨w0, ⟨hw0c, hw0σ⟩, hw0u⟩ := huniv U z (fun j => y j.castSucc) (fun j => hy _)
      (fun Ω _ x a b h => Fin.castSucc_injective _ (hinjU Ω x h))
    let φ : U ⟶ P := pullback.lift (y (Fin.last d)) w0 (by rw [hy, hw0c])
    have hφ1 : φ ≫ pullback.fst s c = y (Fin.last d) := pullback.lift_fst _ _ _
    have hφ2 : φ ≫ pullback.snd s c = w0 := pullback.lift_snd _ _ _
    have hrange : Set.range φ.base ⊆ Set.range O.ι.base := by
      rintro _ ⟨u, rfl⟩
      rw [hOr]
      intro hu
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hu
      let x := U.fromSpecResidueField u
      have hxu : x.base (IsLocalRing.closedPoint (U.residueField u)) = u :=
        U.fromSpecResidueField_apply u _
      have := hpt j (U.residueField u) (x ≫ φ) (by
        show φ.base (x.base _) ∈ _
        rw [hxu]
        exact hj)
      rw [Category.assoc, Category.assoc, hφ1, reassoc_of% hφ2, hw0σ] at this
      exact (Fin.castSucc_lt_last j).ne (hinjU _ x this).symm
    refine ⟨IsOpenImmersion.lift O.ι φ hrange, ⟨?_, fun k => ?_⟩, ?_⟩
    · rw [IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0c]
    · refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [Fin.snoc_last, IsOpenImmersion.lift_fac_assoc, hφ1]
      · rw [Fin.snoc_castSucc, IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0σ]
    · rintro w' ⟨hw'c, hw'σ⟩
      rw [← cancel_mono O.ι, IsOpenImmersion.lift_fac]
      have e2 : w' ≫ O.ι ≫ pullback.snd s c = w0 := by
        refine hw0u _ ⟨by simpa only [Category.assoc] using hw'c, fun j => ?_⟩
        have := hw'σ j.castSucc
        rw [Fin.snoc_castSucc] at this
        simpa only [Category.assoc] using this
      apply pullback.hom_ext
      · have := hw'σ (Fin.last d)
        rw [Fin.snoc_last] at this
        rw [Category.assoc, this, hφ1]
      · rw [Category.assoc, e2, hφ2]

theorem pOrdEx : OrdStep → OrdEx := by
  intro hS Z Y s _ _ d
  induction d with
  | zero =>
    refine ⟨Z, 𝟙 Z, Fin.elim0, inferInstance, inferInstance, fun j => j.elim0, ?_, ?_⟩
    · intro Ω _ x a
      exact a.elim0
    · intro U z y _ _
      exact ⟨z, ⟨Category.comp_id _, fun j => j.elim0⟩, fun w hw => by simpa using hw.1⟩
  | succ d ih =>
    obtain ⟨W, c, σ, hcf, hce, hσ, hinj, huniv⟩ := ih
    exact ordExStep hS s d c σ hcf hce hσ hinj huniv

end UpperTheory.Gal.G3

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEt
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pOpEt :
    OpEt := by
  intro l _ B Z Y Z' p p' s t hst A
  constructor
  · rintro ⟨W, c, G, i1, hG, a, J, i2, σ, _hh, hrest⟩
    exact ⟨W, c, G, i1, hG, a, J, i2, σ, hrest⟩
  · rintro ⟨W, c, G, i1, hG, a, J, i2, σ, hrest⟩
    exact ⟨W, c, G, i1, hG, a, J, i2, σ,
      fun j => by rw [Category.assoc, hst, ← Category.assoc, hrest.2.1.1 j], hrest⟩
end
