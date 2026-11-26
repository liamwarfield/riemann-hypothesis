module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PlaceData
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EtOfRestrict
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.BaseChangeExamples

private theorem isUnit_nat {k : Type} [Field k] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
    (h : (m : k) ≠ 0) : IsUnit (m : Γ(X, ⊤)) := by
  have := (h.isUnit).map ((q.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  simpa using this

private theorem isWt_one {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p] : TranscendenceTraces.IsWt p (Wt.const Z 1) := by
  have h := TranscendenceTraces.multBasic_holds.2.2 p
  rw [← h]
  exact TranscendenceTraces.wtFlat_holds p

private theorem et_of_pb {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) [Etale p] : Etale s :=
  MorphismProperty.of_isPullback (P := @Etale) h ‹_›

private theorem et_of_restrict {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) (f : Γ(D, ⊤)) (hf : IsUnit (e.appTop f)) (he : Etale (p ∣_ D.basicOpen f)) : Etale s := by
  have hr : Set.range e ⊆ Set.range (D.basicOpen f).ι := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ e ⁻¹ᵁ D.basicOpen f := by
      rw [Scheme.preimage_basicOpen]
      have : C.basicOpen ((e.app ⊤).hom f) = ⊤ := Scheme.basicOpen_of_isUnit _ hf
      rw [this]; trivial
    rw [Scheme.Opens.range_ι]
    exact hx
  let e' : C ⟶ (D.basicOpen f).toScheme := IsOpenImmersion.lift _ e hr
  have he' : e' ≫ (D.basicOpen f).ι = e := IsOpenImmersion.lift_fac _ _ _
  have hq := isPullback_morphismRestrict p (D.basicOpen f)
  have hw : (s ≫ e') ≫ (D.basicOpen f).ι = u ≫ p := by
    rw [Category.assoc, he', h.w]
  let t := hq.lift (s ≫ e') u hw
  have ht1 : t ≫ (p ∣_ D.basicOpen f) = s ≫ e' := hq.lift_fst _ _ _
  have ht2 : t ≫ (p ⁻¹ᵁ D.basicOpen f).ι = u := hq.lift_snd _ _ _
  have hpb : IsPullback t s (p ∣_ D.basicOpen f) e' := by
    refine IsPullback.of_right (h₁₂ := (p ⁻¹ᵁ D.basicOpen f).ι) (h₂₂ := (D.basicOpen f).ι) (v₁₃ := p) ?_ ht1 hq.flip
    rw [ht2, he']
    exact h
  exact et_of_pb hpb

end UpperTheory.Gal.Mod.BaseChangeExamples

open UpperTheory.Gal.Mod.BaseChangeExamples in
theorem UpperTheory.Gal.Mod.bcEx :
    BCEx := by
  intro p O k Ω _ _ _ _ _ hp Y g T hg
  let q := pullback.snd g (sp (algebraMap O k))
  let s : geom Ω q ⟶ Y := pullback.fst _ _ ≫ pullback.fst _ _
  have h : IsPullback (pullback.fst T.p s) (pullback.snd T.p s) T.p s := IsPullback.of_hasPullback T.p s
  have hfin : IsFinite (pullback.snd T.p s) := by
    have := T.fin
    infer_instance
  have het : Etale (pullback.snd T.p s) :=
    et_of_restrict h (p : Γ(Y, ⊤)) (by simpa using isUnit_nat (pullback.fst q (sp (algebraMap k Ω)) ≫ q) p hp) T.et
  have c1 : (pullback.fst T.p s ≫ T.r) ≫ g =
      (pullback.snd T.p s ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ q) ≫ sp (algebraMap O k) := by
    have e1 : pullback.fst T.p s ≫ T.p = pullback.snd T.p s ≫ s := h.w
    have e2 : pullback.fst g (sp (algebraMap O k)) ≫ g = q ≫ sp (algebraMap O k) := pullback.condition
    rw [Category.assoc, hg, reassoc_of% e1]
    simp only [s, Category.assoc, e2]
  let a : pullback T.p s ⟶ pullback g (sp (algebraMap O k)) :=
    pullback.lift (pullback.fst T.p s ≫ T.r) (pullback.snd T.p s ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ q) c1
  have ha1 : a ≫ pullback.fst g (sp (algebraMap O k)) = pullback.fst T.p s ≫ T.r := pullback.lift_fst _ _ _
  have ha2 : a ≫ q = pullback.snd T.p s ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ q := pullback.lift_snd _ _ _
  have c2 : a ≫ q = (pullback.snd T.p s ≫ pullback.snd q (sp (algebraMap k Ω))) ≫ sp (algebraMap k Ω) := by
    have e3 : pullback.fst q (sp (algebraMap k Ω)) ≫ q = pullback.snd q (sp (algebraMap k Ω)) ≫ sp (algebraMap k Ω) :=
      pullback.condition
    rw [ha2, e3, Category.assoc]
  let b : pullback T.p s ⟶ geom Ω q := pullback.lift a (pullback.snd T.p s ≫ pullback.snd q (sp (algebraMap k Ω))) c2
  have hb1 : b ≫ pullback.fst q (sp (algebraMap k Ω)) = a := pullback.lift_fst _ _ _
  have hb2 : b ≫ pullback.snd q (sp (algebraMap k Ω)) = pullback.snd T.p s ≫ pullback.snd q (sp (algebraMap k Ω)) :=
    pullback.lift_snd _ _ _
  refine ⟨⟨pullback T.p s, pullback.snd T.p s, b, Wt.const _ 1, hfin, isWt_one _⟩, pullback.fst T.p s, h, ?_, hb2, rfl⟩
  change b ≫ pullback.fst q (sp (algebraMap k Ω)) ≫ pullback.fst g (sp (algebraMap O k)) = pullback.fst T.p s ≫ T.r
  rw [reassoc_of% hb1, ha1]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PGrPass
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.BlockProjectionMultiplicative

variable {d : ℕ} {L : Type} [Field L]

private def blkPart (c : Fin d → ℕ) (M : Matrix (Fin d) (Fin d) L) : Matrix (Fin d) (Fin d) L :=
  fun i j => if c i = c j then M i j else 0

private theorem blkPart_add (c : Fin d → ℕ) (M N : Matrix (Fin d) (Fin d) L) :
    blkPart c (M + N) = blkPart c M + blkPart c N := by
  ext i j
  simp only [blkPart, Matrix.add_apply]
  split_ifs <;> simp

private theorem blkPart_smul (c : Fin d → ℕ) (a : L) (M : Matrix (Fin d) (Fin d) L) :
    blkPart c (a • M) = a • blkPart c M := by
  ext i j
  simp only [blkPart, Matrix.smul_apply]
  split_ifs <;> simp

private theorem blkPart_one (c : Fin d → ℕ) : blkPart c (1 : Matrix (Fin d) (Fin d) L) = 1 := by
  ext i j
  simp only [blkPart]
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne h]; simp

private theorem blkPart_mul (c : Fin d → ℕ) {M N : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (hN : N.BlockTriangular c) :
    blkPart c (M * N) = blkPart c M * blkPart c N := by
  ext i j
  rw [Matrix.mul_apply]
  change (if c i = c j then (M * N) i j else 0) =
    ∑ k, (if c i = c k then M i k else 0) * (if c k = c j then N k j else 0)
  by_cases h : c i = c j
  · rw [if_pos h, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : c i = c k
    · have h2 : c k = c j := h1.symm.trans h
      rw [if_pos h1, if_pos h2]
    · rw [if_neg h1, zero_mul]
      rcases lt_or_gt_of_ne h1 with h3 | h3
      · have h4 : c j < c k := h ▸ h3
        rw [hN h4, mul_zero]
      · rw [hM h3, zero_mul]
  · rw [if_neg h]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h1 : c i = c k
    · have h2 : ¬ c k = c j := fun e => h (h1.trans e)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

private theorem blkTri_pow (c : Fin d → ℕ) {M : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (n : ℕ) : (M ^ n).BlockTriangular c := by
  induction n with
  | zero => rw [pow_zero]; exact Matrix.blockTriangular_one
  | succ n ih => rw [pow_succ]; exact ih.mul hM

private theorem blkPart_pow (c : Fin d → ℕ) {M : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (n : ℕ) : blkPart c (M ^ n) = blkPart c M ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, blkPart_one]
  | succ n ih => rw [pow_succ, pow_succ, blkPart_mul c (blkTri_pow c hM n) hM, ih]

private theorem blkPart_aeval (c : Fin d → ℕ) {M : Matrix (Fin d) (Fin d) L}
    (hM : M.BlockTriangular c) (P : Polynomial L) :
    blkPart c (Polynomial.aeval M P) = Polynomial.aeval (blkPart c M) P := by
  refine Polynomial.induction_on' P (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add (f := _), map_add (f := _), blkPart_add, hp, hq]
  · rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def, ← Algebra.smul_def,
      blkPart_smul, blkPart_pow c hM]

end UpperTheory.Gal.Mod.BlockProjectionMultiplicative

open UpperTheory.Gal.Mod.BlockProjectionMultiplicative in
theorem UpperTheory.Gal.Mod.grPass :
    GrPass := by
  intro Γ L _ _ d ρ₀ ρ hG g P h0
  obtain ⟨c, hc⟩ := hG
  obtain ⟨hT, hD⟩ := hc g
  have e : (ρ g : Matrix (Fin d) (Fin d) L) = blkPart c (ρ₀ g : Matrix (Fin d) (Fin d) L) := by
    ext i j
    exact hD i j
  rw [e, ← blkPart_aeval c hT, h0]
  ext i j
  simp [blkPart]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PHopOp
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et NumberField IsDedekindDomain TensorProduct
open GlobalTheory.GalV (HTower Htot hop galV Splits IsCorrOp IsGalois pullTot)
open UpperTheory.Gal.TranscendenceTraces (Wt trHQ)
open UpperTheory.Gal UpperTheory.Gal.Mod UpperTheory.Gal.Int.Geo
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.Gal.Mod.HopfOperations

private theorem isUnit_nat {k : Type} [Field k] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
    (h : (m : k) ≠ 0) : IsUnit (m : Γ(X, ⊤)) := by
  have := (h.isUnit).map ((q.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  simpa using this

private theorem isWt_one {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] [Etale p] : TranscendenceTraces.IsWt p (Wt.const Z 1) := by
  have h := TranscendenceTraces.multBasic_holds.2.2 p
  rw [← h]
  exact TranscendenceTraces.wtFlat_holds p

private theorem fin_of_pb {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) [IsFinite p] : IsFinite s :=
  MorphismProperty.of_isPullback (P := @IsFinite) h ‹_›

private theorem et_of_pb {A B C D : Scheme.{0}} {u : A ⟶ B} {s : A ⟶ C} {p : B ⟶ D} {e : C ⟶ D}
    (h : IsPullback u s p e) [Etale p] : Etale s :=
  MorphismProperty.of_isPullback (P := @Etale) h ‹_›

private theorem pullQ_comp (l : ℕ) [Fact l.Prime] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (n i : ℤ) :
    pullHQ l (f ≫ g) n i = pullHQ l f n i ∘ₗ pullHQ l g n i := by
  unfold pullHQ; rw [pullHl_comp]; exact LinearMap.baseChange_comp _ _

private theorem gm_fst {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u := pullback.lift_fst _ _ _

private theorem gm_snd {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y)
    (hu : u ≫ q = p) : geomMap Ω p u hu ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

private theorem gm_pb {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (s : X ⟶ Y) :
    IsPullback (pullback.fst (s ≫ q) (sp (algebraMap k Ω))) (geomMap Ω (s ≫ q) s rfl) s
      (pullback.fst q (sp (algebraMap k Ω))) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd q (sp (algebraMap k Ω))) (v₂₂ := q) (h₃₁ := sp (algebraMap k Ω)) ?_
    (gm_fst Ω _ _ _).symm (IsPullback.of_hasPullback q _)
  rw [gm_snd]
  exact IsPullback.of_hasPullback _ _

private theorem card_pb {A B C D P : Scheme.{0}} {a : A ⟶ C} {v : A ⟶ B} {u : C ⟶ D} {b : B ⟶ D}
    (h : IsPullback a v u b) (x : P ⟶ B) :
    Nat.card {y : P ⟶ A // y ≫ v = x} = Nat.card {y : P ⟶ C // y ≫ u = x ≫ b} :=
  Nat.card_congr
    { toFun := fun y => ⟨y.1 ≫ a, by rw [Category.assoc, h.w, reassoc_of% y.2]⟩
      invFun := fun y => ⟨h.lift y.1 x y.2, h.lift_snd _ _ _⟩
      left_inv := fun y => Subtype.ext (h.hom_ext (h.lift_fst _ _ _) (by rw [h.lift_snd, y.2]))
      right_inv := fun y => Subtype.ext (h.lift_fst _ _ _) }

end UpperTheory.Gal.Mod.HopfOperations

open UpperTheory.Gal.Mod.HopfOperations in
theorem UpperTheory.Gal.Mod.hopOp :
    GalEx → CorrOpEq → HopOp := by
  intro hGal hOp l _ k _ H Ω _ _ hlΩ g d hd
  obtain ⟨hF, hE, hcard⟩ := hd
  haveI := hF
  haveI := hE
  have hpb : IsPullback (pullback.fst (H.s g ≫ H.q) (sp (algebraMap k Ω))) (H.sΩ Ω g) (H.s g)
      (pullback.fst H.q (sp (algebraMap k Ω))) := gm_pb Ω H.q (H.s g)
  haveI hsF : IsFinite (H.sΩ Ω g) := fin_of_pb hpb
  haveI hsE : Etale (H.sΩ Ω g) := et_of_pb hpb
  have hFEt : FEt (H.sΩ Ω g) d :=
    ⟨hsF, hsE, fun K _ _ x => (card_pb hpb x).trans (hcard K _)⟩
  have hlZ : IsUnit (l : Γ(H.geomZ Ω, ⊤)) :=
    isUnit_nat (pullback.snd H.q (sp (algebraMap k Ω))) l hlΩ.ne_zero
  obtain ⟨W, c, G, iG, fG, a, σ, hG, hs⟩ := hGal (H.sΩ Ω g) d hFEt
  obtain ⟨hσ, hiso⟩ := id hs
  have hsplit := fun n : ℤ => TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2 l n 0 (H.sΩ Ω g) hlZ W c d σ hσ hiso
  let T : Htot l (sch.obj (H.geomZ Ω)) →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ Ω)) :=
    DirectSum.lmap fun n : ℤ => trHQ l (H.sΩ Ω g) (Wt.const _ 1) n 0 ∘ₗ pullHQ l (sch.map (H.tΩ Ω g)) n 0
  have hcomp : pullTot l (sch.map c) ∘ₗ T = ∑ j, pullTot l (sch.map (σ j ≫ H.tΩ Ω g)) := by
    refine DirectSum.linearMap_ext _ fun n => LinearMap.ext fun y => ?_
    have h1 := LinearMap.congr_fun (hsplit n) (pullHQ l (sch.map (H.tΩ Ω g)) n 0 y)
    simp only [LinearMap.comp_apply, LinearMap.sum_apply] at h1 ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [T, pullTot, DirectSum.lmap_lof, LinearMap.comp_apply, h1, map_sum, Functor.map_comp, pullQ_comp,
      LinearMap.sum_apply]
  have hT : IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T :=
    ⟨W, c, G, iG, fG, a, Fin d, inferInstance, σ, hG, hs, fun x => by
      rw [← LinearMap.sum_apply, ← hcomp]; rfl⟩
  let cc : TranscendenceTraces.Corr (H.geomZ Ω) (H.geomZ Ω) :=
    ⟨_, H.sΩ Ω g, H.tΩ Ω g, Wt.const _ 1, inferInstance, isWt_one _⟩
  haveI : Etale cc.p := hsE
  have hex : ∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T := ⟨T, hT⟩
  have e1 := hOp l cc rfl hlZ T hT
  have e2 := hOp l cc rfl hlZ _ hex.choose_spec
  have hh : hop l H Ω g = hex.choose := by unfold hop; rw [dite_eq_left hex]
  rw [hh, e2]
  exact e1.symm
end
