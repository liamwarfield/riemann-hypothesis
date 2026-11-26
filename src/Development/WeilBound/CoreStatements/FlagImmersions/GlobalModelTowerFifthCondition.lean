module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatUnitOfSplitRootLines
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HasReferenceOfSandwichAllPrimes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI5OfFibreInput
public import Development.WeilBound.CoreStatements.AmpleLineBundles.ExistsPointsOverNumberFields

@[expose] public section

attribute [-instance] GlobalTheory.CompHt.fintypePsi

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerIntersectionOfSandwichSplit
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI6OfReference
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointHeight
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointHeight
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.PointCurve

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar.Small
open GroundTheory.Heights₂.Heights (Coord blockIdx Cone BlockNonzero coordField coordVec flatCone projPts orbitIdeal
  map_ringEquiv_injective mem_map_ringEquiv_iff minimalPrimes_map_ringEquiv isPrime_map_ringEquiv_iff
  length_int_quotient_map length_localizedModule_quotient_map)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : K → ℕ}

abbrev sig (e : ∀ k, ι k ≃ Fin (n k + 1)) : (Σ k, ι k) ≃ Coord n := Equiv.sigmaCongrRight e

abbrev ren (e : ∀ k, ι k ≃ Fin (n k + 1)) : MRing ι ≃+* MRing (blockIdx n) :=
  (renameEquiv ℤ (sig e)).toRingEquiv

def pushLine (e : ∀ k, ι k ≃ Fin (n k + 1)) (A : HermLine ι) : HermLine (blockIdx n) where
  a := A.a
  h z := A.h (z ∘ sig e)
  pos z hz := A.pos _ fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact ⟨(e k).symm i, by simpa [Function.comp, sig] using hi⟩
  smul c z hc := A.smul c (z ∘ sig e) hc

theorem ren_X (e : ∀ k, ι k ≃ Fin (n k + 1)) (k : K) (i : ι k) :
    ren e (X ⟨k, i⟩) = (X ⟨k, e k i⟩ : MRing (blockIdx n)) := by
  show rename (sig e) (X ⟨k, i⟩) = _
  rw [rename_X]
  rfl

theorem ren_C (e : ∀ k, ι k ≃ Fin (n k + 1)) (a : ℤ) :
    ren e (C a) = (C a : MRing (blockIdx n)) := by
  show rename (sig e) (C a) = _
  rw [rename_C]

theorem eval_ren (e : ∀ k, ι k ≃ Fin (n k + 1)) (z : Coord n → ℂ) (g : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (ren e g)) = eval (z ∘ sig e) (map (Int.castRingHom ℂ) g) := by
  show eval z (map _ (rename (sig e) g)) = _
  rw [map_rename, eval_rename]

theorem isRelevant_map_iff (e : ∀ k, ι k ≃ Fin (n k + 1)) (V : Ideal (MRing ι)) :
    IsRelevant (V.map (ren e)) ↔ IsRelevant V := by
  constructor
  · intro h k
    obtain ⟨i, hi⟩ := h k
    refine ⟨(e k).symm i, fun hm => hi ?_⟩
    have := (mem_map_ringEquiv_iff (ren e) V _).2 hm
    rwa [ren_X, Equiv.apply_symm_apply] at this
  · intro h k
    obtain ⟨i, hi⟩ := h k
    refine ⟨e k i, fun hm => hi ?_⟩
    rw [← ren_X] at hm
    exact (mem_map_ringEquiv_iff (ren e) V _).1 hm

theorem comap_C_map (e : ∀ k, ι k ≃ Fin (n k + 1)) (V : Ideal (MRing ι)) :
    (V.map (ren e)).comap (C : ℤ →+* MRing (blockIdx n)) = V.comap (C : ℤ →+* MRing ι) := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap, ← mem_map_ringEquiv_iff (ren e) V, ren_C]

theorem isHorizontal_map_iff (e : ∀ k, ι k ≃ Fin (n k + 1)) (V : Ideal (MRing ι)) :
    IsHorizontal (V.map (ren e)) ↔ IsHorizontal V := by
  unfold IsHorizontal
  rw [comap_C_map]

theorem charOf_map (e : ∀ k, ι k ≃ Fin (n k + 1)) (V : Ideal (MRing ι)) :
    charOf (V.map (ren e)) = charOf V := by
  simp only [charOf, comap_C_map]

theorem divSupp_map (e : ∀ k, ι k ≃ Fin (n k + 1)) (V : Ideal (MRing ι)) (s : MRing ι) :
    divSupp (V.map (ren e)) (ren e s) = Ideal.map (ren e) '' divSupp V s := by
  have hsup : V.map (ren e) ⊔ Ideal.span {ren e s} = (V ⊔ Ideal.span {s}).map (ren e) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  ext W'
  simp only [divSupp, Set.mem_ofPred_eq, Set.mem_image, hsup, minimalPrimes_map_ringEquiv]
  constructor
  · rintro ⟨⟨W, hW, rfl⟩, hrel⟩
    exact ⟨W, ⟨hW, (isRelevant_map_iff e W).1 hrel⟩, rfl⟩
  · rintro ⟨W, ⟨hW, hrel⟩, rfl⟩
    exact ⟨⟨W, hW, rfl⟩, (isRelevant_map_iff e W).2 hrel⟩

theorem multAt_map (e : ∀ k, ι k ≃ Fin (n k + 1)) (J V : Ideal (MRing ι)) :
    multAt (J.map (ren e)) (V.map (ren e)) = multAt J V := by
  unfold multAt
  by_cases hV : V.IsPrime
  · have hV' : (V.map (ren e)).IsPrime := (isPrime_map_ringEquiv_iff (ren e) V).2 hV
    rw [dif_pos hV, dif_pos hV']
    exact congrArg ENat.toNat (length_localizedModule_quotient_map (ren e) J V)
  · have hV' : ¬ (V.map (ren e)).IsPrime := fun h' => hV ((isPrime_map_ringEquiv_iff (ren e) V).1 h')
    rw [dite_eq_right hV, dite_eq_right hV']

theorem length_chart_map (e : ∀ k, ι k ≃ Fin (n k + 1)) (V : Ideal (MRing ι)) (c : ∀ k, ι k) :
    Module.length ℤ (MRing (blockIdx n) ⧸ (V.map (ren e) ⊔
        Ideal.span (Set.range fun k => (X ⟨k, e k (c k)⟩ : MRing (blockIdx n)) - 1))) =
      Module.length ℤ (MRing ι ⧸ (V ⊔ Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing ι) - 1))) := by
  have h : V.map (ren e) ⊔ Ideal.span (Set.range fun k => (X ⟨k, e k (c k)⟩ : MRing (blockIdx n)) - 1) =
      (V ⊔ Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing ι) - 1)).map (ren e) := by
    rw [Ideal.map_sup, Ideal.map_span, ← Set.range_comp]
    congr 3
    funext k
    simp only [Function.comp_apply, map_sub, map_one, ren_X]
  rw [h]
  exact length_int_quotient_map (ren e) _

theorem geoNum_map (e : ∀ k, ι k ≃ Fin (n k + 1)) (V : Ideal (MRing ι)) (hV : IsRelevant V)
    (hD : ∀ c c' : ∀ k, Fin (n k + 1), (∀ k, (X ⟨k, c k⟩ : MRing (blockIdx n)) ∉ V.map (ren e)) →
      (∀ k, (X ⟨k, c' k⟩ : MRing (blockIdx n)) ∉ V.map (ren e)) →
      Nonempty ((MRing (blockIdx n) ⧸ (V.map (ren e) ⊔
          Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing (blockIdx n)) - 1))) ≃+*
        (MRing (blockIdx n) ⧸ (V.map (ren e) ⊔
          Ideal.span (Set.range fun k => (X ⟨k, c' k⟩ : MRing (blockIdx n)) - 1)))))
    (b : Fin 0 → K → ℤ) (b' : Fin 0 → K → ℤ) :
    geoNum (ι := blockIdx n) 0 (V.map (ren e)) b' = geoNum 0 V b := by
  have hV' := (isRelevant_map_iff e V).2 hV
  simp only [geoNum, dif_pos hV, dif_pos hV']
  have hc : ∀ k, (X ⟨k, e k (hV k).choose⟩ : MRing (blockIdx n)) ∉ V.map (ren e) := fun k hm => by
    rw [← ren_X] at hm
    exact (hV k).choose_spec ((mem_map_ringEquiv_iff (ren e) V _).1 hm)
  obtain ⟨φ⟩ := hD (fun k => (hV' k).choose) (fun k => e k (hV k).choose)
    (fun k => (hV' k).choose_spec) hc
  rw [← length_chart_map e V fun k => (hV k).choose, φ.toAddEquiv.toIntLinearEquiv.length_eq]

def ptsEquiv (e : ∀ k, ι k ≃ Fin (n k + 1)) (P : Ideal (MRing ι)) :
    mcPts P ≃ mcPts (P.map (ren e)) where
  toFun z := ⟨z.1 ∘ (sig e).symm, fun k => by
      obtain ⟨i, hi⟩ := z.2.1 k
      exact ⟨e k i, by
        show z.1 ((sig e).symm (sig e ⟨k, i⟩)) ≠ 0
        rwa [Equiv.symm_apply_apply]⟩, fun f hf => by
      obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_of_equiv (ren e) f).1 hf
      rw [eval_ren]
      have : (z.1 ∘ (sig e).symm) ∘ sig e = z.1 := by
        funext p
        exact congrArg z.1 ((sig e).symm_apply_apply p)
      rw [this]
      exact z.2.2 g hg⟩
  invFun z := ⟨z.1 ∘ sig e, fun k => by
      obtain ⟨i, hi⟩ := z.2.1 k
      exact ⟨(e k).symm i, by simpa [Function.comp, sig] using hi⟩, fun f hf => by
      rw [← eval_ren]
      exact z.2.2 _ (Ideal.mem_map_of_equiv (ren e) _ |>.2 ⟨f, hf, rfl⟩)⟩
  left_inv z := by
    ext p
    exact congrArg z.1 ((sig e).symm_apply_apply p)
  right_inv z := by
    ext p
    exact congrArg z.1 ((sig e).apply_symm_apply p)

theorem rel_iff (e : ∀ k, ι k ≃ Fin (n k + 1)) (P : Ideal (MRing ι)) (z z' : mcPts P) :
    (∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ (z' : (Σ k, ι k) → ℂ) = fun p => c p.1 * (z : (Σ k, ι k) → ℂ) p) ↔
      ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ ((ptsEquiv e P z' : mcPts (P.map (ren e))) : Coord n → ℂ) =
        fun p => c p.1 * ((ptsEquiv e P z : mcPts (P.map (ren e))) : Coord n → ℂ) p := by
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    funext p
    show z'.1 ((sig e).symm p) = c p.1 * z.1 ((sig e).symm p)
    rw [h]
    rfl
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    funext p
    have := congrFun h (sig e p)
    have h1 : ∀ y : mcPts P, ((ptsEquiv e P y : mcPts (P.map (ren e))) : Coord n → ℂ) (sig e p) = y.1 p :=
      fun y => congrArg y.1 ((sig e).symm_apply_apply p)
    rw [h1, h1] at this
    exact this

def projEquiv (e : ∀ k, ι k ≃ Fin (n k + 1)) (P : Ideal (MRing ι)) :
    projPts P ≃ projPts (P.map (ren e)) :=
  Quot.congr (ptsEquiv e P) fun z z' => rel_iff e P z z'

theorem degC_map (e : ∀ k, ι k ≃ Fin (n k + 1)) (P : Ideal (MRing ι)) :
    degC (P.map (ren e)) = degC P :=
  (Nat.card_congr (projEquiv e P)).symm

theorem arInt_map (e : ∀ k, ι k ≃ Fin (n k + 1)) {P : Ideal (MRing ι)} (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P 1)
    (hP' : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (P.map (ren e)) 1) {A : HermLine ι} {B : HermLine (blockIdx n)} {s : MRing ι}
    {a : K → ℕ} (hAa : ∀ k, A.a k = a k) (hBa : ∀ k, B.a k = a k) (hs : IsMultiHomog s a)
    (hB : ∀ z ∈ mcPts (P.map (ren e)), B.h z = A.h (z ∘ sig e)) :
    arInt (P.map (ren e)) (ren e s) B (Fin.elim0 : Fin 0 → HermLine (blockIdx n)) =
      arInt P s A (Fin.elim0 : Fin 0 → HermLine ι) := by
  have hs' : IsMultiHomog (ren e s) a :=
    GroundTheory.Heights₂.Heights.LowerBoundFree.FlZArithVar.isMultiHomog_rename_sigma e hs
  rw [GroundTheory.Heights₂.Heights.Targets.CurveRationalSectionSum.arInt_eq_sum hP hAa hs,
    GroundTheory.Heights₂.Heights.Targets.CurveRationalSectionSum.arInt_eq_sum hP' hBa hs']
  let F : projPts P → ℝ := Quot.lift (fun z : mcPts P => logNorm A s z.1) (by
    rintro z z' ⟨c, hc, h⟩
    show logNorm A s z.1 = logNorm A s z'.1
    rw [h]
    exact (GroundTheory.Heights₂.Heights.Targets.CurveRationalSectionSum.logNorm_smul hAa hs c z.1 hc).symm)
  let F' : projPts (P.map (ren e)) → ℝ :=
    Quot.lift (fun z : mcPts (P.map (ren e)) => logNorm B (ren e s) z.1) (by
    rintro z z' ⟨c, hc, h⟩
    show logNorm B (ren e s) z.1 = logNorm B (ren e s) z'.1
    rw [h]
    exact (GroundTheory.Heights₂.Heights.Targets.CurveRationalSectionSum.logNorm_smul hBa hs' c z.1 hc).symm)
  have hF : ∀ q, logNorm A s (Quot.out q : mcPts P).1 = F q := fun q => by
    conv_rhs => rw [← Quot.out_eq q]
  have hF' : ∀ q, logNorm B (ren e s) (Quot.out q : mcPts (P.map (ren e))).1 = F' q := fun q => by
    conv_rhs => rw [← Quot.out_eq q]
  simp only [hF, hF']
  rw [← finsum_comp_equiv (projEquiv e P)]
  refine finsum_congr fun q => ?_
  induction q using Quot.ind with
  | mk z =>
    show logNorm B (ren e s) (ptsEquiv e P z).1 = logNorm A s z.1
    have hz : (ptsEquiv e P z).1 ∘ sig e = z.1 := by
      funext p
      exact congrArg z.1 ((sig e).symm_apply_apply p)
    unfold logNorm
    rw [hB _ (ptsEquiv e P z).2, eval_ren, hz]

theorem mConeMap_ren {Ω : Type} [Field Ω] (e : ∀ k, ι k ≃ Fin (n k + 1)) (y : Coord n → Ω) (f : MRing ι) :
    mConeMap (ι := blockIdx n) y (ren e f) = mConeMap (y ∘ sig e) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap, ren_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, hp]
    obtain ⟨k, i⟩ := q
    rw [ren_X]
    simp only [mConeMap, aeval_X]
    rfl

theorem mCoordIdeal_ren {Ω : Type} [Field Ω] (e : ∀ k, ι k ≃ Fin (n k + 1)) (y : Coord n → Ω) :
    (mCoordIdeal (y ∘ sig e)).map (ren e) = mCoordIdeal (ι := blockIdx n) y := by
  have h : mCoordIdeal (y ∘ sig e) = (mCoordIdeal (ι := blockIdx n) y).comap (ren e) := by
    ext f
    simp only [mCoordIdeal, RingHom.mem_ker, Ideal.mem_comap, mConeMap_ren]
  rw [h]
  exact Ideal.map_comap_of_surjective _ (ren e).surjective _

theorem mCoordIdeal_ringHom {L Ω : Type} [Field L] [Field Ω] (j : L →+* Ω) (w : (Σ k, ι k) → L) :
    mCoordIdeal (fun p => j (w p)) = mCoordIdeal w := by
  have key : ∀ f : MRing ι, mConeMap (fun p => j (w p)) f = MvPolynomial.map j (mConeMap w f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p q hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [mConeMap]
  ext f
  simp only [mCoordIdeal, RingHom.mem_ker, key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective j j.injective)

theorem lineHt_tensor (A B : HermLine ι) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    lineHt (A.tensor B) L w = lineHt A L w + lineHt B L w := by
  have hx : ∀ k, (fun i => w ⟨k, i⟩) ≠ 0 := fun k => Function.ne_iff.mpr (hw k)
  have hfin : ∀ C : K → ℝ, ∑ᶠ v : FinitePlace L, ∑ k, C k * Real.log (⨆ i, v (w ⟨k, i⟩)) =
      ∑ k, C k * ∑ᶠ v : FinitePlace L, Real.log (⨆ i, v (w ⟨k, i⟩)) := fun C =>
    GroundTheory.Heights₂.Heights.finsum_sum_mul _ _
      fun k => GroundTheory.Heights₂.Heights.support_log_iSup_place_finite (hx k)
  have harch : ∀ σ : L →+* ℂ, Real.log ((A.tensor B).h fun p => σ (w p)) =
      Real.log (A.h fun p => σ (w p)) + Real.log (B.h fun p => σ (w p)) := fun σ => by
    have hσ : ∀ k, ∃ i, (fun p => σ (w p)) ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hw k
      exact ⟨i, (map_ne_zero _).mpr hi⟩
    exact Real.log_mul (A.pos _ hσ).ne' (B.pos _ hσ).ne'
  unfold lineHt ptHt
  rw [hfin, hfin, hfin, Finset.sum_congr rfl fun σ _ => harch σ, Finset.sum_add_distrib]
  simp only [HermLine.tensor, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]
  ring

theorem isSmoothHerm_pushLine (e : ∀ k, ι k ≃ Fin (n k + 1)) {A : HermLine ι} (hA : IsSmoothHerm A) :
    IsSmoothHerm (pushLine e A) := by
  have hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Coord n → ℂ => z ∘ sig e) :=
    contDiff_pi.2 fun p => contDiff_apply ℝ (fun _ => ℂ) (sig e p)
  have h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A.h ∘ fun z : Coord n → ℂ => z ∘ sig e)
      {z : Coord n → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    refine ContDiffOn.comp hA hu.contDiffOn fun z hz k => ?_
    obtain ⟨i, hi⟩ := hz k
    exact ⟨(e k).symm i, by
      show z (sig e ⟨k, (e k).symm i⟩) ≠ 0
      simpa [sig] using hi⟩
  exact h

theorem height_eq_lineHt (e : ∀ k, ι k ≃ Fin (n k + 1)) (A : GroundTheory.Heights₂.Heights.HermLine n) (B : HermLine ι)
    (hBa : ∀ k, B.a k = A.deg k)
    (hBh : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      B.h z = A.metric fun k i => z ⟨k, (e k).symm i⟩)
    (L : Type) [Field L] [NumberField L] (j : L →+* AlgebraicClosure ℚ) (w : (Σ k, ι k) → L)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (x : Cone n (AlgebraicClosure ℚ))
    (hx : ∀ k i, x k i = j (w ⟨k, (e k).symm i⟩)) :
    GroundTheory.Heights₂.Heights.height A x = lineHt B L w := by
  let jA : L →ₐ[ℚ] AlgebraicClosure ℚ := j.toRatAlgHom
  have hle : coordField x ≤ jA.fieldRange := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    exact ⟨w ⟨k, (e k).symm i⟩, (hx k i).symm⟩
  let E : L ≃ₐ[ℚ] jA.fieldRange := AlgEquiv.ofInjectiveField jA
  let e0 : coordField x →+* L :=
    (E.symm.toAlgHom.comp (IntermediateField.inclusion hle)).toRingHom
  let w' : (Σ k, ι k) → coordField x := fun p => coordVec x p.1 (e p.1 p.2)
  have hw' : ∀ p, e0 (w' p) = w p := by
    rintro ⟨k, i⟩
    show E.symm (IntermediateField.inclusion hle (w' ⟨k, i⟩)) = _
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    show x k (e k i) = j (w ⟨k, i⟩)
    rw [hx, Equiv.symm_apply_apply]
  have hnz : ∀ k, ∃ i, w' ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hw k
    refine ⟨i, fun h => hi ?_⟩
    rw [← hw', h, map_zero]
  have hext := lineHt_map_scale K ι B (coordField x) L e0 w' (fun _ => 1) hnz fun _ => one_ne_zero
  simp only [one_mul, hw'] at hext
  have hfun : (fun p => w p) = w := rfl
  rw [hfun] at hext
  rw [hext]
  unfold lineHt ptHt GroundTheory.Heights₂.Heights.height
  congr 2
  · refine finsum_congr fun v => Finset.sum_congr rfl fun k _ => ?_
    beta_reduce
    rw [hBa]
    congr 2
    exact ((e k).iSup_comp (g := fun i => v (coordVec x k i))).symm
  · refine Finset.sum_congr rfl fun σ _ => ?_
    have hσ : ∀ k, ∃ i, (fun p => σ (w' p)) ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hnz k
      exact ⟨i, (map_ne_zero _).mpr hi⟩
    beta_reduce
    rw [hBh (fun p => σ (w' p)) hσ]
    congr 2
    funext k i
    simp [w']

section Recursion

variable [DecidableEq K] [Nonempty K]

theorem recR_map (e : ∀ k, ι k ≃ Fin (n k + 1)) {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x)
    {W : Ideal (MRing ι)} (hW : W.map (ren e) = orbitIdeal x) (A : GroundTheory.Heights₂.Heights.HermLine n)
    (C : HermLine ι) (s : MRing ι) (hs : IsSectionOn (orbitIdeal x) A.toGeo (ren e s))
    (harch : arInt (W.map (ren e)) (ren e s) A.toGeo (Fin.elim0 : Fin 0 → HermLine (blockIdx n)) =
      arInt W s C (Fin.elim0 : Fin 0 → HermLine ι))
    (I : Ideal (MRing ι) → (m : ℕ) → (Fin m → HermLine ι) → ℝ)
    (I' : Ideal (MRing (blockIdx n)) → (m : ℕ) → (Fin m → HermLine (blockIdx n)) → ℝ) :
    recR I' (orbitIdeal x) (Fin.elim0 : Fin 0 → HermLine (blockIdx n)) A.toGeo (ren e s) =
      recR I W (Fin.elim0 : Fin 0 → HermLine ι) C s := by
  have hdeh := GroundTheory.Heights₂.Heights.OrbitChartDehom.proof GroundTheory.Heights₂.Heights.OrbitChartMax.proof
    GroundTheory.Heights₂.Heights.OrbitChartQuot.proof K n A x (ren e s) hx hs
  have hver := GroundTheory.Heights₂.Heights.OrbitDivVertical.proof K n A x (ren e s) hx hs
  rw [← hW] at hdeh hver ⊢
  unfold recR
  rw [harch]
  congr 1
  have hsup : W.map (ren e) ⊔ Ideal.span {ren e s} = (W ⊔ Ideal.span {s}).map (ren e) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rw [divSupp_map, finsum_mem_image (map_ringEquiv_injective (ren e)).injOn]
  refine finsum_mem_congr rfl fun V hV => ?_
  have hV' : V.map (ren e) ∈ divSupp (W.map (ren e)) (ren e s) := by
    rw [divSupp_map]
    exact ⟨V, hV, rfl⟩
  have hnh := hver _ hV'
  have hnh' : ¬ IsHorizontal V := fun h => hnh ((isHorizontal_map_iff e V).2 h)
  rw [if_neg hnh, if_neg hnh', hsup, multAt_map, charOf_map,
    geoNum_map e V hV.2 (fun c c' h1 h2 => (hdeh _ hV' c c' h1 h2).2)]

end Recursion

theorem heightRecR : GroundTheory.Heights₂.Heights.HeightRecR.Statement := by
  open GroundTheory.Heights₂.Heights in
  have hM : OrbitChartMax.Statement := OrbitChartMax.proof
  open GroundTheory.Heights₂.Heights in
  have hQ : OrbitChartQuot.Statement := OrbitChartQuot.proof
  open GroundTheory.Heights₂.Heights in
  have hIff : OrbitCenterMemIff.Statement := OrbitCenterMemIff.proof
  open GroundTheory.Heights₂.Heights in
  exact HeightRecR.proof OrbitDivVertical.proof
    (OrbitFiniteSum.proof OrbitDegreeRatio.proof
      (OrbitLocalSum.proof OrbitChartRing.proof hM (OrbitChartResidue.proof hM hQ (OrbitChartDehom.proof hM hQ))
        OrbitChartMult.proof
        (LocalLengthPlaces.proof LocalQuotCard.proof CentredPlacesFinite.proof
          (LocalQuotCentred.proof CentredRingNormal.proof LocalNormalIndex.proof) PlacesRingQuot.proof)
        OrbitCenterChart.proof PlaceCentredSum.proof OrbitChartTerm.proof)
      (OrbitCenterZero.proof OrbitCenterLe.proof hIff
        (OrbitCenterDivSupp.proof hIff (OrbitCenterPrime.proof hIff) SubringPrimeMaximal.proof)))
    (OrbitArchSum.of_conjSum OrbitConjSum.proof)

theorem mem_mCoordIdeal_iff {Ω : Type} [Field Ω] (w : (Σ k, ι k) → Ω) (f : MRing ι) (a : K → ℕ)
    (hf : IsMultiHomog f a) : f ∈ mCoordIdeal w ↔ aeval w f = 0 := by
  rw [GroundTheory.Heights₂.Heights.Inter.mCoordIdeal_eq_ker_multiConeMap]
  exact not_iff_not.mp (by
    simpa using GroundTheory.Heights₂.Heights.Inter.DiagRAux.not_mem_ker_iff_aeval_ne w f a hf)

theorem ren_symm_homog (e : ∀ k, ι k ≃ Fin (n k + 1)) {g : MRing (blockIdx n)} {a : K → ℕ}
    (hg : IsMultiHomog g a) : IsMultiHomog ((ren e).symm g) a := by
  have h : (ren e).symm g = rename (Equiv.sigmaCongrRight fun k => (e k).symm) g := by
    show (renameEquiv ℤ (sig e)).symm g = _
    rw [renameEquiv_symm, Equiv.sigmaCongrRight_symm]
    rfl
  rw [h]
  exact GroundTheory.Heights₂.Heights.LowerBoundFree.FlZArithVar.isMultiHomog_rename_sigma (fun k => (e k).symm) hg

end GlobalTheory.CompanionTheory.Ar.Ht.PointCurve

namespace GlobalTheory.CompanionTheory.Ar.Ht

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
open GroundTheory.Heights₂.Heights (Cone BlockNonzero flatCone orbitIdeal blockIdx chartMonomial)
open GlobalTheory.CompanionTheory.Ar.Ht.PointCurve

theorem pointCurve_height : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem), IsIntersectionSystem II → ∀ (P : Ideal (MRing ι)) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P d → ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L P, ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal w) 1 ∧ P ≤ mCoordIdeal w ∧ (∀ f : MRing ι, (∃ a, IsMultiHomog f a) → (f ∈ mCoordIdeal w ↔ aeval w f = 0)) ∧ ∀ A : HermLine ι, IsSmoothHerm A → II K ι (mCoordIdeal w) 1 ![A] / (degC (mCoordIdeal w) : ℝ) = lineHt A L w := by
  intro K _ ι _ II hII P d hP L _ _ w hw
  classical
  obtain ⟨hwb, hwP⟩ := hw
  haveI : Nonempty K := hP.1
  have hne : ∀ k, Nonempty (ι k) := fun k => (hwb k).elim fun i _ => ⟨i⟩
  let n : K → ℕ := fun k => Fintype.card (ι k) - 1
  have hcard : ∀ k, Fintype.card (ι k) = n k + 1 := fun k => by
    have := @Fintype.card_pos (ι k) _ (hne k)
    simp only [n]
    omega
  let e : ∀ k, ι k ≃ Fin (n k + 1) := fun k => Fintype.equivFinOfCardEq (hcard k)
  let j : L →+* AlgebraicClosure ℚ := (IsAlgClosed.lift : L →ₐ[ℚ] AlgebraicClosure ℚ).toRingHom
  let x : Cone n (AlgebraicClosure ℚ) := fun k i => j (w ⟨k, (e k).symm i⟩)
  have hx : BlockNonzero x := fun k h => by
    obtain ⟨i, hi⟩ := hwb k
    have h0 : j (w ⟨k, (e k).symm (e k i)⟩) = 0 := congrFun h (e k i)
    rw [Equiv.symm_apply_apply, map_eq_zero] at h0
    exact hi h0
  have hWW : (mCoordIdeal w).map (ren e) = orbitIdeal x := by
    have h1 : (flatCone x) ∘ sig e = fun p => j (w p) := by
      funext p
      exact congrArg (fun q => j (w q)) ((sig e).symm_apply_apply p)
    rw [orbitIdeal, ← mCoordIdeal_ren e, h1, mCoordIdeal_ringHom]
  have hcurve' : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ι := blockIdx n) (orbitIdeal x) 1 :=
    GroundTheory.Heights₂.Heights.OrbitCurve.full K n x hx
  have hcurve : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal w) 1 := by
    have h := GroundTheory.Heights₂.Heights.LowerBoundFree.FlZArithVar.isArithVar_comap_rename_sigma e hcurve'
    have h2 : (orbitIdeal x).comap (rename (Equiv.sigmaCongrRight e) : MRing ι →ₐ[ℤ] MRing (blockIdx n)) =
        mCoordIdeal w := by
      rw [← hWW]
      exact Ideal.comap_map_of_bijective (ren e) (ren e).bijective
    rwa [h2] at h
  have hcurve'' : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar ((mCoordIdeal w).map (ren e)) 1 := hWW ▸ hcurve'
  have hdeg : 0 < degC (mCoordIdeal w) := by
    rw [← degC_map e, hWW]
    exact GroundTheory.Heights₂.Heights.OrbitDegree.full K n x hx
  have key : ∀ (C : HermLine ι) (d : K → ℕ), IsSmoothHerm C → (∀ k, C.a k = d k) →
      II K ι (mCoordIdeal w) (0 + 1) (Fin.snoc (Fin.elim0 : Fin 0 → HermLine ι) C) =
        degC (mCoordIdeal w) * lineHt C L w := by
    intro C d hC hd
    let A' : GroundTheory.Heights₂.Heights.HermLine n :=
      GroundTheory.Heights₂.Heights.HermLine.ofGeo (pushLine e C) (isSmoothHerm_pushLine e hC)
    obtain ⟨c, hc⟩ := GroundTheory.Heights₂.Heights.exists_chart hx
    have hdA : ∀ k, A'.deg k = d k := hd
    have hren : ren e ((ren e).symm (chartMonomial c d)) = chartMonomial c d := (ren e).apply_symm_apply _
    have hsec : IsSectionOn (orbitIdeal x) A'.toGeo (ren e ((ren e).symm (chartMonomial c d))) := by
      rw [hren]
      exact GroundTheory.Heights₂.Heights.isSectionOn_chartMonomial A' x c hc d hdA
    have hsd : IsMultiHomog ((ren e).symm (chartMonomial c d)) d :=
      ren_symm_homog e ((GroundTheory.Heights₂.Heights.geoMultiHomog_iff _ d).mpr
        (GroundTheory.Heights₂.Heights.isWeightedHomogeneous_chartMonomial c d))
    have hsW : (ren e).symm (chartMonomial c d) ∉ mCoordIdeal w := fun h =>
      GroundTheory.Heights₂.Heights.chartMonomial_notMem_orbitIdeal x c hc d (by
        rw [← hren, ← hWW]
        exact Ideal.mem_map_of_mem _ h)
    obtain ⟨-, -, hR⟩ := hII K ι
    have h1 := hR (mCoordIdeal w) 0 Fin.elim0 C _ d hcurve (fun j => j.elim0) hC hd hsd hsW
    have harch := arInt_map e hcurve hcurve'' (B := A'.toGeo) hd hd hsd fun z hz => by
      have hzb : BlockNonzero (GroundTheory.Heights₂.Heights.unflatCone z) :=
        (GroundTheory.Heights₂.Heights.blockNonzero_unflatCone_iff z).mpr hz.1
      exact GroundTheory.Heights₂.Heights.HermLine.toGeo_ofGeo_h _ _ hzb
    have h2 := recR_map e hx hWW A' C _ hsec harch (II K ι) fun _ _ _ => 0
    have h3 := heightRecR K n (fun _ _ _ => 0) A' x _ hx hsec
    have h4 := height_eq_lineHt e A' C (fun _ => rfl) (fun z _ => by
      show C.h z = C.h _
      congr 1
      funext p
      exact congrArg z ((sig e).symm_apply_apply p).symm) L j w hwb x fun _ _ => rfl
    have h5 := degC_map e (mCoordIdeal w)
    rw [h1, ← h2, h3, ← hWW, h5, h4]
  have hsnoc : ∀ B : HermLine ι, (Fin.snoc (Fin.elim0 : Fin 0 → HermLine ι) B : Fin 1 → _) = ![B] := by
    intro B
    funext i
    fin_cases i
    rfl
  refine ⟨hcurve, ?_, ?_, ?_⟩
  · obtain ⟨S, hS, hPS⟩ := hP.2.1.2.1
    rw [hPS, Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    exact (mem_mCoordIdeal_iff w f a ha).2 (hwP f (hPS ▸ Ideal.subset_span hf))
  · rintro f ⟨a, ha⟩
    exact mem_mCoordIdeal_iff w f a ha
  · intro A hA
    let m : K → ℕ := fun k => (A.a k).natAbs
    have hS := isSmoothHerm_sqMetric (ι := ι) m
    have hAS := key (A.tensor (HermLine.sqMetric m)) (fun k => (A.a k + m k).toNat)
      (isSmoothHerm_tensor hA hS) fun k => by
        show A.a k + (m k : ℤ) = _
        simp only [m]
        omega
    have hSS := key (HermLine.sqMetric m) m hS fun _ => rfl
    obtain ⟨-, hAdd, -⟩ := hII K ι
    have hadd := hAdd (mCoordIdeal w) 0 Fin.elim0 A (HermLine.sqMetric m) hcurve (fun j => j.elim0) hA hS
    have hten := lineHt_tensor A (HermLine.sqMetric m) L w hwb
    rw [hAS, hSS, hsnoc A, hten] at hadd
    have hpos : (0 : ℝ) < degC (mCoordIdeal w) := by exact_mod_cast hdeg
    rw [div_eq_iff hpos.ne']
    linarith

end GlobalTheory.CompanionTheory.Ar.Ht
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldPointHeightStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.number_field_point_height : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem), IsIntersectionSystem II → ∀ (P : Ideal (MRing ι)) (d : ℕ), IsArithVar P d → ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L P, IsArithVar (mCoordIdeal w) 1 ∧ P ≤ mCoordIdeal w ∧ (∀ f : MRing ι, (∃ a, IsMultiHomog f a) → (f ∈ mCoordIdeal w ↔ aeval w f = 0)) ∧ ∀ A : HermLine ι, IsSmoothHerm A → II K ι (mCoordIdeal w) 1 ![A] / (degC (mCoordIdeal w) : ℝ) = lineHt A L w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.pointCurve_height | exact GlobalTheory.CompanionTheory.Ar.Ht.pointCurve_height | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.pointCurve_height <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsLift
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsLift
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.CoverDense

theorem preimage_dense : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (Q : (L : Type) → [Field L] → ((Σ k, R.ι k) → L) → Prop), (∀ f : MRing R.ι, (∃ a, IsMultiHomog f a) → f ∉ R.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L), ∃ w ∈ ptsOver L R.P, aeval w f ≠ 0 ∧ Q L w) → ∀ f : MRing M.ι, (∃ a, IsMultiHomog f a) → f ∉ M.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (w : (Σ k, R.ι k) → L), ∃ z ∈ ptsOver L' (mCoordIdeal (joinOf M R i)), w ∈ ptsOver L R.P ∧ Q L w ∧ (fun p => z (joinInr M.ι R.ι p)) = (fun p => e (w p)) ∧ aeval (fun p => z (joinInl M.ι R.ι p)) f ≠ 0 :=
  CoverDenseAlt.exists_points_over_number_fields

end GlobalTheory.CompanionTheory.Ar.CoverDense
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsLiftStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.join_model_points_lift : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (Q : (L : Type) → [Field L] → ((Σ k, R.ι k) → L) → Prop), (∀ f : MRing R.ι, (∃ a, IsMultiHomog f a) → f ∉ R.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L), ∃ w ∈ ptsOver L R.P, aeval w f ≠ 0 ∧ Q L w) → ∀ f : MRing M.ι, (∃ a, IsMultiHomog f a) → f ∉ M.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (w : (Σ k, R.ι k) → L), ∃ z ∈ ptsOver L' (mCoordIdeal (joinOf M R i)), w ∈ ptsOver L R.P ∧ Q L w ∧ (fun p => z (joinInr M.ι R.ι p)) = (fun p => e (w p)) ∧ aeval (fun p => z (joinInl M.ι R.ι p)) f ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoverDense.preimage_dense | exact GlobalTheory.CompanionTheory.Ar.CoverDense.preimage_dense | (intros; apply GlobalTheory.CompanionTheory.Ar.CoverDense.preimage_dense <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundedHeightPointsDense
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundedHeightPointsDense
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Dense0

theorem dense_bounded_lines : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P d → ∀ (J : Type) [Fintype J] (A : J → HermLine ι), (∀ j, IsSmoothHerm (A j)) → ∃ C : ℝ, ∀ f : MRing ι, (∃ a, IsMultiHomog f a) → f ∉ P → ∃ (L : Type) (_ : Field L) (_ : NumberField L), ∃ w ∈ ptsOver L P, aeval w f ≠ 0 ∧ ∀ j, |lineHt (A j) L w| ≤ C :=
  @CoverDenseAlt.exists_points_bounded_line_heights

end GlobalTheory.CompanionTheory.Ar.Dense0
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundedHeightPointsDenseStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_height_points_dense : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ), IsArithVar P d → ∀ (J : Type) [Fintype J] (A : J → HermLine ι), (∀ j, IsSmoothHerm (A j)) → ∃ C : ℝ, ∀ f : MRing ι, (∃ a, IsMultiHomog f a) → f ∉ P → ∃ (L : Type) (_ : Field L) (_ : NumberField L), ∃ w ∈ ptsOver L P, aeval w f ≠ 0 ∧ ∀ j, |lineHt (A j) L w| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Dense0.dense_bounded_lines | exact GlobalTheory.CompanionTheory.Ar.Dense0.dense_bounded_lines | (intros; apply GlobalTheory.CompanionTheory.Ar.Dense0.dense_bounded_lines <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI6OfReference
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.UpperTower

theorem proj_inl_mem {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
    [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] {Ω : Type} [Field Ω] (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω)
    {L : Type} [Field L] {z : (Σ k, joinIdx ι₁ ι₂ k) → L} (hz : z ∈ ptsOver L (mCoordIdeal (joinVec y₁ y₂))) :
    (fun p => z (joinInl ι₁ ι₂ p)) ∈ ptsOver L (mCoordIdeal y₁) := by
  refine ⟨fun k => hz.1 (Sum.inl k), fun f hf => ?_⟩
  have key : ∀ g : MRing ι₁, mConeMap (joinVec y₁ y₂) (rename (joinInl ι₁ ι₂) g) =
      rename (Sum.inl : K₁ → K₁ ⊕ K₂) (mConeMap y₁ g) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp only [mConeMap, aeval_X, map_mul, rename_C, rename_X]
      rfl
  have hmem : rename (joinInl ι₁ ι₂) f ∈ mCoordIdeal (joinVec y₁ y₂) := by
    have hf' : mConeMap y₁ f = 0 := hf
    change mConeMap (joinVec y₁ y₂) (rename (joinInl ι₁ ι₂) f) = 0
    rw [key, hf', map_zero]
  have h := hz.2 _ hmem
  rw [aeval_rename] at h
  exact h

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem weightAbsEntrySum_nonneg (mu : Wt Ψ N) : 0 ≤ l1 mu :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem l1_le_card_mul_norm (mu : Wt Ψ N) (h : ‖mu‖ ≤ 2) : l1 mu ≤ (Fintype.card Ψ : ℝ) * (N * 2) := by
  have h1 : ∀ τ i, |mu τ i| ≤ 2 := fun τ i =>
    ((norm_le_pi_norm (mu τ) i).trans (norm_le_pi_norm mu τ)).trans h
  calc l1 mu ≤ ∑ _τ : Ψ, ∑ _i : Fin N, (2 : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => h1 τ i
    _ = _ := by simp

theorem rootHt_le (R : RootModel Ψ N) (t : ℝ) (mu : Wt Ψ N) (s D : ℝ) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, R.ι k) → L) (hw : ∀ j, |lineHt (R.line t j) L w| ≤ D) :
    rootHt R t mu s L w ≤ (l1 mu + |s|) * D := by
  have hD : 0 ≤ D := (abs_nonneg _).trans (hw none)
  have h1 : ∀ j, R.coef mu s j * lineHt (R.line t j) L w ≤ |R.coef mu s j| * D := fun j =>
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hw j) (abs_nonneg _))
  refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hD
  rw [Fintype.sum_option, add_comm]
  refine add_le_add (le_of_eq ?_) ?_
  · simp [RootModel.coef, l1, Fintype.sum_prod_type]
  · have hk : (1 : ℝ) ≤ R.kA := by exact_mod_cast R.kA_pos
    simp only [RootModel.coef, abs_div, Nat.abs_cast]
    exact div_le_self (abs_nonneg _) hk

theorem line_smooth (R : RootModel Ψ N) (t : ℝ) : ∀ j, IsSmoothHerm (R.line t j)
  | some r => R.x_smooth t r
  | none => R.A_smooth

theorem tower_upper : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem)
    (R : T.Comp → RootModel Ψ N), IsIntersectionSystem II → HasRef T R → T.I6 II := by
  intro Ψ _ _ N T II R hII href c₀ hc₀
  obtain ⟨C, s₀, hs₀, href⟩ := href
  obtain ⟨θ₁, hθ₁, hθ₁1, hwt⟩ := GlobalTheory.T.dominant_weight_gap_shift Ψ N T.j T.nu c₀ T.j_pos T.j_lt hc₀
  choose D hD using fun c : T.Comp =>
    GlobalTheory.T.bounded_height_points_dense (R c).K (R c).ι (R c).P _ (R c).arith _ ((R c).line 1) (line_smooth (R c) 1)
  set D' : ℝ := ∑ c, |D c| with hD'
  have hDle : ∀ c, D c ≤ D' := fun c =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun c => |D c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c))
  have hD'0 : 0 ≤ D' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set Λ : ℝ := (Fintype.card Ψ : ℝ) * (N * 2) + 1 with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  refine ⟨min θ₁ s₀, lt_min hθ₁ hs₀, 2 * (Λ * D' + |C|) + Λ * |C|, ?_⟩
  intro B hB c lam θ s _ hlam hθ hθle hs hgap hcg
  have hθ1 : θ ≤ θ₁ := hθle.trans (min_le_left _ _)
  have hθs : θ ≤ s₀ := hθle.trans (min_le_right _ _)
  have hsθ : (s : ℝ) ≤ θ := by rw [hs]; nlinarith
  have hs0 : (0 : ℝ) < s := by rw [hs]; positivity
  obtain ⟨hdom, hnorm, -⟩ := hwt lam θ hlam hθ hθ1 hgap hcg
  rw [← hs] at hdom hnorm
  obtain ⟨i, u, hclose, harch⟩ := href B hB c
  have harch' := harch (T.lamS lam s) s hdom hnorm hs0 (hsθ.trans hθs)
  have hl : l1 (T.lamS lam s) + |(s : ℝ)| ≤ Λ := by
    rw [abs_of_pos hs0]
    exact add_le_add (l1_le_card_mul_norm _ hnorm) (by linarith)
  have hl0 : 0 ≤ l1 (T.lamS lam s) + |(s : ℝ)| := add_nonneg (weightAbsEntrySum_nonneg _) (abs_nonneg _)
  have hlog : 1 ≤ 2 * Real.log B := by
    have h2 : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) (by exact_mod_cast hB)
    have := Real.log_two_gt_d9
    linarith
  refine ⟨{W | (T.M B c).IsPt W ∧ T.mbarHt II B c lam s W ≤ (2 * (Λ * D' + |C|) + Λ * |C|) * Real.log B}, ?_,
    fun W hW => hW⟩
  intro f hf hfP
  obtain ⟨L, _, _, L', _, _, e, w, z, hz, hw, hQ, hze, hfz⟩ :=
    GlobalTheory.T.join_model_points_lift Ψ N (T.M B c) (R c) i
      (fun L _ w => ∀ _ : NumberField L, ∀ j, |lineHt ((R c).line 1 j) L w| ≤ D c)
      (fun g hg hgP => by
        obtain ⟨L, _, _, w, hw, hgw, hb⟩ := hD c g hg hgP
        exact ⟨L, inferInstance, inferInstance, w, hw, hgw, fun _ => hb⟩) f hf hfP
  have hz₁ : (fun p => z (joinInl (T.M B c).ι (R c).ι p)) ∈ ptsOver L' (T.M B c).P := proj_inl_mem _ _ hz
  obtain ⟨hA, hle, hmem, hht⟩ := GlobalTheory.T.number_field_point_height _ _ II hII _ _ (T.M B c).arith L' _ hz₁
  refine ⟨mCoordIdeal fun p => z (joinInl (T.M B c).ι (R c).ι p), ⟨⟨hA, hle⟩, ?_⟩, fun h => hfz ((hmem f hf).1 h)⟩
  have e1 : T.mbarHt II B c lam s (mCoordIdeal fun p => z (joinInl (T.M B c).ι (R c).ι p)) =
      rootHt (T.M B c) (scale s) (T.lamS lam s) s L' (fun p => z (joinInl (T.M B c).ι (R c).ι p)) := by
    simp only [RootTower.mbarHt, RootModel.ht, rootHt, Finset.sum_div, mul_div_assoc]
    exact Finset.sum_congr rfl fun j _ => by rw [hht _ (line_smooth _ _ j)]
  have hcl := (GlobalTheory.T.root_height_difference_bound Ψ N (T.M B c) (R c) i u _ _ _ _ _ _ hclose harch' L' z hz).2
  have hR : rootHt (R c) 1 (T.lamS lam s) s L' (fun p => z (joinInr (T.M B c).ι (R c).ι p)) ≤
      (l1 (T.lamS lam s) + |(s : ℝ)|) * D' := by
    refine rootHt_le _ _ _ _ _ _ _ fun j => ?_
    have h := GlobalTheory.T.line_height_invariant_scaling _ _ ((R c).line 1 j) L L' e w (fun _ => 1) hw.1 (fun _ => one_ne_zero)
    simp only [one_mul] at h
    rw [hze, h]
    exact (hQ inferInstance j).trans (hDle c)
  rw [e1]
  have hlog0 : 0 ≤ Real.log B := by linarith
  have b1 : (l1 (T.lamS lam s) + |(s : ℝ)|) * D' ≤ Λ * D' := mul_le_mul_of_nonneg_right hl hD'0
  have b2 : (l1 (T.lamS lam s) + |(s : ℝ)|) * (C * Real.log B) ≤ Λ * (|C| * Real.log B) :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0) hl0).trans
      (mul_le_mul_of_nonneg_right hl (mul_nonneg (abs_nonneg _) hlog0))
  have b3 : Λ * D' + |C| ≤ (Λ * D' + |C|) * (2 * Real.log B) :=
    le_mul_of_one_le_right (add_nonneg (mul_nonneg hΛ0 hD'0) (abs_nonneg _)) hlog
  have b4 := le_abs_self C
  linarith

end GlobalTheory.CompanionTheory.Ar.Ht.UpperTower
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerI6OfReferenceStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_i6_of_reference : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (R : T.Comp → RootModel Ψ N), IsIntersectionSystem II → HasRef T R → T.I6 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.UpperTower.tower_upper | exact GlobalTheory.CompanionTheory.Ar.Ht.UpperTower.tower_upper | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.UpperTower.tower_upper <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerIntersectionOfSandwichSplit
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TopGood

theorem tower_intersection_of_ample_flat (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (T : Top.RootTower Ψ (p + q)) (II : IntersectionSystem) (R : T.Comp → Top.RootModel Ψ (p + q))
    (hII : IsIntersectionSystem II) (hR : Ht.HasRef T R)
    (h : ∀ a, Ht.AmpleQ (R a).y (R a).A.a ∧ Ht.FlatUnit (R a) ∧ Ht.FibreInput (j := p) (k := q) (R a)) :
    T.I5 II := by
  obtain ⟨j, rfl⟩ : ∃ j, p = j + 1 := ⟨p - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  exact GlobalTheory.T.tower_i5_of_fibre_input Ψ j k T II R hII hR h

theorem tower_good_of_sandwich_split : Top.Given → Flat.FlatLineGenerator → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (g : Top.GoodOrigin Y T)
    (II : IntersectionSystem), IsIntersectionSystem II → SplitComps Y →
    (∀ B a, ∀ p ∈ g.S B, ∃ κ, HT.IsCp p κ ∧ HT.Sandwich (g.Or B a).𝔐 p κ) → T.I5 II ∧ T.I6 II := by
  intro hG hA E _ _ _ H D l Xo c Y _ T g II hII hsp hS
  obtain ⟨⟨hI, hab, -⟩, -, hext, -, hres, -, -, -, hsl, -⟩ := hG
  have hR : Ht.HasRef T g.R := GlobalTheory.T.has_reference_of_sandwich_all_primes E H D l Xo c Y T g hS
  have hj := g.j_eq
  have h1 := T.j_pos
  have h2 := T.j_lt
  have hp : 1 ≤ D.p := by omega
  have hq : 1 ≤ D.q := by omega
  have hN : 1 ≤ D.p + D.q := by omega
  refine ⟨tower_intersection_of_ample_flat _ D.p D.q hp hq T II g.R hII hR fun a => ⟨g.ample a, ?_, ?_⟩,
    GlobalTheory.T.tower_i6_of_reference _ _ T II g.R hII hR⟩
  · exact GlobalTheory.T.flat_unit_of_split_root_lines hA E H D l Xo c Y ∅ (g.R a) (g.refOr a).𝔐 (g.refOr a).Fl (g.refOr a).e hN hsp
      (g.refOr a).lines
  · exact GlobalTheory.T.root_model_flag_height hab hI hres hext hsl E H D l Xo c Y ∅ (g.R a) (g.refOr a).𝔐 (g.refOr a).Fl (g.refOr a).e hN
      (g.refOr a).lines

end GlobalTheory.CompanionTheory.Ar.TopGood
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerIntersectionOfSandwichSplitStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_intersection_of_sandwich_split : Top.Given → Flat.FlatLineGenerator → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (g : Top.GoodOrigin Y T) (II : IntersectionSystem), IsIntersectionSystem II → SplitComps Y → (∀ B a, ∀ p ∈ g.S B, ∃ κ, HT.IsCp p κ ∧ HT.Sandwich (g.Or B a).𝔐 p κ) → T.I5 II ∧ T.I6 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TopGood.tower_good_of_sandwich_split | exact GlobalTheory.CompanionTheory.Ar.TopGood.tower_good_of_sandwich_split | (intros; apply GlobalTheory.CompanionTheory.Ar.TopGood.tower_good_of_sandwich_split <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.EqOfSpecializesGenPt
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace RootFieldNumerics

section General

variable {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem spMap_genMap (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ := by
  have h1 := Spec.map_comp (X.presheaf.stalkSpecializes p.2) (Scheme.stalkClosedPointTo ξ)
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (X := X) p.2
  exact (congrArg (· ≫ X.fromSpecStalk p.1) h1).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) h2).trans
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

theorem eq_of_specializes_genPt {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) (x' : X) (h : x' ⤳ genPt ξ) : x' = genPt ξ := by
  have hF : IsField (X.presheaf.stalk (genPt ξ)) :=
    (RingEquiv.ofBijective _ hb).toMulEquiv.isField (Field.toIsField Ω)
  have h1 : x' ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact h
  have h2 : genPt ξ ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]; exact specializes_rfl
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  let _ := hF.toField
  have huv : u = v := Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genPt ξ))) u v
  rw [← hu, huv, hv]

theorem exists_factor {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) (ξ' : Spec (CommRingCat.of Ω') ⟶ X)
    (h : genPt ξ' ⤳ genPt ξ) : ∃ φ : Ω →+* Ω', ξ' = spMap φ ≫ ξ := by
  let e := RingEquiv.ofBijective _ hb
  refine ⟨(genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom, ?_⟩
  have h1 : Scheme.stalkClosedPointTo ξ ≫
      CommRingCat.ofHom ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom) =
      CommRingCat.ofHom (genMap ξ' ⟨genPt ξ, h⟩) := by
    ext a
    exact congrArg (genMap ξ' ⟨genPt ξ, h⟩) (e.symm_apply_apply a)
  have h2 := spMap_genMap ξ' ⟨genPt ξ, h⟩
  have h3 := Spec.map_comp (Scheme.stalkClosedPointTo ξ)
    (CommRingCat.ofHom ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom))
  refine h2.symm.trans ?_
  refine (congrArg (fun u => Spec.map u ≫ X.fromSpecStalk (genPt ξ)) h1.symm).trans ?_
  refine (congrArg (· ≫ X.fromSpecStalk (genPt ξ)) h3).trans <| (Category.assoc _ _ _).trans ?_
  exact congrArg (spMap ((genMap ξ' ⟨genPt ξ, h⟩).comp e.symm.toRingHom) ≫ ·)
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem splitComps_of_origin {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    {T : Top.RootTower (CMType H) (D.p + D.q)} (o : TowerOrigin Y T) : SplitComps Y := by
  intro Ω _ ξ cst hξ hs a ha
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  obtain ⟨b, hb⟩ := o.comp_onto (genPt ξ) (eq_of_specializes_genPt hξ.bij)
  obtain ⟨φ, hφ⟩ := exists_factor hξ.bij (o.Fx b).ξf (hb ▸ specializes_rfl)
  let r := o.Or 0 b
  have h1 : spMap (r.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) =
      spMap ((r.g.comp (φ.comp cst)).comp (algebraMap (𝓞 c.F) c.F)) := by
    rw [← r.𝔐.cst_over, ← Category.assoc, r.g_over, hφ, Category.assoc, Category.assoc, hs,
      ← Spec.map_comp, ← Spec.map_comp]
    rfl
  have h2 : r.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) =
      (r.g.comp (φ.comp cst)).comp (algebraMap (𝓞 c.F) c.F) :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have h3 : r.𝔐.cst = r.g.comp (φ.comp cst) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) h2
  obtain ⟨x, hx⟩ := r.g_const (φ a) (ha.algHom φ.toIntAlgHom)
  rw [h3] at hx
  exact ⟨x, φ.injective (r.g.injective hx)⟩

end RootFieldNumerics
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem global_model_tower_fifth_condition : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I5 II ∧ T.I6 II := by
  intro hG E _ _ _ _ H D Xo l c Y _ T o II _ _ hII hp _
  have hG' := hG
  obtain ⟨-, -, -, -, hRes, -, hF, hGaga, -⟩ := hG'
  refine GlobalTheory.T.tower_intersection_of_sandwich_split hG (GlobalTheory.T.flat_zero_from_resolution_and_gaga hRes hGaga) E H D l (Xo l) c Y T o II hII.1
    (splitComps_of_origin o.toTowerOrigin) fun B a p hpS => ?_
  haveI : Fact p.Prime := ⟨(o.Or B a).𝔐.S_prime p hpS⟩
  exact GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l (Xo l) c _ _ Y (o.S B) _ _ _ _ (o.Or B a).𝔐 p hpS (by omega) (o.omVB B a p hpS)

end RootFieldNumerics
