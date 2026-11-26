module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegLogDensNonneg

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearNoetherNormalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

theorem LinearNoetherNormalization.ringKrullDim_quotient_le {R : Type*} [CommRing R] (J : Ideal R)
    (k : WithBot ℕ∞) (h : ∀ W ∈ J.minimalPrimes, ringKrullDim (R ⧸ W) ≤ k) :
    ringKrullDim (R ⧸ J) ≤ k := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun l => ?_
  obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le (show J ≤ l.head.1.asIdeal from l.head.2)
  let l' : LTSeries (PrimeSpectrum.zeroLocus (R := R) W) :=
    ⟨l.length, fun i => ⟨(l i).1, show (W : Set R) ⊆ (l i).1.asIdeal from hle.trans (l.head_le i)⟩,
      fun i => l.step i⟩
  calc (l.length : WithBot ℕ∞) = l'.length := rfl
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) W) := Order.LTSeries.length_le_krullDim l'
    _ = ringKrullDim (R ⧸ W) := (ringKrullDim_quotient W).symm
    _ ≤ k := h W hW

theorem LinearNoetherNormalization.exists_nat_of_le {x : WithBot ℕ∞} {d : ℕ} (h0 : 0 ≤ x)
    (hd : x ≤ d) : ∃ e : ℕ, e ≤ d ∧ x = e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h0 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hd
      exact absurd (WithBot.coe_le_coe.mp h1) (by simp)
    | coe e => exact ⟨e, by exact_mod_cast hd, rfl⟩

theorem LinearNoetherNormalization.exists_monic_of_prefix {d e n : ℕ} (h : e ≤ d)
    (A : Matrix (Fin d) (Fin n) ℂ) (P : Ideal (MvPolynomial (Fin n) ℂ))
    (hP : IsFiniteProjection P (A.submatrix (Fin.castLE h) id)) (j : Fin n) :
    ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
      f.eval₂ (pullback A).toRingHom (X j) ∈ P := by
  obtain ⟨g, hg, hg0⟩ := hP.finite.to_isIntegral (Ideal.Quotient.mk P (X j))
  refine ⟨g.map (rename (R := ℂ) (Fin.castLE h)).toRingHom, hg.map _, ?_⟩
  rw [Polynomial.eval₂_map, ← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
  refine (congrArg (fun φ => Polynomial.eval₂ φ (Ideal.Quotient.mk P (X j)) g) ?_).trans hg0
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [projHom, pullback]
    rfl
  · intro i
    simp [projHom, pullback, linPoly]

theorem LinearNoetherNormalization.proof : LinearNoetherNormalization.Statement := by
  classical
  intro n d J hJ

  have hdim : ∀ P ∈ J.minimalPrimes, ∃ e : ℕ, e ≤ d ∧
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = e := by
    intro P hP
    have : P.IsPrime := hP.1.1
    refine LinearNoetherNormalization.exists_nat_of_le ringKrullDim_nonneg_of_nontrivial ?_
    rw [← hJ]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2)
      (Ideal.Quotient.factor_surjective hP.1.2)

  have htop : ∃ P ∈ J.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = d := by
    by_contra hne
    push Not at hne
    rcases d with _ | d'
    · have hJt : J ≠ ⊤ := by
        rintro rfl
        have : Subsingleton (MvPolynomial (Fin n) ℂ ⧸ (⊤ : Ideal (MvPolynomial (Fin n) ℂ))) :=
          Ideal.Quotient.subsingleton_iff.mpr rfl
        rw [ringKrullDim_eq_bot_of_subsingleton] at hJ
        simp at hJ
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJt
      obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (J := M) hJM
      obtain ⟨e, he, he'⟩ := hdim P hP
      exact hne P hP (by rw [he', Nat.le_zero.mp he])
    · have hle := LinearNoetherNormalization.ringKrullDim_quotient_le J (d' : WithBot ℕ∞)
        (fun P hP => by
          obtain ⟨e, he, he'⟩ := hdim P hP
          have hne' : e ≠ d' + 1 := fun h => hne P hP (by rw [he', h])
          rw [he']
          exact_mod_cast (by omega : e ≤ d'))
      rw [hJ] at hle
      exact absurd hle (by norm_cast; omega)
  obtain ⟨P₀, hP₀, hP₀d⟩ := htop
  have hP₀p : P₀.IsPrime := hP₀.1.1
  obtain ⟨W₀, ⟨S₀, rfl⟩, ⟨A₀, p₀, hp₀S, hp₀⟩, hW₀⟩ :=
    FiniteProjectionsContainOpen.full n d P₀ hP₀p hP₀d
  have hp₀0 : p₀ ≠ 0 := fun h => hp₀ (by rw [h, map_zero])

  have hq : ∀ P ∈ J.minimalPrimes, ∃ q : MvPolynomial (Fin d × Fin n) ℂ, q ≠ 0 ∧
      ∀ A : Matrix (Fin d) (Fin n) ℂ, eval (fun ij : Fin d × Fin n => A ij.1 ij.2) q ≠ 0 →
        ∀ j, ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
          f.eval₂ (pullback A).toRingHom (X j) ∈ P := by
    intro P hP
    have : P.IsPrime := hP.1.1
    obtain ⟨e, he, hPe⟩ := hdim P hP
    obtain ⟨W, ⟨S, rfl⟩, ⟨B, p, hpS, hp⟩, hW⟩ := FiniteProjectionsContainOpen.full n e P this hPe
    refine ⟨rename (Prod.map (Fin.castLE he) id) p, fun h0 => ?_, fun A hA j => ?_⟩
    · apply hp
      rw [rename_injective _ ((Fin.castLE_injective he).prodMap Function.injective_id)
        (h0.trans (map_zero _).symm), map_zero]
    · rw [eval_rename] at hA
      exact LinearNoetherNormalization.exists_monic_of_prefix he A P (hW ⟨p, hpS, hA⟩) j
  choose! q hq0 hqA using hq
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) J
  have hQ : p₀ * ∏ P ∈ hfin.toFinset, q P ≠ 0 :=
    mul_ne_zero hp₀0 (Finset.prod_ne_zero_iff.mpr fun P hP => hq0 P (hfin.mem_toFinset.mp hP))

  obtain ⟨x, hx⟩ : ∃ x, eval x (p₀ * ∏ P ∈ hfin.toFinset, q P) ≠ 0 := by
    by_contra! h
    exact hQ (MvPolynomial.funext fun x => by rw [h x, map_zero])
  let A : Matrix (Fin d) (Fin n) ℂ := Matrix.of fun i j => x (i, j)
  have hxA : (fun ij : Fin d × Fin n => A ij.1 ij.2) = x := rfl
  rw [← hxA, map_mul, map_prod] at hx
  have hall := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hx)
  have hA₀ : IsFiniteProjection P₀ A := hW₀ ⟨p₀, hp₀S, left_ne_zero_of_mul hx⟩

  have hint : ∀ j, (projHom J A).toRingHom.IsIntegralElem (Ideal.Quotient.mk J (X j)) := by
    intro j
    have hf : ∀ P ∈ J.minimalPrimes, ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
        f.eval₂ (pullback A).toRingHom (X j) ∈ P :=
      fun P hP => hqA P hP A (hall P (hfin.mem_toFinset.mpr hP)) j
    choose! f hfm hfP using hf
    have hFm : (∏ P ∈ hfin.toFinset, f P).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun P hP => hfm P (hfin.mem_toFinset.mp hP)
    have hFrad : (∏ P ∈ hfin.toFinset, f P).eval₂ (pullback A).toRingHom (X j) ∈ J.radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      rw [show (∏ P ∈ hfin.toFinset, f P).eval₂ (pullback A).toRingHom (X j) =
          ∏ P ∈ hfin.toFinset, (f P).eval₂ (pullback A).toRingHom (X j) from
        map_prod (Polynomial.eval₂RingHom (pullback A).toRingHom (X j)) _ _]
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
        (fun P => (f P).eval₂ (pullback A).toRingHom (X j)) (hfin.mem_toFinset.mpr hP)
      rw [hc]
      exact Ideal.mul_mem_right c P (hfP P hP)
    obtain ⟨m, hm⟩ := hFrad
    refine ⟨(∏ P ∈ hfin.toFinset, f P) ^ m, hFm.pow m, ?_⟩
    rw [← Polynomial.eval₂_pow, ← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂] at hm
    exact hm
  refine ⟨A, fun a b hab => hA₀.injective ?_, ?_⟩
  · have hfac : ∀ c, projHom P₀ A c = Ideal.Quotient.factor hP₀.1.2 (projHom J A c) :=
      fun c => (Ideal.Quotient.factor_mk hP₀.1.2 _).symm
    rw [hfac, hfac, hab]
  · have hI : (projHom J A).toRingHom.IsIntegral := by
      intro y
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
      induction p using MvPolynomial.induction_on with
      | C a =>
        have : Ideal.Quotient.mk J (C a) = (projHom J A).toRingHom (C a) := by
          simp [projHom, pullback]
          rfl
        rw [this]
        exact (projHom J A).toRingHom.isIntegralElem_map
      | add p q hp hq => rw [map_add (f := _)]; exact RingHom.IsIntegralElem.add _ hp hq
      | mul_X p i hp => rw [map_mul]; exact RingHom.IsIntegralElem.mul _ hp (hint i)
    refine hI.to_finite ?_
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial (Fin d) ℂ))
    rw [show (projHom J A).toRingHom.comp (algebraMap ℂ (MvPolynomial (Fin d) ℂ)) =
      algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ J) from (projHom J A).comp_algebraMap]
    exact RingHom.finiteType_algebraMap.mpr inferInstance

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenPolyFull
section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenPoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology Filter Matrix ComplexSets

noncomputable section

namespace IsolatedFibreOpenPoly

variable {n d : ℕ}

def graphSubst (p : Fin d → MvPolynomial (Fin n) ℂ) :
    MvPolynomial (Fin (n + d)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (Fin.append X p)

def graphIdeal (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) :
    Ideal (MvPolynomial (Fin (n + d)) ℂ) :=
  P.comap (graphSubst p)

def graphPt (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin (n + d) → ℂ :=
  Fin.append x fun i => eval x (p i)

def firstPart (z : Fin (n + d) → ℂ) : Fin n → ℂ :=
  fun j => z (Fin.castAdd d j)

def lastRows (n d : ℕ) : Matrix (Fin d) (Fin (n + d)) ℂ :=
  fun i j => if j = Fin.natAdd n i then 1 else 0

theorem lastRows_mulVec (z : Fin (n + d) → ℂ) : lastRows n d *ᵥ z = fun i => z (Fin.natAdd n i) := by
  funext i
  simp [lastRows, Matrix.mulVec, dotProduct, ite_mul]

theorem firstPart_graphPt (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    firstPart (graphPt p x) = x := by
  funext j
  simp [firstPart, graphPt, Fin.append_left]

theorem graphPt_natAdd (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (i : Fin d) :
    graphPt p x (Fin.natAdd n i) = eval x (p i) := by
  simp [graphPt, Fin.append_right]

theorem continuous_firstPart : Continuous (firstPart : (Fin (n + d) → ℂ) → Fin n → ℂ) :=
  continuous_pi fun _ => continuous_apply _

theorem eval_graphSubst (p : Fin d → MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ)
    (q : MvPolynomial (Fin (n + d)) ℂ) : eval x (graphSubst p q) = eval (graphPt p x) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [graphSubst]
  | add q r hq hr => simp only [map_add (f := _), hq, hr]
  | mul_X q i hq =>
    simp only [map_mul, graphSubst, aeval_X, eval_X]
    congr 1
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [graphPt, Fin.append_left]
    · simp [graphPt, Fin.append_right]

theorem graphSubst_rename (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    graphSubst p (rename (Fin.castAdd d) q) = q := by
  rw [graphSubst, aeval_rename]
  have h : (Fin.append X p ∘ Fin.castAdd d : Fin n → MvPolynomial (Fin n) ℂ) = X := by
    funext j
    simp [Fin.append_left]
  rw [h, aeval_X_left_apply]

theorem graphSubst_surjective (p : Fin d → MvPolynomial (Fin n) ℂ) :
    Function.Surjective (graphSubst p) :=
  fun q => ⟨rename (Fin.castAdd d) q, graphSubst_rename p q⟩

theorem isPrime_graphIdeal {P : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P.IsPrime)
    (p : Fin d → MvPolynomial (Fin n) ℂ) : (graphIdeal P p).IsPrime := by
  have := hP
  unfold graphIdeal
  infer_instance

theorem ringKrullDim_graphIdeal (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + d)) ℂ ⧸ graphIdeal P p) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := by
  set f : MvPolynomial (Fin (n + d)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ P :=
    (Ideal.Quotient.mk P).comp (graphSubst p).toRingHom with hf
  have hsurj : Function.Surjective f :=
    Ideal.Quotient.mk_surjective.comp (graphSubst_surjective p)
  have hker : graphIdeal P p = RingHom.ker f := by
    rw [hf, ← RingHom.comap_ker, Ideal.mk_ker]
    rfl
  exact ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj))

theorem graphPt_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} (p : Fin d → MvPolynomial (Fin n) ℂ)
    {x : Fin n → ℂ} (hx : x ∈ zeroSet P) : graphPt p x ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p) := by
  intro q hq
  rw [← eval_graphSubst]
  exact hx _ hq

theorem firstPart_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    firstPart z ∈ zeroSet P := by
  intro q hq
  have h := hz (rename (Fin.castAdd d) q) (by
    show graphSubst p (rename (Fin.castAdd d) q) ∈ P
    rw [graphSubst_rename]
    exact hq)
  rw [eval_rename] at h
  exact h

theorem natAdd_of_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) (i : Fin d) :
    z (Fin.natAdd n i) = eval (firstPart z) (p i) := by
  have h := hz (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) (by
    show graphSubst p (X (Fin.natAdd n i) - rename (Fin.castAdd d) (p i)) ∈ P
    rw [map_sub, graphSubst_rename, graphSubst, aeval_X, Fin.append_right, sub_self]
    exact P.zero_mem)
  rw [map_sub, eval_X, eval_rename, sub_eq_zero] at h
  exact h

theorem eq_graphPt_of_mem {P : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {z : Fin (n + d) → ℂ} (hz : z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p)) :
    z = graphPt p (firstPart z) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun i => ?_) k
  · simp [graphPt, firstPart, Fin.append_left]
  · rw [natAdd_of_mem hz i, graphPt_natAdd]

theorem proof (hOpen : IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpen.Statement) : IsolatedFibreOpenPoly.Statement := by
  intro n d P p x hP hdim hx ⟨W, hW, hiso⟩ W' hW'
  have hV : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety (graphIdeal P p) d :=
    ⟨isPrime_graphIdeal hP p, by rw [ringKrullDim_graphIdeal]; exact hdim⟩
  have hAx : lastRows n d *ᵥ graphPt p x = fun i => eval x (p i) := by
    rw [lastRows_mulVec]
    funext i
    exact graphPt_natAdd p x i
  have hN : ∀ U ∈ 𝓝 x, firstPart ⁻¹' U ∈ 𝓝 (graphPt p x) := fun U hU =>
    continuous_firstPart.continuousAt.preimage_mem_nhds (by rw [firstPart_graphPt]; exact hU)
  have hisoG : ∀ z ∈ firstPart ⁻¹' W, z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroLocus (graphIdeal P p) →
      lastRows n d *ᵥ z = lastRows n d *ᵥ graphPt p x → z = graphPt p x := by
    intro z hzW hz hAz
    have hfz : firstPart z = x := by
      refine hiso _ ⟨firstPart_mem hz, hzW⟩ fun i => ?_
      have h := congrFun hAz i
      rw [lastRows_mulVec, lastRows_mulVec] at h
      simp only at h
      rw [natAdd_of_mem hz, graphPt_natAdd] at h
      exact h
    rw [eq_graphPt_of_mem hz, hfz]
  have h := hOpen (n + d) d (graphIdeal P p) (lastRows n d) (graphPt p x) hV (graphPt_mem p hx)
    ⟨firstPart ⁻¹' W, hN W hW, hisoG⟩ (firstPart ⁻¹' W') (hN W' hW')
  rw [hAx] at h
  refine Filter.mem_of_superset h ?_
  rintro _ ⟨z, ⟨hz, hzW'⟩, rfl⟩
  refine ⟨firstPart z, ⟨firstPart_mem hz, hzW'⟩, ?_⟩
  show (fun i => eval (firstPart z) (p i)) = lastRows n d *ᵥ z
  rw [lastRows_mulVec]
  funext i
  exact (natAdd_of_mem hz i).symm

end IsolatedFibreOpenPoly

end

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IsolatedFibreOpenPoly.full : IsolatedFibreOpenPoly.Statement :=
  IsolatedFibreOpenPoly.proof
    (IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric.proof
      (IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.equiv.mp ComplexSets.GenericProjectionFinite.full)
      IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedPointsCountPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

theorem IsolatedPointsCountPrime.exists_dim_eq {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
  have h0 : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := ringKrullDim_nonneg_of_nontrivial
  have h1 := ringKrullDim_quotient_le J
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h1
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at h0 h1 ⊢
  induction x using WithBot.recBotCoe with
  | bot => simp at h0
  | coe k =>
    induction k using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h1
      exact absurd (WithBot.coe_le_coe.1 h2) (by simp)
    | coe k => exact ⟨k, rfl⟩

theorem IsolatedPointsCountPrime.eval_aeval {n m : ℕ} (Q : Fin m → MvPolynomial (Fin n) ℂ)
    (f : MvPolynomial (Fin m) ℂ) (x : Fin n → ℂ) :
    eval x (aeval Q f) = eval (fun i => eval x (Q i)) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p p' hp hp' => rw [map_add (f := _), map_add (f := _), hp, hp', map_add (f := _)]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]

theorem IsolatedPointsCountPrime.exists_eval_ne_zero {d : ℕ} {Δ : MvPolynomial (Fin d) ℂ} (hΔ : Δ ≠ 0)
    {w : Fin d → ℂ} {S : Set (Fin d → ℂ)} (hS : S ∈ 𝓝 w) : ∃ w' ∈ S, eval w' Δ ≠ 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hS
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  apply hΔ
  refine funext_set (fun i => Metric.ball (w i) ε)
    (fun i => infinite_of_mem_nhds (w i) (Metric.ball_mem_nhds (w i) hε)) (fun y hy => ?_)
  rw [map_zero]
  refine h y (hball ?_)
  rw [ball_pi w hε]
  exact hy

theorem IsolatedPointsCountPrime.proof (hOpen : IsolatedFibreOpenPoly.Statement)
    (hDom : DominantFibreBound.Statement) (hDim : ImageDimLe.Statement) :
    IsolatedPointsCountPrime.Statement := by
  classical
  intro n m P hP Q

  have hKp : (RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q))).IsPrime := RingHom.ker_isPrime _
  set K := RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval Q)) with hK
  obtain ⟨d, hd⟩ := IsolatedPointsCountPrime.exists_dim_eq P
  obtain ⟨r, hr⟩ := IsolatedPointsCountPrime.exists_dim_eq K
  have hrd : r ≤ d := by
    have h := hDim n m P Q hP
    rw [← hK, hr, hd] at h
    exact_mod_cast h
  obtain ⟨B, hB⟩ := (GenericProjectionFinite.full m r K hKp hr).2.1
  have hfib := FibreBound.full m r K B hKp hr hB

  set Qm : (Fin n → ℂ) → (Fin m → ℂ) := fun x i => eval x (Q i) with hQm
  have hQZ : ∀ x ∈ zeroSet P, Qm x ∈ zeroSet K := by
    intro x hx f hf
    have hf' : aeval Q f ∈ P := by
      rw [hK, RingHom.mem_ker] at hf
      simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] using hf
    rw [← IsolatedPointsCountPrime.eval_aeval]
    exact hx _ hf'
  have hQc : Continuous Qm := continuous_pi fun i => MvPolynomial.continuous_eval _

  set q : Fin r → MvPolynomial (Fin n) ℂ := fun i => aeval Q (linPoly B i) with hq
  have hqe : ∀ x, (fun i => eval x (q i)) = B.mulVec (Qm x) := by
    intro x
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hq, IsolatedPointsCountPrime.eval_aeval, linPoly, map_sum, map_mul, eval_C, eval_X,
      Matrix.mulVec, dotProduct, hQm]

  have step1 : ∀ z x, x ∈ isolatedFibrePts P Q z →
      ∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (q i) = eval x (q i)) → x' = x := by
    rintro z x ⟨hxP, hxQ, V, hV, hiso⟩
    have hQx : Qm x = z := funext hxQ
    have hfin : (ComplexSets.fibre K B (B.mulVec z) \ {z}).Finite := (hfib (B.mulVec z)).2.1.subset Set.sdiff_subset
    have hO : (ComplexSets.fibre K B (B.mulVec z) \ {z})ᶜ ∈ 𝓝 (Qm x) := by
      rw [hQx]
      exact hfin.isClosed.compl_mem_nhds fun h => h.2 rfl
    refine ⟨V ∩ Qm ⁻¹' (ComplexSets.fibre K B (B.mulVec z) \ {z})ᶜ,
      Filter.inter_mem hV (hQc.continuousAt.preimage_mem_nhds hO), ?_⟩
    rintro x' ⟨hx'P, hx'V, hx'O⟩ hx'q
    refine hiso x' ⟨hx'P, hx'V⟩ fun i => congrFun (?_ : Qm x' = z) i
    have h1 : B.mulVec (Qm x') = B.mulVec z := by
      rw [← hqe, ← hQx, ← hqe]
      funext i
      exact hx'q i
    by_contra hne
    exact hx'O ⟨⟨hQZ x' hx'P, h1⟩, hne⟩
  rcases lt_or_eq_of_le hrd with hlt | rfl
  ·
    refine ⟨0, fun z => ?_⟩
    suffices isolatedFibrePts P Q z = ∅ by simp [this]
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨W, hW, hiso⟩ := step1 z x hx
    set p : Fin d → MvPolynomial (Fin n) ℂ := fun i => if h : (i : ℕ) < r then q ⟨i, h⟩ else 0 with hp
    have hiso' : ∃ W ∈ 𝓝 x, ∀ x' ∈ zeroSet P ∩ W, (∀ i, eval x' (p i) = eval x (p i)) → x' = x :=
      ⟨W, hW, fun x' hx' h => hiso x' hx' fun i => by
        simpa [hp, i.isLt] using h ⟨i, i.isLt.trans hlt⟩⟩
    have himg := hOpen n d P p x hP hd hx.1 hiso' Set.univ Filter.univ_mem
    set px : Fin d → ℂ := fun i => eval x (p i) with hpx
    set j : Fin d := ⟨r, hlt⟩
    have hsub : (fun x' : Fin n → ℂ => fun i => eval x' (p i)) '' (zeroSet P ∩ Set.univ) ⊆
        {w | w j = 0} := by
      rintro _ ⟨y, -, rfl⟩
      simp [hp, j]
    have hc : Continuous fun t : ℂ => Function.update px j t := continuous_const.update j continuous_id
    have h1 : (fun t : ℂ => Function.update px j t) ⁻¹' {w | w j = 0} ∈ 𝓝 (px j) := by
      refine hc.continuousAt.preimage_mem_nhds ?_
      rw [Function.update_eq_self]
      exact Filter.mem_of_superset himg hsub
    have h2 : (fun t : ℂ => Function.update px j t) ⁻¹' {w | w j = 0} ⊆ {0} := by
      intro t ht
      simpa using ht
    exact (infinite_of_mem_nhds (px j) (Filter.mem_of_superset h1 h2)) (Set.finite_singleton 0)
  ·
    have hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval q)) := by
      have hcomp : aeval q = (aeval Q).comp (pullback B) := by
        apply MvPolynomial.algHom_ext
        intro i
        simp [hq, pullback]
      intro a b hab
      apply hB.injective
      simp only [projHom, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq] at hab ⊢
      rw [hcomp, AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub] at hab
      rw [hK, RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hab
    obtain ⟨e, Δ, hΔ, hbound⟩ := hDom n r P q hP hd hinj
    refine ⟨e, fun z => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq (Order.add_one_le_of_lt hlt)
    have htc' : t.encard = ((e + 1 : ℕ) : ℕ∞) := by rw [htc]; push_cast; rfl
    have htf : t.Finite := Set.finite_of_encard_eq_coe htc'
    obtain ⟨U, hUo, hUd⟩ := htf.t2_separation
    have hw : ∀ x ∈ t, (fun x' : Fin n → ℂ => fun i => eval x' (q i)) '' (zeroSet P ∩ U x) ∈
        𝓝 (B.mulVec z) := by
      intro x hx
      have hx' := hts hx
      obtain ⟨W, hW, hiso⟩ := step1 z x hx'
      have h := hOpen n r P q x hP hd hx'.1 ⟨W, hW, hiso⟩ (U x) ((hUo x).2.mem_nhds (hUo x).1)
      have e1 : (fun i => eval x (q i)) = B.mulVec z := by
        rw [hqe]
        congr 1
        exact funext hx'.2.1
      rwa [e1] at h
    have hI := (Filter.biInter_mem htf).2 hw
    obtain ⟨w', hw'I, hΔw'⟩ := IsolatedPointsCountPrime.exists_eval_ne_zero hΔ hI
    have hpick : ∀ x ∈ t, ∃ y, y ∈ zeroSet P ∩ U x ∧ (fun i => eval y (q i)) = w' :=
      fun x hx => Set.mem_iInter₂.1 hw'I x hx
    choose! g hg1 hg2 using hpick
    have hinjg : Set.InjOn g t := by
      intro x hx y hy hxy
      by_contra hne
      refine Set.disjoint_left.1 (hUd hx hy hne) (hg1 x hx).2 ?_
      rw [hxy]
      exact (hg1 y hy).2
    have himg : g '' t ⊆ {x | x ∈ zeroSet P ∧ ∀ i, eval x (q i) = w' i} := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hg1 x hx).1, fun i => congrFun (hg2 x hx) i⟩
    have hle := (Set.encard_le_encard himg).trans (hbound w' hΔw')
    rw [hinjg.encard_image, htc'] at hle
    have hle' : e + 1 ≤ e := by exact_mod_cast hle
    omega

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarLelongMono
section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarLelongAnnulus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def VarLelongAnnulus.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < r → r ≤ s →
      r ^ (2 * (d + 1)) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1) (fun _ => euclPot) y) -
        s ^ (2 * (d + 1)) * (∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1) (fun _ => euclPot) y) =
      r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) *
        ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1) (fun _ => logDistSq x) y

end

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

namespace LelongNumberMonotone

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem maDens_logDistSq_nonneg (x z : Fin n → ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (hzx : z ≠ x)
    (hs : IsSheetAt J A z s) :
    0 ≤ ReciprocityTheory.AnForm.maDens (fun _ : Fin (d + 1) => logDistSq x ∘ s) (A *ᵥ z) := by
  have han : AnalyticAt ℂ s (A *ᵥ z) := FormIntegralPositivity.analyticAt_sheet hs
  have hsz : s (A *ᵥ z) = z := by
    obtain ⟨U, -, -, -, h, -⟩ := hs
    exact h
  exact ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ =>
    RegularizedLogDensityNonneg.hessC_logDistSq_comp_posSemidef x s _ han (hsz.symm ▸ hzx)

theorem chartDens_annulus_nonneg (x : Fin n → ℂ) {r s : ℝ} (hr : 0 < r) (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1) (fun _ => logDistSq x) y := by
  unfold chartDens sheetSum
  refine finsum_nonneg fun z => finsum_nonneg fun hz => ?_
  split_ifs with h
  · beta_reduce
    by_cases hza : z ∈ euclBall x s \ euclBall x r
    · rw [Set.indicator_of_mem hza, one_mul]
      have := maDens_logDistSq_nonneg x z h.choose (ne_of_mem_euclBall_diff hr hza) h.choose_spec
      rwa [hz.2] at this
    · rw [Set.indicator_of_notMem hza, zero_mul]
  · exact le_rfl

end LelongNumberMonotone


open LelongNumberMonotone in
theorem VarLelongMono.proof (hA : VarLelongAnnulus.Statement) : VarLelongMono.Statement := by
  intro n d J A x r s hJ hdim hAf hr hrs
  have heq := hA n d J A x r s hJ hdim hAf hr hrs
  have hτ : 0 ≤ ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
      (fun _ => logDistSq x) y :=
    integral_nonneg fun y => chartDens_annulus_nonneg x hr y
  have hrs0 : 0 ≤ r ^ (2 * (d + 1)) * s ^ (2 * (d + 1)) :=
    mul_nonneg (pow_nonneg hr.le _) (pow_nonneg (hr.le.trans hrs) _)
  have := mul_nonneg hrs0 hτ
  linarith

end

end GroundTheory.Heights₂.Heights
end
