module

public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DetLocus
open IsLocalRing MvPolynomial

namespace UpperTheory.V.AlgebraTools

variable {P : Type} [CommRing P] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem isPrime_map_C (p : Ideal P) [p.IsPrime] :
    (p.map (C : P →+* MvPolynomial ι P)).IsPrime := by
  have he : p.map (C : P →+* MvPolynomial ι P) =
      RingHom.ker (MvPolynomial.map (σ := ι) (Ideal.Quotient.mk p)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  rw [he]
  exact RingHom.ker_isPrime _

def relIdeal (z : Matrix ι ι P) (m : ι → P) : Ideal P := Ideal.span (Set.range (z.mulVec m))

def detIdeal (z : Matrix ι ι P) (m : ι → P) : Ideal P := relIdeal z m ⊔ Ideal.span {z.det}

noncomputable def lam (P : Type) [CommRing P] (c : ι) (j : ι) : MvPolynomial ι P :=
  if j = c then 1 else X j

noncomputable def chartGen (z : Matrix ι ι P) (m : ι → P) (c : ι) :
    ι ⊕ {j : ι // j ≠ c} → MvPolynomial ι P :=
  Sum.elim ((z.map C).mulVec (lam P c)) (fun j => C (m j.1) - lam P c j.1 * C (m c))

noncomputable def chartIdeal (z : Matrix ι ι P) (m : ι → P) (c : ι) : Ideal (MvPolynomial ι P) :=
  Ideal.span (Set.range (chartGen z m c))

noncomputable def genKer [IsLocalRing P] (z : Matrix ι ι P) (m : ι → P) (c : ι) : Ideal P where
  carrier := {f | ∃ s : MvPolynomial ι P, s ∉ (maximalIdeal P).map (C : P →+* MvPolynomial ι P) ∧
    s * C f ∈ chartIdeal z m c}
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 (Ideal.IsPrime.ne_top (by
    have : (maximalIdeal P).IsPrime := inferInstance
    exact isPrime_map_C _)), by simp⟩
  add_mem' := by
    rintro a b ⟨s, hs, ha⟩ ⟨t, ht, hb⟩
    have hp : ((maximalIdeal P).map (C : P →+* MvPolynomial ι P)).IsPrime :=
      isPrime_map_C _
    refine ⟨s * t, fun h => (hp.mem_or_mem h).elim hs ht, ?_⟩
    have : s * t * C (a + b) = t * (s * C a) + s * (t * C b) := by rw [map_add (f := _)]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
  smul_mem' := by
    rintro r a ⟨s, hs, ha⟩
    refine ⟨s, hs, ?_⟩
    have : s * C (r • a) = C r * (s * C a) := by rw [smul_eq_mul, map_mul]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ ha

end UpperTheory.V.AlgebraTools
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetChartPrime
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaPolyReg
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaFlatReg
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem flat_regular_cotangent_extension
    (A B : Type) [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [IsRegularLocalRing (B ⧸ (maximalIdeal A).map (algebraMap A B))]
    (κ : Type) [Fintype κ] (x : κ → A) (hx : CotInd A x) :
    ∃ (s t : ℕ) (z : (κ ⊕ Fin s) ⊕ Fin t → B), (∀ k, z (Sum.inl (Sum.inl k)) = algebraMap A B (x k)) ∧
      Ideal.span (Set.range z) = maximalIdeal B ∧
      ((Fintype.card ((κ ⊕ Fin s) ⊕ Fin t) : ℕ) : WithBot ℕ∞) = ringKrullDim B := by
  set I := (maximalIdeal A).map (algebraMap A B) with hI
  obtain ⟨s, y, -, hy, hs⟩ := cotInd_extend A κ x hx
  obtain ⟨t, w, -, hw, ht⟩ := cotInd_extend (B ⧸ I) Empty (fun e => e.elim)
    ⟨fun e => e.elim, fun _ _ e => e.elim⟩
  choose v hv using fun j => Ideal.Quotient.mk_surjective (w j)
  have hw' : Ideal.span (Set.range w) = maximalIdeal (B ⧸ I) := by
    rw [← hw, Set.Sum.elim_range, Set.range_eq_empty (ι := Empty), Set.empty_union]
  have hmap : (maximalIdeal B).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hIle : I ≤ maximalIdeal B := IsLocalRing.map_maximalIdeal_le _
  refine ⟨s, t, Sum.elim (fun i => algebraMap A B (Sum.elim x y i)) v, fun k => rfl, ?_, ?_⟩
  · rw [Set.Sum.elim_range, Ideal.span_union]
    have h1 : Ideal.span (Set.range fun i => algebraMap A B (Sum.elim x y i)) = I := by
      rw [hI, ← hy, Ideal.map_span, ← Set.range_comp]
      rfl
    have h2 : (Ideal.span (Set.range v)).map (Ideal.Quotient.mk I) = maximalIdeal (B ⧸ I) := by
      rw [Ideal.map_span, ← Set.range_comp, ← hw']
      congr 2
      funext j
      exact hv j
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk I)) (h2.trans hmap.symm)
    rw [Ideal.comap_map_quotientMk, Ideal.comap_map_quotientMk, sup_eq_right.2 hIle] at h3
    rw [h1, h3]
  · haveI : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
    have H := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
    rw [← hI, hmap] at H
    have H' := congrArg (fun a : ℕ∞ => (a : WithBot ℕ∞)) H
    simp only [WithBot.coe_add, IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at H'
    rw [H', ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A),
      ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := B ⧸ I), ← hs, ← ht]
    simp

theorem UpperTheory.V.AlgebraTools.regular_of_flat_fibre :
    ∀ (A B : Type) [CommRing A] [IsRegularLocalRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
      [IsRegularLocalRing (B ⧸ (maximalIdeal A).map (algebraMap A B))],
      IsRegularLocalRing B ∧ ∀ (κ : Type) [Fintype κ] (x : κ → A), CotInd A x → CotInd B (fun k => algebraMap A B (x k)) := by
  intro A B _ _ _ _ _ _ _ _ _
  constructor
  · obtain ⟨s, t, z, -, hz, hc⟩ := flat_regular_cotangent_extension A B Empty (fun e => e.elim)
      ⟨fun e => e.elim, fun _ _ e => e.elim⟩
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [← hc, ← hz, Nat.cast_le]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range z)).trans ?_
    rw [← Set.image_univ, ← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_image_le
  · intro κ _ x hx
    obtain ⟨s, t, z, hzx, hz, hc⟩ := flat_regular_cotangent_extension A B κ x hx
    have h1 := ringKrullDim_le_spanFinrank_maximalIdeal B
    rw [← hc, Nat.cast_le] at h1
    have h2 := (cotInd_of_span B _ z hz h1).comp (fun k : κ => Sum.inl (Sum.inl k))
      (Sum.inl_injective.comp Sum.inl_injective)
    have h3 : (z ∘ fun k : κ => Sum.inl (Sum.inl k)) = fun k => algebraMap A B (x k) := funext hzx
    rwa [h3] at h2
end

open IsLocalRing UpperTheory.V.AlgebraTools

private theorem fibre_reg (R : Type) [CommRing R] (J n : Ideal R) [n.IsPrime] (hn : J ≤ n)
    [IsRegularRing (R ⧸ J)] (A : Type) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A n] :
    IsRegularLocalRing (A ⧸ J.map (algebraMap R A)) := by
  have hJn : RingHom.ker (Ideal.Quotient.mk J) ≤ n := by
    rwa [Ideal.mk_ker]
  have hm : (n.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hJn
  have hle : J ≤ (J.map (algebraMap R A)).comap (algebraMap R A) := Ideal.le_comap_map
  letI : Algebra (R ⧸ J) (A ⧸ J.map (algebraMap R A)) := (Ideal.quotientMap _ _ hle).toAlgebra
  have hl := IsLocalization.of_surjective n.primeCompl A (S' := A ⧸ J.map (algebraMap R A))
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective rfl
    (by rw [Ideal.mk_ker, Ideal.mk_ker])
  have e : n.primeCompl.map (Ideal.Quotient.mk J) = (n.map (Ideal.Quotient.mk J)).primeCompl := by
    have hc : (n.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = n := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hJn]
    ext y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    constructor
    · rintro ⟨x', hx', e⟩ hx
      exact hx' (hc.le (show Ideal.Quotient.mk J x' ∈ _ from e ▸ hx))
    · exact fun hx => ⟨x, fun h => hx (Ideal.mem_map_of_mem _ h), rfl⟩
  rw [e] at hl
  have := IsRegularRing.isRegularLocalRing_localization (n.map (Ideal.Quotient.mk J))
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv (n.map (Ideal.Quotient.mk J)).primeCompl
    (Localization.AtPrime (n.map (Ideal.Quotient.mk J))) _).toRingEquiv

theorem UpperTheory.V.AlgebraTools.regular_polynomial_localization :
    ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (σ : Type) [Finite σ] (Q : Ideal (MvPolynomial σ A)) [Q.IsPrime],
      (maximalIdeal A).map (MvPolynomial.C : A →+* MvPolynomial σ A) ≤ Q →
      IsRegularLocalRing (Localization.AtPrime Q) ∧ ∀ (κ : Type) [Fintype κ] (x : κ → A), CotInd A x →
        CotInd (Localization.AtPrime Q) (fun k => algebraMap (MvPolynomial σ A) _ (MvPolynomial.C (x k))) := by
  intro A _ _ σ _ Q _ hQ
  have hcomp : algebraMap A (Localization.AtPrime Q) =
      (algebraMap (MvPolynomial σ A) (Localization.AtPrime Q)).comp MvPolynomial.C :=
    IsScalarTower.algebraMap_eq A (MvPolynomial σ A) (Localization.AtPrime Q)
  haveI : IsRegularRing (MvPolynomial σ A ⧸
      (maximalIdeal A).map (MvPolynomial.C : A →+* MvPolynomial σ A)) := by
    letI := Ideal.Quotient.field (maximalIdeal A)
    haveI : IsRegularRing (MvPolynomial σ (A ⧸ maximalIdeal A)) := inferInstance
    exact IsRegularRing.of_ringEquiv
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) (maximalIdeal A)).toRingEquiv
  have hf := fibre_reg _ _ Q hQ (Localization.AtPrime Q)
  rw [Ideal.map_map, ← hcomp] at hf
  haveI : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  haveI : Module.Flat (MvPolynomial σ A) (Localization.AtPrime Q) :=
    IsLocalization.flat _ Q.primeCompl
  haveI : Module.Flat A (Localization.AtPrime Q) :=
    Module.Flat.trans A (MvPolynomial σ A) (Localization.AtPrime Q)
  haveI : IsLocalHom (algebraMap A (Localization.AtPrime Q)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : MvPolynomial.C a ∈ Q := hQ (Ideal.mem_map_of_mem _ ((mem_maximalIdeal a).2 hna))
    rw [hcomp] at ha
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q _).1 ha h1
  have H := regular_of_flat_fibre A (Localization.AtPrime Q)
  rw [hcomp] at H
  exact H
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetChartCot
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.chartGen_cotInd :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι B) (m l : ι → B) (c : ι),
      CotInd B (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) → l c = 1 →
      CotInd B (Sum.elim (z.mulVec l) (fun j : {j : ι // j ≠ c} => m j.1 - l j.1 * m c)) := by
  intro B _ _ ι _ _ z m l c hx hl
  have hmem := hx.mem
  refine ⟨?_, ?_⟩
  · intro k
    rcases k with i | j
    · simp only [Sum.elim_inl, Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hmem (Sum.inl (i, j)))
    · simp only [Sum.elim_inr]
      exact Ideal.sub_mem _ (hmem (Sum.inr j.1)) (Ideal.mul_mem_left _ _ (hmem (Sum.inr c)))
  · intro a ha
    let b : ι × ι ⊕ ι → B := Sum.elim (fun ij => a (Sum.inl ij.1) * l ij.2)
      (fun j => if h : j = c then -(∑ k : {k // k ≠ c}, a (Sum.inr k) * l k.1)
        else a (Sum.inr ⟨j, h⟩))
    have key : ∑ k, b k * Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m k
        = ∑ k, a k * Sum.elim (z.mulVec l) (fun j : {j : ι // j ≠ c} => m j.1 - l j.1 * m c) k := by
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr]
      rw [Fintype.sum_eq_add_sum_subtype_ne (fun j => b (Sum.inr j) * m j) c]
      simp only [b, Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, dotProduct, dite_true]
      have e : ∀ j : {j // j ≠ c}, (if h : (j : ι) = c then
          -(∑ k : {k // k ≠ c}, a (Sum.inr k) * l k.1) else a (Sum.inr ⟨j, h⟩)) * m j
          = a (Sum.inr j) * m j := fun j => by rw [dite_eq_right j.2]
      rw [Finset.sum_congr rfl (fun j _ => e j)]
      have e2 : ∀ i, ∑ j, a (Sum.inl i) * l j * z i j = a (Sum.inl i) * ∑ j, z i j * l j := by
        intro i
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [Finset.sum_congr rfl (fun i _ => e2 i)]
      have e3 : ∑ j : {j // j ≠ c}, a (Sum.inr j) * (m j - l j * m c)
          = ∑ j : {j // j ≠ c}, a (Sum.inr j) * m j - (∑ k : {k // k ≠ c}, a (Sum.inr k) * l k) * m c := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [e3]
      ring
    have hb : ∀ k, b k ∈ maximalIdeal B := hx.indep b (by rw [key]; exact ha)
    intro k
    rcases k with i | j
    · have := hb (Sum.inl (i, c))
      simpa [b, hl] using this
    · have := hb (Sum.inr j.1)
      simpa [b, j.2] using this
end

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.chartIdeal_localization_isPrime :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ (c : ι) (Q : Ideal (MvPolynomial ι P)) [Q.IsPrime],
      (maximalIdeal P).map (MvPolynomial.C : P →+* MvPolynomial ι P) ≤ Q →
      ((chartIdeal z m c).map (algebraMap _ (Localization.AtPrime Q))).IsPrime := by
  intro P _ _ ι _ _ z m hx c Q _ hQ
  obtain ⟨_, hcot⟩ := regular_polynomial_localization P ι Q hQ
  let φ : MvPolynomial ι P →+* Localization.AtPrime Q := algebraMap _ _
  let w : ι → Localization.AtPrime Q := fun j => φ (MvPolynomial.C (m j))
  let l : ι → Localization.AtPrime Q := fun j => φ (lam P c j)
  let y : Matrix ι ι (Localization.AtPrime Q) := z.map (φ.comp MvPolynomial.C)
  have h1 : CotInd (Localization.AtPrime Q) (Sum.elim (fun ij : ι × ι => y ij.1 ij.2) w) := by
    have h := hcot _ _ hx
    convert h using 1
    funext k
    rcases k with k | k <;> rfl
  have hl : l c = 1 := by
    simp [l, lam]
  have h2 := chartGen_cotInd (Localization.AtPrime Q) ι y w l c h1 hl
  have h3 := (regular_quotient_cotInd (Localization.AtPrime Q) _ _ h2).2.2
  have hf : ⇑φ ∘ chartGen z m c = Sum.elim (y.mulVec l) fun j : {j : ι // j ≠ c} => w j - l j * w c := by
    funext k
    rcases k with k | k
    · simp only [Function.comp, chartGen, Sum.elim_inl]
      rw [RingHom.map_mulVec, Matrix.map_map]
      rfl
    · simp [chartGen, w, l]
  have key : (chartIdeal z m c).map φ =
      Ideal.span (Set.range (Sum.elim (y.mulVec l) fun j : {j : ι // j ≠ c} => w j - l j * w c)) := by
    rw [chartIdeal, Ideal.map_span, ← Set.range_comp, hf]
  exact key ▸ h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetKerLe
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.genKer_le_ker :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ (c : ι) (D : Type) [CommRing D] [IsLocalRing D] (φ : P →+* D) [IsLocalHom φ] (l : ι → D),
      l c = 1 → (z.map φ).mulVec l = 0 → (∀ j, φ (m j) = l j * φ (m c)) → genKer z m c ≤ RingHom.ker φ := by
  intro P _ _ ι _ _ z m hcot c D _ _ φ _ l hlc hzl hm
  let ψ : MvPolynomial ι P →+* D := MvPolynomial.eval₂Hom φ l
  have hψC : ∀ a, ψ (MvPolynomial.C a) = φ a := fun a => MvPolynomial.eval₂Hom_C φ l a
  have hlam : ∀ j, ψ (UpperTheory.V.AlgebraTools.lam P c j) = l j := by
    intro j
    unfold UpperTheory.V.AlgebraTools.lam
    split_ifs with h
    · subst h
      simp [hlc]
    · exact MvPolynomial.eval₂Hom_X' φ l j
  let M0 : Ideal (MvPolynomial ι P) := Ideal.map MvPolynomial.C (maximalIdeal P)
  haveI hM0 : M0.IsPrime := UpperTheory.V.AlgebraTools.isPrime_map_C (maximalIdeal P)
  let Q : Ideal (MvPolynomial ι P) := Ideal.comap ψ (maximalIdeal D)
  haveI : Q.IsPrime := Ideal.comap_isPrime ψ (maximalIdeal D)
  have hMQ : M0 ≤ Q := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    show ψ (MvPolynomial.C a) ∈ maximalIdeal D
    rw [hψC]
    exact map_nonunit φ a ha
  have hker : chartIdeal z m c ≤ RingHom.ker ψ := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rcases k with i | ⟨j, hj⟩
    · show ψ (((z.map MvPolynomial.C).mulVec (UpperTheory.V.AlgebraTools.lam P c)) i) = 0
      have h := congrFun hzl i
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at h ⊢
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_mul, hψC, hlam]
      exact h
    · show ψ (MvPolynomial.C (m j) - UpperTheory.V.AlgebraTools.lam P c j * MvPolynomial.C (m c)) = 0
      rw [map_sub, map_mul, hψC, hψC, hlam, hm j, sub_self]
  have hchartM : chartIdeal z m c ≤ M0 := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rcases k with i | ⟨j, hj⟩
    · show ((z.map MvPolynomial.C).mulVec (UpperTheory.V.AlgebraTools.lam P c)) i ∈ M0
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
      simpa using hcot.mem (Sum.inl (i, j))
    · show MvPolynomial.C (m j) - UpperTheory.V.AlgebraTools.lam P c j * MvPolynomial.C (m c) ∈ M0
      refine Ideal.sub_mem _ (Ideal.mem_map_of_mem _ ?_) (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_))
      · simpa using hcot.mem (Sum.inr j)
      · simpa using hcot.mem (Sum.inr c)
  have hprime := UpperTheory.V.AlgebraTools.chartIdeal_localization_isPrime P ι z m hcot c Q hMQ
  have hsat : ∀ x, algebraMap (MvPolynomial ι P) (Localization.AtPrime Q) x ∈
      Ideal.map (algebraMap (MvPolynomial ι P) (Localization.AtPrime Q)) (chartIdeal z m c) →
      ∃ t ∉ Q, t * x ∈ chartIdeal z m c := by
    intro x hx
    obtain ⟨t, ht, htx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := Q.primeCompl)
      (S := Localization.AtPrime Q) (chartIdeal z m c) x).mp hx
    exact ⟨t, ht, htx⟩
  intro f hf
  obtain ⟨s, hs, hsf⟩ := hf
  have hmem := Ideal.mem_map_of_mem (algebraMap (MvPolynomial ι P) (Localization.AtPrime Q)) hsf
  rw [map_mul] at hmem
  rcases hprime.mem_or_mem hmem with h | h
  · exfalso
    obtain ⟨t, ht, hts⟩ := hsat s h
    rcases hM0.mem_or_mem (hchartM hts) with h' | h'
    · exact ht (hMQ h')
    · exact hs h'
  · obtain ⟨t, ht, htf⟩ := hsat _ h
    have h0 : ψ (t * MvPolynomial.C f) = 0 := hker htf
    rw [map_mul, hψC] at h0
    have hu : IsUnit (ψ t) := by
      by_contra hn
      exact ht ((IsLocalRing.mem_maximalIdeal _).mpr hn)
    exact (RingHom.mem_ker).mpr ((hu.mul_right_eq_zero).mp h0)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetLocus
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetMin
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetKerIndep
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.generic_kernel_monotone
    (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι]
    (z : Matrix ι ι P) (m : ι → P)
    (h : CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m)) (c d : ι) :
    genKer z m c ≤ genKer z m d := by
  classical
  intro f hf
  haveI hQ : (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).IsPrime :=
    isPrime_map_C (ι := ι) (maximalIdeal P)
  set Q : Ideal (MvPolynomial ι P) := Ideal.map MvPolynomial.C (maximalIdeal P) with hQdef
  let L := Localization.AtPrime Q
  let J : Ideal L := Ideal.map (algebraMap (MvPolynomial ι P) L) (chartIdeal z m d)
  haveI hJ : J.IsPrime := chartIdeal_localization_isPrime P ι z m h d Q le_rfl
  haveI : IsLocalRing (L ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  let ψ : MvPolynomial ι P →+* L ⧸ J := (Ideal.Quotient.mk J).comp (algebraMap (MvPolynomial ι P) L)
  let φ : P →+* L ⧸ J := ψ.comp MvPolynomial.C
  have hJle : J ≤ maximalIdeal L := IsLocalRing.le_maximalIdeal hJ.ne_top
  have hψ : ∀ g ∈ chartIdeal z m d, ψ g = 0 := fun g hg =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hg)
  haveI : IsLocalHom φ := by
    constructor
    intro p hp
    by_contra hpu
    have hpm : p ∈ maximalIdeal P := (IsLocalRing.mem_maximalIdeal p).2 hpu
    have hC : (MvPolynomial.C p : MvPolynomial ι P) ∈ Q := Ideal.mem_map_of_mem _ hpm
    have hL : algebraMap (MvPolynomial ι P) L (MvPolynomial.C p) ∈ maximalIdeal L :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q _).2 hC
    obtain ⟨u, hu⟩ := hp
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑(u⁻¹) : L ⧸ J)
    have h1 : algebraMap (MvPolynomial ι P) L (MvPolynomial.C p) * y - 1 ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hy]
      have hu' : Ideal.Quotient.mk J (algebraMap (MvPolynomial ι P) L (MvPolynomial.C p)) = ↑u :=
        hu.symm
      rw [hu', Units.mul_inv, sub_self]
    have h3 : algebraMap (MvPolynomial ι P) L (MvPolynomial.C p) * y ∈ maximalIdeal L :=
      Ideal.mul_mem_right _ _ hL
    have h4 : (1 : L) ∈ maximalIdeal L := by
      have h5 := Ideal.sub_mem _ h3 (hJle h1)
      simpa using h5
    exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top ((Ideal.eq_top_iff_one _).2 h4)
  let l : ι → L ⧸ J := fun j => ψ (lam P d j)
  have hl : l d = 1 := by
    show ψ (lam P d d) = 1
    simp [lam]
  have hmul : (z.map φ).mulVec l = 0 := by
    funext i
    have hmem : (z.map MvPolynomial.C).mulVec (lam P d) i ∈ chartIdeal z m d :=
      Ideal.subset_span ⟨Sum.inl i, rfl⟩
    have h0 := hψ _ hmem
    rw [RingHom.map_mulVec, Matrix.map_map] at h0
    exact h0
  have hm : ∀ j, φ (m j) = l j * φ (m d) := by
    intro j
    by_cases hj : j = d
    · subst hj
      rw [hl, one_mul]
    · have hmem : MvPolynomial.C (m j) - lam P d j * MvPolynomial.C (m d) ∈ chartIdeal z m d :=
        Ideal.subset_span ⟨Sum.inr ⟨j, hj⟩, rfl⟩
      have h0 := hψ _ hmem
      rw [map_sub, map_mul, sub_eq_zero] at h0
      exact h0
  have hlamc : lam P d c ∉ Q := by
    rw [hQdef, MvPolynomial.mem_map_C_iff]
    intro hall
    by_cases hcd : c = d
    · have h0 := hall 0
      rw [show lam P d c = 1 from if_pos hcd, MvPolynomial.coeff_zero_one] at h0
      exact (IsLocalRing.maximalIdeal.isMaximal P).ne_top ((Ideal.eq_top_iff_one _).2 h0)
    · have h0 := hall (Finsupp.single c 1)
      rw [show lam P d c = MvPolynomial.X c from if_neg hcd, MvPolynomial.coeff_X, if_pos rfl] at h0
      exact (IsLocalRing.maximalIdeal.isMaximal P).ne_top ((Ideal.eq_top_iff_one _).2 h0)
  have hunitL : IsUnit (algebraMap (MvPolynomial ι P) L (lam P d c)) :=
    IsLocalization.map_units L (⟨lam P d c, hlamc⟩ : Q.primeCompl)
  have hunit : IsUnit (l c) := hunitL.map (Ideal.Quotient.mk J)
  set w : L ⧸ J := ↑hunit.unit⁻¹ with hwdef
  have hw : w * l c = 1 := hunit.val_inv_mul
  let l' : ι → L ⧸ J := fun j => w * l j
  have hl' : l' c = 1 := hw
  have hmul' : (z.map φ).mulVec l' = 0 := by
    funext i
    have h7 := congrFun hmul i
    simp only [l', Matrix.mulVec, dotProduct, Pi.zero_apply] at h7 ⊢
    simp_rw [mul_left_comm _ w]
    rw [← Finset.mul_sum, h7, mul_zero]
  have hm' : ∀ j, φ (m j) = l' j * φ (m c) := by
    intro j
    show φ (m j) = w * l j * φ (m c)
    rw [hm c, hm j]
    calc l j * φ (m d) = l j * φ (m d) * (w * l c) := by rw [hw, mul_one]
      _ = w * l j * (l c * φ (m d)) := by ring
  have hk := genKer_le_ker P ι z m h c (L ⧸ J) φ l' hl' hmul' hm' hf
  rw [RingHom.mem_ker] at hk
  have hfJ : algebraMap (MvPolynomial ι P) L (MvPolynomial.C f) ∈ J :=
    Ideal.Quotient.eq_zero_iff_mem.1 hk
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff Q.primeCompl L).1 hfJ
  simp only at hx
  rw [← map_mul, IsLocalization.eq_iff_exists Q.primeCompl L] at hx
  obtain ⟨⟨t, ht⟩, htx⟩ := hx
  simp only at htx
  refine ⟨t * s, ?_, ?_⟩
  · exact Q.primeCompl.mul_mem ht hs
  · have h6 : t * s * MvPolynomial.C f = t * a := by rw [← htx]; ring
    rw [h6]
    exact Ideal.mul_mem_left _ _ ha

theorem UpperTheory.V.AlgebraTools.genKer_eq :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ c d : ι, genKer z m c = genKer z m d := by
  intro P _ _ ι _ _ z m h c d
  exact le_antisymm (generic_kernel_monotone P ι z m h c d) (generic_kernel_monotone P ι z m h d c)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetKerPrime
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.genKer_isPrime :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ c : ι, (genKer z m c).IsPrime ∧ detIdeal z m ≤ genKer z m c := by
  intro P _ _ ι _ _ z m hind c
  haveI hQ : (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).IsPrime :=
    isPrime_map_C _
  haveI hJ := chartIdeal_localization_isPrime P ι z m hind c
    (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)) le_rfl
  have key : genKer z m c = Ideal.comap
      ((algebraMap (MvPolynomial ι P) (Localization.AtPrime
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)))).comp MvPolynomial.C)
      (Ideal.map (algebraMap (MvPolynomial ι P) (Localization.AtPrime
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)))) (chartIdeal z m c)) := by
    ext f
    rw [Ideal.mem_comap, RingHom.comp_apply,
      IsLocalization.algebraMap_mem_map_algebraMap_iff
        (Ideal.map (MvPolynomial.C : P →+* MvPolynomial ι P) (maximalIdeal P)).primeCompl]
    exact Iff.rfl
  have sub : ∀ f : P, MvPolynomial.C f ∈ chartIdeal z m c → f ∈ genKer z m c := by
    intro f hf
    rw [key, Ideal.mem_comap, RingHom.comp_apply]
    exact Ideal.mem_map_of_mem _ hf
  have gen : ∀ k, chartGen z m c k ∈ chartIdeal z m c := by
    intro k
    unfold chartIdeal
    exact Ideal.subset_span ⟨k, rfl⟩
  have hinl : ∀ i, ((z.map MvPolynomial.C).mulVec (lam P c)) i ∈ chartIdeal z m c :=
    fun i => gen (Sum.inl i)
  have hinr : ∀ j (h : j ≠ c),
      MvPolynomial.C (m j) - lam P c j * MvPolynomial.C (m c) ∈ chartIdeal z m c :=
    fun j h => gen (Sum.inr ⟨j, h⟩)
  have hdet : MvPolynomial.C z.det ∈ chartIdeal z m c := by
    have e : ((z.map MvPolynomial.C).adjugate.mulVec
        ((z.map MvPolynomial.C).mulVec (lam P c))) c = MvPolynomial.C z.det := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
        RingHom.map_det]
      simp [lam]
    rw [← e]
    show (∑ i, (z.map MvPolynomial.C).adjugate c i *
      ((z.map MvPolynomial.C).mulVec (lam P c)) i) ∈ _
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hinl i)
  refine ⟨by rw [key]; infer_instance, ?_⟩
  unfold detIdeal relIdeal
  refine sup_le (Ideal.span_le.2 ?_) (Ideal.span_le.2 (Set.singleton_subset_iff.2 (sub _ hdet)))
  rintro _ ⟨i, rfl⟩
  apply sub
  have e : MvPolynomial.C ((z.mulVec m) i) =
      ((z.map MvPolynomial.C).mulVec (lam P c)) i * MvPolynomial.C (m c) +
        ∑ j, MvPolynomial.C (z i j) * (MvPolynomial.C (m j) - lam P c j * MvPolynomial.C (m c)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul,
      mul_sub, Finset.sum_sub_distrib, mul_assoc]
    ring
  rw [e]
  refine add_mem (Ideal.mul_mem_right _ _ (hinl i)) (Ideal.sum_mem _ fun j _ => ?_)
  by_cases h : j = c
  · simp [h, lam]
  · exact Ideal.mul_mem_left _ _ (hinr j h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetField
open IsLocalRing

private theorem UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero {K : Type} [Field K] (V : ValuationSubring K)
    {ι : Type} [Fintype ι] [Nonempty ι] (w : ι → K) (hw : w ≠ 0) :
    ∃ c, w c ≠ 0 ∧ ∀ j, w j / w c ∈ V := by
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun j => V.valuation (w j))
    Finset.univ_nonempty
  have hwc : w c ≠ 0 := by
    intro h0
    apply hw
    funext j
    have hj := hc j (Finset.mem_univ j)
    rw [h0, map_zero] at hj
    exact (Valuation.zero_iff _).mp (le_antisymm hj zero_le')
  refine ⟨c, hwc, fun j => ?_⟩
  rw [← V.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (hc j (Finset.mem_univ j)) zero_le'

theorem UpperTheory.V.AlgebraTools.exists_kernel_vector :
    ∀ (K : Type) [Field K] (V : ValuationSubring K) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
      (z : Matrix ι ι K) (m : ι → K), z.mulVec m = 0 → z.det = 0 →
      ∃ (c : ι) (l : ι → K), l c = 1 ∧ (∀ j, l j ∈ V) ∧ z.mulVec l = 0 ∧ ∀ j, m j = l j * m c := by
  intro K _ V ι _ _ _ z m hm hdet
  have key : ∀ w : ι → K, z.mulVec w = 0 → ∀ c, w c ≠ 0 →
      z.mulVec (fun j => w j / w c) = 0 := by
    intro w hw c _
    have e : (fun j => w j / w c) = (w c)⁻¹ • w := by
      funext j
      simp [div_eq_inv_mul]
    rw [e, Matrix.mulVec_smul, hw, smul_zero]
  by_cases h0 : m = 0
  · obtain ⟨w, hw, hzw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    obtain ⟨c, hc, hV⟩ := UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero V w hw
    exact ⟨c, fun j => w j / w c, div_self hc, hV, key w hzw c hc, fun j => by simp [h0]⟩
  · obtain ⟨c, hc, hV⟩ := UpperTheory.V.AlgebraTools.exists_div_mem_valuationSubring_of_ne_zero V m h0
    exact ⟨c, fun j => m j / m c, div_self hc, hV, key m hm c hc,
      fun j => (div_mul_cancel₀ _ hc).symm⟩
end

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.exists_least_prime_detIdeal :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) → Nonempty ι →
      ∃ K : Ideal P, K.IsPrime ∧ detIdeal z m ≤ K ∧ ∀ Q : Ideal P, Q.IsPrime → detIdeal z m ≤ Q → K ≤ Q := by
  intro P _ _ ι _ _ z m h hι
  obtain ⟨c0⟩ := id hι
  refine ⟨genKer z m c0, (genKer_isPrime P ι z m h c0).1, (genKer_isPrime P ι z m h c0).2, ?_⟩
  intro Q hQ hle
  let f : P →+* FractionRing (P ⧸ Q) :=
    (algebraMap (P ⧸ Q) (FractionRing (P ⧸ Q))).comp (Ideal.Quotient.mk Q)
  have hf : ∀ x, f x = 0 ↔ x ∈ Q := by
    intro x
    simp only [f, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective (P ⧸ Q) (FractionRing (P ⧸ Q))),
      Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have h1 : (z.map f).mulVec (fun j => f (m j)) = 0 := by
    funext i
    have hi : z.mulVec m i ∈ Q :=
      hle (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
    have h2 := (hf _).2 hi
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Matrix.mulVec, dotProduct, map_sum, map_mul] using h2
  have h2 : (z.map f).det = 0 := by
    have hi : z.det ∈ Q := hle (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have h3 := (hf _).2 hi
    rw [RingHom.map_det] at h3
    exact h3
  obtain ⟨c, l, hc, hl, hz, hm⟩ := exists_kernel_vector _ V ι (z.map f) (fun j => f (m j)) h1 h2
  haveI : IsLocalRing V.toSubring := inferInstanceAs (IsLocalRing V)
  have hk := genKer_le_ker P ι z m h c V.toSubring (f.codRestrict V.toSubring hV)
    (fun j => ⟨l j, hl j⟩) (Subtype.ext hc) (by
      funext i
      apply Subtype.ext
      have h4 := congrFun hz i
      simpa [Matrix.mulVec, dotProduct] using h4) (fun j => Subtype.ext (hm j))
  rw [genKer_eq P ι z m h c0 c]
  intro x hx
  have h5 := hk hx
  rw [RingHom.mem_ker] at h5
  exact (hf x).1 (congrArg Subtype.val h5)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetDim
open IsLocalRing UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.dim_quot_le_of_primes {P : Type} [CommRing P] (I J : Ideal P)
    (h : ∀ p : Ideal P, p.IsPrime → J ≤ p → I ≤ p) :
    ringKrullDim (P ⧸ J) ≤ ringKrullDim (P ⧸ I) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient]
  have hsub : PrimeSpectrum.zeroLocus (R := P) (J : Set P) ⊆ PrimeSpectrum.zeroLocus (I : Set P) := by
    intro q hq
    rw [PrimeSpectrum.mem_zeroLocus] at hq ⊢
    exact h q.asIdeal q.isPrime hq
  exact Order.krullDim_le_of_strictMono (Set.inclusion hsub) (fun a b hab => hab)

theorem UpperTheory.V.AlgebraTools.dim_relIdeal_le :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ringKrullDim (P ⧸ relIdeal z m) + (Fintype.card ι : ℕ) ≤ ringKrullDim P := by
  classical
  intro P _ _ ι _ _ z m hx
  set x : ι × ι ⊕ ι → P := Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m with hxdef
  let K : Ideal P := Ideal.span (Set.range x)
  let g : ι × ι → P := fun ij => z ij.1 ij.2 - if ij.1 = ij.2 then m ij.1 else 0
  let G : Ideal P := Ideal.span (Set.range g)
  have hreg := (regular_quotient_cotInd P (ι × ι ⊕ ι) x hx).2.1
  rw [Fintype.card_sum, Fintype.card_prod] at hreg
  have hA : ringKrullDim (P ⧸ relIdeal z m ⊔ G) ≤ ringKrullDim (P ⧸ K) := by
    apply dim_quot_le_of_primes
    intro q hq hle
    have hrel : relIdeal z m ≤ q := le_trans le_sup_left hle
    have hG : G ≤ q := le_trans le_sup_right hle
    have hg : ∀ ij, g ij ∈ q := fun ij => hG (Ideal.subset_span ⟨ij, rfl⟩)
    have hm : ∀ i, m i ∈ q := by
      intro i
      have h1 : z.mulVec m i ∈ q := hrel (Ideal.subset_span ⟨i, rfl⟩)
      have h2 : m i * m i = z.mulVec m i - ∑ j, g (i, j) * m j := by
        simp only [g, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring
      have h3 : m i * m i ∈ q := by
        rw [h2]
        exact q.sub_mem h1 (q.sum_mem fun j _ => q.mul_mem_right _ (hg (i, j)))
      rcases hq.mem_or_mem h3 with h | h <;> exact h
    rw [Ideal.span_le]
    rintro _ ⟨(⟨i, j⟩ | i), rfl⟩
    · have h4 : z i j = g (i, j) + (if i = j then m i else 0) := by simp [g]
      show z i j ∈ q
      rw [h4]
      refine q.add_mem (hg _) ?_
      split_ifs
      · exact hm i
      · exact q.zero_mem
    · exact hm i
  have hB : ringKrullDim (P ⧸ relIdeal z m) ≤
      ringKrullDim (P ⧸ K) + ((Fintype.card ι * Fintype.card ι : ℕ) : WithBot ℕ∞) := by
    let Gb : Ideal (P ⧸ relIdeal z m) := G.map (Ideal.Quotient.mk _)
    have hsf : Gb.spanFinrank ≤ Fintype.card ι * Fintype.card ι := by
      have e : Gb = Ideal.span (Set.range (Ideal.Quotient.mk (relIdeal z m) ∘ g)) := by
        simp only [Gb, G, Ideal.map_span, Set.range_comp]
      rw [e]
      refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
      rw [← Set.image_univ, ← Finset.coe_univ]
      exact (Set.ncard_coe_finset _ ▸ Set.ncard_image_le (Finset.finite_toSet _)).trans (by simp)
    have hdim : ringKrullDim (P ⧸ relIdeal z m) ≤
        ringKrullDim ((P ⧸ relIdeal z m) ⧸ Gb) + Gb.spanFinrank := by
      rw [ringKrullDim_le_iff_isMaximal_height_le]
      intro M hM
      apply height_le_ringKrullDim_quotient_add_spanFinrank
      rw [Ideal.map_le_iff_le_comap]
      have hc : Ideal.comap (Ideal.Quotient.mk (relIdeal z m)) M = maximalIdeal P :=
        IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
      rw [hc, Ideal.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      have hz : z i j ∈ maximalIdeal P := hx.mem (Sum.inl (i, j))
      have hmi : m i ∈ maximalIdeal P := hx.mem (Sum.inr i)
      show z i j - (if i = j then m i else 0) ∈ maximalIdeal P
      refine (maximalIdeal P).sub_mem hz ?_
      split_ifs
      · exact hmi
      · exact (maximalIdeal P).zero_mem
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup (relIdeal z m) G)] at hdim
    exact hdim.trans (add_le_add hA (by exact_mod_cast hsf))
  rw [← hreg]
  refine (add_le_add hB le_rfl).trans (le_of_eq ?_)
  rw [add_assoc]
  norm_cast
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDetAdj
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.det_mem_of_rel :
    ∀ (P : Type) [CommRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P)
      (Q : Ideal P), Q.IsPrime → relIdeal z m ≤ Q → (∃ j, m j ∉ Q) → detIdeal z m ≤ Q := by
  intro P _ ι _ _ z m Q hQ hrel ⟨j, hj⟩
  have hzm : ∀ k, z.mulVec m k ∈ Q := fun k => hrel (Ideal.subset_span ⟨k, rfl⟩)
  have hdet : z.det * m j ∈ Q := by
    have h1 : (z.adjugate.mulVec (z.mulVec m)) j = z.det * m j := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp
    rw [← h1, Matrix.mulVec, dotProduct]
    exact Q.sum_mem fun k _ => Q.mul_mem_left _ (hzm k)
  have hd : z.det ∈ Q := (hQ.mem_or_mem hdet).resolve_right hj
  exact sup_le hrel ((Ideal.span_singleton_le_iff_mem _).mpr hd)
end

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.le_of_detIdeal_le :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ Z : Ideal P, Z.IsPrime → relIdeal z m ≤ Z → (∃ j, m j ∉ Z) →
      ringKrullDim P ≤ ringKrullDim (P ⧸ Z) + (Fintype.card ι : ℕ) →
      ∀ Q : Ideal P, Q.IsPrime → detIdeal z m ≤ Q → Z ≤ Q := by
  intro P _ _ ι _ _ z m hc Z hZ hrel hm hdim Q hQ hdet
  have hdZ : detIdeal z m ≤ Z := det_mem_of_rel P ι z m Z hZ hrel hm
  by_cases hne : Nonempty ι
  swap
  · exfalso
    have : IsEmpty ι := not_nonempty_iff.1 hne
    apply hQ.ne_top
    rw [eq_top_iff]
    refine le_trans ?_ hdet
    simp [detIdeal, Matrix.det_isEmpty]
  obtain ⟨K, hK, hKdet, hKmin⟩ := exists_least_prime_detIdeal P ι z m hc hne
  haveI := hK
  haveI := hZ
  refine le_trans ?_ (hKmin Q hQ hdet)
  have hKZ : K ≤ Z := hKmin Z hZ hdZ
  by_contra hnot
  obtain ⟨x, hxZ, hxK⟩ := Set.not_subset.1 hnot
  have hrK : relIdeal z m ≤ K :=
    le_trans (le_sup_left : relIdeal z m ≤ relIdeal z m ⊔ Ideal.span {z.det}) hKdet
  have h1 : ringKrullDim (P ⧸ Z) + 1 ≤ ringKrullDim (P ⧸ K) := by
    refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hKZ)
      (Ideal.Quotient.factor_surjective hKZ) (r := Ideal.Quotient.mk K x) ?_ ?_
    · exact mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    · simpa [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] using hxZ
  have h2 : ringKrullDim (P ⧸ K) ≤ ringKrullDim (P ⧸ relIdeal z m) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hrK) (Ideal.Quotient.factor_surjective hrK)
  have h3 := dim_relIdeal_le P ι z m hc
  have hfin : ringKrullDim (P ⧸ Z) < ⊤ := lt_of_le_of_lt (ringKrullDim_quotient_le Z) ringKrullDim_lt_top
  have hbot : ringKrullDim (P ⧸ Z) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial
  have h12 := h1.trans h2
  have key : ringKrullDim (P ⧸ Z) + 1 + (Fintype.card ι : ℕ) ≤ ringKrullDim (P ⧸ Z) + (Fintype.card ι : ℕ) := by
    refine le_trans ?_ (h3.trans hdim)
    gcongr
  generalize ringKrullDim (P ⧸ Z) = d at key hfin hbot
  generalize Fintype.card ι = c at key
  induction d using WithBot.recBotCoe with
  | bot => exact hbot rfl
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => simp at hfin
    | coe d =>
      norm_cast at key
      omega
end

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.under_le_of_det_mem :
    ∀ (P : Type) [CommRing P] [IsRegularLocalRing P] (ι : Type) [Fintype ι] [DecidableEq ι] (z : Matrix ι ι P) (m : ι → P),
      CotInd P (Sum.elim (fun ij : ι × ι => z ij.1 ij.2) m) →
      ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] [Algebra.IsIntegral B A] [FaithfulSMul B A]
      (π : P →+* A), Function.Surjective π → relIdeal z m ≤ RingHom.ker π →
      ∀ Z : Ideal B, Z.IsPrime → ringKrullDim P ≤ ringKrullDim (B ⧸ Z) + (Fintype.card ι : ℕ) →
      (∀ Z' : Ideal A, Z'.IsPrime → Z'.comap (algebraMap B A) = Z → ∃ j, π (m j) ∉ Z') →
      ∀ Q' : Ideal A, Q'.IsPrime → π z.det ∈ Q' → Z ≤ Q'.comap (algebraMap B A) := by
  intro P _ _ ι _ _ z m hC B A _ _ _ _ _ π hπ hrel Z hZ hdim hm Q' hQ' hdet
  haveI := hZ
  have hinj : Function.Injective (algebraMap B A) := FaithfulSMul.algebraMap_injective B A
  obtain ⟨Z', -, hZ'p, hZ'c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral Z (⊥ : Ideal A) (by
    rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]; exact bot_le)
  change Ideal.comap (algebraMap B A) Z' = Z at hZ'c
  haveI := hZ'p
  haveI := hQ'
  obtain ⟨j, hj⟩ := hm Z' hZ'p hZ'c
  have hker : RingHom.ker ((Ideal.Quotient.mk Z').comp π) = Z'.comap π := by
    ext x
    simp [Ideal.Quotient.eq_zero_iff_mem]
  have e : P ⧸ Z'.comap π ≃+* A ⧸ Z' :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective
      (Ideal.Quotient.mk_surjective.comp hπ))
  have hdimZ : ringKrullDim (P ⧸ Z'.comap π) = ringKrullDim (B ⧸ Z) := by
    rw [ringKrullDim_eq_of_ringEquiv e,
      ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral (A := B) (B := A) Z', hZ'c]
  have hrelQ : ∀ I : Ideal A, relIdeal z m ≤ I.comap π := fun I x hx => by
    have h0 : π x = 0 := RingHom.mem_ker.mp (hrel hx)
    simp [Ideal.mem_comap, h0]
  have key := le_of_detIdeal_le P ι z m hC (Z'.comap π) inferInstance (hrelQ Z') ⟨j, hj⟩
    (by rw [hdimZ]; exact hdim) (Q'.comap π) inferInstance (by
      show relIdeal z m ⊔ Ideal.span {z.det} ≤ _
      refine sup_le (hrelQ Q') ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hdet)
  have hle : Z' ≤ Q' := by
    intro a ha
    obtain ⟨x, rfl⟩ := hπ a
    exact key ha
  rw [← hZ'c]
  exact Ideal.comap_mono hle
