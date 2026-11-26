module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocQuot

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


open Classical in
set_option synthInstance.maxHeartbeats 400000 in
theorem SemilocalLength.proof (h1 : SemilocalLengthSum.Statement.{u})
    (h2 : FibreRelDim.Statement.{u}) (h3 : DivCycleMinimal.Statement.{u})
    (h4 : ConeLocalLength.Statement.{u}) : SemilocalLength.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn c a h ha hh haP W hW hWn hPW hhW M hM1 hM0 α hα
  have := hP'.isPrime
  obtain ⟨d, hd⟩ := exists_relDegFn (F := F) j (ι' := ι')
  obtain ⟨β, hβ⟩ := exists_fibreLift j P' W α
  obtain ⟨hfin, hlen⟩ := h1 F K K' j ι' P' hP' n hP'n hPn c a h ha hh haP W hW hWn hPW hhW d
    (fun W' hW' _ => hd W' hW') α hα β hβ
  have key : ∀ W' ∈ hfin.toFinset.filter (fun W' => (rename (blockIncl j ι') a) ∈ W'), ∃ hW' : IsMultiProjPrime W',
      haveI := hW'.isPrime
      Ring.ord (degZeroLoc P' {W'}) (β W') = multAt (P' ⊔ Ideal.span {(rename (blockIncl j ι') a)}) W' ∧
        multAt (P' ⊔ Ideal.span {(rename (blockIncl j ι') a)}) W' ≠ ⊤ ∧
        divCycle P' (rename (blockIncl j ι') a) W' = ((multAt (P' ⊔ Ideal.span {(rename (blockIncl j ι') a)}) W').toNat : ℤ) ∧ M W' = d W' := by
    intro W' hT
    obtain ⟨hWf, haW'⟩ := Finset.mem_filter.mp hT
    have hWf' := hfin.mem_toFinset.mp hWf
    obtain ⟨hW'p, hPW', hcW'⟩ := id hWf'
    have := hW'p.isPrime
    have hmin := h3 F K' ι' P' hP'.isPrime n hP'n (rename (blockIncl j ι') a) haP W' hW'p.isPrime
      (h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW W' hWf')
      (sup_le hPW' ((Ideal.span_singleton_le_iff_mem _).mpr haW'))
    have hcone := h4 F K' ι' P' hP' W' hW'p hPW' (Function.extend j c 0) (rename (blockIncl j ι') a)
      (rename (blockIncl j ι') h) (isMultiHomog_rename j ι' ha) (isMultiHomog_rename j ι' hh)
      (fun hm => hhW (by rw [← hcW']; exact hm)) (β W')
      (by rw [hβ W' hWf', hα, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap])
    refine ⟨hW'p, hcone.symm, hmin.2, ?_, by rw [hM1 W' hW'p hcW', hd W' hW'p]⟩
    unfold divCycle
    rw [dite_eq_left ⟨hmin.1, hW'p.relevant⟩]
  refine ⟨∑ W' ∈ hfin.toFinset.filter (fun W' => (rename (blockIncl j ι') a) ∈ W'),
    (Ring.ord (degZeroLoc P' {W'}) (β W')).toNat * d W', ?_, ?_⟩
  · rw [hlen, Nat.cast_sum]
    refine Finset.sum_congr rfl fun W' hT => ?_
    obtain ⟨hW'p, hord, hfin', -, -⟩ := key W' hT
    rw [Nat.cast_mul, ENat.natCast_toNat (hord ▸ hfin')]
  · unfold cycEval
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset.filter (fun W' => (rename (blockIncl j ι') a) ∈ W')) _ ?_,
      Nat.cast_sum]
    · refine Finset.sum_congr rfl fun W' hT => ?_
      obtain ⟨hW'p, hord, -, hdiv, hMd⟩ := key W' hT
      rw [hdiv, hMd, hord]
      push_cast
      ring
    · intro W' hW'
      have hdc : divCycle P' (rename (blockIncl j ι') a) W' ≠ 0 := left_ne_zero_of_mul (Function.mem_support.mp hW')
      have hMW : M W' ≠ 0 := right_ne_zero_of_mul (Function.mem_support.mp hW')
      obtain ⟨hWp, -⟩ := DivCycleSupport.proof F K' ι' P' hP' n hP'n (Function.extend j c 0) (rename (blockIncl j ι') a)
        (isMultiHomog_rename j ι' ha) haP W' hdc
      have hmin : W' ∈ (P' ⊔ Ideal.span {(rename (blockIncl j ι') a)}).minimalPrimes := by
        by_contra hn
        exact hdc (by unfold divCycle; rw [dite_eq_right (fun hc => hn hc.1)])
      have hc : contractPrime j W' = W := by
        by_contra hne
        exact hMW (hM0 W' hne)
      exact Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr ⟨hWp, le_sup_left.trans hmin.1.2, hc⟩,
        hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocLocal.proof (h : DegZeroLocQuot.Statement.{u}) : DegZeroLocLocal.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have hWp : W.IsPrime := hW.isPrime
  have hne : ∀ g : MRing ι F, g ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 :=
    fun g hg => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  have hrep : ∀ x : degZeroLoc P {W}, ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧
      IsMultiHomog g b ∧ g ∉ P ∧ g ∉ W ∧
      (x : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) := fun x => by
    obtain ⟨b, f, g, hf, hg, hgP, hgW, hx⟩ := h F K ι P {W}
      (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hWp) x x.2
    exact ⟨b, f, g, hf, hg, hgP, hgW W (Set.mem_singleton W), hx⟩

  have hnon : ∀ (x : degZeroLoc P {W}) (f g : MRing ι F), g ∉ W → f ∈ W →
      (x : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) → ¬ IsUnit x := by
    intro x f g hgW hfW hx hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨b', f', g', -, -, hg'P, hg'W, hy'⟩ := hrep y
    have hgP : g ∉ P := fun hg => hgW (hPW hg)
    have h1 : ((x * y : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) = 1 := by
      rw [hy]; rfl
    rw [Subalgebra.coe_mul, hx, hy', div_mul_div_comm,
      div_eq_one_iff_eq (mul_ne_zero (hne g hgP) (hne g' hg'P)), ← map_mul, ← map_mul,
      ← map_mul, ← map_mul] at h1
    have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ h1)
    have h3 : g * g' ∈ W := by
      have := W.sub_mem (W.mul_mem_right f' hfW) (hPW h2)
      rwa [sub_sub_cancel] at this
    rcases hWp.mem_or_mem h3 with h4 | h4
    exacts [hgW h4, hg'W h4]

  have hunit : ∀ (x : degZeroLoc P {W}) (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b →
      IsMultiHomog g b → g ∉ P → f ∉ W →
      (x : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) → IsUnit x := by
    intro x b f g hf hg hgP hfW hx
    have hfP : f ∉ P := fun h' => hfW (hPW h')
    have hmem := div_mem_degZeroLoc P {W} hg hf hfP
      (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hfW)
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, Subalgebra.coe_one, hx, div_mul_div_comm, mul_comm (algebraMap _ _ _),
      div_self (mul_ne_zero (hne g hgP) (hne f hfP))]
  have : Nontrivial (degZeroLoc P {W}) :=
    ⟨⟨0, 1, fun e => zero_ne_one (congrArg Subtype.val e)⟩⟩
  refine IsLocalRing.of_nonunits_add ?_
  intro a c ha hc
  obtain ⟨b, f, g, hf, hg, hgP, hgW, hx⟩ := hrep a
  obtain ⟨b', f', g', hf', hg', hg'P, hg'W, hy⟩ := hrep c
  have hfW : f ∈ W := by
    by_contra hfW
    exact (mem_nonunits_iff.mp ha) (hunit a b f g hf hg hgP hfW hx)
  have hf'W : f' ∈ W := by
    by_contra hf'W
    exact (mem_nonunits_iff.mp hc) (hunit c b' f' g' hf' hg' hg'P hf'W hy)
  refine mem_nonunits_iff.mpr (hnon (a + c) (f * g' + g * f') (g * g') (fun h5 => ?_)
    (W.add_mem (W.mul_mem_right g' hfW) (W.mul_mem_left g hf'W)) ?_)
  · rcases hWp.mem_or_mem h5 with h6 | h6
    exacts [hgW h6, hg'W h6]
  · rw [Subalgebra.coe_add, hx, hy, div_add_div _ _ (hne g hgP) (hne g' hg'P)]
    set_option synthInstance.maxHeartbeats 200000 in
      simp only [map_add, map_mul]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocNoetherian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocNoetherian.proof (h : DegZeroLocQuot.Statement.{u}) :
    DegZeroLocNoetherian.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  let φ : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P) :=
    (IsScalarTower.toAlgHom F (MRing ι F ⧸ P) _).comp (Ideal.Quotient.mkₐ F P)
  have hφ : ∀ f, f ∉ P → φ f ≠ 0 := fun f hf h0 => hf (by
    rwa [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at h0)
  choose v hv using hW.relevant
  let e : MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P) :=
    aeval fun x => φ (X x) / φ (X ⟨x.1, v x.1⟩)
  let c : (K → ℕ) → MRing ι F := fun b => ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ b k
  have hcW : ∀ b, c b ∉ W := by
    intro b
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, -, hk⟩
    exact hv k (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hk)
  have hc : ∀ b, IsMultiHomog (c b) b := by
    intro b
    have hprod := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
      (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ b k) (fun k => b k • blockWeight ι ⟨k, v k⟩)
      (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) _).pow (b k))
    have hb : (∑ k, b k • blockWeight ι ⟨k, v k⟩) = b := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hb] at hprod
    exact hprod
  have hcadd : ∀ b b', c (b + b') = c b * c b' := fun b b' => by
    simp only [c, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

  have hmono : ∀ m : (Σ k, ι k) →₀ ℕ,
      φ (monomial m 1) = e (monomial m 1) * φ (c (Finsupp.weight (blockWeight ι) m)) := by
    intro m
    refine Finsupp.induction m ?_ ?_
    · simp [c]
    · intro x n m _ _ ih
      have hs : φ (monomial (Finsupp.single x n) 1) = e (monomial (Finsupp.single x n) 1) *
          φ (c (Finsupp.weight (blockWeight ι) (Finsupp.single x n))) := by
        rw [Finsupp.weight_single, ← X_pow_eq_monomial, map_pow, map_pow, aeval_X]
        have hcs : c (n • blockWeight ι x) = (X ⟨x.1, v x.1⟩ : MRing ι F) ^ n := by
          simp only [c, blockWeight]
          rw [Finset.prod_eq_single x.1]
          · simp
          · intro k _ hk
            simp [hk]
          · simp
        rw [hcs, map_pow, ← mul_pow, div_mul_cancel₀ _ (hφ _ fun hm => hv x.1 (hPW hm))]
      rw [← mul_one (1 : F), ← monomial_mul, map_mul, map_mul, ih, map_add (f := _), hcadd, map_mul, hs]
      ring

  have hhom : ∀ (b : K → ℕ) (f : MRing ι F), IsMultiHomog f b → φ f = e f * φ (c b) := by
    intro b f hf
    conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hw : Finsupp.weight (blockWeight ι) m = b := hf (mem_support_iff.mp hm)
    have hmon : monomial m (AddMonoidAlgebra.coeff f m) = AddMonoidAlgebra.coeff f m • monomial m (1 : F) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, map_smul, hmono, hw, smul_mul_assoc]
  have hle : e.range ≤ degZeroLoc P {W} := by
    rw [← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩
    exact div_mem_degZeroLoc P {W} (isWeightedHomogeneous_X F (blockWeight ι) x)
      (isWeightedHomogeneous_X F (blockWeight ι) ⟨x.1, v x.1⟩) (fun hm => hv x.1 (hPW hm))
      (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hv x.1)
  have : Algebra.FiniteType F e.range :=
    Algebra.FiniteType.of_surjective e.rangeRestrict e.rangeRestrict_surjective
  have _ : IsNoetherianRing e.range := Algebra.FiniteType.isNoetherianRing F e.range
  let _ : Algebra e.range (degZeroLoc P {W}) := (Subalgebra.inclusion hle).toAlgebra
  let M : Submonoid e.range :=
    (IsUnit.submonoid (degZeroLoc P {W})).comap (algebraMap e.range (degZeroLoc P {W}))
  have hloc : IsLocalization M (degZeroLoc P {W}) := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun z => ?_,
      fun {x y} hxy => ⟨1, by rw [Subalgebra.inclusion_injective hle hxy]⟩⟩
    obtain ⟨b, f, g, hf, hg, hgP, hgW, hz⟩ := h F K ι P {W}
      (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hW.isPrime) z.1 z.2
    have hgW' : g ∉ W := hgW W rfl
    have hcb : φ (c b) ≠ 0 := hφ _ fun hm => hcW b (hPW hm)
    have hz' : (z : FractionRing (MRing ι F ⧸ P)) = φ f / φ g := hz
    have heg : e g ≠ 0 := by
      intro h0
      apply hφ g hgP
      rw [hhom b g hg, h0, zero_mul]
    have hinv : (e g)⁻¹ ∈ degZeroLoc P {W} := by
      have hq : (e g)⁻¹ = φ (c b) / φ g := by
        rw [hhom b g hg]
        field_simp
      rw [hq]
      exact div_mem_degZeroLoc P {W} (hc b) hg hgP
        (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hgW')
    have hunit : (⟨e g, g, rfl⟩ : e.range) ∈ M :=
      isUnit_iff_exists_inv.mpr ⟨⟨(e g)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ heg)⟩
    refine ⟨(⟨e f, f, rfl⟩, ⟨⟨e g, g, rfl⟩, hunit⟩), Subtype.ext ?_⟩
    change (z : FractionRing (MRing ι F ⧸ P)) * e g = e f
    rw [hz', hhom b f hf, hhom b g hg]
    field_simp
  exact IsLocalization.isNoetherianRing M _ inferInstance

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
