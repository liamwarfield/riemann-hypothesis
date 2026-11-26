module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalLengthSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option synthInstance.maxHeartbeats 400000 in
theorem SemilocalLengthSum.proof (h1 : FibreFinite.Statement.{u})
    (h2 : SemilocalFiniteRank.Statement.{u}) (h3 : DegZeroLocalRing.Statement.{u})
    (h4 : FiniteAlgebraLengthSum.Statement.{u}) (h5 : SemilocalMaxIdeals.Statement.{u}) :
    SemilocalLengthSum.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn c a h ha hh haP W hW hWn hPW hhW d hd α hα β hβ
  have := hP'.isPrime
  have hfin := h1 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  refine ⟨hfin, ?_⟩
  have := (h2 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW).1
  have := (h3 F K (fun k => ι' (j k)) (contractPrime j P') (isMultiProjPrime_contractPrime j ι' hP')
    W hW hPW).1.2
  obtain ⟨𝔪, h𝔪, hinj, hcov, hloc⟩ := h5 F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  let : Fintype (fibrePrimes j P' W) := hfin.fintype
  let alg : ∀ W' : fibrePrimes j P' W,
      Algebra (degZeroLoc P' (fibrePrimes j P' W)) (degZeroLoc P' {W'.1}) :=
    fun W' => degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)
  rw [h4 _ _ _ 𝔪 h𝔪 hinj hcov (fun W' => degZeroLoc P' {W'.1}) (fun W' => (hloc W').1) α,
    Finset.sum_filter, Finset.sum_subtype hfin.toFinset (fun _ => Set.Finite.mem_toFinset hfin)]
  refine Finset.sum_congr rfl fun W' _ => ?_
  obtain ⟨hW'p, -, hW'c⟩ := W'.2
  have := hW'p.isPrime
  have hb : algebraMap _ (degZeroLoc P' {W'.1}) (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W)) α) = β W'.1 :=
    Subtype.ext (hβ W'.1 W'.2).symm
  rw [hb, (hloc W').2, ← hd W'.1 hW'p hW'c]
  split_ifs with haW'
  · rfl
  rw [Ring.ord_of_isUnit, zero_mul]
  have hne : ∀ g, g ∉ contractPrime j P' → algebraMap (MRing ι' F ⧸ P')
      (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' (rename (blockIncl j ι') g)) ≠ 0 :=
    fun g hg => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact hg
  have hhP : h ∉ contractPrime j P' := fun hm => hhW (hPW hm)
  refine IsUnit.of_mul_eq_one ⟨_, div_mem_degZeroLoc P' {W'.1} (isMultiHomog_rename j ι' hh)
    (isMultiHomog_rename j ι' ha) haP (fun W'' hW'' => (Set.mem_singleton_iff.mp hW'') ▸ haW')⟩ ?_
  apply Subtype.ext
  change (β W'.1 : FractionRing (MRing ι' F ⧸ P')) * _ = 1
  rw [hβ W'.1 W'.2, hα, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]
  have := hne h hhP
  have := hne a haP
  field_simp

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarInj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem ConeVarInj.proof (hNum : ConeVarNumerator.Statement.{u}) : ConeVarInj.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨B, g, h, -, hgW, hh, hc, hφ⟩ := hNum F K ι P hP W hW hPW v hv p

  have hu : ∀ d : K →₀ ℕ, IsMultiHomog (∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k) ⇑d := fun d => by
    unfold IsMultiHomog
    convert IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, v k⟩)
      (fun k _ => (isWeightedHomogeneous_X F (blockWeight ι) ⟨k, v k⟩).pow (d k)) using 1
    ext k
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  have huW : ∀ d : K →₀ ℕ, ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k ∉ W := fun d => by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨k, -, hk⟩
    exact hv k (hW.isPrime.mem_of_pow_mem _ hk)
  have hN : ∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k ∈ P := by
    have hg0 : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact fun hg => hgW (hPW hg)
    rw [hp, ZeroMemClass.coe_zero, eq_comm, div_eq_zero_iff, or_iff_left hg0,
      IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hφ
    exact hφ
  refine MvPolynomial.ext _ _ fun d => ?_
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hd
  have hcomp := hP.multiHomog _ hN (B + ⇑d)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single d] at hcomp
  · rw [((hh d).mul (hu d)).weightedHomogeneousComponent_same] at hcomp
    have hhd : h d ∈ P := (hP.isPrime.mem_or_mem hcomp).resolve_right fun hm => huW d (hPW hm)
    apply hd
    apply Subtype.ext
    rw [hc d, Ideal.Quotient.eq_zero_iff_mem.mpr hhd, map_zero, zero_div]
    rfl
  · intro d' _ hne
    refine ((hh d').mul (hu d')).weightedHomogeneousComponent_ne _ fun heq => hne ?_
    ext k
    have := congrFun heq k
    simp only [Pi.add_apply] at this
    omega
  · exact fun hn => absurd (mem_support_iff.mpr hd) hn

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem module_finite_of_forall_mem_span {A A' B L : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing A'] [CommRing B] [Algebra A B] [CommRing L] [Algebra A' L] (φ : A →+* A')
    (hφ : Function.Surjective φ) (ψ : B →+* L) (hψ : Function.Injective ψ)
    (hcomm : ∀ a b, ψ (algebraMap A B a * b) = algebraMap A' L (φ a) * ψ b) (s : Finset L)
    (h : ∀ b, ψ b ∈ Submodule.span A' (s : Set L)) : Module.Finite A B := by
  let _ : Algebra A L := ((algebraMap A' L).comp φ).toAlgebra
  have hspan : ∀ x ∈ Submodule.span A' (s : Set L), x ∈ Submodule.span A (s : Set L) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add _ _ _ _ hy hz => exact add_mem hy hz
    | smul a' y _ hy =>
      obtain ⟨a, rfl⟩ := hφ a'
      have e : φ a • y = a • y := by rw [Algebra.smul_def, Algebra.smul_def]; rfl
      rw [e]
      exact Submodule.smul_mem _ a hy
  let f : B →ₗ[A] L :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := fun a b => by rw [Algebra.smul_def, hcomm]; rfl }
  have : IsNoetherian A (Submodule.span A (s : Set L)) :=
    isNoetherian_span_of_finite A s.finite_toSet
  exact Module.Finite.of_injective (f.codRestrict _ fun b => hspan _ (h b))
    fun b c hbc => hψ (congrArg Subtype.val hbc)

theorem SemilocalFinite.proof (h1 : SemilocalIntegral.Statement.{u})
    (h2 : LocalIntegralClosureFinite.Statement.{u}) (h3 : DegZeroLocNoetherian.Statement.{u}) :
    SemilocalFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hd' hd W hW hdW hle
  have := hP'.isPrime
  set A := degZeroLoc (contractPrime j P') {W}
  set B := degZeroLoc P' (fibrePrimes j P' W)
  set A' := A.map (contractFracMap j P')
  have : IsNoetherianRing A :=
    h3 F K (fun k => ι' (j k)) _ (isMultiProjPrime_contractPrime _ _ hP') W hW hle
  have hint : Algebra.IsIntegral A B := h1 F K K' j ι' P' hP' n hd' hd W hW hdW hle
  obtain ⟨s, -, hs⟩ := h2 F K K' j ι' P' hP' (hd.trans hd'.symm) W hW hle
  let φA : A →+* A' := (((contractFracMap j P').comp A.val).codRestrict A'
    (fun a => Subalgebra.mem_map.mpr ⟨a, a.2, rfl⟩)).toRingHom
  have hφA : Function.Surjective φA := fun a' => by
    obtain ⟨a, ha, hae⟩ := Subalgebra.mem_map.mp a'.2
    exact ⟨⟨a, ha⟩, Subtype.ext hae⟩
  refine module_finite_of_forall_mem_span φA hφA B.val.toRingHom Subtype.val_injective
    (fun _ _ => rfl) s fun b => ?_
  exact hs _ (mem_homFracDegZero_of_mem_degZeroLoc P' _ _ b.2)
    (IsIntegral.map_of_comp_eq φA B.val.toRingHom (RingHom.ext fun _ => rfl) (hint.isIntegral b))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocSeparate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocSeparate.proof : DegZeroLocSeparate.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P
  have := hP.isPrime
  intro W₁ hW₁ W₂ hW₂ hle
  obtain ⟨hW₁p, hPW₁⟩ := h𝒲P W₁ hW₁
  obtain ⟨hW₂p, hPW₂⟩ := h𝒲P W₂ hW₂
  have : W₂.IsPrime := hW₂p.isPrime

  obtain ⟨f, c, hf, hfW₁, hfW₂⟩ := exists_form_mem_not_mem hW₁p.multiHomog hle

  obtain ⟨e, h, hh, hce, hhS⟩ := exists_form_avoid_primes (insert P h𝒲.toFinset)
    (fun W hW => by
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact ⟨hP.isPrime, hP.multiHomog, hP.relevant⟩
      · have hW' := (h𝒲P W (h𝒲.mem_toFinset.mp hW)).1
        exact ⟨hW'.isPrime, hW'.multiHomog, hW'.relevant⟩) c
  have hhP : h ∉ P := hhS P (Finset.mem_insert_self _ _)
  have hh𝒲 : ∀ W ∈ 𝒲, h ∉ W := fun W hW =>
    hhS W (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW))

  obtain ⟨m, hm, hmW₂⟩ := exists_form_not_mem_of_isRelevant (H := W₂) hW₂p.relevant (e - c)
  have hfm : IsMultiHomog (f * m) e := by
    have := IsWeightedHomogeneous.mul hf hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hfmW₂ : f * m ∉ W₂ := fun h' => (hW₂p.isPrime.mem_or_mem h').elim hfW₂ hmW₂
  have hfmP : f * m ∉ P := fun h' => hfmW₂ (hPW₂ h')
  have hq0 : ∀ a : MRing ι F, a ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0 :=
    fun a ha => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  refine ⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, ?_, _,
    div_mem_degZeroLoc P {W₂} hh hfm hfmP
      (fun W hW => by rw [Set.mem_singleton_iff.mp hW]; exact hfmW₂), ?_⟩
  ·
    rintro ⟨y, hy, hxy⟩
    obtain ⟨b', f', g', -, -, hg'P, hg'W, hy'⟩ := DegZeroLocQuot.proof F K ι P {W₁}
      (fun W hW => by rw [Set.mem_singleton_iff.mp hW]; exact hW₁p.isPrime) y hy
    rw [hy', div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hq0 h hhP) (hq0 g' hg'P)),
      ← map_mul, ← map_mul, ← map_mul, ← map_mul] at hxy
    have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ hxy)
    have h3 : h * g' ∈ W₁ := by
      have := W₁.sub_mem (W₁.mul_mem_right f' (W₁.mul_mem_right m hfW₁)) (hPW₁ h2)
      rwa [sub_sub_cancel] at this
    rcases hW₁p.isPrime.mem_or_mem h3 with h4 | h4
    exacts [hh𝒲 W₁ hW₁ h4, hg'W W₁ (Set.mem_singleton W₁) h4]
  ·
    rw [div_mul_div_comm, mul_comm (algebraMap _ _ (Ideal.Quotient.mk P (f * m))),
      div_self (mul_ne_zero (hq0 h hhP) (hq0 _ hfmP))]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreNonempty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem FibreNonempty.proof (h1 : SemilocalFiniteRank.Statement.{u})
    (h2 : DegZeroLocalRing.Statement.{u}) : FibreNonempty.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hn hc W hW hWn hle
  have := hP'.isPrime
  by_contra hem
  rw [Set.not_nonempty_iff_eq_empty] at hem
  obtain ⟨hfin, -, -⟩ := h1 F K K' j ι' P' hP' n hn hc W hW hWn hle
  have := hfin
  have hnone : ∀ W' ∈ fibrePrimes j P' W, False := fun W' hW' => by
    rw [hem] at hW'
    exact hW'

  have hB : IsField (degZeroLoc P' (fibrePrimes j P' W)) := by
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
    intro x hx
    obtain ⟨b, f, g, hf, hg, hgP, -, hxfg⟩ := DegZeroLocQuot.proof F K' ι' P' (fibrePrimes j P' W)
      (fun W' hW' => (hnone W' hW').elim) x.1 x.2
    have hfP : f ∉ P' := by
      intro hfP
      apply hx
      apply Subtype.ext
      rw [hxfg, Ideal.Quotient.eq_zero_iff_mem.mpr hfP, map_zero, zero_div]
      rfl
    refine ⟨⟨_, div_mem_degZeroLoc P' (fibrePrimes j P' W) hg hf hfP
      (fun W' hW' => (hnone W' hW').elim)⟩, ?_⟩
    have hne : ∀ a : MRing ι' F, a ∉ P' →
        algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P')) (Ideal.Quotient.mk P' a) ≠ 0 :=
      fun a ha => by
        rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
        exact ha
    apply Subtype.ext
    change x.1 * _ = 1
    rw [hxfg, div_mul_div_comm, mul_comm (algebraMap _ _ (Ideal.Quotient.mk P' f))]
    exact div_self (mul_ne_zero (hne g hgP) (hne f hfP))

  have hinj : Function.Injective (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W))) := by
    intro x y hxy
    have := congrArg (fun z : degZeroLoc P' (fibrePrimes j P' W) =>
      (z : FractionRing (MRing ι' F ⧸ P'))) hxy
    simp only [degZeroLoc.algebraMap_contract_coe] at this
    exact Subtype.ext ((contractFracMap j P').toRingHom.injective this)
  have : Algebra.IsIntegral (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W)) := Algebra.IsIntegral.of_finite _ _
  have hA := isField_of_isIntegral_of_isField hinj hB
  have hdim := (h2 F K (fun k => ι' (j k)) (contractPrime j P')
    (isMultiProjPrime_contractPrime j ι' hP') W hW hle).2 n hc hWn
  rw [ringKrullDim_eq_zero_of_isField hA] at hdim
  exact zero_ne_one hdim

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]


omit [DecidableEq K] in
theorem finiteType_quotient_mRing (I : Ideal (MRing ι F)) : Algebra.FiniteType F (MRing ι F ⧸ I) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ_surjective F I)


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem chartMonomial_not_mem (Q : Ideal (MRing ι F)) [Q.IsPrime] (u : ∀ k, ι k)
    (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) (b : K → ℕ) : chartMonomial u b ∉ Q := by
  unfold chartMonomial
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hu k (Ideal.IsPrime.mem_of_pow_mem ‹_› _ hk)

theorem chart_ringKrullDim_add_card (h : MChartTrdeg.Statement.{u}) (Q : Ideal (MRing ι F)) [Q.IsPrime]
    (hQ : IsMultiHomogIdeal Q) (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) :
    ringKrullDim (MRing ι F ⧸ chartIdeal Q u) + Fintype.card K = ringKrullDim (MRing ι F ⧸ Q) := by
  have := finiteType_quotient_mRing (F := F) (chartIdeal Q u)
  have := finiteType_quotient_mRing (F := F) Q
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F,
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F (A := MRing ι F ⧸ Q), ← h F K ι Q hQ u hu,
    map_add, map_natCast]
  norm_cast

end

theorem DegZeroLocDim.proof (h₁ : MChartHomog.Statement.{u}) (h₂ : MChartTrdeg.Statement.{u})
    (h₃ : MChartLocDim.Statement.{u}) : DegZeroLocDim.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  choose u hu using hW.relevant
  have huP : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P := fun k hk => hu k (hPW hk)
  have hle : chartIdeal P u ≤ chartIdeal W u := by
    intro p hp
    obtain ⟨b, h, -, hh⟩ := h₁ F K ι u p
    simp only [chartIdeal, RingHom.mem_ker] at hp ⊢
    rw [hh P huP, div_eq_zero_iff, IsFractionRing.to_map_eq_zero_iff,
      IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.Quotient.eq_zero_iff_mem] at hp
    have hW' : h ∈ W := by
      rcases hp with hp | hp
      · exact hPW hp
      · exact absurd hp (chartMonomial_not_mem P u huP b)
    rw [hh W hu, IsFractionRing.to_map_eq_zero_iff.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hW'), zero_div]
  have : ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)
  have := finiteType_quotient_mRing (F := F) (chartIdeal P u)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F)
    ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u)))
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)] at hform
  show ringKrullDim (degZeroLoc P {W}) + ringKrullDim (MRing ι F ⧸ W) = ringKrullDim (MRing ι F ⧸ P)
  rw [h₃ F K ι P W hPW u hu, ← chart_ringKrullDim_add_card h₂ W hW.multiHomog u hu,
    ← chart_ringKrullDim_add_card h₂ P hP.multiHomog u huP, ← hform, add_assoc]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem ConeVarUnit.proof (hDZ : DegZeroLocQuot.Statement.{u})
    (hNum : ConeVarNumerator.Statement.{u}) : ConeVarUnit.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  intro p e he
  obtain ⟨b, g, h, hg, hgW, hh, hcoeff, himg⟩ := hNum F K ι P hP W hW hPW v hv p
  have hne : ∀ x : MRing ι F, x ∉ W →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P x) ≠ 0 :=
    fun x hx h0 => hx (hPW ((Ideal.Quotient.eq_zero_iff_mem).mp
      ((IsFractionRing.to_map_eq_zero_iff).mp h0)))

  have heW : h e ∉ W := by
    intro heW
    obtain ⟨y, hy⟩ := he.exists_right_inv
    obtain ⟨b', f', g', -, -, -, hg'W, hy'⟩ :=
      hDZ F K ι P {W} (fun W' hW' => (Set.mem_singleton_iff.mp hW') ▸ hW.isPrime) y y.2
    have h1 : ((p.coeff e : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) * y = 1 := by
      rw [← Subalgebra.coe_mul, hy, Subalgebra.coe_one]
    rw [hcoeff e, hy', div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero (hne g hgW)
      (hne g' (hg'W W rfl))), ← map_mul, ← map_mul, ← map_mul, ← map_mul] at h1
    have h2 := Ideal.Quotient.eq.mp (IsFractionRing.injective _ _ h1)
    have h3 : g * g' ∈ W := by
      have := W.sub_mem (W.mul_mem_right f' heW) (hPW h2)
      rwa [sub_sub_cancel] at this
    rcases hW.isPrime.mem_or_mem h3 with h4 | h4
    exacts [hgW h4, hg'W W rfl h4]

  have hu : ∀ d : K →₀ ℕ, IsMultiHomog (∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k) (⇑d) := by
    intro d
    have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, v k⟩) (fun k _ => (isWeightedHomogeneous_X F _ _).pow _)
    have hdeg : (∑ k, d k • blockWeight ι ⟨k, v k⟩) = ⇑d := by
      ext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hdeg] at this
    exact this
  have huW : ∀ d : K →₀ ℕ, (∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k) ∉ W := by
    intro d hd
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp hd
    exact hv k (hW.isPrime.mem_of_pow_mem _ hk)

  set N := ∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k with hNdef
  have hcomp : weightedHomogeneousComponent (blockWeight ι) (b + ⇑e) N =
      h e * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ e k := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hNdef, map_sum, Finset.sum_eq_single e]
    · exact ((hh e).mul (hu e)).weightedHomogeneousComponent_same
    · intro d _ hde
      refine weightedHomogeneousComponent_eq_zero' _ _ fun c hc hw => hde ?_
      rw [((hh d).mul (hu d)) (mem_support_iff.mp hc)] at hw
      exact DFunLike.coe_injective (add_left_cancel hw)
    · intro hes
      exact absurd (notMem_support_iff.mp hes) he.ne_zero
  have hNW : N ∉ W := fun hN => by
    have := hW.multiHomog N hN (b + ⇑e)
    rw [hcomp] at this
    rcases hW.isPrime.mem_or_mem this with h4 | h4
    exacts [heW h4, huW e h4]

  have hunit : ∀ x : MRing ι F, x ∉ W →
      IsUnit (algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P x)) :=
    fun x hx => IsLocalization.map_units (coneLocal P W hPW)
      (⟨_, Submonoid.mem_map_of_mem _ hx⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  have heq : coneVarMap P W hPW v p *
      algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P N) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, himg,
      div_mul_cancel₀ _ (hne g hgW)]
  exact isUnit_of_mul_isUnit_left (heq ▸ hunit N hNW)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarSurj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option maxHeartbeats 400000 in
theorem ConeVarSurj.proof : ConeVarSurj.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v hv
  have := hP.isPrime
  have := hW.isPrime
  classical
  intro z
  set L := FractionRing (MRing ι F ⧸ P)
  let π : MRing ι F → L := fun x => algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P x)
  have hπ : ∀ x, x ∉ P → π x ≠ 0 := fun x hx => by
    simp only [π, Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hx
  let U : (K → ℕ) → MRing ι F := fun d => ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k
  have hUh : ∀ d, IsMultiHomog (U d) d := fun d => by
    have := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, v k⟩ : MRing ι F) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, v k⟩) (fun k _ => (isWeightedHomogeneous_X _ _ _).pow _)
    have hd : ∑ k, d k • blockWeight ι ⟨k, v k⟩ = d := by
      funext j
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hd] at this
    exact this
  have hUW : ∀ d, U d ∉ W := fun d =>
    W.primeCompl.prod_mem fun k _ => W.primeCompl.pow_mem (hv k) _
  let comp : MRing ι F → (K → ℕ) → MRing ι F := fun h d =>
    weightedHomogeneousComponent (blockWeight ι) d h
  let c : MRing ι F → (K → ℕ) → degZeroLoc P {W} := fun h d =>
    ⟨π (comp h d) / π (U d), div_mem_degZeroLoc P {W}
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (hUh d) (fun h' => hUW d (hPW h')) (by rintro _ rfl; exact hUW d)⟩
  let D : MRing ι F → Finset (K → ℕ) := fun h => h.support.image (Finsupp.weight (blockWeight ι))
  have hsum : ∀ h, ∑ d ∈ D h, comp h d = h := fun h => by
    rw [← finsum_eq_sum_of_support_subset _ (s := D h) (fun d hd => by
      by_contra hd'
      exact hd (weightedHomogeneousComponent_eq_zero_of_notMem _ h d hd'))]
    exact sum_weightedHomogeneousComponent (blockWeight ι) h
  let Q : MRing ι F → MvPolynomial K (degZeroLoc P {W}) := fun h =>
    ∑ d ∈ D h, monomial (Finsupp.equivFunOnFinite.symm d) (c h d)
  have hQ : ∀ h, coneVarMap P W hPW v (Q h) =
      algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P h) := fun h => by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← hsum h, map_sum, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [coneVarMap, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, degZeroLoc.algebraMap_cone_coe, SubmonoidClass.coe_finsetProd,
      SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap, Finsupp.coe_equivFunOnFinite_symm]
    have hU : ∏ k, algebraMap (MRing ι F ⧸ P) L (Ideal.Quotient.mk P (X ⟨k, v k⟩)) ^ d k =
        π (U d) := by
      simp [π, U, map_prod, map_pow]
    rw [hU]
    exact div_mul_cancel₀ _ (hπ _ fun h' => hUW d (hPW h'))
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (W.primeCompl.map (Ideal.Quotient.mk P)) z
  obtain ⟨g, hg, hgs⟩ := Submonoid.mem_map.mp s.2
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨d, hdD, hdW⟩ : ∃ d ∈ D g, comp g d ∉ W := by
    by_contra hne
    push Not at hne
    exact hg (hsum g ▸ W.sum_mem hne)
  refine ⟨Q f, Q g, Finsupp.equivFunOnFinite.symm d, ?_, ?_⟩
  · have hcoeff : (Q g).coeff (Finsupp.equivFunOnFinite.symm d) = c g d := by
      simp only [Q, coeff_sum, coeff_monomial, EmbeddingLike.apply_eq_iff_eq]
      rw [Finset.sum_ite_eq', if_pos hdD]
    rw [hcoeff]
    refine isUnit_iff_exists_inv.mpr ⟨⟨π (U d) / π (comp g d), div_mem_degZeroLoc P {W} (hUh d)
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (fun h' => hdW (hPW h'))
      (by rintro _ rfl; exact hdW)⟩, Subtype.ext ?_⟩
    simp only [c, Subalgebra.coe_mul, Subalgebra.coe_one]
    rw [div_mul_div_cancel₀ (hπ _ fun h' => hUW d (hPW h')), div_self (hπ _ fun h' => hdW (hPW h'))]
  · rw [hQ, hQ, hgs]
    exact hxs

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeVarNumerator
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option maxHeartbeats 400000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem ConeVarNumerator.proof (hDZ : DegZeroLocQuot.Statement.{u}) :
    ConeVarNumerator.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW v _
  have := hP.isPrime
  have := hW.isPrime
  intro p
  have hne : ∀ g : MRing ι F, g ∉ W →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P g) ≠ 0 := by
    intro g hg
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h' => hg (hPW h')
  have h𝒲 : ∀ W' ∈ ({W} : Set (Ideal (MRing ι F))), W'.IsPrime := by
    intro W' hW'
    rw [Set.mem_singleton_iff.mp hW']
    infer_instance

  have step : ∀ D : Finset (K →₀ ℕ), ∃ (b : K → ℕ) (g : MRing ι F) (hn : (K →₀ ℕ) → MRing ι F),
      IsMultiHomog g b ∧ g ∉ W ∧ (∀ d, IsMultiHomog (hn d) b) ∧ (∀ d, d ∉ D → hn d = 0) ∧
      ∀ d ∈ D, ((p.coeff d : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) =
        algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (hn d)) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      refine ⟨0, 1, fun _ => 0, isWeightedHomogeneous_one F _, fun h1 => ?_,
        fun _ => isWeightedHomogeneous_zero F _ _, fun _ _ => rfl, fun d hd => absurd hd (Finset.notMem_empty d)⟩
      exact Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one W).mpr h1)
    | insert d₀ D hd₀ ih =>
      obtain ⟨b, g, hn, hg, hgW, hh, h0, hD⟩ := ih
      obtain ⟨b', f', g', hf', hg', -, hg'W, he⟩ := hDZ F K ι P {W} h𝒲 _ (p.coeff d₀).2
      have hg'W' : g' ∉ W := hg'W W rfl
      refine ⟨b + b', g * g', fun d => if d = d₀ then g * f' else hn d * g',
        IsWeightedHomogeneous.mul hg hg', fun hm => ?_, fun d => ?_, fun d hd => ?_, fun d hd => ?_⟩
      · exact (Ideal.IsPrime.mem_or_mem inferInstance hm).elim hgW hg'W'
      · dsimp only
        split_ifs
        · exact IsWeightedHomogeneous.mul hg hf'
        · exact IsWeightedHomogeneous.mul (hh d) hg'
      · rw [Finset.mem_insert, not_or] at hd
        dsimp only
        rw [if_neg hd.1, h0 d hd.2, zero_mul]
      · rcases Finset.mem_insert.mp hd with rfl | hd
        · dsimp only
          rw [if_pos rfl, he]
          simp only [map_mul]
          rw [mul_div_mul_left _ _ (hne g hgW)]
        · have hdd : d ≠ d₀ := fun e => hd₀ (e ▸ hd)
          dsimp only
          rw [if_neg hdd, hD d hd]
          simp only [map_mul]
          rw [mul_div_mul_right _ _ (hne g' hg'W')]
  obtain ⟨b, g, hn, hg, hgW, hh, h0, hD⟩ := step p.support
  refine ⟨b, g, hn, hg, hgW, hh, fun d => ?_, ?_⟩
  · by_cases hd : d ∈ p.support
    · exact hD d hd
    · rw [notMem_support_iff.mp hd, h0 d hd]
      simp

  have hφ : ∀ x : MvPolynomial K (degZeroLoc P {W}),
      ((coneVarMap P W hPW v x : coneLocal P W hPW) : FractionRing (MRing ι F ⧸ P)) =
        eval₂ (degZeroLoc P {W}).val.toRingHom (fun k => algebraMap (MRing ι F ⧸ P)
          (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, v k⟩))) x := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C a =>
      rw [coneVarMap, aeval_C, degZeroLoc.algebraMap_cone_coe, eval₂_C]
      rfl
    | add x y hx hy =>
      rw [map_add (coneVarMap P W hPW v) x y, Subalgebra.coe_add, hx, hy, eval₂_add]
    | mul_X x k hx =>
      rw [map_mul, Subalgebra.coe_mul, hx, eval₂_mul, eval₂_X, coneVarMap, aeval_X]
      rfl
  rw [hφ, eval₂_eq']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_prod, map_pow, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [mul_div_right_comm, ← hD d hd]
  rfl

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalResidueLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem SemilocalResidueLength.proof (hRes : DegZeroLocResidue.Statement.{u})
    (hFR : SemilocalFiniteRank.Statement.{u}) (hLoc : DegZeroLocLocalize.Statement.{u}) :
    SemilocalResidueLength.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W hW hWn hPW
  have := hP'.isPrime
  intro W' hW'
  have := hW'.1.isPrime
  haveI hfin := (hFR F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW).1
  have h𝒲 := FibreFinite.proof F K K' j ι' P' hP' n hP'n hPn W hW hWn hPW
  obtain ⟨-, hPW', hc⟩ := id hW'
  subst hc
  obtain ⟨ρO, hρOv, hρOk, hρOr⟩ := hRes F K' ι' P' W' hPW'
  obtain ⟨ρA, hρAv, -, hρAr⟩ := hRes F K (fun k => ι' (j k)) (contractPrime j P') _ hPW
  have hLE := map_homFracDegZero_le j ι' W'
  have hBO := degZeroLoc_anti P' (Set.singleton_subset_iff.mpr hW')
  let L := (homFracDegZero (contractPrime j W')).map (contractFracMap j W')
  let M := IntermediateField.extendScalars hLE
  let τ : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) →+* M :=
    (ρO.comp (Subalgebra.inclusion hBO).toRingHom).codRestrict M (fun b => (hρOr _).mpr ⟨_, rfl⟩)
  let σ : degZeroLoc (contractPrime j P') {contractPrime j W'} →+* L :=
    ((contractFracMap j W').toRingHom.comp ρA).codRestrict L
      (fun a => ⟨ρA a, (hρAr _).mpr ⟨a, rfl⟩, rfl⟩)
  have hσs : Function.Surjective σ := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨a, rfl⟩ := (hρAr w).mp hw
    exact ⟨a, rfl⟩
  letI : Algebra (degZeroLoc (contractPrime j P') {contractPrime j W'}) L := σ.toAlgebra
  letI : Algebra (degZeroLoc (contractPrime j P') {contractPrime j W'}) M :=
    ((algebraMap L M).comp σ).toAlgebra
  haveI : IsScalarTower (degZeroLoc (contractPrime j P') {contractPrime j W'}) L M :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hcomp : ∀ a : degZeroLoc (contractPrime j P') {contractPrime j W'}, τ (algebraMap _ _ a) = algebraMap _ M a := by
    intro a
    obtain ⟨b, f, g, hf, hg, -, hgW, hx⟩ := DegZeroLocQuot.proof F K (fun k => ι' (j k))
      (contractPrime j P') {contractPrime j W'} (fun V hV => by rw [hV]; infer_instance) a.1 a.2
    apply Subtype.ext
    show ρO ⟨contractFracMap j P' a, _⟩ = contractFracMap j W' (ρA a)
    rw [hρAv a b f g hf hg (hgW _ rfl) hx, map_div₀, contractFracMap_algebraMap,
      contractFracMap_algebraMap]
    apply hρOv _ _ _ _ (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hg) (hgW _ rfl)
    show contractFracMap j P' a = _
    rw [hx, map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]
  let τA : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) →ₐ[degZeroLoc (contractPrime j P') {contractPrime j W'}] M :=
    { τ with commutes' := hcomp }

  have hmem : ∀ l : L, algebraMap L M l ∈ τ.rangeS := by
    intro l
    obtain ⟨a, rfl⟩ := hσs l
    exact ⟨_, hcomp a⟩
  let R : Subalgebra L M := { τ.rangeS with algebraMap_mem' := hmem }
  have hsurj : Function.Surjective τ := by
    rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := (hρOr z).mp hz
    obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hys⟩ := hLoc F K' ι' P' hP' _ h𝒲
      (fun V hV => ⟨hV.1, hV.2.1⟩) W' hW' y.1 y.2
    have hs0 : τ ⟨s, hs⟩ ≠ 0 := by
      intro h0
      have h1 : ρO ⟨s, hBO hs⟩ * ρO ⟨t, ht⟩ = 1 := by
        rw [← map_mul, ← map_one ρO]
        exact congrArg ρO (Subtype.ext hst)
      rw [show ρO ⟨s, hBO hs⟩ = 0 from congrArg Subtype.val h0, zero_mul] at h1
      exact zero_ne_one h1
    have hint : IsIntegral L (τ ⟨s, hs⟩) :=
      ((Algebra.IsIntegral.isIntegral (R := degZeroLoc (contractPrime j P') {contractPrime j W'})
        (⟨s, hs⟩ : degZeroLoc P' (fibrePrimes j P' (contractPrime j W')))).map τA).tower_top
    obtain ⟨c, hc⟩ := hint.inv_mem (A := R) ⟨⟨s, hs⟩, rfl⟩
    have hbys : τ ⟨b, hb⟩ = ⟨ρO y, hz⟩ * τ ⟨s, hs⟩ := by
      apply Subtype.ext
      show ρO ⟨b, hBO hb⟩ = ρO y * ρO ⟨s, hBO hs⟩
      rw [← map_mul]
      exact congrArg ρO (Subtype.ext hys.symm)
    refine ⟨⟨b, hb⟩ * c, ?_⟩
    rw [map_mul, hc, hbys, mul_inv_cancel_right₀ hs0]
  refine ⟨RingHom.ker τ, fun x => ?_, ?_⟩
  · rw [RingHom.mem_ker, ← ZeroMemClass.coe_eq_zero]
    exact hρOk ⟨x, hBO x.2⟩
  · let e : (degZeroLoc P' (fibrePrimes j P' (contractPrime j W')) ⧸ RingHom.ker τ) ≃ₐ[degZeroLoc (contractPrime j P') {contractPrime j W'}] M :=
      AlgEquiv.ofRingEquiv (f := RingHom.quotientKerEquivOfSurjective hsurj) (fun a => by
        rw [← Ideal.Quotient.mk_algebraMap, RingHom.quotientKerEquivOfSurjective_apply_mk]
        exact hcomp a)
    haveI : Module.Finite (degZeroLoc (contractPrime j P') {contractPrime j W'}) M :=
      Module.Finite.of_surjective τA.toLinearMap hsurj
    haveI : Module.Finite L M :=
      Module.Finite.of_restrictScalars_finite (degZeroLoc (contractPrime j P') {contractPrime j W'}) L M
    refine e.toLinearEquiv.length_eq.trans ?_
    refine (Module.length_eq_of_surjective (S := degZeroLoc (contractPrime j P') {contractPrime j W'}) (R := L) (M := M) hσs).trans ?_
    rw [Module.length_eq_finrank L M, relDeg,
      IntermediateField.relfinrank_eq_finrank_of_le hLE]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
