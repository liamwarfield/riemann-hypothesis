module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.NormLeOneOfInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZpowWNe

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MainFin
namespace UpperTheory.Reformulated.B.Ra5

open Polynomial

private theorem ext_inj {R S K : Type} [CommRing R] [CommRing S] [IsDomain S]
    [Field K] [IsAlgClosed K] (f : R →+* S) (hf : Function.Injective f) (hfi : f.IsIntegral)
    (g : R →+* K) (hg : Function.Injective g) :
    ∃ l : S →+* K, l.comp f = g := by
  haveI : IsDomain R := hf.isDomain f
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R K := g.toAlgebra
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).mpr hf
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  haveI : Algebra.IsIntegral R S := ⟨hfi⟩
  let l := IsAlgClosed.lift (R := R) (S := S) (M := K)
  exact ⟨(l : S →+* K), RingHom.ext fun x => l.commutes x⟩

private theorem ext_integral {R S K : Type} [CommRing R] [CommRing S] [IsDomain S]
    [Field K] [IsAlgClosed K] (f : R →+* S) (hinj : Function.Injective f) (hfi : f.IsIntegral)
    (y : R →+* K) :
    ∃ ξ : S →+* K, ξ.comp f = y := by
  letI : Algebra R S := f.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hfi⟩
  haveI hp : (RingHom.ker y).IsPrime := RingHom.ker_isPrime y
  obtain ⟨Q, -, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker y) (⊥ : Ideal S) (by
      intro x hx
      have h0 : algebraMap R S x = 0 := by simpa using hx
      have hx0 : x = 0 := hinj (h0.trans (map_zero f).symm)
      simp [hx0])
  have hQc' : Q.comap f = RingHom.ker y := hQc
  let q : (R ⧸ Q.comap f) →+* (S ⧸ Q) := Ideal.quotientMap Q f le_rfl
  have hq : Function.Injective q := Ideal.quotientMap_injective
  have hqi : q.IsIntegral := RingHom.IsIntegral.quotient f hfi
  let g : (R ⧸ Q.comap f) →+* K := Ideal.Quotient.lift _ y (fun a ha => by
    have : a ∈ RingHom.ker y := hQc' ▸ ha
    exact this)
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    intro h
    have hx : x ∈ RingHom.ker y := h
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hQc' ▸ hx)
  obtain ⟨l, hl⟩ := ext_inj q hq hqi g hg
  refine ⟨l.comp (Ideal.Quotient.mk Q), RingHom.ext fun x => ?_⟩
  have h := RingHom.congr_fun hl (Ideal.Quotient.mk _ x)
  exact h

private theorem gen_alg {A B K : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra B A] [Field K] [IsAlgClosed K]
    (hinj : Function.Injective (algebraMap B A)) (t : A) (ht : Algebra.adjoin B {t} = ⊤)
    (f : B[X]) (hf : f ≠ 0) (hft : aeval t f = 0) (y : B →+* K) (hy : y f.leadingCoeff ≠ 0) :
    ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y := by
  have hc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  let M : Submonoid B := Submonoid.powers f.leadingCoeff
  have hM : M ≤ nonZeroDivisors B := powers_le_nonZeroDivisors_of_noZeroDivisors hc
  let M' : Submonoid A := M.map (algebraMap B A)
  have hM' : M' ≤ nonZeroDivisors A := by
    rintro _ ⟨m, hm, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero (hM hm) (hinj (by simpa using h)))
  haveI : IsDomain (Localization M') := IsLocalization.isDomain_localization hM'
  let φ : Localization M →+* Localization M' :=
    IsLocalization.map (Localization M') (algebraMap B A) M.le_comap_map
  have hφ : ∀ r : B, φ (algebraMap B (Localization M) r) =
      algebraMap A (Localization M') (algebraMap B A r) := fun r => IsLocalization.map_eq _ r
  have h1 : ∀ s : A, φ.IsIntegralElem (algebraMap A (Localization M') s) := by
    intro s
    have hs : s ∈ Algebra.adjoin B {t} := ht ▸ Algebra.mem_top
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact RingHom.isIntegralElem_localization_at_leadingCoeff (algebraMap B A) x f hft M
        (Submonoid.mem_powers _)
    | algebraMap r =>
      rw [← hφ]
      exact RingHom.isIntegralElem_map φ
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact RingHom.IsIntegralElem.add φ hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact RingHom.IsIntegralElem.mul φ hx hy
  have hint : φ.IsIntegral := by
    intro x
    obtain ⟨⟨s, ⟨_, m, hm, rfl⟩⟩, hx⟩ := IsLocalization.surj M' x
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp
      (IsLocalization.map_units (Localization M) (⟨m, hm⟩ : M))
    have hv' : algebraMap A (Localization M') (algebraMap B A m) * φ v = 1 := by
      rw [← hφ, ← map_mul]
      have : algebraMap B (Localization M) m * v = 1 := hv
      rw [this, map_one]
    have hxe : x = algebraMap A (Localization M') s * φ v := by
      rw [← hx, mul_assoc]
      simp only [] at hv' ⊢
      rw [hv', mul_one]
    rw [hxe]
    exact RingHom.IsIntegralElem.mul φ (h1 s) (RingHom.isIntegralElem_map φ)
  have hφi : Function.Injective φ :=
    IsLocalization.map_injective_of_injective M (Localization M) (Localization M') hinj
  let y' : Localization M →+* K := IsLocalization.lift (M := M) (g := y) (by
    rintro ⟨_, n, rfl⟩
    simpa using (isUnit_iff_ne_zero.mpr hy).pow n)
  obtain ⟨ξ, hξ⟩ := ext_integral φ hφi hint y'
  refine ⟨ξ.comp (algebraMap A (Localization M')), RingHom.ext fun r => ?_⟩
  have h := RingHom.congr_fun hξ (algebraMap B (Localization M) r)
  simp only [RingHom.comp_apply, hφ] at h ⊢
  rw [h]
  exact IsLocalization.lift_eq _ r

private theorem one_gen {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra B A] (hinj : Function.Injective (algebraMap B A)) (t : A)
    (ht : Algebra.adjoin B {t} = ⊤) (a : A) (ha : a ≠ 0) :
    ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K), y b ≠ 0 →
      ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 := by
  haveI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hinj
  by_cases hta : IsAlgebraic B t
  · have haa : IsAlgebraic B a :=
      Algebra.isAlgebraic_adjoin_singleton_iff.mpr hta a (ht ▸ Algebra.mem_top)
    obtain ⟨f, hf, hft⟩ := hta
    obtain ⟨r, hr, d, hd⟩ := haa.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha)
    refine ⟨f.leadingCoeff * r, mul_ne_zero (leadingCoeff_ne_zero.mpr hf) hr,
      fun K _ _ y hy => ?_⟩
    rw [map_mul] at hy
    obtain ⟨ξ, hξ⟩ := gen_alg hinj t ht f hf hft y (left_ne_zero_of_mul hy)
    refine ⟨ξ, hξ, fun h0 => right_ne_zero_of_mul hy ?_⟩
    have h1 := congrArg ξ hd
    rw [map_mul, h0, zero_mul] at h1
    rw [← hξ]
    exact h1
  · have hsurj : Function.Surjective (aeval t : B[X] →ₐ[B] A) := by
      intro x
      have hx : x ∈ Algebra.adjoin B {t} := ht ▸ Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
      exact hx
    have hbij : Function.Bijective (aeval t : B[X] →ₐ[B] A) :=
      ⟨transcendental_iff_injective.mp hta, hsurj⟩
    obtain ⟨p, rfl⟩ := hsurj a
    have hp : p ≠ 0 := fun h => ha (by simp [h])
    refine ⟨p.leadingCoeff, leadingCoeff_ne_zero.mpr hp, fun K _ _ y hy => ?_⟩
    have hpm : p.map y ≠ 0 := by
      intro h
      apply hy
      have := congrArg (fun q => q.coeff p.natDegree) h
      simpa [coeff_map] using this
    obtain ⟨r, hr⟩ : ∃ r, (p.map y).eval r ≠ 0 := by
      by_contra! h
      exact hpm (Polynomial.funext (by simpa using h))
    let e := AlgEquiv.ofBijective (aeval t : B[X] →ₐ[B] A) hbij
    refine ⟨(eval₂RingHom y r).comp (e.symm : A →+* B[X]), RingHom.ext fun x => ?_, ?_⟩
    · have : e.symm (algebraMap B A x) = C x := by
        rw [AlgEquiv.symm_apply_eq]
        simp [e]
      simp [this]
    · have : e.symm (aeval t p) = p := e.symm_apply_apply p
      simpa [this, eval_map] using hr

end UpperTheory.Reformulated.B.Ra5

theorem UpperTheory.Reformulated.B.Ra5.main_fin :
    ∀ (A : Type) [inst : CommRing A] [IsDomain A]
    (s : Finset A) (B : Type) [inst_2 : CommRing B] [IsDomain B] [inst_4 : Algebra B A],
    Algebra.adjoin B (↑s : Set A) = ⊤ →
      Function.Injective (⇑(Algebra.algebraMap B A) : B → A) →
        ∀ (a : A),
          a ≠ (0 : A) →
            ∃ (b : B),
              b ≠ (0 : B) ∧
                ∀ (K : Type) [inst_5 : Field K] [IsAlgClosed K] (y : B →+* K),
                  (y : B → K) b ≠ (0 : K) →
                    ∃ (ξ : A →+* K), ξ.comp (Algebra.algebraMap B A) = y ∧ (ξ : A → K) a ≠ (0 : K) := by
  intro A _ _ s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro B _ _ _ htop hinj a ha
    have hinj' : Function.Injective (algebraMap B A) := hinj
    have hsurj : Function.Surjective (algebraMap B A) := by
      intro x
      have hx : x ∈ (⊥ : Subalgebra B A) := by
        rw [← Algebra.adjoin_empty B A, ← Finset.coe_empty, htop]
        exact Algebra.mem_top
      exact Algebra.mem_bot.mp hx
    obtain ⟨b, rfl⟩ := hsurj a
    let e := RingEquiv.ofBijective (algebraMap B A) ⟨hinj', hsurj⟩
    have hb : b ≠ 0 := fun h => ha (by simp [h])
    refine ⟨b, hb, fun K _ _ y hy => ⟨y.comp (e.symm : A →+* B), ?_, ?_⟩⟩
    · refine RingHom.ext fun x => ?_
      have : e.symm (algebraMap B A x) = x := e.symm_apply_apply x
      exact congrArg y this
    · have : e.symm (algebraMap B A b) = b := e.symm_apply_apply b
      simpa [this] using hy
  | insert t s' hts ih =>
    intro B _ _ _ htop hinj a ha
    have hinj' : Function.Injective (algebraMap B A) := hinj
    rw [Finset.coe_insert, Set.insert_eq, Algebra.adjoin_union_eq_adjoin_adjoin] at htop
    have h1 : Algebra.adjoin (Algebra.adjoin B ({t} : Set A)) (s' : Set A) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ Subalgebra.restrictScalars B
          (Algebra.adjoin (Algebra.adjoin B ({t} : Set A)) (s' : Set A)) := htop ▸ Algebra.mem_top
      exact hx
    obtain ⟨b₁, hb₁, h⟩ := ih (Algebra.adjoin B ({t} : Set A)) h1 Subtype.val_injective a ha
    let t₁ : Algebra.adjoin B ({t} : Set A) := ⟨t, Algebra.subset_adjoin rfl⟩
    have ht₁ : Algebra.adjoin B {t₁} = ⊤ := by
      apply Subalgebra.map_injective (f := (Algebra.adjoin B ({t} : Set A)).val)
        Subtype.val_injective
      rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, Set.image_singleton]
      rfl
    have hinj₁ : Function.Injective (algebraMap B (Algebra.adjoin B ({t} : Set A))) := by
      intro x x' hxx
      exact hinj' (congrArg Subtype.val hxx)
    obtain ⟨b, hb, h2⟩ := one_gen hinj₁ t₁ ht₁ b₁ hb₁
    refine ⟨b, hb, fun K _ _ y hy => ?_⟩
    obtain ⟨ξ₁, h3, h4⟩ := h2 K y hy
    obtain ⟨ξ, h5, h6⟩ := h K ξ₁ h4
    refine ⟨ξ, RingHom.ext fun x => ?_, h6⟩
    have h7 := RingHom.congr_fun h5 (algebraMap B _ x)
    have h8 := RingHom.congr_fun h3 x
    exact h7.trans h8
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.ExistsBetweenFinset
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem twist {O B A K : Type} [CommRing O] [CommRing B] [CommRing A] [Field K] [Algebra O A] [Algebra O K]
    [Algebra B A] (gr : ℤ → Submodule B A) (h1 : DirectSum.IsInternal gr) (h2 : SetLike.GradedMonoid gr)
    (h0 : ∀ c : O, algebraMap O A c ∈ gr 0) (ξ : A →ₐ[O] K) (u : K) (hu : u ≠ 0) :
    ∃ ξ' : A →ₐ[O] K, ∀ j, ∀ a ∈ gr j, ξ' a = u ^ j * ξ a := by
  classical
  letI dec : DirectSum.Decomposition gr := h1.chooseDecomposition
  letI : GradedRing gr := { h2, dec with }
  let f : ∀ j, gr j →+ K := fun j =>
    { toFun := fun a => u ^ j * ξ a.1
      map_zero' := by simp
      map_add' := fun a b => by simp [mul_add] }
  let e : (DirectSum ℤ fun j => gr j) →+* K := DirectSum.toSemiring f
    (by show u ^ (0 : ℤ) * ξ 1 = 1; simp)
    (fun {i j} a b => by
      show u ^ (i + j) * ξ (a.1 * b.1) = (u ^ i * ξ a.1) * (u ^ j * ξ b.1)
      rw [zpow_add₀ hu, map_mul]; ring)
  let φ : A →+* K := e.comp (DirectSum.decomposeRingEquiv gr).toRingHom
  have key : ∀ j, ∀ a ∈ gr j, φ a = u ^ j * ξ a := fun j a ha => by
    show e (DirectSum.decompose gr a) = _
    have : DirectSum.decompose gr a = DirectSum.of (fun j => gr j) j ⟨a, ha⟩ :=
      DirectSum.decompose_of_mem gr ha
    rw [this]
    exact DirectSum.toSemiring_of _ _ _ _ _
  refine ⟨{ φ with commutes' := fun c => ?_ }, key⟩
  show φ _ = _
  rw [key 0 _ (h0 c), zpow_zero, one_mul, AlgHom.commutes]

private theorem exists_log_norm {K : Type} [NormedField K] [IsAlgClosed K] (x : K) (hx : 1 < ‖x‖) {α β : ℝ}
    (h : α < β) : ∃ u : K, u ≠ 0 ∧ α < Real.log ‖u‖ ∧ Real.log ‖u‖ < β := by
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx
    linarith
  have hc : 0 < Real.log ‖x‖ := Real.log_pos hx
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (div_lt_div_of_pos_right h hc)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ q.num) q.den_pos
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow q.den_pos.ne'] at hu
    exact zpow_ne_zero _ hx0 hu.symm
  have hlog : Real.log ‖u‖ = (q : ℝ) * Real.log ‖x‖ := by
    have e := congrArg (fun z => Real.log ‖z‖) hu
    simp only [norm_pow, norm_zpow, Real.log_pow, Real.log_zpow] at e
    have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    rw [Rat.cast_def]
    field_simp
    linear_combination e
  refine ⟨u, hu0, ?_, ?_⟩
  · rw [hlog]
    rw [div_lt_iff₀ hc] at hq1
    linarith
  · rw [hlog]
    rw [lt_div_iff₀ hc] at hq2
    linarith

private theorem exists_between_finset (L U : Finset ℝ) (h : ∀ x ∈ L, ∀ y ∈ U, x < y) :
    ∃ α β : ℝ, α < β ∧ (∀ x ∈ L, x ≤ α) ∧ ∀ y ∈ U, β ≤ y := by
  rcases L.eq_empty_or_nonempty with rfl | hL
  · rcases U.eq_empty_or_nonempty with rfl | hU
    · exact ⟨0, 1, one_pos, by simp, by simp⟩
    · exact ⟨U.min' hU - 1, U.min' hU, by linarith, by simp, fun y hy => U.min'_le y hy⟩
  · rcases U.eq_empty_or_nonempty with rfl | hU
    · exact ⟨L.max' hL, L.max' hL + 1, by linarith, fun x hx => L.le_max' x hx, by simp⟩
    · exact ⟨L.max' hL, U.min' hU, h _ (L.max'_mem hL) _ (U.min'_mem hU),
        fun x hx => L.le_max' x hx, fun y hy => U.min'_le y hy⟩

private theorem exists_scale {K P : Type} [NormedField K] [IsAlgClosed K] [Finite P] (x : K) (hx : 1 < ‖x‖)
    (w : P → ℤ) (a : P → ℝ) (ha : ∀ p, 0 ≤ a p) (hw : ∀ p, w p ≠ 0)
    (hc : ∀ p q, 0 < w p → w q < 0 → a p ^ (-w q).toNat * a q ^ (w p).toNat < 1) :
    ∃ u : K, u ≠ 0 ∧ ∀ p, ‖u‖ ^ (w p) * a p < 1 := by
  classical
  haveI := Fintype.ofFinite P
  let L : Finset ℝ := (Finset.univ.filter (fun p => w p < 0 ∧ 0 < a p)).image
    (fun p => -Real.log (a p) / (w p : ℝ))
  let U : Finset ℝ := (Finset.univ.filter (fun p => 0 < w p ∧ 0 < a p)).image
    (fun p => -Real.log (a p) / (w p : ℝ))
  have hLU : ∀ s ∈ L, ∀ t ∈ U, s < t := by
    intro s hs t ht
    simp only [L, U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
    obtain ⟨q, ⟨hq, haq⟩, rfl⟩ := hs
    obtain ⟨p, ⟨hp, hap⟩, rfl⟩ := ht
    have h1 := hc p q hp hq
    have hprod : 0 < a p ^ (-w q).toNat * a q ^ (w p).toNat := by positivity
    have hlog := Real.log_neg hprod h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
    have e1 : (((-w q).toNat : ℕ) : ℝ) = -(w q : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]
    have e2 : (((w p).toNat : ℕ) : ℝ) = (w p : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hp.le]
    rw [e1, e2] at hlog
    have hwq : (w q : ℝ) < 0 := by exact_mod_cast hq
    have hwp : (0 : ℝ) < w p := by exact_mod_cast hp
    have hq0 : (w q : ℝ) ≠ 0 := hwq.ne
    have hp0 : (w p : ℝ) ≠ 0 := hwp.ne'
    have key : -Real.log (a p) / (w p : ℝ) - -Real.log (a q) / (w q : ℝ)
        = -((-(w q : ℝ)) * Real.log (a p) + (w p : ℝ) * Real.log (a q)) / ((w p : ℝ) * (-(w q : ℝ))) := by
      field_simp
      ring
    have hpos : 0 < -Real.log (a p) / (w p : ℝ) - -Real.log (a q) / (w q : ℝ) := by
      rw [key]
      apply div_pos
      · linarith
      · nlinarith
    linarith
  obtain ⟨α, β, hαβ, hαL, hβU⟩ := exists_between_finset L U hLU
  obtain ⟨u, hu0, h1, h2⟩ := exists_log_norm x hx hαβ
  refine ⟨u, hu0, fun p => ?_⟩
  rcases (ha p).eq_or_lt with hap | hap
  · rw [← hap, mul_zero]
    exact one_pos
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hpos : 0 < ‖u‖ ^ (w p) * a p := by positivity
  rw [← Real.log_neg_iff hpos, Real.log_mul (by positivity) hap.ne', Real.log_zpow]
  rcases lt_or_gt_of_ne (hw p) with hwn | hwp
  · have hmem : -Real.log (a p) / (w p : ℝ) ∈ L := by
      simp only [L, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, ⟨hwn, hap⟩, rfl⟩
    have h3 := lt_of_le_of_lt (hαL _ hmem) h1
    have hwr : (w p : ℝ) < 0 := by exact_mod_cast hwn
    rw [div_lt_iff_of_neg hwr] at h3
    linarith [mul_comm (Real.log ‖u‖) (w p : ℝ)]
  · have hmem : -Real.log (a p) / (w p : ℝ) ∈ U := by
      simp only [U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, ⟨hwp, hap⟩, rfl⟩
    have h4 := lt_of_lt_of_le h2 (hβU _ hmem)
    have hwr : (0 : ℝ) < w p := by exact_mod_cast hwp
    rw [lt_div_iff₀ hwr] at h4
    linarith [mul_comm (Real.log ‖u‖) (w p : ℝ)]

private theorem exists_max_entry {B A K G : Type} [CommRing B] [CommRing A] [Algebra B A] [NormedField K]
    [IsUltrametricDist K] [Nonempty G] (ξ : A →+* K) (hB : ∀ b, ‖ξ (algebraMap B A b)‖ ≤ 1) (s : G → A)
    (hfg : (Submodule.span B (Set.range s)).FG) : ∃ g₀, ∀ g, ‖ξ (s g)‖ ≤ ‖ξ (s g₀)‖ := by
  classical
  obtain ⟨U, hUs, hU⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  have bound : ∀ m : ℝ, 0 ≤ m → (∀ a ∈ U, ‖ξ a‖ ≤ m) → ∀ g, ‖ξ (s g)‖ ≤ m := by
    intro m hm hUm
    have key : ∀ x ∈ Submodule.span B (U : Set A), ‖ξ x‖ ≤ m := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact hUm x hx
      | zero => simpa using hm
      | add x y _ _ hx hy =>
        rw [map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
      | smul b x _ hx =>
        rw [Algebra.smul_def, map_mul, norm_mul]
        calc ‖ξ (algebraMap B A b)‖ * ‖ξ x‖ ≤ 1 * m :=
              mul_le_mul (hB b) hx (norm_nonneg _) zero_le_one
          _ = m := one_mul m
    intro g
    exact key _ (hU ▸ Submodule.subset_span ⟨g, rfl⟩)
  rcases U.eq_empty_or_nonempty with hE | hne
  · obtain ⟨g₀⟩ := ‹Nonempty G›
    exact ⟨g₀, bound _ (norm_nonneg _) (by simp [hE])⟩
  · obtain ⟨a, ha, hmax⟩ := U.exists_max_image (fun a => ‖ξ a‖) hne
    obtain ⟨g₀, rfl⟩ := hUs ha
    exact ⟨g₀, bound _ (norm_nonneg _) hmax⟩

private theorem scale_core {O B A K G I : Type} [CommRing O] [CommRing B] [CommRing A] [NormedField K]
    [IsUltrametricDist K] [IsAlgClosed K] [Algebra O A] [Algebra O K] [Algebra B A] [Nonempty G] [Finite I]
    (x : K) (hx : 1 < ‖x‖) (gr : ℤ → Submodule B A) (h1 : DirectSum.IsInternal gr) (h2 : SetLike.GradedMonoid gr)
    (h0 : ∀ b : B, algebraMap B A b ∈ gr 0) (hO : ∀ c : O, algebraMap O A c ∈ gr 0)
    (w : I → ℤ) (hw : ∀ i j, i ≠ j → w i - w j ≠ 0) (r : G → I → I → A)
    (hr : ∀ g i j, r g i j ∈ gr (w i - w j))
    (hfg : ∀ i j, (Submodule.span B (Set.range fun g => r g i j)).FG) (ξ : A →ₐ[O] K)
    (hB : ∀ b, ‖ξ (algebraMap B A b)‖ ≤ 1)
    (hcyc : ∀ L : List (G × I × I), (L.map fun s => w s.2.1 - w s.2.2).sum = 0 → (∃ s ∈ L, s.2.1 ≠ s.2.2) →
      ‖ξ (L.map fun s => r s.1 s.2.1 s.2.2).prod‖ < 1) :
    ∃ ξ' : A →ₐ[O] K, (∀ b, ξ' (algebraMap B A b) = ξ (algebraMap B A b)) ∧
      (∀ j, ∀ a ∈ gr j, ξ' a = 0 ↔ ξ a = 0) ∧ ∀ g i j, i ≠ j → ‖ξ' (r g i j)‖ < 1 := by
  classical
  have hmax : ∀ p : {p : I × I // p.1 ≠ p.2}, ∃ g₀ : G,
      ∀ g, ‖ξ (r g p.1.1 p.1.2)‖ ≤ ‖ξ (r g₀ p.1.1 p.1.2)‖ := fun p =>
    exists_max_entry (B := B) ξ.toRingHom hB (fun g => r g p.1.1 p.1.2) (hfg p.1.1 p.1.2)
  choose g₀ hg₀ using hmax
  have hc : ∀ p q : {p : I × I // p.1 ≠ p.2}, 0 < w p.1.1 - w p.1.2 → w q.1.1 - w q.1.2 < 0 →
      ‖ξ (r (g₀ p) p.1.1 p.1.2)‖ ^ (-(w q.1.1 - w q.1.2)).toNat *
        ‖ξ (r (g₀ q) q.1.1 q.1.2)‖ ^ (w p.1.1 - w p.1.2).toNat < 1 := by
    intro p q hp hq
    have e1 : (((-(w q.1.1 - w q.1.2)).toNat : ℕ) : ℤ) = -(w q.1.1 - w q.1.2) := Int.toNat_of_nonneg (by omega)
    have e2 : (((w p.1.1 - w p.1.2).toNat : ℕ) : ℤ) = w p.1.1 - w p.1.2 := Int.toNat_of_nonneg (by omega)
    have hsum : ((List.replicate (-(w q.1.1 - w q.1.2)).toNat (g₀ p, p.1.1, p.1.2) ++
        List.replicate (w p.1.1 - w p.1.2).toNat (g₀ q, q.1.1, q.1.2)).map
          fun s => w s.2.1 - w s.2.2).sum = 0 := by
      simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate, nsmul_eq_mul]
      rw [e1, e2]
      ring
    have hex : ∃ s ∈ List.replicate (-(w q.1.1 - w q.1.2)).toNat (g₀ p, p.1.1, p.1.2) ++
        List.replicate (w p.1.1 - w p.1.2).toNat (g₀ q, q.1.1, q.1.2), s.2.1 ≠ s.2.2 := by
      refine ⟨(g₀ p, p.1.1, p.1.2), ?_, p.2⟩
      rw [List.mem_append, List.mem_replicate]
      exact Or.inl ⟨by omega, rfl⟩
    have h := hcyc _ hsum hex
    simpa only [List.map_append, List.map_replicate, List.prod_append, List.prod_replicate, map_mul, map_pow,
      norm_mul, norm_pow] using h
  obtain ⟨u, hu, hu'⟩ := exists_scale (P := {p : I × I // p.1 ≠ p.2}) x hx (fun p => w p.1.1 - w p.1.2)
    (fun p => ‖ξ (r (g₀ p) p.1.1 p.1.2)‖) (fun p => norm_nonneg _) (fun p => hw _ _ p.2) hc
  obtain ⟨ξ', hξ'⟩ := twist gr h1 h2 hO ξ u hu
  refine ⟨ξ', fun b => ?_, fun j c hc' => ?_, fun g i j hij => ?_⟩
  · rw [hξ' 0 _ (h0 b), zpow_zero, one_mul]
  · rw [hξ' j c hc']
    simp [zpow_ne_zero _ hu]
  · rw [hξ' _ _ (hr g i j), norm_mul, norm_zpow]
    calc ‖u‖ ^ (w i - w j) * ‖ξ (r g i j)‖
        ≤ ‖u‖ ^ (w i - w j) * ‖ξ (r (g₀ ⟨(i, j), hij⟩) i j)‖ :=
          mul_le_mul_of_nonneg_left (hg₀ ⟨(i, j), hij⟩ g) (zpow_nonneg (norm_nonneg _) _)
      _ < 1 := hu' ⟨(i, j), hij⟩

private theorem w_sub_ne {n : ℕ} (hn : n = 2 ∨ n = 3) (i j : Fin n) (h : i ≠ j) : Fr.w n i - Fr.w n j ≠ 0 := by
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp_all [Fr.w]

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.J.scale :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ ξ : S.A →ₐ[c.O] Qbar l, S.u.OffTri (RingHom.ker ξ) →
          ∃ ξ' : S.A →ₐ[c.O] Qbar l, VPt S ξ' ∧ ξ'.comp S.inc = ξ.comp S.inc ∧
            (∀ (j : ℤ), ∀ a ∈ S.gr j, ξ' a = 0 ↔ ξ a = 0) := by
  intro l _ c _ F C₀ n hF hn S ξ _
  obtain ⟨hco, hmB⟩ := Fr.co_B hF hn S
  haveI := hco
  obtain ⟨hcone, -⟩ := Fr.cone_u hF hn S
  obtain ⟨hint, hgm, hgr0, -, -, -, hrgr⟩ := Fr.gr_A hF hn S
  obtain ⟨-, hy1, hy2⟩ := coPt l c S.B (ξ.comp S.inc)
  haveI : Nonempty F.G0 := ⟨F.g0⟩
  have hx : 1 < ‖(((l : ℚ_[l])⁻¹ : ℚ_[l]) : Qbar l)‖ := by
    rw [PadicAlgCl.norm_extends, norm_inv, Padic.norm_p, inv_inv]
    exact_mod_cast (Fact.out : l.Prime).one_lt
  have h0 : ∀ b : S.B, algebraMap S.B S.A b ∈ S.gr 0 := by
    intro b
    rw [hgr0, Submodule.mem_one]
    exact ⟨b, rfl⟩
  have hO : ∀ o : c.O, algebraMap c.O S.A o ∈ S.gr 0 := fun o => h0 (algebraMap c.O S.B o)
  have hB : ∀ b, ‖ξ (algebraMap S.B S.A b)‖ ≤ 1 := fun b => hy1 b
  have hcyc : ∀ L : List (F.G0 × Fin n × Fin n), (L.map fun s => Fr.w n s.2.1 - Fr.w n s.2.2).sum = 0 →
      (∃ s ∈ L, s.2.1 ≠ s.2.2) → ‖ξ (L.map fun s => S.u.r s.1 s.2.1 s.2.2).prod‖ < 1 := by
    intro L hs hne
    obtain ⟨b, hb, hbe⟩ := hcone.cyc L hs hne
    rw [← hbe]
    exact hy2 b hb
  obtain ⟨ξ', hξB, hz, hoff⟩ := scale_core _ hx S.gr hint hgm h0 hO (Fr.w n) (w_sub_ne hn) S.u.r hrgr
    hcone.fg ξ hB hcyc
  have hξB' : ∀ b, ξ' (S.inc b) = ξ (S.inc b) := hξB
  have hinc : ξ'.comp S.inc = ξ.comp S.inc := AlgHom.ext fun b => hξB' b
  refine ⟨ξ', ⟨⟨?_, ?_⟩, hoff⟩, hinc, hz⟩
  · rintro ⟨a, ha⟩
    have ha' : a ∈ Algebra.adjoin c.O ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j}) := ha
    refine Algebra.adjoin_induction (p := fun x hx => ‖ξ' ⟨x, hx⟩‖ ≤ 1) ?_ ?_ ?_ ?_ ha'
    · intro x hx
      rcases hx with hxB | ⟨g, i, j, rfl⟩
      · show ‖ξ' (S.inc ⟨x, hxB⟩)‖ ≤ 1
        rw [hξB']
        exact hy1 _
      · by_cases hij : i = j
        · subst hij
          show ‖ξ' (S.inc (S.aB g i))‖ ≤ 1
          rw [hξB']
          exact hy1 _
        · exact (hoff g i j hij).le
    · intro o
      show ‖ξ' (S.inc (algebraMap c.O S.B o))‖ ≤ 1
      rw [hξB']
      exact hy1 _
    · intro x y hx hy ihx ihy
      show ‖ξ' (⟨x, hx⟩ + ⟨y, hy⟩)‖ ≤ 1
      rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ihx ihy)
    · intro x y hx hy ihx ihy
      show ‖ξ' (⟨x, hx⟩ * ⟨y, hy⟩)‖ ≤ 1
      rw [map_mul, norm_mul]
      exact mul_le_one₀ ihx (norm_nonneg _) ihy
  · intro b hb
    rw [hξB']
    exact hy2 b (hmB ▸ hb)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.ScalarIrreducibility.ExtIntegral
set_option linter.overlappingInstances false

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

namespace UpperTheory.V.J.ChevalleyRestriction

private theorem main_fin (A : Type) [CommRing A] [IsDomain A] (s : Finset A) :
    ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra B A],
      Algebra.adjoin B (s : Set A) = ⊤ → Function.Injective (algebraMap B A) →
      ∀ a : A, a ≠ 0 → ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K),
        y b ≠ 0 → ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Ra5.main_fin A s

end UpperTheory.V.J.ChevalleyRestriction

theorem UpperTheory.V.J.chev :
    ∀ (B A : Type) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A] [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) →
        ∀ a : A, a ≠ 0 → ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K), y b ≠ 0 →
          ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 := by
  intro B A _ _ _ _ _ hft hinj a ha
  obtain ⟨s, hs⟩ := hft.out
  exact UpperTheory.V.J.ChevalleyRestriction.main_fin A s B hs hinj a ha
end

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

private theorem chev_prime (B A : Type) [CommRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A]
    (P : Ideal A) [P.IsPrime] (a : A) (ha : a ∉ P) :
    ∃ b : B, b ∉ P.comap (algebraMap B A) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K),
      P.comap (algebraMap B A) ≤ RingHom.ker y → y b ≠ 0 →
        ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 ∧ P ≤ RingHom.ker ξ := by
  set p := P.comap (algebraMap B A)
  haveI : Algebra.FiniteType B (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ B P) (Ideal.Quotient.mkₐ_surjective B P)
  haveI : Algebra.FiniteType (B ⧸ p) (A ⧸ P) :=
    Algebra.FiniteType.of_restrictScalars_finiteType B (B ⧸ p) (A ⧸ P)
  obtain ⟨b', hb'0, hb'⟩ := UpperTheory.V.J.chev (B ⧸ p) (A ⧸ P) Ideal.algebraMap_quotient_injective
    (Ideal.Quotient.mk P a) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  refine ⟨b, ?_, ?_⟩
  · rwa [Ne, Ideal.Quotient.eq_zero_iff_mem] at hb'0
  · intro K _ _ y hy hyb
    let y' : B ⧸ p →+* K := Ideal.Quotient.lift p y (fun x hx => (RingHom.mem_ker).mp (hy hx))
    obtain ⟨ξ', hξ'1, hξ'2⟩ := hb' K y' (by simpa [y'] using hyb)
    refine ⟨ξ'.comp (Ideal.Quotient.mk P), ?_, hξ'2, ?_⟩
    · ext x
      have h := congrArg (fun f => f (Ideal.Quotient.mk p x)) hξ'1
      simp only [RingHom.comp_apply, y', Ideal.Quotient.lift_mk] at h ⊢
      exact h
    · intro x hx
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

private theorem gen_out {R : Type} [CommRing R] {s : Set R} {P : Ideal R} (h : ¬ Ideal.span s ≤ P) :
    ∃ x ∈ s, x ∉ P := by
  by_contra hc
  push_neg at hc
  exact h (Ideal.span_le.2 hc)

set_option synthInstance.maxHeartbeats 200000 in
theorem UpperTheory.V.J.genPt :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) [Fr.IsCoef l c.O] (F : Fr.Frame l (ResidueField c.O)) (C₀ n : ℕ), F.Ok C₀ → (n = 2 ∨ n = 3) →
        ∀ (S : Fr.Space c.O F n), ∀ (P : Ideal S.A) (Gd : (S.B →ₐ[c.O] Qbar l) → Prop), P ∈ minimalPrimes S.A → S.u.TI P →
          (∀ b ∉ S.π P, ∃ y : S.B →ₐ[c.O] Qbar l, S.π P ≤ RingHom.ker y ∧ Gd y ∧ y b ≠ 0) →
          ∃ ξ : S.A →ₐ[c.O] Qbar l, VPt S ξ ∧ S.u.TI (RingHom.ker ξ) ∧ P ≤ RingHom.ker ξ ∧ Gd (ξ.comp S.inc) := by
  intro l _ c _ F C₀ n hF hn S P Gd hP hTI hext
  obtain ⟨-, -, hgr0, -, hFT, -, hr⟩ := Fr.gr_A hF hn S
  haveI := hFT
  haveI hPp : P.IsPrime := hP.1.1
  have hTI' : (¬ S.u.triP ≤ P ∧ ¬ S.u.triM ≤ P) ∧ (n = 3 → ¬ S.u.ee ≤ P) := hTI
  obtain ⟨x1, ⟨g1, i1, j1, hlt1, rfl⟩, hx1⟩ :=
    gen_out (s := {x | ∃ g i, ∃ j < i, x = S.u.r g i j}) hTI'.1.1
  obtain ⟨x2, ⟨g2, i2, j2, hlt2, rfl⟩, hx2⟩ :=
    gen_out (s := {x | ∃ g i j, i < j ∧ x = S.u.r g i j}) hTI'.1.2
  obtain ⟨x3, ⟨k3, hx3k⟩, hx3P, hx3ee⟩ :
      ∃ x3 : S.A, (∃ k, x3 ∈ S.gr k) ∧ x3 ∉ P ∧ (n = 3 → x3 ∈ S.u.ee) := by
    by_cases h3 : n = 3
    · obtain ⟨x, ⟨g, i, j, hodd, rfl⟩, hx⟩ :=
        gen_out (s := {x | ∃ g i j, Odd (Fr.w n i - Fr.w n j) ∧ x = S.u.r g i j}) (hTI'.2 h3)
      exact ⟨_, ⟨_, hr g i j⟩, hx, fun _ => Ideal.subset_span ⟨g, i, j, hodd, rfl⟩⟩
    · refine ⟨1, ⟨0, ?_⟩, (Ideal.ne_top_iff_one P).mp hPp.ne_top, fun h => absurd h h3⟩
      rw [hgr0]
      exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have ha : S.u.r g1 i1 j1 * S.u.r g2 i2 j2 * x3 ∉ P := by
    intro h
    rcases hPp.mem_or_mem h with h | h
    · rcases hPp.mem_or_mem h with h | h
      · exact hx1 h
      · exact hx2 h
    · exact hx3P h
  obtain ⟨b, hbP, hb⟩ := chev_prime S.B S.A P _ ha
  obtain ⟨y, hyP, hGd, hyb⟩ := hext b hbP
  obtain ⟨ξ0, hξ0, hξ0a, hPξ0⟩ := hb (Qbar l) (y : S.B →+* Qbar l) (fun x hx => hyP hx) hyb
  have hξ0' : ∀ x : S.B, ξ0 (S.inc x) = y x := fun x =>
    congrArg (fun f : S.B →+* Qbar l => f x) hξ0
  let ξ1 : S.A →ₐ[c.O] Qbar l :=
    { ξ0 with
      commutes' := fun r => by
        show ξ0 (algebraMap c.O S.A r) = algebraMap c.O (Qbar l) r
        rw [← S.inc.commutes r, hξ0', y.commutes r] }
  have hcomp : ξ1.comp S.inc = y := by
    ext x
    exact hξ0' x
  rw [map_mul, map_mul, mul_ne_zero_iff, mul_ne_zero_iff] at hξ0a
  obtain ⟨⟨h1, h2⟩, h3⟩ := hξ0a
  have hoff : S.u.OffTri (RingHom.ker ξ1) :=
    ⟨fun h => h1 (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g1, i1, j1, hlt1, rfl⟩))),
      fun h => h2 (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g2, i2, j2, hlt2, rfl⟩)))⟩
  obtain ⟨ξ', hV, hc', hz⟩ := UpperTheory.V.J.scale l c F C₀ n hF hn S ξ1 hoff
  have hTIξ : S.u.TI (RingHom.ker ξ') :=
    ⟨⟨fun h => h1 ((hz _ _ (hr g1 i1 j1)).mp
        (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g1, i1, j1, hlt1, rfl⟩)))),
      fun h => h2 ((hz _ _ (hr g2 i2 j2)).mp
        (RingHom.mem_ker.mp (h (Ideal.subset_span ⟨g2, i2, j2, hlt2, rfl⟩))))⟩,
      fun hn3 h => h3 ((hz _ _ hx3k).mp (RingHom.mem_ker.mp (h (hx3ee hn3))))⟩
  refine ⟨ξ', hV, hTIξ, ?_, ?_⟩
  · intro x hx
    have hh := Fr.min_hom hF hn S P hP
    unfold Fr.Space.IsHom at hh
    rw [hh] at hx
    refine (Ideal.span_le.mpr ?_) hx
    rintro z ⟨hzP, k, hzk⟩
    exact RingHom.mem_ker.mpr ((hz k z hzk).mpr (RingHom.mem_ker.mp (hPξ0 hzP)))
  · rw [hc', hcomp]
    exact hGd
