module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedAlgebraExists
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FixedCentraliserReg

theorem fixed_algebra_exists : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β Y : G.Cˣ),
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : CommRing L) (_ : IsReduced L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L) (ι : L →ₐ[ℚ] G.C), Function.Injective ι ∧
      ∀ c : G.C, c ∈ Set.range ι ↔ Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c := by
  intro p _ G β Y hsep hdeg
  have hcomm : ∀ a b : G.C, Commute a (Y : G.C) → Commute b (Y : G.C) → Commute a b :=
    fun a b ha hb => GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G (Y : G.C) hsep hdeg a b ha hb
  have hshmul : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := by
    intro x y; simp only [sh, map_mul, MulOpposite.unop_mul]
  have hshadd : ∀ x y : G.C, sh G (x + y) = sh G x + sh G y := by
    intro x y; simp only [sh, map_add (f := _), MulOpposite.unop_add]
  have hshalg : ∀ q : ℚ, sh G (algebraMap ℚ G.C q) = algebraMap ℚ G.C q := by
    intro q
    have h := RingHom.congr_fun (RingHom.ext_rat (G.star.comp (algebraMap ℚ G.C)) (algebraMap ℚ G.Cᵐᵒᵖ)) q
    simp only [RingHom.comp_apply, MulOpposite.algebraMap_apply] at h
    simp only [sh, h, MulOpposite.unop_op]
  have hββ : ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) = 1 := by simp
  let S : Subalgebra ℚ G.C :=
    { carrier := {c | Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨ha1.mul_left hb1, ?_⟩
        calc (β : G.C) * sh G (a * b) * ((β⁻¹ : G.Cˣ) : G.C)
            = ((β : G.C) * sh G b * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G a * ((β⁻¹ : G.Cˣ) : G.C)) := by
              rw [hshmul]
              simp only [mul_assoc]
              rw [← mul_assoc ((β⁻¹ : G.Cˣ) : G.C) (β : G.C), hββ, one_mul]
          _ = b * a := by rw [ha2, hb2]
          _ = a * b := (hcomm a b ha1 hb1).eq.symm
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨ha1.add_left hb1, ?_⟩
        rw [hshadd, mul_add, add_mul, ha2, hb2]
      algebraMap_mem' := by
        intro q
        refine ⟨Algebra.commutes q _, ?_⟩
        rw [hshalg, ← Algebra.commutes q (β : G.C), mul_assoc, Units.mul_inv, mul_one] }
  letI cr : CommRing S :=
    { (inferInstance : Ring S) with
      mul_comm := fun a b => Subtype.ext (hcomm a b a.2.1 b.2.1).eq }
  have hred : IsReduced S := by
    refine ⟨fun x ⟨k, hk⟩ => Subtype.ext ?_⟩
    have hk' : (x : G.C) ^ k = 0 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero p G (Y : G.C) hsep hdeg x x.2.1 k hk'
  haveI := G.towerC
  haveI := G.finC
  haveI : FiniteDimensional ℚ G.C := Module.Finite.trans G.F G.C
  have hfd : FiniteDimensional ℚ S :=
    Module.Finite.of_injective (S.val.toLinearMap) Subtype.val_injective
  refine ⟨S, cr, hred, S.algebra, hfd, S.val, Subtype.val_injective, fun c => ?_⟩
  constructor
  · rintro ⟨x, rfl⟩; exact x.2
  · intro h; exact ⟨⟨c, h⟩, rfl⟩

end GlobalTheory.FixedCentraliserReg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeFixedCentraliserAlg
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical


open GlobalTheory.FinClsLoc.BaseChangeCent in
theorem GlobalTheory.FinClsLoc.baseChange_fixedCentraliser_alg :
  ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β Y : G.Cˣ) (L : Type) [Ring L] [Algebra ℚ L] (ι : L →ₐ[ℚ] G.C),
    Function.Injective ι →
    (∀ c : G.C, c ∈ Set.range ι ↔ Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c) →
    ∀ (K : Type) [Field K] [Algebra ℚ K],
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) ι) ∧
      ∀ x : K ⊗[ℚ] G.C, x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id K K) ι) ↔
        Commute x (inC G K (Y : G.C)) ∧
          inC G K (β : G.C) * (starT G.star K x).unop * inC G K ((β⁻¹ : G.Cˣ) : G.C) = x := by
  intro p _ G β Y L _ _ ι hinj hrange K _ _
  have hmap : ∀ z, Algebra.TensorProduct.map (AlgHom.id K K) ι z = (ι.toLinearMap.lTensor K) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul k l => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hex : Function.Exact ι.toLinearMap (phi G β Y ((β⁻¹ : G.Cˣ) : G.C)) := by
    intro c
    change _ ↔ c ∈ Set.range ι
    rw [phi_apply, hrange c, Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero]
    rfl
  have hex' := Module.Flat.lTensor_exact K hex
  refine ⟨?_, ?_⟩
  · have := Module.Flat.lTensor_preserves_injective_linearMap (M := K) ι.toLinearMap hinj
    intro a b hab
    apply this
    rw [← hmap, ← hmap, hab]
  · intro x
    have e1 : x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id K K) ι) ↔
        x ∈ Set.range (ι.toLinearMap.lTensor K) := by
      constructor <;> rintro ⟨z, rfl⟩ <;> exact ⟨z, by rw [hmap]⟩
    rw [e1, ← hex' x, ← (TensorProduct.prodRight ℚ ℚ K G.C G.C).map_eq_zero_iff, lTensor_phi,
      Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero]
    exact and_congr Iff.rfl Iff.rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSqSubMulSq
open scoped TensorProduct
open IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.OddLocalNormEtale

theorem exists_eq_sq_sub_mul_sq : ∀ (L : Type) [CommRing L] [IsReduced L] [Algebra ℚ L] [FiniteDimensional ℚ L] (v : IsDedekindDomain.HeightOneSpectrum ℤ), v.asIdeal ≠ Ideal.span {2} →
    ∀ m m' d d' : v.adicCompletion ℚ ⊗[ℚ] L, m * m' = 1 → d * d' = 1 →
    (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval m f = 0) → (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval m' f = 0) → (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval d f = 0) → (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval d' f = 0) →
    ∃ a b : v.adicCompletion ℚ ⊗[ℚ] L, m = a * a - d * (b * b) := by
  intro L _ _ _ _ v hv m m' d d' hm hd im im' id id'
  obtain ⟨hH, hF⟩ := GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField v
  letI : Algebra (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) :=
    ((algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)).comp
      (v.adicCompletionIntegers ℚ).subtype).toAlgebra
  have key : ∀ x : v.adicCompletion ℚ ⊗[ℚ] L,
      (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧
        (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval x f = 0) →
      IsIntegral (v.adicCompletionIntegers ℚ) x := by
    rintro x ⟨f, hf, hc, hx⟩
    obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (f := (v.adicCompletionIntegers ℚ).subtype)
      ((Polynomial.lifts_iff_coeff_lifts f).2 fun n => ⟨⟨_, hc n⟩, rfl⟩) hf
    refine ⟨g, hgm, ?_⟩
    rw [← hg, Polynomial.aeval_def, Polynomial.eval₂_map] at hx
    exact hx
  have h2 : (2 : ℤ) ∉ v.asIdeal := fun h =>
    hv ((PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible).eq_of_le
      v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm
  have h2u : IsUnit (2 : v.adicCompletionIntegers ℚ) := by
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have h := valuedAdicCompletion_eq_valuation' v (2 : ℚ)
    have h' : v.valuation ℚ (2 : ℚ) = 1 := by
      have := (valuation_eq_one_iff_notMem v (K := ℚ) (r := (2 : ℤ))).2 h2
      simpa using this
    rw [h'] at h
    rw [← h]
    congr 1
    exact (map_ofNat (algebraMap ℚ (v.adicCompletion ℚ)) 2).symm
  exact GlobalTheory.OddLocalNorm.exists_eq_of_isIntegral (v.adicCompletionIntegers ℚ) h2u hm hd
    (key _ im) (key _ im') (key _ id) (key _ id')

end GlobalTheory.OddLocalNormEtale
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTauFixedUnitCentralizerIsNorm
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical


open GlobalTheory.LocNormTau in
theorem GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G (β : G.C) = β →
    ∀ (Y : G.Cˣ) (s : ℚ), (Y : G.C) * β * sh G (Y : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) →
      IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) → IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β hβ Y s hY hsep hdeg
  obtain ⟨f, hf0, hfc⟩ := exists_conj_neg G
  set e : G.C := algebraMap G.F G.C f with he_def
  set e' : G.C := algebraMap G.F G.C f⁻¹ with he'_def
  have hecomm : ∀ c : G.C, Commute e c := fun c => Algebra.commutes f c
  have he'comm : ∀ c : G.C, Commute e' c := fun c => Algebra.commutes f⁻¹ c
  have hee' : e * e' = 1 := by rw [he_def, he'_def, ← map_mul, mul_inv_cancel₀ hf0, map_one]
  have hsh_e : sh G e = -e := by
    simp only [sh, he_def, G.star_F, hfc, map_neg]
  have hsh_e' : sh G e' = -e' := by
    simp only [sh, he'_def, G.star_F, map_inv₀, hfc, inv_neg, map_neg]
  have hτe : (β : G.C) * sh G e * ((β⁻¹ : G.Cˣ) : G.C) = -e := by
    rw [hsh_e, mul_neg, neg_mul, (hecomm _).symm.eq, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨L, _, _, _, _, ι, hιinj, hιrange⟩ := GlobalTheory.FixedCentraliserReg.fixed_algebra_exists p G β Y hsep hdeg
  have hee : e * e ∈ Set.range ι := by
    refine (hιrange _).2 ⟨(hecomm _).mul_left (hecomm _), ?_⟩
    rw [sh_mul, hsh_e, neg_mul_neg, ← ((hecomm (β : G.C)).mul_left (hecomm _)).eq, mul_assoc, Units.mul_inv,
      mul_one]
  have hee'' : e' * e' ∈ Set.range ι := by
    refine (hιrange _).2 ⟨(he'comm _).mul_left (he'comm _), ?_⟩
    rw [sh_mul, hsh_e', neg_mul_neg, ← ((he'comm (β : G.C)).mul_left (he'comm _)).eq, mul_assoc, Units.mul_inv,
      mul_one]
  obtain ⟨d, hd⟩ := hee
  obtain ⟨di, hdi⟩ := hee''
  have hddi : d * di = 1 := hιinj (by
    rw [map_mul, hd, hdi, map_one, mul_assoc, ← mul_assoc e e', hee', one_mul, hee'])
  have hne2 : ∀ᶠ w : AwayP p in Filter.cofinite, w.1.asIdeal ≠ Ideal.span {2} := by
    rw [Filter.eventually_cofinite]
    refine Set.Subsingleton.finite ?_
    intro w₁ h₁ w₂ h₂
    simp only [Set.mem_setOf_eq, not_not] at h₁ h₂
    exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext (h₁.trans h₂.symm))
  filter_upwards [hne2, GlobalTheory.T.eventually_isIntegral_of_integralCoordsLocalTensor p G, GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion p G (ι d), GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion p G (ι di)] with w h2 hint hId hId'
  intro m hmY hmI hmI' hmτ
  set K := w.1.adicCompletion ℚ
  obtain ⟨hΦinj, hΦrange⟩ := GlobalTheory.FinClsLoc.baseChange_fixedCentraliser_alg p G β Y L ι hιinj hιrange K
  set Φ := Algebra.TensorProduct.map (AlgHom.id K K) ι with hΦ
  have hmτ' : tauR G β K (m : K ⊗[ℚ] G.C) = m := hmτ
  have hm'τ : tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) = ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) := by
    have h1 : tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) * (m : K ⊗[ℚ] G.C) = 1 := by
      rw [← hmτ', ← tauR_mul, Units.mul_inv, tauR_one]
    calc _ = tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) * ((m : K ⊗[ℚ] G.C) * ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C)) := by
          rw [Units.mul_inv, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  obtain ⟨y, hy⟩ := (hΦrange m).2 ⟨hmY, hmτ⟩
  obtain ⟨y', hy'⟩ := (hΦrange ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C)).2 ⟨hmY.units_inv_left, hm'τ⟩
  have hyy' : y * y' = 1 := hΦinj (by rw [map_mul, hy, hy', Units.mul_inv, map_one])
  set dK : K ⊗[ℚ] L := (1 : K) ⊗ₜ d
  set dK' : K ⊗[ℚ] L := (1 : K) ⊗ₜ di
  have hdd' : dK * dK' = 1 := by
    simp only [dK, dK', Algebra.TensorProduct.tmul_mul_tmul, one_mul, hddi]
    rfl
  have hΦd : Φ dK = inC G K (ι d) := by
    simp only [hΦ, dK, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have hΦd' : Φ dK' = inC G K (ι di) := by
    simp only [hΦ, dK', Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have pull : ∀ z : K ⊗[ℚ] L, IntC G w (Φ z) →
      ∃ g : Polynomial K, g.Monic ∧ (∀ i, g.coeff i ∈ w.1.adicCompletionIntegers ℚ) ∧ Polynomial.aeval z g = 0 := by
    intro z hz
    obtain ⟨g, hg1, hg2, hg3⟩ := hint _ hz
    refine ⟨g, hg1, hg2, hΦinj ?_⟩
    rw [← Polynomial.aeval_algHom_apply, hg3, map_zero]
  obtain ⟨a', b', hab⟩ := GlobalTheory.OddLocalNormEtale.exists_eq_sq_sub_mul_sq L w.1 h2 y y' dK dK' hyy' hdd'
    (pull y (by rw [hy]; exact hmI)) (pull y' (by rw [hy']; exact hmI'))
    (pull dK (by rw [hΦd]; exact hId)) (pull dK' (by rw [hΦd']; exact hId'))
  set a := Φ a'
  set b := Φ b'
  set E := inC G K e
  have haY := ((hΦrange a).1 ⟨a', rfl⟩).1
  have haτ : tauR G β K a = a := ((hΦrange a).1 ⟨a', rfl⟩).2
  have hbY := ((hΦrange b).1 ⟨b', rfl⟩).1
  have hbτ : tauR G β K b = b := ((hΦrange b).1 ⟨b', rfl⟩).2
  have hE : ∀ x : K ⊗[ℚ] G.C, Commute E x := commute_inC_of_forall G K e hecomm
  have hτE : tauR G β K E = -E := by
    rw [tauR_inC, hτe, map_neg]
  have habc : a * b = b * a := by
    simp only [a, b, ← map_mul, mul_comm a' b']
  have hEE : Φ dK = E * E := by rw [hΦd, hd, map_mul]
  have hm : (m : K ⊗[ℚ] G.C) = a * a - E * E * (b * b) := by
    rw [← hy, hab, map_sub, map_mul, map_mul, map_mul, hEE]
  set vv : K ⊗[ℚ] G.C := a + b * E
  have hτv : tauR G β K vv = a - E * b := by
    rw [tauR_add, tauR_mul, haτ, hbτ, hτE, neg_mul, sub_eq_add_neg]
  obtain ⟨key1, key2⟩ := norm_aux a b E (hE a) (hE b) habc
  rw [← hm] at key1 key2
  have hmv : Commute (m : K ⊗[ℚ] G.C) vv := by
    show (m : K ⊗[ℚ] G.C) * vv = vv * m
    calc (m : K ⊗[ℚ] G.C) * vv = vv * (a - E * b) * vv := by rw [key1]
      _ = vv * m := by rw [mul_assoc, key2]
  refine ⟨⟨vv, (a - E * b) * ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C), ?_, ?_⟩, ?_, ?_⟩
  · rw [← mul_assoc, key1, Units.mul_inv]
  · rw [mul_assoc, hmv.units_inv_left.eq, ← mul_assoc, key2, Units.mul_inv]
  · exact haY.add_left (hbY.mul_left (hE _))
  · change (m : K ⊗[ℚ] G.C) = vv * tauR G β K vv
    rw [hτv, key1]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTauFixedUnitCentralizerIsNormStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_tauFixed_unit_centralizer_is_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G (β : G.C) = β →
    ∀ (Y : G.Cˣ) (s : ℚ), (Y : G.C) * β * sh G (Y : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) →
      IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) → IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  first | (exact @GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep) | (exact GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep) | (intros; apply GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep  <;> assumption)
end
