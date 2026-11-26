module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ExistsDescends
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LayeredIsomorphisms.Kmono

@[expose] public section

section -- merged from Development.EtaleCohomology.CyclotomicDiscriminants.SFewOfCut
noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain UpperTheory.V.KL UpperTheory.V.ZK

namespace LateralTheory.Q.SFewOfCut

theorem one_add_pow_eq (w : ℤ) (d : ℕ) : ∃ t : ℤ, (1 + w) ^ d = 1 + w * (d + w * t) := by
  induction d with
  | zero => exact ⟨0, by simp⟩
  | succ d ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨t + d + w * t, by rw [pow_succ, ht]; push_cast; ring⟩

theorem not_dvd_pow_sub_one (l c M d : ℕ) (hl : l.Prime) (hM : M < l ^ c) (hd0 : 0 < d) (hd : d < M) :
    ¬ (l : ℤ) ^ (c + M) ∣ (1 + (l : ℤ) ^ c) ^ d - 1 := by
  obtain ⟨t, ht⟩ := one_add_pow_eq ((l : ℤ) ^ c) d
  have hl0 : (l : ℤ) ^ c ≠ 0 := pow_ne_zero _ (by exact_mod_cast hl.ne_zero)
  rw [ht, add_sub_cancel_left, pow_add, mul_dvd_mul_iff_left hl0]
  intro h
  have key : ∀ j, j ≤ c → j ≤ M → l ^ j ≤ d := by
    intro j hjc hjM
    have h1 : (l : ℤ) ^ j ∣ (d : ℤ) + (l : ℤ) ^ c * t := (pow_dvd_pow _ hjM).trans h
    have h2 : (l : ℤ) ^ j ∣ (d : ℤ) := (dvd_add_left ((pow_dvd_pow _ hjc).mul_right t)).1 h1
    exact Nat.le_of_dvd hd0 (by exact_mod_cast h2)
  rcases le_total c M with h1 | h1
  · have := key c le_rfl h1; omega
  · have := key M h1 le_rfl
    have := Nat.lt_pow_self (n := M) hl.one_lt
    omega

theorem cast_dvd_of_not_dvd (l ν w : ℕ) (hl : l.Prime) (f : ℤ) (hf : ¬ (l : ℤ) ^ w ∣ f) :
    (f : ZMod (l ^ ν)) ∣ (l : ZMod (l ^ ν)) ^ w := by
  induction w generalizing f with
  | zero => simp at hf
  | succ w ih =>
    by_cases h : (l : ℤ) ∣ f
    · obtain ⟨g, rfl⟩ := h
      have hg : ¬ (l : ℤ) ^ w ∣ g := fun h => hf (by rw [pow_succ']; exact mul_dvd_mul_left _ h)
      rw [pow_succ']
      push_cast
      exact mul_dvd_mul_left _ (ih g hg)
    · have hc : IsCoprime f ((l : ℤ) ^ ν) :=
        (((Nat.prime_iff_prime_int.1 hl).irreducible.coprime_iff_not_dvd.2 h).symm).pow_right
      obtain ⟨a, b, hab⟩ := hc
      have h0 : ((l : ZMod (l ^ ν))) ^ ν = 0 := by exact_mod_cast ZMod.natCast_self (l ^ ν)
      have h1 : (f : ZMod (l ^ ν)) * a = 1 := by
        have := congrArg (Int.cast : ℤ → ZMod (l ^ ν)) hab
        push_cast at this
        rw [h0] at this
        linear_combination this
      exact (Dvd.intro _ h1).trans (one_dvd _)

theorem not_dvd_sub (l c M i j : ℕ) (hl : l.Prime) (hc : 1 ≤ c) (hM : M < l ^ c) (hij : j < i) (hi : i < M) :
    ¬ (l : ℤ) ^ (c + M) ∣ (1 + (l : ℤ) ^ c) ^ i - (1 + (l : ℤ) ^ c) ^ j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij.le
  intro h
  have h1 : (1 + (l : ℤ) ^ c) ^ (j + d) - (1 + (l : ℤ) ^ c) ^ j =
      (1 + (l : ℤ) ^ c) ^ j * ((1 + (l : ℤ) ^ c) ^ d - 1) := by ring
  rw [h1] at h
  have hco : IsCoprime (l : ℤ) (1 + (l : ℤ) ^ c) := by
    obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hc
    exact ⟨-(l : ℤ) ^ c', 1, by ring⟩
  exact not_dvd_pow_sub_one l c M d hl hM (by omega) (by omega) (hco.pow.dvd_of_dvd_mul_left h)

theorem pe_dvd (l c ν M E : ℕ) (hl : l.Prime) (hc : 1 ≤ c) (hM : M < l ^ c) (hE : E < M) :
    (pe (1 + l ^ c) M E : ZMod (l ^ ν)) ∣ (l : ZMod (l ^ ν)) ^ (M * (c + M)) := by
  have h1 : (pe (1 + l ^ c) M E : ZMod (l ^ ν)) ∣
      ∏ _j ∈ (Finset.range M).erase E, (l : ZMod (l ^ ν)) ^ (c + M) := by
    unfold pe
    rw [Int.cast_prod]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun j hj => cast_dvd_of_not_dvd l ν _ hl _ ?_
    rw [Finset.mem_erase, Finset.mem_range] at hj
    push_cast
    rcases lt_or_gt_of_ne hj.1 with h | h
    · exact not_dvd_sub l c M E j hl hc hM h hE
    · rw [dvd_sub_comm]
      exact not_dvd_sub l c M j E hl hc hM h hj.2
  refine h1.trans ?_
  rw [Finset.prod_const, ← pow_mul, mul_comm]
  refine pow_dvd_pow _ (Nat.mul_le_mul_right _ ?_)
  exact (Finset.card_erase_le).trans (Finset.card_range M).le

theorem exists_index (G : Type) [CommGroup G] [Finite G] [IsCyclic G] (q : ℕ) (hq : q ∣ Nat.card G) :
    ∃ v : G →* Cq q, ∀ u, v u = 1 → ∃ s, u = s ^ q := by
  let e : Multiplicative (ZMod (Nat.card G)) ≃* G := zmodCyclicMulEquiv inferInstance
  haveI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  refine ⟨(AddMonoidHom.toMultiplicative (ZMod.castHom hq (ZMod q)).toAddMonoidHom).comp e.symm.toMonoidHom, ?_⟩
  intro u hu
  obtain ⟨x, rfl⟩ := e.surjective u
  have h1 : ZMod.castHom hq (ZMod q) (Multiplicative.toAdd x) = 0 := by
    simpa using congrArg Multiplicative.toAdd hu
  obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (Multiplicative.toAdd x)
  rw [← hn, map_natCast, ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨m, rfl⟩ := h1
  refine ⟨e (Multiplicative.ofAdd (m : ZMod _)), ?_⟩
  rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ← Nat.cast_mul, hn, ofAdd_toAdd]

theorem prim_map {R k : Type} [CommRing R] [IsDomain R] [Field k] (r : R →+* k) (l ν : ℕ) (hl : l.Prime)
    (hν : 1 ≤ ν) (hr : r l ≠ 0) (ζ : Rˣ) (hζ : IsPrimitiveRoot ζ (l ^ ν)) :
    IsPrimitiveRoot (Units.map (r : R →* k) ζ) (l ^ ν) := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hν
  have h1 : Units.map (r : R →* k) ζ ^ l ^ (n + 1) = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have h2 : ¬ Units.map (r : R →* k) ζ ^ l ^ n = 1 := by
    intro h
    have h3 : IsPrimitiveRoot ((ζ : R) ^ l ^ n) l :=
      (IsPrimitiveRoot.coe_units_iff.2 hζ).pow (pow_pos hl.pos _) (pow_succ l n)
    have h4 := congrArg r (h3.geom_sum_eq_zero hl.one_lt)
    have h5 : r ((ζ : R) ^ l ^ n) = 1 := by simpa using congrArg Units.val h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h4
    simp only [map_pow r ((ζ : R) ^ l ^ n), h5] at h4
    apply hr
    simpa using h4
  rw [← orderOf_eq_prime_pow h2 h1]
  exact IsPrimitiveRoot.orderOf _

section Res

variable {F : Type} [Field F] {k : Type} [Field k] {r : 𝓞 F →+* k}

theorem res_one : Res r 1 1 := ⟨1, 1, by simp, by simp, by simp⟩

theorem res_mul {α β : Fˣ} {u w : kˣ} (h : Res r α u) (h' : Res r β w) : Res r (α * β) (u * w) := by
  obtain ⟨a, b, hb, h1, h2⟩ := h
  obtain ⟨a', b', hb', h1', h2'⟩ := h'
  refine ⟨a * a', b * b', by rw [map_mul]; exact mul_ne_zero hb hb', ?_, ?_⟩
  · have e1 : ((b * b' : 𝓞 F) : F) = (b : F) * (b' : F) := rfl
    have e2 : ((a * a' : 𝓞 F) : F) = (a : F) * (a' : F) := rfl
    rw [e1, e2, ← h1, ← h1', Units.val_mul]; ring
  · rw [map_mul, map_mul, h2, h2', Units.val_mul]; ring

theorem res_inv {α : Fˣ} {u : kˣ} (h : Res r α u) : Res r α⁻¹ u⁻¹ := by
  obtain ⟨a, b, hb, h1, h2⟩ := h
  refine ⟨b, a, by rw [h2]; exact mul_ne_zero u.ne_zero hb, ?_, ?_⟩
  · rw [← h1, Units.inv_mul_cancel_left]
  · rw [h2, Units.inv_mul_cancel_left]

theorem res_pow {α : Fˣ} {u : kˣ} (h : Res r α u) (n : ℕ) : Res r (α ^ n) (u ^ n) := by
  induction n with
  | zero => simpa using res_one
  | succ n ih => rw [pow_succ, pow_succ]; exact res_mul ih h

end Res

theorem isPrimFam_pi {R A I : Type} [CommRing R] [CommRing A] {m : ℕ}
    (Φ : I → ∀ n : ℕ, Ch A (GL (Fin n) R) (m + 1) →ₗ[A] A) (h : ∀ i, IsPrimFam (Φ i)) :
    IsPrimFam fun n => LinearMap.pi fun i => Φ i n :=
  ⟨fun n z hz => funext fun i => (h i).bdry n z hz, fun n n' hn z hz => funext fun i => (h i).stab n n' hn z hz,
    fun d n z hz => funext fun i => (h i).psi d n z hz⟩

theorem sFewOf : SFewOf := by
  classical
  intro hT hP hC hU hD L F _ _ _ _ _ hL l c ν e hl ζ γ hlay hc hr S hS hinj
  choose 𝔡 h𝔡 using hS
  choose N y b hy hb hval using fun α : S => hC L F l c ν e ζ γ hlay hc α (𝔡 α α.2) (h𝔡 α α.2)
  have hl0 : (l : 𝓞 F) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have hb0 : (l : 𝓞 F) * ∏ α, b α ≠ 0 := mul_ne_zero hl0 (Finset.prod_ne_zero_iff.2 fun α _ => hb α)
  let I : Type := {P : HeightOneSpectrum (𝓞 F) // (l : 𝓞 F) * ∏ α, b α ∉ P.asIdeal ∧
    Function.Surjective ((Ideal.Quotient.mk P.asIdeal).comp (algebraMap (𝓞 L) (𝓞 F)))}
  have main : ∀ P : I, ∃ Φ : ∀ n : ℕ, Ch (ZMod (l ^ ν)) (GL (Fin n) (𝓞 L)) (2 * e + 2 + 1) →ₗ[ZMod (l ^ ν)]
      ZMod (l ^ ν), IsPrimFam Φ ∧ ∀ α α' : S, l ^ (2 * e + 2) • Φ _ (y α) = l ^ (2 * e + 2) • Φ _ (y α') →
        letI := P.1.isMaximal
        letI := Ideal.Quotient.field P.1.asIdeal
        ∃ s : (𝓞 F ⧸ P.1.asIdeal)ˣ, Res (Ideal.Quotient.mk P.1.asIdeal)
          (nrm γ ((1 + l ^ c) ^ (e + 1)) α ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))) *
            (nrm γ ((1 + l ^ c) ^ (e + 1)) α' ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))))⁻¹) (s ^ l ^ ν) := by
    rintro ⟨P, hPb, hPs⟩
    letI := P.isMaximal
    letI := Ideal.Quotient.field P.asIdeal
    haveI : Finite (𝓞 F ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
    have hlP : Ideal.Quotient.mk P.asIdeal (l : 𝓞 F) ≠ 0 := fun h =>
      hPb (Ideal.mul_mem_right _ _ (Ideal.Quotient.eq_zero_iff_mem.1 h))
    have hbP : ∀ α, Ideal.Quotient.mk P.asIdeal (b α) ≠ 0 := fun α h =>
      hPb (Ideal.mem_of_dvd _ ((Finset.dvd_prod_of_mem b (Finset.mem_univ α)).mul_left _)
        (Ideal.Quotient.eq_zero_iff_mem.1 h))
    have hz := prim_map (Ideal.Quotient.mk P.asIdeal) l ν hl.out (hlay.c_pos.trans hlay.c_le) hlP ζ hlay.prim
    obtain ⟨v, hv⟩ := exists_index (𝓞 F ⧸ P.asIdeal)ˣ (l ^ ν) (by rw [hz.eq_orderOf]; exact orderOf_dvd_natCard _)
    obtain ⟨θ, hθ, hθv⟩ := hT _ (l ^ ν) e _ hz v
    refine ⟨_, hP _ _ _ θ hθ (𝓞 L) ((Ideal.Quotient.mk P.asIdeal).comp (algebraMap (𝓞 L) (𝓞 F))), ?_⟩
    intro α α' hαα
    obtain ⟨u, hu, hu1⟩ := hval α _ _ hPs (hbP α) _ v θ hθ hθv
    obtain ⟨u', hu', hu1'⟩ := hval α' _ _ hPs (hbP α') _ v θ hθ hθv
    simp only [LinearMap.comp_apply] at hαα
    rw [hu1, hu1'] at hαα
    obtain ⟨x, hx⟩ := pe_dvd l c ν (2 * e + 3) (e + 1) hl.out hlay.c_pos hc (by omega)
    obtain ⟨s, hs⟩ := hv (u ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))) *
        (u' ^ l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3))))⁻¹) (by
      rw [map_mul, map_inv, map_pow, map_pow, mul_inv_eq_one]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_pow]
      simp only [nsmul_eq_mul, Nat.cast_pow] at hαα ⊢
      rw [pow_add, hx]
      linear_combination x * hαα)
    exact ⟨s, hs ▸ res_mul (res_pow hu _) (res_inv (res_pow hu' _))⟩
  choose Φ hΦ hsep using main
  let f : S → (I → ZMod (l ^ ν)) := fun α => l ^ (2 * e + 2) • (LinearMap.pi fun i => Φ i (N α)) (y α)
  have hf : Function.Injective f := by
    intro α α' h
    obtain ⟨δ, hδ⟩ := hD L F l ν hl.out ζ hlay.prim _ _ hb0 fun P _ hPb hPs =>
      hsep ⟨P, hPb, hPs⟩ α α' (congrFun h ⟨P, hPb, hPs⟩)
    exact Subtype.ext (hinj _ α.2 _ α'.2 ⟨δ, (mul_inv_eq_iff_eq_mul.1 hδ).trans (mul_comm _ _)⟩)
  have hcard := hU L hL (2 * e + 2) ⟨e + 1, by ring⟩ hr l ν (I → ZMod (l ^ ν)) _ (isPrimFam_pi Φ hΦ)
    (Finset.univ.image f) (by
      intro s hs
      obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 hs
      exact ⟨N α, y α, hy α, rfl⟩)
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_coe,
    show 2 * (2 * e + 2 + 1) + 4 = 4 * e + 10 by ring] at hcard
  exact hcard

end LateralTheory.Q.SFewOfCut

end
end

section -- merged from Development.EtaleCohomology.CyclotomicDiscriminants.FinSLayer
section -- merged from Development.EtaleCohomology.CyclotomicDiscriminants.SLayerCut
noncomputable section

open NumberField NumberField.InfinitePlace Polynomial UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Tower

namespace LateralTheory.Q.SLayerCut

theorem disc_cyc (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L'] (N : ℕ)
    (hN : N ≠ 0) [hc : IsCyclotomicExtension {N} L L'] :
    (discr L').natAbs ≤ (discr L).natAbs ^ Module.finrank L L' * N ^ Module.finrank ℚ L' := by
  have : NeZero N := ⟨hN⟩
  have hz := IsCyclotomicExtension.zeta_spec N L L'
  set z := IsCyclotomicExtension.zeta N L L' with hzd
  let x : 𝓞 L' := hz.toInteger
  have hx : x ^ N = 1 := hz.toInteger_isPrimitiveRoot.pow_eq_one
  have hadj : Algebra.adjoin L {algebraMap (𝓞 L') L' x} = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hz
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 L) L L' x hadj
  have hint : IsIntegral (𝓞 L) x := Algebra.IsIntegral.isIntegral x
  have hdvd : minpoly (𝓞 L) x ∣ (X ^ N - 1 : (𝓞 L)[X]) :=
    minpoly.isIntegrallyClosed_dvd hint (by simp [hx])
  obtain ⟨g, hg⟩ := hdvd
  have h1 := congrArg (fun p => aeval x (derivative p) * x) hg
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul, map_add (f := _), map_mul,
    minpoly.aeval, zero_mul, add_zero, map_pow, aeval_X, map_natCast] at h1
  have h2 : (N : 𝓞 L') ∈ differentIdeal (𝓞 L) (𝓞 L') := by
    have h3 : (N : 𝓞 L') = aeval x (derivative (minpoly (𝓞 L) x)) * (aeval x g * x) := by
      rw [← mul_assoc, ← h1, mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hN), hx, mul_one]
    rw [h3]
    exact Ideal.mul_mem_right _ _ hmem
  have h4 : Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 L')) ∣ N ^ Module.finrank ℚ L' := by
    have h5 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 h2)
    rwa [Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h5
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow L (𝓞 L) L' (𝓞 L'), mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero hN) _) h4)

theorem sha_le (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L'] (l E m : ℕ)
    [Fact l.Prime] (hμ : HasMuQ l L) (hE : 1 ≤ E) (h : IsLayer l m L L') : shaInv L l E ≤ shaInv L' l E := by
  obtain ⟨γ, -, -, -, hd⟩ := exists_descends l L (AlgebraicClosure L) hμ
  have h0 : IsLayer l 0 L L := by
    refine ⟨⟨0, ?_⟩, by simp⟩
    have : NeZero (l ^ 0) := ⟨by simp⟩
    rw [IsCyclotomicExtension.iff_singleton]
    exact ⟨⟨1, by simp⟩, fun x => Subalgebra.algebraMap_mem _ x⟩
  rw [hd E hE 0 L h0, hd E hE m L' h, pow_zero, pow_one]
  generalize xTw l l (⊤ : Subgroup (Formalism.ConjugateSelfDual.G L (AlgebraicClosure L))) (E : ℤ) γ = g
  have hr : LinearMap.range (g ^ l ^ m - 1) ≤ LinearMap.range (g - 1) := by
    rw [← mul_geom_sum g (l ^ m), Module.End.mul_eq_comp]
    exact LinearMap.range_comp_le_range _ _
  exact Module.length_le_of_surjective (Submodule.factor hr) (Submodule.factor_surjective hr)

theorem goal_of : UpperTheory.V.ZK.SLayer := by
  intro L _ _ l E hl hμ hE
  have hp : l.Prime := hl.out
  let Ω := AlgebraicClosure L
  let m := Nat.clog l (4 * E + 4)
  have hm1 : 4 * E + 4 ≤ l ^ m := Nat.le_pow_clog hp.one_lt _
  have hm2 : l ^ m ≤ l * (4 * E + 4) := by
    have h1 := Nat.pow_pred_clog_lt_self l (x := 4 * E + 4) (by omega)
    have h2 : 0 < m := Nat.clog_pos hp.one_lt (by omega)
    calc l ^ m = l * l ^ (m - 1) := by rw [← pow_succ', Nat.sub_add_cancel h2]
      _ ≤ _ := Nat.mul_le_mul_left _ h1.le
  have hLay := (layerUniq L Ω l hμ).1 m
  have hcyc := (Kum.fnCyc L Ω l (cZero l L + m)).1
  let L' : Type := layF l L Ω m
  have hμ' : HasMuQ l L' := by
    obtain ⟨ζ, hζ⟩ := hμ
    exact ⟨_, hζ.map_of_injective (algebraMap L L').injective⟩
  obtain ⟨q1, -, q3, q4, -⟩ := muQ L' (AlgebraicClosure L') l
  have htc : IsTotallyComplex L' := (q4 hμ').1
  have hq := q3.1 hμ'
  have hle : cZero l L + m ≤ cZero l L' :=
    (q1 _).1 (hcyc.exists_isPrimitiveRoot (Set.mem_singleton _) (pow_ne_zero _ hp.ne_zero))
  have hdeg : Module.finrank L L' = l ^ m := hLay.2
  have hfin : Module.finrank ℚ L' = l ^ m * Module.finrank ℚ L := by
    rw [← Module.finrank_mul_finrank ℚ L L', hdeg, mul_comm]
  have hpos : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hln : l ≤ Module.finrank ℚ L + 1 := by
    by_cases h2 : l = 2
    · omega
    · obtain ⟨z, hz⟩ := hμ
      rw [if_neg h2] at hz
      have h1 := IsPrimitiveRoot.lcm_totient_le_finrank (K := ℚ) hz hz
        (Polynomial.cyclotomic.irreducible_rat (by rw [Nat.lcm_self]; exact hp.pos))
      rw [Nat.lcm_self, Nat.totient_prime hp] at h1
      omega
  have hpw : l ^ (cZero l L + m) ≤ l ^ cZero l L' := Nat.pow_le_pow_right hp.pos hle
  have hpm : l ^ m ≤ l ^ (cZero l L + m) := Nat.pow_le_pow_right hp.pos (by omega)
  refine ⟨L', inferInstance, inferInstance, cZero l L', l ^ m, htc, ⟨?_, fun h2 => ?_, (q1 _).2 le_rfl, fun h => ?_⟩,
    by omega, ?_, hfin, hm2.trans (Nat.mul_le_mul_right _ hln), Win.rootdeg L' l _ hp ((q1 _).2 le_rfl), ?_,
    sha_le L L' l E m hμ hE hLay⟩
  · unfold Base.qExp at hq
    split_ifs at hq <;> omega
  · unfold Base.qExp at hq
    rwa [if_pos h2] at hq
  · have := (q1 _).1 h
    omega
  · have h1 := IsTotallyComplex.finrank L'
    have h2 : l ^ m ≤ l ^ m * Module.finrank ℚ L := Nat.le_mul_of_pos_right _ hpos
    omega
  · have h1 := disc_cyc L L' (l ^ (cZero l L + m)) (pow_ne_zero _ hp.ne_zero) (hc := hcyc)
    rw [hdeg] at h1
    exact h1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpw _))

end LateralTheory.Q.SLayerCut

end
end

namespace LateralTheory.Fin.SLayer
theorem layer_statement_holds : UpperTheory.V.ZK.SLayer := by
  apply LateralTheory.Q.SLayerCut.goal_of
theorem intersectionNumber_baseChange : UpperTheory.V.ZK.SLayer := layer_statement_holds
end LateralTheory.Fin.SLayer
end

section -- merged from Development.EtaleCohomology.CyclotomicDiscriminants.FinSDetect
section -- merged from Development.EtaleCohomology.CyclotomicDiscriminants.SDetectCut
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.ZK

namespace LateralTheory.Q.SDetectCut

theorem root_eq_one {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) (q : ℕ) (η : R) (hη : η ^ q = 1)
    (h1 : η - 1 ∈ P) (hq : (q : R) ∉ P) : η = 1 := by
  by_contra hne
  apply hq
  have h0 : ∑ i ∈ Finset.range q, η ^ i = 0 := by
    have := mul_geom_sum η q
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have h2 : Ideal.Quotient.mk P η = 1 := by
    rw [← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq]
    exact h1
  have h3 := congrArg (Ideal.Quotient.mk P) h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_pow, h2, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    map_zero] at h3
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h3

theorem surj_of_prime {A k : Type} [CommRing A] [CommRing k] (f : A →+* k) (hp : (Nat.card k).Prime) :
    Function.Surjective f := by
  intro y
  have : Fact (Nat.card k).Prime := ⟨hp⟩
  have : Finite k := Nat.finite_of_card_ne_zero hp.ne_zero
  have : Nontrivial k := Finite.one_lt_card_iff_nontrivial.1 hp.one_lt
  obtain ⟨n, hn⟩ := mem_zmultiples_of_prime_card (G := k) (p := Nat.card k) rfl (g := 1) (g' := y) one_ne_zero
  exact ⟨n, by simpa using hn⟩

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in
theorem val_le (B : ValuationSubring Ω) (x : 𝓞 F) : B.valuation (algebraMap F Ω (x : F)) ≤ 1 := by
  have hz : IsIntegral ℤ (algebraMap F Ω (x : F)) := x.isIntegral_coe.map (algebraMap F Ω).toIntAlgHom
  exact (Valuation.integer.integers B.valuation).mem_of_integral hz.tower_top


omit [NumberField F] in
theorem frob_fix {v : HeightOneSpectrum (𝓞 F)} {B : ValuationSubring Ω} (hB : IsPlaceOver B v) {N : ℕ} (hN : N ≠ 0)
    {σ : G F Ω} (hσ : IsFrob B N σ) {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 F) ∉ v.asIdeal) {ζ : 𝓞 F}
    (hζ : IsPrimitiveRoot ζ q) {β : F} {x : Ω} (hx : x ^ q = algebraMap F Ω β) {a b t : 𝓞 F}
    (hb : b ∉ v.asIdeal) (ht : t ∉ v.asIdeal) (hab : β * b = a) (hc : a - t ^ q * b ∈ v.asIdeal) : σ x = x := by
  have : NeZero q := ⟨hq0⟩
  let ι : 𝓞 F →+* Ω := (algebraMap F Ω).comp (algebraMap (𝓞 F) F)
  have hι : ∀ y : 𝓞 F, ι y = algebraMap F Ω (y : F) := fun _ => rfl
  have hinj : Function.Injective ι := (algebraMap F Ω).injective.comp (RingOfIntegers.coe_injective)
  have hone : ∀ y : 𝓞 F, y ∉ v.asIdeal → B.valuation (ι y) = 1 := fun y hy =>
    le_antisymm (val_le B y) (not_lt.1 fun h => hy ((hB y).1 h))
  have hζ' : IsPrimitiveRoot (ι ζ) q := hζ.map_of_injective hinj
  have h1 : B.valuation (x ^ q - ι t ^ q) < 1 := by
    have e : (x ^ q - ι t ^ q) * ι b = ι (a - t ^ q * b) := by
      rw [hx, map_sub, map_mul, map_pow, sub_mul, hι a, hι b, ← hab, map_mul]
    have := (hB _).2 hc
    rw [← hι, ← e, map_mul, hone b hb, mul_one] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i : ℕ, B.valuation (x - ι (ζ ^ i * t)) < 1 := by
    by_contra! h
    have e := congrArg (Polynomial.eval x) (X_pow_sub_C_eq_prod hζ' (Nat.pos_of_ne_zero hq0) (rfl : ι t ^ q = ι t ^ q))
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_prod] at e
    rw [e, map_prod] at h1
    refine absurd h1 (not_lt.2 (Finset.one_le_prod' fun i _ => ?_))
    have := h i
    rwa [map_mul, map_pow] at this
  set c := ζ ^ i * t with hcdef
  have hcv : c ∉ v.asIdeal := fun h =>
    ht ((v.isPrime.mem_or_mem h).resolve_left fun h' =>
      v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' ((hζ.isUnit hq0).pow i)))
  have hxv : B.valuation x = 1 := by
    rw [← hone c hcv]
    exact Valuation.map_eq_of_sub_lt _ (by rw [hone c hcv]; exact hi)
  have h2 : B.valuation (σ (x - ι c)) < 1 := by
    have e : σ (x - ι c) = (σ (x - ι c) - (x - ι c) ^ N) + (x - ι c) ^ N := by ring
    rw [e]
    refine Valuation.map_add_lt _ (hσ.2 _ hi.le) ?_
    rw [map_pow]
    exact pow_lt_one' hi hN
  have h3 : B.valuation (σ x - x) < 1 := by
    have e : σ x - x = σ (x - ι c) - (x - ι c) := by
      rw [map_sub, hι, AlgEquiv.commutes]; ring
    rw [e]
    exact Valuation.map_sub_lt _ h2 hi
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hxv
  have h4 : (σ x / x) ^ q = 1 := by
    rw [div_pow, ← map_pow, hx, AlgEquiv.commutes, ← hx, div_self (pow_ne_zero _ hx0)]
  obtain ⟨j, -, hj⟩ := hζ'.eq_pow_of_pow_eq_one h4
  have h5 : σ x = ι (ζ ^ j) * x := by rw [map_pow, hj, div_mul_cancel₀ _ hx0]
  have h6 : ζ ^ j - 1 ∈ v.asIdeal := by
    rw [← hB, ← hι]
    have e : σ x - x = ι (ζ ^ j - 1) * x := by rw [h5, map_sub, map_one]; ring
    rwa [e, map_mul, hxv, mul_one] at h3
  have h7 : ζ ^ j = 1 := root_eq_one v.asIdeal q _ (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) h6 hq
  rw [h5, h7, map_one, one_mul]

theorem goal : SDetect := by
  intro L F _ _ _ _ _ l ν hl ζ hζ β b hb H
  have hq0 : l ^ ν ≠ 0 := pow_ne_zero _ hl.ne_zero
  generalize l ^ ν = q at *
  let Ω := AlgebraicClosure F
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F Ω (β : F)) (Nat.pos_of_ne_zero hq0)
  have hS : {v : HeightOneSpectrum (𝓞 F) | b * (q : 𝓞 F) ∈ v.asIdeal}.Finite := by
    simp_rw [← Ideal.dvd_span_singleton]
    exact Ideal.finite_factors (by simp [hb, hq0])
  have : IsGalois F Ω := {}
  have hfix : ∀ g : Ω ≃ₐ[F] Ω, g x = x := by
    intro g
    have hV : IsOpen {σ : G F Ω | σ x = g x} := by
      have h1 : IsOpen (MulAction.stabilizer (Ω ≃ₐ[F] Ω) x : Set (Ω ≃ₐ[F] Ω)) := stabilizer_isOpen_of_isIntegral x
      have h2 := h1.preimage (continuous_const_mul g⁻¹)
      convert h2 using 1
      ext σ
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul,
        inv_smul_eq_iff]
      rfl
    obtain ⟨σ, hσV, v, hv, hd, B, hB, hσ⟩ :=
      (GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
        hS).inter_open_nonempty _ hV ⟨g, rfl⟩
    have hp : (Nat.card (𝓞 F ⧸ v.asIdeal)).Prime := by
      have := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    have := v.isMaximal
    obtain ⟨s, a, b', hb', hab, hr⟩ := H v (fun h => hv (Ideal.mul_mem_right _ _ h)) (surj_of_prime _ hp)
    let := Ideal.Quotient.field v.asIdeal
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (s : 𝓞 F ⧸ v.asIdeal)
    rw [← hσV]
    refine frob_fix hB hp.ne_zero hσ hq0 (fun h => hv (Ideal.mul_mem_left _ _ h))
      (IsPrimitiveRoot.coe_units_iff.2 hζ) hx (a := a) (b := b') (t := t)
      (fun h => hb' (Ideal.Quotient.eq_zero_iff_mem.2 h))
      (fun h => s.ne_zero (ht ▸ Ideal.Quotient.eq_zero_iff_mem.2 h)) hab ?_
    rw [← Ideal.Quotient.eq, map_mul, map_pow, ht, hr, Units.val_pow_eq_pow_val]
  obtain ⟨δ, hδ⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).2 hfix
  have hd : (β : F) = δ ^ q := (algebraMap F Ω).injective (by rw [map_pow, hδ, hx])
  have h0 : δ ≠ 0 := by
    rintro rfl
    exact β.ne_zero (by rw [hd, zero_pow hq0])
  exact ⟨Units.mk0 δ h0, Units.ext (by simpa using hd)⟩

end LateralTheory.Q.SDetectCut
end

namespace LateralTheory.Fin.SDetect
theorem detection_statement_holds : UpperTheory.V.ZK.SDetect := by
  apply LateralTheory.Q.SDetectCut.goal
theorem intersectionNumber_baseChange : UpperTheory.V.ZK.SDetect := detection_statement_holds
end LateralTheory.Fin.SDetect
end

section -- merged from Development.EtaleCohomology.CyclotomicDiscriminants.FinSStein
section -- merged from Development.EtaleCohomology.CyclotomicDiscriminants.SSteinTPf
noncomputable section

open NumberField IsDedekindDomain FractionalIdeal Matrix
open scoped nonZeroDivisors

namespace LateralTheory.Q.SSteinT

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

theorem val_eq_count (P : HeightOneSpectrum R) (x : K) (hx : x ≠ 0) :
    P.valuation K x = WithZero.exp (-count K P (spanSingleton R⁰ x)) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hx
  have h : spanSingleton R⁰ (algebraMap R K r / algebraMap R K s) =
      spanSingleton R⁰ (algebraMap R K s)⁻¹ * ((Ideal.span {r} : Ideal R) : FractionalIdeal R⁰ K) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, div_eq_inv_mul]
  rw [count_well_defined K P (spanSingleton_ne_zero_iff.mpr hx) h, map_div₀,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_if_neg P hr0, HeightOneSpectrum.intValuation_if_neg P hs0,
    ← WithZero.exp_sub]
  congr 1
  ring

theorem val_le_of_mem (P : HeightOneSpectrum R) {I : FractionalIdeal R⁰ K} {x : K} (hx : x ∈ I) :
    P.valuation K x ≤ WithZero.exp (-count K P I) := by
  by_cases h0 : x = 0
  · simp [h0]
  rw [val_eq_count P x h0, WithZero.exp_le_exp, neg_le_neg_iff]
  exact count_mono K P (spanSingleton_ne_zero_iff.mpr h0) (spanSingleton_le_iff_mem.mpr hx)

theorem exists_frac (d : HeightOneSpectrum R →₀ ℤ) :
    ∃ I : FractionalIdeal R⁰ K, I ≠ 0 ∧ ∀ P, count K P I = d P := by
  refine ⟨d.prod fun P n => (P.asIdeal : FractionalIdeal R⁰ K) ^ n, ?_, fun P => count_finsuppProd K P d⟩
  refine Finset.prod_ne_zero_iff.mpr fun P _ => zpow_ne_zero _ ?_
  exact coeIdeal_ne_zero.mpr P.ne_bot

theorem exists_sl2_with_valuation_bounds (d e : HeightOneSpectrum R →₀ ℤ) :
    ∃ p q r s : K, p ≠ 0 ∧ p * s - q * r = 1 ∧ ∀ P : HeightOneSpectrum R,
      P.valuation K p ≤ WithZero.exp (-d P) ∧ P.valuation K q ≤ WithZero.exp (-e P) ∧
      P.valuation K r ≤ WithZero.exp (-(-e P)) ∧ P.valuation K s ≤ WithZero.exp (-(-d P)) := by
  obtain ⟨C, hC, hCd⟩ := exists_frac (K := K) d
  obtain ⟨D, hD, hDe⟩ := exists_frac (K := K) e
  obtain ⟨p, hp0, hp⟩ := exists_ne_zero_mem_isInteger hC
  set p' := algebraMap R K p with hp'
  have hp'0 : p' ≠ 0 := by
    rw [hp']
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hp0
  have h1 : spanSingleton R⁰ p' * C⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hC]
    exact mul_le_mul_left (spanSingleton_le_iff_mem.mpr hp) _
  obtain ⟨q, hq⟩ := exists_add_spanSingleton_mul_eq h1
    (mul_ne_zero (spanSingleton_ne_zero_iff.mpr hp'0) (inv_ne_zero hC)) (inv_ne_zero hD)
  have hqD : q ∈ D := by
    have h2 : spanSingleton R⁰ q * D⁻¹ ≤ 1 := by
      rw [← hq]
      exact le_sup_right
    have h3 : spanSingleton R⁰ q * D⁻¹ * D ≤ 1 * D := mul_le_mul_left h2 _
    rw [inv_mul_cancel_right₀ hD, one_mul] at h3
    exact spanSingleton_le_iff_mem.mp h3
  have h4 : (1 : K) ∈ spanSingleton R⁰ p' * C⁻¹ + spanSingleton R⁰ q * D⁻¹ := by
    rw [hq]
    exact one_mem_one _
  obtain ⟨u, hu, w, hw, huw⟩ := (mem_add _ _ _).mp h4
  obtain ⟨s, hs, rfl⟩ := mem_singleton_mul.mp hu
  obtain ⟨r, hr, rfl⟩ := mem_singleton_mul.mp hw
  refine ⟨p', q, -r, s, hp'0, by rw [← huw]; ring, fun P => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [← hCd]; exact val_le_of_mem P hp
  · rw [← hDe]; exact val_le_of_mem P hqD
  · rw [← hDe, ← count_inv, Valuation.map_neg]; exact val_le_of_mem P hr
  · rw [← hCd, ← count_inv]; exact val_le_of_mem P hs

theorem val_comb (P : HeightOneSpectrum R) {u x u' x' : K} {m a m' a' c : ℤ}
    (hu : P.valuation K u ≤ WithZero.exp (-m)) (hx : P.valuation K x ≤ WithZero.exp (-a))
    (hu' : P.valuation K u' ≤ WithZero.exp (-m')) (hx' : P.valuation K x' ≤ WithZero.exp (-a'))
    (h : c = m + a) (h' : c = m' + a') : P.valuation K (u * x + u' * x') ≤ WithZero.exp (-c) := by
  refine Valuation.map_add_le _ ?_ ?_
  · rw [map_mul, h, neg_add, WithZero.exp_add]; exact mul_le_mul' hu hx
  · rw [map_mul, h', neg_add, WithZero.exp_add]; exact mul_le_mul' hu' hx'

variable {J : Type} [Fintype J] [DecidableEq J]

def Lat (𝔞 : J → HeightOneSpectrum R →₀ ℤ) (x : J → K) : Prop :=
  ∀ j P, P.valuation K (x j) ≤ WithZero.exp (-𝔞 j P)

def Rel (𝔞 𝔟 : J → HeightOneSpectrum R →₀ ℤ) (β : K) : Prop :=
  ∃ M : Matrix J J K, M.det = β ∧ ∀ x : J → K, Lat 𝔞 x ↔ Lat 𝔟 (M *ᵥ x)

theorem Rel.refl (𝔞 : J → HeightOneSpectrum R →₀ ℤ) : Rel 𝔞 𝔞 (1 : K) :=
  ⟨1, det_one, fun x => by rw [one_mulVec]⟩

theorem Rel.trans {𝔞 𝔟 𝔠 : J → HeightOneSpectrum R →₀ ℤ} {β γ : K} (h : Rel 𝔞 𝔟 β) (h' : Rel 𝔟 𝔠 γ) :
    Rel 𝔞 𝔠 (γ * β) := by
  obtain ⟨M, hM, h⟩ := h
  obtain ⟨N, hN, h'⟩ := h'
  exact ⟨N * M, by rw [det_mul, hM, hN], fun x => by rw [h, h', mulVec_mulVec]⟩

theorem exists_block {i j : J} (hij : i ≠ j) {p q r s : K} (hp : p ≠ 0) (h : p * s - q * r = 1) :
    ∃ M : Matrix J J K, M.det = 1 ∧ ∀ x : J → K, (M *ᵥ x) i = p * x i + q * x j ∧
      (M *ᵥ x) j = r * x i + s * x j ∧ ∀ k, k ≠ i → k ≠ j → (M *ᵥ x) k = x k := by
  refine ⟨transvection j i (r / p) * diagonal (Pi.mulSingle i p * Pi.mulSingle j p⁻¹) *
    transvection i j (q / p), ?_, fun x => ?_⟩
  · rw [det_mul, det_mul, det_transvection_of_ne _ _ hij, det_transvection_of_ne _ _ hij.symm, det_diagonal]
    simp [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', hp]
  · have hs : s = (1 + q * r) / p := by
      rw [← h]; field_simp; ring
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    refine ⟨?_, ?_, fun k hk hk' => ?_⟩
    · simp [-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hij, hij.symm]
      field_simp
    · simp [-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hij, hij.symm, hs]
      field_simp
      ring
    · simp [-mulVec_mulVec, transvection, add_mulVec, single_mulVec, mulVec_diagonal, hk, hk']

theorem rel_move {i j : J} (hij : i ≠ j) (𝔞 : J → HeightOneSpectrum R →₀ ℤ) (d : HeightOneSpectrum R →₀ ℤ) :
    Rel 𝔞 (𝔞 + Pi.single i d - Pi.single j d) (1 : K) := by
  obtain ⟨p, q, r, s, hp, h, hv⟩ := exists_sl2_with_valuation_bounds (K := K) d (𝔞 i + d - 𝔞 j)
  obtain ⟨M, hM, hx⟩ := exists_block hij hp h
  refine ⟨M, hM, fun x => ?_⟩
  obtain ⟨hi, hj, hk⟩ := hx x
  constructor
  · intro H k P
    obtain ⟨h1, h2, h3, h4⟩ := hv P
    by_cases hki : k = i
    · subst hki
      rw [hi]
      refine val_comb P h1 (H k P) h2 (H j P) ?_ ?_ <;> simp [hij] <;> ring
    by_cases hkj : k = j
    · subst hkj
      rw [hj]
      refine val_comb P h3 (H i P) h4 (H k P) ?_ ?_ <;> simp [hij.symm] <;> ring
    · rw [hk k hki hkj]
      simpa [hki, hkj] using H k P
  · intro H k P
    obtain ⟨h1, h2, h3, h4⟩ := hv P
    by_cases hki : k = i
    · subst hki
      have : x k = s * (M *ᵥ x) k + (-q) * (M *ᵥ x) j := by
        rw [hi, hj]; linear_combination (-x k) * h
      rw [this]
      rw [← Valuation.map_neg] at h2
      refine val_comb P h4 (H k P) h2 (H j P) ?_ ?_ <;> simp [hij, hij.symm] <;> ring
    by_cases hkj : k = j
    · subst hkj
      have : x k = (-r) * (M *ᵥ x) i + p * (M *ᵥ x) k := by
        rw [hi, hj]; linear_combination (-x k) * h
      rw [this]
      rw [← Valuation.map_neg] at h3
      refine val_comb P h3 (H i P) h1 (H k P) ?_ ?_ <;> simp [hij, hij.symm] <;> ring
    · have := H k P
      rw [hk k hki hkj] at this
      simpa [hki, hkj] using this

theorem rel_of_sum_eq (j₀ : J) (S : Finset J) : ∀ 𝔞 𝔟 : J → HeightOneSpectrum R →₀ ℤ,
    (∀ j, j ∉ S → j ≠ j₀ → 𝔞 j = 𝔟 j) → ∑ j, 𝔞 j = ∑ j, 𝔟 j → Rel 𝔞 𝔟 (1 : K) := by
  induction S using Finset.induction_on with
  | empty =>
    intro 𝔞 𝔟 h hs
    have : 𝔞 = 𝔟 := by
      funext j
      by_cases hj : j = j₀
      · subst hj
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ 𝔟 (Finset.mem_univ j),
          Finset.sum_congr rfl fun k hk => h k (by simp) (Finset.ne_of_mem_erase hk)] at hs
        exact add_right_cancel hs
      · exact h j (by simp) hj
    rw [this]
    exact Rel.refl 𝔟
  | insert i S hi ih =>
    intro 𝔞 𝔟 h hs
    by_cases hi₀ : i = j₀
    · exact ih 𝔞 𝔟 (fun j hj hj' => h j (by simp [hj, hi₀, hj']) hj') hs
    have h1 := rel_move (K := K) hi₀ 𝔞 (𝔟 i - 𝔞 i)
    have h2 := ih (𝔞 + Pi.single i (𝔟 i - 𝔞 i) - Pi.single j₀ (𝔟 i - 𝔞 i)) 𝔟 (fun j hj hj' => by
      by_cases hji : j = i
      · subst hji; simp [hj']
      · simpa [hji, hj'] using h j (by simp [hj, hji]) hj') (by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, hs])
    simpa using h1.trans h2

theorem rel_scale (j₀ : J) (𝔞 : J → HeightOneSpectrum R →₀ ℤ) (d : HeightOneSpectrum R →₀ ℤ) (β : K)
    (hβ : ∀ P : HeightOneSpectrum R, P.valuation K β = WithZero.exp (-d P)) :
    Rel 𝔞 (𝔞 + Pi.single j₀ d) β := by
  refine ⟨diagonal (Pi.mulSingle j₀ β), by simp [det_diagonal, Finset.prod_pi_mulSingle'], fun x => ?_⟩
  refine forall_congr' fun j => forall_congr' fun P => ?_
  by_cases hj : j = j₀
  · subst hj
    rw [mulVec_diagonal, Pi.mulSingle_eq_same, map_mul, hβ, Pi.add_apply, Pi.single_eq_same, Finsupp.add_apply,
      neg_add, WithZero.exp_add, mul_comm, mul_le_mul_iff_left₀ WithZero.exp_pos]
  · simp [mulVec_diagonal, hj]

open UpperTheory.V.ZK in
theorem SStein_of : UpperTheory.V.ZK.SStein := by
  intro F _ _ J _ 𝔞 𝔟 β hJ hβ
  classical
  have key : Rel (R := 𝓞 F) (K := F) 𝔞 𝔟 (β : F) := by
    rcases isEmpty_or_nonempty J with hE | ⟨⟨j₀⟩⟩
    · have h1 : β = 1 := hJ.resolve_left (not_nonempty_iff.mpr hE)
      rw [h1, Units.val_one, Subsingleton.elim 𝔞 𝔟]
      exact @Rel.refl _ _ _ _ _ _ _ _ _ (_) 𝔟
    · have h1 := rel_scale (K := F) j₀ 𝔞 (∑ j, (𝔟 j - 𝔞 j)) β fun P => by
        have h0 : P.valuation F (β : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr β.ne_zero
        have h2 : (∑ j, (𝔟 j - 𝔞 j)) P = ordP P β := by
          rw [hβ, Finsupp.finsetSum_apply]; rfl
        rw [h2, ordP, neg_neg, WithZero.exp_log h0]
      have h2 := rel_of_sum_eq (K := F) j₀ Finset.univ (𝔞 + Pi.single j₀ (∑ j, (𝔟 j - 𝔞 j))) 𝔟 (by simp)
        (by simp [Finset.sum_add_distrib, Finset.sum_sub_distrib])
      simpa using h1.trans h2
  obtain ⟨M, hM, h⟩ := key
  have hU : IsUnit M.det := hM ▸ β.isUnit
  refine ⟨Matrix.toLinearEquiv (Pi.basisFun F J) M hU, ?_, fun x => ?_⟩
  · ext
    rw [LinearEquiv.coe_det, ← hM, ← LinearMap.det_toLin (Pi.basisFun F J) M]
    congr 1
  · have : Matrix.toLinearEquiv (Pi.basisFun F J) M hU x = M *ᵥ x := by
      rw [Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
    rw [this]
    exact h x

end LateralTheory.Q.SSteinT
end
end

namespace LateralTheory.Fin.SStein
theorem stein_statement_holds : UpperTheory.V.ZK.SStein := by
  apply LateralTheory.Q.SSteinT.SStein_of
theorem intersectionNumber_baseChange : UpperTheory.V.ZK.SStein := stein_statement_holds
end LateralTheory.Fin.SStein
end
