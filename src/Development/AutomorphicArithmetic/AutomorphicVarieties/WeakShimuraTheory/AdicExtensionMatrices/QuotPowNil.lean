module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PdMapAdj

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SxLimPt
theorem UpperTheory.Reformulated.B.Qg4.sxLimPt :
    ∀ {Λ A R S : Type} [inst : CommRing Λ] [inst_1 : CommRing A] [inst_2 : Algebra Λ A]
    [inst_3 : CommRing R] [inst_4 : Algebra Λ R] (I : Ideal R) [IsAdicComplete I R] (e : S → A) (y : S → R),
    (∀ (N : ℕ),
        ∃ (f : A →ₐ[Λ] R ⧸ I ^ (N + (1 : ℕ))),
          ∀ (s : S),
            (f : A → R ⧸ I ^ (N + (1 : ℕ))) (e s) =
              (Ideal.Quotient.mk (I ^ (N + (1 : ℕ))) : R → R ⧸ I ^ (N + (1 : ℕ))) (y s)) →
      (∀ (N : ℕ) (f f' : A →ₐ[Λ] R ⧸ I ^ (N + (1 : ℕ))),
          (∀ (s : S), (f : A → R ⧸ I ^ (N + (1 : ℕ))) (e s) = (f' : A → R ⧸ I ^ (N + (1 : ℕ))) (e s)) → f = f') →
        ∃ (f : A →ₐ[Λ] R), ∀ (s : S), (f : A → R) (e s) = y s := by
  intro Λ A R S _ _ _ _ _ I _ e y hex huniq
  choose f hf using hex
  have hc : ∀ {m n : ℕ} (hle : m + 1 ≤ n + 1),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (f n) = f m := by
    intro m n hle
    refine huniq m _ _ fun s => ?_
    rw [AlgHom.comp_apply, hf, hf]
    rfl
  let g : (n : ℕ) → A →ₐ[Λ] R ⧸ I ^ n := fun n =>
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (f n)
  have hg : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (g n) = g m := by
    intro m n hle
    refine AlgHom.ext fun a => ?_
    simp only [g, ← hc (Nat.succ_le_succ hle), AlgHom.comp_apply]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (f n a)
    rw [← hr]
    rfl
  refine ⟨IsAdicComplete.liftAlgHom I g hg, fun s => ?_⟩
  have key : (fun s => IsAdicComplete.liftAlgHom I g hg (e s)) = y := by
    apply IsHausdorff.funext' I
    intro n t
    have h1 := IsAdicComplete.mk_liftAlgHom I g hg n (e t)
    refine h1.trans ?_
    simp only [g, AlgHom.comp_apply, hf]
    rfl
  exact congrFun key s
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NearOfAdjoin
theorem UpperTheory.Reformulated.B.Qg2.near_of_adjoin :
    ∀ {P L : Type} [inst : CommRing P] [inst_1 : CommRing L]
    [inst_2 : Algebra P L] (G : Set L),
    (∀ g ∈ G, IsNilpotent g) →
      ∀ x ∈ Algebra.adjoin P G, ∃ (p : P), IsNilpotent (x - (Algebra.algebraMap P L : P → L) p) := by
  intro P L _ _ _ G hG x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact ⟨0, by simpa using hG y hy⟩
  | algebraMap r => exact ⟨r, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    refine ⟨p + q, ?_⟩
    have h := (Commute.all _ _).isNilpotent_add hp hq
    convert h using 1
    rw [map_add (f := _)]
    ring
  | mul y z _ _ hy hz =>
    obtain ⟨p, hp⟩ := hy
    obtain ⟨q, hq⟩ := hz
    refine ⟨p * q, ?_⟩
    rw [← mem_nilradical] at hp hq ⊢
    have h := (nilradical L).add_mem ((nilradical L).mul_mem_right z hp)
      ((nilradical L).mul_mem_left ((Algebra.algebraMap P L : P → L) p) hq)
    convert h using 1
    rw [map_mul]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxExtA
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxExtA :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (f f' : W.A →ₐ[Λ] R'), (∀ s, f (W.zA s) = f' (W.zA s)) → f = f' := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hz R' _ _ _ f f' hf
  haveI := wPres_gr_zero_isCO_of_mem_maximalIdeal Λ X R W hz
  let ι : ↥(W.gr 0) →ₐ[Λ] W.A :=
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }
  have hzA : ∀ s, ((W.zA s : W.A) : R) = W.z s := fun _ => rfl
  have h0 : f.comp ι = f'.comp ι := by
    refine sxExtGr0 W hz R' _ _ ?_
    intro b n _ hb
    have hbA : (b : W.A) = n.prod fun s k => W.zA s ^ k := by
      apply Subtype.ext
      rw [hb]
      simp [Finsupp.prod, hzA]
    show f (b : W.A) = f' (b : W.A)
    rw [hbA]
    simp [Finsupp.prod, map_prod, map_pow, hf]
  refine AlgHom.ext_of_adjoin_eq_top (gr_gen Λ R X W) ?_
  rintro x (hx | ⟨s, rfl⟩)
  · exact congrArg (fun g => g ⟨x, hx⟩) h0
  · exact hf s
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxLimPt
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxLimPt :
    ∀ {Λ A R S : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] [CommRing R] [Algebra Λ R] (I : Ideal R) [IsAdicComplete I R] (e : S → A) (y : S → R), (∀ N : ℕ, ∃ f : A →ₐ[Λ] R ⧸ I ^ (N + 1), ∀ s, f (e s) = Ideal.Quotient.mk _ (y s)) → (∀ (N : ℕ) (f f' : A →ₐ[Λ] R ⧸ I ^ (N + 1)), (∀ s, f (e s) = f' (e s)) → f = f') → ∃ f : A →ₐ[Λ] R, ∀ s, f (e s) = y s :=
  _root_.UpperTheory.Reformulated.B.Qg4.sxLimPt
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.LaurPart
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem laurPart_prod {S R' ι : Type} [CommRing S] [CommRing R'] (e : S →+* LaurentSeries R')
    (w : ι → ℤ) (z : ι → S) (h : ∀ s, ∃ y, e (z s) = HahnSeries.single (w s) y) (d : ι → ℕ) (t : Finset ι) :
    ∃ y, e (∏ i ∈ t, z i ^ d i) = HahnSeries.single (∑ i ∈ t, d i • w i) y := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a t ha ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨u, hu⟩ := h a
    refine ⟨u ^ d a * y, ?_⟩
    rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, map_pow, hy, hu, HahnSeries.single_pow,
      HahnSeries.single_mul_single]

theorem UpperTheory.V.Ws.sxLaurPart :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ {R' : Type} [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {S : Type} [CommRing S] [Algebra Λ S] [IsCO Λ S] {c : ℕ} {e : S →+* LaurentSeries R'}, Laur (Λ := Λ) c e → ∀ (τ : X →+ ℤ) (F : R →ₐ[Λ] S), (∀ s, ∃ y, e (F (W.z s)) = HahnSeries.single (τ (W.wt s)) y) → ∀ j, ∀ x ∈ W.part j, ∃ y, e (F x) = HahnSeries.single (τ j) y := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hW R' _ _ _ S _ _ _ c e hL τ F hF j x hx
  classical
  obtain ⟨g, hg, rfl⟩ := hx
  have hm : ∀ s, (F.comp W.π) (MvPowerSeries.X s) ∈ maximalIdeal S := fun s => by
    show F (W.z s) ∈ maximalIdeal S
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hW s
  refine ⟨(e (F (W.π g))).coeff (τ j), ?_⟩
  ext n
  show (e (F (W.π g))).coeff n = _
  by_cases hn : n = τ j
  · subst hn
    rw [HahnSeries.coeff_single_same]
  rw [HahnSeries.coeff_single_of_ne hn]
  obtain ⟨M, hM⟩ := hL.small n
  have h1 := hM _ (GlobalTheory.algHom_sub_aeval_truncTotal_mem (F.comp W.π) hm M g)
  rw [map_sub, HahnSeries.coeff_sub, sub_eq_zero] at h1
  refine h1.trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, map_sum, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw : Finsupp.weight W.wt d = j := by
    by_contra hne
    apply MvPolynomial.mem_support_iff.1 hd
    rw [MvPowerSeries.coeff_truncTotal_eq_ite, hg d hne, ite_self]
  obtain ⟨y, hy⟩ := laurPart_prod e (fun s => τ (W.wt s)) (fun s => F (W.z s)) hF d d.support
  have hs : (∑ i ∈ d.support, d i • τ (W.wt i)) = τ j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hw, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp only [map_nsmul]
  rw [hs] at hy
  rw [map_mul, hL.alg]
  erw [hy]
  rw [HahnSeries.single_mul_single, zero_add, HahnSeries.coeff_single_of_ne hn]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearOfAdjoin
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem near_of_adjoin {P L : Type} [CommRing P] [CommRing L] [Algebra P L] (G : Set L)
    (hG : ∀ g ∈ G, IsNilpotent g) (x : L) (hx : x ∈ Algebra.adjoin P G) :
    ∃ p : P, IsNilpotent (x - algebraMap P L p) :=
  _root_.UpperTheory.Reformulated.B.Qg2.near_of_adjoin G hG x hx

private theorem unit_of_near {S : Type} [CommRing S] {x u : S} (h : IsNilpotent (x - u)) (hu : IsUnit u) :
    IsUnit x := by
  have := h.isUnit_add_right_of_commute hu (Commute.all _ _)
  simpa using this

private theorem local_of_near {P S : Type} [CommRing P] [IsLocalRing P] [CommRing S] [Nontrivial S] [Algebra P S]
    (h : ∀ x : S, ∃ p : P, IsNilpotent (x - algebraMap P S p)) : IsLocalRing S := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨p, hp⟩ := h x
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self p with hu | hu
  · exact Or.inl (unit_of_near hp (hu.map _))
  · refine Or.inr (unit_of_near (u := algebraMap P S (1 - p)) ?_ (hu.map _))
    have := hp.neg
    convert this using 1
    rw [map_sub, map_one]; ring

private theorem nil_mem_max {S : Type} [CommRing S] [IsLocalRing S] {x : S} (h : IsNilpotent x) :
    x ∈ maximalIdeal S := fun hu => by
  obtain ⟨n, hn⟩ := h
  exact not_isUnit_zero (hn ▸ hu.pow n)

private theorem bound_fin {R : Type} [CommRing R] (S : Subalgebra (PowerSeries R) (LaurentSeries R))
    [Module.Finite (PowerSeries R) S] :
    ∃ N : ℕ, ∀ y ∈ S, ∃ q : PowerSeries R,
      algebraMap (PowerSeries R) (LaurentSeries R) q = (PowerSeries.X : PowerSeries R) ^ N • y := by
  have hfg : S.toSubmodule.FG := Module.Finite.iff_fg.1 ‹_›
  obtain ⟨t, ht⟩ := hfg
  obtain ⟨⟨b, N, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (Submonoid.powers (PowerSeries.X : PowerSeries R)) t
  refine ⟨N, fun y hy => ?_⟩
  have hy' : y ∈ Submodule.span (PowerSeries R) (t : Set (LaurentSeries R)) := by
    rw [ht]; exact hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem g hg => exact hb g hg
  | zero => exact ⟨0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨p, hp⟩ := ha
    obtain ⟨q, hq⟩ := hb
    exact ⟨p + q, by rw [map_add (f := _), hp, hq, smul_add]⟩
  | smul r a _ ha =>
    obtain ⟨p, hp⟩ := ha
    exact ⟨r * p, by rw [map_mul, hp, ← Algebra.smul_def, smul_comm]⟩

private theorem alg_monomial {R : Type} [CommRing R] (n : ℕ) (x : R) :
    algebraMap (PowerSeries R) (LaurentSeries R) (PowerSeries.C x * PowerSeries.X ^ n)
      = HahnSeries.single (n : ℤ) x := by
  show HahnSeries.ofPowerSeries ℤ R _ = _
  rw [map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one]

theorem UpperTheory.V.Ws.sxLaur :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R], IsNilpotent (maximalIdeal R) → ∀ c : ℕ, ∃ (S : Type) (_ : CommRing S) (_ : Algebra Λ S) (_ : IsCO Λ S) (e : S →+* LaurentSeries R), Laur (Λ := Λ) c e := by
  intro Λ _ _ R _ _ hR hnil c
  haveI hP : IsCO Λ (PowerSeries R) := co_mvps Λ R Unit
  have hnilx : ∀ x ∈ maximalIdeal R, IsNilpotent x := fun x hx => by
    obtain ⟨k, hk⟩ := hnil
    refine ⟨k, ?_⟩
    have := Ideal.pow_mem_pow hx k
    rw [hk] at this
    simpa using this
  have hnils : ∀ (n : ℤ), ∀ x ∈ maximalIdeal R, IsNilpotent (HahnSeries.single n x : LaurentSeries R) :=
    fun n x hx => by
      obtain ⟨k, hk⟩ := hnilx x hx
      exact ⟨k, by rw [HahnSeries.single_pow, hk, map_zero]⟩
  obtain ⟨s, hs⟩ : (maximalIdeal R).FG := IsNoetherian.noetherian _
  let G : Set (LaurentSeries R) := (fun x => HahnSeries.single (-(c : ℤ)) x) '' (s : Set R)
  have hGfin : G.Finite := s.finite_toSet.image _
  have hG : ∀ g ∈ G, IsNilpotent g := by
    rintro _ ⟨x, hx, rfl⟩
    exact hnils _ x (hs ▸ Ideal.subset_span hx)
  let S := Algebra.adjoin (PowerSeries R) G
  haveI hfin : Module.Finite (PowerSeries R) S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hGfin fun g hg => by
      obtain ⟨k, hk⟩ := hG g hg
      exact ⟨X ^ k, monic_X_pow k, by simp [hk]⟩
  have hnear : ∀ x : S, ∃ p : PowerSeries R, IsNilpotent (x - algebraMap _ S p) := fun x => by
    obtain ⟨p, k, hk⟩ := near_of_adjoin G hG x.1 x.2
    exact ⟨p, k, Subtype.ext hk⟩
  haveI : IsLocalRing S := local_of_near hnear
  letI : Algebra Λ S := ((algebraMap (PowerSeries R) S).comp (algebraMap Λ (PowerSeries R))).toAlgebra
  haveI : IsScalarTower Λ (PowerSeries R) S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcomap : (maximalIdeal S).comap (algebraMap (PowerSeries R) S) = maximalIdeal (PowerSeries R) :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal S))
  have hin : ∀ p ∈ maximalIdeal (PowerSeries R), algebraMap _ S p ∈ maximalIdeal S := fun p hp => by
    rw [← hcomap] at hp; exact hp
  haveI hS : IsCO Λ S := co_finite Λ (PowerSeries R) S fun x => by
    obtain ⟨p, hp⟩ := hnear x
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := Λ) p
    refine ⟨a, ?_⟩
    have := (maximalIdeal S).add_mem (nil_mem_max hp) (hin _ ha)
    convert this using 1
    rw [map_sub, ← IsScalarTower.algebraMap_apply]; ring
  have hXmax : (PowerSeries.X : PowerSeries R) ∈ maximalIdeal (PowerSeries R) := fun hu => by
    have := PowerSeries.isUnit_constantCoeff _ hu
    simp at this
  refine ⟨S, inferInstance, inferInstance, hS, S.val.toRingHom, Subtype.val_injective, fun x => ?_, ?_, ?_⟩
  · have := alg_monomial 0 (algebraMap Λ R x)
    rw [pow_zero, mul_one, ← PowerSeries.algebraMap_apply] at this
    exact this
  · rintro n x (hn | ⟨hn, hx⟩)
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn.le
      refine ⟨algebraMap _ S (PowerSeries.C x * PowerSeries.X ^ k), hin _ ?_, alg_monomial k x⟩
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hXmax k (by exact_mod_cast hn))
    · have h1 : ∀ x ∈ Ideal.span (s : Set R), (HahnSeries.single (-(c : ℤ)) x : LaurentSeries R) ∈ S := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem g hg => exact Algebra.subset_adjoin ⟨g, hg, rfl⟩
        | zero => rw [map_zero]; exact S.zero_mem
        | add a b _ _ ha hb => rw [HahnSeries.single_add]; exact S.add_mem ha hb
        | smul r a _ ha =>
          have := S.mul_mem (S.algebraMap_mem (PowerSeries.C r * PowerSeries.X ^ 0)) ha
          rw [alg_monomial, HahnSeries.single_mul_single] at this
          simpa using this
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (a := n + c) (by omega)
      have h2 := S.mul_mem (S.algebraMap_mem (PowerSeries.C 1 * PowerSeries.X ^ k)) (h1 x (hs ▸ hx))
      rw [alg_monomial, HahnSeries.single_mul_single, one_mul, ← hk, add_neg_cancel_right] at h2
      obtain ⟨j, hj⟩ := hnils n x hx
      exact ⟨⟨_, h2⟩, nil_mem_max ⟨j, Subtype.ext hj⟩, rfl⟩
  · intro n
    obtain ⟨N, hN⟩ := bound_fin S
    have hrad : maximalIdeal S ≤ (Ideal.span {algebraMap (PowerSeries R) S PowerSeries.X}).radical := by
      intro y hy
      obtain ⟨p, hp⟩ := hnear y
      have hp0 : PowerSeries.constantCoeff p ∈ maximalIdeal R := fun hu =>
        hy (unit_of_near hp ((PowerSeries.isUnit_iff_constantCoeff.2 hu).map _))
      obtain ⟨q, hq⟩ : (PowerSeries.X : PowerSeries R) ∣ p - PowerSeries.C (PowerSeries.constantCoeff p) :=
        PowerSeries.X_dvd_iff.2 (by simp)
      have e1 : y = (y - algebraMap _ S p) + algebraMap _ S (PowerSeries.C (PowerSeries.constantCoeff p))
          + algebraMap (PowerSeries R) S PowerSeries.X * algebraMap _ S q := by
        rw [← map_mul, ← hq, map_sub]; ring
      have hz : ∀ z : S, IsNilpotent z →
          z ∈ (Ideal.span {algebraMap (PowerSeries R) S PowerSeries.X}).radical := fun z ⟨k, hk⟩ =>
        ⟨k, hk ▸ Ideal.zero_mem _⟩
      rw [e1]
      refine Ideal.add_mem _ (Ideal.add_mem _ (hz _ hp) (hz _ (((hnilx _ hp0).map _).map _))) ?_
      exact Ideal.le_radical (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
    refine ⟨e * (n.natAbs + 1 + N), fun y hy => ?_⟩
    rw [pow_mul] at hy
    have hy2 := Ideal.pow_right_mono he _ hy
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy2
    obtain ⟨z, rfl⟩ := hy2
    obtain ⟨q, hq⟩ := hN z.1 z.2
    have e2 : S.val.toRingHom (algebraMap (PowerSeries R) S PowerSeries.X ^ (n.natAbs + 1 + N) * z)
        = algebraMap (PowerSeries R) (LaurentSeries R) (PowerSeries.X ^ (n.natAbs + 1) * q) := by
      rw [map_mul (algebraMap (PowerSeries R) (LaurentSeries R)), hq, Algebra.smul_def, ← mul_assoc, ← map_mul,
        ← pow_add, ← map_pow]
      rfl
    rw [e2]
    show ((PowerSeries.X ^ (n.natAbs + 1) * q : PowerSeries R) : LaurentSeries R).coeff n = 0
    rw [PowerSeries.coeff_coe, PowerSeries.coeff_X_pow_mul']
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.LaurDesc
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxLaurDesc :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {X : Type} [AddCommGroup X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] (W : WPres Λ X R) {R' : Type} [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {S : Type} [CommRing S] [Algebra Λ S] [IsCO Λ S] {c : ℕ} {e : S →+* LaurentSeries R'}, Laur (Λ := Λ) c e → ∀ (τ : X →+ ℤ) (F : R →ₐ[Λ] S), (∀ j, ∀ x ∈ W.part j, ∃ y, e (F x) = HahnSeries.single (τ j) y) → ∃ f : W.A →ₐ[Λ] R', ∀ j, ∀ x ∈ W.gr j, e (F x) = HahnSeries.single (τ j) (f x) := by
  intro Λ _ _ X _ _ R _ _ W R' _ _ _ S _ _ _ c e hL τ F hF
  let φ : ∀ j, W.gr j →ₗ[Λ] R' := fun j =>
    { toFun := fun x => (e (F ((x : W.A) : R))).coeff (τ j)
      map_add' := fun x y => by
        simp only [Submodule.coe_add, Subalgebra.coe_add, map_add (f := _), HahnSeries.coeff_add]
      map_smul' := fun a x => by
        have h1 : (((a • x : W.gr j) : W.A) : R) = algebraMap Λ R a * ((x : W.A) : R) := by
          rw [← Algebra.smul_def]; rfl
        rw [h1, map_mul, AlgHom.commutes, map_mul, hL.alg, HahnSeries.coeff_single_zero_mul,
          RingHom.id_apply, Algebra.smul_def] }
  have key : ∀ j (x : W.gr j), e (F ((x : W.A) : R)) = HahnSeries.single (τ j) (φ j x) := by
    intro j x
    obtain ⟨y, hy⟩ := hF j ((x : W.A) : R) x.2
    have h2 : φ j x = y := by
      show (e (F ((x : W.A) : R))).coeff (τ j) = y
      rw [hy, HahnSeries.coeff_single_same]
    rw [h2, hy]
  have hone : φ 0 (GradedMonoid.GOne.one (A := fun j => W.gr j)) = 1 := by
    show (e (F 1)).coeff (τ 0) = 1
    rw [map_one, map_one, map_zero, HahnSeries.coeff_one, if_pos rfl]
  have hmul : ∀ {i j} (a : W.gr i) (b : W.gr j), φ _ (GradedMonoid.GMul.mul (A := fun j => W.gr j) a b) = φ i a * φ j b := by
    intro i j a b
    show (e (F (((a : W.A) : R) * ((b : W.A) : R)))).coeff (τ (i + j)) = _
    rw [map_mul, map_mul, key, key, HahnSeries.single_mul_single, map_add (f := _), HahnSeries.coeff_single_same]
  refine ⟨(DirectSum.toAlgebra Λ (fun j => W.gr j) φ hone hmul).comp
    (DirectSum.decomposeAlgEquiv W.gr).toAlgHom, fun j x hx => ?_⟩
  have h : DirectSum.decompose W.gr x = DirectSum.of (fun j => W.gr j) j ⟨x, hx⟩ :=
    DirectSum.decompose_of_mem W.gr hx
  have h3 : ((DirectSum.toAlgebra Λ (fun j => W.gr j) φ hone hmul).comp
      (DirectSum.decomposeAlgEquiv W.gr).toAlgHom) x = φ j ⟨x, hx⟩ := by
    show DirectSum.toAlgebra Λ (fun j => W.gr j) φ hone hmul (DirectSum.decompose W.gr x) = _
    rw [h]
    exact DirectSum.toSemiring_of (fun j => (φ j).toAddMonoidHom) hone hmul j _
  rw [h3]
  exact key j ⟨x, hx⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ScaleRD
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem wt_add' (i j k : Fin 4) : wt i j + wt j k = wt i k := by
  simp [wt]

private theorem laurent_mul_apply_eq_single_of_entries_single {R S : Type} [CommRing R] [CommRing S] (e : S →+* LaurentSeries R)
    (τ : ℤ × ℤ →+ ℤ) (X Y : M4 S) (X0 Y0 : M4 R)
    (hX : ∀ i j, e (X i j) = HahnSeries.single (τ (wt i j)) (X0 i j))
    (hY : ∀ i j, e (Y i j) = HahnSeries.single (τ (wt i j)) (Y0 i j)) (i j : Fin 4) :
    e ((X * Y) i j) = HahnSeries.single (τ (wt i j)) ((X0 * Y0) i j) := by
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [map_add e, map_mul, hX, hY, HahnSeries.single_mul_single, ← map_add τ, wt_add',
    HahnSeries.single_add]

private theorem laurent_adj_apply_eq_single_of_entries_single {R S : Type} [CommRing R] [CommRing S] (e : S →+* LaurentSeries R)
    (τ : ℤ × ℤ →+ ℤ) (X : M4 S) (X0 : M4 R)
    (hX : ∀ i j, e (X i j) = HahnSeries.single (τ (wt i j)) (X0 i j)) (i j : Fin 4) :
    e ((adj X) i j) = HahnSeries.single (τ (wt i j)) ((adj X0) i j) := by
  have hrev : ∀ i j : Fin 4, wt j.rev i.rev = wt i j := by decide
  simp only [adj, Matrix.of_apply, zsmul_eq_mul, map_mul, map_intCast, hX, hrev]
  rw [← map_intCast (HahnSeries.C : R →+* LaurentSeries R), HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add]

private theorem laurent_smul_one_apply_eq_single_of_eq_single {R S : Type} [CommRing R] [CommRing S] (e : S →+* LaurentSeries R)
    (τ : ℤ × ℤ →+ ℤ) (ν : S) (ν0 : R) (hν : e ν = HahnSeries.single 0 ν0) (i j : Fin 4) :
    e ((ν • (1 : M4 S)) i j) = HahnSeries.single (τ (wt i j)) ((ν0 • (1 : M4 R)) i j) := by
  have hw0 : ∀ i : Fin 4, wt i i = 0 := by decide
  by_cases h : i = j
  · subst h
    simp [Matrix.smul_apply, hν, hw0]
  · simp [Matrix.smul_apply, Matrix.one_apply_ne h]

theorem UpperTheory.V.Ws.sxScaleRD :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {S : Type} [CommRing S] [Algebra Λ S] [IsCO Λ S] {c : ℕ} {e : S →+* LaurentSeries R} {τ : ℤ × ℤ →+ ℤ} {D : RD Φ R}, IsNilpotent (maximalIdeal R) → Laur (Λ := Λ) c e → (∀ i j, -(c : ℤ) ≤ τ (wt i j)) → Φ.Near a τ D → ∃ D' : RD Φ S, Φ.Near a 0 D' ∧ (∀ g i j, e (D'.r g i j) = HahnSeries.single (τ (wt i j)) (D.r g i j)) ∧ ∀ v i s, e (D'.ψ v i s) = HahnSeries.single 0 (D.ψ v i s) := by
  intro O Γ _ _ _ Φ Λ _ _ a R _ _ _ S _ _ _ c e τ D hnil hL hc hN
  classical
  have hw0 : ∀ i : Fin 4, wt i i = 0 := by decide
  have hresm : ∀ {T : Type} [CommRing T] [Algebra Λ T] [IsCO Λ T] (y : T), y ∈ maximalIdeal T →
      res Λ T y = 0 := by
    intro T _ _ _ y hy
    simp [res, (IsLocalRing.residue_eq_zero_iff y).mpr hy]
  have hex0 : ∀ x : R, ∃ y : S, e y = HahnSeries.single 0 x ∧ res Λ S y = res Λ R x := by
    intro x
    obtain ⟨l, hl⟩ := IsCO.res_surj (O := Λ) x
    obtain ⟨y, hy, hye⟩ := hL.mem 0 _ (Or.inr ⟨by omega, hl⟩)
    refine ⟨y + algebraMap Λ S l, ?_, ?_⟩
    · rw [map_add (f := _), hye, hL.alg, ← HahnSeries.single_add, sub_add_cancel]
    · rw [map_add (f := _), hresm y hy, AlgHom.commutes, zero_add]
      conv_rhs => rw [← sub_add_cancel x (algebraMap Λ R l)]
      rw [map_add (f := _), hresm _ hl, AlgHom.commutes, zero_add]
  have hent : ∀ g i j, ∃ y, e y = HahnSeries.single (τ (wt i j)) (D.r g i j) := by
    intro g i j
    rcases lt_trichotomy (τ (wt i j)) 0 with h | h | h
    · have hij : i ≠ j := by
        rintro rfl
        rw [hw0, map_zero] at h
        exact lt_irrefl _ h
      obtain ⟨y, -, hy⟩ := hL.mem _ _ (Or.inr ⟨hc i j, hN.off g i j hij h.le⟩)
      exact ⟨y, hy⟩
    · rw [h]
      obtain ⟨y, hy, -⟩ := hex0 (D.r g i j)
      exact ⟨y, hy⟩
    · obtain ⟨y, -, hy⟩ := hL.mem _ _ (Or.inl h)
      exact ⟨y, hy⟩
  have hmem : ∀ g i j, i ≠ j → ∀ y, e y = HahnSeries.single (τ (wt i j)) (D.r g i j) →
      y ∈ maximalIdeal S := by
    intro g i j hij y hy
    rcases le_or_gt (τ (wt i j)) 0 with h | h
    · obtain ⟨y', hy', he'⟩ := hL.mem _ _ (Or.inr ⟨hc i j, hN.off g i j hij h⟩)
      rw [hL.inj (hy.trans he'.symm)]
      exact hy'
    · obtain ⟨y', hy', he'⟩ := hL.mem _ _ (Or.inl h)
      rw [hL.inj (hy.trans he'.symm)]
      exact hy'
  let pre : LaurentSeries R → S := fun z => if h : ∃ y, e y = z then h.choose else 0
  have hpre : ∀ z, (∃ y, e y = z) → e (pre z) = z := by
    intro z h
    simp only [pre, dif_pos h]
    exact h.choose_spec
  have hpre0 : ∀ x : R, e (pre (HahnSeries.single 0 x)) = HahnSeries.single 0 x := by
    intro x
    obtain ⟨y, hy, -⟩ := hex0 x
    exact hpre _ ⟨y, hy⟩
  have hres0 : ∀ x : R, res Λ S (pre (HahnSeries.single 0 x)) = res Λ R x := by
    intro x
    obtain ⟨y, hy, hr⟩ := hex0 x
    rw [hL.inj ((hpre0 x).trans hy.symm)]
    exact hr
  let rr : Γ → M4 S := fun g => Matrix.of fun i j => pre (HahnSeries.single (τ (wt i j)) (D.r g i j))
  have hrr : ∀ g i j, e (rr g i j) = HahnSeries.single (τ (wt i j)) (D.r g i j) :=
    fun g i j => hpre _ (hent g i j)
  have hext : ∀ X Y : M4 S, (∀ i j, e (X i j) = e (Y i j)) → X = Y :=
    fun X Y h => Matrix.ext fun i j => hL.inj (h i j)
  have h1 : ∀ i j, e ((1 : M4 S) i j) = HahnSeries.single (τ (wt i j)) ((1 : M4 R) i j) := by
    intro i j
    have := laurent_smul_one_apply_eq_single_of_eq_single e τ 1 1 (by rw [map_one, HahnSeries.single_zero_one]) i j
    simpa only [one_smul] using this
  let r' : Γ →* M4 S :=
    { toFun := rr
      map_one' := hext _ _ fun i j => by rw [hrr, D.r.map_one, h1]
      map_mul' := fun g h => hext _ _ fun i j => by
        rw [hrr, D.r.map_mul, laurent_mul_apply_eq_single_of_entries_single e τ _ _ _ _ (hrr g) (hrr h)] }
  have hr' : ∀ g i j, e (r' g i j) = HahnSeries.single (τ (wt i j)) (D.r g i j) := hrr
  let ψ' : (v : Φ.ι) → Fin 4 → ↥(Φ.Gv v) →* S := fun v i =>
    { toFun := fun s => pre (HahnSeries.single 0 (D.ψ v i s))
      map_one' := hL.inj (by rw [hpre0, (D.ψ v i).map_one, HahnSeries.single_zero_one, map_one])
      map_mul' := fun s t => hL.inj (by
        rw [hpre0, (D.ψ v i).map_mul, map_mul e, hpre0, hpre0, HahnSeries.single_mul_single, zero_add]) }
  obtain ⟨K, hK⟩ := hnil
  have hinj : Function.Injective (Ideal.Quotient.mk (maximalIdeal R ^ K)) := by
    intro x y h
    rwa [Ideal.Quotient.eq, hK, Ideal.zero_eq_bot, Ideal.mem_bot, sub_eq_zero] at h
  refine ⟨⟨r', ψ'⟩, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, hr', fun v i s => hpre0 _⟩
  · intro g
    have hg : adj (D.r g) * D.r g = _ := hN.rep.mult g
    show adj (r' g) * r' g = _
    simp only [RingHom.comp_apply] at hg ⊢
    refine hext _ _ fun i j => ?_
    rw [laurent_mul_apply_eq_single_of_entries_single e τ _ _ _ _ (laurent_adj_apply_eq_single_of_entries_single e τ _ _ (hr' g)) (hr' g), hg,
      laurent_smul_one_apply_eq_single_of_eq_single e τ _ _ (hL.alg _)]
  · intro g hg
    refine hext _ _ fun i j => ?_
    rw [hr', hN.rep.kill g hg, h1]
  · intro i j hij
    apply hL.inj
    rw [hr', hN.rep.nrm hij, HahnSeries.single_eq_zero, map_zero]
  · intro i j N
    have h2 : IsLocallyConstant fun g => D.r g i j :=
      IsLocallyConstant.desc _ _ (hN.cont i j K) hinj
    exact h2.comp (fun x => Ideal.Quotient.mk (maximalIdeal S ^ N) (pre (HahnSeries.single (τ (wt i j)) x)))
  · intro v i N
    have h2 : IsLocallyConstant fun s => D.ψ v i s :=
      IsLocallyConstant.desc _ _ (hN.contψ v i K) hinj
    exact h2.comp (fun x => Ideal.Quotient.mk (maximalIdeal S ^ N) (pre (HahnSeries.single 0 x)))
  · intro g i
    rw [← hN.diag g i]
    show res Λ S (pre (HahnSeries.single (τ (wt i i)) (D.r g i i))) = _
    rw [hw0, map_zero]
    exact hres0 _
  · intro g i j hij _
    exact hmem g i j hij _ (hr' g i j)
  · intro v i s
    rw [← hN.redψ v i s]
    exact hres0 _
end

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] {x y : R}
    (h : ∀ N : ℕ, x - y ∈ maximalIdeal R ^ (N + 1)) : x = y := by
  rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  cases n with
  | zero => simp
  | succ N => exact h N

private theorem nontrivial_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ) :
    Nontrivial (R ⧸ maximalIdeal R ^ (N + 1)) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  apply (maximalIdeal.isMaximal R).ne_top
  exact top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero N))

private theorem isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ)
    [IsLocalRing (R ⧸ maximalIdeal R ^ (N + 1))] :
    IsNilpotent (maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1))) := by
  refine ⟨N + 1, ?_⟩
  have hle : maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1)) ≤
      (maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1))) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (hu.map _)
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  calc _ ≤ ((maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1)))) ^ (N + 1) :=
        Ideal.pow_right_mono hle _
    _ = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem UpperTheory.V.Ws.sxNearA :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, Φ.RUniv a D → RD.Graded D W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (τ : ℤ × ℤ →+ ℤ) (Q : RD Φ R'), Φ.Near a τ Q → ∃ f : W.A →ₐ[Λ] R', D'.map (f : W.A →+* R') = Q := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W hU hG D' hD' R' _ _ _ τ Q hQ
  classical
  have liftNilpotent : ∀ (T : Type) [CommRing T] [Algebra Λ T] [IsCO Λ T] (P : RD Φ T),
      IsNilpotent (maximalIdeal T) → Φ.Near a τ P → ∃ f : W.A →ₐ[Λ] T, D'.map (f : W.A →+* T) = P := by
    intro T _ _ _ P hnil hP
    let c := ∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs
    have hc : ∀ i j, -(c : ℤ) ≤ τ (wt i j) := by
      intro i j
      have h : (τ (wt i j)).natAbs ≤ c :=
        Finset.single_le_sum (f := fun p : Fin 4 × Fin 4 => (τ (wt p.1 p.2)).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))
      omega
    obtain ⟨S, _, _, _, e, he⟩ := sxLaur (Λ := Λ) hnil c
    obtain ⟨P', hP', hr, hψ⟩ := sxScaleRD hnil he hc hP
    obtain ⟨F, hF, -⟩ := hU.2 S P' hP'
    have hFr : ∀ g i j, e (F (D.r g i j)) = HahnSeries.single (τ (wt i j)) (P.r g i j) := by
      intro g i j
      rw [← hr, ← hF]
      rfl
    have hFψ : ∀ v i s, e (F (D.ψ v i s)) = HahnSeries.single 0 (P.ψ v i s) := by
      intro v i s
      rw [← hψ, ← hF]
      rfl
    have hz : ∀ s, ∃ y, e (F (W.z s)) = HahnSeries.single (τ (W.wt s)) y := by
      intro s
      rcases hG.var s with ⟨g, i, j, x, h1, h2, h3⟩ | ⟨v, i, t, x, h1, h2⟩
      · rw [h1, h2, map_sub, map_sub, hFr, AlgHom.commutes, he.alg]
        by_cases hij : i = j
        · rw [(wt_eq_zero i j).2 hij, map_zero]
          exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
        · rw [h3 hij]
          exact ⟨P.r g i j, by simp⟩
      · rw [h1, h2, map_sub, map_sub, hFψ, AlgHom.commutes, he.alg, map_zero]
        exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
    obtain ⟨f, hf⟩ := sxLaurDesc W he τ F (sxLaurPart W hG.max he τ F hz)
    have er : ∀ g i j, ((D'.r g i j : W.A) : R) = D.r g i j := by
      intro g i j
      rw [← hD']
      rfl
    have eψ : ∀ v i s, ((D'.ψ v i s : W.A) : R) = D.ψ v i s := by
      intro v i s
      rw [← hD']
      rfl
    refine ⟨f, RD.ext ?_ ?_⟩
    · ext g i j
      have hm : D'.r g i j ∈ W.gr (wt i j) := by
        show ((D'.r g i j : W.A) : R) ∈ W.part (wt i j)
        rw [er]
        exact hG.ent g i j
      have h := hf _ _ hm
      rw [er, hFr] at h
      exact (HahnSeries.single_injective _ h).symm
    · funext v i
      ext s
      have hm : D'.ψ v i s ∈ W.gr 0 := by
        show ((D'.ψ v i s : W.A) : R) ∈ W.part 0
        rw [eψ]
        exact hG.chr v i s
      have h := hf _ _ hm
      rw [eψ, hFψ, map_zero] at h
      exact (HahnSeries.single_injective _ h).symm
  have hlev : ∀ N : ℕ, ∃ f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1),
      D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) := by
    intro N
    haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
    haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
      co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
    exact liftNilpotent _ _ (isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ N)
      (sxNearMap (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))) hQ)
  have hval : ∀ s : W.σ, ∃ y : R', ∀ (N : ℕ) (f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
      D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) →
      f (W.zA s) = Ideal.Quotient.mk _ y := by
    intro s
    rcases hG.var s with ⟨g, i, j, c, hz, -, -⟩ | ⟨v, i, t, c, hz, -⟩
    · refine ⟨Q.r g i j - algebraMap Λ R' c, fun N f hf => ?_⟩
      have e1 : D.r g i j = ((D'.r g i j : W.A) : R) := by rw [← hD']; rfl
      have hA : W.zA s = D'.r g i j - algebraMap Λ W.A c := by
        apply Subtype.ext
        change W.z s = _
        rw [hz, e1]
        rfl
      have e2 : f (D'.r g i j) = Ideal.Quotient.mk _ (Q.r g i j) :=
        congrArg (fun E => E.r g i j) hf
      rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
    · refine ⟨Q.ψ v i t - algebraMap Λ R' c, fun N f hf => ?_⟩
      have e1 : D.ψ v i t = ((D'.ψ v i t : W.A) : R) := by rw [← hD']; rfl
      have hA : W.zA s = D'.ψ v i t - algebraMap Λ W.A c := by
        apply Subtype.ext
        change W.z s = _
        rw [hz, e1]
        rfl
      have e2 : f (D'.ψ v i t) = Ideal.Quotient.mk _ (Q.ψ v i t) :=
        congrArg (fun E => E.ψ v i t) hf
      rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
  choose y hy using hval
  choose fN hfN using hlev
  have huniq : ∀ (N : ℕ) (f f' : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
      (∀ s, f (W.zA s) = f' (W.zA s)) → f = f' := by
    intro N f f' h
    haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
    haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
      co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
    exact sxExtA W hG.max _ f f' h
  haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := Λ)
  obtain ⟨F, hF⟩ := sxLimPt (Λ := Λ) (maximalIdeal R') W.zA y
    (fun N => ⟨fN N, fun s => hy s N (fN N) (hfN N)⟩) huniq
  have hcomp : ∀ N, (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))).comp F = fN N := by
    intro N
    apply huniq
    intro s
    rw [AlgHom.comp_apply, hF s, hy s N (fN N) (hfN N)]
    rfl
  have hpt : ∀ (x : W.A) (q : R'), (∀ N, fN N x = Ideal.Quotient.mk _ q) → F x = q := by
    intro x q hx
    apply eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete
    intro N
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← hx N, ← hcomp N]
    rfl
  refine ⟨F, ?_⟩
  apply RD.ext
  · ext g i j
    exact hpt _ _ (fun N => congrArg (fun E => E.r g i j) (hfN N))
  · funext v i
    ext t
    exact hpt _ _ (fun N => congrArg (fun E => E.ψ v i t) (hfN N))
