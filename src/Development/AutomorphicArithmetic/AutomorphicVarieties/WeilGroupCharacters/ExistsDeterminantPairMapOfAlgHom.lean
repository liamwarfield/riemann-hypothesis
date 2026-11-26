module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairMapOfAlgHom
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

section SlopeTestRemainingChoices

open Polynomial

variable {n : ℕ} {A A' A'' G : Type} [CommRing A] [CommRing A'] [CommRing A''] [Group G]

private theorem pm_map_map (D : GDet n A G) (f : A →+* A') (g : A' →+* A'') :
    (D.map f).map g = D.map (g.comp f) := rfl

private theorem pm_chi_map (D : GDet n A G) (f : A →+* A') (y : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
  letI : Algebra A A'[X] := ((algebraMap A' A'[X]).comp f).toAlgebra
  have h := D.nat A[X] A'[X]
    { (Polynomial.mapRingHom f : A[X] →+* A'[X]) with
      commutes' := fun a => by
        show Polynomial.map f (C a) = C (f a)
        simp }
    (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
  refine Eq.trans ?_ h
  show D.D A'[X] _ = D.D A'[X] (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · clear h
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp

private theorem pm_lam_map (D : GDet n A G) (f : A →+* A') (i : ℕ) (y : MonoidAlgebra A G) :
    (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y) := by
  simp [GDet.lam, pm_chi_map]

private theorem pm_lam_single (D : GDet n A G) (f : A →+* A') (i : ℕ) (g : G) :
    (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  rw [← pm_lam_map]; simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.W.exists_determinantPair_map_of_algHom :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid F O n) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (p : Pair r R), ∃ p' : Pair r R', p.Maps (f : R →+* R') p'.D p'.ψ := by
  intro l _ F O _ _ _ n r R _ _ _ R' _ _ _ f p
  have hle : ∀ N, maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := fun N => by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  have heps : ∀ g, Units.map ((f : R →+* R') : R →* R') (F.eps O R g) = F.eps O R' g := fun g =>
    Units.ext (f.commutes _)
  refine ⟨
    { D := p.D.map (f : R →+* R')
      ψ := fun v i => pushCh (f : R →+* R') (p.ψ v i)
      cont := fun i N => ?_
      red := ?_
      psi := fun v i =>
        { cont := fun N => ((p.psi v i).cont N).comp (Ideal.quotientMap _ (f : R →+* R') (hle N))
          red := fun g => (res_map f _).trans ((p.psi v i).red g)
          mu := fun g => (congrArg f ((p.psi v i).mu g)).trans (f.commutes _) }
      P := fun i g => ?_
      Ord := fun v g h => ?_
      I := fun u g hg h => ?_ }, rfl, fun _ _ => rfl⟩
  · simp only [pm_lam_single]
    exact (p.cont i N).comp (Ideal.quotientMap _ (f : R →+* R') (hle N))
  · rw [pm_map_map, ← p.red]
    congr 1
    exact RingHom.ext (res_map f)
  · have h1 : F.star O R' n (MonoidAlgebra.single g 1) =
        MonoidAlgebra.mapRingHom _ (f : R →+* R') (F.star O R n (MonoidAlgebra.single g 1)) := by
      simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, one_smul, MonoidHom.coe_mk, OneHom.coe_mk,
        MulOpposite.unop_op, MonoidAlgebra.mapRingHom_single]
      rw [← heps, ← map_zpow]
      rfl
    rw [h1, pm_lam_map, p.P, pm_lam_single]
  · have h1 : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh (f : R →+* R') (p.ψ v i)) g =
        MonoidAlgebra.mapRingHom _ (f : R →+* R') (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) g) := by
      simp only [GFrame.oEl, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub,
        MonoidAlgebra.mapRingHom_single, map_one]
      rfl
    rw [h1, GDet.tr, pm_lam_map]
    exact (congrArg (f : R →+* R') (p.Ord v g h)).trans (map_zero _)
  · have h1 : MonoidAlgebra.single h (1 : R') * (MonoidAlgebra.single g 1 - 1) =
        MonoidAlgebra.mapRingHom _ (f : R →+* R') (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) := by
      simp only [map_mul, map_sub, MonoidAlgebra.mapRingHom_single, map_one]
    rw [h1, GDet.tr, pm_lam_map]
    exact (congrArg (f : R →+* R') (p.I u g hg h)).trans (map_zero _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsAlgebraicPointOfGroupDeterminant
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AlgebraicPointIntegral
open Polynomial

private theorem UpperTheory.Reformulated.B.AlgebraicPointIntegral.factor {O : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (p : O[X])
    (hp : ∃ i, p.coeff i ∉ IsLocalRing.maximalIdeal O) :
    ∃ g q : O[X], g.Monic ∧ IsUnit (q.coeff 0) ∧ p = g * q := by
  have h0 : (p : PowerSeries O).map (IsLocalRing.residue O) ≠ 0 := by
    obtain ⟨i, hi⟩ := hp
    intro h
    apply hi
    have := congrArg (PowerSeries.coeff i) h
    rwa [PowerSeries.coeff_map, Polynomial.coeff_coe, map_zero,
      IsLocalRing.residue_eq_zero_iff] at this
  obtain ⟨g, h, hg, hh, e⟩ := PowerSeries.exists_isWeierstrassFactorization h0
  have hI : IsLocalRing.maximalIdeal O ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal O).ne_top
  have hd := hg.isWeierstrassDivisorAt hI
  have hn : (((g : PowerSeries O).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O))).order.toNat) = g.natDegree := by
    rw [← hg.coe_natDegree_eq_order_map (g : PowerSeries O) 1
      (by rwa [PowerSeries.constantCoeff_one, ← Ideal.ne_top_iff_one]) (by simp)]
    simp
  have hdeg : g.degree = g.natDegree := Polynomial.degree_eq_natDegree hg.monic.ne_zero
  have e2 := Polynomial.modByMonic_add_div p g
  have key := hd.eq_of_mul_add_eq_mul_add (q := h) (q' := ((p /ₘ g : O[X]) : PowerSeries O))
    (r := 0) (r' := p %ₘ g)
    (by rw [hn, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _)
    (by rw [hn, ← hdeg]; exact Polynomial.degree_modByMonic_lt p hg.monic)
    (by
      rw [← e, Polynomial.coe_zero, add_zero, ← Polynomial.coe_mul, ← Polynomial.coe_add,
        add_comm, e2])
  refine ⟨g, p /ₘ g, hg.monic, ?_, ?_⟩
  · have := PowerSeries.isUnit_iff_constantCoeff.1 hh
    rw [key.1] at this
    simpa using this
  · rw [← key.2, zero_add] at e2
    exact e2.symm

theorem UpperTheory.Reformulated.B.AlgebraicPointIntegral.algpt_int :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O]
    [inst_2 : IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {R : Type} [inst_4 : CommRing R]
    [inst_5 : Algebra O R] [inst_6 : IsLocalRing R] {K : Type} [inst_7 : Field K] [inst_8 : Algebra O K]
    [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (f : R →ₐ[O] K),
    ∀ a ∈ IsLocalRing.maximalIdeal R, IsIntegral O ((f : R → K) a) := by
  intro O _ _ _ _ R _ _ _ K _ _ _ _ f a ha
  classical
  obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := O) (f a)
  obtain ⟨inst⟩ : Nonempty (NormalizedGCDMonoid O) := inferInstance
  have h1 : aeval (f a) p.primPart = 0 := aeval_primPart_eq_zero hp0 hp
  have h2 : ∃ i, p.primPart.coeff i ∉ IsLocalRing.maximalIdeal O := by
    by_contra hc
    push Not at hc
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    apply hϖ.not_isUnit
    apply isPrimitive_iff_isUnit_of_C_dvd.1 p.isPrimitive_primPart
    rw [C_dvd_iff_dvd_coeff]
    intro i
    have := hc i
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
  obtain ⟨g, q, hg, hq, e⟩ := UpperTheory.Reformulated.B.AlgebraicPointIntegral.factor _ h2
  have h3 : IsUnit (aeval a q) := by
    by_contra hu
    have hm : aeval a q ∈ IsLocalRing.maximalIdeal R := hu
    have e3 : aeval a q = aeval a q.divX * a + algebraMap O R (q.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add q]
      simp
    rw [e3, Ideal.add_mem_iff_right _ (Ideal.mul_mem_left _ _ ha)] at hm
    exact hm (hq.map _)
  have h4 : aeval (f a) q ≠ 0 := by
    rw [aeval_algHom_apply]
    exact (h3.map f).ne_zero
  rw [e, map_mul] at h1
  exact ⟨g, hg, (mul_eq_zero.1 h1).resolve_right h4⟩
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

section SlopeTestRemainingChoices

open Polynomial

private theorem algpt_int {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] {R : Type} [CommRing R] [Algebra O R] [IsLocalRing R]
    {K : Type} [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (f : R →ₐ[O] K)
    (a : R) (ha : a ∈ maximalIdeal R) : IsIntegral O (f a) :=
  _root_.UpperTheory.Reformulated.B.AlgebraicPointIntegral.algpt_int f a ha

private theorem algpt_pow {O S : Type} [CommRing O] [CommRing S] [Algebra O S] [IsNoetherianRing S] (m : Ideal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ m) (n : ℕ) :
    ∃ N : Submodule O S, N.FG ∧ ∀ x : S, ∃ y ∈ N, x - y ∈ m ^ n :=
  _root_.UpperTheory.Reformulated.B.FinitelyGeneratedModPow.fg_mod_pow m hres n

private theorem algpt_finite {O S : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing S] [Algebra O S] [IsLocalRing S] [IsNoetherianRing S] [Algebra.IsIntegral O S]
    (hloc : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ maximalIdeal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ maximalIdeal S) : Module.Finite O S := by
  set J : Ideal S := (maximalIdeal O).map (algebraMap O S) with hJ
  have hJle : J ≤ maximalIdeal S := Ideal.map_le_iff_le_comap.2 hloc
  have hJne : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (h ▸ hJle))
  haveI : IsHausdorff (maximalIdeal O) S :=
    IsHausdorff.map_algebraMap_iff.1 (IsHausdorff.of_isLocalRing J S hJne)
  have hrad : maximalIdeal S ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hJP, hP⟩
    have h1 : maximalIdeal O ≤ P.comap (algebraMap O S) := Ideal.map_le_iff_le_comap.1 hJP
    have h2 : P.comap (algebraMap O S) = maximalIdeal O :=
      ((maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) h1).symm
    have h3 : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
      (algebraMap O S) (algebraMap_isIntegral_iff.mpr ‹Algebra.IsIntegral O S›) P
      (h2 ▸ maximalIdeal.isMaximal O)
    exact (eq_maximalIdeal h3).ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  obtain ⟨N, hN, h⟩ := algpt_pow (maximalIdeal S) hres n
  refine (UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) S).2 ⟨?_⟩
  have : (⊤ : Submodule O (S ⧸ (maximalIdeal O) • (⊤ : Submodule O S))) = N.map (Submodule.mkQ _) := by
    symm
    rw [Submodule.map_mkQ_eq_top, eq_top_iff]
    intro x _
    obtain ⟨y, hy, h1⟩ := h x
    have h2 : x - y ∈ (maximalIdeal O) • (⊤ : Submodule O S) := by
      rw [Ideal.smul_top_eq_map]
      exact hn h1
    simpa using Submodule.add_mem_sup h2 hy
  rw [this]
  exact hN.map _

end SlopeTestRemainingChoices

theorem UpperTheory.V.W.exists_algebraicPoint_of_groupDeterminant :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (K : Type) [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (f : R →ₐ[O] K), Module.Finite O f.range := by
  intro O _ _ _ _ R _ _ _ K _ _ _ _ f
  have hint : ∀ a : R, IsIntegral O (f a) := by
    intro a
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    have h1 : IsIntegral O (f (a - algebraMap O R c)) := algpt_int f _ hc
    have h2 : f a = f (a - algebraMap O R c) + algebraMap O _ c := by simp
    rw [h2]
    exact h1.add isIntegral_algebraMap
  let g : R →ₐ[O] f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' (g : R →+* f.range) hg
  haveI : IsNoetherianRing f.range := isNoetherianRing_of_surjective R _ (g : R →+* f.range) hg
  haveI : IsLocalHom (g : R →+* f.range) := IsLocalHom.of_surjective _ hg
  have hm : ∀ a ∈ maximalIdeal R, g a ∈ maximalIdeal f.range := fun a ha =>
    map_nonunit (g : R →+* f.range) a ha
  haveI : Algebra.IsIntegral O f.range := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hg x
    exact (isIntegral_algHom_iff f.range.val Subtype.val_injective).1 (hint a)⟩
  exact algpt_finite
    (fun a ha => by
      rw [← g.commutes]
      exact hm _ (map_nonunit (algebraMap O R) a ha))
    (fun x => by
      obtain ⟨a, rfl⟩ := hg x
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
      exact ⟨c, by simpa using hm _ hc⟩)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairPullback
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.W.FramePullback

section Det

variable {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]

private theorem chi_comap (D : GDet n A G) (φ : H →* G) (y : MonoidAlgebra A H) :
    (D.comap φ).chi y = D.chi (MonoidAlgebra.mapDomainRingHom A φ y) := by
  change D.D _ (MonoidAlgebra.mapDomainRingHom _ φ _) = D.D _ _
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp

private theorem lam_comap (D : GDet n A G) (φ : H →* G) (i : ℕ) (y : MonoidAlgebra A H) :
    (D.comap φ).lam i y = D.lam i (MonoidAlgebra.mapDomainRingHom A φ y) := by
  unfold GDet.lam
  rw [chi_comap]

private theorem tr_zero (D : GDet n A G) (hn : 1 ≤ n) : D.tr 0 = 0 := by
  have h1 : D.chi 0 = Polynomial.X ^ n := by
    have := D.homog (Polynomial A) Polynomial.X 1
    rw [map_one, mul_one] at this
    rw [← this, GDet.chi, map_zero, sub_zero]
    congr 1
    simp [MonoidAlgebra.one_def]
  unfold GDet.tr GDet.lam
  rw [h1, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]

private theorem tr_dim_zero (D : GDet 0 A G) (y : MonoidAlgebra A G) : D.tr y = -1 := by
  have h1 : ∀ x, D.D (Polynomial A) x = D.D (Polynomial A) 0 := fun x => by
    have := D.homog (Polynomial A) 0 x
    rw [zero_smul, pow_zero, one_mul] at this
    exact this.symm
  have h2 : D.chi y = 1 := by rw [GDet.chi, h1, ← h1 1, map_one]
  unfold GDet.tr GDet.lam
  rw [h2]
  simp

private theorem ofRep_comap (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) :
    (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (ρ.comp φ) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg]

end Det

private theorem adic_comp {Γ Γ' R : Type} [TopologicalSpace Γ] [TopologicalSpace Γ'] [CommRing R] {I : Ideal R}
    {f : Γ → R} (hf : AdicCont I f) {φ : Γ' → Γ} (hφ : Continuous φ) : AdicCont I fun x => f (φ x) :=
  fun m => (hf m).comp_continuous hφ

private theorem mu_map {l : ℕ} [Fact l.Prime] {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : G →* H) (hφ : Continuous φ) {g : G}
    (hg : g ∈ muG l G) : φ g ∈ muG l H := by
  obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.1 hg
  refine CommGroup.mem_primaryComponent.2 ⟨k, ?_⟩
  have h1 : g ^ l ^ k ∈ (commutator G).topologicalClosure := (QuotientGroup.eq_one_iff _).1 hk
  have h2 : (commutator G).topologicalClosure ≤ (commutator H).topologicalClosure.comap φ := by
    refine Subgroup.topologicalClosure_minimal _ ?_ ((Subgroup.isClosed_topologicalClosure _).preimage hφ)
    refine le_trans ?_ (Subgroup.comap_mono (Subgroup.le_topologicalClosure _))
    rw [← Subgroup.map_le_iff_le_comap, commutator, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have h3 : φ g ^ l ^ k ∈ (commutator H).topologicalClosure := by
    rw [← map_pow]; exact h2 h1
  exact (QuotientGroup.eq_one_iff _).2 h3

variable {l : ℕ} [Fact l.Prime] {F' F : GFrame l} (h : FHom F' F)

private theorem continuous_pullback_projection : Continuous h.π₀ := (h.π_cont.comp (continuous_subtype_val : Continuous (fun x : F'.G₀ => (x : F'.Γ)))).subtype_mk _

private theorem pullback_projection_frobenius (v) (g) : h.π₀ (F'.φ v g) = F.φ (h.vl v) (h.gv v g) := Subtype.ext (h.hφ v g).symm

private theorem pullback_projection_conj (g) : h.π₀ (F'.conj g) = F.conj (h.π₀ g) := by
  apply Subtype.ext
  change h.π (F'.c * g * F'.c⁻¹) = F.c * h.π g * F.c⁻¹
  rw [map_mul, map_mul, map_inv, h.hc]

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R]

private theorem pullback_projection_sign_eq (g) : F.eps O R (h.π₀ g) = F'.eps O R g := by
  change Units.map _ (F.ε (h.π g)) = Units.map _ (F'.ε g)
  rw [h.hε]

private theorem star_single (F : GFrame l) (n : ℕ) (g : F.G₀) :
    F.star O R n (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R) := by
  simp [GFrame.star, GFrame.starOp]

private theorem map_star0 (n : ℕ) (g : F'.G₀) :
    MonoidAlgebra.mapDomainRingHom R h.π₀ (F'.star O R n (MonoidAlgebra.single g 1)) =
      F.star O R n (MonoidAlgebra.single (h.π₀ g) 1) := by
  rw [star_single, star_single, pullback_projection_sign_eq, ← pullback_projection_conj, ← map_inv]
  simp

private theorem map_oEl {n : ℕ} (v : F'.Vl) (ψ : Fin n → F.Gv (h.vl v) →* Rˣ) (g : Fin n → F'.Gv v) :
    MonoidAlgebra.mapDomainRingHom R h.π₀ (F'.oEl v (fun i => (ψ i).comp (h.gv v)) g) =
      F.oEl (h.vl v) ψ fun i => h.gv v (g i) := by
  unfold GFrame.oEl
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  rw [Function.comp_apply, map_sub]
  simp [pullback_projection_frobenius]

end UpperTheory.V.W.FramePullback


open UpperTheory.V.W.FramePullback in
theorem UpperTheory.V.W.Pair.isEmpty_of_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R)
    (hn : n = 0) : IsEmpty F.St ∧ IsEmpty F.Vl := by
  subst hn
  refine ⟨⟨fun u => ?_⟩, ⟨fun v => ?_⟩⟩
  · have := p.I u 1 (one_mem _) 1
    rw [tr_dim_zero] at this
    exact one_ne_zero (neg_eq_zero.1 this)
  · have := p.Ord v (fun _ => 1) 1
    rw [tr_dim_zero] at this
    exact one_ne_zero (neg_eq_zero.1 this)

open UpperTheory.V.W.FramePullback in
theorem UpperTheory.V.W.exists_determinantPair_pullback :
    ∀ (l : ℕ) [Fact l.Prime] (F' F : GFrame l) (h : FHom F' F) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r' : Resid F' O n) (r : Resid F O n), h.Compat r' r → (n = 0 → IsEmpty F'.St) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R),
      ∃ p' : Pair r' R, p'.D = p.D.comap h.π₀ ∧ ∀ v i, p'.ψ v i = (p.ψ (h.vl v) i).comp (h.gv v) := by
  intro l _ F' F h O _ _ _ n r' r hc hn R _ _ _ p
  have hs : ∀ g : F'.G₀, MonoidAlgebra.mapDomainRingHom R h.π₀ (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (h.π₀ g) 1 := fun g => by simp
  refine ⟨⟨p.D.comap h.π₀, fun v i => (p.ψ (h.vl v) i).comp (h.gv v), fun i => ?_, ?_, fun v i => ⟨?_, fun g => ?_, fun g => ?_⟩,
    fun i g => ?_, fun v g k => ?_, fun u g hg k => ?_⟩, rfl, fun _ _ => rfl⟩
  · simp only [lam_comap, hs]
    exact adic_comp (p.cont i) (continuous_pullback_projection h)
  · have : (p.D.comap h.π₀).map (res O R : R →+* ResidueField O) =
        (p.D.map (res O R : R →+* ResidueField O)).comap h.π₀ := rfl
    rw [this, p.red, Resid.Dbar, ofRep_comap, Resid.Dbar]
    congr 1
    ext g : 1
    have e : r'.chib = fun i => (r.chib i).comp h.π₀ := funext hc.chib
    rw [e]; rfl
  · exact adic_comp (p.psi (h.vl v) i).cont (h.gv_cont v)
  · rw [hc.psib]
    exact (p.psi (h.vl v) i).red _
  · have hg : h.gv v g ∈ F.mu (h.vl v) := mu_map (h.gv v) (h.gv_cont v) g.2
    rw [hc.th v i g hg]
    exact (p.psi (h.vl v) i).mu ⟨_, hg⟩
  · rw [lam_comap, lam_comap, map_star0, hs, p.P]
  · rw [GDet.tr, lam_comap, map_mul, hs, map_oEl]
    exact p.Ord _ _ _
  · rw [GDet.tr, lam_comap, map_mul, map_sub, hs, hs, map_one]
    rcases hc.ip u g hg with h1 | ⟨u', hu'⟩
    · rw [h1, ← MonoidAlgebra.one_def, sub_self, mul_zero]
      exact tr_zero p.D (Nat.pos_of_ne_zero fun h0 => (hn h0).elim u)
    · exact p.I u' _ hu' _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ResidualDiagonalDeterminantIsPolar
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocConstOfKer
theorem UpperTheory.Reformulated.B.LocallyConstantOfKernelCapelliIdentities.locConst_of_ker :
    ∀ {G M : Type} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : Group M] (χ : G →* M),
    IsOpen (↑χ.ker : Set G) → IsLocallyConstant (⇑χ : G → M) := by
  intro G M _ _ _ _ χ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (↑χ.ker : Set G),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro y hy
    have hy' : χ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv] at hy'
    exact (inv_mul_eq_one.mp hy').symm
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W Polynomial

namespace UpperTheory.V.W

private theorem locConst_of_ker {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
    (χ : G →* M) (h : IsOpen (χ.ker : Set G)) : IsLocallyConstant χ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernelCapelliIdentities.locConst_of_ker χ h

private theorem locConst_pi {G M ι : Type} [TopologicalSpace G] [Finite ι] (f : ι → G → M)
    (h : ∀ i, IsLocallyConstant (f i)) : IsLocallyConstant fun g i => f i g := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have := Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (h i) x
  exact this.mono fun y hy => funext hy

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (y : MonoidAlgebra A G) : (GDet.ofRep ρ).chi y =
      (Matrix.scalar (Fin n) X - GDet.repAlg ρ A[X] (MonoidAlgebra.mapRingHom G C y)).det := by
  change (GDet.repAlg ρ A[X] _).det = _
  rw [map_sub]
  congr 2
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, h]

private theorem star_single {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (b : R) :
    F.star O R n (MonoidAlgebra.single g b) =
      MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp]

private theorem star_sub {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (x y : MonoidAlgebra R F.G₀) :
    F.star O R n (x - y) = F.star O R n x - F.star O R n y := by
  simp [GFrame.star]

private theorem eps_C {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) (m : ℤ) :
    ((F.eps O R[X] g ^ m : R[X]ˣ) : R[X]) = C ((F.eps O R g ^ m : Rˣ) : R) := by
  have h : F.eps O R[X] g = Units.map (C : R →+* R[X]).toMonoidHom (F.eps O R g) := Units.ext rfl
  rw [h, ← map_zpow]
  rfl

end UpperTheory.V.W

theorem UpperTheory.V.W.residual_diagonal_determinant_isPolar :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (n : ℕ) (r : Resid F O n) [IsCO O (ResidueField O)], 1 ≤ n → r.Ok → ∃ p : Pair r (ResidueField O), p.D = r.Dbar ∧ p.ψ = r.psib := by
  intro l _ F O _ _ _ _ _ _ _ n r _ hn hok
  have hres : ∀ x, res O (ResidueField O) x = x := fun x => by
    obtain ⟨a, rfl⟩ := residue_surjective x
    exact (res O (ResidueField O)).commutes a
  have hres' : (res O (ResidueField O) : ResidueField O →+* ResidueField O) = RingHom.id _ := RingHom.ext hres
  refine ⟨⟨r.Dbar, r.psib, fun i N => ?_, ?_, fun v i => ⟨fun N => ?_, fun g => hres _, fun g => ?_⟩, fun i g => ?_,
    hok.1, fun u g hg h => ?_⟩, rfl, rfl⟩
  · have h1 := locConst_pi _ fun j => locConst_of_ker _ (r.chib_open j)
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ((IsLocallyConstant.iff_eventually_eq _).1 h1 x).mono fun y hy => ?_
    have h2 : diagRep r.chib y = diagRep r.chib x := by
      change Matrix.diagonal _ = Matrix.diagonal _
      congr 1
      funext j
      rw [congrFun hy j]
    simp only [Resid.Dbar, GDet.lam, chi_ofRep]
    simp [GDet.repAlg, h2]
  · rw [hres']
    rfl
  · exact (locConst_of_ker _ (r.psib_open v i)).comp fun u => Ideal.Quotient.mk _ (u : ResidueField O)
  · rw [hok.2 v i g]
    rfl
  · have h1 := r.polar (ResidueField O)[X] (MonoidAlgebra.single 1 X -
      MonoidAlgebra.mapRingHom _ C (MonoidAlgebra.single g (1 : ResidueField O)))
    simp only [GDet.lam, GDet.chi, Resid.Dbar]
    rw [← h1, star_sub]
    simp only [MonoidAlgebra.mapRingHom_single, star_single, eps_C]
    simp
  · have h2 : diagRep r.chib g = 1 := by
      change Matrix.diagonal _ = Matrix.diagonal _
      congr 1
      funext j
      have h3 : r.chib j g = 1 := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hg).2) j
      rw [h3]
      rfl
    have h4 : GDet.repAlg (diagRep r.chib) (ResidueField O)[X] (MonoidAlgebra.mapRingHom _ C
        (MonoidAlgebra.single h (1 : ResidueField O) * (MonoidAlgebra.single g 1 - 1))) = 0 := by
      rw [map_mul, map_mul, map_sub, map_sub, map_one, map_one]
      simp [GDet.repAlg, h2]
    simp only [GDet.tr, Resid.Dbar, GDet.lam, chi_ofRep, h4, sub_zero]
    have h5 : n - 1 ≠ n := by omega
    simp [Matrix.scalar_apply, coeff_X_pow, h5]
end
