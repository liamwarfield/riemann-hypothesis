module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightedHomogeneousMap
theorem UpperTheory.aeval_map_eq_rename_map_iff :
    ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S), Function.Injective φ → ∀ (σ M : Type) [AddCommMonoid M] (w : σ → M) (ν : M) (f : MvPolynomial σ R), (MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.map φ f) ν ↔ MvPolynomial.IsWeightedHomogeneous w f ν) ∧ ∀ (τ : Type) (gR : σ → MvPolynomial τ R) (gS : σ → MvPolynomial τ S) (ρ : σ → τ), (∀ v, MvPolynomial.map φ (gR v) = gS v) → (MvPolynomial.aeval gS (MvPolynomial.map φ f) = MvPolynomial.rename ρ (MvPolynomial.map φ f) ↔ MvPolynomial.aeval gR f = MvPolynomial.rename ρ f) := by
  intro R S _ _ φ hφ σ M _ w ν f
  refine ⟨?_, ?_⟩
  · unfold MvPolynomial.IsWeightedHomogeneous
    refine forall_congr' fun d => ?_
    rw [MvPolynomial.coeff_map, map_ne_zero_iff φ hφ]
  · intro τ gR gS ρ hg
    have hgS : gS = fun v => MvPolynomial.map φ (gR v) := funext fun v => (hg v).symm
    subst hgS
    rw [MvPolynomial.aeval_eq_bind₁, MvPolynomial.aeval_eq_bind₁, ← MvPolynomial.map_bind₁,
      ← MvPolynomial.map_rename]
    exact (MvPolynomial.map_injective φ hφ).eq_iff
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SemilinearLatticeMem
theorem UpperTheory.semilinear_lattice_mem :
    ∀ (R K C V W : Type) [CommRing R] [Field K] [Field C] [Algebra R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] [AddCommGroup W] [Module C W] (e : K →+* C) (U : Submodule K V) (Φ : U →ₛₗ[e] W) (A : Set C) (L : AddSubgroup W) (G : Set V), (∀ a ∈ A, ∀ y ∈ L, a • y ∈ L) → (∀ r : R, e (algebraMap R K r) ∈ A) → (∀ g ∈ G, ∃ h : g ∈ U, Φ ⟨g, h⟩ ∈ L) → ∀ (s : R), algebraMap R K s ≠ 0 → e (algebraMap R K s)⁻¹ ∈ A → ∀ v : U, s • (v : V) ∈ Submodule.span R G → Φ v ∈ L := by
  intro R K C V W _ _ _ _ _ _ _ _ _ _ e U Φ A L G hA hR hG s hs hsA v hv
  have key : ∀ x ∈ Submodule.span R G, ∃ h : x ∈ U, Φ ⟨x, h⟩ ∈ L := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hG x hx
    | zero =>
      refine ⟨U.zero_mem, ?_⟩
      have h0 : (⟨0, U.zero_mem⟩ : U) = 0 := rfl
      rw [h0, map_zero]
      exact L.zero_mem
    | add x y _ _ hx hy =>
      obtain ⟨hxU, hx⟩ := hx
      obtain ⟨hyU, hy⟩ := hy
      refine ⟨U.add_mem hxU hyU, ?_⟩
      have h0 : (⟨x + y, U.add_mem hxU hyU⟩ : U) = ⟨x, hxU⟩ + ⟨y, hyU⟩ := rfl
      rw [h0, map_add (f := _)]
      exact L.add_mem hx hy
    | smul r x _ hx =>
      obtain ⟨hxU, hx⟩ := hx
      have hm : r • x ∈ U := by
        rw [← algebraMap_smul K r x]
        exact U.smul_mem _ hxU
      refine ⟨hm, ?_⟩
      have h0 : (⟨r • x, hm⟩ : U) = algebraMap R K r • (⟨x, hxU⟩ : U) :=
        Subtype.ext (algebraMap_smul K r x).symm
      rw [h0, LinearMap.map_smulₛₗ]
      exact hA _ (hR r) _ hx
  obtain ⟨hU, hL⟩ := key _ hv
  have h1 : v = (algebraMap R K s)⁻¹ • (⟨s • (v : V), hU⟩ : U) := by
    apply Subtype.ext
    change (v : V) = (algebraMap R K s)⁻¹ • (s • (v : V))
    rw [← algebraMap_smul K s (v : V), inv_smul_smul₀ hs]
  rw [h1, LinearMap.map_smulₛₗ]
  exact hA _ hsA _ hL
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormIntegersLeOne
theorem UpperTheory.norm_integers_le_one :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact (Nat.Prime l)] (e : K →+* PadicAlgCl l) (x : NumberField.RingOfIntegers K), ‖e (algebraMap (NumberField.RingOfIntegers K) K x)‖ ≤ 1 := by
  intro K _ _ l _ e x
  have hx : IsIntegral ℤ (e (algebraMap (NumberField.RingOfIntegers K) K x)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).map e.toIntAlgHom
  generalize e (algebraMap (NumberField.RingOfIntegers K) K x) = y at hx
  let S : Subring (PadicAlgCl l) := (NormedField.valuation (K := PadicAlgCl l)).integer
  have hS : IsIntegral S y := hx.tower_top
  have h := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral hS
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h
end

open MvPolynomial in
private theorem mem_dw_iff {R : Type} [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν ↔ IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) f ν ∧
      ∀ l j : Fin n, l < j → Formalism.GradedWeylDivisibility.colAddGen R l j f = rename some f := by
  simp [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_iInf, sub_eq_zero]

open MvPolynomial in
private theorem map_mem_dw_iff {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ)
    (r n : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ f ∈ Formalism.GradedWeylDivisibility.dualWeyl S r n ν ↔ f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν := by
  rw [mem_dw_iff, mem_dw_iff]
  obtain ⟨h1, h2⟩ := UpperTheory.aeval_map_eq_rename_map_iff R S φ hφ _ _ (Formalism.GradedWeylDivisibility.colW r n) ν f
  refine and_congr h1 (forall_congr' fun l => forall_congr' fun j => forall_congr' fun _ => ?_)
  refine h2 _ _ _ some fun v => ?_
  split_ifs <;> simp

private theorem smul_mem_latN {l : ℕ} [Fact l.Prime] {ι : Type} {n : ℕ} (F : GlobalTheory.ExpFrame.Frame l ι n) (lamW : ι → ℕ → ℕ)
    (a : F.O) (y : Formalism.CohomologicalDescent.DepthNonnegative.NablaT (PadicAlgCl l) n lamW) (hy : y ∈ F.latN lamW) : F.emb a • y ∈ F.latN lamW := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, x, hx, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * c, x, hx, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

private theorem map_detPol {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) :
    MvPolynomial.map φ (GlobalTheory.FrameRead.detPol R n) = GlobalTheory.FrameRead.detPol S n := by
  unfold GlobalTheory.FrameRead.detPol
  rw [RingHom.map_det]
  congr 1
  ext a s : 2
  simp

theorem UpperTheory.Reformulated.B.Ga11.lift_nabStd_mem_latN :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K] (l : ℕ)
    [inst_2 : Fact (Nat.Prime l)] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (e0 : K →+* PadicAlgCl l) (ι : Type) [inst_3 : Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → Formalism.BasicNotions.DomWeight n)
    (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : GlobalTheory.ExpFrame.Frame l ι n)
    (Φ : ↥(Formalism.L2.DIV.VV K lam) →ₛₗ[e0] Formalism.CohomologicalDescent.DepthNonnegative.NablaT (PadicAlgCl l) n lamW),
    GlobalTheory.FrameRead.AtPlace w e0 →
      Function.Injective (⇑F.emb : F.O → PadicAlgCl l) →
        (∀ (x : K),
            ‖(e0 : K → PadicAlgCl l) x‖ ≤ (1 : ℝ) → (e0 : K → PadicAlgCl l) x ∈ Set.range (⇑F.emb : F.O → PadicAlgCl l)) →
          GlobalTheory.FrameRead.Shift lam lamW c →
            GlobalTheory.FrameRead.IsPhi e0 lam lamW Φ →
              ∀ (v : ↥(Formalism.L2.DIV.VV K lam)),
                (↑v : Formalism.L2.DIV.Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.L2.DIV.nabStd K lam) →
                  (Φ : ↥(Formalism.L2.DIV.VV K lam) → Formalism.CohomologicalDescent.DepthNonnegative.NablaT (PadicAlgCl l) n lamW) v ∈
                    F.latN
                      lamW := by
  intro K _ _ l _ w e0 ι _ _ n lam lamW c F Φ hw hinj hrange _ hΦ v hv
  obtain ⟨s, hs, hv⟩ := hv
  have hint : ∀ r : NumberField.RingOfIntegers K, e0 (algebraMap _ K r) ∈ Set.range F.emb :=
    fun r => hrange _ (UpperTheory.norm_integers_le_one K l e0 r)
  have hs1 : 1 ≤ ‖e0 (algebraMap _ K s)‖ := not_lt.1 fun h => hs ((hw s).2 h)
  have hs0 : algebraMap _ K s ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hs1
    exact absurd hs1 (by norm_num)
  refine UpperTheory.semilinear_lattice_mem _ K _ _ _ e0 _ Φ (Set.range F.emb) (F.latN lamW) _ ?_ hint ?_ s hs0 ?_ v hv
  · rintro _ ⟨a, rfl⟩ y hy
    exact smul_mem_latN F lamW a y hy
  · rintro _ ⟨x, hx, rfl⟩
    choose x0 hx0 hxe using hx
    have hxe' : ∀ τ, MvPolynomial.map (algebraMap (NumberField.RingOfIntegers K) K) (x0 τ) = x τ := hxe
    have hxK : ∀ τ, x τ ∈ Formalism.BasicNotions.nablaSq K n (lam τ) := fun τ => by
      rw [← hxe' τ]
      exact (map_mem_dw_iff _ (IsFractionRing.injective _ K) _ _ _ _).2 (hx0 τ)
    have hU : Formalism.L2.DIV.ten x ∈ Formalism.L2.DIV.VV K lam := Submodule.subset_span ⟨x, hxK, rfl⟩
    refine ⟨hU, ?_⟩
    obtain ⟨y, hy, hΦv⟩ := hΦ x ⟨_, hU⟩ hxK rfl
    let φ : NumberField.RingOfIntegers K →+* F.O :=
      ((RingEquiv.ofBijective F.emb.rangeRestrict
        ⟨fun a b h => hinj (congrArg Subtype.val h), F.emb.rangeRestrict_surjective⟩).symm.toRingHom).comp
        ((e0.comp (algebraMap _ K)).codRestrict F.emb.range hint)
    have hφ : F.emb.comp φ = e0.comp (algebraMap _ K) := by
      ext r
      exact congrArg Subtype.val ((RingEquiv.ofBijective F.emb.rangeRestrict
        ⟨fun a b h => hinj (congrArg Subtype.val h), F.emb.rangeRestrict_surjective⟩).apply_symm_apply _)
    refine AddSubgroup.subset_closure ⟨1, y, fun τ => ?_, ?_⟩
    · have he : MvPolynomial.map F.emb (GlobalTheory.FrameRead.liftPol φ (lamW τ (n - 1)) (x0 τ)) = y τ := by
        rw [hy τ, ← hxe' τ]
        simp only [GlobalTheory.FrameRead.liftPol, map_mul, map_pow, map_detPol, MvPolynomial.map_map, hφ]
      refine ⟨_, (map_mem_dw_iff F.emb hinj _ _ _ _).1 ?_, he⟩
      rw [he]
      exact (y τ).2
    · rw [map_one, one_smul]
      exact hΦv
  · refine hrange _ ?_
    rw [map_inv₀, norm_inv]
    exact inv_le_one_of_one_le₀ hs1
