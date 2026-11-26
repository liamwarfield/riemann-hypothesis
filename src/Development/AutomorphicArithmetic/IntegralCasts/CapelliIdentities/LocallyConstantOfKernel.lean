module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel
theorem UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker :
    ∀ {Γ C : Type} [inst : Group Γ]
    [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [inst_3 : Group C] (η : Γ →* C),
    IsOpen (↑η.ker : Set Γ) → IsLocallyConstant (⇑η : Γ → C) := by
  intro Γ C _ _ _ _ η h
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (η.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change x⁻¹ * x ∈ η.ker
    simp [MonoidHom.mem_ker]
  · intro y hy
    have hy' : η (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv] at hy'
    exact (inv_mul_eq_one.mp hy').symm
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfIsIntegral
namespace UpperTheory.Reformulated.B.NormLeOneOfIsIntegral

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  have hle : ∀ y : PadicAlgCl l,
      y ∈ (PadicAlgCl.valued l).v.integer ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [Valuation.mem_integer_iff, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  have hmem : ∀ a : ℤ_[l],
      algebraMap ℤ_[l] (PadicAlgCl l) a ∈ (PadicAlgCl.valued l).v.integer := by
    intro a
    rw [hle, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact (PadicAlgCl.norm_extends l _).trans_le a.2
  have hint : IsIntegral (PadicAlgCl.valued l).v.integer x :=
    hx.map_of_comp_eq ((algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict _ hmem) (RingHom.id _) rfl
  exact (hle x).1 ((Valuation.integer.integers (PadicAlgCl.valued l).v).mem_of_integral hint)

end UpperTheory.Reformulated.B.NormLeOneOfIsIntegral
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixedSubgroup
noncomputable def UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd :
    {A H M : Type} →
      [inst : CommRing A] →
        [inst_1 : Group H] →
          [inst_2 : AddCommGroup M] → [inst_3 : _root_.Module A M] → Representation A H M → Subgroup H → Submodule A M :=
  fun {_A _H _M} _ _ _ _ ρ K =>
    { carrier := {v | ∀ k ∈ K, ρ k v = v}
      add_mem' := fun {a b} ha hb k hk => by
        rw [map_add (f := _), ha k hk, hb k hk]
      zero_mem' := fun k _ => map_zero (ρ k)
      smul_mem' := fun c v hv k hk => by
        rw [map_smul, hv k hk] }
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinitelyGeneratedModPow
namespace UpperTheory.Reformulated.B.FinitelyGeneratedModPow

theorem fg_mod_pow {O A : Type} [CommRing O] [CommRing A] [Algebra O A] [IsNoetherianRing A]
    (m : Ideal A) (hres : ∀ x : A, ∃ a : O, x - algebraMap O A a ∈ m) (n : ℕ) :
    ∃ N : Submodule O A, N.FG ∧ ∀ x : A, ∃ y ∈ N, x - y ∈ m ^ n := by
  induction n with
  | zero => exact ⟨⊥, Submodule.fg_bot, fun x => ⟨0, Submodule.zero_mem _, by simp⟩⟩
  | succ n ih =>
    obtain ⟨N, hN, hx⟩ := ih
    obtain ⟨s, hs⟩ : (m ^ n).FG := IsNoetherian.noetherian (m ^ n)
    have key : ∀ z ∈ Ideal.span (s : Set A),
        ∃ w ∈ Submodule.span O (s : Set A), z - w ∈ m ^ (n + 1) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz => exact ⟨z, Submodule.subset_span hz, by simp⟩
      | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
      | add z₁ z₂ _ _ h₁ h₂ =>
        obtain ⟨w₁, hw₁, e₁⟩ := h₁
        obtain ⟨w₂, hw₂, e₂⟩ := h₂
        refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_⟩
        have : z₁ + z₂ - (w₁ + w₂) = (z₁ - w₁) + (z₂ - w₂) := by ring
        rw [this]
        exact Ideal.add_mem _ e₁ e₂
      | smul a z hz h =>
        obtain ⟨w, hw, e⟩ := h
        obtain ⟨c, hc⟩ := hres a
        have hz' : z ∈ m ^ n := by rw [← hs]; exact hz
        refine ⟨c • w, Submodule.smul_mem _ c hw, ?_⟩
        have : a • z - c • w = z * (a - algebraMap O A c) + algebraMap O A c * (z - w) := by
          rw [smul_eq_mul, Algebra.smul_def]; ring
        rw [this]
        refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ e)
        rw [pow_succ]
        exact Ideal.mul_mem_mul hz' hc
    refine ⟨N ⊔ Submodule.span O (s : Set A), hN.sup ⟨s, rfl⟩, fun x => ?_⟩
    obtain ⟨y, hy, hxy⟩ := hx x
    rw [← hs] at hxy
    obtain ⟨w, hw, e⟩ := key _ hxy
    refine ⟨y + w, Submodule.add_mem_sup hy hw, ?_⟩
    rwa [← sub_sub]

end UpperTheory.Reformulated.B.FinitelyGeneratedModPow
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLtOne
namespace UpperTheory.Reformulated.B.NormLtOne

theorem norm_lt_one {l : ℕ} [Fact l.Prime] {O R : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [CommRing R] [IsLocalRing R] [Algebra O R]
    (y : R →ₐ[O] PadicAlgCl l) (a : R) (ha : a ∈ IsLocalRing.maximalIdeal R) : ‖y a‖ < 1 := by
  by_contra hx
  rw [not_lt] at hx
  have hx0 : y a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact absurd hx (by norm_num)
  have hu : ‖(y a)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hx
  have hint : IsIntegral ℚ_[l] (y a)⁻¹ := Algebra.IsIntegral.isIntegral _
  have hmon : (minpoly ℚ_[l] (y a)⁻¹).Monic := minpoly.monic hint
  have hc : ∀ n, ‖(minpoly ℚ_[l] (y a)⁻¹).coeff n‖ ≤ 1 := by
    rw [← spectralValue_le_one_iff hmon]
    exact hu
  have hz := minpoly.aeval ℚ_[l] (y a)⁻¹
  generalize minpoly ℚ_[l] (y a)⁻¹ = P at hmon hc hz
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_smul] at hz
  let c : ℕ → ℤ_[l] := fun i => ⟨P.coeff i, hc i⟩
  have hr : (∑ i ∈ Finset.range P.natDegree,
      algebraMap O R (algebraMap ℤ_[l] O (c i)) * a ^ (P.natDegree - i)) ∈ IsLocalRing.maximalIdeal R := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ha _ ?_)
    have := Finset.mem_range.mp hi
    omega
  have hunit := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (neg_mem hr)
  apply (hunit.map y).ne_zero
  have hz' := congrArg (· * y a ^ P.natDegree) hz
  simp only [zero_mul, add_mul, Finset.sum_mul] at hz'
  rw [← mul_pow, inv_mul_cancel₀ hx0, one_pow] at hz'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sub_neg_eq_add, map_add (f := _), map_one, map_sum, add_comm, ← hz']
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := (Finset.mem_range.mp hi).le
  rw [map_mul, map_pow, AlgHom.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), Algebra.smul_def, mul_assoc,
    pow_sub₀ _ hx0 hi', inv_pow, mul_comm (y a ^ P.natDegree)]
  rfl

end UpperTheory.Reformulated.B.NormLtOne
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsInfEmbUnique
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh26.Ainf :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ NumberField.InfiniteAdeleRing F

noncomputable def UpperTheory.Reformulated.B.Qh26.IsInfEmb :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] → [inst_2 : Algebra F E] → (E →+* ℂ) → (TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ) → Prop :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (τ : E →+* ℂ)
        (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ) ↦
      (∀ (x : E),
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E → ℂ) ((1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] x) = (τ : E → ℂ) x) ∧
        Continuous fun (a : UpperTheory.Reformulated.B.Qh26.Ainf F) ↦
          (θ : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E → ℂ) (a ⊗ₜ[F] (1 : E))

theorem UpperTheory.Reformulated.B.Qh26.isInfEmb_unique :
    ∀ {F E : Type} [inst : Field F] [NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E] (τ : E →+* ℂ)
      {θ θ' : TensorProduct F (UpperTheory.Reformulated.B.Qh26.Ainf F) E →+* ℂ},
      UpperTheory.Reformulated.B.Qh26.IsInfEmb τ θ → UpperTheory.Reformulated.B.Qh26.IsInfEmb τ θ' → θ = θ' := by
  intro F E _ _ _ _ _ τ θ θ' h h'
  have hd : DenseRange (algebraMap F (UpperTheory.Reformulated.B.Qh26.Ainf F)) :=
    NumberField.InfiniteAdeleRing.denseRange_algebraMap F
  have key : ∀ x : F, (algebraMap F (UpperTheory.Reformulated.B.Qh26.Ainf F) x) ⊗ₜ[F] (1 : E)
      = (1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] (algebraMap F E x) := by
    intro x
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have h1 : (fun a : UpperTheory.Reformulated.B.Qh26.Ainf F ↦ θ (a ⊗ₜ[F] (1 : E)))
      = fun a : UpperTheory.Reformulated.B.Qh26.Ainf F ↦ θ' (a ⊗ₜ[F] (1 : E)) := by
    refine hd.equalizer h.2 h'.2 ?_
    funext x
    simp only [Function.comp_apply]
    rw [key, h.1, h'.1]
  refine RingHom.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a e =>
    have hs : a ⊗ₜ[F] e = (a ⊗ₜ[F] (1 : E)) * ((1 : UpperTheory.Reformulated.B.Qh26.Ainf F) ⊗ₜ[F] e) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hs, map_mul, map_mul, h.1, h'.1, congrFun h1 a]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvalue
theorem UpperTheory.Reformulated.B.CommonEigenvectorOfCommutingSet.common_eig :
    ∀ {k : Type} [inst : Field k] [IsAlgClosed k]
    {V : Type} [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V] [FiniteDimensional k V] (S : Set (Module.End k V)),
    (∀ f ∈ S, ∀ f' ∈ S, f * f' = f' * f) →
      ∀ (d : ℕ) (W : Submodule k V),
        Module.finrank k ↥W = d →
          W ≠ ⊥ →
            (∀ f ∈ S, ∀ x ∈ W, (f : V → V) x ∈ W) → ∃ v ∈ W, v ≠ (0 : V) ∧ ∀ f ∈ S, ∃ (c : k), (f : V → V) v = c • v := by
  intro k _ _ V _ _ _ S hS d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro W hd hW hinv
    by_cases h : ∀ f ∈ S, ∀ x ∈ W, ∃ c : k, f x = c • x
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      exact ⟨v, hv, hv0, fun f hf => h f hf v hv⟩
    · push Not at h
      obtain ⟨f, hf, x, hx, hfx⟩ := h
      haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f.restrict (hinv f hf) : Module.End k W)
      obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
      have hwe : f (w : V) = μ • (w : V) := by
        have h1 := congrArg Subtype.val hw.apply_eq_smul
        simpa [LinearMap.restrict_apply] using h1
      have hw0 : (w : V) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
      have hlt : W ⊓ f.eigenspace μ < W := by
        refine lt_of_le_of_ne inf_le_left fun he => ?_
        have hx' : x ∈ W ⊓ f.eigenspace μ := he.symm ▸ hx
        exact hfx μ (Module.End.mem_eigenspace_iff.mp hx'.2)
      have hne : W ⊓ f.eigenspace μ ≠ ⊥ := by
        intro hb
        have hm : (w : V) ∈ W ⊓ f.eigenspace μ :=
          ⟨w.2, Module.End.mem_eigenspace_iff.mpr hwe⟩
        rw [hb] at hm
        exact hw0 ((Submodule.mem_bot k).mp hm)
      have hinv' : ∀ g ∈ S, ∀ y ∈ W ⊓ f.eigenspace μ, g y ∈ W ⊓ f.eigenspace μ := by
        intro g hg y hy
        refine ⟨hinv g hg y hy.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h1 : f y = μ • y := Module.End.mem_eigenspace_iff.mp hy.2
        have h2 : f (g y) = g (f y) := LinearMap.congr_fun (hS f hf g hg) y
        rw [h2, h1, map_smul]
      obtain ⟨v, hv, hv0, hv'⟩ := ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl hne hinv'
      exact ⟨v, hv.1, hv0, hv'⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemSpanVariable
theorem UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X :
    ∀ {O σ : Type} [inst : CommRing O] [Fintype σ]
    (f : MvPowerSeries σ O),
    (MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) f = (0 : O) → f ∈ Ideal.span (Set.range MvPowerSeries.X) := by
  intro O σ _ _ f hf
  classical
  have hc : ∀ n : σ →₀ ℕ, ∃ o : Option σ, n ≠ 0 → ∃ i, o = some i ∧ n i ≠ 0 := by
    intro n
    by_cases h : n = 0
    · exact ⟨none, fun h' => absurd h h'⟩
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp h
      exact ⟨some i, fun _ => ⟨i, rfl, hi⟩⟩
  choose c hc using hc
  let g : σ → MvPowerSeries σ O := fun i m =>
    if c (m + Finsupp.single i 1) = some i then
      MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0
  have hg : ∀ i m, MvPowerSeries.coeff m (g i) =
      if c (m + Finsupp.single i 1) = some i then
        MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0 := fun _ _ => rfl
  have key : ∀ (i : σ) (n : σ →₀ ℕ), MvPowerSeries.coeff n (MvPowerSeries.X i * g i) =
      if n i ≠ 0 ∧ c n = some i then MvPowerSeries.coeff n f else 0 := by
    intro i n
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
    by_cases h : n i = 0
    · have h' : ¬ Finsupp.single i 1 ≤ n := by
        rw [Finsupp.single_le_iff]; omega
      rw [if_neg h', if_neg (fun hh => hh.1 h)]
    · have h' : Finsupp.single i 1 ≤ n := by
        rw [Finsupp.single_le_iff]; omega
      rw [if_pos h', one_mul, hg, tsub_add_cancel_of_le h']
      simp [h]
  have hsum : f = ∑ i, MvPowerSeries.X i * g i := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [key]
    by_cases h : n = 0
    · subst h
      simpa using hf
    · obtain ⟨i, hi, hn⟩ := hc n h
      rw [Finset.sum_eq_single i]
      · rw [if_pos ⟨hn, hi⟩]
      · intro j _ hj
        rw [if_neg]
        rintro ⟨_, h2⟩
        exact hj (Option.some.inj (h2.symm.trans hi))
      · intro h2
        exact absurd (Finset.mem_univ i) h2
  rw [hsum]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PiSpanVariable
theorem UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X :
    ∀ {O σ : Type} [inst : CommRing O] (s : Finset σ)
    (f : MvPowerSeries σ O),
    (∀ (n : σ →₀ ℕ), (∀ i ∈ s, (n : σ → ℕ) i = (0 : ℕ)) → (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f = (0 : O)) →
      f ∈ Ideal.span (Set.range MvPowerSeries.X) := by
  intro O σ inst s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    rw [h0]
    exact Ideal.zero_mem _
  | insert a t hat ih =>
    intro f hf
    let g : MvPowerSeries σ O := fun n => if n a = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g =
        if n a = 0 then MvPowerSeries.coeff n f else 0 := fun n => rfl
    have h1 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) := by
      apply ih
      intro n hn
      rw [hg]
      split_ifs with h
      · apply hf
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have h2 : (MvPowerSeries.X a : MvPowerSeries σ O) ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro m hm
      rw [map_sub, hg, if_pos hm, sub_self]
    have h3 : f - g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨a, rfl⟩)
    have h4 := Ideal.add_mem _ h3 h1
    rwa [sub_add_cancel] at h4
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMoreTer
theorem UpperTheory.Reformulated.B.Qf50.multiset_eq_of_sum :
    ∀ {Γ : Type} [inst : Monoid Γ] (s t : Multiset (Γ →* ℂ)),
    (∀ (g : Γ),
        (Multiset.map (fun (f : Γ →* ℂ) ↦ (f : Γ → ℂ) g) s).sum =
          (Multiset.map (fun (f : Γ →* ℂ) ↦ (f : Γ → ℂ) g) t).sum) →
      s = t := by
  classical
  intro Γ _ s t h
  have key : ∀ (u : Finset (Γ →* ℂ)) (r : Multiset (Γ →* ℂ)), r.toFinset ⊆ u → ∀ g : Γ,
      (Multiset.map (fun (f : Γ →* ℂ) ↦ (f : Γ → ℂ) g) r).sum
        = ∑ f ∈ u, (r.count f : ℂ) * f g := by
    intro u r hr g
    rw [Finset.sum_multiset_map_count, Finset.sum_subset hr]
    · exact Finset.sum_congr rfl fun f _ => by simp
    · intro f _ hf
      have : r.count f = 0 := Multiset.count_eq_zero.2 (by simpa using hf)
      simp [this]
  set u : Finset (Γ →* ℂ) := s.toFinset ∪ t.toFinset with hu
  have hs : s.toFinset ⊆ u := Finset.subset_union_left
  have ht : t.toFinset ⊆ u := Finset.subset_union_right
  have lin := linearIndependent_iff'.1 (linearIndependent_monoidHom Γ ℂ) u
    (fun f => (s.count f : ℂ) - (t.count f : ℂ)) (by
      funext g
      have e := h g
      rw [key u s hs g, key u t ht g] at e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul,
        Finset.sum_sub_distrib]
      exact sub_eq_zero.2 e)
  ext f
  by_cases hf : f ∈ u
  · have := lin f hf
    exact_mod_cast sub_eq_zero.1 this
  · have h1 : f ∉ s := fun m => hf (hs (by simpa using m))
    have h2 : f ∉ t := fun m => hf (ht (by simpa using m))
    rw [Multiset.count_eq_zero.2 h1, Multiset.count_eq_zero.2 h2]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MatIrr
noncomputable def UpperTheory.Reformulated.B.Qf5.MatIrr.{u_1, u_2} :
    {G : Type u_1} →
      [inst : Group G] → {R : Type u_2} → [CommRing R] → {m : ℕ} → Subgroup G → (G → Matrix (Fin m) (Fin m) R) → Prop :=
    fun {G : Type u_1} [Group G] {R : Type u_2} [CommRing R] {m : ℕ} (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) R) ↦
      ∀ (W : Submodule R (Fin m → R)), (∀ g ∈ H, ∀ v ∈ W, (a g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤

theorem UpperTheory.Reformulated.B.Qf5.matIrr_conj :
    ∀ {G R : Type} [inst : Group G] [inst_1 : CommRing R] {m : ℕ} {U : Subgroup G} {a a' : G → Matrix (Fin m) (Fin m) R}
      (h : GL (Fin m) R),
      (∀ g ∈ U, a g = (↑h⁻¹ : Matrix (Fin m) (Fin m) R) * a' g * (↑h : Matrix (Fin m) (Fin m) R)) →
        UpperTheory.Reformulated.B.Qf5.MatIrr U a → UpperTheory.Reformulated.B.Qf5.MatIrr U a' := by
  intro G R _ _ m U a a' h hconj hirr W hW
  have hcancel : ∀ w : Fin m → R,
      (↑h : Matrix (Fin m) (Fin m) R).mulVec ((↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hmem : ∀ v : Fin m → R,
      v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) ↔
        (↑h : Matrix (Fin m) (Fin m) R).mulVec v ∈ W := fun v => Iff.rfl
  have hinv : ∀ g ∈ U, ∀ v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)),
      (a g).mulVec v ∈ W.comap (Matrix.mulVecLin (↑h : Matrix (Fin m) (Fin m) R)) := by
    intro g hg v hv
    rw [hmem] at hv ⊢
    rw [hconj g hg, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcancel]
    exact hW g hg _ hv
  rcases hirr _ hinv with hb | ht
  · left
    rw [Submodule.eq_bot_iff] at hb ⊢
    intro w hw
    have h0 := hb ((↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w) (by rw [hmem, hcancel]; exact hw)
    rw [← hcancel w, h0, Matrix.mulVec_zero]
  · right
    rw [Submodule.eq_top_iff'] at ht ⊢
    intro w
    have h1 := (hmem _).1 (ht ((↑h⁻¹ : Matrix (Fin m) (Fin m) R).mulVec w))
    rwa [hcancel] at h1
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfNear
namespace UpperTheory.Reformulated.B.S7

theorem eq_one_of_near {l : ℕ} [Fact l.Prime] {u : PadicAlgCl l} {m : ℕ} (hm : ¬ l ∣ m) (hu : u ^ m = 1)
    (h : ‖u - 1‖ < 1) : u = 1 := by
  by_contra hne
  have hu1 : ‖u‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (u - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le h.le le_rfl)
  have hpow : ∀ i : ℕ, ‖u ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : u ^ (i + 1) - 1 = (u ^ i - 1) * u + (u - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ h)
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hu1).trans_lt ih
  have hsum : ∀ n : ℕ, ‖(∑ i ∈ Finset.range n, u ^ i) - (n : PadicAlgCl l)‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : PadicAlgCl l)
          = ((∑ i ∈ Finset.range n, u ^ i) - (n : PadicAlgCl l)) + (u ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (hpow n))
  have h0 : (∑ i ∈ Finset.range m, u ^ i) = 0 := by
    have := geom_sum_mul u m
    rw [hu, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  have hlt := hsum m
  rw [h0, zero_sub, norm_neg] at hlt
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := by simp
  rw [e, norm_algebraMap'] at hlt
  exact hm (Padic.norm_natCast_lt_one_iff.mp hlt)

end UpperTheory.Reformulated.B.S7
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraBis
namespace UpperTheory.Reformulated.B.S8

theorem diag_mul {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) R) (hX : ∀ i j, j < i → X i j = 0)
    (hY : ∀ i j, j < i → Y i j = 0) (a : Fin n) : (X * Y) a a = X a a * Y a a := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single_of_mem a (Finset.mem_univ a) ?_
  intro b _ hb
  rcases lt_or_gt_of_ne hb with h | h
  · rw [hX a b h, zero_mul]
  · rw [hY b a h, mul_zero]

end UpperTheory.Reformulated.B.S8
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjugateSqrtNeg
theorem UpperTheory.Reformulated.B.ConjugateSqrtNeg.conj_sqrt_neg :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (d : ℕ) (x : E),
    (0 : ℕ) < d → x ^ (2 : ℕ) = -(↑d : E) → (NumberField.IsCMField.complexConj E : E → E) x = -x := by
  intro E _ _ _ d x hd hx
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : (NumberField.IsCMField.complexConj E x) ^ 2 = x ^ 2 := by
    rw [← map_pow, hx, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exfalso
    have h1 := NumberField.IsCMField.complexEmbedding_complexConj E φ x
    rw [h] at h1
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp h1.symm
    have h2 : (φ x) ^ 2 = -(d : ℂ) := by rw [← map_pow, hx, map_neg, map_natCast]
    rw [hr] at h2
    have h3 : r ^ 2 = -(d : ℝ) := by exact_mod_cast h2
    have h4 : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg r]
  · exact h
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraAlt
namespace UpperTheory.Reformulated.B.S6

theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  let v : Valuation (PadicAlgCl l) NNReal := NormedField.valuation
  have hmem : ∀ a : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) a ∈ v.integer := by
    intro a
    have h : ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
      exact a.2
    exact h
  let f : ℤ_[l] →+* v.integer := (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer hmem
  have hint : IsIntegral v.integer x := by
    obtain ⟨P, hP, hPx⟩ := hx
    refine ⟨P.map f, hP.map f, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hPx
  exact (Valuation.integer.integers v).mem_of_integral hint

end UpperTheory.Reformulated.B.S6
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CurveDVRPrecompleteFinite
theorem UpperTheory.Reformulated.B.PrecompleteOfFiniteOverAdicComplete.curveDVR_prec_finite :
    ∀ {O M : Type} [inst : CommRing O] [IsNoetherianRing O]
    (I : Ideal O) [IsAdicComplete I O] [inst_3 : AddCommGroup M] [inst_4 : _root_.Module O M] [Module.Finite O M],
    IsPrecomplete I M := by
  intro O M _ _ I _ _ _ _
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
  | tmul r m =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I O r
    refine ⟨a • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I O) a (AdicCompletion.of I M m)).symm
  | add x z hx hz =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultisetSeparation
open Polynomial in
private lemma eval_prod_add (m : Multiset ℂ) (u : ℂ) :
    (((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod).eval u
      = (m.map (fun x : ℂ ↦ u + x)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, eval_mul, ih, eval_sub, eval_X, eval_C]
    ring

theorem UpperTheory.Reformulated.B.MultisetSeparation.msetSep :
    ∀ (m m' : Multiset ℂ),
    (∀ (u : ℂ), (Multiset.map (fun (x : ℂ) ↦ u + x) m).prod = (Multiset.map (fun (x : ℂ) ↦ u + x) m').prod) → m = m' := by
  intro m m' h
  have hp : ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ Polynomial.X - Polynomial.C x)).prod
      = ((m'.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ Polynomial.X - Polynomial.C x)).prod := by
    apply Polynomial.funext
    intro u
    rw [eval_prod_add, eval_prod_add, h u]
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerTail
theorem UpperTheory.Reformulated.B.Qf13.pow_cong :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) {a b : Ω},
    (A.valuation : Ω → A.ValueGroup) a ≤ (1 : A.ValueGroup) →
      (A.valuation : Ω → A.ValueGroup) b ≤ (1 : A.ValueGroup) →
        (A.valuation : Ω → A.ValueGroup) (a - b) < (1 : A.ValueGroup) →
          ∀ (m : ℕ), (A.valuation : Ω → A.ValueGroup) (a ^ m - b ^ m) < (1 : A.ValueGroup) := by
  intro Ω _ A a b ha hb hab m
  induction m with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = (a ^ n - b ^ n) * a + (a - b) * b ^ n := by ring
    rw [e]
    refine A.valuation.map_add_lt ?_ ?_
    · rw [map_mul]
      calc A.valuation (a ^ n - b ^ n) * A.valuation a
          ≤ A.valuation (a ^ n - b ^ n) * 1 := by gcongr
        _ < 1 := by rwa [mul_one]
    · rw [map_mul, map_pow]
      have hb' : A.valuation b ^ n ≤ 1 := pow_le_one' hb n
      calc A.valuation (a - b) * A.valuation b ^ n
          ≤ A.valuation (a - b) * 1 := by gcongr
        _ < 1 := by rwa [mul_one]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeOfAddOneLeSucc
theorem UpperTheory.Reformulated.B.Qn14.le_of_add_one_le_succ :
    ∀ {a : WithBot ℕ∞} {k : ℕ},
    a + (1 : WithBot ℕ∞) ≤ (↑(k + (1 : ℕ)) : WithBot ℕ∞) → a ≤ (↑k : WithBot ℕ∞) := by
  intro a k h
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by
        rw [← WithBot.coe_le_coe]
        exact h
      rw [top_add, top_le_iff] at h1
      exact ENat.coe_ne_top _ h1
    | coe n =>
      have h1 : ((n : ℕ∞) + 1 : ℕ∞) ≤ ((k + 1 : ℕ) : ℕ∞) := by
        rw [← WithBot.coe_le_coe]
        exact h
      have h2 : n + 1 ≤ k + 1 := by exact_mod_cast h1
      have h3 : (n : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast (Nat.le_of_succ_le_succ h2)
      exact WithBot.coe_le_coe.mpr h3
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GlR
noncomputable def UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR :
    {K : Type} → [inst : CommRing K] → Subring K → (n : ℕ) → Subgroup (GL (Fin n) K) :=
  fun {K} _ R n =>
  { carrier := {g | (∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ R) ∧
      ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ R}
    one_mem' := by
      have h : ∀ i j : Fin n, (1 : Matrix (Fin n) (Fin n) K) i j ∈ R := fun i j => by
        rw [Matrix.one_apply]
        split_ifs
        exacts [R.one_mem, R.zero_mem]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [Units.val_one]
        exact h i j
      · rw [inv_one, Units.val_one]
        exact h i j
    mul_mem' := by
      rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · rw [Units.val_mul, Matrix.mul_apply]
        exact R.sum_mem fun k _ => R.mul_mem (ha i k) (hb k j)
      · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
        exact R.sum_mem fun k _ => R.mul_mem (hb' i k) (ha' k j)
    inv_mem' := by
      rintro a ⟨ha, ha'⟩
      refine ⟨ha', fun i j => ?_⟩
      rw [inv_inv]
      exact ha i j }
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherMore
theorem UpperTheory.Reformulated.B.Qk8.exists_place :
    ∀ {F : Type} [inst : Field F] [NumberField F] (p : ℕ),
    Nat.Prime p →
      ∃ (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
        (↑p : NumberField.RingOfIntegers F) ∈ w.asIdeal := by
  intro F _ _ p hp
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hinj : Function.Injective (algebraMap ℤ (NumberField.RingOfIntegers F)) :=
    (algebraMap ℤ (NumberField.RingOfIntegers F)).injective_int
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := NumberField.RingOfIntegers F) (Ideal.span {(p : ℤ)}) ⊥ (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have hx0 : x = 0 := hinj (by rw [hx, map_zero])
      rw [hx0]
      exact Ideal.zero_mem _)
  have hmem : (p : NumberField.RingOfIntegers F) ∈ Q := by
    have h : (p : ℤ) ∈ Q.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) := by
      change (p : ℤ) ∈ Ideal.under ℤ Q
      rw [hQP]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at h
    exact h
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  intro hbot
  rw [hbot, Ideal.mem_bot] at hmem
  exact hp.ne_zero (Nat.cast_eq_zero.mp hmem)
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqOneOfPowNear
theorem UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near :
    ∀ (z : ℂ),
    (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have step : ∀ n : ℕ, (3 / 2 : ℝ) * ‖z ^ n - 1‖ ≤ ‖z ^ (n * 2) - 1‖ := by
    intro n
    have e : z ^ (n * 2) - 1 = (z ^ n + 1) * (z ^ n - 1) := by ring
    have h1 : ‖(2 : ℂ)‖ ≤ ‖z ^ n + 1‖ + ‖z ^ n - 1‖ := by
      have e2 : (2 : ℂ) = (z ^ n + 1) - (z ^ n - 1) := by ring
      calc ‖(2 : ℂ)‖ = ‖(z ^ n + 1) - (z ^ n - 1)‖ := congrArg _ e2
        _ ≤ _ := norm_sub_le _ _
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have h3 := h n
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have grow : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have s := step (2 ^ k)
      rw [pow_succ, pow_succ]
      linarith
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ hpos] at hk
  have g := grow k
  have h4 := h (2 ^ k)
  linarith
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClearDenominatorsLattice
theorem UpperTheory.Reformulated.B.ClearDenominatorsLattice.exists_integer_smul_mem_of_span_top :
    ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    Submodule.span K (↑L : Set V) = ⊤ →
      ∀ (x : V), ∃ (r : NumberField.RingOfIntegers K), r ≠ (0 : NumberField.RingOfIntegers K) ∧ r • x ∈ L := by
  intro K V _ _ _ _ _ _ L hL x
  have hx : x ∈ Submodule.span K (↑L : Set V) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨s, hs, hsz⟩ := hz
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hry
    · rw [mul_smul]
      exact L.smul_mem _ hsz
  | smul a y _ hy =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨⟨n, d⟩, hnd⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    refine ⟨r * d, mul_ne_zero hr (nonZeroDivisors.ne_zero d.2), ?_⟩
    have h1 : (d : NumberField.RingOfIntegers K) • (a • y) = n • y := by
      rw [← algebraMap_smul K (d : NumberField.RingOfIntegers K) (a • y), ← mul_smul, mul_comm,
        hnd, algebraMap_smul]
    rw [mul_smul, h1, ← mul_smul, mul_comm, mul_smul]
    exact L.smul_mem _ hry
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterContinuous
@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G E Ω →* (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)).comp
        (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cont_cyc :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycBar F Ω l) : UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.G F Ω → (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous (fun x : ℤ_[l] ↦ algebraMap ℚ_[l] (PadicAlgCl l) (x : ℚ_[l])) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AbsoluteValueAltAlt
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InfiniteNormOneElements
theorem UpperTheory.infinite_norm_one_elements :
    ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
        {t : E | t * σ t = 1}.Infinite := by
  intro F E _ _ _ _ σ hE hσ
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
  have hw : ¬ NumberField.ComplexEmbedding.IsReal w.embedding :=
    NumberField.InfinitePlace.isComplex_iff.mp (hE.isComplex w)
  generalize w.embedding = τ at hw
  have hinv : ∀ x : E, σ (σ x) = x := fun x =>
    τ.injective (by rw [hσ, hσ, star_star])
  obtain ⟨a, ha⟩ : ∃ a : E, σ a ≠ a := by
    by_contra h
    push Not at h
    apply hw
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have := hσ τ x
    rw [h] at this
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    exact this.symm
  have h1 : ∀ n : ℕ, (n : E) + a ≠ 0 := by
    intro n hn
    apply ha
    have : a = -(n : E) := by linear_combination hn
    rw [this, map_neg, map_natCast]
  have h2 : ∀ n : ℕ, (n : E) + σ a ≠ 0 := by
    intro n hn
    apply h1 n
    have := congrArg σ hn
    rwa [map_add, map_natCast, hinv, map_zero] at this
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((n : E) + a) / ((n : E) + σ a)) ?_ ?_
  · intro m n hmn
    have h3 := (div_eq_div_iff (h2 m) (h2 n)).mp hmn
    have h4 : ((m : E) - n) * (σ a - a) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact Nat.cast_injective (R := E) (sub_eq_zero.mp h)
    · exact absurd (sub_eq_zero.mp h) ha
  · intro n
    show _ * σ _ = 1
    rw [map_div₀, map_add (f := _), map_add (f := _), map_natCast, hinv, div_mul_div_cancel₀ (h2 n), div_self (h1 n)]
end

theorem UpperTheory.Reformulated.B.CapelliAbsoluteValue.abs : ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
    {t : E | t * σ t = 1}.Infinite :=
  UpperTheory.infinite_norm_one_elements
end
