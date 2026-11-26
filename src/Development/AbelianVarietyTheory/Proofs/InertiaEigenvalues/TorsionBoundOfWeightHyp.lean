module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordEquivariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentDevissageCommRing
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open Filter Topology

namespace GlobalTheory

theorem continuous_adicModule_span_iff {R M G : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace G] (a : R) (f : G → M) :
    @Continuous G M _ ((Ideal.span {a}).adicModuleTopology M) f ↔
      ∀ (g₀ : G) (n : ℕ), ∀ᶠ g in 𝓝 g₀, ∃ y : M, f g = f g₀ + a ^ n • y := by
  letI : TopologicalSpace M := (Ideal.span {a}).adicModuleTopology M
  have hmem : ∀ (n : ℕ) (x : M), x ∈ ((Ideal.span {a}) ^ n • (⊤ : Submodule R M)) ↔
      ∃ y : M, a ^ n • y = x := by
    intro n x
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hb := fun x₀ : M => (@ModuleFilterBasis.toAddGroupFilterBasis R M _
    (Ideal.span {a}).adic_basis.topology _ _
    ((Ideal.span {a}).ringFilterBasis.moduleFilterBasis
      ((Ideal.span {a}).adic_module_basis M))).nhds_hasBasis x₀
  rw [continuous_iff_continuousAt]
  refine forall_congr' fun g₀ => ?_
  refine ((hb (f g₀)).tendsto_right_iff).trans ?_
  constructor
  · intro h n
    filter_upwards [h _ ⟨n, rfl⟩] with g hg
    obtain ⟨y, hy, hy'⟩ := hg
    obtain ⟨z, rfl⟩ := (hmem n y).1 hy
    exact ⟨z, hy'.symm⟩
  · rintro h _ ⟨n, rfl⟩
    filter_upwards [h n] with g hg
    obtain ⟨z, hz⟩ := hg
    exact ⟨a ^ n • z, (hmem n _).2 ⟨z, rfl⟩, hz.symm⟩

theorem torsionExponent_devissage_commRing {R G X X' X'' : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R X'] [AddCommGroup X''] [Module R X'']
    (a : R) (htf : ∀ (n : ℕ) (z : X''), a ^ n • z = 0 → z = 0)
    (ρ : Representation R G X) (ρ' : Representation R G X') (ρ'' : Representation R G X'')
    (i : X' →ₗ[R] X) (p : X →ₗ[R] X'') (r' r'' : R)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (hiρ : ∀ g x, i (ρ' g x) = ρ g (i x)) (hpρ : ∀ g x, p (ρ g x) = ρ'' g (p x))
    (hc : ∀ x, @Continuous G X _ ((Ideal.span {a}).adicModuleTopology X) fun g => ρ g x)
    (h0 : ∀ z, (∀ g, ρ'' g z = z) → ∃ (k : ℕ) (x : X), (∀ g, ρ g x = x) ∧ p x = a ^ k • z)
    (h' : @TorsKilledBy R G X' _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X') ρ' a r')
    (h'' : @TorsKilledBy R G X'' _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X'') ρ'' a r'') :
    @TorsKilledBy R G X _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X) ρ a (r' * r'') := by
  rintro f ⟨hfc, hf⟩ ⟨k, x, hx⟩
  rw [continuous_adicModule_span_iff] at hfc
  simp only [Pi.smul_apply] at hx

  obtain ⟨z'', hz''⟩ := h'' (fun g => p (f g)) ⟨by
      rw [continuous_adicModule_span_iff]
      intro g₀ n
      filter_upwards [hfc g₀ n] with g hg
      obtain ⟨y, hy⟩ := hg
      exact ⟨p y, by rw [hy, map_add (f := _), map_smul]⟩,
    fun g h => by simp only [hf, map_add (f := _), hpρ]⟩
    ⟨k, p x, fun g => by rw [Pi.smul_apply, ← map_smul, hx, map_sub, hpρ]⟩
  obtain ⟨z, rfl⟩ := hp z''
  simp only [Pi.smul_apply] at hz''
  have hex' : ∀ g, ∃ y, i y = r'' • f g - (ρ g z - z) := fun g =>
    (hex _).1 (by rw [map_sub, map_smul, hz'', map_sub, hpρ, sub_self])
  choose f' hf' using hex'
  have hcoc : @IsCoc R G X' _ _ _ _ _ ((Ideal.span {a}).adicModuleTopology X') ρ' f' := by
    refine ⟨?_, fun g h => hi ?_⟩
    · rw [continuous_adicModule_span_iff]
      intro g₀ n
      filter_upwards [hfc g₀ n, (continuous_adicModule_span_iff a _).1 (hc z) g₀ n] with g hg hg'
      obtain ⟨y, hy⟩ := hg
      obtain ⟨w, hw⟩ := hg'
      have h1 : i (f' g) = i (f' g₀) + a ^ n • (r'' • y - w) := by
        rw [hf', hf', hy, hw]; module
      have h2 : p (r'' • y - w) = 0 := by
        apply htf n
        have := congrArg p h1
        rwa [map_add, hex.apply_apply_eq_zero, hex.apply_apply_eq_zero, zero_add, map_smul,
          eq_comm] at this
      obtain ⟨u, hu⟩ := (hex _).1 h2
      exact ⟨u, hi (by rw [h1, map_add (f := _), map_smul, hu])⟩
    · rw [map_add (f := _), hiρ, hf', hf', hf', hf, map_mul]
      simp only [Module.End.mul_apply, map_sub, map_smul]
      module

  have hw : ∀ g, i (a ^ k • f' g) = ρ g (r'' • x - a ^ k • z) - (r'' • x - a ^ k • z) := by
    intro g
    rw [map_smul, hf', smul_sub, smul_comm, hx]
    simp only [map_sub, map_smul]
    module
  obtain ⟨k', x₀, hx₀, hpx₀⟩ := h0 (p (r'' • x - a ^ k • z)) (fun g => by
    rw [← hpρ, ← sub_eq_zero, ← map_sub, ← hw, hex.apply_apply_eq_zero])
  obtain ⟨w', hw'⟩ := (hex (a ^ k' • (r'' • x - a ^ k • z) - x₀)).1
    (by rw [map_sub, map_smul, hpx₀, sub_self])
  obtain ⟨u, hu⟩ := h' f' hcoc ⟨k' + k, w', fun g => hi (by
    rw [Pi.smul_apply, pow_add, mul_smul, map_smul, hw, map_sub i, hiρ, hw', map_sub (ρ g) _ x₀,
      hx₀, map_smul (ρ g) (a ^ k')]
    module)⟩
  refine ⟨i u + r' • z, fun g => ?_⟩
  have := congrArg i (hu g)
  rw [Pi.smul_apply, map_smul, hf', map_sub, hiρ] at this
  rw [Pi.smul_apply, map_add (f := _), map_smul]
  linear_combination (norm := module) this

theorem torsKilledBy_devissage : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [NoZeroSMulDivisors ℤ_[l] X] [IsAdicComplete (Ideal.span {(l : ℤ_[l])}) X] (X' : Type) [AddCommGroup X'] [Module ℤ_[l] X'] [NoZeroSMulDivisors ℤ_[l] X'] [IsAdicComplete (Ideal.span {(l : ℤ_[l])}) X'] (X'' : Type) [AddCommGroup X''] [Module ℤ_[l] X''] [NoZeroSMulDivisors ℤ_[l] X''] [IsAdicComplete (Ideal.span {(l : ℤ_[l])}) X''] (ρ : Representation ℤ_[l] G X) (ρ' : Representation ℤ_[l] G X') (ρ'' : Representation ℤ_[l] G X'') (i : X' →ₗ[ℤ_[l]] X) (p : X →ₗ[ℤ_[l]] X'') (c' c'' : ℕ), letI : TopologicalSpace X := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology X; letI : TopologicalSpace X' := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology X'; letI : TopologicalSpace X'' := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology X''; Function.Injective i → Function.Surjective p → Function.Exact i p → (∀ g x, i (ρ' g x) = ρ g (i x)) → (∀ g x, p (ρ g x) = ρ'' g (p x)) → (∀ x, Continuous fun g => ρ g x) → (∀ z, (∀ g, ρ'' g z = z) → ∃ (k : ℕ) (x : X), (∀ g, ρ g x = x) ∧ p x = (l : ℤ_[l]) ^ k • z) → TorsKilledBy ρ' (l : ℤ_[l]) ((l : ℤ_[l]) ^ c') → TorsKilledBy ρ'' (l : ℤ_[l]) ((l : ℤ_[l]) ^ c'') → TorsKilledBy ρ (l : ℤ_[l]) ((l : ℤ_[l]) ^ (c' + c'')) := by
  intro l _ G _ _ _ _ _ X _ _ _ _ X' _ _ _ _ X'' _ _ _ _ ρ ρ' ρ'' i p c' c''
  intro hi hp hex hiρ hpρ hc h0 h' h''
  rw [pow_add]
  refine torsionExponent_devissage_commRing (l : ℤ_[l]) ?_ ρ ρ' ρ'' i p _ _ hi hp hex hiρ hpρ hc h0 h' h''
  intro n z hz
  have hl : ((l : ℤ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  exact (NoZeroSMulDivisors.eq_zero_or_eq_zero_of_smul_eq_zero hz).resolve_left hl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorQuotientTorsionFreeComplete
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

noncomputable section

namespace GlobalTheory.XiQuotient

section Algebra

variable {R : Type} [CommRing R] (π : R)

theorem smodEq_iff {M : Type} [AddCommGroup M] [Module R M] (n : ℕ) (x y : M) :
    x ≡ y [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule R M)] ↔ ∃ z : M, π ^ n • z = x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem isAdicComplete_iff {M : Type} [AddCommGroup M] [Module R M] :
    IsAdicComplete (Ideal.span {π}) M ↔
      (∀ x : M, (∀ n : ℕ, ∃ z : M, π ^ n • z = x) → x = 0) ∧
      ∀ u : ℕ → M, (∀ n : ℕ, ∃ z : M, π ^ n • z = u n - u (n + 1)) →
        ∃ L : M, ∀ n : ℕ, ∃ z : M, π ^ n • z = u n - L := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun u hu => ?_⟩
    · refine h.toIsHausdorff.haus x fun n => ?_
      rw [smodEq_iff, sub_zero]
      exact hx n
    · have hc : ∀ {m n : ℕ}, m ≤ n →
          u m ≡ u n [SMOD (Ideal.span {π} ^ m • ⊤ : Submodule R M)] := by
        intro m n hmn
        rw [smodEq_iff]
        induction n, hmn using Nat.le_induction with
        | base => exact ⟨0, by simp⟩
        | succ k hk ih =>
          obtain ⟨z, hz⟩ := ih
          obtain ⟨w, hw⟩ := hu k
          refine ⟨z + π ^ (k - m) • w, ?_⟩
          rw [smul_add, smul_smul, ← pow_add, Nat.add_sub_cancel' hk, hz, hw]
          abel
      obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec hc
      exact ⟨L, fun n => (smodEq_iff π n _ _).1 (hL n)⟩
  · rintro ⟨h1, h2⟩
    haveI : IsHausdorff (Ideal.span {π}) M := ⟨fun x hx => h1 x fun n => by
      simpa using (smodEq_iff π n _ _).1 (hx n)⟩
    haveI : IsPrecomplete (Ideal.span {π}) M := ⟨fun u hu => by
      obtain ⟨L, hL⟩ := h2 u fun n => (smodEq_iff π n _ _).1 (hu (Nat.le_succ n))
      exact ⟨L, fun n => (smodEq_iff π n _ _).2 (hL n)⟩⟩
    exact ⟨⟩

theorem isAdicComplete_coker {A Q : Type} [AddCommGroup A] [Module R A] [AddCommGroup Q]
    [Module R Q] (hA : IsAdicComplete (Ideal.span {π}) A) (hπ : ∀ x : A, π • x = 0 → x = 0)
    (f : A →ₗ[R] A) (g : A →ₗ[R] Q) (hg : Function.Surjective g)
    (hfg : ∀ x, g x = 0 ↔ ∃ y, f y = x)
    (hreg : ∀ x y : A, π • x = f y → ∃ y', y = π • y') :
    (∀ q : Q, π • q = 0 → q = 0) ∧ IsAdicComplete (Ideal.span {π}) Q := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_iff π).1 hA
  have hstep : ∀ x y : A, π • x = f y → ∃ y', y = π • y' ∧ x = f y' := by
    intro x y h
    obtain ⟨y', rfl⟩ := hreg x y h
    refine ⟨y', rfl, sub_eq_zero.1 (hπ _ ?_)⟩
    rw [smul_sub, h, map_smul, sub_self]
  have hpow : ∀ (n : ℕ) (x y : A), π ^ n • x = f y → ∃ y', π ^ n • y' = y := by
    intro n
    induction n with
    | zero => intro x y _; exact ⟨y, by simp⟩
    | succ n ih =>
      intro x y h
      rw [pow_succ', mul_smul] at h
      obtain ⟨y', rfl, h'⟩ := hstep _ _ h
      obtain ⟨y'', rfl⟩ := ih _ _ h'
      exact ⟨y'', by rw [pow_succ', mul_smul]⟩
  refine ⟨fun q hq => ?_, (isAdicComplete_iff π).2 ⟨fun q hq => ?_, fun u hu => ?_⟩⟩
  · obtain ⟨x, rfl⟩ := hg q
    rw [← map_smul, hfg] at hq
    obtain ⟨y, hy⟩ := hq
    obtain ⟨y', -, h⟩ := hstep _ _ hy.symm
    exact (hfg x).2 ⟨y', h.symm⟩
  · obtain ⟨x, rfl⟩ := hg q
    have : ∀ n : ℕ, ∃ y z : A, f y = x - π ^ n • z := by
      intro n
      obtain ⟨w, hw⟩ := hq n
      obtain ⟨z, rfl⟩ := hg w
      obtain ⟨y, hy⟩ := (hfg (x - π ^ n • z)).1 (by rw [map_sub, map_smul, hw, sub_self])
      exact ⟨y, z, hy⟩
    choose y z hyz using this
    obtain ⟨L, hL⟩ := h2 y fun n => hpow n (π • z (n + 1) - z n) _ (by
      rw [map_sub, hyz, hyz, smul_sub, smul_smul, ← pow_succ]; abel)
    refine (hfg x).2 ⟨L, (sub_eq_zero.1 (h1 _ fun n => ?_)).symm⟩
    obtain ⟨w, hw⟩ := hL n
    refine ⟨z n + f w, ?_⟩
    rw [smul_add, ← map_smul, hw, map_sub, hyz]
    abel
  · choose z hz using hu
    choose z' hz' using fun n => hg (z n)
    obtain ⟨x₀, hx₀⟩ := hg (u 0)
    let x : ℕ → A := fun n => x₀ - ∑ i ∈ Finset.range n, π ^ i • z' i
    have hx : ∀ n, g (x n) = u n := by
      intro n
      induction n with
      | zero => simp [x, hx₀]
      | succ n ih =>
        have : x (n + 1) = x n - π ^ n • z' n := by
          simp only [x, Finset.sum_range_succ]; abel
        rw [this, map_sub, ih, map_smul, hz', hz]
        abel
    obtain ⟨L, hL⟩ := h2 x fun n => ⟨z' n, by simp only [x, Finset.sum_range_succ]; abel⟩
    refine ⟨g L, fun n => ?_⟩
    obtain ⟨w, hw⟩ := hL n
    exact ⟨g w, by rw [← map_smul, hw, map_sub, hx]⟩

theorem isAdicComplete_of_equiv_pi {ι Q M : Type} [AddCommGroup Q] [Module R Q] [AddCommGroup M]
    [Module R M] (hQ : IsAdicComplete (Ideal.span {π}) Q) (e : M ≃ₗ[R] (ι → Q)) :
    IsAdicComplete (Ideal.span {π}) M := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_iff π).1 hQ
  refine (isAdicComplete_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · apply e.injective
    rw [map_zero]
    funext i
    refine h1 _ fun n => ?_
    obtain ⟨z, hz⟩ := hx n
    exact ⟨e z i, by rw [← hz, map_smul]; rfl⟩
  · have : ∀ i, ∃ L : Q, ∀ n : ℕ, ∃ z : Q, π ^ n • z = e (u n) i - L := by
      intro i
      refine h2 (fun n => e (u n) i) fun n => ?_
      obtain ⟨z, hz⟩ := hu n
      refine ⟨e z i, ?_⟩
      have := congrFun (congrArg e hz) i
      rw [map_smul, map_sub] at this
      exact this
    choose L z hz using this
    refine ⟨e.symm L, fun n => ⟨e.symm (fun i => z i n), ?_⟩⟩
    apply e.injective
    rw [map_smul, map_sub, e.apply_symm_apply, e.apply_symm_apply]
    funext i
    exact hz i n

end Algebra

theorem noZeroSMulDivisors_of_prime {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M]
    [Module ℤ_[l] M] (h : ∀ x : M, (l : ℤ_[l]) • x = 0 → x = 0) : NoZeroSMulDivisors ℤ_[l] M := by
  have hpow : ∀ (n : ℕ) (x : M), (l : ℤ_[l]) ^ n • x = 0 → x = 0 := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ, mul_smul] at hx
      exact h x (ih _ hx)
  refine ⟨fun {c x} hcx => ?_⟩
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    rw [PadicInt.unitCoeff_spec hc, mul_comm, mul_smul] at hcx
    have := hpow _ _ hcx
    rwa [← Units.smul_def, smul_eq_zero_iff_eq] at this

section Ainf

variable {l : ℕ} [Fact l.Prime]

theorem smul_l (x : Ainf l) : (l : ℤ_[l]) • x = (l : Ainf l) * x := by
  rw [Algebra.smul_def, map_natCast]

theorem ainf_complete : IsAdicComplete (Ideal.span {(l : ℤ_[l])}) (Ainf l) := by
  have h : IsAdicComplete (Ideal.span {(l : Ainf l)}) (Ainf l) := inferInstance
  rw [← IsAdicComplete.map_algebraMap_iff (S := Ainf l), Ideal.map_span, Set.image_singleton,
    map_natCast]
  exact h

theorem inclW_injective : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

variable {P : LocPrime l} (AI : LocAinf l P)

theorem xi_coeff_ne_zero : WittVector.constantCoeff AI.ξ ≠ 0 := by
  intro h
  have hu := AI.isUnit_inclW_ξ.map (WittVector.constantCoeff : WCb l →+* Cb l)
  apply hu.ne_zero
  change (inclW l AI.ξ).coeff 0 = 0
  rw [inclW, WittVector.map_coeff]
  change algebraMap (OCb l) (Cb l) (WittVector.constantCoeff AI.ξ) = 0
  rw [h, map_zero]

theorem xi_pow_regular (k : ℕ) (x y : Ainf l) (h : (l : ℤ_[l]) • x = AI.ξ ^ k * y) :
    ∃ y', y = (l : ℤ_[l]) • y' := by
  rw [smul_l] at h
  have h0 := congrArg (WittVector.constantCoeff : Ainf l →+* OCb l) h
  rw [map_mul, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, map_pow] at h0
  have hy : y.coeff 0 = 0 :=
    (mul_eq_zero.1 h0.symm).resolve_left (pow_ne_zero k (xi_coeff_ne_zero AI))
  rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero, Ideal.mem_span_singleton'] at hy
  obtain ⟨y', rfl⟩ := hy
  exact ⟨y', by rw [smul_l, mul_comm]⟩

def toMxi (a : ℤ) : Ainf l →ₗ[ℤ_[l]] Mxi (AinfSub l) (xiU AI) a :=
  LinearMap.codRestrict _
    ((LinearMap.mulLeft ℤ_[l] ((xiU AI ^ a : (WCb l)ˣ) : WCb l)) ∘ₗ (inclWA l).toLinearMap)
    fun x => ⟨inclWA l x, ⟨x, rfl⟩, rfl⟩

theorem toMxi_val (a : ℤ) (x : Ainf l) :
    (toMxi AI a x : WCb l) = ((xiU AI ^ a : (WCb l)ˣ) : WCb l) * inclW l x := rfl

theorem toMxi_surjective (a : ℤ) : Function.Surjective (toMxi AI a) := by
  rintro ⟨_, _, ⟨x, rfl⟩, rfl⟩
  exact ⟨x, rfl⟩

theorem quotient_complete (a b : ℤ) (hab : a ≤ b) :
    (∀ q : Qab (AinfSub l) (xiU AI) a b, (l : ℤ_[l]) • q = 0 → q = 0) ∧
      IsAdicComplete (Ideal.span {(l : ℤ_[l])}) (Qab (AinfSub l) (xiU AI) a b) := by
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le hab
  have hk : ∀ y : Ainf l, ((xiU AI ^ (a + k) : (WCb l)ˣ) : WCb l) * inclW l y =
      ((xiU AI ^ a : (WCb l)ˣ) : WCb l) * inclW l (AI.ξ ^ k * y) := by
    intro y
    rw [zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val, map_mul, map_pow, mul_assoc]
    rfl
  refine isAdicComplete_coker (l : ℤ_[l]) ainf_complete ?_ (LinearMap.mulLeft ℤ_[l] (AI.ξ ^ k))
    ((Submodule.mkQ _) ∘ₗ toMxi AI a)
    ((Submodule.mkQ_surjective _).comp (toMxi_surjective AI a)) ?_ (xi_pow_regular AI k)
  · intro x hx
    rw [smul_l, mul_comm] at hx
    exact WittVector.eq_zero_of_p_mul_eq_zero x hx
  · intro x
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.subtype_apply, toMxi_val]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, hy⟩
      refine ⟨y, inclW_injective ?_⟩
      have hy' : ((xiU AI ^ (a + k) : (WCb l)ˣ) : WCb l) * inclW l y =
          ((xiU AI ^ a : (WCb l)ˣ) : WCb l) * inclW l x := hy
      rw [hk] at hy'
      exact (Units.mul_right_inj _).1 hy'
    · rintro ⟨y, rfl⟩
      exact ⟨inclW l y, ⟨y, rfl⟩, hk y⟩

end Ainf

theorem tensor_quotient_torsionFree_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (AI : LocAinf l P) (a b : ℤ), a ≤ b → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T]
    [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T],
    NoZeroSMulDivisors ℤ_[l] (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b)) ∧
      IsAdicComplete (Ideal.span {(l : ℤ_[l])})
        (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b)) := by
  intro l _ P AI a b hab T _ _ _ _
  classical
  obtain ⟨h1, h2⟩ := quotient_complete AI a b hab
  let β := Module.Free.chooseBasis ℤ_[l] T
  let e : TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b) ≃ₗ[ℤ_[l]]
      (Module.Free.ChooseBasisIndex ℤ_[l] T → Qab (AinfSub l) (xiU AI) a b) :=
    (TensorProduct.comm ℤ_[l] _ _).trans
      ((TensorProduct.congr (LinearEquiv.refl ℤ_[l] _) β.equivFun).trans
        (TensorProduct.piScalarRight ℤ_[l] ℤ_[l] _ _))
  refine ⟨noZeroSMulDivisors_of_prime fun x hx => ?_, isAdicComplete_of_equiv_pi _ h2 e⟩
  apply e.injective
  rw [map_zero]
  funext i
  apply h1
  have := congrFun (congrArg e hx) i
  rw [map_smul, map_zero] at this
  exact this

end GlobalTheory.XiQuotient
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionBoundOfWeightHyp
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

noncomputable section

namespace GlobalTheory.TorsLL

section Maps

variable {O G WC : Type} [CommRing O] [Group G] [CommRing WC] [Algebra O WC]
  {AA : Subalgebra O WC} {act : G →* (WC ≃ₐ[O] WC)} {ξ : WCˣ}

def iQ {a e : ℤ} (b : ℤ) (hae : Mxi AA ξ e ≤ Mxi AA ξ a) : Qab AA ξ e b →ₗ[O] Qab AA ξ a b :=
  Submodule.mapQ _ _ (Submodule.inclusion hae) (fun _ hx => hx)

def pQ (a : ℤ) {e b : ℤ} (heb : Mxi AA ξ b ≤ Mxi AA ξ e) : Qab AA ξ a b →ₗ[O] Qab AA ξ a e :=
  Submodule.mapQ _ _ LinearMap.id (fun _ hx => heb hx)

theorem iQ_injective {a e : ℤ} (b : ℤ) (hae : Mxi AA ξ e ≤ Mxi AA ξ a) :
    Function.Injective (iQ b hae) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx' : (Submodule.Quotient.mk (Submodule.inclusion hae y) : Qab AA ξ a b) = 0 := hx
  rw [Submodule.Quotient.mk_eq_zero] at hx' ⊢
  exact hx'

theorem pQ_surjective (a : ℤ) {e b : ℤ} (heb : Mxi AA ξ b ≤ Mxi AA ξ e) :
    Function.Surjective (pQ a heb) := by
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Submodule.Quotient.mk y, rfl⟩

theorem exact_iQ_pQ {a e b : ℤ} (hae : Mxi AA ξ e ≤ Mxi AA ξ a) (heb : Mxi AA ξ b ≤ Mxi AA ξ e) :
    Function.Exact (iQ b hae) (pQ a heb) := by
  intro x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  constructor
  · intro hx
    rw [pQ, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    exact ⟨Submodule.Quotient.mk ⟨y.1, hx⟩, rfl⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [← hz]
    change (Submodule.Quotient.mk (Submodule.inclusion hae w) : Qab AA ξ a e) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact w.2

variable {T : Type} [AddCommGroup T] [Module O T] (ρT : G →* (T →ₗ[O] T)) (h : XiOK AA act ξ)

theorem iQ_equiv {a e : ℤ} (b : ℤ) (hae : Mxi AA ξ e ≤ Mxi AA ξ a) (g : G)
    (x : TensorProduct O T (Qab AA ξ e b)) :
    LinearMap.lTensor T (iQ b hae) (repX ρT h e b g x) =
      repX ρT h a b g (LinearMap.lTensor T (iQ b hae) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t q =>
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem pQ_equiv (a : ℤ) {e b : ℤ} (heb : Mxi AA ξ b ≤ Mxi AA ξ e) (g : G)
    (x : TensorProduct O T (Qab AA ξ a b)) :
    LinearMap.lTensor T (pQ a heb) (repX ρT h a b g x) =
      repX ρT h a e g (LinearMap.lTensor T (pQ a heb) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t q =>
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem repX_res {G' : Type} [Group G'] (φ : G' →* G) (act' : G' →* (WC ≃ₐ[O] WC))
    (hact : ∀ g, act' g = act (φ g)) (ρ' : G' →* (T →ₗ[O] T)) (hρ : ∀ g, ρ' g = ρT (φ g))
    (h' : XiOK AA act' ξ) (a b : ℤ) (g : G') : repX ρ' h' a b g = repX ρT h a b (φ g) := by
  obtain rfl : act' = act.comp φ := MonoidHom.ext hact
  obtain rfl : ρ' = ρT.comp φ := MonoidHom.ext hρ
  rfl

end Maps

theorem tors_of_subgroup {R Γ X : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup X]
    [Module R X] [TopologicalSpace X] (G H : Subgroup Γ) (hHG : H ≤ G) (ρ : Representation R G X)
    (ρ' : Representation R H X) (hρ : ∀ g : H, ρ' g = ρ (Subgroup.inclusion hHG g)) (l v c : ℕ)
    (hl : l ≠ 0) (hidx : H.relIndex G = l ^ v) (hT : TorsKilledBy ρ' (l : R) ((l : R) ^ c)) :
    TorsKilledBy ρ (l : R) ((l : R) ^ (v + c)) := by
  rintro f ⟨hfc, hf⟩ ⟨k, x, hx⟩
  have hcont : Continuous (Subgroup.inclusion hHG) :=
    Continuous.subtype_mk continuous_subtype_val _
  obtain ⟨y, hy⟩ := hT (fun g => f (Subgroup.inclusion hHG g))
    ⟨hfc.comp hcont, fun g g' => by simp only [map_mul, hf, hρ]⟩
    ⟨k, x, fun g => by rw [hρ, ← hx]; rfl⟩
  have : (H.subgroupOf G).FiniteIndex := ⟨by
    change H.relIndex G ≠ 0
    rw [hidx]; exact pow_ne_zero _ hl⟩
  obtain ⟨z, hz⟩ := GlobalTheory.index_smul_cocycle_eq_coboundary R G X ρ (H.subgroupOf G) ((l : R) ^ c • f)
    (fun g g' => by simp only [Pi.smul_apply, hf, smul_add, map_smul])
    ⟨y, fun g hg => by
      have := hy ⟨g.1, hg⟩
      rw [hρ] at this
      exact this⟩
  refine ⟨z, fun g => ?_⟩
  rw [← hz g]
  change _ = H.relIndex G • _
  rw [hidx, ← Nat.cast_smul_eq_nsmul R, Pi.smul_apply, Pi.smul_apply, smul_smul, pow_add, Nat.cast_pow]

theorem tors_repX {O Γ WC : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing WC]
    [Algebra O WC] {AA : Subalgebra O WC} {act : Γ →* (WC ≃ₐ[O] WC)} {ξ : WCˣ} (G H : Subgroup Γ)
    (hHG : H ≤ G) {T : Type} [AddCommGroup T] [Module O T] (ρ : ↥G →* (T →ₗ[O] T))
    (ρ' : ↥H →* (T →ₗ[O] T)) (hρ : ∀ g, ρ' g = ρ (Subgroup.inclusion hHG g))
    (hG : XiOK AA (act.comp G.subtype) ξ) (hH : XiOK AA (act.comp H.subtype) ξ) (a b : ℤ)
    [TopologicalSpace (TensorProduct O T (Qab AA ξ a b))] (l v c : ℕ)
    (hl : l ≠ 0) (hidx : H.relIndex G = l ^ v)
    (hT : TorsKilledBy (repX ρ' hH a b) (l : O) ((l : O) ^ c)) :
    TorsKilledBy (repX ρ hG a b) (l : O) ((l : O) ^ (v + c)) :=
  tors_of_subgroup G H hHG _ _
    (fun g => repX_res ρ hG (Subgroup.inclusion hHG) _ (fun _ => rfl) ρ' hρ hH a b g) l v c hl hidx hT

theorem comp_inclusion {Γ M : Type} [Group Γ] [Monoid M] {L G H : Subgroup Γ} (hHG : H ≤ G)
    (hG : G ≤ L) (hH : H ≤ L) (ρ : ↥L →* M) (g : ↥H) :
    (ρ.comp (Subgroup.inclusion hH)) g = (ρ.comp (Subgroup.inclusion hG)) (Subgroup.inclusion hHG g) :=
  rfl

variable {l : ℕ} [Fact l.Prime]

theorem tors_repQ {P : LocPrime l} (AI : LocAinf l P) (G H : Subgroup (GQ l))
    (hHG : H ≤ G) {T : Type} [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥G →* (T →ₗ[ℤ_[l]] T))
    (ρ' : ↥H →* (T →ₗ[ℤ_[l]] T)) (hρ : ∀ g, ρ' g = ρ (Subgroup.inclusion hHG g)) (a b : ℤ)
    [TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b))] (v c : ℕ)
    (hidx : H.relIndex G = l ^ v)
    (hT : TorsKilledBy (repQ AI H ρ' a b) (l : ℤ_[l]) ((l : ℤ_[l]) ^ c)) :
    TorsKilledBy (repQ AI G ρ a b) (l : ℤ_[l]) ((l : ℤ_[l]) ^ (v + c)) := by
  unfold repQ at hT ⊢
  exact tors_repX G H hHG ρ ρ' hρ _ _ a b l v c (Fact.out : l.Prime).ne_zero hidx hT

theorem Gj_anti (K : FinExt l) {i j : ℕ} (hij : i ≤ j) : Gj K j ≤ Gj K i := by
  refine IntermediateField.fixingSubgroup_le (sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _)
  intro x hx
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  change x ^ l ^ i = 1 at hx
  change x ^ l ^ (i + k) = 1
  rw [pow_add, pow_mul, hx, one_pow]

theorem compact_Gj (K : FinExt l) (j : ℕ) : CompactSpace ↥(Gj K j) :=
  isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed (Ks K j)).isCompact

theorem finrank_cyclotomicTowerBase_ne_zero (K : FinExt l) : Module.finrank ℚ_[l] ↥(K0 K) ≠ 0 := by
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  exact Module.finrank_pos.ne'

theorem deg_Ks (K : FinExt l) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    Module.finrank ℚ_[l] ↥(Ks K j) = l ^ (j - i) * Module.finrank ℚ_[l] ↥(Ks K i) ∧
      Module.finrank ℚ_[l] ↥(Ks K i) ≠ 0 := by
  have hl : l.Prime := Fact.out
  have h1 := (finrank_Ks_and_chi_surjective l K).1
  rw [h1 j (hi.trans hij), h1 i hi]
  refine ⟨?_, mul_ne_zero (finrank_cyclotomicTowerBase_ne_zero K) (mul_ne_zero ?_ (pow_ne_zero _ hl.ne_zero))⟩
  · have : j - 1 = (j - i) + (i - 1) := by omega
    rw [this, pow_add]; ring
  · have := hl.two_le; omega

theorem relIndex_Gj (K : FinExt l) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    (Gj K j).relIndex (Gj K i) = l ^ (j - i) := by
  have h := Subgroup.relIndex_mul_index (Gj_anti K hij)
  obtain ⟨h1, h2⟩ := deg_Ks K hi hij
  rw [Gj, Gj, ← IntermediateField.finrank_eq_fixingSubgroup_index,
    ← IntermediateField.finrank_eq_fixingSubgroup_index, h1] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h2) h

theorem val_deg (K : FinExt l) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    padicValNat l (Module.finrank ℚ_[l] ↥(Ks K j)) - padicValNat l (Module.finrank ℚ_[l] ↥(Ks K i))
      = j - i := by
  have hl : l.Prime := Fact.out
  obtain ⟨h1, h2⟩ := deg_Ks K hi hij
  rw [h1, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (pow_ne_zero _ hl.ne_zero) h2]
  rw [show padicValNat l (l ^ (j - i)) = j - i from by
    simpa only [← Nat.padicValNat_def] using Nat.multiplicity_prime_pow (p := l) (j - i)]
  omega

theorem free_finite (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) :
    letI := zlMod LL T
    Module.Free ℤ_[l] ↥T.L.T ∧ Module.Finite ℤ_[l] ↥T.L.T := by
  obtain ⟨d, M, A, hM⟩ := (GlobalTheory.Cyc.isMat_exists_and_props l K LL T).1
  unfold IsMat at hM
  obtain ⟨bT, _⟩ := hM
  letI := zlMod LL T
  exact ⟨Module.Free.of_basis bT, Module.Finite.of_basis bT⟩

theorem tors_induction {P : LocPrime l} (AI : LocAinf l P) (G : Subgroup (GQ l)) [CompactSpace ↥G]
    (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T]
    (ρ : ↥G →* (T →ₗ[ℤ_[l]] T)) (c : ℤ → ℕ)
    (hcont : ∀ a b : ℤ, a ≤ b →
      letI : TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b)) :=
        (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
      ∀ x, Continuous fun g => repQ AI G ρ a b g x)
    (hinv : ∀ a e b : ℤ, a ≤ e → e ≤ b →
      ∀ p : Qab (AinfSub l) (xiU AI) a b →ₗ[ℤ_[l]] Qab (AinfSub l) (xiU AI) a e,
      (∀ x, p (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) →
      ∀ z : (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a e)), (∀ g, repQ AI G ρ a e g z = z) →
        ∃ (k : ℕ) (x : (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b))), (∀ g, repQ AI G ρ a b g x = x) ∧
          LinearMap.lTensor T p x = (l : ℤ_[l]) ^ k • z)
    (hC : ∀ i : ℤ,
      letI : TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) i (i + 1))) :=
        (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
      TorsKilledBy (repQ AI G ρ i (i + 1)) (l : ℤ_[l]) ((l : ℤ_[l]) ^ c i))
    (a : ℤ) (n : ℕ) :
    letI : TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a (a + n + 1))) :=
        (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
    TorsKilledBy (repQ AI G ρ a (a + n + 1)) (l : ℤ_[l])
      ((l : ℤ_[l]) ^ ∑ i ∈ Finset.Ico a (a + n + 1), c i) := by
  induction n with
  | zero =>
    have e : a + ((0 : ℕ) : ℤ) + 1 = a + 1 := by simp
    rw [e]
    have e2 : Finset.Ico a (a + 1) = {a} := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    rw [e2, Finset.sum_singleton]
    exact hC a
  | succ n ih =>
    have e : a + ((n + 1 : ℕ) : ℤ) + 1 = (a + n + 1) + 1 := by push_cast; ring
    rw [e]
    generalize hb : a + n + 1 = b at ih ⊢
    have hab : a ≤ b := by omega
    have hb1 : b ≤ b + 1 := by omega
    have e2 : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [e2, Finset.sum_insert (by simp)]
    have hae := Mxi_anti (xiOK AI) hab
    have heb := Mxi_anti (xiOK AI) hb1
    obtain ⟨_, _⟩ := GlobalTheory.XiQuotient.tensor_quotient_torsionFree_complete l P AI a (b + 1) (hab.trans hb1) T
    obtain ⟨_, _⟩ := GlobalTheory.XiQuotient.tensor_quotient_torsionFree_complete l P AI b (b + 1) hb1 T
    obtain ⟨_, _⟩ := GlobalTheory.XiQuotient.tensor_quotient_torsionFree_complete l P AI a b hab T
    exact GlobalTheory.torsKilledBy_devissage l ↥G _ _ _ (repQ AI G ρ a (b + 1)) (repQ AI G ρ b (b + 1)) (repQ AI G ρ a b)
      (LinearMap.lTensor T (iQ (b + 1) hae))
      (LinearMap.lTensor T (pQ a heb)) _ _
      (Module.Flat.lTensor_preserves_injective_linearMap _ (iQ_injective _ hae))
      (LinearMap.lTensor_surjective _ (pQ_surjective a heb))
      (lTensor_exact _ (exact_iQ_pQ hae heb) (pQ_surjective a heb))
      (fun g x => iQ_equiv ρ _ _ hae g x) (fun g x => pQ_equiv ρ _ _ heb g x)
      (hcont a (b + 1) (hab.trans hb1))
      (hinv a b (b + 1) hab hb1 (pQ a heb) (fun _ => rfl))
      (hC b) ih

theorem tors_descend {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i ≤ j) (G : Subgroup (GQ l)) (hle : Gj K i ≤ G) (hle' : Gj K j ≤ G)
    (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥G →* (T →ₗ[ℤ_[l]] T)) (a b : ℤ) (c : ℕ)
    [TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b))]
    (h : TorsKilledBy (repQ AI (Gj K j) (ρ.comp (Subgroup.inclusion hle')) a b) (l : ℤ_[l])
      ((l : ℤ_[l]) ^ c)) :
    TorsKilledBy (repQ AI (Gj K i) (ρ.comp (Subgroup.inclusion hle)) a b) (l : ℤ_[l])
      ((l : ℤ_[l]) ^ (j - i + c)) :=
  tors_repQ AI (Gj K i) (Gj K j) (Gj_anti K hij) _ _ (comp_inclusion (Gj_anti K hij) hle hle' ρ) a b _ _
    (relIndex_Gj K hi hij) h


set_option maxHeartbeats 1000000 in
theorem tors_combine {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i ≤ j) (G : Subgroup (GQ l)) (hle : Gj K i ≤ G) (hle' : Gj K j ≤ G)
    (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T]
    (ρ : ↥G →* (T →ₗ[ℤ_[l]] T)) (c : ℤ → ℕ)
    (hcont : ∀ a b : ℤ, a ≤ b →
      letI : TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b)) :=
        (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
      ∀ x, Continuous fun g => repQ AI (Gj K j) (ρ.comp (Subgroup.inclusion hle')) a b g x)
    (hinv : ∀ a e b : ℤ, a ≤ e → e ≤ b →
      ∀ p : Qab (AinfSub l) (xiU AI) a b →ₗ[ℤ_[l]] Qab (AinfSub l) (xiU AI) a e,
      (∀ x, p (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) →
      ∀ z : (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a e)),
        (∀ g, repQ AI (Gj K j) (ρ.comp (Subgroup.inclusion hle')) a e g z = z) →
        ∃ (k : ℕ) (x : (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b))),
          (∀ g, repQ AI (Gj K j) (ρ.comp (Subgroup.inclusion hle')) a b g x = x) ∧
          LinearMap.lTensor T p x = (l : ℤ_[l]) ^ k • z)
    (hC : ∀ e : ℤ,
      letI : TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) e (e + 1))) :=
        (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
      TorsKilledBy (repQ AI (Gj K j) (ρ.comp (Subgroup.inclusion hle')) e (e + 1)) (l : ℤ_[l])
        ((l : ℤ_[l]) ^ c e))
    (a b : ℤ) (hab : a < b) (N : ℕ) (hN : N = j - i + ∑ e ∈ Finset.Ico a b, c e) :
    letI : TopologicalSpace (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b)) :=
        (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _
    TorsKilledBy (repQ AI (Gj K i) (ρ.comp (Subgroup.inclusion hle)) a b) (l : ℤ_[l])
      ((l : ℤ_[l]) ^ N) := by
  subst hN
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n + 1 := ⟨(b - a - 1).toNat, by omega⟩
  have := compact_Gj K j
  have key := tors_induction AI (Gj K j) T (ρ.comp (Subgroup.inclusion hle')) c hcont hinv hC a n
  exact @tors_descend l _ P AI K i j hi hij G hle hle' T _ _ ρ a _ _ (_) key

theorem vdeg_eq (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) (m : ℕ) (hsm : s ≤ m) :
    vdegMs (sit D.loc HW l (D.locA l) K s LL h) m = m - s := by
  have h1 : ell (sit D.loc HW l (D.locA l) K s LL h) = l := (D.loc l).PD_p K
  have h2 : (sit D.loc HW l (D.locA l) K s LL h).W.s = s := (HW l).W_s K s LL h
  rw [vdegMs, h1, h2]
  exact val_deg K h.1 hsm


set_option maxHeartbeats 1000000 in
theorem torsion_bound_at_level : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm5 D → adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (a b : ℤ) (hle : Gj K s ≤ GK K), a < b → HypW S E T M0 h0 → letI := zlMod LL T; letI : TopologicalSpace (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a b)) := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _; TorsKilledBy (repQ (D.locA l) (Gj K s) ((actTZ LL T).comp (Subgroup.inclusion hle)) a b) (l : ℤ_[l]) ((l : ℤ_[l]) ^ cLL l (mN l s (M0 + h0)) (vdegMs S (mN l s (M0 + h0))) (Jset S T) a b) := by
  intro D HW F h5 h7 l _ K s LL h S E T M0 h0 a b hle hab hW
  have hsm : s ≤ mN l s (M0 + h0) := by unfold mN; omega
  have hc : cLL l (mN l s (M0 + h0)) (vdegMs S (mN l s (M0 + h0))) (Jset S T) a b =
      mN l s (M0 + h0) - s + ∑ e ∈ Finset.Ico a b, (2 + max 1 (rI l (mN l s (M0 + h0)) (Jset S T) e)) := by
    rw [cLL, vdeg_eq D HW K s LL h _ hsm]
  have hle' := (Gj_anti K hsm).trans hle
  obtain ⟨hfree, hfin⟩ := free_finite K LL T
  have hC := fun i : ℤ => GlobalTheory.Cyc.GradedTorsion.torsion_killed D HW F h7 l K s LL h T M0 h0 i hle' hW
  have hcont := fun a b : ℤ => GlobalTheory.AinfCont.continuous_orbit_tensor_Qab D HW F l K s LL h T a b _ hle'
  have hinv := fun (a e b : ℤ) (hae : a ≤ e) (heb : e ≤ b) =>
    GlobalTheory.T.xiQuotient_invariants_lift_rationally D HW F h5 h7 l K s LL h T a e b _ hle' hsm hae heb hW.1
  exact @tors_combine l _ _ (D.locA l) K _ _ h.1 hsm (GK K) hle hle' _ _ (zlMod LL T) hfree hfin
    (actTZ LL T) _ hcont hinv hC a b hab _ hc

end GlobalTheory.TorsLL
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionBoundOfWeightHypStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_bound_of_weight_hyp : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm5 D → adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (a b : ℤ) (hle : Gj K s ≤ GK K), a < b → HypW S E T M0 h0 → letI := zlMod LL T; letI : TopologicalSpace (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a b)) := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _; TorsKilledBy (repQ (D.locA l) (Gj K s) ((actTZ LL T).comp (Subgroup.inclusion hle)) a b) (l : ℤ_[l]) ((l : ℤ_[l]) ^ cLL l (mN l s (M0 + h0)) (vdegMs S (mN l s (M0 + h0))) (Jset S T) a b) := by
  first | exact @GlobalTheory.TorsLL.torsion_bound_at_level | exact GlobalTheory.TorsLL.torsion_bound_at_level | (intros; apply GlobalTheory.TorsLL.torsion_bound_at_level <;> assumption)
end
