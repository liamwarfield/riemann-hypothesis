module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwasawaBruhatDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatWeightDecreases
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFactorization

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AOpRightInvariant
noncomputable def UpperTheory.Reformulated.B.Qf37.aOp :
    {G : Type} → [Group G] → Finset G → G → (G → ℂ) → G → ℂ :=
    fun {G : Type} [Group G] (R : Finset G) (t : G) (φ : G → ℂ) (g : G) ↦ ∑ r ∈ R, φ (g * r * t)

theorem UpperTheory.Reformulated.B.Qf37.aOp_rightInvariant :
    ∀ {G : Type} [inst : Group G] {I : Subgroup G} {t : G} {R : Finset G},
      (∀ r ∈ R, r ∈ I) →
        (∀ i ∈ I, ∃! r : G, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) →
          ∀ {φ : G → ℂ},
            (∀ (g i : G), i ∈ I → φ (g * i) = φ g) →
              ∀ (g i : G), i ∈ I → UpperTheory.Reformulated.B.Qf37.aOp R t φ (g * i) = UpperTheory.Reformulated.B.Qf37.aOp R t φ g := by
  intro G inst I t R hR hU φ hφ g i hi
  have hex : ∀ r ∈ R, ∃ s, s ∈ R ∧ t⁻¹ * (s⁻¹ * (i * r)) * t ∈ I := fun r hr =>
    (hU (i * r) (I.mul_mem hi (hR r hr))).exists
  choose σ hσR hσ using hex
  have hinj : ∀ a (ha : a ∈ R) b (hb : b ∈ R), σ a ha = σ b hb → a = b := by
    intro a ha b hb hab
    have h1 := hσ a ha
    have h2 := hσ b hb
    rw [← hab] at h2
    have h3 := I.mul_mem (I.inv_mem h1) h2
    have h4 : t⁻¹ * (a⁻¹ * b) * t ∈ I := by
      convert h3 using 1
      group
    have h5 : t⁻¹ * (b⁻¹ * b) * t ∈ I := by
      simp
    exact (hU b (hR b hb)).unique ⟨ha, h4⟩ ⟨hb, h5⟩
  unfold UpperTheory.Reformulated.B.Qf37.aOp
  refine Finset.sum_bij σ hσR hinj ?_ ?_
  · intro b hb
    obtain ⟨a, ha, hab⟩ := Finset.surj_on_of_inj_on_of_card_le σ hσR
      (fun a b ha hb h => hinj a ha b hb h) le_rfl b hb
    exact ⟨a, ha, hab.symm⟩
  · intro a ha
    rw [← hφ (g * σ a ha * t) _ (hσ a ha)]
    congr 1
    group
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalZeroOfInjectivePower
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalZeroOfInjectivePower
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

namespace GlobalTheory.CompanionTheory.SatPow

theorem functional_eq_zero_of_late_iterates :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (A : V →ₗ[ℂ] V), Function.Injective A → ∀ (l : V →ₗ[ℂ] ℂ) (v : V) (j₀ : ℕ), (∀ j ≥ j₀, l ((A ^ j) v) = 0) → l v = 0 := by
  intro V _ _ _ A hA l v j₀ h
  let U : Submodule ℂ V := Submodule.span ℂ (Set.range fun i : ℕ => (A ^ (i + j₀)) v)
  have hUl : U ≤ LinearMap.ker l := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (h (i + j₀) (Nat.le_add_left j₀ i))
  have hle : U ≤ U.comap A := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have e : A ((A ^ (i + j₀)) v) = (A ^ ((i + 1) + j₀)) v := by
      rw [show i + 1 + j₀ = (i + j₀) + 1 by omega, pow_succ', Module.End.mul_apply]
    show A ((A ^ (i + j₀)) v) ∈ U
    rw [e]
    exact Submodule.subset_span ⟨i + 1, rfl⟩
  have hAU : ∀ u ∈ U, A u ∈ U := fun u hu => hle hu
  let B : U →ₗ[ℂ] U := A.restrict hAU
  have hBi : Function.Injective B := by
    intro x y hxy
    apply Subtype.ext
    apply hA
    have := congrArg Subtype.val hxy
    simpa [B, LinearMap.restrict_apply] using this
  have hBs : Function.Surjective B := LinearMap.injective_iff_surjective.mp hBi
  have pull : ∀ x : V, A x ∈ U → x ∈ U := by
    intro x hx
    obtain ⟨u, hu⟩ := hBs ⟨A x, hx⟩
    have hux : A u = A x := congrArg Subtype.val hu
    rw [← hA hux]
    exact u.2
  have key : ∀ k : ℕ, (A ^ (j₀ - k)) v ∈ U := by
    intro k
    induction k with
    | zero =>
      have e0 : (A ^ (j₀ - 0)) v = (A ^ (0 + j₀)) v := by rw [Nat.sub_zero, Nat.zero_add]
      rw [e0]
      exact Submodule.subset_span ⟨0, rfl⟩
    | succ k ih =>
      rcases Nat.eq_zero_or_pos (j₀ - k) with h0 | hpos
      · have e1 : j₀ - (k + 1) = j₀ - k := by omega
        rw [e1]
        exact ih
      · have e : j₀ - k = (j₀ - (k + 1)) + 1 := by omega
        have e2 : (A ^ (j₀ - k)) v = A ((A ^ (j₀ - (k + 1))) v) := by
          rw [e, pow_succ', Module.End.mul_apply]
        rw [e2] at ih
        exact pull _ ih
  have hv : v ∈ U := by
    have h1 := key j₀
    rwa [Nat.sub_self, pow_zero, Module.End.one_apply] at h1
  exact LinearMap.mem_ker.mp (hUl hv)

end GlobalTheory.CompanionTheory.SatPow
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalZeroOfInjectivePowerStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_zero_of_injective_power : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (A : V →ₗ[ℂ] V), Function.Injective A → ∀ (l : V →ₗ[ℂ] ℂ) (v : V) (j₀ : ℕ), (∀ j ≥ j₀, l ((A ^ j) v) = 0) → l v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.functional_eq_zero_of_late_iterates | exact GlobalTheory.CompanionTheory.SatPow.functional_eq_zero_of_late_iterates | (intros; apply GlobalTheory.CompanionTheory.SatPow.functional_eq_zero_of_late_iterates <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriIndexFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriIndexFinite
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isOpen_iwU {σ : L →+* L} {n : ℕ} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) :
    IsOpen (IwU σ n : Set (GU σ n)) := by
  have hc : ∀ i j : Fin n, Continuous fun g : GU σ n =>
      ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j := fun i j =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  have hle : IsOpen {x : L | Valued.v x ≤ 1} := by
    convert Valued.isOpen_integer (Γ₀ := WithZero (Multiplicative ℤ)) L using 1
    ext x
    exact (Valuation.mem_integer_iff (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) x).symm
  have hlt : IsOpen {x : L | Valued.v x < 1} := by
    convert Valued.isOpen_ball L 1 using 2 with x
    simp only [Valuation.restrict_lt_one_iff]
  have hset : (IwU σ n : Set (GU σ n)) =
      ⋂ i : Fin n, ⋂ j : Fin n,
        ({g : GU σ n | Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1} ∩
         {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1}) := by
    ext g
    simp only [SetLike.mem_coe, mem_iwU_iff hσv g, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩ i j
      exact ⟨h1 i j, h2 i j⟩
    · intro h
      exact ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  refine (hle.preimage (hc i j)).inter ?_
  by_cases hij : j < i
  · have e : {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1} =
        (fun g : GU σ n => ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ⁻¹'
          {x : L | Valued.v x < 1} := by
      ext g
      simp [hij]
    rw [e]
    exact hlt.preimage (hc i j)
  · have e : {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1} =
        Set.univ := by
      ext g
      simp [hij]
    rw [e]
    exact isOpen_univ

theorem isOpen_map_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsOpen (H : Set G)) (t : G) :
    IsOpen ((H.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have e : ⇑(MulAut.conj t).toMonoidHom = fun x => t * x * t⁻¹ := by
    funext x
    simp [MulAut.conj_apply]
  rw [e]
  have h1 : IsOpenMap fun x : G => t * x * t⁻¹ :=
    (isOpenMap_mul_right t⁻¹).comp (isOpenMap_mul_left t)
  exact h1 _ hH

theorem finite_index_iwU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q →
      Finite (KU σ n ⧸ (IwU σ n).subgroupOf (KU σ n)) ∧
      ∀ t : GU σ n, Finite (IwU σ n ⧸
        (IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom).subgroupOf (IwU σ n)) := by
  intro L _ _ _ ϖ σ q n h
  obtain ⟨-, hKc, hle, -⟩ := GlobalTheory.CompanionTheory.KUFactsU.kuFacts L ϖ σ q n h
  have hIo : IsOpen (IwU σ n : Set (GU σ n)) := isOpen_iwU h.2.1
  haveI : CompactSpace (KU σ n) := isCompact_iff_compactSpace.mp hKc
  refine ⟨Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hIo), fun t => ?_⟩
  have hIc : IsCompact (IwU σ n : Set (GU σ n)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hIo) fun x hx => hle hx
  haveI : CompactSpace (IwU σ n) := isCompact_iff_compactSpace.mp hIc
  have hOpen : IsOpen ((IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom : Subgroup (GU σ n)) :
      Set (GU σ n)) := by
    rw [Subgroup.coe_inf]
    exact hIo.inter (isOpen_map_conj hIo t)
  exact Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hOpen)

end GlobalTheory.CompanionTheory.SatPow

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriIndexFiniteStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwahori_index_finite : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → Finite (KU σ n ⧸ (IwU σ n).subgroupOf (KU σ n)) ∧ ∀ t : GU σ n, Finite (IwU σ n ⧸ (IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom).subgroupOf (IwU σ n)) := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.finite_index_iwU | exact GlobalTheory.CompanionTheory.SatPow.finite_index_iwU | (intros; apply GlobalTheory.CompanionTheory.SatPow.finite_index_iwU <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetRepsOfFactorization
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetRepsOfFactorization
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

namespace GlobalTheory.CompanionTheory.SatPow.RepsGen

private theorem mem_map_conj_iff_inv_mul_mul_mem {G : Type*} [Group G] (I : Subgroup G) (t y : G) :
    y ∈ I.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * y * t ∈ I := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro h
    exact ⟨t⁻¹ * y * t, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem reps_of_quotient_with_property (G : Type) [Group G] (I : Subgroup G) (t : G) (P : G → Prop)
    (hP1 : P 1)
    (hfin : Finite (I ⧸ (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I))
    (hfac : ∀ i ∈ I, ∃ u ∈ I, P u ∧ ∃ y ∈ I, t⁻¹ * y * t ∈ I ∧ i = u * y) :
    ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ r ∈ R, r ∈ I ∧ P r) ∧
      ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I := by
  classical
  set H := (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I with hH
  have : Fintype (I ⧸ H) := @Fintype.ofFinite _ hfin
  have hmem : ∀ a b : I, (QuotientGroup.mk a : I ⧸ H) = QuotientGroup.mk b ↔
      t⁻¹ * ((a : G)⁻¹ * b) * t ∈ I := by
    intro a b
    rw [QuotientGroup.eq, hH, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      and_iff_right (a⁻¹ * b).2, mem_map_conj_iff_inv_mul_mul_mem]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have key : ∀ c : I ⧸ H, ∃ r : I, P r ∧ (QuotientGroup.mk r : I ⧸ H) = c ∧
      (c = QuotientGroup.mk 1 → r = 1) := by
    intro c
    obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective c
    by_cases h : (QuotientGroup.mk i : I ⧸ H) = QuotientGroup.mk 1
    · exact ⟨1, by simpa using hP1, h.symm, fun _ => rfl⟩
    · obtain ⟨u, hu, hPu, y, hy, hty, hi⟩ := hfac i i.2
      refine ⟨⟨u, hu⟩, hPu, ?_, fun h' => absurd h' h⟩
      rw [hmem]
      have hy' : u⁻¹ * (i : G) = y := by rw [hi, inv_mul_cancel_left]
      show t⁻¹ * (u⁻¹ * (i : G)) * t ∈ I
      rw [hy']
      exact hty
  choose f hfP hfmk hf1 using key
  refine ⟨Finset.univ.image (fun c => (f c : G)), ?_, ?_, ?_⟩
  · exact Finset.mem_image.2 ⟨QuotientGroup.mk 1, Finset.mem_univ _, by rw [hf1 _ rfl]; simp⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    exact ⟨(f c).2, hfP c⟩
  · intro i hi
    refine ⟨f (QuotientGroup.mk ⟨i, hi⟩),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · exact (hmem (f (QuotientGroup.mk ⟨i, hi⟩)) ⟨i, hi⟩).1 (hfmk _)
    · rintro r ⟨hr, hri⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
      have hc : c = QuotientGroup.mk ⟨i, hi⟩ := (hfmk c).symm.trans ((hmem _ _).2 hri)
      subst hc
      rfl

end GlobalTheory.CompanionTheory.SatPow.RepsGen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetRepsOfFactorizationStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_reps_of_factorization : ∀ (G : Type) [Group G] (I : Subgroup G) (t : G) (P : G → Prop), P 1 → Finite (I ⧸ (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I) → (∀ i ∈ I, ∃ u ∈ I, P u ∧ ∃ y ∈ I, t⁻¹ * y * t ∈ I ∧ i = u * y) → ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ r ∈ R, r ∈ I ∧ P r) ∧ ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property | exact GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property | (intros; apply GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckePowerCosetFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckePowerCosetFormula
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow.HeckeTrace

variable {G : Type} [Group G]

theorem aOp_rightInvariant {I : Subgroup G} {t : G} {R : Finset G} (hR : ∀ r ∈ R, r ∈ I)
    (hu : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) {φ : G → ℂ}
    (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g) : ∀ g, ∀ i ∈ I, aOp R t φ (g * i) = aOp R t φ g :=
  _root_.UpperTheory.Reformulated.B.Qf37.aOp_rightInvariant hR hu hφ

theorem aOp_iterate_rightInvariant {I : Subgroup G} {t : G} {R : Finset G} (hR : ∀ r ∈ R, r ∈ I)
    (hu : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) {φ : G → ℂ}
    (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g) (j : ℕ) :
    ∀ g, ∀ i ∈ I, (aOp R t)^[j] φ (g * i) = (aOp R t)^[j] φ g := by
  induction j with
  | zero => simpa using hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact aOp_rightInvariant hR hu ih

theorem exists_words (K : Subgroup G) (t : G) (R : Finset G) (h1 : (1 : G) ∈ R)
    (hc : ∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K) (j : ℕ) :
    ∃ W : Multiset G, W ≠ 0 ∧ (∀ w ∈ W, ∃ k ∈ K, w = k * t ^ j) ∧
      ∀ (ψ : G → ℂ) (g : G), (aOp R t)^[j] ψ g = (W.map fun w => ψ (g * w)).sum := by
  induction j with
  | zero =>
    refine ⟨{1}, by simp, ?_, fun ψ g => by simp⟩
    intro w hw
    exact ⟨1, one_mem K, by simpa using hw⟩
  | succ j ih =>
    obtain ⟨W, hW0, hWK, hWf⟩ := ih
    refine ⟨W.bind fun w => R.val.map fun r => w * r * t, ?_, ?_, ?_⟩
    · obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hW0
      intro h0
      have hm : w * 1 * t ∈ W.bind fun w => R.val.map fun r => w * r * t :=
        Multiset.mem_bind.2 ⟨w, hw, Multiset.mem_map.2 ⟨1, h1, rfl⟩⟩
      rw [h0] at hm
      exact Multiset.notMem_zero _ hm
    · intro x hx
      obtain ⟨w, hw, hx⟩ := Multiset.mem_bind.1 hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨k, hk, rfl⟩ := hWK w hw
      refine ⟨k * (t ^ j * r * (t ^ j)⁻¹), mul_mem hk (hc r hr j), ?_⟩
      rw [pow_succ]
      group
    · intro ψ g
      rw [Function.iterate_succ_apply, hWf, Multiset.map_bind, Multiset.sum_bind]
      congr 1
      refine Multiset.map_congr rfl fun w _ => ?_
      rw [Multiset.map_map]
      show ∑ r ∈ R, ψ (g * w * r * t) = _
      simp only [Function.comp, mul_assoc]
      rfl

theorem finsum_left_mul {K I : Subgroup G} (hIK : I ≤ K) {φ : G → ℂ} (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g)
    {k : G} (hk : k ∈ K) :
    ∑ᶠ c : K ⧸ I.subgroupOf K, φ (k * ((c.out : K) : G)) = ∑ᶠ c : K ⧸ I.subgroupOf K, φ ((c.out : K) : G) := by
  let kk : K := ⟨k, hk⟩
  rw [← finsum_comp_equiv (MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K))
    (f := fun c : K ⧸ I.subgroupOf K => φ ((c.out : K) : G))]
  refine finsum_congr fun c => ?_
  have e : (MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K)) c = ((kk * c.out : K) : K ⧸ I.subgroupOf K) := by
    show kk • c = _
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (I.subgroupOf K) (kk * c.out)
  have hi : ((h : K) : G) ∈ I := Subgroup.mem_subgroupOf.1 h.2
  show _ = φ ((((MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K)) c).out : K) : G)
  rw [e, hh]
  show _ = φ (k * ((c.out : K) : G) * ((h : K) : G))
  rw [hφ _ _ hi]

theorem multiset_sum_eq_hAct (K : Subgroup G) (s : G) (M : Multiset G) (hM0 : M ≠ 0)
    (hMs : ∀ x ∈ M, x ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G))
    (hinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ k ∈ K,
      (M.map fun x => ψ (k * x)).sum = (M.map ψ).sum) :
    ∃ m : ℕ, 0 < m ∧ ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) →
      (M.map ψ).sum = (m : ℂ) * hAct K (dosetInd ℂ K s) ψ 1 := by
  classical
  set M' : Multiset (G ⧸ K) := M.map (QuotientGroup.mk : G → G ⧸ K) with hM'
  have hout : ∀ (ψ : G → ℂ), (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ x : G,
      ψ ((x : G ⧸ K).out) = ψ x := by
    intro ψ hψ x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
    rw [hh, hψ _ _ h.2]
  have key1 : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) →
      (M.map ψ).sum = ∑ y ∈ M'.toFinset, (M'.count y : ℂ) * ψ y.out := by
    intro ψ hψ
    have e : M.map ψ = M'.map fun y : G ⧸ K => ψ y.out := by
      rw [hM', Multiset.map_map]
      exact Multiset.map_congr rfl fun x _ => (hout ψ hψ x).symm
    rw [e, Finset.sum_multiset_map_count]
    simp only [nsmul_eq_mul]
  let e : G ⧸ K → G → ℂ := fun y x => if (x : G ⧸ K) = y then 1 else 0
  have he : ∀ y g, ∀ k ∈ K, e y (g * k) = e y g := by
    intro y g k hk
    have : ((g * k : G) : G ⧸ K) = g := by
      rw [QuotientGroup.eq]
      simpa using inv_mem hk
    simp only [e, this]
  have key2 : ∀ y, (M.map (e y)).sum = (M'.count y : ℂ) := by
    intro y
    rw [key1 _ (he y)]
    have : ∀ z : G ⧸ K, (M'.count z : ℂ) * e y z.out = if z = y then (M'.count z : ℂ) else 0 := by
      intro z
      simp only [e, QuotientGroup.out_eq']
      split_ifs <;> simp
    simp only [this]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · have : M'.count y = 0 := Multiset.count_eq_zero.2 (by simpa using h)
      simp [this]
  have key3 : ∀ k ∈ K, ∀ g : G, M'.count ((k * g : G) : G ⧸ K) = M'.count (g : G ⧸ K) := by
    intro k hk g
    have h1 := hinv (e ((k * g : G) : G ⧸ K)) (he _) k hk
    have h2 : (fun x => e ((k * g : G) : G ⧸ K) (k * x)) = e (g : G ⧸ K) := by
      funext x
      have : ((k * x : G) : G ⧸ K) = ((k * g : G) : G ⧸ K) ↔ (x : G ⧸ K) = (g : G ⧸ K) := by
        rw [QuotientGroup.eq, QuotientGroup.eq]
        have : (k * x)⁻¹ * (k * g) = x⁻¹ * g := by group
        rw [this]
      simp only [e, this]
    rw [h2, key2, key2] at h1
    exact_mod_cast h1.symm
  obtain ⟨x0, hx0⟩ := Multiset.exists_mem_of_ne_zero hM0
  have hconst : ∀ g ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G),
      M'.count (g : G ⧸ K) = M'.count (x0 : G ⧸ K) := by
    have hred : ∀ g ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G),
        M'.count (g : G ⧸ K) = M'.count (s : G ⧸ K) := by
      intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
      have : ((a * s * b : G) : G ⧸ K) = ((a * s : G) : G ⧸ K) := by
        rw [QuotientGroup.eq]
        simpa [mul_assoc] using inv_mem hb
      rw [this, key3 a ha]
    intro g hg
    rw [hred g hg, hred x0 (hMs x0 hx0)]
  have hpos : 0 < M'.count (x0 : G ⧸ K) :=
    Multiset.count_pos.2 (Multiset.mem_map_of_mem _ hx0)
  refine ⟨M'.count (x0 : G ⧸ K), hpos, fun ψ hψ => ?_⟩
  have hmem : ∀ y : G ⧸ K, y ∈ M'.toFinset ↔ y.out ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G) := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 hy)
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
      obtain ⟨a, ha, b, hb, e1⟩ := DoubleCoset.mem_doubleCoset.1 (hMs x hx)
      refine DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * h, mul_mem hb h.2, ?_⟩
      rw [hh, e1]
      group
    · intro hy
      have h := hconst _ hy
      rw [QuotientGroup.out_eq'] at h
      refine Multiset.mem_toFinset.2 (Multiset.count_pos.1 ?_)
      rw [h]
      exact hpos
  have hact : hAct K (dosetInd ℂ K s) ψ 1 = ∑ y ∈ M'.toFinset, ψ y.out := by
    unfold hAct
    rw [finsum_eq_sum_of_support_subset (s := M'.toFinset)]
    · refine Finset.sum_congr rfl fun y hy => ?_
      have h := (hmem y).1 hy
      simp [dosetInd, Set.indicator_of_mem h]
    · intro y hy
      by_contra hn
      have h : y.out ∉ DoubleCoset.doubleCoset s (K : Set G) (K : Set G) := fun h => hn ((hmem y).2 h)
      apply hy
      simp [dosetInd, Set.indicator_of_notMem h]
  rw [hact, key1 ψ hψ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h := hconst _ ((hmem y).1 hy)
  rw [QuotientGroup.out_eq'] at h
  rw [h]

theorem heckeTrace : ∀ (G : Type) [Group G] (K I : Subgroup G), I ≤ K → Finite (K ⧸ I.subgroupOf K) → ∀ (t : G) (R : Finset G), (1 : G) ∈ R → (∀ r ∈ R, r ∈ I) → (∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K) → (∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) → ∀ j : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (m : ℂ) * hAct K (dosetInd ℂ K (t ^ j)) ψ 1 := by
  intro G _ K I hIK hfin t R h1 hR hc hu j
  classical
  haveI := Fintype.ofFinite (K ⧸ I.subgroupOf K)
  obtain ⟨W, hW0, hWK, hWf⟩ := exists_words K t R h1 hc j
  set M : Multiset G := (Finset.univ : Finset (K ⧸ I.subgroupOf K)).val.bind
    fun c => W.map fun w => ((c.out : K) : G) * w with hMdef
  have hM : ∀ φ : G → ℂ, (M.map φ).sum =
      ∑ c : K ⧸ I.subgroupOf K, (W.map fun w => φ (((c.out : K) : G) * w)).sum := by
    intro φ
    rw [hMdef, Multiset.map_bind, Multiset.sum_bind]
    simp only [Multiset.map_map, Function.comp_def]
    rfl
  have hL : ∀ ψ : G → ℂ, ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (M.map ψ).sum := by
    intro ψ
    rw [finsum_eq_sum_of_fintype, hM]
    exact Finset.sum_congr rfl fun c _ => hWf ψ _
  have hIinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ g, ∀ i ∈ I, ψ (g * i) = ψ g :=
    fun ψ hψ g i hi => hψ g i (hIK hi)
  have hinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ k ∈ K,
      (M.map fun x => ψ (k * x)).sum = (M.map ψ).sum := by
    intro ψ hψ k hk
    rw [← hL ψ, ← finsum_left_mul hIK (aOp_iterate_rightInvariant hR hu (hIinv ψ hψ) j) hk,
      finsum_eq_sum_of_fintype, hM]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hWf ψ]
    simp only [mul_assoc]
  have hMs : ∀ x ∈ M, x ∈ DoubleCoset.doubleCoset (t ^ j) (K : Set G) (K : Set G) := by
    intro x hx
    obtain ⟨c, -, hx⟩ := Multiset.mem_bind.1 hx
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨k, hk, rfl⟩ := hWK w hw
    exact DoubleCoset.mem_doubleCoset.2
      ⟨((c.out : K) : G) * k, mul_mem (c.out : K).2 hk, 1, one_mem K, by simp [mul_assoc]⟩
  have hM0 : M ≠ 0 := by
    obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hW0
    let c0 : K ⧸ I.subgroupOf K := ((1 : K) : K ⧸ I.subgroupOf K)
    intro h0
    have hm : ((c0.out : K) : G) * w ∈ M :=
      Multiset.mem_bind.2 ⟨c0, Finset.mem_univ c0, Multiset.mem_map.2 ⟨w, hw, rfl⟩⟩
    rw [h0] at hm
    exact Multiset.notMem_zero _ hm
  obtain ⟨m, hm, hmf⟩ := multiset_sum_eq_hAct K (t ^ j) M hM0 hMs hinv
  exact ⟨m, hm, fun ψ hψ => by rw [hL, hmf ψ hψ]⟩

end GlobalTheory.CompanionTheory.SatPow.HeckeTrace

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckePowerCosetFormulaStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_power_coset_formula : ∀ (G : Type) [Group G] (K I : Subgroup G), I ≤ K → Finite (K ⧸ I.subgroupOf K) → ∀ (t : G) (R : Finset G), (1 : G) ∈ R → (∀ r ∈ R, r ∈ I) → (∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K) → (∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) → ∀ j : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (m : ℂ) * hAct K (dosetInd ℂ K (t ^ j)) ψ 1 := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.HeckeTrace.heckeTrace | exact GlobalTheory.CompanionTheory.SatPow.HeckeTrace.heckeTrace | (intros; apply GlobalTheory.CompanionTheory.SatPow.HeckeTrace.heckeTrace <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantConjugateUnipotentMem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantConjugateUnipotentMem
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

section Contr

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem val_le_of_ordL_lt {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) (h : ordL a < ordL b) :
    Valued.v b ≤ Valued.v a := by
  have ha' : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have hb' : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  unfold ordL at h
  rw [dite_eq_right ha', dite_eq_right hb'] at h
  have hle : WithZero.unzero hb' ≤ WithZero.unzero ha' := by
    rw [← Multiplicative.toAdd_le]; omega
  have := WithZero.coe_le_coe.2 hle
  rwa [WithZero.coe_unzero, WithZero.coe_unzero] at this

theorem conj_entries_le_one {t A : GL (Fin n) L} (ht : IsDiagM t) (hd : IsStrictDom t)
    (h1 : ∀ i j, Valued.v ((A : Matrix (Fin n) (Fin n) L) i j) ≤ 1)
    (h2 : ∀ i j, j < i → (A : Matrix (Fin n) (Fin n) L) i j = 0)
    (h3 : ∀ i, (A : Matrix (Fin n) (Fin n) L) i i = 1) (k : ℕ) (i j : Fin n) :
    Valued.v (((t ^ k * A * (t ^ k)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 := by
  set d : Fin n → L := fun i => (t : Matrix (Fin n) (Fin n) L) i i with hdef
  have htd : (t : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hdef]
    · rw [Matrix.diagonal_apply_ne _ hab]; exact ht a b hab
  have hd0 : ∀ a, d a ≠ 0 := by
    intro a h0
    have hm : ((t : Matrix (Fin n) (Fin n) L) * ((t⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) a a = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]; simp
    rw [htd, Matrix.diagonal_mul, h0, zero_mul] at hm
    exact zero_ne_one hm
  have hpow : ((t ^ k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun a => d a ^ k := by
    rw [Units.val_pow_eq_pow_val, htd, Matrix.diagonal_pow]
    rfl
  have hinv : (((t ^ k)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun a => (d a ^ k)⁻¹ := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hpow, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    exact mul_inv_cancel₀ (pow_ne_zero _ (hd0 a))
  rw [Units.val_mul, Units.val_mul, hpow, hinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hle : Valued.v (d i) ≤ Valued.v (d j) := val_le_of_ordL_lt (hd0 j) (hd0 i) (hd i j hij)
    have hb : Valued.v (d j) ^ k ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).2 (hd0 j))
    rw [map_mul, map_mul, map_inv₀, map_pow, map_pow]
    calc Valued.v (d i) ^ k * Valued.v ((A : Matrix (Fin n) (Fin n) L) i j) * (Valued.v (d j) ^ k)⁻¹
        ≤ Valued.v (d i) ^ k * 1 * (Valued.v (d j) ^ k)⁻¹ := by gcongr; exact h1 i j
      _ = Valued.v (d i) ^ k / Valued.v (d j) ^ k := by rw [mul_one, div_eq_mul_inv]
      _ ≤ 1 := (div_le_one₀ (zero_lt_iff.2 hb)).2 (pow_le_pow_left' hle k)
  · subst hij
    rw [h3, mul_one, mul_inv_cancel₀ (pow_ne_zero _ (hd0 i)), map_one]
  · rw [h2 i j hij]; simp

theorem conj_unip_mem_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (t u : GU σ n), IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → u ∈ IwU σ n → IsUnipU u →
      ∀ k : ℕ, t ^ k * u * (t ^ k)⁻¹ ∈ KU σ n := by
  intro L _ _ σ n t u ht hd hu hU k
  have hinv := (GlobalTheory.LGrp.mem_GU_iff σ n (u : GL (Fin n) L)).1 u.2
  have huGL : (u : GL (Fin n) L) ∈ IwGL L n := hu
  have hU1 : ∀ i j, Valued.v (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 :=
    fun i j => GlobalTheory.CompanionTheory.KUFactsU.iwGL_entries huGL i j
  have hV1 : ∀ i j, Valued.v ((((u : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 :=
    fun i j => GlobalTheory.CompanionTheory.KUFactsU.iwGL_entries (inv_mem huGL) i j
  have hV2 : ∀ i j, j < i → (((u : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
    intro i j hji
    rw [hinv, hU.1 _ _ (Fin.rev_lt_rev.2 hji), map_zero]
  have hV3 : ∀ i, (((u : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
    intro i
    rw [hinv, hU.2, map_one]
  have hmem : t ^ k * u * (t ^ k)⁻¹ ∈ (KU σ n : Set (GU σ n)) := by
    rw [IntPtsUnitary.coe_KU, Set.mem_preimage, IntPtsUnitary.coe_GLint]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact conj_entries_le_one ht hd hU1 hU.1 hU.2 k i j
    · have e : (((t ^ k * u * (t ^ k)⁻¹ : GU σ n) : GL (Fin n) L))⁻¹ =
          (t : GL (Fin n) L) ^ k * (u : GL (Fin n) L)⁻¹ * ((t : GL (Fin n) L) ^ k)⁻¹ := by
        simp [mul_assoc]
      rw [e]
      exact conj_entries_le_one ht hd hV1 hV2 hV3 k i j
  exact hmem

end Contr

end GlobalTheory.CompanionTheory.SatPow

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantConjugateUnipotentMemStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_conjugate_unipotent_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (t u : GU σ n), IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → u ∈ IwU σ n → IsUnipU u → ∀ k : ℕ, t ^ k * u * (t ^ k)⁻¹ ∈ KU σ n := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.conj_unip_mem_KU | exact GlobalTheory.CompanionTheory.SatPow.conj_unip_mem_KU | (intros; apply GlobalTheory.CompanionTheory.SatPow.conj_unip_mem_KU <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakePowerNonvanishing
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

theorem aOp_rightInv {G : Type} [Group G] (I : Subgroup G) (t : G) (R : Finset G) (hRI : ∀ r ∈ R, r ∈ I)
    (hR : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) (φ : G → ℂ) (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g) :
    ∀ g, ∀ i ∈ I, aOp R t φ (g * i) = aOp R t φ g := by
  classical
  intro g i hi
  have key : ∀ r, r ∈ R → ∃ r', r' ∈ R ∧ t⁻¹ * (r'⁻¹ * (i * r)) * t ∈ I := fun r hr => by
    obtain ⟨r', h, -⟩ := hR (i * r) (I.mul_mem hi (hRI r hr))
    exact ⟨r', h⟩
  choose! f hfR hf using key
  have he : ∀ r ∈ R, φ (g * i * r * t) = φ (g * f r * t) := fun r hr => by
    have e : g * i * r * t = (g * f r * t) * (t⁻¹ * ((f r)⁻¹ * (i * r)) * t) := by group
    rw [e, hφ _ _ (hf r hr)]
  have hinj : Set.InjOn f (R : Set G) := fun r₁ h₁ r₂ h₂ e => by
    have h3 : t⁻¹ * (r₁⁻¹ * r₂) * t ∈ I := by
      have := I.mul_mem (I.inv_mem (hf r₁ h₁)) (hf r₂ h₂)
      rw [← e] at this
      have e2 : (t⁻¹ * ((f r₁)⁻¹ * (i * r₁)) * t)⁻¹ * (t⁻¹ * ((f r₁)⁻¹ * (i * r₂)) * t) = t⁻¹ * (r₁⁻¹ * r₂) * t := by
        group
      rwa [e2] at this
    exact (hR r₂ (hRI r₂ h₂)).unique ⟨h₁, h3⟩ ⟨h₂, by simp [I.one_mem]⟩
  have himg : R.image f = R :=
    Finset.eq_of_subset_of_card_le (fun x hx => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
      exact hfR r hr) (by rw [Finset.card_image_of_injOn hinj])
  unfold aOp
  rw [Finset.sum_congr rfl he]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image hinj]

theorem abs_main {G : Type} [Group G] (K I : Subgroup G) (hIK : I ≤ K) (hfin : Finite (K ⧸ I.subgroupOf K)) (t : G)
    (R : Finset G) (h1R : (1 : G) ∈ R) (hRI : ∀ r ∈ R, r ∈ I) (hRt : ∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K)
    (hR : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I)
    (Wsp : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ Wsp]
    (hWA : ∀ φ ∈ Wsp, aOp R t φ ∈ Wsp) (hinj : ∀ φ ∈ Wsp, aOp R t φ = 0 → φ = 0)
    (φ₀ : G → ℂ) (hφ₀ : φ₀ ∈ Wsp) (hK : ∀ g, ∀ k ∈ K, φ₀ (g * k) = φ₀ g) (h1 : φ₀ 1 = 1)
    (lam : ℕ → ℂ) (hlam : ∀ j, hAct K (dosetInd ℂ K (t ^ j)) φ₀ 1 = lam j) (j₀ : ℕ) : ∃ j ≥ j₀, lam j ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  haveI := Fintype.ofFinite (K ⧸ I.subgroupOf K)
  let A : Wsp →ₗ[ℂ] Wsp :=
    { toFun := fun φ => ⟨aOp R t φ, hWA φ φ.2⟩
      map_add' := fun a b => Subtype.ext (by
        funext g; simp [aOp, Finset.sum_add_distrib])
      map_smul' := fun c a => Subtype.ext (by
        funext g; simp [aOp, Finset.mul_sum]) }
  let l : Wsp →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∑ c : K ⧸ I.subgroupOf K, (φ : G → ℂ) ((c.out : K) : G)
      map_add' := fun a b => by simp [Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.mul_sum] }
  let v : Wsp := ⟨φ₀, hφ₀⟩
  have hAj : ∀ j, (((A ^ j) v : Wsp) : G → ℂ) = (aOp R t)^[j] φ₀ := fun j => by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
      show aOp R t (((A ^ j) v : Wsp) : G → ℂ) = _
      rw [ih]
  have hAinj : Function.Injective A := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    exact Subtype.ext (hinj a a.2 (congrArg Subtype.val ha))
  have hl0 : l v = 0 := by
    refine GlobalTheory.T.functional_zero_of_injective_power _ A hAinj l v j₀ fun j hj => ?_
    obtain ⟨m, -, hm⟩ := GlobalTheory.T.hecke_power_coset_formula G K I hIK hfin t R h1R hRI hRt hR j
    have := hm φ₀ hK
    rw [hlam, hcon j hj, mul_zero, finsum_eq_sum_of_fintype] at this
    show ∑ c : K ⧸ I.subgroupOf K, (((A ^ j) v : Wsp) : G → ℂ) ((c.out : K) : G) = 0
    rw [hAj, this]
  have hl1 : l v = (Fintype.card (K ⧸ I.subgroupOf K) : ℂ) := by
    show ∑ c : K ⧸ I.subgroupOf K, φ₀ ((c.out : K) : G) = _
    have : ∀ c : K ⧸ I.subgroupOf K, φ₀ ((c.out : K) : G) = 1 := fun c => by
      have := hK 1 _ (c.out : K).2
      rwa [one_mul, h1] at this
    simp [this]
  rw [hl1] at hl0
  exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 hl0)

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem isPermW_unique {w w' : GU σ n} {π : Equiv.Perm (Fin n)} (h : IsPermW w π) (h' : IsPermW w' π) : w = w' :=
  Subtype.ext (Units.ext (Matrix.ext fun a c => by rw [h a c, h' a c]))

theorem chiDeltaU_congr {m : ℕ} (q : ℕ) (α : Fin m → ℂ) {b b' : GU σ n}
    (h : ∀ a : Fin n, ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) =
      ordL (((b' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a)) : chiDeltaU q α b = chiDeltaU q α b' := by
  unfold chiDeltaU
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [h]
  · rfl

theorem chiDeltaU_ne_zero {m : ℕ} {q : ℕ} (hq : (q : ℂ) ≠ 0) {α : Fin m → ℂ} (hα : ∀ i, α i ≠ 0) (b : GU σ n) :
    chiDeltaU q α b ≠ 0 := by
  unfold chiDeltaU
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  split_ifs with hi
  · exact mul_ne_zero (zpow_ne_zero _ (hα i)) (zpow_ne_zero _ hq)
  · exact one_ne_zero

theorem conj_diag {t w : GU σ n} {π : Equiv.Perm (Fin n)} (ht : IsDiagM (t : GL (Fin n) L)) (hw : IsPermW w π) :
    IsBorelU (w * t * w⁻¹) ∧ ∀ a : Fin n, (((w * t * w⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a =
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π a) := by
  set s := w * t * w⁻¹ with hs
  have hsw : (((s * w : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (((w * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [hs]; congr 2; group
  have key : ∀ a e : Fin n, ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a e =
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π e) := fun a e => by
    have := congrFun (congrFun hsw a) (π e)
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply] at this
    simpa [hw _ _] using this
  refine ⟨fun i j hij => ?_, fun a => key a a⟩
  rw [key]
  exact ht _ _ fun h => (ne_of_gt hij) (π.injective h)

theorem aOp_inj (q : ℕ) (hq : (q : ℂ) ≠ 0) {m : ℕ} (α : Fin m → ℂ) (hα : ∀ i, α i ≠ 0)
    (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (t : GU σ n) (htD : IsDiagM (t : GL (Fin n) L)) (htS : IsStrictDom (t : GL (Fin n) L))
    (R : Finset (GU σ n)) (h1R : (1 : GU σ n) ∈ R) (hRI : ∀ r ∈ R, r ∈ IwU σ n)
    (φ : GU σ n → ℂ) (hB : ∀ b g, IsBorelU b → φ (b * g) = chiDeltaU q α b * φ g)
    (hI : ∀ g, ∀ i ∈ IwU σ n, φ (g * i) = φ g) (h0 : aOp R t φ = 0) : φ = 0 := by
  classical
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hdec : ∀ b w i : GU σ n, IsBorelU b → i ∈ IwU σ n → φ (b * w * i) = chiDeltaU q α b * φ w :=
    fun b w i hb hi => by rw [hI _ _ hi, hB _ _ hb]
  set S : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter fun π => ∃ w : GU σ n, IsPermW w π ∧ φ w ≠ 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨b, w, i, π, hb, hw, hi, e⟩ := GlobalTheory.T.unitary_iwasawa_bruhat_decomposition L σ n hσ hσv g
    refine ⟨π, Finset.mem_filter.2 ⟨Finset.mem_univ _, w, hw, fun h => hg ?_⟩⟩
    rw [e, hdec _ _ _ hb hi, h, mul_zero]
  obtain ⟨π, hπS, hmin⟩ := Finset.exists_min_image S (permWt t) hSne
  obtain ⟨w, hw, hφw⟩ := (Finset.mem_filter.1 hπS).2
  obtain ⟨hsB, hsd⟩ := conj_diag (w := w) htD hw
  set x := chiDeltaU q α (w * t * w⁻¹) * φ w with hx
  have hx0 : x ≠ 0 := mul_ne_zero (chiDeltaU_ne_zero hq hα _) hφw
  have hterm : ∀ r ∈ R, φ (w * r * t) = if φ (w * r * t) = x then x else 0 := fun r hr => by
    split_ifs with h
    · exact h
    obtain ⟨b, w', i, π', hb, hw', hi, e⟩ := GlobalTheory.T.unitary_iwasawa_bruhat_decomposition L σ n hσ hσv (w * r * t)
    rcases GlobalTheory.T.bruhat_weight_decreases L σ n t w w' b r i π π' htD htS hw hw' hb (hRI r hr) hi e with hlt | ⟨rfl, hord⟩
    · have hz : φ w' = 0 := by
        by_contra hz
        exact absurd (hmin π' (Finset.mem_filter.2 ⟨Finset.mem_univ _, w', hw', hz⟩)) (not_le.2 hlt)
      rw [e, hdec _ _ _ hb hi, hz, mul_zero]
    · exfalso
      apply h
      rw [e, hdec _ _ _ hb hi, isPermW_unique hw' hw, hx,
        chiDeltaU_congr q α (b' := w * t * w⁻¹) fun a => by rw [hord, hsd]]
  have h1 : φ (w * 1 * t) = x := by
    have e : w * 1 * t = (w * t * w⁻¹) * w := by group
    rw [e, hB _ _ hsB]
  have hsum := congrFun h0 w
  simp only [aOp, Pi.zero_apply] at hsum
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : (R.filter fun r => φ (w * r * t) = x).card ≠ 0 :=
    Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨h1R, h1⟩)
  exact (mul_ne_zero (Nat.cast_ne_zero.2 hc) hx0) hsum

def iwFix (σ : L →+* L) (n : ℕ) (q : ℕ) (α : Fin (n / 2) → ℂˣ) : Submodule ℂ (GU σ n → ℂ) where
  carrier := {φ | φ ∈ psSpaceU σ q α ∧ ∀ g, ∀ i ∈ IwU σ n, φ (g * i) = φ g}
  add_mem' h h' := ⟨add_mem h.1 h'.1, fun g i hi => by simp [h.2 g i hi, h'.2 g i hi]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ _ => rfl⟩
  smul_mem' c _ h := ⟨Submodule.smul_mem _ c h.1, fun g i hi => by simp [h.2 g i hi]⟩

theorem finiteDimensional_iwFix (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (q : ℕ)
    (α : Fin (n / 2) → ℂˣ) : FiniteDimensional ℂ (iwFix σ n q α) := by
  classical
  let wOf : Equiv.Perm (Fin n) → GU σ n := fun π => if h : ∃ w : GU σ n, IsPermW w π then h.choose else 1
  have hwOf : ∀ (w : GU σ n) π, IsPermW w π → wOf π = w := fun w π hw => by
    have h : ∃ w : GU σ n, IsPermW w π := ⟨w, hw⟩
    simp only [wOf, dif_pos h]
    exact isPermW_unique h.choose_spec hw
  let F : iwFix σ n q α →ₗ[ℂ] (Equiv.Perm (Fin n) → ℂ) :=
    { toFun := fun φ π => (φ : GU σ n → ℂ) (wOf π)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective F ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro φ hφ
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨b, w, i, π, hb, hw, hi, rfl⟩ := GlobalTheory.T.unitary_iwasawa_bruhat_decomposition L σ n hσ hσv g
  have h1 : (φ : GU σ n → ℂ) w = 0 := by
    have := congrFun hφ π
    rwa [show F φ π = (φ : GU σ n → ℂ) (wOf π) from rfl, hwOf w π hw] at this
  have h2 := φ.2.2 (b * w) i hi
  have h3 := φ.2.1 b w hb
  show (φ : GU σ n → ℂ) (b * w * i) = 0
  rw [h2, h3, h1, mul_zero]

end U

theorem satPowNonvan : PositivityTheory.SphericalProduct.SatPowNonvan := by
  intro L _ _ _ ϖ σ q n hU α t htD htS j₀
  have hσ := hU.1
  have hσv := hU.2.1
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hα : ∀ i, (fun i => (α i : ℂ)) i ≠ 0 := fun i => (α i).ne_zero
  obtain ⟨hKI, hYI⟩ := GlobalTheory.T.unitary_iwahori_index_finite L ϖ σ q n hU
  obtain ⟨R, h1R, hRP, hR⟩ := GlobalTheory.T.coset_reps_of_factorization (GU σ n) (IwU σ n) t (fun u => u ∈ IwU σ n ∧ IsUnipU u)
    ⟨one_mem _, isBorelU_one, fun i => by simp⟩ (hYI t) (fun i hi => by
      obtain ⟨u, hu, hu', y, hy, hy', e⟩ := GlobalTheory.T.unitary_iwahori_factorization L σ n hσ hσv t htD htS i hi
      exact ⟨u, hu, ⟨hu, hu'⟩, y, hy, hy', e⟩)
  have hRI : ∀ r ∈ R, r ∈ IwU σ n := fun r hr => (hRP r hr).1
  have hRt : ∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ KU σ n := fun r hr k =>
    GlobalTheory.T.dominant_conjugate_unipotent_mem L σ n t r htD htS (hRP r hr).1 (hRP r hr).2.2 k
  obtain ⟨φ₀, hsph, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega) (fun i => (α i : ℂ)) hα
  have hIK := GlobalTheory.CompanionTheory.KUFactsU.iwU_le_KU σ n
  have hK : ∀ g, ∀ k ∈ KU σ n, φ₀ (g * k) = φ₀ g := fun g k hk => by
    simpa [chiDeltaU_one] using hsph 1 g k isBorelU_one hk
  have hφ₀ : φ₀ ∈ iwFix σ n q α :=
    ⟨fun b g hb => by simpa using hsph b g 1 hb (one_mem _), fun g i hi => hK g i (hIK hi)⟩
  haveI := finiteDimensional_iwFix hσ hσv q α
  exact abs_main (KU σ n) (IwU σ n) hIK hKI t R h1R hRI hRt hR (iwFix σ n q α)
    (fun φ hφ => ⟨fun b g hb => by
        show aOp R t φ (b * g) = _ * aOp R t φ g
        simp only [aOp, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [mul_assoc b, mul_assoc b, hφ.1 b _ hb], aOp_rightInv _ t R hRI hR φ hφ.2⟩)
    (fun φ hφ h0 => aOp_inj q hq _ hα hσ hσv t htD htS R h1R hRI φ hφ.1 hφ.2 h0)
    φ₀ hφ₀ hK h1 (fun j => SatU ϖ q (dosetInd ℂ (KU σ n) (t ^ j)) (fun i => (α i : ℂ)))
    (fun j => by
      have e := Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega) _ hα
        (dosetInd ℂ (KU σ n) (t ^ j)) (Final.DosetIndMem _ (KU σ n) ℂ _) φ₀ hsph
      have := congrFun e 1
      simpa [h1] using this) j₀

end GlobalTheory.CompanionTheory.SatPow

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakePowerNonvanishingStatement
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_power_nonvanishing : PositivityTheory.SphericalProduct.SatPowNonvan := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.satPowNonvan | exact GlobalTheory.CompanionTheory.SatPow.satPowNonvan | (intros; apply GlobalTheory.CompanionTheory.SatPow.satPowNonvan <;> assumption)
end
