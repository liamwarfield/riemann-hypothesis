module

public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DoubleCosetSeparation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintSph
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CharacterEigenspaceAddMem
open scoped Classical

theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux1 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) {a b : V},
      a ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        b ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
          ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (a + b) = (↑((χ : ↥H → kˣ) h) : k) • (a + b) := by
  intro k G V _ _ _ _ ρ H χ a b ha hb h
  rw [map_add (f := _), ha h, hb h, smul_add]

theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux2 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (h : ↥H),
      ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (0 : V) = (↑((χ : ↥H → kˣ) h) : k) • (0 : V) := by
  intro k G V _ _ _ _ ρ H χ h
  rw [map_zero, smul_zero]

theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux3 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (c : k) {v : V},
      v ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (c • v) = (↑((χ : ↥H → kˣ) h) : k) • c • v := by
  intro k G V _ _ _ _ ρ H χ c v hv h
  rw [map_smul, hv h, smul_comm]

noncomputable def UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.eig :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (H : Subgroup G) → (↥H →* kˣ) → Submodule k V :=
    fun {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
        (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) ↦
      { carrier := {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v},
        add_mem' := @UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux1 k G V inst inst_1 inst_2 inst_3 ρ H χ, zero_mem' := UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux2 ρ H χ,
        smul_mem' := UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux3 ρ H χ : Submodule k V }

noncomputable def UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → Representation k G V → Subgroup G → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V)
        (H : Subgroup G) ↦
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.eig ρ H (1 : ↥H →* kˣ)

noncomputable def UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp :
    {G : Type} →
      [inst : Group G] →
        {V : Type} →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module ℂ V] →
              Representation ℂ G V → Subgroup G → Subgroup G → (G → ℂ) → (V →ₗ[ℂ] V) → V →ₗ[ℂ] V :=
    fun {G : Type} [Group G] {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ G V) (K K' : Subgroup G)
        (f : G → ℂ) (A : V →ₗ[ℂ] V) ↦
      (↑(K'.relIndex K) : ℂ)⁻¹ • ∑ᶠ (q : G ⧸ K'), f (Quotient.out q) • (ρ : G → V →ₗ[ℂ] V) (Quotient.out q) ∘ₗ A

noncomputable def UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.twTr :
    {G : Type} →
      [inst : Group G] →
        {V : Type} →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → Subgroup G → Subgroup G → (G → ℂ) → (V →ₗ[ℂ] V) → ℂ :=
    fun {G : Type} [Group G] {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ G V) (K K' : Subgroup G)
        (f : G → ℂ) (A : V →ₗ[ℂ] V) ↦
      if h :
          ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ K', (UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K K' f A : V → V) v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ K' then
        (LinearMap.trace ℂ ↥(UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ K') :
            (↥(UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ K') →ₗ[ℂ] ↥(UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ K')) → ℂ)
          ((UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K K' f A).restrict h)
      else (0 : ℂ)

theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux11 :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) {a b : H},
      a ∈ {k : H | ∀ (x : H), u (x * k) = u x} → b ∈ {k : H | ∀ (x : H), u (x * k) = u x} → ∀ (x : H), u (x * (a * b)) = u x := by
  intro H _ u a b ha hb x
  rw [← mul_assoc, hb, ha]

theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux12 :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) (a : H), u (a * (1 : H)) = u a := by
  intro H _ u a
  rw [mul_one]

theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.algebra_smulCommClass_complex :
    ∀ {H : Type} [inst : Group H] (u : H → ℂ) {a : H},
      a ∈ {k : H | ∀ (x : H), u (x * k) = u x} → ∀ (x : H), u (x * a⁻¹) = u x := by
  intro H _ u a ha x
  have := ha (x * a⁻¹)
  rw [← this, inv_mul_cancel_right]

noncomputable def UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.rStab :
    {H : Type} → [inst : Group H] → (H → ℂ) → Subgroup H :=
    fun {H : Type} [inst : Group H] (u : H → ℂ) ↦
      { carrier := {k : H | ∀ (x : H), u (x * k) = u x}, mul_mem' := @UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux11 H inst u,
        one_mem' := UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.aux12 u, inv_mem' := @UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.algebra_smulCommClass_complex H inst u : Subgroup H }

noncomputable def UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trc :
    {G V : Type} →
      [inst : Group G] →
        [inst_1 : AddCommGroup V] → [inst_2 : _root_.Module ℂ V] → Representation ℂ G V → Subgroup G → (G → ℂ) → ℂ :=
    fun {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
        (f : G → ℂ) ↦
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.twTr ρ K (K ⊓ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.rStab f ⊓ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.rStab fun (y : G) ↦ f y⁻¹) f LinearMap.id

private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.mem_fixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ H ↔ ∀ a ∈ H, ρ a v = v := by
  constructor
  · intro hv a ha
    simpa using hv ⟨a, ha⟩
  · intro hv a
    simpa using hv a a.2

private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.supp_finite {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G)) {C : Set G} (hC : IsCompact C)
    (f : G → ℂ) (hf : ∀ y, f y ≠ 0 → y ∈ C) :
    (Function.support fun q : G ⧸ H ↦ f (Quotient.out q)).Finite := by
  haveI : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  refine (hC.image (QuotientGroup.continuous_mk (N := H))).finite_of_discrete.subset ?_
  intro q hq
  exact ⟨_, hf _ hq, QuotientGroup.out_eq' q⟩

private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.relIndex_ne {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K I : Subgroup G) (hK : IsCompact (K : Set G))
    (hI : IsOpen (I : Set G)) : I.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have h : IsOpen ((I.subgroupOf K : Subgroup K) : Set K) := hI.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ h
  exact Subgroup.index_ne_zero_of_finite

private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.out_mk {G M : Type} [Group G] (H : Subgroup G) (F : G → M)
    (hF : ∀ a ∈ H, ∀ y, F (y * a) = F y) (g : G) :
    F (Quotient.out (QuotientGroup.mk g : G ⧸ H)) = F g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hF _ h.2]

private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.finsum_le {G M : Type} [Group G] [AddCommMonoid M] {I J : Subgroup G}
    (hIJ : I ≤ J) (hne : I.relIndex J ≠ 0) (F : G → M) (hF : ∀ a ∈ J, ∀ y, F (y * a) = F y)
    (hs : (Function.support fun q : G ⧸ J ↦ F (Quotient.out q)).Finite) :
    ∑ᶠ q : G ⧸ I, F (Quotient.out q) = I.relIndex J • ∑ᶠ q : G ⧸ J, F (Quotient.out q) := by
  haveI : Finite (J ⧸ I.subgroupOf J) := Nat.finite_of_card_ne_zero hne
  haveI := Fintype.ofFinite (J ⧸ I.subgroupOf J)
  have key : ∀ q : G ⧸ I, F (Quotient.out q) =
      F (Quotient.out (Subgroup.quotientEquivProdOfLE hIJ q).1) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.out_mk I F (fun a ha ↦ hF a (hIJ ha))]
      exact (UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.out_mk J F hF g).symm
  rw [finsum_congr key, finsum_comp_equiv (Subgroup.quotientEquivProdOfLE hIJ)
    (f := fun p ↦ F (Quotient.out p.1)), finsum_curry _
      ((hs.prod Set.finite_univ).subset (fun p hp ↦ ⟨hp, trivial⟩)), smul_finsum' _ hs]
  refine finsum_congr fun q ↦ ?_
  rw [finsum_eq_sum_of_fintype]
  simp [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.term_inv {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (H : Subgroup G) (f : G → ℂ) (hf : ∀ a ∈ H, ∀ y, f (y * a) = f y)
    {v : V} (hv : v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ H) :
    ∀ a ∈ H, ∀ y, f (y * a) • ρ (y * a) v = f y • ρ y v := by
  intro a ha y
  rw [hf a ha, map_mul, Module.End.mul_apply, (UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.mem_fixed ρ H v).1 hv a ha]

private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_apply {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K H : Subgroup G) (f : G → ℂ)
    (hs : (Function.support fun q : G ⧸ H ↦ f (Quotient.out q)).Finite) (v : V) :
    UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K H f LinearMap.id v =
      (H.relIndex K : ℂ)⁻¹ • ∑ᶠ q : G ⧸ H, f (Quotient.out q) • ρ (Quotient.out q) v := by
  unfold UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp
  rw [LinearMap.smul_apply]
  congr 1
  exact (LinearMap.applyₗ (R := ℂ) (M₂ := V) v).toAddMonoidHom.map_finsum
    (hs.subset fun q hq h0 ↦ hq (by simp only [show f (Quotient.out q) = 0 from h0, zero_smul]))

private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_mem {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K H J : Subgroup G) (f : G → ℂ)
    (hs : (Function.support fun q : G ⧸ H ↦ f (Quotient.out q)).Finite)
    (hr : ∀ a ∈ H, ∀ y, f (y * a) = f y) (hl : ∀ a ∈ J, ∀ y, f (a * y) = f y) :
    ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ H,
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K H f LinearMap.id v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J := by
  intro v hv
  rw [UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_apply ρ K H f hs]
  refine Submodule.smul_mem _ _ ((UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.mem_fixed ρ J _).2 fun a ha ↦ ?_)
  have h1 := (ρ a).toAddMonoidHom.map_finsum
    (f := fun q : G ⧸ H ↦ f (Quotient.out q) • ρ (Quotient.out q) v)
    (hs.subset (Function.support_smul_subset_left _ _))
  refine h1.trans ?_
  rw [← finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ H))
    (f := fun q : G ⧸ H ↦ f (Quotient.out q) • ρ (Quotient.out q) v)]
  refine finsum_congr fun q ↦ ?_
  rw [MulAction.toPerm_apply, ← MulAction.Quotient.mk_smul_out,
    UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.out_mk H (fun g ↦ f g • ρ g v) (UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.term_inv ρ H f hr hv)]
  simp [hl a ha]

private theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trace_le {V : Type} [AddCommGroup V] [Module ℂ V]
    {P Q : Submodule ℂ V} [FiniteDimensional ℂ Q] (hle : P ≤ Q) (T : V →ₗ[ℂ] V)
    (h : ∀ v ∈ Q, T v ∈ P) :
    LinearMap.trace ℂ P (T.restrict fun v hv ↦ h v (hle hv)) =
      LinearMap.trace ℂ Q (T.restrict fun v hv ↦ hle (h v hv)) := by
  haveI : FiniteDimensional ℂ P := Submodule.finiteDimensional_of_le hle
  exact LinearMap.trace_comp_comm' (Submodule.inclusion hle) (T.restrict h)

theorem UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trc_eq :
    ∀ {G V : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (K I : Subgroup G),
      IsOpen (↑K : Set G) →
        IsCompact (↑K : Set G) →
          IsOpen (↑I : Set G) →
            IsCompact (↑I : Set G) →
              I ≤ K →
                ∀ (x : G) (f : G → ℂ),
                  (∀ (y : G), f y = if ∃ a ∈ I, ∃ b ∈ I, y = a * x * b then (1 : ℂ) else (0 : ℂ)) →
                    FiniteDimensional ℂ ↥(UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I) →
                      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trc ρ K f = UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.twTr ρ K I f LinearMap.id := by
  intro G V _ _ _ _ _ ρ K I hKo hKc hIo hIc hIK x f hf hfd
  have hr : ∀ a ∈ I, ∀ y, f (y * a) = f y := by
    intro a ha y
    rw [hf, hf]
    refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro ⟨c, hc, b, hb, h⟩
      exact ⟨c, hc, b * a⁻¹, I.mul_mem hb (I.inv_mem ha), by rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
    · rintro ⟨c, hc, b, hb, h⟩
      exact ⟨c, hc, b * a, I.mul_mem hb ha, by rw [← mul_assoc, ← h]⟩
  have hl : ∀ a ∈ I, ∀ y, f (a * y) = f y := by
    intro a ha y
    rw [hf, hf]
    refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro ⟨c, hc, b, hb, h⟩
      refine ⟨a⁻¹ * c, I.mul_mem (I.inv_mem ha) hc, b, hb, ?_⟩
      rw [mul_assoc a⁻¹, mul_assoc a⁻¹, ← h, inv_mul_cancel_left]
    · rintro ⟨c, hc, b, hb, h⟩
      refine ⟨a * c, I.mul_mem ha hc, b, hb, ?_⟩
      rw [h, mul_assoc a, mul_assoc a]
  have hC : IsCompact ((fun p : G × G ↦ p.1 * x * p.2) '' ((I : Set G) ×ˢ (I : Set G))) :=
    (hIc.prod hIc).image (by fun_prop)
  have hsupp : ∀ y, f y ≠ 0 → y ∈ ((fun p : G × G ↦ p.1 * x * p.2) '' ((I : Set G) ×ˢ (I : Set G))) := by
    intro y hy
    rw [hf] at hy
    split_ifs at hy with h
    · obtain ⟨a, ha, b, hb, h⟩ := h
      exact ⟨(a, b), ⟨ha, hb⟩, h.symm⟩
    · exact absurd rfl hy
  unfold UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trc
  set J : Subgroup G := K ⊓ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.rStab f ⊓ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.rStab fun (y : G) ↦ f y⁻¹ with hJ
  have hIJ : I ≤ J := by
    intro a ha
    refine ⟨⟨hIK ha, fun y ↦ hr a ha y⟩, fun y ↦ ?_⟩
    show f (y * a)⁻¹ = f y⁻¹
    rw [mul_inv_rev, hl _ (I.inv_mem ha)]
  have hJK : J ≤ K := fun a ha ↦ ha.1.1
  have hJr : ∀ a ∈ J, ∀ y, f (y * a) = f y := fun a ha y ↦ ha.1.2 y
  have hJl : ∀ a ∈ J, ∀ y, f (a * y) = f y := by
    intro a ha y
    have h : f (y⁻¹ * a⁻¹)⁻¹ = f y⁻¹⁻¹ := (J.inv_mem ha).2 y⁻¹
    simpa using h
  have hJo : IsOpen (J : Set G) := Subgroup.isOpen_mono hIJ hIo
  have hsI := UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.supp_finite I hIo hC f hsupp
  have hsJ := UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.supp_finite J hJo hC f hsupp
  have hne : I.relIndex K ≠ 0 := UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.relIndex_ne K I hKc hIo
  have hmul : I.relIndex J * J.relIndex K = I.relIndex K := Subgroup.relIndex_mul_relIndex I J K hIJ hJK
  have hne1 : I.relIndex J ≠ 0 := left_ne_zero_of_mul (hmul ▸ hne)
  have hle : UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J ≤ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I := by
    intro v hv
    rw [UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.mem_fixed] at hv ⊢
    exact fun a ha ↦ hv a (hIJ ha)
  have h1 : ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I,
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K I f LinearMap.id v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J :=
    UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_mem ρ K I J f hsI hr hJl
  have h2 : ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J,
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K J f LinearMap.id v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J :=
    UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_mem ρ K J J f hsJ hJr hJl
  have h3 : ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I,
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K I f LinearMap.id v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ I :=
    fun v hv ↦ hle (h1 v hv)
  have h4 : ∀ v ∈ UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.fixed ρ J,
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K I f LinearMap.id v = UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp ρ K J f LinearMap.id v := by
    intro v hv
    rw [UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_apply ρ K I f hsI, UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.levOp_apply ρ K J f hsJ,
      UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.finsum_le hIJ hne1 (fun g ↦ f g • ρ g v)
        (UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.term_inv ρ J f hJr hv)
        (hsJ.subset (Function.support_smul_subset_left _ _)), ← hmul,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    have : (I.relIndex J : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne1
    push_cast
    field_simp
  unfold UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.twTr
  rw [dite_eq_left h2, dite_eq_left h3, ← UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trace_le hle _ h1]
  congr 1
  ext v
  exact (h4 v v.2).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.DcosSep
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm


end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.dcosSep :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.DcosSep :=
  _root_.UpperTheory.Reformulated.B.DoubleCosetSeparation.dcosSep
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.DcosTr
noncomputable section

open GlobalTheory.PRep GlobalTheory.BCT UpperTheory.V.Hi UpperTheory.V.AlgebraTools

open NumberField IsDedekindDomain Formalism.UG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

private theorem psum_ne (Z : Multiset ℂ) (hZ : Z ≠ 0) (h0 : (0 : ℂ) ∉ Z) :
    ∃ j : ℕ, 1 ≤ j ∧ (Z.map (· ^ j)).sum ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨z₀, hz₀⟩ := Multiset.exists_mem_of_ne_zero hZ
  set S := Z.toFinset with hS
  let Q : Polynomial ℂ := Polynomial.X * ∏ z ∈ S.erase z₀, (Polynomial.X - Polynomial.C z)
  have hp : ∀ j, 1 ≤ j → ∑ a ∈ S, (Z.count a : ℂ) * a ^ j = 0 := fun j hj => by
    have := hcon j hj
    rw [Finset.sum_multiset_map_count] at this
    simpa [nsmul_eq_mul] using this
  have hq0 : Q.coeff 0 = 0 := by simp [Q, Polynomial.mul_coeff_zero]
  have h1 : ∑ a ∈ S, (Z.count a : ℂ) * Q.eval a = 0 := by
    have : ∀ a, Q.eval a = ∑ j ∈ Q.support, Q.coeff j * a ^ j := fun a => by
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp_rw [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [hq0]
    · calc _ = Q.coeff j * ∑ a ∈ S, (Z.count a : ℂ) * a ^ j := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
        _ = 0 := by rw [hp j hj, mul_zero]
  have h2 : ∑ a ∈ S, (Z.count a : ℂ) * Q.eval a = (Z.count z₀ : ℂ) * Q.eval z₀ := by
    refine Finset.sum_eq_single_of_mem z₀ (Multiset.mem_toFinset.2 hz₀) fun a ha hne => ?_
    have : Q.eval a = 0 := by
      simp only [Q, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_C]
      rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne, ha⟩) (sub_self a), mul_zero]
    rw [this, mul_zero]
  rw [h2] at h1
  have hc : (Z.count z₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Multiset.count_ne_zero.2 hz₀)
  have hQ : Q.eval z₀ ≠ 0 := by
    simp only [Q, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_C]
    refine mul_ne_zero (fun h => h0 (h ▸ hz₀)) (Finset.prod_ne_zero_iff.2 fun a ha => sub_ne_zero.2 (Finset.ne_of_mem_erase ha).symm)
  exact mul_ne_zero hc hQ h1

private theorem exists_pow_trace {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (T : Module.End ℂ W) (hT : IsUnit T) : ∃ j : ℕ, 1 ≤ j ∧ LinearMap.trace ℂ W (T ^ j) ≠ 0 := by
  obtain ⟨u, rfl⟩ := hT
  let R : Representation ℂ (Multiplicative ℤ) W := (Units.coeHom _).comp (zpowersHom _ u)
  obtain ⟨E, -, hE⟩ := GlobalTheory.IwahoriTraceProof.exists_exponents (G := Multiplicative ℤ) _ W R rfl
  have hR : ∀ j : ℕ, R (Multiplicative.ofAdd 1 ^ j) = (u : Module.End ℂ W) ^ j := fun j => by
    rw [map_pow]
    congr 1
  let Z : Multiset ℂ := E.map fun χ => ((χ (Multiplicative.ofAdd 1) : ℂˣ) : ℂ)
  have hcard : (Module.finrank ℂ W : ℂ) = (E.card : ℂ) := by
    have h1 := hE 1
    rw [map_one, Module.End.one_eq_id, LinearMap.trace_id] at h1
    rw [h1]
    simp
  have hZ : Z ≠ 0 := by
    intro h
    have hE0 : E = 0 := by simpa [Z] using h
    rw [hE0] at hcard
    have : Module.finrank ℂ W = 0 := by exact_mod_cast hcard
    exact Module.finrank_pos.ne' this
  have h0 : (0 : ℂ) ∉ Z := by
    intro h
    obtain ⟨χ, -, h⟩ := Multiset.mem_map.1 h
    exact (χ (Multiplicative.ofAdd 1)).ne_zero h
  obtain ⟨j, hj, hne⟩ := psum_ne Z hZ h0
  refine ⟨j, hj, fun h => hne ?_⟩
  rw [← hR, hE] at h
  rw [← h, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun χ _ => ?_
  simp

section Abs

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem fixed_eq (ρ : Representation ℂ G V) (I : Subgroup G) : fixed ρ I = fixd ρ I := by
  ext v
  rw [GlobalTheory.TwTrLevel.mem_fixed_iff]
  rfl

private theorem mem_orbit (I : Subgroup G) (x g : G) :
    (g : G ⧸ I) ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, ∃ b ∈ I, g = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have ha' : (((a : G) * x : G) : G ⧸ I) = g := ha
    exact ⟨a, a.2, _, QuotientGroup.eq.1 ha', by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    change ((a * x : G) : G ⧸ I) = _
    exact (QuotientGroup.mk_mul_of_mem _ hb).symm

open scoped Classical in
private theorem levOp_eq (ρ : Representation ℂ G V) (K I : Subgroup G) (x : G) (hx : FinOrb I I x) (f : G → ℂ)
    (hf : ∀ y, f y = if ∃ a ∈ I, ∃ b ∈ I, y = a * x * b then 1 else 0) (v : fixd ρ I) :
    levOp ρ K I f LinearMap.id (v : V) = ((I.relIndex K : ℕ) : ℂ)⁻¹ • (hk ρ I x v : V) := by
  have hx' : (MulAction.orbit I (x : G ⧸ I)).Finite := hx
  have h1 : (hk ρ I x v : V) = ∑ q ∈ hx'.toFinset, ρ q.out v := by
    rw [hk, (hkApply ℂ G V ρ I I x hx).1 v, UpperTheory.V.Hi.dc,
      finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ I => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ hx',
      LinearMap.sum_apply]
  have hmem : ∀ q : G ⧸ I, q ∈ MulAction.orbit I (x : G ⧸ I) ↔ ∃ a ∈ I, ∃ b ∈ I, q.out = a * x * b := fun q => by
    rw [← mem_orbit, QuotientGroup.out_eq']
  have h2 : (∑ᶠ q : G ⧸ I, f q.out • (ρ q.out ∘ₗ LinearMap.id)) = ∑ q ∈ hx'.toFinset, ρ q.out := by
    rw [finsum_eq_sum_of_support_subset (s := hx'.toFinset)]
    · refine Finset.sum_congr rfl fun q hq => ?_
      rw [hf, if_pos ((hmem q).1 (hx'.mem_toFinset.1 hq)), one_smul]
      rfl
    · intro q hq
      rw [Finset.mem_coe, hx'.mem_toFinset, hmem]
      by_contra hn
      exact hq (by show f q.out • _ = 0; rw [hf, if_neg hn, zero_smul])
  unfold levOp
  rw [h2, h1, LinearMap.smul_apply, LinearMap.sum_apply]

private theorem trace_move {M M' : Submodule ℂ V} (h : M = M') (L : V →ₗ[ℂ] V) (hL : ∀ v ∈ M, L v ∈ M)
    (B : Module.End ℂ M') (hB : ∀ v : M', L v = B v) :
    LinearMap.trace ℂ M (L.restrict hL) = LinearMap.trace ℂ M' B := by
  subst h
  congr 1
  ext v
  exact hB v

open scoped Classical in
private theorem twTr_eq (ρ : Representation ℂ G V) (K I : Subgroup G) (x : G) (hx : FinOrb I I x) (f : G → ℂ)
    (hf : ∀ y, f y = if ∃ a ∈ I, ∃ b ∈ I, y = a * x * b then 1 else 0) :
    twTr ρ K I f LinearMap.id = ((I.relIndex K : ℕ) : ℂ)⁻¹ * LinearMap.trace ℂ (fixd ρ I) (hk ρ I x) := by
  have hst : ∀ v ∈ fixed ρ I, levOp ρ K I f LinearMap.id v ∈ fixed ρ I := fun v hv => by
    rw [fixed_eq] at hv ⊢
    rw [levOp_eq ρ K I x hx f hf ⟨v, hv⟩]
    exact Submodule.smul_mem _ _ (hk ρ I x ⟨v, hv⟩).2
  unfold twTr
  rw [dite_eq_left hst, trace_move (fixed_eq ρ I) _ hst (((I.relIndex K : ℕ) : ℂ)⁻¹ • hk ρ I x)
    fun v => levOp_eq ρ K I x hx f hf v, map_smul, smul_eq_mul]

end Abs

section Lev

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

open scoped Classical in
private theorem trc_eq (ρ : Representation ℂ G V) (K I : Subgroup G) (hKo : IsOpen (K : Set G))
    (hKc : IsCompact (K : Set G)) (hIo : IsOpen (I : Set G)) (hIc : IsCompact (I : Set G)) (hIK : I ≤ K) (x : G)
    (f : G → ℂ) (hf : ∀ y, f y = if ∃ a ∈ I, ∃ b ∈ I, y = a * x * b then 1 else 0)
    (hfd : FiniteDimensional ℂ (fixed ρ I)) :
    trc ρ K f = twTr ρ K I f LinearMap.id :=
  _root_.UpperTheory.Reformulated.B.trace_eq_twisted_trace_of_fixed.trc_eq ρ K I hKo hKc hIo hIc hIK x f hf hfd

end Lev

section Loc

open ValuativeRel GlobalTheory.SmGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem dom_pow {ϖ : kˣ} (hϖ : valuation k (ϖ : k) < 1) {a : Fin n → ℤ} (ha : Antitone a) :
    Dom fun i => ϖ ^ a i := by
  intro i j hij
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact (zpow_le_zpow_iff_right_of_lt_one₀ h0 hϖ).2 (ha hij)

private theorem exists_hk_trace {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
    {I : Subgroup (GL (Fin n) k)} (hI : iwC k n ⊤ = I) [FiniteDimensional ℂ (fixd ρ I)] [Nontrivial (fixd ρ I)]
    {ϖ : kˣ} (hϖ : valuation k (ϖ : k) < 1) :
    ∃ x : Fin n → ℤ, StrictAnti x ∧
      LinearMap.trace ℂ (fixd ρ I) (hk ρ I (diagT k (Fin n) fun i => ϖ ^ x i)) ≠ 0 := by
  subst hI
  obtain ⟨hmul, hunit, -⟩ := domMul k n ⊤ ℂ V ρ
  have hq : IsUnit ((GlobalTheory.SplitWeil.resCard k : ℕ) : ℂ) :=
    (Nat.cast_ne_zero.2 (GlobalTheory.SplitWeil.one_lt_resCard k).ne_bot).isUnit
  let x₀ : Fin n → ℤ := fun i => -(i : ℤ)
  have hx₀ : StrictAnti x₀ := fun a b h => by
    have : (a : ℤ) < b := by exact_mod_cast h
    simp only [x₀]
    omega
  let T := hk ρ (iwC k n ⊤) (diagT k (Fin n) fun i => ϖ ^ x₀ i)
  have hT : IsUnit T := hunit hq _ (dom_pow hϖ hx₀.antitone)
  have hsa : ∀ j : ℕ, 1 ≤ j → StrictAnti (j • x₀) := fun j hj a b h => by
    have h1 := hx₀ h
    simp only [Pi.smul_apply, nsmul_eq_mul]
    exact mul_lt_mul_of_pos_left h1 (by exact_mod_cast hj)
  have hpow : ∀ j : ℕ, hk ρ (iwC k n ⊤) (diagT k (Fin n) fun i => ϖ ^ ((j + 1) • x₀) i) = T ^ (j + 1) := by
    intro j
    induction j with
    | zero => simp [T]
    | succ j ih =>
      rw [pow_succ, ← ih]
      show _ = hk ρ (iwC k n ⊤) _ * hk ρ (iwC k n ⊤) _
      rw [hmul _ _ (dom_pow hϖ (hsa _ (by omega)).antitone) (dom_pow hϖ hx₀.antitone)]
      congr 2
      congr 1
      funext i
      simp only [Pi.mul_apply, Pi.smul_apply, nsmul_eq_mul, ← zpow_add]
      congr 1
      push_cast
      ring
  obtain ⟨j, hj, hne⟩ := exists_pow_trace T hT
  obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  refine ⟨(j + 1) • x₀, hsa _ hj, ?_⟩
  rw [hpow]
  exact hne

end Loc

private theorem v_lt_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x : L} (h : Formalism.UG.ordL x = 1) :
    Valued.v x < 1 := by
  unfold Formalism.UG.ordL at h
  split_ifs at h with h0
  · exact absurd h (by norm_num)
  · have h1 : Multiplicative.toAdd (WithZero.unzero h0) = -1 := by omega
    have h2 : WithZero.unzero h0 < 1 := by
      show Multiplicative.toAdd (WithZero.unzero h0) < (0 : ℤ)
      omega
    rw [← WithZero.coe_unzero h0]
    exact_mod_cast h2

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

open ValuativeRel GlobalTheory.SmGL GlobalTheory.LFun in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.dcosTr :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.DcosTr := by
  classical
  intro E _ _ _ n w ϖ hϖ τ hτ
  let I := iwGL n w
  have hI : iwC (w.adicCompletion E) n ⊤ = I := (memIwC (w.adicCompletion E) n ⊤).2.1
  have hIo : IsOpen (I : Set (GLw n w)) := GroundTheory.Automorphic.GLnLocal.isOpen_iwahori _ _
  have hIc : IsCompact (I : Set (GLw n w)) := GroundTheory.Automorphic.GLnLocal.isCompact_iwahori _ _
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hIK : I ≤ KGL w n := GlobalTheory.CompanionTheory.IwLevels.iwGL_le_KGL w n
  have hfd : FiniteDimensional ℂ (fixed τ.ρ I) :=
    (PositivityTheory.PfBern.Props1.irrSmoothAdmissible_holds _ _ _ τ.ρ τ.smooth τ.irred).2 _ hIo hIc
  haveI hfd' : FiniteDimensional ℂ (UpperTheory.V.Hi.fixd τ.ρ I) := by
    rw [← fixed_eq]
    exact hfd
  haveI hnt : Nontrivial (UpperTheory.V.Hi.fixd τ.ρ I) := by
    rw [Submodule.nontrivial_iff_ne_bot, ← fixed_eq]
    intro hb
    refine hτ (eq_bot_iff.2 fun v hv => ?_)
    have hvI : v ∈ fixed τ.ρ I := by
      rw [GlobalTheory.TwTrLevel.mem_fixed_iff] at hv ⊢
      exact fun k hk => hv k (hIK hk)
    rw [hb] at hvI
    exact hvI
  have hv : valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) < 1 :=
    GlobalTheory.CjInv.lt_one_iff _ |>.2 (v_lt_one hϖ)
  obtain ⟨x, hx, hne⟩ := exists_hk_trace τ.ρ hI hv
  refine ⟨x, hx, ?_⟩
  have hfx : ∀ y, dcos n w (tdiag ϖ x) y = if ∃ a ∈ I, ∃ b ∈ I, y = a * tdiag ϖ x * b then 1 else 0 := fun y => rfl
  have hfin : UpperTheory.V.AlgebraTools.FinOrb I I (tdiag ϖ x) := by
    rw [← hI]
    exact (heckePairIwC (w.adicCompletion E) n ⊤).1 _
  rw [trc_eq τ.ρ (KGL w n) I hKo hKc hIo hIc hIK _ _ hfx hfd, twTr_eq τ.ρ _ I _ hfin _ hfx]
  refine mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 ?_)) hne
  haveI := GlobalTheory.TwTrLevel.finite_quot (KGL w n) (KGL w n) I hKc hKo hIo le_rfl
  exact Subgroup.index_ne_zero_of_finite
end
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT

private theorem exists_unit_ordL_eq_one {E : Type} [Field E] [NumberField E] (w : Pl E) :
    ∃ ϖ : (w.adicCompletion E)ˣ, ordL (ϖ : w.adicCompletion E) = 1 := by
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have hv : Valued.v (algebraMap E (w.adicCompletion E) π) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w π).trans hπ
  have h0 : algebraMap E (w.adicCompletion E) π ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  exact ⟨Units.mk0 _ h0, GlobalTheory.GramParity.ordL_eq_of h0 hv⟩

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.regFn :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.RegFn := by
  intro E _ _ _ n w τ B h
  obtain ⟨ϖ, hϖ⟩ := exists_unit_ordL_eq_one w
  obtain ⟨x, hx, htr⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.dcosTr E n w ϖ hϖ τ h.1
  obtain ⟨hL, hS⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.dcosSep E n w ϖ hϖ x hx
  exact ⟨_, hL, htr, hS⟩
