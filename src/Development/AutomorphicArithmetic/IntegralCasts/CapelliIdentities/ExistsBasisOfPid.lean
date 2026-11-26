module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsBasisOfPid
theorem UpperTheory.Reformulated.B.Qi33.aux1.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  intro R _ W _ _ S L x y hx hy
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨t, ht, hy⟩ := hy
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  rw [smul_add]
  refine L.add_mem ?_ ?_
  · rw [mul_comm, mul_smul]
    exact L.smul_mem t hx
  · rw [mul_smul]
    exact L.smul_mem s hy

theorem UpperTheory.Reformulated.B.Qi33.aux2.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by simp⟩

theorem UpperTheory.Reformulated.B.Qi33.aux3.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  intro R _ W _ _ S L r x hx
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem r hx

noncomputable def UpperTheory.Reformulated.B.Qi33.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @UpperTheory.Reformulated.B.Qi33.aux1 R inst W inst_1 inst_2 S L,
        zero_mem' := UpperTheory.Reformulated.B.Qi33.aux2 S L, smul_mem' := UpperTheory.Reformulated.B.Qi33.aux3 S L : Submodule R W }

noncomputable def UpperTheory.Reformulated.B.Qi33.localization₂.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] →
            [inst_2 : _root_.Module R W] → (p : Ideal R) → [p.IsPrime] → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [CommRing R] {W : Type u_4} [AddCommGroup W] [_root_.Module R W] (p : Ideal R) [p.IsPrime]
        (L : Submodule R W) ↦
      UpperTheory.Reformulated.B.Qi33.locS p.primeCompl L

private theorem UpperTheory.Reformulated.B.Qi33.mem_locS_iff {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W]
    [Module R W] (S : Submonoid R) (R' : Type*) [CommRing R'] [Algebra R R'] [IsLocalization S R']
    [Module R' W] [IsScalarTower R R' W] (L : Submodule R W) (x : W) :
    x ∈ UpperTheory.Reformulated.B.Qi33.locS S L ↔ x ∈ Submodule.span R' (L : Set W) := by
  rw [IsLocalization.mem_span_iff S, Submodule.span_eq]
  constructor
  · rintro ⟨s, hs, hx⟩
    refine ⟨s • x, hx, ⟨s, hs⟩, ?_⟩
    rw [← algebraMap_smul R' s x, smul_smul]
    have h := IsLocalization.mk'_spec R' (1 : R) (⟨s, hs⟩ : S)
    simp only [map_one] at h
    rw [h, one_smul]
  · rintro ⟨y, hy, z, rfl⟩
    refine ⟨z, z.2, ?_⟩
    rw [← algebraMap_smul R' (z : R), smul_smul]
    have h := IsLocalization.mk'_spec' R' (1 : R) z
    simp only [map_one] at h
    rw [h, one_smul]
    exact hy

private theorem UpperTheory.Reformulated.B.Qi33.exists_basis_of_pid {D K Z : Type} [CommRing D] [IsDomain D]
    [IsPrincipalIdealRing D] [Field K] [Algebra D K] [IsFractionRing D K] [AddCommGroup Z]
    [Module K Z] [Module D Z] [IsScalarTower D K Z] (M : Submodule D Z) (hM : M.FG)
    (hs : Submodule.span K (M : Set Z) = ⊤) :
    ∃ b : Module.Basis (Fin (Module.finrank K Z)) K Z, Submodule.span D (Set.range b) = M := by
  haveI : Module.Finite D M := Module.Finite.iff_fg.mpr hM
  haveI : Module.IsTorsionFree D Z := Module.IsTorsionFree.trans_faithfulSMul D K Z
  haveI : Module.Free D M := inferInstance
  let c := Module.finBasis D M
  let v : Fin (Module.finrank D M) → Z := fun i => (c i : Z)
  have hli : LinearIndependent D v := c.linearIndependent.map' M.subtype M.ker_subtype
  have hliK : LinearIndependent K v := (LinearIndependent.iff_fractionRing D K).mp hli
  have hsp : Submodule.span D (Set.range v) = M := by
    have h1 : Set.range v = M.subtype '' Set.range c := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspK : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← Submodule.span_span_of_tower D K (Set.range v), hsp, hs]
  let b0 := Module.Basis.mk hliK hspK
  have hn : Module.finrank K Z = Module.finrank D M := by
    simpa using Module.finrank_eq_card_basis b0
  refine ⟨b0.reindex (finCongr hn.symm), ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.coe_mk, hsp]

theorem UpperTheory.Reformulated.B.Qi33.exists_loc_basis :
    ∀ {K : Type} [inst : Field K] [NumberField K] [StarRing K] {Z : Type} [inst_3 : AddCommGroup Z]
      [inst_4 : _root_.Module K Z] [inst_5 : _root_.Module (NumberField.RingOfIntegers K) Z]
      [IsScalarTower (NumberField.RingOfIntegers K) K Z] [FiniteDimensional K Z]
      (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (A : Submodule (NumberField.RingOfIntegers K) Z),
      A.FG →
        Submodule.span K (↑A : Set Z) = ⊤ →
          ∃ (b : Module.Basis (Fin (Module.finrank K Z)) K Z),
            UpperTheory.Reformulated.B.Qi33.localization₂ w.asIdeal A =
              UpperTheory.Reformulated.B.Qi33.localization₂ w.asIdeal
                (Submodule.span (NumberField.RingOfIntegers K) (Set.range (⇑b : Fin (Module.finrank K Z) → Z))) := by
  intro K _ _ _ Z _ _ _ _ _ w A hA hsp
  let D := Localization.subalgebra.ofField K w.asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors w.asIdeal)
  haveI hloc : IsLocalization w.asIdeal.primeCompl D :=
    Localization.subalgebra.isLocalization_ofField K _ _
  haveI : IsFractionRing D K := Localization.subalgebra.isFractionRing_ofField K _ _
  haveI : IsDiscreteValuationRing D :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (NumberField.RingOfIntegers K) w.ne_bot D
  haveI : IsScalarTower (NumberField.RingOfIntegers K) D Z :=
    IsScalarTower.of_algebraMap_smul fun r z => algebraMap_smul K r z
  have hfg : (Submodule.span D (A : Set Z)).FG := by
    obtain ⟨t, rfl⟩ := hA
    exact ⟨t, (Submodule.span_span_of_tower _ _ _).symm⟩
  obtain ⟨b, hb⟩ := UpperTheory.Reformulated.B.Qi33.exists_basis_of_pid (D := D) (K := K) _ hfg
    (by rw [Submodule.span_span_of_tower, hsp])
  refine ⟨b, ?_⟩
  ext x
  unfold UpperTheory.Reformulated.B.Qi33.localization₂
  rw [UpperTheory.Reformulated.B.Qi33.mem_locS_iff _ D, UpperTheory.Reformulated.B.Qi33.mem_locS_iff _ D,
    Submodule.span_span_of_tower, hb]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsFixedLift
noncomputable def UpperTheory.Reformulated.B.Gwa5.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}

theorem UpperTheory.Reformulated.B.Gwa5.aux2 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) {a b : V},
      a ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        b ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
          ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (a + b) = (↑((χ : ↥H → kˣ) h) : k) • (a + b) := by
  intro k G V _ _ _ _ ρ H χ a b ha hb h
  rw [map_add (f := _), smul_add, ha h, hb h]

theorem UpperTheory.Reformulated.B.Gwa5.aux3 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (h : ↥H),
      ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (0 : V) = (↑((χ : ↥H → kˣ) h) : k) • (0 : V) := by
  intro k G V _ _ _ _ ρ H χ h
  rw [map_zero, smul_zero]

theorem UpperTheory.Reformulated.B.Gwa5.aux4 :
    ∀ {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
      (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) (c : k) {v : V},
      v ∈ {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v} →
        ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) (c • v) = (↑((χ : ↥H → kˣ) h) : k) • c • v := by
  intro k G V _ _ _ _ ρ H χ c v hv h
  rw [map_smul, hv h, smul_comm]

noncomputable def UpperTheory.Reformulated.B.Gwa5.eig :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 : _root_.Module k V] → Representation k G V → (H : Subgroup G) → (↥H →* kˣ) → Submodule k V :=
    fun {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V] [inst_3 : _root_.Module k V]
        (ρ : Representation k G V) (H : Subgroup G) (χ : ↥H →* kˣ) ↦
      { carrier := {v : V | ∀ (h : ↥H), ((ρ : G → V →ₗ[k] V) (↑h : G) : V → V) v = (↑((χ : ↥H → kˣ) h) : k) • v},
        add_mem' := @UpperTheory.Reformulated.B.Gwa5.aux2 k G V inst inst_1 inst_2 inst_3 ρ H χ, zero_mem' := UpperTheory.Reformulated.B.Gwa5.aux3 ρ H χ,
        smul_mem' := UpperTheory.Reformulated.B.Gwa5.aux4 ρ H χ : Submodule k V }

noncomputable def UpperTheory.Reformulated.B.Gwa5.fixed :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → Representation k G V → Subgroup G → Submodule k V :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] (ρ : Representation k G V)
        (H : Subgroup G) ↦
      UpperTheory.Reformulated.B.Gwa5.eig ρ H (1 : ↥H →* kˣ)

theorem UpperTheory.Reformulated.B.Gwa5.exists_fixed_lift :
    ∀ {G V : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (J L A : Subgroup G),
      IsOpen (↑J : Set G) →
        IsCompact (↑J : Set G) →
          ∀ (π : Representation ℂ G V),
            UpperTheory.Reformulated.B.Gwa5.IsSmooth π →
              ∀ (q : Submodule ℂ V) (u : V),
                L ≤ J →
                  (∀ y ∈ L, ((π : G → V →ₗ[ℂ] V) y : V → V) u = u) →
                    A ≤ J →
                      (∀ x ∈ A, ((π : G → V →ₗ[ℂ] V) x : V → V) u - u ∈ q) →
                        (∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ L) → ∃ v ∈ UpperTheory.Reformulated.B.Gwa5.fixed π J, v - u ∈ q := by
  intro G V _ _ _ _ _ J L A _ hJc π hπ q u _ hL hAJ hA hdec
  classical
  have hmul : ∀ (x y : G) (w : V), π x (π y w) = π (x * y) w := by
    intro x y w
    rw [map_mul, Module.End.mul_apply]

  have hq : ∀ y ∈ J, π y u - u ∈ q := by
    intro y hy
    obtain ⟨a, ha, hl⟩ := hdec y hy
    have h1 : π y u = π a u := by
      conv_rhs => rw [← hL _ hl, hmul, mul_inv_cancel_left]
    rw [h1]
    exact hA a ha

  have hfin : ((fun g : G => π g u) '' (J : Set G)).Finite := by
    have hU : ∀ x ∈ (J : Set G), {g : G | π g u = π x u} ∈ nhds x := by
      intro x _
      have ho : IsOpen ((fun g : G => x⁻¹ * g) ⁻¹' {g : G | π g u = u}) :=
        (hπ u).preimage (continuous_const.mul continuous_id)
      refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
      · simp
      · intro g hg
        have hg' : π (x⁻¹ * g) u = u := hg
        show π g u = π x u
        conv_rhs => rw [← hg', hmul, mul_inv_cancel_left]
    obtain ⟨t, -, ht⟩ := hJc.elim_nhds_subcover _ hU
    refine (t.finite_toSet.image (fun g : G => π g u)).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨x, hx, hgx⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact ⟨x, hx, hgx.symm⟩
  set O : Finset V := hfin.toFinset with hO
  have hmem : ∀ w, w ∈ O ↔ ∃ g ∈ J, π g u = w := by
    intro w
    rw [hO, Set.Finite.mem_toFinset]
    rfl
  have hstab : ∀ h ∈ J, ∀ w ∈ O, π h w ∈ O := by
    intro h hh w hw
    obtain ⟨g, hg, rfl⟩ := (hmem w).1 hw
    exact (hmem _).2 ⟨h * g, J.mul_mem hh hg, (hmul h g u).symm⟩
  have hne : (O.card : ℂ) ≠ 0 := by
    have : O.Nonempty := ⟨π 1 u, (hmem _).2 ⟨1, J.one_mem, rfl⟩⟩
    exact_mod_cast this.card_pos.ne'
  refine ⟨(O.card : ℂ)⁻¹ • ∑ w ∈ O, w, ?_, ?_⟩
  · intro h
    have hs : ∑ w ∈ O, π (h : G) w = ∑ w ∈ O, w := by
      refine Finset.sum_nbij' (fun w => π (h : G) w) (fun w => π (h : G)⁻¹ w)
        (fun w hw => hstab _ h.2 w hw) (fun w hw => hstab _ (J.inv_mem h.2) w hw) ?_ ?_
        (fun _ _ => rfl)
      · intro w _
        simp only [hmul, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro w _
        simp only [hmul, mul_inv_cancel, map_one, Module.End.one_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, hs, MonoidHom.one_apply, Units.val_one, one_smul]
  · have h2 : (O.card : ℂ)⁻¹ • ∑ w ∈ O, w - u = (O.card : ℂ)⁻¹ • ∑ w ∈ O, (w - u) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ,
        smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [h2]
    refine q.smul_mem _ (q.sum_mem ?_)
    intro w hw
    obtain ⟨g, hg, rfl⟩ := (hmem w).1 hw
    exact hq g hg
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummandLocalization
theorem UpperTheory.Reformulated.B.SummandLocalization.aux1.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  rw [smul_add, mul_smul s t y, mul_comm s t, mul_smul t s x]
  exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)

theorem UpperTheory.Reformulated.B.SummandLocalization.aux2.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by rw [smul_zero]; exact L.zero_mem⟩

theorem UpperTheory.Reformulated.B.SummandLocalization.aux3.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L r x ⟨s, hs, hx⟩
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem r hx

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @UpperTheory.Reformulated.B.SummandLocalization.aux1 R inst W inst_1 inst_2 S L,
        zero_mem' := UpperTheory.Reformulated.B.SummandLocalization.aux2 S L, smul_mem' := UpperTheory.Reformulated.B.SummandLocalization.aux3 S L : Submodule R W }

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.locF :
    {K F W : Type} →
      [inst : Field K] →
        [inst_1 : Field F] →
          [Algebra F K] →
            [inst_3 : AddCommGroup W] →
              [inst_4 : _root_.Module (NumberField.RingOfIntegers K) W] →
                Ideal (NumberField.RingOfIntegers F) →
                  Submodule (NumberField.RingOfIntegers K) W → Submodule (NumberField.RingOfIntegers K) W :=
    fun {K F W : Type} [Field K] [Field F] [Algebra F K] [AddCommGroup W] [_root_.Module (NumberField.RingOfIntegers K) W]
        (𝔭 : Ideal (NumberField.RingOfIntegers F)) (L : Submodule (NumberField.RingOfIntegers K) W) ↦
      UpperTheory.Reformulated.B.SummandLocalization.locS
        (Submonoid.closure
          {s : NumberField.RingOfIntegers K |
            ∃ t ∉ 𝔭,
              (Algebra.algebraMap (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers K) :
                    NumberField.RingOfIntegers F → NumberField.RingOfIntegers K)
                  t =
                s})
        L

noncomputable def UpperTheory.Reformulated.B.SummandLocalization.SummandLoc :
    Prop :=
    ∀ (K F V : Type) [inst : Field K] [NumberField K] [inst_2 : Field F] [NumberField F] [inst_4 : Algebra F K]
      [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V] [FiniteDimensional K V]
      [inst_8 : _root_.Module (NumberField.RingOfIntegers K) V] [inst_9 : IsScalarTower (NumberField.RingOfIntegers K) K V]
      (X : Submodule K V) (𝔭 : Ideal (NumberField.RingOfIntegers F)),
      𝔭.IsMaximal →
        ∀ (Λ : Submodule (NumberField.RingOfIntegers K) V),
          (∃ (Λ₀ : Submodule (NumberField.RingOfIntegers K) V), Submodule.IsFullLattice K Λ₀ ∧ UpperTheory.Reformulated.B.SummandLocalization.locF 𝔭 Λ₀ = Λ) →
            ∃ (π : V →ₗ[K] V), (∀ (v : V), (π : V → V) v ∈ X) ∧ (∀ x ∈ X, (π : V → V) x = x) ∧ ∀ y ∈ Λ, (π : V → V) y ∈ Λ

private theorem UpperTheory.Reformulated.B.SummandLocalization.lattice_isLocalizedModule {R K W : Type*} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (M : Submodule R W) (hM : Submodule.span K (M : Set W) = ⊤) :
    IsLocalizedModule (nonZeroDivisors R) M.subtype where
  map_units s := by
    have hs : algebraMap R K s ≠ 0 := (IsLocalization.map_units K s).ne_zero
    rw [Module.End.isUnit_iff]
    have h : ((algebraMap R (Module.End R W)) s : W → W) = fun w => (algebraMap R K s) • w := by
      funext w
      simp
    rw [h]
    exact MulAction.bijective (Units.mk0 _ hs)
  surj y := by
    have hy : y ∈ Submodule.span K (M : Set W) := hM ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K (M : Set W) y hy
    rw [Submodule.span_eq] at ht
    exact ⟨⟨⟨_, ht⟩, t⟩, rfl⟩
  exists_of_eq h := ⟨1, by rw [Subtype.ext h]⟩

private theorem UpperTheory.Reformulated.B.SummandLocalization.exists_proj {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (X : Submodule K V) (L : Submodule R V) (hL : Submodule.IsFullLattice K L) :
    ∃ π : V →ₗ[K] V, (∀ v, π v ∈ X) ∧ (∀ x ∈ X, π x = x) ∧ ∀ y ∈ L, π y ∈ L := by
  let q : V →ₗ[R] V ⧸ X := X.mkQ.restrictScalars R
  let M : Submodule R (V ⧸ X) := L.map q
  have hM : Submodule.span K (M : Set (V ⧸ X)) = ⊤ := by
    have h : (M : Set (V ⧸ X)) = X.mkQ '' (L : Set V) := rfl
    rw [h, ← Submodule.map_span, hL.span_eq_top, Submodule.map_top, Submodule.range_mkQ]
  haveI : Module.Finite R M := Module.Finite.iff_fg.2 (hL.fg.map q)
  haveI : Module.IsTorsionFree R (V ⧸ X) := Module.IsTorsionFree.trans_faithfulSMul R K (V ⧸ X)
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  haveI : Module.Projective R M := Module.Flat.projective_of_finitePresentation
  have hsurj : Function.Surjective (q.submoduleMap L) := LinearMap.submoduleMap_surjective q L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (q.submoduleMap L) LinearMap.id hsurj
  haveI := UpperTheory.Reformulated.B.SummandLocalization.lattice_isLocalizedModule M hM
  have hb : IsBaseChange K M.subtype := IsLocalizedModule.isBaseChange (nonZeroDivisors R) K M.subtype
  let σ : (V ⧸ X) →ₗ[K] V := hb.lift (L.subtype ∘ₗ s)
  have hσ : ∀ m : M, σ m = (s m : V) := fun m => hb.lift_eq (L.subtype ∘ₗ s) m
  have hq : X.mkQ ∘ₗ σ = LinearMap.id := by
    apply LinearMap.ext_on hM
    intro m hm
    have h1 := congrArg Subtype.val (LinearMap.congr_fun hs ⟨m, hm⟩)
    rw [LinearMap.comp_apply, hσ ⟨m, hm⟩]
    exact h1
  refine ⟨LinearMap.id - σ ∘ₗ X.mkQ, fun v => ?_, fun x hx => ?_, fun y hy => ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have h1 := LinearMap.congr_fun hq (X.mkQ v)
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
  · have h1 : X.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero X).2 hx
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h1, map_zero, sub_zero]
  · have h1 := hσ ⟨q y, Submodule.mem_map_of_mem hy⟩
    have h2 : σ (X.mkQ y) ∈ L := by
      have h3 : σ (X.mkQ y) = _ := h1
      rw [h3]
      exact Subtype.property _
    exact L.sub_mem hy h2

theorem UpperTheory.Reformulated.B.SummandLocalization.summand_localization :
    UpperTheory.Reformulated.B.SummandLocalization.SummandLoc := by
  rintro K F V _ _ _ _ _ _ _ _ _ _ X 𝔭 _ Λ ⟨Λ₀, hΛ₀, rfl⟩
  obtain ⟨π, h1, h2, h3⟩ := UpperTheory.Reformulated.B.SummandLocalization.exists_proj X Λ₀ hΛ₀
  refine ⟨π, h1, h2, ?_⟩
  rintro y ⟨s, hs, hy⟩
  refine ⟨s, hs, ?_⟩
  rw [← LinearMap.map_smul_of_tower]
  exact h3 _ hy
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AbsolutelyIrreducibleSpan
noncomputable def UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr.{u_1, u_2, u_3} :
    {k : Type u_1} → [Field k] → {n : Type u_2} → [Fintype n] → [DecidableEq n] → {G : Type u_3} → (G → Matrix n n k) → Prop :=
    fun {k : Type u_1} [Field k] {n : Type u_2} [Fintype n] [DecidableEq n] {G : Type u_3} (ρ : G → Matrix n n k) ↦
      (∀ (W : Submodule k (n → k)), (∀ (g : G), ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
        ∀ (M : Matrix n n k), (∀ (g : G), M * ρ g = ρ g * M) → ∃ (c : k), M = c • (1 : Matrix n n k)

noncomputable def UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.StatOntoSpan :
    Prop :=
    ∀ (O : Type) [inst : CommRing O] [inst_1 : IsLocalRing O] (n : Type) [inst_2 : Fintype n] [inst_3 : DecidableEq n]
      (G : Type) [inst_4 : Monoid G] (ρ : G →* Matrix n n O),
      (UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr fun (g : G) ↦
          ((ρ : G → Matrix n n O) g).map (⇑(IsLocalRing.residue O) : O → IsLocalRing.ResidueField O)) →
        Submodule.span O (Set.range (⇑ρ : G → Matrix n n O)) = ⊤

private theorem UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.adjoin_top {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {G : Type} (ρ : G → Matrix n n k) (h : UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr ρ) :
    Algebra.adjoin k (Set.range ρ) = ⊤ := by
  classical
  obtain ⟨h1, h2⟩ := h
  set A : Subalgebra k (Module.End k (n → k)) :=
    (Algebra.adjoin k (Set.range ρ)).map (Matrix.toLinAlgEquiv' (R := k) (n := n)).toAlgHom with hA
  have hmem : ∀ g, Matrix.toLin' (ρ g) ∈ A := fun g =>
    ⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩, rfl⟩
  have hsm : ∀ (a : A) (v : n → k), a • v = (a : Module.End k (n → k)) v := fun _ _ => rfl
  have hk : ∀ (c : k) (v : n → k), (algebraMap k A c) • v = c • v := fun c v => by
    rw [hsm]; simp
  haveI : IsSemisimpleModule A (n → k) := by
    rw [isSemisimpleModule_iff]
    constructor
    intro W
    let W' : Submodule k (n → k) :=
      { carrier := W
        add_mem' := fun ha hb => W.add_mem ha hb
        zero_mem' := W.zero_mem
        smul_mem' := fun c v hv => by
          rw [← hk]; exact W.smul_mem _ hv }
    have hW := h1 W' (fun g v hv => by
      have := W.smul_mem (⟨_, hmem g⟩ : A) hv
      rw [hsm] at this
      exact this)
    rcases hW with hW | hW
    · have : W = ⊥ := by
        ext v
        have : v ∈ W' ↔ v ∈ (⊥ : Submodule k (n → k)) := by rw [hW]
        exact this
      exact ⟨⊤, this ▸ isCompl_bot_top⟩
    · have : W = ⊤ := by
        ext v
        have : v ∈ W' ↔ v ∈ (⊤ : Submodule k (n → k)) := by rw [hW]
        exact this
      exact ⟨⊥, this ▸ isCompl_top_bot⟩
  have hsc : ∀ φ : Module.End A (n → k), ∃ c : k, ∀ v, φ v = c • v := by
    intro φ
    let ψ : Module.End k (n → k) :=
      { toFun := φ
        map_add' := φ.map_add
        map_smul' := fun c v => by
          rw [← hk, φ.map_smul, hk]; rfl }
    obtain ⟨c, hc⟩ := h2 (LinearMap.toMatrix' ψ) (fun g => by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
      refine LinearMap.ext fun v => ?_
      exact φ.map_smul (⟨_, hmem g⟩ : A) v)
    refine ⟨c, fun v => ?_⟩
    have h3 : ψ = Matrix.toLin' (c • (1 : Matrix n n k)) := by
      rw [← hc, Matrix.toLin'_toMatrix']
    have h4 : φ v = ψ v := rfl
    rw [h4, h3]
    simp
  rw [eq_top_iff]
  intro M _
  let f : Module.End (Module.End A (n → k)) (n → k) :=
    { toFun := Matrix.toLin' M
      map_add' := (Matrix.toLin' M).map_add
      map_smul' := fun φ v => by
        obtain ⟨c, hc⟩ := hsc φ
        change Matrix.toLin' M (φ v) = φ (Matrix.toLin' M v)
        rw [hc, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f
    (Finset.univ.image fun i : n => (Pi.single i 1 : n → k))
  obtain ⟨r, N, hN, rfl⟩ := r
  have : M = N := by
    apply Matrix.toLin'.injective
    apply (Pi.basisFun k n).ext
    intro i
    rw [Pi.basisFun_apply]
    exact hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact this ▸ hN

theorem UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan :
    UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.StatOntoSpan := by
  intro O _ _ n _ _ G _ ρ h
  have h1 := UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.adjoin_top _ h
  let π : Matrix n n O →+* Matrix n n (IsLocalRing.ResidueField O) :=
    (IsLocalRing.residue O).mapMatrix
  have h2 : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => π (ρ g)) = ⊤ := by
    rw [← Algebra.adjoin_eq_span_of_subset]
    · exact (congrArg Subalgebra.toSubmodule h1).trans rfl
    · intro x hx
      apply Submodule.subset_span
      have : x ∈ MonoidHom.mrange (π.toMonoidHom.comp ρ) :=
        (Submonoid.closure_le (S := MonoidHom.mrange (π.toMonoidHom.comp ρ))).mpr
          (by rintro _ ⟨g, rfl⟩; exact ⟨g, rfl⟩) hx
      exact this
  have h3 : ∀ X : Matrix n n (IsLocalRing.ResidueField O),
      ∃ Y ∈ Submodule.span O (Set.range (ρ : G → Matrix n n O)), π Y = X := by
    intro X
    have hX : X ∈ Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => π (ρ g)) := h2 ▸ Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨a + b, Submodule.add_mem _ ha hb, map_add _ _ _⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨d • a, Submodule.smul_mem _ _ ha, ?_⟩
      ext i j
      simp [π]
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro M _
  obtain ⟨Y, hY, hYM⟩ := h3 (π M)
  have h4 : M - Y ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Matrix n n O)) := by
    rw [Matrix.matrix_eq_sum_single (M - Y)]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have h5 : (M - Y) i j ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      have h6 : π (M - Y) = 0 := by rw [map_sub, hYM, sub_self]
      exact congrFun (congrFun h6 i) j
    have h7 : Matrix.single i j ((M - Y) i j) = (M - Y) i j • Matrix.single i j (1 : O) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [h7]
    exact Submodule.smul_mem_smul h5 Submodule.mem_top
  have h8 : M = Y + (M - Y) := by abel
  rw [h8]
  exact Submodule.add_mem_sup hY h4
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CosetOfCover
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qn18.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qn18.MP :
    (C : Type) → [Field C] → ℕ → Type :=
    fun (C : Type) [Field C] (N : ℕ) ↦ MvPolynomial (Fin N × Fin N) C

noncomputable def UpperTheory.Reformulated.B.Qn18.ev :
    {C : Type} → [inst : Field C] → {N : ℕ} → UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.MP C N → C :=
    fun {C : Type} [Field C] {N : ℕ} (x : UpperTheory.Reformulated.B.Qn18.Mat C N) (f : UpperTheory.Reformulated.B.Qn18.MP C N) ↦
      (MvPolynomial.eval fun (p : Fin N × Fin N) ↦ x p.1 p.2 : MvPolynomial (Fin N × Fin N) C → C) f

noncomputable def UpperTheory.Reformulated.B.Qn18.dAt :
    {C : Type} →
      [inst : Field C] → {N : ℕ} → UpperTheory.Reformulated.B.Qn18.MP C N → UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.Mat C N → C :=
    fun {C : Type} [Field C] {N : ℕ} (f : UpperTheory.Reformulated.B.Qn18.MP C N) (x Y : UpperTheory.Reformulated.B.Qn18.Mat C N) ↦
      ∑ p : Fin N × Fin N,
        UpperTheory.Reformulated.B.Qn18.ev x
            ((MvPolynomial.pderiv p : MvPolynomial (Fin N × Fin N) C → MvPolynomial (Fin N × Fin N) C) f) *
          Y p.1 p.2

noncomputable def UpperTheory.Reformulated.B.Qn18.Chain :
    Prop :=
    ∀ (C : Type) [inst : Field C] (N M : ℕ) (φ : UpperTheory.Reformulated.B.Qn18.Mat C N →ₗ[C] UpperTheory.Reformulated.B.Qn18.Mat C M)
      (f : UpperTheory.Reformulated.B.Qn18.MP C M),
      ∃ (f' : UpperTheory.Reformulated.B.Qn18.MP C N),
        (∀ (x : UpperTheory.Reformulated.B.Qn18.Mat C N),
            UpperTheory.Reformulated.B.Qn18.ev x f' =
              UpperTheory.Reformulated.B.Qn18.ev ((φ : UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.Mat C M) x) f) ∧
          ∀ (x Y : UpperTheory.Reformulated.B.Qn18.Mat C N),
            UpperTheory.Reformulated.B.Qn18.dAt f' x Y =
              UpperTheory.Reformulated.B.Qn18.dAt f ((φ : UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.Mat C M) x)
                ((φ : UpperTheory.Reformulated.B.Qn18.Mat C N → UpperTheory.Reformulated.B.Qn18.Mat C M) Y)

noncomputable def UpperTheory.Reformulated.B.Qn18.OpenCoset :
    Prop :=
    ∀ (Γ C : Type) [inst : Group Γ] [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [inst_4 : Field C]
      (n : ℕ) (r : Γ →* GL (Fin n) C) (f : UpperTheory.Reformulated.B.Qn18.MP C n) (O : Set Γ),
      IsOpen O →
        O.Nonempty →
          (∀ g ∈ O, UpperTheory.Reformulated.B.Qn18.ev (↑((r : Γ → GL (Fin n) C) g) : Matrix (Fin n) (Fin n) C) f = (0 : C)) →
            ∃ (U : Subgroup Γ),
              U.Normal ∧
                U.FiniteIndex ∧
                  ∃ (g : Γ),
                    ∀ u ∈ U, UpperTheory.Reformulated.B.Qn18.ev (↑((r : Γ → GL (Fin n) C) (g * u)) : Matrix (Fin n) (Fin n) C) f = (0 : C)

open scoped Pointwise in
private theorem UpperTheory.Reformulated.B.Qn18.coset_of_cover {G : Type} [Group G] [TopologicalSpace G]
    [TopologicalSpace.NoetherianSpace G] (hc : ∀ h : G, Continuous fun x : G => h * x)
    (Z : Set G) (hZ : IsClosed Z) (s : Finset G) (hs : ∀ x : G, ∃ a ∈ s, a * x ∈ Z) :
    ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ ∃ g : G, ∀ u ∈ U, g * u ∈ Z := by
  classical
  haveI : ContinuousConstSMul G G := ⟨hc⟩
  set X : Set G := irreducibleComponent (1 : G) with hX
  have hXc : X ∈ irreducibleComponents G := irreducibleComponent_mem_irreducibleComponents _
  have horb : MulAction.orbit G X ⊆ irreducibleComponents G := by
    rintro _ ⟨h, rfl⟩
    refine ⟨?_, ?_⟩
    · exact hXc.1.image _ (hc h).continuousOn
    · intro Y hY hle
      have h1 : IsIrreducible (h⁻¹ • Y) := IsIrreducible.image hY _ (hc h⁻¹).continuousOn
      have h2 : X ⊆ h⁻¹ • Y := by
        have : h • X ⊆ Y := hle
        exact Set.smul_set_subset_iff_subset_inv_smul_set.mp this
      have h3 : h⁻¹ • Y ⊆ X := hXc.2 h1 h2
      have h4 : Y ⊆ h • X := by
        have := Set.smul_set_subset_iff_subset_inv_smul_set.mp h3
        simpa using this
      exact h4
  have hfin : (MulAction.orbit G X).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset horb
  haveI : (MulAction.stabilizer G X).FiniteIndex := by
    refine ⟨?_⟩
    rw [MulAction.index_stabilizer]
    exact ((Set.ncard_pos hfin).mpr ⟨X, MulAction.mem_orbit_self X⟩).ne'
  obtain ⟨W, hW, hXW⟩ := isIrreducible_iff_sUnion_isClosed.mp hXc.1
    (s.image fun a => (fun x : G => a * x) ⁻¹' Z)
    (by
      intro z hz
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
      exact hZ.preimage (hc a))
    (by
      intro x _
      obtain ⟨a, ha, hx⟩ := hs x
      exact ⟨_, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ha), hx⟩)
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hW
  refine ⟨(MulAction.stabilizer G X).normalCore, inferInstance, inferInstance, a, ?_⟩
  intro u hu
  have hu' : u • X = X := Subgroup.normalCore_le _ hu
  have : u ∈ X := by
    rw [← hu']
    exact ⟨1, mem_irreducibleComponent, by simp⟩
  exact hXW this

private theorem UpperTheory.Reformulated.B.Qn18.finite_cover {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] (O : Set G) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ s : Finset G, ∀ x : G, ∃ a ∈ s, a * x ∈ O := by
  obtain ⟨o, ho⟩ := hne
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun a : G => (fun x : G => a * x) ⁻¹' O)
    (fun a => hO.preimage (continuous_const_mul a))
    (fun x _ => Set.mem_iUnion.mpr ⟨o * x⁻¹, by simpa using ho⟩)
  refine ⟨s, fun x => ?_⟩
  simpa using hs (Set.mem_univ x)

theorem UpperTheory.Reformulated.B.Qn18.main :
    UpperTheory.Reformulated.B.Qn18.Chain → UpperTheory.Reformulated.B.Qn18.OpenCoset := by
  intro hch Γ C _ _ _ _ _ n r f O hO hne hf
  obtain ⟨s, hs⟩ := UpperTheory.Reformulated.B.Qn18.finite_cover O hO hne
  let p : Γ → PrimeSpectrum (MvPolynomial (Fin n × Fin n) C) := fun g =>
    ⟨RingHom.ker (MvPolynomial.eval fun q : Fin n × Fin n =>
      (↑(r g) : Matrix (Fin n) (Fin n) C) q.1 q.2), RingHom.ker_isPrime _⟩
  have hp : ∀ (g : Γ) (S : Set (MvPolynomial (Fin n × Fin n) C)),
      p g ∈ PrimeSpectrum.zeroLocus S ↔
        ∀ k ∈ S, UpperTheory.Reformulated.B.Qn18.ev (↑(r g) : Matrix (Fin n) (Fin n) C) k = 0 := by
    intro g S
    rw [PrimeSpectrum.mem_zeroLocus]
    exact Iff.rfl
  let τ : TopologicalSpace Γ := TopologicalSpace.induced p inferInstance
  have hcl : ∀ k : MvPolynomial (Fin n × Fin n) C,
      @IsClosed Γ τ {g | UpperTheory.Reformulated.B.Qn18.ev (↑(r g) : Matrix (Fin n) (Fin n) C) k = 0} := by
    intro k
    refine (@isClosed_induced_iff _ _ _ _ p).mpr ⟨_, PrimeSpectrum.isClosed_zeroLocus {k}, ?_⟩
    ext g
    simp [hp]
  have hN : @TopologicalSpace.NoetherianSpace Γ τ := by
    letI := τ
    exact (@Topology.IsInducing.mk _ _ τ _ p rfl).noetherianSpace
  have hc : ∀ h : Γ, @Continuous Γ Γ τ τ fun x => h * x := by
    intro h
    refine (@continuous_iff_isClosed _ _ τ τ _).mpr ?_
    intro T hT
    obtain ⟨T', hT', rfl⟩ := (@isClosed_induced_iff _ _ _ _ p).mp hT
    obtain ⟨S, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).mp hT'
    choose F hF using fun k => hch C n n
      (LinearMap.mulLeft C (↑(r h) : Matrix (Fin n) (Fin n) C)) k
    have : (fun x => h * x) ⁻¹' (p ⁻¹' PrimeSpectrum.zeroLocus S) =
        ⋂ k ∈ S, {g | UpperTheory.Reformulated.B.Qn18.ev (↑(r g) : Matrix (Fin n) (Fin n) C) (F k) = 0} := by
      ext g
      simp only [Set.mem_preimage, hp, Set.mem_iInter, Set.mem_setOf_eq, (hF _).1,
        LinearMap.mulLeft_apply, map_mul, Units.val_mul]
    rw [this]
    exact @isClosed_biInter _ _ τ _ _ fun k _ => hcl (F k)
  exact @UpperTheory.Reformulated.B.Qn18.coset_of_cover Γ _ τ hN hc _ (hcl f) s fun x => by
    obtain ⟨a, ha, hx⟩ := hs x
    exact ⟨a, ha, hf _ hx⟩
end
