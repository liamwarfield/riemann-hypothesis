module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.AdjointActionReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorsionFreeGenerators.ProjectiveReduction

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.RetractionReduction
open NumberField

namespace PI.SRW

theorem retraction_reduction : RetrStep := by
  intro E V _ _ _ _ _ _ Λ N hNΛ hfg hsat
  let N' : Submodule (𝓞 E) Λ := N.comap Λ.subtype
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite (𝓞 E) (Λ ⧸ N') := inferInstance
  haveI : NoZeroSMulDivisors (𝓞 E) (Λ ⧸ N') := by
    refine ⟨fun {o q} hq => ?_⟩
    by_cases ho : o = 0
    · exact Or.inl ho
    right
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N' q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact hsat o x ho x.2 hq
  haveI : Module.Projective (𝓞 E) (Λ ⧸ N') := PI.FGTFG.projective_reduction (𝓞 E) (Λ ⧸ N')
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N'.mkQ LinearMap.id (Submodule.mkQ_surjective N')
  let ρ' : Λ →ₗ[𝓞 E] Λ := LinearMap.id - s.comp N'.mkQ
  have hρ' : ∀ x : Λ, ρ' x ∈ N' := by
    intro x
    have h1 : N'.mkQ (ρ' x) = 0 := by
      have h2 := LinearMap.congr_fun hs (N'.mkQ x)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
      show N'.mkQ (x - s (N'.mkQ x)) = 0
      rw [map_sub, h2, sub_self]
    simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using h1
  refine ⟨Λ.subtype.comp ρ', fun x => hρ' x, fun x hx => ?_⟩
  have hx' : x ∈ N' := hx
  have h0 : N'.mkQ x = 0 := by simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx'
  simp [ρ', h0]

end PI.SRW
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.DualFamilyExists
open NumberField Module

namespace PI.SRW

theorem dualFamilyExists : CoordStep := by
  intro E V _ _ _ n g hg
  classical
  let b := Basis.span hg
  choose c hc using fun i => LinearMap.exists_extend (b.coord i)
  refine ⟨c, fun i j => ?_⟩
  have hmem : g j ∈ Submodule.span E (Set.range g) := Submodule.subset_span ⟨j, rfl⟩
  have h1 : c i (g j) = b.coord i ⟨g j, hmem⟩ := by
    rw [← hc i]; rfl
  have h2 : (⟨g j, hmem⟩ : Submodule.span E (Set.range g)) = b j := by
    rw [Basis.span_apply]
  rw [h1, h2, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

end PI.SRW
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.SesquilinearRepresentation
open NumberField Module

namespace PI.SRW

theorem sesquilinearRepresentation : RepStep := by
  intro E V _ _ _ _ _ _ _ _ h hnd Λ hΛ ℓ

  have hsurj : Function.Surjective h := by
    rw [← LinearMap.range_eq_top]
    have hco : (LinearMap.range h).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_dualCoannihilator] at hy
      rw [Submodule.mem_bot]
      exact hnd.2 y (fun x => hy (h x) ⟨x, rfl⟩)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range h), hco,
      Submodule.dualAnnihilator_bot]

  obtain ⟨s, hsΛ, hspan, hli⟩ := exists_linearIndependent E (Λ : Set V)
  classical
  have hs : LinearIndepOn E id s := hli
  let b := Basis.extend hs
  let f : hs.extend (Set.subset_univ s) → E :=
    fun i => if hi : (i : V) ∈ s then ℓ ⟨i, hsΛ hi⟩ else 0
  let φ : V →ₗ[E] E := b.constr E f
  have hφb : ∀ v (hv : v ∈ s), φ v = ℓ ⟨v, hsΛ hv⟩ := by
    intro v hv
    let i : hs.extend (Set.subset_univ s) := ⟨v, Basis.subset_extend hs hv⟩
    calc
      φ v = φ (b i) := congrArg φ (Basis.extend_apply_self hs i).symm
      _ = _ := by simpa only [f, i, dite_eq_left hv] using b.constr_basis E f i

  have hind : ∀ y ∈ Submodule.span (𝓞 E) (s : Set V), ∃ hy : y ∈ Λ, ℓ ⟨y, hy⟩ = φ y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem v hv => exact ⟨hsΛ hv, (hφb v hv).symm⟩
    | zero => exact ⟨zero_mem _, (map_zero ℓ).trans (map_zero φ).symm⟩
    | add u v _ _ hu hv =>
      obtain ⟨hu', eu⟩ := hu
      obtain ⟨hv', ev⟩ := hv
      refine ⟨add_mem hu' hv', ?_⟩
      have e : (⟨u + v, add_mem hu' hv'⟩ : Λ) = ⟨u, hu'⟩ + ⟨v, hv'⟩ := rfl
      rw [e, map_add (f := _), map_add (f := _), eu, ev]
    | smul a u _ hu =>
      obtain ⟨hu', eu⟩ := hu
      refine ⟨Λ.smul_mem a hu', ?_⟩
      have e : (⟨a • u, Λ.smul_mem a hu'⟩ : Λ) = a • ⟨u, hu'⟩ := rfl
      rw [e, map_smul, eu, ← algebraMap_smul E a u, map_smul, Algebra.smul_def, smul_eq_mul]

  have key : ∀ x : Λ, φ x = ℓ x := by
    intro x
    have hxE : (x : V) ∈ Submodule.span E s := by
      rw [hspan]
      exact Submodule.subset_span x.property
    obtain ⟨y, hy, z, hxy⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 E))).mp hxE
    have hzx : (z : 𝓞 E) • (x : V) = y := by
      rw [hxy, ← algebraMap_smul E (z : 𝓞 E), smul_smul, IsLocalization.mk'_spec', map_one,
        one_smul]
    obtain ⟨hyΛ, hℓφ⟩ := hind y hy
    have h1 : ℓ ((z : 𝓞 E) • x) = algebraMap (𝓞 E) E z * ℓ x := by
      rw [map_smul, Algebra.smul_def]
    have h2 : φ ((z : 𝓞 E) • (x : V)) = algebraMap (𝓞 E) E z * φ x := by
      rw [← algebraMap_smul E (z : 𝓞 E) (x : V), map_smul, smul_eq_mul]
    have hzΛ : ((z : 𝓞 E) • x : Λ) = ⟨y, hyΛ⟩ := by
      ext
      exact hzx
    have hne : algebraMap (𝓞 E) E z ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2
    apply mul_left_cancel₀ hne
    rw [← h1, ← h2, hzΛ, hzx, hℓφ]
  obtain ⟨w, hw⟩ := hsurj φ
  exact ⟨w, fun x => by rw [hw, key]⟩

end PI.SRW
end

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.SRW

theorem fi_zero {E : Type} [Field E] [NumberField E] (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    (0 : E) ∈ I := (I : Submodule (𝓞 E) E).zero_mem

theorem fi_add {E : Type} [Field E] [NumberField E] {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    {x y : E} (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I := (I : Submodule (𝓞 E) E).add_mem hx hy

theorem fi_smul {E : Type} [Field E] [NumberField E] {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    (o : 𝓞 E) {x : E} (hx : x ∈ I) : o • x ∈ I := (I : Submodule (𝓞 E) E).smul_mem o hx

theorem osmul {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (o : 𝓞 E) (v : V) : o • v = (o : E) • v := (IsScalarTower.algebraMap_smul E o v).symm

theorem exists_not_int {E : Type} [Field E] [NumberField E] : ∃ c : E, ∀ o : 𝓞 E, (o : E) ≠ c := by
  refine ⟨algebraMap ℚ E (1 / 2), fun o ho => ?_⟩
  have hint : IsIntegral ℤ (algebraMap ℚ E (1 / 2)) := by
    rw [← ho]
    exact o.2
  have hq : IsIntegral ℤ ((1 : ℚ) / 2) :=
    (isIntegral_algHom_iff (x := (1 : ℚ) / 2) (IsScalarTower.toAlgHom ℤ ℚ E) (algebraMap ℚ E).injective).mp hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  have hn' : (n : ℚ) = 1 / 2 := by
    rw [← hn]
    simp
  have h2 : ((2 * n : ℤ) : ℚ) = 1 := by
    push_cast
    rw [hn']
    norm_num
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

theorem mem_orth_iff {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}
    {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth]

theorem hX_left {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F0 : FlagG S r T) {v : S.V} (hv : ∀ a, S.hT (F0.e a) v = 0) : ∀ y ∈ F0.X, S.hT y v = 0 := by
  intro y hy
  have hy' : y ∈ Submodule.span E (Set.range F0.e) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact hv a
  | zero => simp
  | add x w _ _ hx hw => simp [hx, hw]
  | smul c x _ hx => simp [hx]

theorem X_le_orth {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (F0 : FlagG S r T) : F0.X ≤ orth S F0.X := by
  intro x hx
  rw [mem_orth_iff]
  apply hX_left F0
  intro a
  have hx' : x ∈ Submodule.span E (Set.range F0.e) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact F0.e_iso a b
  | zero => simp
  | add y w _ _ hy hw => simp [hy, hw]
  | smul c y _ hy => simp [hy]

theorem frame_reduction : FrameStep := by
  intro E _ _ _ S r T aa F0 Λ hC
  obtain ⟨hlat, huni, hz, hprim, hX, haa, hcs, htr⟩ := hC
  have hXL : Λ ⊓ (F0.X).restrictScalars (𝓞 E) = Formalism.L2.SG.Saturated.latSpan aa F0.e := hX
  have hzo : ∀ y ∈ F0.X, S.hT y F0.z = 0 := hX_left F0 F0.z_orth
  have hXo : F0.X ≤ orth S F0.X := X_le_orth F0
  have hzorth : F0.z ∈ orth S F0.X := mem_orth_iff.2 hzo

  have hznX : F0.z ∉ F0.X := by
    intro hzX
    obtain ⟨c, hc⟩ := exists_not_int (E := E)
    have hcz : c • F0.z ∈ Lsub Λ (⟨F0, F0.z⟩ : LFlag S r T) := by
      refine Submodule.mem_inf.2 ⟨Submodule.mem_sup_right ?_, ?_⟩
      · exact (Submodule.restrictScalars_mem _ _ _).2 (F0.X.smul_mem c hzX)
      · exact (Submodule.restrictScalars_mem _ _ _).2 ((orth S F0.X).smul_mem c hzorth)
    obtain ⟨o, ho⟩ := hprim c hcz
    exact hc o ho

  let N : Submodule (𝓞 E) S.V := Formalism.L2.SG.Saturated.latSpan aa F0.e ⊔ Submodule.span (𝓞 E) {F0.z}
  have hlatΛ : Formalism.L2.SG.Saturated.latSpan aa F0.e ≤ Λ := hXL ▸ inf_le_left
  have hlatX : ∀ n ∈ Formalism.L2.SG.Saturated.latSpan aa F0.e, n ∈ F0.X := by
    intro n hn
    rw [← hXL] at hn
    exact (Submodule.restrictScalars_mem _ _ _).1 (Submodule.mem_inf.1 hn).2
  have hNΛ : N ≤ Λ := sup_le hlatΛ ((Submodule.span_singleton_le_iff_mem _ _).2 hz)
  have hzN : F0.z ∈ N := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hsat : ∀ (o : 𝓞 E) (x : S.V), o ≠ 0 → x ∈ Λ → o • x ∈ N → x ∈ N := by
    intro o x ho hx hox
    obtain ⟨n1, hn1, n2, hn2, hsum⟩ := Submodule.mem_sup.1 hox
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hn2
    have hoE : (o : E) ≠ 0 := (RingOfIntegers.coe_ne_zero_iff).2 ho
    have hn1X : n1 ∈ F0.X := hlatX n1 hn1
    have h1 : (o : E) • x = n1 + (t : E) • F0.z := by
      rw [← osmul, ← osmul, hsum]
    have hxeq : x = (o : E)⁻¹ • n1 + ((o : E)⁻¹ * (t : E)) • F0.z := by
      calc x = (o : E)⁻¹ • ((o : E) • x) := by rw [smul_smul, inv_mul_cancel₀ hoE, one_smul]
        _ = _ := by rw [h1, smul_add, smul_smul]
    have hxorth : x ∈ orth S F0.X := by
      rw [hxeq]
      exact add_mem ((orth S F0.X).smul_mem _ (hXo hn1X)) ((orth S F0.X).smul_mem _ hzorth)
    have hcz : ((o : E)⁻¹ * (t : E)) • F0.z ∈ Lsub Λ (⟨F0, F0.z⟩ : LFlag S r T) := by
      have he : ((o : E)⁻¹ * (t : E)) • F0.z = x + (-(o : E)⁻¹) • n1 := by
        rw [hxeq, neg_smul]; abel
      refine Submodule.mem_inf.2 ⟨?_, (Submodule.restrictScalars_mem _ _ _).2
        ((orth S F0.X).smul_mem _ hzorth)⟩
      rw [he]
      refine Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨hx, ?_⟩) ?_
      · exact (Submodule.restrictScalars_mem _ _ _).2 hxorth
      · exact (Submodule.restrictScalars_mem _ _ _).2 (F0.X.smul_mem _ hn1X)
    obtain ⟨o', ho'⟩ := hprim _ hcz
    have hdiff : x - o' • F0.z ∈ Formalism.L2.SG.Saturated.latSpan aa F0.e := by
      rw [← hXL]
      refine Submodule.mem_inf.2 ⟨Λ.sub_mem hx (Λ.smul_mem o' hz), ?_⟩
      refine (Submodule.restrictScalars_mem _ _ _).2 ?_
      have he : x - o' • F0.z = (o : E)⁻¹ • n1 := by
        rw [osmul, ho', hxeq]; abel
      rw [he]
      exact F0.X.smul_mem _ hn1X
    have he : x = (x - o' • F0.z) + o' • F0.z := by abel
    rw [he]
    exact Submodule.add_mem_sup hdiff (Submodule.mem_span_singleton.2 ⟨o', rfl⟩)
  obtain ⟨ρ, hρN, hρid⟩ := retraction_reduction E S.V Λ N hNΛ hlat.fg hsat

  have hind : LinearIndependent E (Fin.snoc F0.e F0.z : Fin (r + 1) → S.V) :=
    F0.e_indep.finSnoc hznX
  obtain ⟨cf, hcf⟩ := dualFamilyExists E S.V (r + 1) _ hind
  have hcfe : ∀ b a, cf (Fin.castSucc b) (F0.e a) = if b = a then 1 else 0 := by
    intro b a
    have h := hcf (Fin.castSucc b) (Fin.castSucc a)
    simp only [Fin.snoc_castSucc, Fin.castSucc_inj] at h
    exact h
  have hcfz : ∀ b, cf (Fin.castSucc b) F0.z = 0 := by
    intro b
    have h := hcf (Fin.castSucc b) (Fin.last r)
    simp only [Fin.snoc_last, Fin.castSucc_ne_last, if_false] at h
    exact h
  have hcfN : ∀ b, ∀ n ∈ N, cf (Fin.castSucc b) n ∈ aa b := by
    intro b n hn
    obtain ⟨n1, hn1, n2, hn2, rfl⟩ := Submodule.mem_sup.1 hn
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hn2
    rw [map_add (f := _), osmul t, map_smul, hcfz, smul_zero, add_zero]
    clear hn
    induction hn1 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, x, hx, rfl⟩ := hy
      rw [map_smul, hcfe, smul_eq_mul]
      split_ifs with hba
      · subst hba; rw [mul_one]; exact hx
      · rw [mul_zero]; exact fi_zero _
    | zero => rw [map_zero]; exact fi_zero _
    | add y y' _ _ h1 h2 => rw [map_add (f := _)]; exact fi_add h1 h2
    | smul o y _ h1 =>
      rw [osmul o, map_smul, smul_eq_mul, ← Algebra.smul_def]
      exact fi_smul o h1

  have hw := fun b : Fin r =>
    sesquilinearRepresentation E S.V S.hT S.nondeg Λ hlat (((cf (Fin.castSucc b)).restrictScalars (𝓞 E)).comp ρ)
  choose f hf using hw
  have hfv : ∀ b, ∀ x (hx : x ∈ Λ), S.hT (f b) x = cf (Fin.castSucc b) (ρ ⟨x, hx⟩) :=
    fun b x hx => hf b ⟨x, hx⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a b
    have hne : (aa a : Submodule (𝓞 E) E) ≠ ⊥ := FractionalIdeal.coeToSubmodule_ne_bot.2 (haa a)
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hxa : x • F0.e a ∈ Formalism.L2.SG.Saturated.latSpan aa F0.e :=
      Submodule.subset_span ⟨a, x, hx, rfl⟩
    have h1 := hfv b (x • F0.e a) (hlatΛ hxa)
    rw [hρid ⟨_, hlatΛ hxa⟩ (Submodule.mem_sup_left hxa)] at h1
    simp only [map_smul, hcfe, smul_eq_mul] at h1
    have h2 : S.hT (f b) (F0.e a) = if b = a then 1 else 0 := mul_left_cancel₀ hx0 h1
    have h3 := S.herm.eq (f b) (F0.e a)
    rw [h2] at h3
    rw [← h3]
    split_ifs with h4 h5 h5
    · simp
    · exact absurd h4.symm h5
    · exact absurd h5.symm h4
    · simp
  · intro b
    rw [hfv b F0.z hz, hρid ⟨F0.z, hz⟩ hzN]
    exact hcfz b
  · intro b x hx
    rw [hfv b x hx]
    exact hcfN b _ (hρN _)

end PI.SRW
