module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.RepIndep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPushforward

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberCardFormula
theorem UpperTheory.orbitalFiber_card_formula : UpperTheory.V.Z.Sym.Glob.Fib.CardFib := by
  intro G _ S U U' x Ux s₀ hS hU hx
  classical
  have hmem : ∀ w : ↥(U' ⊓ S), (s₀ : G) * x * (w : G) * x⁻¹ ∈ S := by
    intro w
    have h1 := S.mul_mem s₀.2 (hS.conj_mem (w : G) (Subgroup.mem_inf.1 w.2).2 x)
    simpa [mul_assoc] using h1
  let g : ↥(U' ⊓ S) → ↥S ⧸ Ux := fun w => ((⟨_, hmem w⟩ : ↥S) : ↥S ⧸ Ux)
  have hg : ∀ w w' : ↥(U' ⊓ S), g w = g w' ↔ (w : G)⁻¹ * (w' : G) ∈ U := by
    intro w w'
    simp only [g]
    rw [QuotientGroup.eq, hx]
    have e : x⁻¹ * (((⟨_, hmem w⟩ : ↥S)⁻¹ * ⟨_, hmem w'⟩ : ↥S) : G) * x = (w : G)⁻¹ * (w' : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
  have hgT : ∀ w, g w ∈ {s : ↥S ⧸ Ux | (((Quotient.out s : ↥S) : G) * x : G ⧸ U') = ((s₀ : G) * x : G ⧸ U')} := by
    intro w
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul Ux (⟨_, hmem w⟩ : ↥S)
    simp only [Set.mem_setOf_eq, g]
    rw [hk, QuotientGroup.eq]
    have hkU : x⁻¹ * ((k : ↥S) : G) * x ∈ U' := hU ((hx k).1 k.2)
    have e : ((((⟨_, hmem w⟩ : ↥S) * (k : ↥S) : ↥S) : G) * x)⁻¹ * ((s₀ : G) * x) =
        (x⁻¹ * ((k : ↥S) : G) * x)⁻¹ * ((w : G))⁻¹ := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact U'.mul_mem (U'.inv_mem hkU) (U'.inv_mem (Subgroup.mem_inf.1 w.2).1)
  rw [← Nat.card_coe_set_eq]
  unfold Subgroup.relIndex Subgroup.index
  let F : ↥(U' ⊓ S) ⧸ U.subgroupOf (U' ⊓ S) →
      {s : ↥S ⧸ Ux | (((Quotient.out s : ↥S) : G) * x : G ⧸ U') = ((s₀ : G) * x : G ⧸ U')} :=
    Quotient.lift (fun w => ⟨g w, hgT w⟩) (fun a b hab => Subtype.ext ((hg a b).2 (by
      have h := QuotientGroup.leftRel_apply.1 hab
      simpa [Subgroup.mem_subgroupOf] using h)))
  refine (Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)).symm
  · intro a b hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have h := congrArg Subtype.val hab
    change g a = g b at h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using (hg a b).1 h
  · rintro ⟨s, hs⟩
    rw [Set.mem_setOf_eq] at hs
    have hwS : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x ∈ S := by
      simpa using hS.conj_mem _ (S.mul_mem (S.inv_mem s₀.2) (Quotient.out s).2) x⁻¹
    have hwU : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x ∈ U' := by
      have h1 := QuotientGroup.eq.1 hs
      have e : x⁻¹ * ((s₀ : G)⁻¹ * ((Quotient.out s : ↥S) : G)) * x =
          ((((Quotient.out s : ↥S) : G) * x)⁻¹ * ((s₀ : G) * x))⁻¹ := by
        group
      rw [e]
      exact U'.inv_mem h1
    refine ⟨((⟨_, Subgroup.mem_inf.2 ⟨hwU, hwS⟩⟩ : ↥(U' ⊓ S)) : ↥(U' ⊓ S) ⧸ U.subgroupOf (U' ⊓ S)),
      Subtype.ext ?_⟩
    change g _ = s
    conv_rhs => rw [← QuotientGroup.out_eq' s]
    simp only [g]
    congr 1
    apply Subtype.ext
    dsimp only
    group
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricFiberCovering
open MulAction

theorem UpperTheory.symmetric_fiber_covering : UpperTheory.V.Z.Sym.Glob.Fib.Cover := by
  intro H G _ _ S U U' x Ux ι Φ hS hU hUx hr hL hR hT hfin
  classical
  letI a1 : MulAction H (S ⧸ Ux) := MulAction.compHom _ ι
  letI a2 : MulAction H (G ⧸ U') := MulAction.compHom _ (S.subtype.comp ι)
  let q : S ⧸ Ux → G ⧸ U' := fun y => (((y.out : S) : G) * x : G)
  let k : S ⧸ Ux → ℂ := fun y => Φ (((y.out : S) : G) * x)
  have hΦ : ∀ a b : G, (a : G ⧸ U') = b → Φ a = Φ b := by
    intro a b e
    have hm : a⁻¹ * b ∈ U' := QuotientGroup.eq.1 e
    have := hR _ hm a
    rw [← this]
    congr 1
    group
  have hq0 : ∀ s : S, q (s : S ⧸ Ux) = (((s : G) * x : G) : G ⧸ U') := by
    intro s
    have h1 : ((s : S ⧸ Ux).out)⁻¹ * s ∈ Ux := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    have h2 := hU ((hUx _).1 h1)
    show ((((s : S ⧸ Ux).out : G) * x : G) : G ⧸ U') = _
    rw [QuotientGroup.eq]
    have e : (((s : S ⧸ Ux).out : G) * x)⁻¹ * ((s : G) * x) = x⁻¹ * ((((s : S ⧸ Ux).out)⁻¹ * s : S) : G) * x := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h2
  have hq : ∀ (h : H) (y : S ⧸ Ux), q (h • y) = h • q y := by
    intro h y
    induction y using QuotientGroup.induction_on with | H s => ?_
    have e1 : h • (s : S ⧸ Ux) = ((ι h * s : S) : S ⧸ Ux) := rfl
    rw [e1, hq0, hq0]
    have e2 : ∀ z : G ⧸ U', h • z = ((ι h : S) : G) • z := fun _ => rfl
    rw [e2, Subgroup.coe_mul, mul_assoc]
    rfl
  have hkq : ∀ y, k y = Φ (q y).out := fun y => hΦ _ _ (QuotientGroup.out_eq' (q y)).symm
  have hk : ∀ (h : H) y, k (h • y) = k y := by
    intro h y
    rw [hkq, hkq, hq]
    have e2 : h • q y = ((((ι h : S) : G) * (q y).out : G) : G ⧸ U') := by
      conv_lhs => rw [← QuotientGroup.out_eq' (q y)]
      rfl
    have := hΦ _ _ ((QuotientGroup.out_eq' (h • q y)).trans e2)
    rw [this]
    exact hL h _
  have hT' : ∃ T : Finset (S ⧸ Ux), ∀ y, k y ≠ 0 → ∃ h : H, ∃ s ∈ T, y = h • s := by
    obtain ⟨T, hT⟩ := hT
    refine ⟨T.image (fun t : S => (QuotientGroup.mk t : S ⧸ Ux)), fun y _ => ?_⟩
    induction y using QuotientGroup.induction_on with | H s => ?_
    obtain ⟨h, t, ht, u, hu, e⟩ := hT s
    refine ⟨h, (QuotientGroup.mk t : S ⧸ Ux), Finset.mem_image_of_mem (fun t : S => (QuotientGroup.mk t : S ⧸ Ux)) ht, ?_⟩
    rw [e]
    show ((ι h * t * u : S) : S ⧸ Ux) = ((ι h * t : S) : S ⧸ Ux)
    exact QuotientGroup.mk_mul_of_mem _ hu
  have hcard : ∀ s₀ : S, {y | q y = (((s₀ : G) * x : G) : G ⧸ U')}.ncard = U.relIndex (U' ⊓ S) :=
    fun s₀ => UpperTheory.orbitalFiber_card_formula G S U U' x Ux s₀ hS hU hUx
  have hfinF : ∀ s₀ : S, {y | q y = (((s₀ : G) * x : G) : G ⧸ U')}.Finite := fun s₀ =>
    Set.finite_of_ncard_ne_zero (by rw [hcard]; exact hr)
  have hfib : ∀ z, {y | q y = z ∧ k y ≠ 0}.Finite := by
    intro z
    by_cases hz : ∃ y, q y = z
    · obtain ⟨y, rfl⟩ := hz
      exact (hfinF y.out).subset fun w hw => hw.1
    · refine Set.Finite.subset Set.finite_empty fun w hw => hz ⟨w, hw.1⟩
  have hrel : ∀ y, k y ≠ 0 → (⊥ : Subgroup H).relIndex (stabilizer H (q y)) ≠ 0 := by
    intro y _
    rw [Subgroup.relIndex_bot_left]
    have hs : ((stabilizer H (q y) : Subgroup H) : Set H).Finite := by
      refine (hfin (q y).out).subset fun h hh => ?_
      have hh' : h • q y = q y := hh
      have e2 : h • q y = ((((ι h : S) : G) * (q y).out : G) : G ⧸ U') := by
        conv_lhs => rw [← QuotientGroup.out_eq' (q y)]
        rfl
      rw [e2] at hh'
      have e3 : (((q y).out : G) : G ⧸ U') = ((((ι h : S) : G) * (q y).out : G) : G ⧸ U') :=
        (QuotientGroup.out_eq' (q y)).trans hh'.symm
      have := QuotientGroup.eq.1 e3
      show ((q y).out)⁻¹ * ((ι h : S) : G) * (q y).out ∈ U'
      rwa [mul_assoc]
    haveI : Finite (stabilizer H (q y)) := hs.to_subtype
    exact Nat.card_pos.ne'
  have hpush := UpperTheory.orbitalFiber_pushforward H (S ⧸ Ux) (G ⧸ U') ⊥ q k inferInstance hq
    (fun z hz y => by rw [Subgroup.mem_bot.1 hz, one_smul]) hk hT' hfib hrel
  have hK : (fun z : G ⧸ U' => ∑ᶠ (y : S ⧸ Ux) (_ : q y = z), k y) =
      fun z => (U.relIndex (U' ⊓ S) : ℂ) * (orbit S (x : G ⧸ U')).indicator (fun y => Φ y.out) z := by
    funext z
    by_cases hz : z ∈ orbit S (x : G ⧸ U')
    · rw [Set.indicator_of_mem hz]
      obtain ⟨s₀, rfl⟩ := hz
      have e0 : (fun m : S => m • (x : G ⧸ U')) s₀ = (((s₀ : G) * x : G) : G ⧸ U') := rfl
      rw [e0]
      set z : G ⧸ U' := (((s₀ : G) * x : G) : G ⧸ U') with hzdef
      have step : (∑ᶠ (y : S ⧸ Ux) (_ : q y = z), k y) = ∑ᶠ y ∈ {y | q y = z}, Φ z.out :=
        by
          change (∑ᶠ y ∈ {y | q y = z}, k y) = ∑ᶠ y ∈ {y | q y = z}, Φ z.out
          exact finsum_mem_congr rfl fun y hy => by
            have hy' : q y = z := hy
            rw [hkq, hy']
      rw [step, finsum_mem_eq_finite_toFinset_sum _ (hfinF s₀), Finset.sum_const, nsmul_eq_mul,
        ← Set.ncard_eq_toFinset_card _ (hfinF s₀), hcard]
    · rw [Set.indicator_of_notMem hz, mul_zero]
      have h0 : ∀ y : S ⧸ Ux, (∑ᶠ (_ : q y = z), k y) = 0 := by
        intro y
        refine finsum_eq_if.trans (if_neg fun e => hz ?_)
        exact ⟨y.out, e⟩
      simp only [h0, finsum_zero]
  have hbot := (UpperTheory.orbitalFiber_of_bot H (G ⧸ U') ⊥ ((orbit S (x : G ⧸ U')).indicator fun y => Φ y.out)).1
    (U.relIndex (U' ⊓ S) : ℂ)
  show UpperTheory.V.Z.Sym.gq ⊥ k = (U.relIndex (U' ⊓ S) : ℂ) *
    UpperTheory.V.Z.Sym.gq ⊥ ((orbit S (x : G ⧸ U')).indicator fun y => Φ y.out)
  rw [hpush, hK]
  exact hbot
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberSumOverFibers
open MulAction

private theorem conj_memS {G : Type} [Group G] {S : Subgroup G} (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S)
    {s : G} (hs : s ∈ S) (a : G) : a * s * a⁻¹ ∈ S := by
  have h : a * s * a⁻¹ = (a * s * a⁻¹ * s⁻¹) * s := by group
  rw [h]
  exact S.mul_mem (hc a s) hs

private theorem mem_orb {G : Type} [Group G] (S U : Subgroup G) (x : G) (y : G ⧸ U) :
    y ∈ orbit S (x : G ⧸ U) ↔ ∃ s ∈ S, y = ((s * x : G) : G ⧸ U) := by
  constructor
  · rintro ⟨⟨s, hs⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩

private theorem sup_act {G : Type} [Group G] {S U : Subgroup G} (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S)
    {g : G} (hg : g ∈ S ⊔ U) (x : G) {y : G ⧸ U} (hy : y ∈ orbit S (x : G ⧸ U)) :
    g • y ∈ orbit S (x : G ⧸ U) := by
  haveI : S.Normal := ⟨fun n hn a => conj_memS hc hn a⟩
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hg
  obtain ⟨s, hs, u, hu, rfl⟩ := hg
  obtain ⟨s₀, hs₀, rfl⟩ := (mem_orb S U x y).1 hy
  refine (mem_orb S U x _).2 ⟨s * (u * s₀ * x * u⁻¹ * x⁻¹), S.mul_mem hs ?_, ?_⟩
  · convert S.mul_mem (conj_memS hc hs₀ u) (hc u x) using 1
    group
  · rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
    convert U.inv_mem hu using 1
    group

private theorem phi_out {G : Type} [Group G] (U : Subgroup G) (Φ : G → ℂ) (hΦu : ∀ u ∈ U, ∀ g, Φ (g * u) = Φ g) (g : G) :
    Φ ((g : G ⧸ U).out) = Φ g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  rw [hu, hΦu _ u.2]

theorem UpperTheory.orbitalFiber_sum_over_fibers :
    UpperTheory.V.Z.Sym.Glob.Fib.SumFib := by
  intro Γ G I _ _ _ ι S U' Γ₀ x Φ hc hN hΦl hΦu hT hdisj hcov
  classical
  let Γ' : Subgroup Γ := Subgroup.comap ι (S ⊔ U')
  letI A : MulAction Γ (G ⧸ U') := MulAction.compHom _ ι
  letI B : MulAction Γ' (G ⧸ U') := MulAction.compHom _ (ι.comp Γ'.subtype)
  let k : G ⧸ U' → ℂ := fun y => Φ y.out
  let ki : I → G ⧸ U' → ℂ := fun i => (orbit S (x i : G ⧸ U')).indicator k
  have hsmul : ∀ (h : Γ) (g : G), h • (g : G ⧸ U') = ((ι h * g : G) : G ⧸ U') := fun h g => rfl
  have hk : ∀ g : G, k g = Φ g := phi_out U' Φ hΦu
  have hkinv : ∀ (h : Γ) (y : G ⧸ U'), k (h • y) = k y := by
    intro h y
    refine QuotientGroup.induction_on y fun g => ?_
    rw [hsmul, hk, hk, hΦl]
  have hki_mem : ∀ i y, ki i y ≠ 0 → y ∈ orbit S (x i : G ⧸ U') :=
    fun i y h => Set.mem_of_indicator_ne_zero h
  have hD := @UpperTheory.orbitalFiber_decomposition Γ (G ⧸ U') I _ A Γ₀ k (fun _ => Γ') (fun _ => G ⧸ U')
    (fun _ => inferInstance) (fun _ => B) (fun _ => Γ'.subtype) (fun _ => id) ki hN hkinv
    ?_ (fun _ _ _ => rfl) (fun _ => Function.injective_id) ?_ ?_ ?_ ?_
  · show UpperTheory.V.Z.Sym.gq Γ₀ k = ∑ i, UpperTheory.V.Z.Sym.gq (Γ₀.subgroupOf Γ') (ki i)
    rw [hD, finsum_eq_sum_of_fintype]
    rfl
  · obtain ⟨T, hT⟩ := hT
    refine ⟨T.image (fun g : G => (g : G ⧸ U')), fun y => ?_⟩
    refine QuotientGroup.induction_on y fun g _ => ?_
    obtain ⟨γ, s, hs, u, hu, rfl⟩ := hT g
    refine ⟨γ, (s : G ⧸ U'), Finset.mem_image_of_mem _ hs, ?_⟩
    rw [hsmul, QuotientGroup.eq]
    convert U'.inv_mem hu using 1
    group
  · intro i h y
    have hh : ι h ∈ S ⊔ U' := h.2
    have e : h • y = (ι h) • y := rfl
    have hmem : h • y ∈ orbit S (x i : G ⧸ U') ↔ y ∈ orbit S (x i : G ⧸ U') := by
      rw [e]
      constructor
      · intro hy'
        simpa using sup_act hc (Subgroup.inv_mem _ hh) (x i) hy'
      · intro hy
        exact sup_act hc hh (x i) hy
    show Set.indicator _ k (h • y) = Set.indicator _ k y
    by_cases hy : y ∈ orbit S (x i : G ⧸ U')
    · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hmem.2 hy), if_pos hy]
      exact hkinv (h : Γ) y
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg (mt hmem.1 hy), if_neg hy]
  · intro i y h
    exact (Set.indicator_of_mem (hki_mem i y h) k).symm
  · intro z
    refine QuotientGroup.induction_on z fun g hz => ?_
    obtain ⟨i, γ, s, hs, u, hu, rfl⟩ := hcov g
    have hy : ((s * x i : G) : G ⧸ U') ∈ orbit S (x i : G ⧸ U') := (mem_orb S U' _ _).2 ⟨s, hs, rfl⟩
    have hval : k ((s * x i : G) : G ⧸ U') = k ((ι γ * s * x i * u : G) : G ⧸ U') := by
      rw [hk, hk, hΦu _ hu, mul_assoc (ι γ) s, hΦl]
    refine ⟨i, ((s * x i : G) : G ⧸ U'), γ, ?_, ?_⟩
    · rw [show ki i _ = k _ from Set.indicator_of_mem hy k, hval]
      exact hz
    · show _ = γ • ((s * x i : G) : G ⧸ U')
      rw [hsmul, QuotientGroup.eq]
      convert U'.inv_mem hu using 1
      group
  · intro i j y y' h hy hy' he
    obtain ⟨s, hs, rfl⟩ := (mem_orb S U' _ _).1 (hki_mem i y hy)
    obtain ⟨s', hs', rfl⟩ := (mem_orb S U' _ _).1 (hki_mem j y' hy')
    change ((ι h * (s * x i) : G) : G ⧸ U') = ((s' * x j : G) : G ⧸ U') at he
    rw [QuotientGroup.eq] at he
    obtain ⟨u, hu_mem, hu_eq⟩ : ∃ u ∈ U', (ι h * (s * x i))⁻¹ * (s' * x j) = u := ⟨_, he, rfl⟩
    have hxj : x j = ι h * ((ι h)⁻¹ * s'⁻¹ * ι h * s) * x i * u := by
      rw [← hu_eq]
      group
    have e2 : ι h = s' * x j * u⁻¹ * (x i)⁻¹ * s⁻¹ := by
      rw [← hu_eq]
      group
    have hmid : (ι h)⁻¹ * s'⁻¹ * ι h * s ∈ S :=
      S.mul_mem (by simpa using conj_memS hc (S.inv_mem hs') (ι h)⁻¹) hs
    have key : ∀ X : G, s' * X * u⁻¹ * X⁻¹ * s⁻¹ ∈ S ⊔ U' := by
      intro X
      have e3 : s' * X * u⁻¹ * X⁻¹ * s⁻¹ = s' * (X * u⁻¹ * X⁻¹ * u⁻¹⁻¹) * u⁻¹ * s⁻¹ := by group
      rw [e3]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hs')
        (Subgroup.mem_sup_left (hc _ _))) (Subgroup.mem_sup_right (U'.inv_mem hu_mem)))
        (Subgroup.mem_sup_left (S.inv_mem hs))
    have hij := hdisj i j h _ hmid u hu_mem hxj
    subst hij
    refine ⟨rfl, ⟨h, ?_⟩, rfl⟩
    show ι h ∈ S ⊔ U'
    rw [e2]
    exact key _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberSingle
open MulAction in
theorem UpperTheory.orbitalFiber_single :
    UpperTheory.V.Z.Sym.Glob.Fib.OneFib := by
  intro Γ G _ _ ι S U' Γ₁ Γ₀ x Φ hcomm hΓS hN htriv hΦl hΦr hTex hst hrel hcard
  classical
  haveI hSn : S.Normal := ⟨fun n hn g => by
    convert S.mul_mem (hcomm g n) hn using 1
    group⟩
  set C := Subgroup.comap ι (S ⊔ U') with hC
  set f := (orbit ↥S (x : G ⧸ U')).indicator fun y => Φ (Quotient.out y) with hf
  have hΓC : Γ₁ ≤ C := fun a ha =>
    Subgroup.mem_comap.mpr ((le_sup_left : S ≤ S ⊔ U') (Subgroup.mem_comap.mp (hΓS ha)))
  let j : C →* G := ι.comp C.subtype
  let φ : Γ₁ →* C := Subgroup.inclusion hΓC
  have hclos : ∀ g ∈ S ⊔ U', ∀ y ∈ orbit ↥S (x : G ⧸ U'), g • y ∈ orbit ↥S (x : G ⧸ U') := by
    intro g hg y hy
    obtain ⟨s, hs, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg
    obtain ⟨⟨s', hs'⟩, rfl⟩ := hy
    refine ⟨⟨s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s', S.mul_mem (S.mul_mem hs (hcomm _ _)) hs'⟩, ?_⟩
    show ((s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s' * x : G) : G ⧸ U') = ((s * u * (s' * x) : G) : G ⧸ U')
    rw [QuotientGroup.eq]
    have he : (s * (u * (s' * x) * u⁻¹ * (s' * x)⁻¹) * s' * x)⁻¹ * (s * u * (s' * x)) = u := by group
    rw [he]
    exact hu
  have hinv : ∀ (h : C) (y : G ⧸ U'), f (j h • y) = f y := by
    intro h y
    have hg : ι h.1 ∈ S ⊔ U' := h.2
    change f (ι h.1 • y) = f y
    by_cases hy : y ∈ orbit ↥S (x : G ⧸ U')
    · have hy' := hclos _ hg y hy
      rw [hf, Set.indicator_of_mem hy', Set.indicator_of_mem hy]
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U' (ι h.1 * Quotient.out y)
      have hyy : ι h.1 • y = ((ι h.1 * Quotient.out y : G) : G ⧸ U') := by
        conv_lhs => rw [← QuotientGroup.out_eq' y]
        rfl
      rw [hyy, hu, hΦr _ u.2, hΦl]
    · have hy' : ι h.1 • y ∉ orbit ↥S (x : G ⧸ U') := fun hm => hy (by
        have := hclos _ (inv_mem hg) _ hm
        rwa [inv_smul_smul] at this)
      rw [hf, Set.indicator_apply, if_neg hy', Set.indicator_apply, if_neg hy]
  have hfin : ∃ T' : Finset (G ⧸ U'), ∀ y, f y ≠ 0 → ∃ h : C, ∃ x' ∈ T', y = j h • x' := by
    obtain ⟨T, hT⟩ := hTex
    refine ⟨T.image (QuotientGroup.mk : G → G ⧸ U'), ?_⟩
    intro y hy
    obtain ⟨⟨s, hs⟩, rfl⟩ := Set.mem_of_indicator_ne_zero hy
    obtain ⟨h, hh, t, ht, u, hu, he⟩ := hT s hs
    refine ⟨⟨h, hΓC hh⟩, (t : G ⧸ U'), Finset.mem_image_of_mem QuotientGroup.mk ht, ?_⟩
    show ((s * x : G) : G ⧸ U') = ((ι h * t : G) : G ⧸ U')
    rw [he, QuotientGroup.eq]
    rw [show (ι h * t * u)⁻¹ * (ι h * t) = u⁻¹ by group]
    exact inv_mem hu
  have hsup : φ.range ⊔ Γ₀.subgroupOf C = (Γ₁ ⊔ Γ₀).subgroupOf C := by
    ext z
    rw [Subgroup.mem_sup_of_normal_right, Subgroup.mem_subgroupOf, Subgroup.mem_sup_of_normal_right]
    constructor
    · rintro ⟨a, ⟨a', rfl⟩, b, hb, rfl⟩
      exact ⟨a'.1, a'.2, b.1, Subgroup.mem_subgroupOf.mp hb, rfl⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      have hbC : b ∈ C := by
        have hb' : b = a⁻¹ * (z : Γ) := by rw [← hab]; group
        rw [hb']
        exact C.mul_mem (C.inv_mem (hΓC ha)) z.2
      exact ⟨φ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, ⟨b, hbC⟩, Subgroup.mem_subgroupOf.mpr hb, Subtype.ext hab⟩
  have hidx : (φ.range ⊔ Γ₀.subgroupOf C).index = (Γ₁ ⊔ Γ₀).relIndex C := by
    rw [hsup]
    rfl
  have key := UpperTheory.V.Z.Sym.Tf.gqIndex Γ₁ C G φ j (Γ₀.subgroupOf C) U' f
    inferInstance (fun z hz y => htriv z.1 (Subgroup.mem_subgroupOf.mp hz) y)
    (by rw [hidx]; exact hrel) hinv hfin
    (fun y _ => by
      rw [← Subgroup.comap_comap]
      exact Subgroup.relIndex_comap_ne_zero _ (hst y))
  have e1 : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) (Γ₀.subgroupOf Γ₁) U' f =
      UpperTheory.V.Z.Sym.gqOn (j.comp φ) (Subgroup.comap φ (Γ₀.subgroupOf C)) U' f := rfl
  have hb : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) (Γ₀.subgroupOf Γ₁) U' f =
      ↑(Nat.card ↥(Γ₀.subgroupOf Γ₁)) * UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) ⊥ U' f := by
    letI := MulAction.compHom (G ⧸ U') (ι.comp Γ₁.subtype)
    exact (UpperTheory.orbitalFiber_of_bot Γ₁ (G ⧸ U') (Γ₀.subgroupOf Γ₁) f).2 hcard
      (fun z hz y => htriv z.1 (Subgroup.mem_subgroupOf.mp hz) y)
  rw [← hb, e1, key, hidx]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberIndexFinite
namespace UpperTheory

private lemma relIndex_normal_sup {Γ : Type} [Group Γ] (N A C : Subgroup Γ) [N.Normal] (hN : N ≤ A)
    (h : A.relIndex C ≠ 0) : A.relIndex (N ⊔ C) ≠ 0 := by
  have hA : (A.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = A := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.2 hN]
  have key : ∀ K : Subgroup Γ, A.relIndex K = (A.map (QuotientGroup.mk' N)).relIndex (K.map (QuotientGroup.mk' N)) := by
    intro K
    rw [← Subgroup.relIndex_comap, hA]
  have hm : (N ⊔ C).map (QuotientGroup.mk' N) = C.map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_sup]
    have : N.map (QuotientGroup.mk' N) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [this, bot_sup_eq]
  rw [key, hm, ← key]
  exact h

theorem orbitalFiber_index_finite : V.Z.Sym.Glob.Fib.IndexFin := by
  intro Γ G _ _ ι S U' Γ₁ Γ₀ hS hΓ₁ hT h0
  obtain ⟨T, hT⟩ := hT
  have hAC : (Γ₁ ⊔ Γ₀).relIndex (U'.comap ι) ≠ 0 := by
    intro h
    apply h0
    have := Subgroup.relIndex_dvd_of_le_left (U'.comap ι) (le_sup_right : Γ₀ ≤ Γ₁ ⊔ Γ₀)
    rw [h] at this
    exact Nat.eq_zero_of_zero_dvd this
  have h1 : (Γ₁ ⊔ Γ₀).relIndex (Γ₁ ⊔ U'.comap ι) ≠ 0 :=
    relIndex_normal_sup Γ₁ _ _ le_sup_left hAC
  have pick : ∀ b : ((S ⊔ U').comap ι : Subgroup Γ), ∃ t, t ∈ T ∧ ∃ h ∈ Γ₁, ∃ u ∈ U',
      ι (b : Γ) = ι h * t * u := by
    intro b
    have hb : ι (b : Γ) ∈ S ⊔ U' := b.2
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hb
    obtain ⟨s, hs, u, hu, e⟩ := hb
    obtain ⟨h, hh, t, ht, u₂, hu₂, rfl⟩ := hT s hs
    exact ⟨t, ht, h, hh, u₂ * u, U'.mul_mem hu₂ hu, by rw [← e]; group⟩
  choose f hfT hf using pick
  have h2 : (Γ₁ ⊔ U'.comap ι).relIndex ((S ⊔ U').comap ι) ≠ 0 := by
    have inj : Function.Injective
        (fun q : ((S ⊔ U').comap ι : Subgroup Γ) ⧸ (Γ₁ ⊔ U'.comap ι).subgroupOf ((S ⊔ U').comap ι) =>
          (⟨f q.out, hfT _⟩ : T)) := by
      intro q q' hq
      have hq' : f q.out = f q'.out := congrArg Subtype.val hq
      rw [← q.out_eq', ← q'.out_eq', QuotientGroup.eq, Subgroup.mem_subgroupOf]
      generalize q.out = a at hq'
      generalize q'.out = b at hq'
      obtain ⟨h, hh, u, hu, ha⟩ := hf a
      obtain ⟨h', hh', u', hu', hb⟩ := hf b
      rw [← hq'] at hb
      have hx : (a : Γ)⁻¹ * (h' * h⁻¹) * a ∈ Γ₁ := by
        simpa using hΓ₁.conj_mem (h' * h⁻¹) (Γ₁.mul_mem hh' (Γ₁.inv_mem hh)) (a : Γ)⁻¹
      have hc : (a : Γ)⁻¹ * h * h'⁻¹ * b ∈ U'.comap ι := by
        have : ι ((a : Γ)⁻¹ * h * h'⁻¹ * b) = u⁻¹ * u' := by
          simp only [map_mul, map_inv, ha, hb]
          group
        rw [Subgroup.mem_comap, this]
        exact U'.mul_mem (U'.inv_mem hu) hu'
      have e : (((a⁻¹ * b : ((S ⊔ U').comap ι : Subgroup Γ))) : Γ)
          = ((a : Γ)⁻¹ * (h' * h⁻¹) * a) * ((a : Γ)⁻¹ * h * h'⁻¹ * b) := by
        push_cast
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hc)
    haveI := Finite.of_injective _ inj
    exact Subgroup.index_ne_zero_of_finite
  exact Subgroup.relIndex_ne_zero_trans h1 h2

end UpperTheory
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberStabilizerFinite
namespace UpperTheory

theorem orbitalFiber_stabilizer_finite : UpperTheory.V.Z.Sym.Glob.Fib.StabFin := by
  intro H G _ _ S U U' ι x hS hidx hfin
  let ψ : H →* G := (MulAut.conj x⁻¹).toMonoidHom.comp (S.subtype.comp ι)
  have hψ : ∀ h, ψ h = x⁻¹ * ι h * x := fun h => by simp [ψ]
  have hB : (U' ⊓ S).comap ψ = U'.comap ψ := by
    ext h
    simp only [Subgroup.mem_comap, Subgroup.mem_inf, and_iff_left_iff_imp]
    intro _
    rw [hψ]
    simpa using hS.conj_mem _ (ι h).2 x⁻¹
  have h1 : (U.comap ψ).relIndex (U'.comap ψ) ≠ 0 := by
    rw [← hB]
    exact Subgroup.relIndex_comap_ne_zero ψ hidx
  have hA : Finite (U.comap ψ) := by
    have : ((U.comap ψ : Subgroup H) : Set H).Finite := by
      convert hfin using 1
      ext h
      simp [hψ]
    exact this.to_subtype
  have hA' : Finite ((U.comap ψ).subgroupOf (U'.comap ψ)) :=
    Finite.of_injective (fun a => (⟨a.1.1, a.2⟩ : U.comap ψ)) (fun a b hab => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : U.comap ψ => (z : H)) hab)
  have hq : Finite ((U'.comap ψ) ⧸ (U.comap ψ).subgroupOf (U'.comap ψ)) :=
    Nat.finite_of_card_ne_zero h1
  have hfB : Finite (U'.comap ψ) :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup
      (s := (U.comap ψ).subgroupOf (U'.comap ψ))).symm
  have : ((U'.comap ψ : Subgroup H) : Set H).Finite := Set.toFinite _
  convert this using 1
  ext h
  simp [hψ]

end UpperTheory
end

open MulAction in
theorem UpperTheory.symmetric_fiber_master_formula :
    UpperTheory.V.Z.Sym.Glob.Fib.Master := by
  intro Γ G _ _ ι S U U' Γ₁ Γ₀ ι₁ hι₁ hcomm hΓ₁ hΓ₀ htriv hUU' hidx hfinT hfinS hT hstab
  classical
  haveI hSN : S.Normal := ⟨fun s hs g => by
    have h := S.mul_mem (hcomm g s) hs
    simpa [mul_assoc] using h⟩
  have hcomp : S.subtype.comp ι₁ = ι.comp Γ₁.subtype := MonoidHom.ext fun γ => hι₁ γ
  have hsub : Γ₁ ≤ S.comap ι := fun γ hγ => by
    have h := (ι₁ ⟨γ, hγ⟩).2
    rw [hι₁] at h
    exact h
  have hfinU' : ∀ g : G, {h : Γ₁ | g⁻¹ * ι₁ h * g ∈ U'}.Finite := fun g =>
    UpperTheory.orbitalFiber_stabilizer_finite Γ₁ G S U U' ι₁ g hSN hidx (hfinS g)

  have hn : Nat.card (Γ₀.subgroupOf Γ₁) ≠ 0 := by
    have hsubset : ((Γ₀.subgroupOf Γ₁ : Subgroup Γ₁) : Set Γ₁) ⊆ {h : Γ₁ | (1 : G)⁻¹ * ι₁ h * 1 ∈ U'} := by
      intro z hz
      have hz' : (z : Γ) ∈ Γ₀ := Subgroup.mem_subgroupOf.1 hz
      have h := htriv _ hz' ((1 : G) : G ⧸ U')
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq] at h
      have h' : ι z ∈ U' := by simpa using U'.inv_mem h
      simpa [hι₁] using h'
    haveI : Finite (Γ₀.subgroupOf Γ₁) := ((hfinU' 1).subset hsubset).to_subtype
    exact Nat.card_pos.ne'
  have hd : (Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) ≠ 0 := by
    refine UpperTheory.orbitalFiber_index_finite Γ G ι S U' Γ₁ Γ₀ hSN hΓ₁ ?_ ?_
    · obtain ⟨T, hT1⟩ := hfinT 1
      refine ⟨T.image (fun t : S => (t : G)), fun s hs => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 ⟨s, hs⟩
      refine ⟨h, h.2, t, Finset.mem_image_of_mem _ ht, u, hUU' (by simpa using hu), ?_⟩
      have e' := congrArg (Subtype.val) e
      simpa [hι₁] using e'
    · have h := hstab ((1 : G) : G ⧸ U')
      rwa [MulAction.stabilizer_quotient] at h
  have hn' : (Nat.card (Γ₀.subgroupOf Γ₁) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine ⟨(U.relIndex (U' ⊓ S) : ℝ) * ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℝ) /
    (Nat.card (Γ₀.subgroupOf Γ₁) : ℝ), ?_, ?_⟩
  · have h1 : (0 : ℝ) < (U.relIndex (U' ⊓ S) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx)
    have h2 : (0 : ℝ) < ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hd)
    have h3 : (0 : ℝ) < (Nat.card (Γ₀.subgroupOf Γ₁) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    exact div_pos (mul_pos h1 h2) h3
  intro I _ x Ux Φ hij hcov hUx hΦl hΦr
  rw [UpperTheory.orbitalFiber_sum_over_fibers Γ G I ι S U' Γ₀ x Φ hcomm hΓ₀ hΦl hΦr hT hij hcov, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcover := UpperTheory.symmetric_fiber_covering Γ₁ G S U U' (x i) (Ux i) ι₁ Φ hSN hUU' (hUx i) hidx
    (fun h g => by rw [hι₁]; exact hΦl _ _) hΦr
    (by
      obtain ⟨T, hT1⟩ := hfinT (x i)
      refine ⟨T, fun s => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 s
      exact ⟨h, t, ht, u, (hUx i u).2 hu, e⟩)
    hfinU'
  have hone := UpperTheory.orbitalFiber_single Γ G ι S U' Γ₁ Γ₀ (x i) Φ hcomm hsub hΓ₀ htriv hΦl hΦr
    (by
      obtain ⟨T, hT1⟩ := hfinT (x i)
      refine ⟨T.image (fun t : S => (t : G) * x i), fun s hs => ?_⟩
      obtain ⟨h, t, ht, u, hu, e⟩ := hT1 ⟨s, hs⟩
      refine ⟨h, h.2, _, Finset.mem_image_of_mem _ ht, _, hUU' hu, ?_⟩
      have e' : s = ι h * t * u := by
        have e2 := congrArg (Subtype.val) e
        simpa [hι₁] using e2
      rw [e']
      group)
    hstab hd hn
  rw [hcover, hcomp]
  have hC : UpperTheory.V.Z.Sym.gqOn (ι.comp Γ₁.subtype) ⊥ U'
      ((orbit S (x i : G ⧸ U')).indicator fun y => Φ y.out) =
      ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℂ) *
        UpperTheory.V.Z.Sym.gqOn (ι.comp ((S ⊔ U').comap ι).subtype) (Γ₀.subgroupOf ((S ⊔ U').comap ι)) U'
          ((orbit S (x i : G ⧸ U')).indicator fun y => Φ y.out) / (Nat.card (Γ₀.subgroupOf Γ₁) : ℂ) := by
    rw [eq_div_iff hn', mul_comm]
    exact hone
  rw [hC]
  push_cast
  ring
