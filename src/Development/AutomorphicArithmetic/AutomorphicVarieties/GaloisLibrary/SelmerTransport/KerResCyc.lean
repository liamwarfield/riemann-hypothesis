module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResSmul
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.ZModInj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotMemSqOfDerivative

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResCyc
open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.kerResCyc :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) (h : U' ≤ U) [(U'.subgroupOf U).Normal] (γ : G), γ ∈ U →
      U ≤ (Subgroup.zpowers γ ⊔ U').topologicalClosure →
      (Module.length R (H0U ρ U') ≠ ⊤ → Module.length R (LinearMap.ker (resU ρ h)) ≤ Module.length R (H0U ρ U)) ∧
      ((∀ m ∈ H0U ρ U', ∃ m' ∈ H0U ρ U', ρ γ m' - m' = m) → Function.Injective (resU ρ h)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U h _ γ hγ hcl
  have memU : ∀ (V : Subgroup G) (m : M), m ∈ H0U ρ V ↔ ∀ g ∈ V, ρ g m = m := by
    intro V m
    simp [H0U, H0, Representation.mem_invariants]
  have hinv : ∀ m ∈ H0U ρ U', ρ γ m ∈ H0U ρ U' := by
    intro m hm
    rw [memU] at hm ⊢
    intro u hu
    have hc := Subgroup.Normal.conj_mem (H := U'.subgroupOf U) ⟨u, h hu⟩
      (by simpa [Subgroup.mem_subgroupOf] using hu) (⟨γ, hγ⟩⁻¹)
    rw [Subgroup.mem_subgroupOf] at hc
    simp only [inv_inv, Subgroup.coe_mul, InvMemClass.coe_inv] at hc
    have e : ρ u (ρ γ m) = ρ γ (ρ (γ⁻¹ * u * γ) m) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, hm _ hc]
  let T : H0U ρ U' →ₗ[R] H0U ρ U' := LinearMap.codRestrict (H0U ρ U')
    ((ρ γ - LinearMap.id) ∘ₗ (H0U ρ U').subtype)
    (fun m => Submodule.sub_mem _ (hinv m m.2) m.2)
  have hT : ∀ m : H0U ρ U', ((T m : H0U ρ U') : M) = ρ γ m - m := fun m => rfl
  obtain ⟨φ, hφ⟩ := kerResGen1 R G M ρ hρ U' U h γ hγ hcl T hT
  refine ⟨fun hfin => ?_, fun hsurj => ?_⟩
  · have hfix : ∀ m : H0U ρ U', T m = 0 → (m : M) ∈ H0U ρ U := by
      intro m hm0
      have hγm : ρ γ m = m := by
        have := congrArg Subtype.val hm0
        rw [hT] at this
        exact sub_eq_zero.mp this
      let S : Subgroup G :=
        { carrier := {g | ρ g m = m}
          mul_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
            rw [hb, ha]
          one_mem' := by simp
          inv_mem' := by
            intro a ha
            simp only [Set.mem_setOf_eq] at *
            calc ρ a⁻¹ m = ρ a⁻¹ (ρ a m) := by rw [ha]
              _ = m := by rw [← Module.End.mul_apply, ← map_mul]; simp }
      have hScl : IsClosed (S : Set G) :=
        IsClosed.preimage (hρ.comp (Continuous.prodMk continuous_id continuous_const))
          (isClosed_singleton (x := (m : M)))
      have hle : Subgroup.zpowers γ ⊔ U' ≤ S :=
        sup_le (Subgroup.zpowers_le.mpr hγm) (fun u hu => (memU U' m).mp m.2 u hu)
      have hUS := hcl.trans (Subgroup.topologicalClosure_minimal _ hle hScl)
      exact (memU U m).mpr fun g hg => hUS hg
    let ι : LinearMap.ker T →ₗ[R] H0U ρ U := LinearMap.codRestrict (H0U ρ U)
      ((H0U ρ U').subtype ∘ₗ (LinearMap.ker T).subtype) (fun m => hfix m m.2)
    have hι : Function.Injective ι := by
      intro a b hab
      have e : ((ι a : H0U ρ U) : M) = ((ι b : H0U ρ U) : M) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext e)
    calc Module.length R (LinearMap.ker (resU ρ h))
        ≤ Module.length R (H0U ρ U' ⧸ LinearMap.range T) := Module.length_le_of_injective φ hφ
      _ = Module.length R (LinearMap.ker T) :=
        (KStar.Selmer.length_ker_eq_length_coker T hfin).symm
      _ ≤ Module.length R (H0U ρ U) := Module.length_le_of_injective ι hι
  · have hq : ∀ x : H0U ρ U' ⧸ LinearMap.range T, x = 0 := by
      intro x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨m', hm', he⟩ := hsurj y y.2
      exact ⟨⟨m', hm'⟩, Subtype.ext (by rw [hT]; exact he)⟩
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have := @hφ ⟨x, hx⟩ 0 (by rw [hq (φ _), hq (φ 0)])
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelUnit
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.CorInv
open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.corInv :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsOpen (U'.subgroupOf U : Set U) →
      ∀ x ∈ invariantsUnderSubgroupH1 ρ U U', U'.relIndex U • x ∈ LinearMap.range (resU ρ h) := by
  classical
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U _ h hopen x hx
  by_cases hfin : U'.relIndex U = 0
  · rw [hfin, zero_smul]
    exact zero_mem _
  haveI : (U'.subgroupOf U).FiniteIndex := ⟨hfin⟩
  haveI : Fintype (U ⧸ U'.subgroupOf U) := Fintype.ofFinite _
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hinv : ∀ g : U, conjU ρ U' g (Submodule.Quotient.mk z) = Submodule.Quotient.mk z :=
    fun g => (Representation.mem_invariants _ _).mp hx g
  have hq : ∀ q : U ⧸ U'.subgroupOf U, ∃ m : M, ∀ u : U',
      ρ (q.out : G) (z.1 (conjHom U' (q.out : G) u)) - z.1 u = ρ u m - m := by
    intro q
    obtain ⟨z', hz1, hz2⟩ := conjU_mk ρ U' (q.out : G) z
    rw [hinv, mk_eq_mk] at hz1
    obtain ⟨m, hm⟩ := hz1
    refine ⟨-m, fun u => ?_⟩
    have e := hm u
    rw [hz2] at e
    rw [map_neg, neg_sub_neg, ← neg_sub ((ρ u) m) m, ← e]
    abel
  choose mq hmq using hq
  let f : U → M := fun g => if hg : (g : G) ∈ U' then z.1 ⟨g, hg⟩ else 0
  have hfc : ContinuousOn f (U'.subgroupOf U : Set U) := by
    rw [continuousOn_iff_continuous_restrict]
    refine (z.2.1.comp (Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun g : (U'.subgroupOf U : Set U) => Subgroup.mem_subgroupOf.mp g.2))).congr ?_
    intro g
    simp [f, dif_pos (Subgroup.mem_subgroupOf.mp g.2)]
  have hfcoc : ∀ g ∈ U'.subgroupOf U, ∀ k ∈ U'.subgroupOf U,
      f (g * k) = f g + (ρ.comp U.subtype) g (f k) := by
    intro g hg k hk
    rw [Subgroup.mem_subgroupOf] at hg hk
    have hgk : ((g * k : U) : G) ∈ U' := by
      rw [Subgroup.coe_mul]
      exact U'.mul_mem hg hk
    simp only [f, dif_pos hg, dif_pos hk, dif_pos hgk]
    exact z.2.2 ⟨g, hg⟩ ⟨k, hk⟩
  obtain ⟨F, hFc, hFcoc, ⟨x0, hx0⟩, -⟩ := GlobalTheory.exists_corestriction_cocycle R U M
    (ρ.comp U.subtype) (U'.subgroupOf U) hopen (fun _ => continuous_of_discreteTopology)
    (fun m => hρ.comp (Continuous.prodMk
      (continuous_subtype_val) continuous_const)) f hfc hfcoc
  let Fz : Z1U ρ U := ⟨F, hFc, hFcoc⟩
  refine ⟨Submodule.Quotient.mk Fz, ?_⟩
  obtain ⟨w, hw1, hw2⟩ := resU_mk ρ h Fz
  rw [hw1, ← Submodule.Quotient.mk_smul, mk_eq_mk]
  refine ⟨x0 + ∑ q, mq q, fun u => ?_⟩
  have hterm : ∀ q : U ⧸ U'.subgroupOf U,
      (ρ.comp U.subtype) q.out (f ((q.out)⁻¹ * ⟨(u : G), h u.2⟩ * q.out)) =
        z.1 u + (ρ u (mq q) - mq q) := by
    intro q
    rw [← hmq q u, add_sub_cancel]
    have hmem : (((q.out)⁻¹ * ⟨(u : G), h u.2⟩ * q.out : U) : G) ∈ U' := by
      have e := ‹U'.Normal›.conj_mem u u.2 ((q.out : G)⁻¹)
      simpa [mul_assoc] using e
    simp only [f, dif_pos hmem]
    rfl
  have hcard : Fintype.card (U ⧸ U'.subgroupOf U) = U'.relIndex U := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [hw2 u]
  show F ⟨(u : G), h u.2⟩ - _ = _
  rw [hx0 ⟨u, h u.2⟩ (Subgroup.mem_subgroupOf.mpr u.2), finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, hcard]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Submodule.coe_smul, Pi.smul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    map_add, map_sum]
  rw [show ((U'.relIndex U • z : Z1U ρ U') : U' → M) u = U'.relIndex U • z.1 u from rfl]
  abel
end

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem relIndex_inf_dvd {G : Type} [Group G] (U' U D : Subgroup G) [U'.Normal] :
    (U' ⊓ D).relIndex (U ⊓ D) ∣ U'.relIndex U := by
  have e : (U' ⊓ D).relIndex (U ⊓ D) = U'.relIndex (U ⊓ D) := by
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
  rw [e]
  have k : ∀ K : Subgroup G, U'.relIndex K = Nat.card (K.map (QuotientGroup.mk' U')) := fun K => by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  rw [k, k]
  exact Subgroup.card_dvd_of_le (Subgroup.map_mono inf_le_left)

private theorem eq_zero_of_nsmul {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {n : ℕ}
    (hn : IsUnit (n : R)) {x : N} (hx : n • x = 0) : x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul R] at hx
  exact (hn.smul_eq_zero).1 hx

theorem UpperTheory.V.Base.selUnit :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsOpen (U'.subgroupOf U : Set U) →
      IsUnit (U'.relIndex U : R) → ∀ (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      Function.Injective (selRes ρ h 𝒟) ∧ LinearMap.range (selRes ρ h 𝒟) = selEig ρ U' h𝒟 U 1 := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U _ h hop hu 𝒟 h𝒟
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : resU ρ h x.1 = 0 := congrArg Subtype.val hx
    exact Subtype.ext (eq_zero_of_nsmul hu (kerResSmul R G M ρ U' U h x.1 h0))
  · ext y
    rw [selEig, eig_one]
    constructor
    · rintro ⟨x, rfl⟩ g
      exact Subtype.ext (restriction_mem_invariant_H1 ρ h x.1 g)
    · intro hy
      have hy' : y.1 ∈ invariantsUnderSubgroupH1 ρ U U' := fun g => congrArg Subtype.val (hy g)
      have h1 := corInv R G M ρ hρ U' U h hop y.1 hy'
      rw [← Nat.cast_smul_eq_nsmul R] at h1
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      have h2 := Submodule.smul_mem _ v h1
      rw [smul_smul, hv, one_smul] at h2
      obtain ⟨x, hx⟩ := h2
      have hxs : x ∈ LocSel ρ U 𝒟 := by
        rw [mem_locSel]
        intro D hD
        have hu' : IsUnit (((U' ⊓ D).relIndex (U ⊓ D) : ℕ) : R) :=
          isUnit_of_dvd_unit (Nat.cast_dvd_cast (relIndex_inf_dvd U' U D)) hu
        refine eq_zero_of_nsmul hu' (kerResSmul R G M ρ _ _ (inf_le_inf_right D h) _ ?_)
        rw [resU_resU, ← resU_resU ρ inf_le_left h, hx]
        exact mem_locSel.1 y.2 D hD
      exact ⟨⟨x, hxs⟩, Subtype.ext hx⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResAb
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem len_le_pi {R Z M ι : Type} [CommRing R] [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M]
    [Fintype ι] (ev : Z →ₗ[R] (ι → M)) (hev : Function.Injective ev) (W : Submodule R Z) (H : ι → Submodule R M)
    (hW : ∀ z ∈ W, ∀ i, ev z i ∈ H i) : Module.length R W ≤ ∑ i, Module.length R (H i) := by
  rw [← Module.length_pi_of_fintype]
  let φ : W →ₗ[R] (∀ i, H i) := LinearMap.pi fun i =>
    LinearMap.codRestrict (H i) ((LinearMap.proj i).comp (ev.comp W.subtype)) fun z => hW z.1 z.2 i
  refine Module.length_le_of_injective φ fun x y hxy => ?_
  refine Subtype.ext (hev (funext fun i => ?_))
  exact congrArg Subtype.val (congrFun hxy i)

private theorem len_abs {R Z K M ι : Type} [CommRing R] [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K] [Fintype ι] (hM : ∀ m : M, Module.length R (Submodule.span R {m}) ≠ ⊤)
    (ev : Z →ₗ[R] (ι → M)) (hev : Function.Injective ev) (π : Z →ₗ[R] K) (hπ : Function.Surjective π) (a : R)
    (ha : ∀ z, π (a • z) = 0) (H : Submodule R M) (hH : ∀ m, a • m = 0 → m ∈ H) :
    Module.length R K ≤ Fintype.card ι * Module.length R H := by
  have hZ : ∀ z : Z, Module.length R (Submodule.span R {z}) ≠ ⊤ := by
    intro z
    refine ne_top_of_le_ne_top ?_ (len_le_pi ev hev _ (fun i => Submodule.span R {ev z i}) ?_)
    · exact ENat.sum_ne_top.2 fun i _ => hM _
    · intro w hw i
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have h1 := lenCokerLe R Z hZ a
  have h2 := len_le_pi ev hev (LinearMap.ker (a • (LinearMap.id : Z →ₗ[R] Z))) (fun _ => H) (by
    intro z hz i
    apply hH
    have : a • z = 0 := hz
    have e := congrFun (congrArg ev this) i
    simpa using e)
  have h3 : Module.length R K ≤ Module.length R (Z ⧸ LinearMap.range (a • (LinearMap.id : Z →ₗ[R] Z))) := by
    refine Module.length_le_of_surjective (Submodule.liftQ _ π ?_) ?_
    · rintro _ ⟨z, rfl⟩
      exact ha z
    · intro k
      obtain ⟨z, rfl⟩ := hπ k
      exact ⟨Submodule.Quotient.mk z, rfl⟩
  refine h3.trans (h1.trans (h2.trans ?_))
  simp

theorem UpperTheory.V.Base.kerResAb :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) [IsPrincipalIdealRing R], ContAction ρ → (∀ m : M, Module.length R (Submodule.span R {m}) ≠ ⊤) → (∀ g, ∃ c : R, ∀ m, ρ g m = c • m) →
      ∀ (U' U : Subgroup G) (h : U' ≤ U), (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') → ∀ T : Finset G, (T : Set G) ⊆ U →
      U ≤ (Subgroup.closure (T : Set G) ⊔ U').topologicalClosure →
      Module.length R (LinearMap.ker (resU ρ h)) ≤ T.card * Module.length R (H0U ρ U) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ _ hρ hM hc U' U h hab T hT hU
  choose c hc using hc
  have hρU : ContAction (ρ.comp U.subtype : Representation R U M) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let Z0 : Submodule R (Z1U ρ U) :=
    { carrier := {z | ∀ u : U, u.1 ∈ U' → z.1 u = 0}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun {x y} hx hy u hu => by
        show x.1 u + y.1 u = 0
        rw [hx u hu, hy u hu, add_zero]
      smul_mem' := fun r x hx u hu => by
        show r • x.1 u = 0
        rw [hx u hu, smul_zero] }
  have hcoc : ∀ (z : Z1U ρ U) (u v : U), z.1 (u * v) = z.1 u + ρ u (z.1 v) := fun z u v => z.2.2 u v
  let ev : Z0 →ₗ[R] (T → M) := LinearMap.pi fun t =>
    (LinearMap.proj (⟨t.1, hT t.2⟩ : U)).comp ((Z1U ρ U).subtype.comp Z0.subtype)
  have hev : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    have h1 : z.1.1 1 = 0 := z.2 1 U'.one_mem
    let K : Subgroup U :=
      { carrier := {u | z.1.1 u = 0}
        one_mem' := h1
        mul_mem' := fun {u v} hu hv => by
          have hu' : z.1.1 u = 0 := hu
          have hv' : z.1.1 v = 0 := hv
          show z.1.1 (u * v) = 0
          rw [hcoc, hu', hv', map_zero, add_zero]
        inv_mem' := fun {u} hu => by
          have hu' : z.1.1 u = 0 := hu
          have e := hcoc z.1 u⁻¹ u
          rw [inv_mul_cancel, h1, hu', map_zero, add_zero] at e
          exact e.symm }
    have hK : IsClosed (K : Set U) := isClosed_eq z.1.2.1 continuous_const
    have hle : Subgroup.closure (T : Set G) ⊔ U' ≤ K.map U.subtype := by
      refine sup_le ((Subgroup.closure_le _).2 fun t ht => ?_) fun u hu => ?_
      · exact ⟨⟨t, hT ht⟩, congrFun hz ⟨t, ht⟩, rfl⟩
      · exact ⟨⟨u, h hu⟩, z.2 _ hu, rfl⟩
    refine Subtype.ext (Subtype.ext (funext fun u => ?_))
    have : u ∈ closure (K : Set U) := by
      rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
      exact closure_mono hle (hU u.2)
    rw [hK.closure_eq] at this
    exact this
  let π : Z0 →ₗ[R] LinearMap.ker (resU ρ h) :=
    LinearMap.codRestrict _ ((Submodule.mkQ _).comp Z0.subtype) fun z =>
      (resU_mk_eq_zero ρ h z.1).2 ⟨0, fun u => by rw [z.2 _ u.2]; simp⟩
  have hπ : Function.Surjective π := by
    rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 hx
    let b : Z1U ρ U := ⟨d0 _ m, coboundaries_le_cocycles _ hρU ⟨m, rfl⟩⟩
    refine ⟨⟨z - b, fun u hu => ?_⟩, Subtype.ext ?_⟩
    · show z.1 u - (ρ u m - m) = 0
      exact sub_eq_zero.2 (hm ⟨u.1, hu⟩)
    · refine (mk_eq_mk ρ U (z - b) z).2 ⟨-m, fun u => ?_⟩
      show z.1 u - (ρ u m - m) - z.1 u = _
      rw [map_neg]
      abel
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (Ideal.span (Set.range fun u : U => c u - 1))).principal
  have hkill : ∀ (u : U) (z : Z0), π ((c u - 1) • z) = 0 := by
    intro u z
    refine Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨z.1.1 u, fun g => ?_⟩))
    show (c u - 1) • z.1.1 g = ρ g (z.1.1 u) - z.1.1 u
    have e0 : u * g = (u * g * u⁻¹ * g⁻¹) * (g * u) := by group
    have e1 : ρ ((u * g * u⁻¹ * g⁻¹ : U) : G) = 1 := by
      have : ρ u * ρ g = ρ g * ρ u := by
        ext m
        simp only [Module.End.mul_apply, hc, smul_smul, mul_comm]
      have e : ((u * g * u⁻¹ * g⁻¹ : U) : G) = u * g * ((u : G)⁻¹ * (g : G)⁻¹) := by
        simp [mul_assoc]
      rw [e, map_mul, map_mul, this, ← map_mul, ← map_mul]
      simp
    have e2 : z.1.1 (u * g) = z.1.1 (g * u) := by
      rw [e0, hcoc, e1, z.2 _ (hab u u.2 g g.2)]
      simp
    rw [hcoc, hcoc, hc u] at e2
    rw [sub_smul, one_smul, eq_sub_of_add_eq' e2]
    abel
  have hamem : a ∈ Ideal.span (Set.range fun u : U => c u - 1) := by
    rw [ha]; exact Submodule.mem_span_singleton_self a
  have key := len_abs hM ev hev π hπ a (fun z => ?_) (H0U ρ U) (fun m hm => ?_)
  · simpa using key
  · refine Submodule.span_induction (p := fun r _ => π (r • z) = 0) ?_ ?_ ?_ ?_ hamem
    · rintro _ ⟨u, rfl⟩
      exact hkill u z
    · simp
    · intro x y _ _ hx hy
      rw [add_smul, map_add (f := _), hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_assoc, map_smul, hx, smul_zero]
  · intro u
    have : c u - 1 ∈ Ideal.span (Set.range fun u : U => c u - 1) := Ideal.subset_span ⟨u, rfl⟩
    rw [ha] at this
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
    show ρ u m = m
    have e : (c u - 1) • m = 0 := by rw [← hr, smul_assoc, hm, smul_zero]
    rw [hc, ← sub_eq_zero]
    rw [sub_smul, one_smul] at e
    exact e
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigSign
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigVia
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigEq
open ReciprocityTheory.Gal UpperTheory.V.Base

section

variable {O Q N : Type} [CommRing O] [CommGroup Q] [Fintype Q] [AddCommGroup N] [Module O N]

private noncomputable def prj (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) : N →ₗ[O] N :=
  c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g

private theorem prj_apply (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) (x : N) :
    prj π c ψ x = c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g x := by
  simp only [prj, LinearMap.smul_apply, LinearMap.sum_apply]

private theorem prj_mem (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) (x : N) :
    prj π c ψ x ∈ eig π ψ := by
  rw [mem_eig]
  intro h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [prj_apply, map_smul, smul_comm, map_sum, Finset.smul_sum (r := ((ψ h : Oˣ) : O))]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  rw [map_smul, smul_smul, Equiv.coe_mulLeft, ← Units.val_mul, ← map_mul, map_mul π, Module.End.mul_apply]
  congr 3
  rw [mul_inv, mul_inv_cancel_left]

private theorem prj_act (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) (h : Q) (x : N) :
    prj π c ψ (π h x) = ((ψ h : Oˣ) : O) • prj π c ψ x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← mem_eig.1 (prj_mem π c ψ x) h, prj_apply, prj_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

private theorem prj_self (π : Representation O Q N) {c : O} (hc : c * (Fintype.card Q : O) = 1) (ψ : Q →* Oˣ)
    {x : N} (hx : x ∈ eig π ψ) : prj π c ψ x = x := by
  rw [prj_apply]
  have : ∀ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g x = x := fun g => by
    rw [mem_eig.1 hx, smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_smul]
  simp only [this]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]

private theorem prj_ne [IsDomain O] (π : Representation O Q N) (c : O) {ψ χ : Q →* Oˣ} (hne : ψ ≠ χ)
    {x : N} (hx : x ∈ eig π χ) : prj π c ψ x = 0 := by
  rw [prj_apply]
  have : ∀ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g x = ((Units.coeHom O).comp (ψ⁻¹ * χ) g) • x := fun g => by
    rw [mem_eig.1 hx, smul_smul]
    simp
  simp only [this]
  rw [← Finset.sum_smul, sum_hom_units_eq_zero, zero_smul, smul_zero]
  intro h
  apply hne
  ext g
  have h1 := DFunLike.congr_fun h g
  have h2 : (ψ g)⁻¹ * χ g = 1 := Units.ext (by simpa using h1)
  rw [inv_mul_eq_one.1 h2]

private theorem sub_prj_mem (π : Representation O Q N) {c : O} (hc : c * (Fintype.card Q : O) = 1) (ψ : Q →* Oˣ)
    (x : N) : prj π c ψ x - x ∈ coeig π ψ := by
  have hx : x = c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • ((ψ g : Oˣ) : O) • x := by
    have : ∀ g : Q, ((ψ g⁻¹ : Oˣ) : O) • ((ψ g : Oˣ) : O) • x = x := fun g => by
      rw [smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_smul]
    simp only [this]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]
  have : prj π c ψ x - x = c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • (π g x - ((ψ g : Oˣ) : O) • x) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← hx, prj_apply]
  rw [this]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.mem_iSup_of_mem g ⟨x, rfl⟩

private theorem sum_prj [IsDomain O] [HasEnoughRootsOfUnity O (Monoid.exponent Q)] [Fintype (Q →* Oˣ)]
    (π : Representation O Q N) {c : O} (hc : c * (Fintype.card Q : O) = 1) (x : N) :
    ∑ ψ : Q →* Oˣ, prj π c ψ x = x := by
  simp only [prj_apply]
  rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_eq_single (1 : Q)]
  · simp only [inv_one, map_one, Units.val_one, one_smul, Module.End.one_apply]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]
  · intro g _ hg
    rw [← Finset.sum_smul]
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q O (inv_ne_one.2 hg)
    have := sum_hom_units_eq_zero ((Units.coeHom O).comp (MonoidHom.eval g⁻¹ : (Q →* Oˣ) →* Oˣ)) (by
      intro h
      exact hφ (Units.ext (DFunLike.congr_fun h φ)))
    have h2 : ∑ ψ : Q →* Oˣ, ((ψ g⁻¹ : Oˣ) : O) = 0 := this
    rw [h2, zero_smul]
  · simp

end

theorem UpperTheory.V.Base.lenEigEq :
    ∀ (O Q N : Type) [CommRing O] [IsDomain O] [CommGroup Q] [Finite Q] [HasEnoughRootsOfUnity O (Monoid.exponent Q)]
      [Fintype (Q →* Oˣ)] [AddCommGroup N] [Module O N] (π : Representation O Q N), IsUnit (Nat.card Q : O) →
      Module.length O N = ∑ ψ : Q →* Oˣ, Module.length O (eig π ψ) ∧ ∀ ψ : Q →* Oˣ, IsCompl (eig π ψ) (coeig π ψ) := by
  intro O Q N _ _ _ _ _ _ _ _ π hu
  classical
  letI := Fintype.ofFinite Q
  rw [Nat.card_eq_fintype_card] at hu
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  refine ⟨?_, fun ψ => ⟨?_, ?_⟩⟩
  · rw [← Module.length_pi_of_fintype]
    let f : N →ₗ[O] (∀ ψ : Q →* Oˣ, eig π ψ) :=
      LinearMap.pi fun ψ => (prj π c ψ).codRestrict (eig π ψ) (prj_mem π c ψ)
    have hf : ∀ x ψ, ((f x ψ : eig π ψ) : N) = prj π c ψ x := fun _ _ => rfl
    refine (LinearEquiv.ofBijective f ⟨?_, ?_⟩).length_eq
    · intro x y hxy
      rw [← sum_prj π hc x, ← sum_prj π hc y]
      exact Finset.sum_congr rfl fun ψ _ => by rw [← hf, ← hf, hxy]
    · intro y
      refine ⟨∑ χ, (y χ : N), funext fun ψ => Subtype.ext ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hf, map_sum, Finset.sum_eq_single ψ, prj_self π hc ψ (y ψ).2]
      · intro χ _ hχ
        exact prj_ne π c hχ.symm (y χ).2
      · simp
  · rw [Submodule.disjoint_def]
    intro x hx hy
    have hle : coeig π ψ ≤ LinearMap.ker (prj π c ψ) := by
      refine iSup_le fun g => ?_
      rintro _ ⟨z, rfl⟩
      simp [prj_act]
    rw [← prj_self π hc ψ hx]
    exact hle hy
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have : x = prj π c ψ x - (prj π c ψ x - x) := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (prj_mem π c ψ x))
      (Submodule.mem_sup_right (sub_prj_mem π hc ψ x))
end

section -- restored from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenRoots
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_product_polynomial_le (O N : Type) [CommRing O] [AddCommGroup N] [Module O N]
    (f : Module.End O N) (p : ℕ → Polynomial O) (s : Finset ℕ) :
    Module.length O (LinearMap.ker (Polynomial.aeval f (∏ i ∈ s, p i))) ≤
        ∑ i ∈ s, Module.length O (LinearMap.ker (Polynomial.aeval f (p i))) ∧
    Module.length O (N ⧸ LinearMap.range (Polynomial.aeval f (∏ i ∈ s, p i))) ≤
        ∑ i ∈ s, Module.length O (N ⧸ LinearMap.range (Polynomial.aeval f (p i))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have key : ∀ g : Module.End O N, g = 1 →
        Module.length O (LinearMap.ker g) = 0 ∧ Module.length O (N ⧸ LinearMap.range g) = 0 := by
      rintro g rfl
      rw [Module.End.one_eq_id, LinearMap.ker_id, LinearMap.range_id]
      constructor <;> rw [Module.length_eq_zero_iff] <;> infer_instance
    obtain ⟨k1, k2⟩ := key (Polynomial.aeval f (∏ i ∈ (∅ : Finset ℕ), p i))
      (by rw [Finset.prod_empty, map_one])
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ⟨k1.le, k2.le⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, map_mul]
    obtain ⟨h1, h2⟩ := lenComp O N (Polynomial.aeval f (p a)) (Polynomial.aeval f (∏ i ∈ s, p i))
    exact ⟨h1.trans (add_le_add le_rfl ih.1), h2.trans (add_le_add le_rfl ih.2)⟩

theorem UpperTheory.V.Base.lenRoots :
    ∀ (O N : Type) [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N] (n : ℕ) (ζ : O), 0 < n → IsPrimitiveRoot ζ n →
      ∀ f : Module.End O N, f ^ n = 1 →
      Module.length O N ≤ ∑ i ∈ Finset.range n, Module.length O (LinearMap.ker (f - ζ ^ i • (1 : Module.End O N))) ∧
      Module.length O N ≤ ∑ i ∈ Finset.range n, Module.length O (N ⧸ LinearMap.range (f - ζ ^ i • (1 : Module.End O N))) := by
  intro O N _ _ _ _ n ζ hn hζ f hf
  have hprod := X_pow_sub_C_eq_prod hζ hn (one_pow n)
  have hterm : ∀ i, Polynomial.aeval f (Polynomial.X - Polynomial.C (ζ ^ i * 1))
      = f - ζ ^ i • (1 : Module.End O N) := by
    intro i
    simp [Algebra.algebraMap_eq_smul_one, smul_pow]
  have e : Polynomial.aeval f (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (ζ ^ i * 1))) = 0 := by
    rw [← hprod]
    simp [hf]
  have key : ∀ g : Module.End O N, g = 0 →
      Module.length O (LinearMap.ker g) = Module.length O N ∧
      Module.length O (N ⧸ LinearMap.range g) = Module.length O N := by
    rintro g rfl
    rw [LinearMap.ker_zero, LinearMap.range_zero, Module.length_top,
      (Submodule.quotEquivOfEqBot (⊥ : Submodule O N) rfl).length_eq]
    exact ⟨rfl, rfl⟩
  have cong : ∀ g h : Module.End O N, g = h →
      Module.length O (LinearMap.ker g) = Module.length O (LinearMap.ker h) ∧
      Module.length O (N ⧸ LinearMap.range g) = Module.length O (N ⧸ LinearMap.range h) := by
    rintro g h rfl
    exact ⟨rfl, rfl⟩
  obtain ⟨h1, h2⟩ := length_product_polynomial_le O N f (fun i => Polynomial.X - Polynomial.C (ζ ^ i * 1))
    (Finset.range n)
  obtain ⟨k1, k2⟩ := key _ e
  refine ⟨?_, ?_⟩
  · rw [← k1]
    refine h1.trans (le_of_eq (Finset.sum_congr rfl fun i _ => (cong _ _ (hterm i)).1))
  · rw [← k2]
    refine h2.trans (le_of_eq (Finset.sum_congr rfl fun i _ => (cong _ _ (hterm i)).2))
end

section -- restored from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigLe
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem lenEigLe_one {O N : Type} [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N]
    (n : ℕ) (ζ : O) (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) (f : Module.End O N) (hf : f ^ n = 1)
    (P : Submodule O N) (hP : ∀ x ∈ P, f x ∈ P) :
    Module.length O P ≤ ∑ j : Fin n,
      Module.length O (P ⊓ LinearMap.ker (f - ζ ^ (j : ℕ) • (1 : Module.End O N)) : Submodule O N) := by
  have h1 : (f.restrict hP) ^ n = 1 := by
    ext x
    rw [Module.End.pow_restrict]
    simp [hf]
  refine (lenRoots O P n ζ hn hζ (f.restrict hP) h1).1.trans ?_
  rw [Finset.sum_range]
  refine Finset.sum_le_sum fun j _ => ?_
  refine Module.length_le_of_injective
    (LinearMap.codRestrict _ (P.subtype ∘ₗ Submodule.subtype _) fun x => ⟨x.1.2, ?_⟩) ?_
  · have := congrArg Subtype.val (LinearMap.mem_ker.1 x.2)
    exact this
  · intro x y h
    have := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext this)

private theorem lenEigLe_many {O N : Type} [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N] (k : ℕ) :
    ∀ (n : Fin k → ℕ) (ζ : Fin k → O), (∀ i, 0 < n i) → (∀ i, IsPrimitiveRoot (ζ i) (n i)) →
      ∀ f : Fin k → Module.End O N, (∀ i, f i ^ n i = 1) → (∀ i j, f i * f j = f j * f i) →
      ∀ P : Submodule O N, (∀ i, ∀ x ∈ P, f i x ∈ P) →
      Module.length O P ≤ ∑ a : (∀ i, Fin (n i)),
        Module.length O (P ⊓ ⨅ i, LinearMap.ker (f i - ζ i ^ (a i : ℕ) • (1 : Module.End O N)) : Submodule O N) := by
  induction k with
  | zero =>
    intro n ζ _ _ f _ _ P _
    rw [Fintype.sum_unique, iInf_of_empty, inf_top_eq]
  | succ k ih =>
    intro n ζ hn hζ f hf hc P hP
    refine (lenEigLe_one (n 0) (ζ 0) (hn 0) (hζ 0) (f 0) (hf 0) P (hP 0)).trans ?_
    rw [← (Fin.consEquiv fun i => Fin (n i)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun j _ => ?_
    refine (ih (fun i => n i.succ) (fun i => ζ i.succ) (fun i => hn _) (fun i => hζ _) (fun i => f i.succ)
      (fun i => hf _) (fun i j => hc _ _) _ ?_).trans (le_of_eq ?_)
    · intro i x hx
      refine ⟨hP _ x hx.1, ?_⟩
      have h2 : f 0 x = ζ 0 ^ (j : ℕ) • x := by simpa [sub_eq_zero] using hx.2
      have h3 : f 0 (f i.succ x) = ζ 0 ^ (j : ℕ) • f i.succ x := by
        rw [← Module.End.mul_apply, hc, Module.End.mul_apply, h2, map_smul]
      simpa [sub_eq_zero] using h3
    · refine Finset.sum_congr rfl fun a _ => ?_
      have : (P ⊓ LinearMap.ker (f 0 - ζ 0 ^ (j : ℕ) • (1 : Module.End O N))) ⊓
          ⨅ i : Fin k, LinearMap.ker (f i.succ - ζ i.succ ^ (a i : ℕ) • (1 : Module.End O N)) =
          P ⊓ ⨅ i, LinearMap.ker (f i - ζ i ^
            (((Fin.consEquiv fun i => Fin (n i)) (j, a) i : Fin (n i)) : ℕ) • (1 : Module.End O N)) := by
        ext x
        simp only [Submodule.mem_inf, Submodule.mem_iInf, Fin.forall_fin_succ, and_assoc]
        rfl
      rw [this]

private theorem lenEigLe_gen (Q : Type) [CommGroup Q] [Finite Q] :
    ∃ (k : ℕ) (n : Fin k → ℕ) (g : Fin k → Q), (∀ i, 0 < n i) ∧ (∀ i, orderOf (g i) = n i) ∧
      Submonoid.closure (Set.range g) = ⊤ ∧
      ∀ (C : Type) [CommGroup C] (u : Fin k → C), (∀ i, u i ^ n i = 1) → ∃ ψ : Q →* C, ∀ i, ψ (g i) = u i := by
  classical
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite Q
  let σ := (Fintype.equivFin ι).symm
  haveI : ∀ i, NeZero (n i) := fun i => ⟨by have := hn i; omega⟩
  refine ⟨_, fun i => n (σ i), fun i => e.symm (Pi.mulSingle (σ i) (Multiplicative.ofAdd 1)),
    fun i => zero_lt_one.trans (hn (σ i)), fun i => ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    have := orderOf_injective (MonoidHom.mulSingle (fun i => Multiplicative (ZMod (n i))) (σ i))
      (Pi.mulSingle_injective (M := fun i => Multiplicative (ZMod (n i))) (σ i)) (Multiplicative.ofAdd 1)
    rw [MonoidHom.mulSingle_apply] at this
    rw [this, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  · rw [eq_top_iff]
    intro q _
    obtain ⟨y, rfl⟩ := e.symm.surjective q
    rw [← Finset.univ_prod_mulSingle y, map_prod]
    refine Submonoid.prod_mem _ fun i _ => ?_
    obtain ⟨i, rfl⟩ := σ.surjective i
    have : y (σ i) = Multiplicative.ofAdd (1 : ZMod (n (σ i))) ^ (y (σ i)).toAdd.val := by
      rw [← ofAdd_nsmul]; simp
    rw [this, Pi.mulSingle_pow, map_pow]
    exact Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_range_self i)) _
  · intro C _ u hu
    have hu' : ∀ i, u (σ.symm i) ^ n i = 1 := fun i => by simpa using hu (σ.symm i)
    refine ⟨(∏ i, (AddChar.zmodChar (n i) (hu' i)).toMonoidHom.comp
      (Pi.evalMonoidHom (fun i => Multiplicative (ZMod (n i))) i)).comp e.toMonoidHom, fun i => ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      ]
    change MonoidHom.eval (Pi.mulSingle (σ i) (Multiplicative.ofAdd 1))
      (∏ j : ι, (AddChar.zmodChar (n j) (hu' j)).toMonoidHom.comp
        (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (n j))) j)) = u i
    rw [map_prod]
    change (∏ j : ι, (AddChar.zmodChar (n j) (hu' j)).toMonoidHom
      (Pi.mulSingle (M := fun j => Multiplicative (ZMod (n j))) (σ i) (Multiplicative.ofAdd 1) j)) = u i
    rw [Finset.prod_eq_single (σ i)]
    · haveI : Fact (1 < n (σ i)) := ⟨hn _⟩
      simp [AddChar.zmodChar_apply, ZMod.val_one]
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne hj, map_one]
    · simp

theorem UpperTheory.V.Base.lenEigLe :
    ∀ (O Q N : Type) [CommRing O] [IsDomain O] [CommGroup Q] [Finite Q] [HasEnoughRootsOfUnity O (Monoid.exponent Q)]
      [Fintype (Q →* Oˣ)] [AddCommGroup N] [Module O N] (π : Representation O Q N),
      Module.length O N ≤ ∑ ψ : Q →* Oˣ, Module.length O (eig π ψ) := by
  intro O Q N _ _ _ _ _ _ _ _ π
  classical
  obtain ⟨k, n, g, hn, hg, hcl, hψ⟩ := lenEigLe_gen Q
  have hζ : ∀ i, ∃ ζ : Oˣ, IsPrimitiveRoot ζ (n i) := fun i => by
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot O (Monoid.exponent Q)
    have he : 0 < Monoid.exponent Q := Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite
    obtain ⟨m, hm⟩ : n i ∣ Monoid.exponent Q := hg i ▸ Monoid.order_dvd_exponent (g i)
    have h := hz.pow he (hm.trans (mul_comm _ _))
    exact ⟨_, h.isUnit_unit (hn i).ne'⟩
  choose ζ hζ using hζ
  have h1 := lenEigLe_many k n (fun i => (ζ i : O)) hn (fun i => IsPrimitiveRoot.coe_units_iff.2 (hζ i))
    (fun i => π (g i)) (fun i => by rw [← map_pow, ← hg i, pow_orderOf_eq_one, map_one])
    (fun i j => by rw [← map_mul, mul_comm, map_mul]) ⊤ (fun _ _ _ => trivial)
  have h2 : ∀ a : (∀ i, Fin (n i)), ∃ ψ : Q →* Oˣ, ∀ i, ψ (g i) = ζ i ^ (a i : ℕ) := fun a =>
    hψ Oˣ _ fun i => by rw [← pow_mul, mul_comm, pow_mul, (hζ i).pow_eq_one, one_pow]
  choose ψ hψ' using h2
  have hinj : Function.Injective ψ := fun a b h => funext fun i => Fin.ext <|
    (hζ i).pow_inj (a i).2 (b i).2 (by rw [← hψ', ← hψ', h])
  rw [Module.length_top] at h1
  refine h1.trans ?_
  calc _ ≤ ∑ a, Module.length O (eig π (ψ a)) := Finset.sum_le_sum fun a _ => ?_
    _ = ∑ χ ∈ Finset.univ.image ψ, Module.length O (eig π χ) :=
      (Finset.sum_image (f := fun χ => Module.length O (eig π χ)) fun a _ b _ h => hinj h).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  refine Module.length_le_of_injective (Submodule.inclusion ?_) (Submodule.inclusion_injective _)
  intro x hx
  rw [mem_eig]
  intro q
  have hq : q ∈ Submonoid.closure (Set.range g) := hcl ▸ Submonoid.mem_top q
  induction hq using Submonoid.closure_induction with
  | mem q hq =>
    obtain ⟨i, rfl⟩ := hq
    have := (Submodule.mem_iInf _).1 hx.2 i
    rw [hψ']
    simpa [sub_eq_zero] using this
  | one => simp
  | mul p q _ _ hp hq =>
    rw [map_mul, Module.End.mul_apply, hq, map_smul, hp, map_mul, Units.val_mul, smul_smul, mul_comm]
end

open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.lenEigVia :
    ∀ (O W Q N : Type) [CommRing O] [IsDomain O] [Group W] [CommGroup Q] [Finite Q] [HasEnoughRootsOfUnity O (Monoid.exponent Q)]
      [Fintype (Q →* Oˣ)] [AddCommGroup N] [Module O N] (π : Representation O W N) (p : W →* Q), Function.Surjective p →
      (∀ g, p g = 1 → ∀ x, π g x = x) →
      Module.length O N ≤ ∑ ψ : Q →* Oˣ, Module.length O (eig π (ψ.comp p)) ∧
      (IsUnit (Nat.card Q : O) → Module.length O N = ∑ ψ : Q →* Oˣ, Module.length O (eig π (ψ.comp p))) := by
  intro O W Q N _ _ _ _ _ _ _ _ _ π p hp hfix
  have hker : p.ker ≤ MonoidHom.ker π := fun g hg =>
    (MonoidHom.mem_ker).mpr (LinearMap.ext (hfix g ((MonoidHom.mem_ker).mp hg)))
  let e := QuotientGroup.quotientKerEquivOfSurjective p hp
  let π' : Representation O Q N := (QuotientGroup.lift p.ker π hker).comp e.symm.toMonoidHom
  have hπ' : ∀ g, π' (p g) = π g := by
    intro g
    have he : e.symm (p g) = (g : W ⧸ p.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift p.ker π hker (e.symm (p g)) = π g
    rw [he, QuotientGroup.lift_mk]
  have heig : ∀ ψ : Q →* Oˣ, eig π (ψ.comp p) = eig π' ψ := by
    intro ψ
    ext x
    simp only [mem_eig]
    constructor
    · intro h q
      obtain ⟨g, rfl⟩ := hp q
      rw [hπ']
      exact h g
    · intro h g
      rw [← hπ']
      exact h (p g)
  have hsum : ∑ ψ : Q →* Oˣ, Module.length O (eig π (ψ.comp p))
      = ∑ ψ : Q →* Oˣ, Module.length O (eig π' ψ) :=
    Finset.sum_congr rfl fun ψ _ =>
      congrArg (fun S : Submodule O N => Module.length O S) (heig ψ)
  rw [hsum]
  exact ⟨lenEigLe O Q N π', fun hu => (lenEigEq O Q N π' hu).1⟩
end

open ReciprocityTheory.Gal UpperTheory.V.Base

set_option maxHeartbeats 200000 in
theorem UpperTheory.V.Base.lenEigSign :
    ∀ (O W Q N : Type) [CommRing O] [IsDomain O] [Group W] [CommGroup Q] [Finite Q] [HasEnoughRootsOfUnity O (Monoid.exponent Q)]
      [Fintype (Q →* Oˣ)] [AddCommGroup N] [Module O N] (π : Representation O W N) (p : W →* Q), Function.Surjective p →
      (∀ g, p g = 1 → ∀ x, π g x = x) →
      IsUnit (2 : O) → ∀ (c : W) (s : Oˣ), p c * p c = 1 → s * s = 1 → ∀ T : Finset (Q →* Oˣ), (∀ ψ, ψ (p c) = s → ψ ∈ T) →
      Module.length O (Module.End.eigenspace (π c) (s : O)) ≤ ∑ ψ ∈ T, Module.length O (eig π (ψ.comp p)) := by
  intro O W Q N _ _ _ _ _ _ _ _ _ π p hp hker h2 c s hc hs T hT
  have hcomm : ∀ (g : W) (x : N), π g (π c x) = π c (π g x) := by
    intro g x
    have hk : p ((c * g)⁻¹ * (g * c)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, mul_comm (p g) (p c), inv_mul_cancel]
    have e1 : g * c = (c * g) * ((c * g)⁻¹ * (g * c)) := by group
    have a1 : π g (π c x) = π (g * c) x := by rw [map_mul]; rfl
    have a2 : π c (π g x) = π (c * g) x := by rw [map_mul]; rfl
    rw [a1, a2, e1, map_mul, Module.End.mul_apply, hker _ hk]
  have hE : ∀ g, Module.End.eigenspace (π c) (s : O) ≤
      (Module.End.eigenspace (π c) (s : O)).comap (π g) := by
    intro g x hx
    rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff] at *
    rw [← hcomm, hx, map_smul]
  let πE := π.subrepresentation _ hE
  have hkerE : ∀ g, p g = 1 → ∀ x, πE g x = x := by
    intro g hg x
    apply Subtype.ext
    exact hker g hg x
  obtain ⟨hlen, -⟩ := lenEigVia O W Q _ πE p hp hkerE
  refine hlen.trans ?_
  have hzero : ∀ ψ : Q →* Oˣ, ψ ∉ T → Module.length O (eig πE (ψ.comp p)) = 0 := by
    intro ψ hψ
    have hne : ψ (p c) ≠ s := fun h => hψ (hT ψ h)
    have hu : IsUnit ((s : O) - (ψ (p c) : O)) := by
      have a : (s : O) * s = 1 := by rw [← Units.val_mul, hs, Units.val_one]
      have b : (ψ (p c) : O) * ψ (p c) = 1 := by
        rw [← Units.val_mul, ← map_mul, hc, map_one, Units.val_one]
      have hsq : ((s : O) - ψ (p c)) * ((s : O) + ψ (p c)) = 0 := by
        linear_combination a - b
      rcases mul_eq_zero.mp hsq with h | h
      · exact absurd (Units.ext (sub_eq_zero.mp h)).symm hne
      · have e : (s : O) - ψ (p c) = 2 * s := by linear_combination (-1 : O) * h
        rw [e]
        exact h2.mul s.isUnit
    have key : ∀ y : eig πE (ψ.comp p), y = 0 := by
      intro y
      have h1 : π c y.1.1 = (ψ (p c) : O) • y.1.1 :=
        congrArg Subtype.val ((mem_eig.mp y.2) c)
      have h2' : π c y.1.1 = (s : O) • y.1.1 :=
        Module.End.mem_eigenspace_iff.mp y.1.2
      have h3 : ((s : O) - ψ (p c)) • y.1.1 = 0 := by
        rw [sub_smul, ← h1, ← h2', sub_self]
      have h4 : y.1.1 = 0 := hu.smul_eq_zero.mp h3
      apply Subtype.ext
      apply Subtype.ext
      exact h4
    rw [Module.length_eq_zero_iff]
    exact ⟨fun a b => (key a).trans (key b).symm⟩
  have hmono : ∀ ψ : Q →* Oˣ,
      Module.length O (eig πE (ψ.comp p)) ≤ Module.length O (eig π (ψ.comp p)) := by
    intro ψ
    refine Module.length_le_of_injective
      (LinearMap.codRestrict (eig π (ψ.comp p))
        ((Module.End.eigenspace (π c) (s : O)).subtype ∘ₗ (eig πE (ψ.comp p)).subtype) ?_) ?_
    · intro y
      rw [mem_eig]
      intro g
      exact congrArg Subtype.val ((mem_eig.mp y.2) g)
    · intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
  rw [← Finset.sum_subset (Finset.subset_univ T) (fun ψ _ hψ => hzero ψ hψ)]
  exact Finset.sum_le_sum fun ψ _ => hmono ψ
end
