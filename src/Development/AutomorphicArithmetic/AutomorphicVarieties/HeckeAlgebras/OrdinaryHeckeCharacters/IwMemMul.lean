module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem iwMem_mul {G : Type} [Group G] (I : Iwa G) (c : ℕ) (S : Subgroup G) (hS : S ≤ I.T)
    (hc : I.Tc c ≤ S) {a b : G} (ha : ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, a = x * t * y)
    (hb : ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, b = x * t * y) :
    ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, a * b = x * t * y := by
  obtain ⟨x, hx, t, ht, y, hy, rfl⟩ := ha
  obtain ⟨x', hx', t', ht', y', hy', rfl⟩ := hb
  obtain ⟨x2, hx2, s, hs, y2, hy2, h⟩ := I.swap c y hy x' hx'
  refine ⟨x * (t * x2 * t⁻¹), mul_mem hx (I.T_N t (hS ht) x2 hx2), t * s * t',
    mul_mem (mul_mem ht (hc hs)) ht', (t'⁻¹ * y2 * t'⁻¹⁻¹) * y',
    mul_mem (I.T_Nm c t'⁻¹ (inv_mem (hS ht')) y2 hy2) hy', ?_⟩
  calc x * t * y * (x' * t' * y') = x * t * (y * x') * t' * y' := by group
    _ = x * t * (x2 * s * y2) * t' * y' := by rw [h]
    _ = _ := by group

private theorem iwMem_gen {G : Type} [Group G] (I : Iwa G) (c : ℕ) (S : Subgroup G) (hS : S ≤ I.T)
    (hc : I.Tc c ≤ S) (g : G) :
    g ∈ I.N ⊔ S ⊔ I.Nm c ↔ ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, g = x * t * y := by
  constructor
  · intro hg
    have hN : ∀ x ∈ I.N, ∃ x' ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, x = x' * t * y :=
      fun x hx => ⟨x, hx, 1, S.one_mem, 1, (I.Nm c).one_mem, by simp⟩
    have hT : ∀ t ∈ S, ∃ x ∈ I.N, ∃ t' ∈ S, ∃ y ∈ I.Nm c, t = x * t' * y :=
      fun t ht => ⟨1, I.N.one_mem, t, ht, 1, (I.Nm c).one_mem, by simp⟩
    have hY : ∀ y ∈ I.Nm c, ∃ x ∈ I.N, ∃ t ∈ S, ∃ y' ∈ I.Nm c, y = x * t * y' :=
      fun y hy => ⟨1, I.N.one_mem, 1, S.one_mem, y, hy, by simp⟩
    let M : Subgroup G :=
      { carrier := {g | ∃ x ∈ I.N, ∃ t ∈ S, ∃ y ∈ I.Nm c, g = x * t * y}
        mul_mem' := fun ha hb => iwMem_mul I c S hS hc ha hb
        one_mem' := hN 1 I.N.one_mem
        inv_mem' := by
          rintro g ⟨x, hx, t, ht, y, hy, rfl⟩
          have e : (x * t * y)⁻¹ = y⁻¹ * t⁻¹ * x⁻¹ := by group
          rw [e]
          exact iwMem_mul I c S hS hc
            (iwMem_mul I c S hS hc (hY _ ((I.Nm c).inv_mem hy)) (hT _ (S.inv_mem ht)))
            (hN _ (I.N.inv_mem hx)) }
    have hle : I.N ⊔ S ⊔ I.Nm c ≤ M :=
      sup_le (sup_le (fun x hx => hN x hx) (fun t ht => hT t ht)) (fun y hy => hY y hy)
    exact hle hg
  · rintro ⟨x, hx, t, ht, y, hy, rfl⟩
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right ht))) (Subgroup.mem_sup_right hy)

theorem UpperTheory.V.Hi.iwMem :
    ∀ (G : Type) [Group G] (I : Iwa G) (c : ℕ) (g : G), (g ∈ I.Iw c ↔ ∃ x ∈ I.N, ∃ t ∈ I.T, ∃ y ∈ I.Nm c, g = x * t * y) ∧ (g ∈ I.I1 c ↔ ∃ x ∈ I.N, ∃ t ∈ I.Tc c, ∃ y ∈ I.Nm c, g = x * t * y) ∧ (g ∈ I.Nf → g ∈ I.Iw c → g ∈ I.N) := by
  intro G _ I c g
  refine ⟨iwMem_gen I c I.T le_rfl (I.Tc_le c) g,
    iwMem_gen I c (I.Tc c) (I.Tc_le c) le_rfl g, ?_⟩
  intro hg hw
  obtain ⟨x, hx, t, ht, y, hy, rfl⟩ := (iwMem_gen I c I.T le_rfl (I.Tc_le c) _).1 hw
  have hy0 : y ∈ I.Nm 0 := I.Nm_anti (Nat.zero_le c) hy
  have h := I.uniq ((x * t * y)⁻¹ * x) (I.Nf.mul_mem (I.Nf.inv_mem hg) (I.N_le hx)) t
    (I.T_le ht) y hy0 (by group)
  have e : x * t * y = x := by
    calc x * t * y = x * ((x * t * y)⁻¹ * x)⁻¹ := by group
      _ = x := by rw [h.1]; group
  rw [e]
  exact hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcSumEqOfMk
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem dcSum_eq_of_mk {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K' : Subgroup H) {v : M} (hv : v ∈ fixd ρ K') {y z : H}
    (h : (y : H ⧸ K') = (z : H ⧸ K')) : ρ y v = ρ z v := by
  have h1 : y⁻¹ * z ∈ K' := QuotientGroup.eq.mp h
  have h2 : ρ (y⁻¹ * z) v = v := hv _ h1
  calc ρ y v = ρ y (ρ (y⁻¹ * z) v) := by rw [h2]
    _ = ρ (y * (y⁻¹ * z)) v := by rw [map_mul ρ y]; rfl
    _ = ρ z v := by rw [mul_inv_cancel_left]

private theorem dcSum_apply {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K K' : Subgroup H) (x : H)
    [Fintype (MulAction.orbit K (x : H ⧸ K'))] (v : M) :
    dc ρ K K' x v = ∑ q : MulAction.orbit K (x : H ⧸ K'), ρ (q : H ⧸ K').out v := by
  rw [dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]

theorem UpperTheory.V.Hi.dcSum :
    ∀ (A H M : Type) [CommRing A] [Group H] [AddCommGroup M] [Module A M] (ρ : Representation A H M) (K K' : Subgroup H) (x : H), (MulAction.orbit K (x : H ⧸ K')).Finite → (∀ s : Finset H, (∀ y ∈ s, (y : H ⧸ K') ∈ MulAction.orbit K (x : H ⧸ K')) → (∀ q ∈ MulAction.orbit K (x : H ⧸ K'), ∃! y, y ∈ s ∧ (y : H ⧸ K') = q) → ∀ v ∈ fixd ρ K', dc ρ K K' x v = ∑ y ∈ s, ρ y v) ∧ (∀ v ∈ fixd ρ K', dc ρ K K' x v ∈ fixd ρ K) ∧ (∀ V : Subgroup H, (∀ u ∈ V, u * x = x * u ∧ ∀ k ∈ K, u * k = k * u) → ∀ v ∈ fixd ρ K', v ∈ fixd ρ V → dc ρ K K' x v ∈ fixd ρ V) ∧ ∀ (A' M' : Type) [CommRing A'] [AddCommGroup M'] [Module A' M'] (ρ' : Representation A' H M') (f : M →+ M'), (∀ h v, f (ρ h v) = ρ' h (f v)) → ∀ v, f (dc ρ K K' x v) = dc ρ' K K' x (f v) := by
  intro A H M _ _ _ _ ρ K K' x hfin
  letI : Fintype (MulAction.orbit K (x : H ⧸ K')) := hfin.fintype
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs hu v hv
    rw [dcSum_apply]
    symm
    refine Finset.sum_bij (fun y hy => (⟨(y : H ⧸ K'), hs y hy⟩ : MulAction.orbit K (x : H ⧸ K')))
      (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro y hy z hz h
      have h' : (y : H ⧸ K') = (z : H ⧸ K') := congrArg Subtype.val h
      exact (hu _ (hs z hz)).unique ⟨hy, h'⟩ ⟨hz, rfl⟩
    · intro q _
      obtain ⟨y, ⟨hy, hq⟩, -⟩ := hu q.1 q.2
      exact ⟨y, hy, Subtype.ext hq⟩
    · intro y hy
      exact dcSum_eq_of_mk ρ K' hv (QuotientGroup.out_eq' _).symm
  · intro v hv u hu
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dcSum_apply, map_sum]
    refine Fintype.sum_equiv (MulAction.toPerm (⟨u, hu⟩ : K)) _ _ ?_
    intro q
    have : ρ u (ρ (q : H ⧸ K').out v) = ρ (u * (q : H ⧸ K').out) v := by rw [map_mul]; rfl
    rw [this]
    apply dcSum_eq_of_mk ρ K' hv
    rw [QuotientGroup.out_eq']
    change _ = u • (q : H ⧸ K')
    conv_rhs => rw [← QuotientGroup.out_eq' (q : H ⧸ K')]
    rfl
  · intro V hV v hv hvV u hu
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dcSum_apply, map_sum]
    refine Finset.sum_congr rfl ?_
    rintro ⟨q, k, hk⟩ _
    have h1 : ρ q.out v = ρ ((k : H) * x) v := by
      apply dcSum_eq_of_mk ρ K' hv
      rw [QuotientGroup.out_eq', ← hk]
      rfl
    have h2 : u * ((k : H) * x) = ((k : H) * x) * u := by
      rw [← mul_assoc, (hV u hu).2 k k.2, mul_assoc, (hV u hu).1, mul_assoc]
    change ρ u (ρ q.out v) = ρ q.out v
    rw [h1]
    calc ρ u (ρ ((k : H) * x) v) = ρ (u * ((k : H) * x)) v := by rw [map_mul ρ u]; rfl
      _ = ρ ((k : H) * x) (ρ u v) := by rw [h2, map_mul ρ _ u]; rfl
      _ = _ := by rw [hvV u hu]
  · intro A' M' _ _ _ ρ' f hf v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [dcSum_apply, dcSum_apply, map_sum]
    exact Finset.sum_congr rfl fun q _ => hf _ _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpNat
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.uOpNat :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (A' M' : Type) [CommRing A'] [AddCommGroup M'] [Module A' M'] (π' : Representation A' G M') (f : M →+ M') (a : G), a ∈ I.P → ∀ v, (∀ u ∈ I.N, f (π (u * a) v) = π' (u * a) (f v)) → f (I.uOp π a v) = I.uOp π' a (f v) := by
  intro G _ I A M _ _ _ π A' M' _ _ _ π' f a ha v hv
  have hfin : Finite (↥I.N ⧸ (I.Nconj a).subgroupOf I.N) :=
    Subgroup.index_ne_zero_iff_finite.mp (I.fin_N a ha)
  have _ := Fintype.ofFinite (↥I.N ⧸ (I.Nconj a).subgroupOf I.N)
  unfold Iwa.uOp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply,
    LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun q _ => hv _ (Quotient.out q).2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpSum
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.uOpSum :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (a : G), a ∈ I.P → (∃ s : Finset G, (∀ u ∈ s, u ∈ I.N) ∧ ∀ x ∈ I.N, ∃! u, u ∈ s ∧ u⁻¹ * x ∈ I.Nconj a) ∧ ∀ s : Finset G, (∀ u ∈ s, u ∈ I.N) → (∀ x ∈ I.N, ∃! u, u ∈ s ∧ u⁻¹ * x ∈ I.Nconj a) → s.card = (I.Nconj a).relIndex I.N ∧ ∀ v ∈ fixd π I.N, I.uOp π a v = ∑ u ∈ s, π (u * a) v := by
  intro G _ I A M _ _ _ π a ha
  classical
  have hfin : Finite (I.N ⧸ (I.Nconj a).subgroupOf I.N) :=
    Nat.finite_of_card_ne_zero (I.fin_N a ha)
  letI : Fintype (I.N ⧸ (I.Nconj a).subgroupOf I.N) := Fintype.ofFinite _
  have key : ∀ x y : I.N, (QuotientGroup.mk x : I.N ⧸ (I.Nconj a).subgroupOf I.N) = QuotientGroup.mk y ↔
      (x : G)⁻¹ * y ∈ I.Nconj a := by
    intro x y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp
  refine ⟨⟨Finset.univ.image (fun q : I.N ⧸ (I.Nconj a).subgroupOf I.N => ((q.out : I.N) : G)), ?_, ?_⟩, ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact q.out.2
  · intro x hx
    refine ⟨((QuotientGroup.mk (⟨x, hx⟩ : I.N) : I.N ⧸ (I.Nconj a).subgroupOf I.N).out : I.N),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · exact (key _ ⟨x, hx⟩).1 (QuotientGroup.out_eq' _)
    · rintro u ⟨hu, hux⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      have h := (key q.out ⟨x, hx⟩).2 hux
      rw [QuotientGroup.out_eq'] at h
      rw [h]
  · intro s hs hu
    let i : ∀ u ∈ s, I.N ⧸ (I.Nconj a).subgroupOf I.N := fun u h => QuotientGroup.mk ⟨u, hs u h⟩
    have inj : ∀ u₁ (h₁ : u₁ ∈ s) u₂ (h₂ : u₂ ∈ s), i u₁ h₁ = i u₂ h₂ → u₁ = u₂ := by
      intro u₁ h₁ u₂ h₂ h
      have h' := (key ⟨u₁, hs _ h₁⟩ ⟨u₂, hs _ h₂⟩).1 h
      exact (hu u₂ (hs _ h₂)).unique ⟨h₁, h'⟩ ⟨h₂, by simp⟩
    have surj : ∀ q ∈ (Finset.univ : Finset (I.N ⧸ (I.Nconj a).subgroupOf I.N)), ∃ u h, i u h = q := by
      intro q _
      obtain ⟨u, ⟨h, h'⟩, -⟩ := hu q.out q.out.2
      exact ⟨u, h, ((key ⟨u, hs u h⟩ q.out).2 h').trans (QuotientGroup.out_eq' q)⟩
    refine ⟨?_, ?_⟩
    · rw [Finset.card_bij i (fun _ _ => Finset.mem_univ _) inj surj, Subgroup.relIndex, Subgroup.index,
        Nat.card_eq_fintype_card, Finset.card_univ]
    · intro v hv
      rw [Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
      refine (Finset.sum_bij i (fun _ _ => Finset.mem_univ _) inj surj ?_).symm
      intro u h
      have h' := (key ⟨u, hs u h⟩ (i u h).out).1 (QuotientGroup.out_eq' _).symm
      obtain ⟨n, hn, e⟩ := Subgroup.mem_map.1 h'
      have e' : (((i u h).out : I.N) : G) * a = u * a * n := by
        have e2 : a * n * a⁻¹ = u⁻¹ * (((i u h).out : I.N) : G) := e
        calc (((i u h).out : I.N) : G) * a = u * (u⁻¹ * (((i u h).out : I.N) : G)) * a := by group
          _ = u * a * n := by rw [← e2]; group
      rw [e', map_mul π (u * a) n, Module.End.mul_apply, hv n hn]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PropCp
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.propCp :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (a : G), a ∈ I.P → ∀ v ∈ fixd π I.N, I.uOp π a v - ((I.Nconj a).relIndex I.N : A) • π a v ∈ I.jacKer π := by
  intro G _ I A M _ _ _ π a ha v _
  have hfin : ((I.Nconj a).subgroupOf I.N).FiniteIndex := ⟨I.fin_N a ha⟩
  haveI : Fintype (I.N ⧸ (I.Nconj a).subgroupOf I.N) := Fintype.ofFinite _
  have hc : (I.Nconj a).relIndex I.N = Fintype.card (I.N ⧸ (I.Nconj a).subgroupOf I.N) := by
    rw [← Nat.card_eq_fintype_card]; rfl
  have hs : (((I.Nconj a).relIndex I.N : ℕ) : A) • π a v
      = ∑ _q : I.N ⧸ (I.Nconj a).subgroupOf I.N, π a v := by
    rw [Finset.sum_const, Finset.card_univ, hc, Nat.cast_smul_eq_nsmul]
  rw [hs, Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun q _ => Submodule.subset_span ?_
  refine ⟨(q.out : I.N), I.N_le (q.out).2, π a v, ?_⟩
  rw [map_mul]; rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CtrlEq
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem UpperTheory.V.Hi.ctrlEq_row {G : Type} [Group G] {I : Iwa G} {O Ω : Type} [CommRing O] [IsLocalRing O] [Field Ω]
    [Algebra O Ω] (W : WtRep I O Ω) (g x : G) (hx : x ∈ I.Nf) (t : I.Tf) (v : Fin (W.d + 1) → Ω) :
    (((W.ξ (g * (x * t)))⁻¹).val *ᵥ v) 0 = (((W.χ t)⁻¹ : Ωˣ) : Ω) * (((W.ξ g)⁻¹).val *ᵥ v) 0 := by
  have h1 : ∀ w : Fin (W.d + 1) → Ω, ((W.ξ x⁻¹).val *ᵥ w) 0 = w 0 := by
    intro w
    have := W.row_N x⁻¹ (inv_mem hx)
    simp only [mulVec, dotProduct]
    simp_rw [this]
    simp
  have h2 : ∀ w : Fin (W.d + 1) → Ω, ((W.ξ ((t⁻¹ : I.Tf) : G)).val *ᵥ w) 0 = (W.χ t⁻¹ : Ω) * w 0 := by
    intro w
    have := W.torusAction t⁻¹
    simp only [mulVec, dotProduct]
    simp_rw [this]
    simp
  have h3 : (W.ξ (g * (x * t)))⁻¹ = W.ξ ((t⁻¹ : I.Tf) : G) * (W.ξ x⁻¹ * (W.ξ g)⁻¹) := by
    simp [mul_assoc]
  rw [h3, Units.val_mul, Units.val_mul, ← mulVec_mulVec, h2, ← mulVec_mulVec, h1, map_inv]

theorem UpperTheory.V.Hi.ctrlEq :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) Ω), (∀ u F, X.ctrl m W (X.raF (W.d + 1) τ u F) = X.ra τ u (X.ctrl m W F)) ∧ (∀ (a : X.I.P) F, X.ctrl m W (X.UF m W a F) = X.U Ω m a (X.ctrl m W F)) ∧ (∀ u (b : Gp) F, X.raF (W.d + 1) τ u (X.rpF Ω (W.d + 1) m b F) = X.rpF Ω (W.d + 1) m b (X.raF (W.d + 1) τ u F)) := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m τ
  refine ⟨fun u F => ?_, fun a F => ?_, fun u b F => ?_⟩
  · ext g i
    change (((W.ξ g.2)⁻¹).val *ᵥ fun k => ((τ u).val *ᵥ fun j => F j (g * ((u : Ga), 1)) k) i) 0 =
      ((τ u).val *ᵥ fun j => (((W.ξ (g * ((u : Ga), 1)).2)⁻¹).val *ᵥ F j (g * ((u : Ga), 1))) 0) i
    simp only [mulVec, dotProduct, Prod.snd_mul, mul_one, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  · haveI : Finite (X.I.N ⧸ (X.I.Nconj a).subgroupOf X.I.N) :=
      Nat.finite_of_card_ne_zero (X.I.fin_N a a.2)
    haveI := Fintype.ofFinite (X.I.N ⧸ (X.I.Nconj a).subgroupOf X.I.N)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Frame.UF, Frame.U, Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.smul_apply, LinearMap.sum_apply,
      map_smul, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ext g i
    have := UpperTheory.V.Hi.ctrlEq_row W g.2 (q.out : X.I.N) (X.I.N_le q.out.2) ⟨a, X.I.P_le a a.2⟩
      (F i (g * (1, ((q.out : X.I.N) : Gp) * a)))
    exact this.symm
  · ext i g k
    change ((τ u).val *ᵥ fun j => F j (g * ((u : Ga), 1) * (1, b)) k) i =
      ((τ u).val *ᵥ fun j => F j (g * (1, b) * ((u : Ga), 1)) k) i
    simp [mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.FnIndep
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.fnIndep :
    ∀ (O Ω S ι : Type) [CommRing O] [IsDomain O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ∀ (m : ℕ) (v : ι → S → Fin m → O), LinearIndependent O v → LinearIndependent Ω fun i s j => algebraMap O Ω (v i s j) := by
  intro O Ω S ι _ _ _ _ hinj m v hv
  classical
  letI : Algebra (FractionRing O) Ω := (IsFractionRing.lift hinj).toAlgebra
  have htow : ∀ x : O, algebraMap O Ω x =
      algebraMap (FractionRing O) Ω (algebraMap O (FractionRing O) x) :=
    fun x => (IsFractionRing.lift_algebraMap hinj x).symm
  have hu : LinearIndependent (FractionRing O)
      (fun i s j => algebraMap O (FractionRing O) (v i s j)) := by
    rw [← LinearIndependent.iff_fractionRing O (FractionRing O)]
    have hf : Function.Injective
        (((Algebra.linearMap O (FractionRing O)).compLeft (Fin m)).compLeft S) := by
      intro a c hac
      funext s j
      exact IsFractionRing.injective O (FractionRing O) (congrFun (congrFun hac s) j)
    exact hv.map' _ (LinearMap.ker_eq_bot.mpr hf)
  let b := Module.Free.chooseBasis (FractionRing O) Ω
  rw [linearIndependent_iff'] at hu ⊢
  intro s g hg i hi
  refine b.ext_elem fun k => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine hu s (fun i => b.repr (g i) k) ?_ i hi
  funext x y
  have h := congrFun (congrFun hg x) y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
  have h2 := congrArg (fun z => b.repr z k) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zero, Finsupp.zero_apply, Finset.sum_apply'] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : g i * algebraMap (FractionRing O) Ω (algebraMap O (FractionRing O) (v i x y)) =
      algebraMap O (FractionRing O) (v i x y) • g i := by
    rw [Algebra.smul_def, mul_comm]
  rw [htow, e, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
end
