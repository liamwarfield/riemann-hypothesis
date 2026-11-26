module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KrullDimQuotientComapEq
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem krull_dim_quotient_comap_eq {k Z A B C : Type} [Field k] [AddCommGroup Z] [Module k Z] [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C] [Module.Finite k A] [Module.Finite k C]
    (δ : Z →ₗ[k] A) (β : A →ₗ[k] B) (p : B →ₗ[k] C) (h0 : Function.Injective δ)
    (h1 : LinearMap.range δ = LinearMap.ker β) (h2 : LinearMap.range β = LinearMap.ker p) :
    Module.finrank k Z + Module.finrank k B = Module.finrank k A + Module.finrank k (LinearMap.range p) := by
  have hB : Module.Finite k B := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker p (IsNoetherian.noetherian _) ?_⟩
    rw [top_inf_eq, ← h2, LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  have e1 := LinearMap.finrank_range_add_finrank_ker β
  have e2 := LinearMap.finrank_range_add_finrank_ker p
  have e3 := LinearMap.finrank_range_of_inj h0
  rw [← h1, h2] at e1
  omega

private theorem cob_lc {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module k M] (ρ : Representation k Γ M) (h : IsOpen (ρ.ker : Set Γ)) (m : M) :
    IsLocallyConstant (fun g => ρ g m - m) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ρ.ker : Set Γ), h.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  have hy' : ρ (x⁻¹ * y) = 1 := hy
  have : ρ y = ρ x := by
    conv_lhs => rw [← mul_inv_cancel_left x y, map_mul, hy', mul_one]
  rw [this]

theorem UpperTheory.V.Alg.finrank_compact_support_H1 :
    ∀ (k Γ M : Type) [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M]
      (ρ : Representation k Γ M), IsOpen (ρ.ker : Set Γ) → ∀ (F : Frame Γ), (∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) → Module.Finite k (ReciprocityTheory.Gal.H1 ρ) →
      Module.finrank k (ReciprocityTheory.Gal.H0 ρ) + Module.finrank k (F.H1c ρ) = ∑ v, Module.finrank k (ReciprocityTheory.Gal.H0 (ρ.comp (F.φ v) : Representation k _ M)) +
        Module.finrank k (ReciprocityTheory.Gal.Sha1 ρ F.φ F.hφ ⊓ ReciprocityTheory.Gal.Sel ρ F.ψ F.hψ (fun q => ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) : Submodule k (ReciprocityTheory.Gal.H1 ρ)) := by
  intro k Γ M _ _ _ _ _ _ _ _ _ _ _ ρ hρ F hN hfin
  classical
  let δ : ReciprocityTheory.Gal.H0 ρ →ₗ[k] (∀ v, ReciprocityTheory.Gal.H0 (ρ.comp (F.φ v) : Representation k _ M)) :=
    LinearMap.pi fun v => ReciprocityTheory.Gal.resH0 ρ (F.φ v)
  let β : (∀ v, ReciprocityTheory.Gal.H0 (ρ.comp (F.φ v) : Representation k _ M)) →ₗ[k] F.H1c ρ :=
    { toFun := fun b => ⟨(fun g => ρ g (-(b F.v0).1) - (-(b F.v0).1), fun v => (b v).1 - (b F.v0).1),
        cob_lc ρ hρ _, fun s t => by
          simp only [map_mul, Module.End.mul_apply, map_sub]; abel,
        fun q n hn => by simp [hN q n hn],
        fun v s => by
          have : ρ (F.φ v s) (b v).1 = (b v).1 := (b v).2 s
          simp only [map_sub, map_neg, this]; abel,
        sub_self _⟩
      map_add' := fun b b' => by
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
        · simp; abel
        · simp; abel
      map_smul' := fun c b => by
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
        · simp [smul_add]
        · simp [smul_sub] }
  let p0 : F.H1c ρ →ₗ[k] ReciprocityTheory.Gal.Z1 ρ :=
    { toFun := fun x => ⟨x.1.1, x.2.1.continuous, x.2.2.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p : F.H1c ρ →ₗ[k] ReciprocityTheory.Gal.H1 ρ := (Submodule.mkQ _).comp p0
  have h0 : Function.Injective δ := by
    intro x y hxy
    have := congrArg (fun b => (b F.v0).1) hxy
    exact Subtype.ext this
  have h1 : LinearMap.range δ = LinearMap.ker β := by
    ext b
    rw [LinearMap.mem_ker]
    constructor
    · rintro ⟨m, rfl⟩
      apply Subtype.ext
      refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
      · change ρ g (-m.1) - (-m.1) = 0
        rw [map_neg, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere ρ m.1).1 m.2 g, sub_self]
      · exact sub_self m.1
    · intro hb
      have e1 : ∀ g, ρ g (-(b F.v0).1) - (-(b F.v0).1) = 0 := fun g =>
        congrArg (fun x : F.H1c ρ => x.1.1 g) hb
      have e2 : ∀ v, (b v).1 - (b F.v0).1 = 0 := fun v =>
        congrArg (fun x : F.H1c ρ => x.1.2 v) hb
      refine ⟨⟨(b F.v0).1, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere ρ _).2 fun g => ?_⟩, funext fun v => Subtype.ext ?_⟩
      · have := e1 g
        rw [map_neg, sub_eq_zero] at this
        exact neg_injective this
      · exact (sub_eq_zero.1 (e2 v)).symm
  have h2 : LinearMap.range β = LinearMap.ker p := by
    ext x
    rw [LinearMap.mem_ker]
    change _ ↔ Submodule.Quotient.mk (p0 x) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨-(b F.v0).1, fun g => rfl⟩
    · rintro ⟨m, hm⟩
      have hm' : ∀ g, x.1.1 g = ρ g m - m := hm
      obtain ⟨-, -, -, a4, a5⟩ := x.2
      refine ⟨fun v => ⟨x.1.2 v - m, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun s => ?_⟩, ?_⟩
      · change ρ (F.φ v s) (x.1.2 v - m) = x.1.2 v - m
        have := a4 v s
        rw [hm'] at this
        rw [map_sub, sub_eq_sub_iff_sub_eq_sub, this]
      · apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
        · change ρ g (-(x.1.2 F.v0 - m)) - (-(x.1.2 F.v0 - m)) = x.1.1 g
          rw [a5, hm']; simp
        · change x.1.2 v - m - (x.1.2 F.v0 - m) = x.1.2 v
          rw [a5]; abel
  have key : ∀ c : ReciprocityTheory.Gal.Z1 ρ, (Submodule.Quotient.mk c : ReciprocityTheory.Gal.H1 ρ) ∈
      (ReciprocityTheory.Gal.Sha1 ρ F.φ F.hφ ⊓ ReciprocityTheory.Gal.Sel ρ F.ψ F.hψ (fun q => ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) : Submodule k (ReciprocityTheory.Gal.H1 ρ)) ↔
      (∀ v, ∃ m, ∀ s, c.1 (F.φ v s) = ρ (F.φ v s) m - m) ∧ ∀ q, ∀ n ∈ F.N q, c.1 (F.ψ q n) = 0 := by
    intro c
    rw [Submodule.mem_inf, ReciprocityTheory.Gal.mem_Sel, ReciprocityTheory.Gal.Sha1, Submodule.mem_iInf]
    refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun q => ?_)
    · rw [LinearMap.mem_ker, ReciprocityTheory.Gal.resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
      rfl
    · rw [ReciprocityTheory.Gal.H1ur, LinearMap.mem_ker, ReciprocityTheory.Gal.resH1]
      refine (Submodule.Quotient.mk_eq_zero _).trans ?_
      rw [ Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
      constructor
      · rintro ⟨m, hm⟩ n hn
        have : c.1 (F.ψ q n) = ρ (F.ψ q n) m - m := hm ⟨n, hn⟩
        rw [this, hN q n hn]; simp
      · intro h
        refine ⟨0, fun n => ?_⟩
        change c.1 (F.ψ q n.1) = ρ (F.ψ q n.1) 0 - 0
        rw [h n.1 n.2]; simp
  have h3 : LinearMap.range p = (ReciprocityTheory.Gal.Sha1 ρ F.φ F.hφ ⊓ ReciprocityTheory.Gal.Sel ρ F.ψ F.hψ (fun q => ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) : Submodule k (ReciprocityTheory.Gal.H1 ρ)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨-, -, a3, a4, -⟩ := x.2
      exact (key (p0 x)).2 ⟨fun v => ⟨x.1.2 v, a4 v⟩, a3⟩
    · intro hy
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨k1, k2⟩ := (key c).1 hy
      choose m hm using k1
      refine ⟨⟨(fun g => c.1 g - (ρ g (m F.v0) - m F.v0), fun v => m v - m F.v0),
        ((IsLocallyConstant.iff_continuous _).2 c.2.1).sub (cob_lc ρ hρ _), fun s t => ?_, fun q n hn => ?_,
        fun v s => ?_, sub_self _⟩, ?_⟩
      · simp only [c.2.2 s t, map_mul, Module.End.mul_apply, map_sub]; abel
      · simp [k2 q n hn, hN q n hn]
      · simp only [hm, map_sub]; abel
      · change Submodule.Quotient.mk _ = _
        rw [Submodule.Quotient.eq, Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
        refine ⟨-m F.v0, fun g => ?_⟩
        change c.1 g - (ρ g (m F.v0) - m F.v0) - c.1 g = _
        rw [map_neg]; abel
  have := krull_dim_quotient_comap_eq δ β p h0 h1 h2
  rw [h3, Module.finrank_pi_fintype] at this
  exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ContSection
open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem chain_stab {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (K : Ideal R)
    (hK : maximalIdeal R * K = ⊥) (F : ℕ → Ideal R) (hF : Antitone F) (hle : ∀ n, F n ≤ K) :
    ∃ N, ∀ n, F N ≤ F n := by
  classical
  have hT : Module.IsTorsionBySet R K (maximalIdeal R : Set R) := by
    intro x a
    apply Subtype.ext
    have h1 : (a : R) * (x : R) ∈ maximalIdeal R * K := Ideal.mul_mem_mul a.2 x.2
    rw [hK] at h1
    simpa using h1
  letI : Module (R ⧸ maximalIdeal R) K := hT.module
  haveI : IsScalarTower R (R ⧸ maximalIdeal R) K := hT.isScalarTower
  haveI : Module.Finite R K := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian K)
  haveI : Module.Finite (R ⧸ maximalIdeal R) K :=
    Module.Finite.of_restrictScalars_finite R _ _
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  haveI : IsArtinianRing (R ⧸ maximalIdeal R) := inferInstance
  haveI : IsArtinian (R ⧸ maximalIdeal R) K := isArtinian_of_fg_of_artinian'
  haveI : IsArtinian R K := isArtinian_of_surjective_algebraMap (R := R ⧸ maximalIdeal R)
    (Ideal.Quotient.mk_surjective (I := maximalIdeal R))
  let G : ℕ → Submodule R K := fun n => Submodule.comap (Submodule.subtype K) (F n)
  have hG : Antitone G := fun a b h => Submodule.comap_mono (hF h)
  obtain ⟨_, ⟨N, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule R K)).has_min (Set.range G) ⟨_, 0, rfl⟩
  refine ⟨N, fun n => ?_⟩
  have hle2 : G (max N n) ≤ G N := hG (le_max_left _ _)
  have heq : G (max N n) = G N := by
    by_contra hne
    exact hmin _ ⟨_, rfl⟩ (lt_of_le_of_ne hle2 hne)
  intro x hx
  have hxK : x ∈ K := hle N hx
  have h2 : (⟨x, hxK⟩ : K) ∈ G N := hx
  rw [← heq] at h2
  exact hF (le_max_right N n) h2

private theorem mul_mem_of_mem_ideal_killed_by_maximalIdeal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [IsCO O R] (J : Ideal R) (hJ : maximalIdeal R * J = ⊥) (S : Submodule O R) (r k : R)
    (hk : k ∈ J) (hS : k ∈ S) : r * k ∈ S := by
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) r
  have h0 : (r - algebraMap O R a) * k = 0 := by
    have h1 := Ideal.mul_mem_mul ha hk
    rw [hJ] at h1
    exact (Ideal.mem_bot).1 h1
  have h2 : r * k = a • k := by
    rw [Algebra.smul_def]
    linear_combination h0
  rw [h2]
  exact S.smul_mem a hS

theorem UpperTheory.V.Alg.cont_section :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (p : R →ₐ[O] R'), Function.Surjective p → maximalIdeal R * RingHom.ker p = ⊥ → ∀ (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) →
      ∀ (Γ : Type) [TopologicalSpace Γ] (j : X) (x : Γ → R'), AdicCont (maximalIdeal R') x → (∀ g, x g ∈ (W.part j).map p.toLinearMap) →
      ∃ y : Γ → R, AdicCont (maximalIdeal R) y ∧ (∀ g, y g ∈ W.part j) ∧ ∀ g, p (y g) = x g := by
  intro O _ _ _ _ X _ _ _ R _ _ _ R' _ _ _ p hp hker W hz Γ _ j x hxc hxp
  classical
  have hmem : ∀ r : R, p r ∈ maximalIdeal R' ↔ r ∈ maximalIdeal R := by
    intro r
    rw [← res_eq_zero_iff O R', ← res_eq_zero_iff O R, res_map]
  have hmapm : Ideal.map p (maximalIdeal R) = maximalIdeal R' := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective p hp]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact (hmem r).2 hr
    · intro ha
      obtain ⟨r, rfl⟩ := hp a
      exact ⟨r, (hmem r).1 ha, rfl⟩
  have hlift : ∀ n (a : R'), a ∈ maximalIdeal R' ^ n → ∃ w, w ∈ maximalIdeal R ^ n ∧ p w = a := by
    intro n a ha
    rw [← hmapm, ← Ideal.map_pow] at ha
    exact (Ideal.mem_map_iff_of_surjective p hp).1 ha
  obtain ⟨N0, hN0⟩ := chain_stab (RingHom.ker p) hker (fun n => maximalIdeal R ^ n ⊓ RingHom.ker p)
    (fun a b h => inf_le_inf_right _ (Ideal.pow_le_pow_right h)) (fun n => inf_le_right)
  have hinj : ∀ u v : R, u ∈ maximalIdeal R ^ N0 → v ∈ maximalIdeal R ^ N0 → p u = p v → u = v := by
    intro u v hu hv huv
    have hk : u - v ∈ maximalIdeal R ^ N0 ⊓ RingHom.ker p :=
      ⟨Ideal.sub_mem _ hu hv, (RingHom.mem_ker).2 (by rw [map_sub, huv, sub_self])⟩
    have hall : u - v ∈ ⨅ n, maximalIdeal R ^ n := Ideal.mem_iInf.2 fun n => (hN0 n hk).1
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing (I := maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top] at hall
    exact sub_eq_zero.1 ((Ideal.mem_bot).1 hall)
  let F : ℕ → Ideal R := fun n =>
    { carrier := {k | k ∈ RingHom.ker p ∧ k ∈ W.part j ⊔ (maximalIdeal R ^ n).restrictScalars O}
      add_mem' := fun ha hb => ⟨Ideal.add_mem _ ha.1 hb.1, Submodule.add_mem _ ha.2 hb.2⟩
      zero_mem' := ⟨Ideal.zero_mem _, Submodule.zero_mem _⟩
      smul_mem' := fun r k hk =>
        ⟨Ideal.mul_mem_left _ r hk.1, mul_mem_of_mem_ideal_killed_by_maximalIdeal (O := O) _ hker _ r k hk.1 hk.2⟩ }
  have hFanti : Antitone F := by
    intro a b h k hk
    have H : (maximalIdeal R ^ b).restrictScalars O ≤ (maximalIdeal R ^ a).restrictScalars O :=
      fun z hz => Ideal.pow_le_pow_right h hz
    exact ⟨hk.1, SetLike.le_def.1 (sup_le_sup_left H (W.part j)) hk.2⟩
  obtain ⟨N1, hN1⟩ := chain_stab (RingHom.ker p) hker F hFanti (fun n k hk => hk.1)
  have hclosed : ∀ k, k ∈ RingHom.ker p →
      k ∈ W.part j ⊔ (maximalIdeal R ^ N1).restrictScalars O → k ∈ W.part j := by
    intro k hk1 hk2
    have hkF : k ∈ F N1 := ⟨hk1, hk2⟩
    apply part_closed O X R W hz j k
    intro N
    obtain ⟨y, hy, z, hz2, hyz⟩ := Submodule.mem_sup.1 (hN1 N hkF).2
    refine ⟨y, hy, ?_⟩
    rw [← hyz, add_sub_cancel_left]
    exact hz2
  have hL : ∀ a, a ∈ (W.part j).map p.toLinearMap → a ∈ maximalIdeal R' ^ (max N0 N1) →
      ∃ w, w ∈ W.part j ∧ w ∈ maximalIdeal R ^ (max N0 N1) ∧ p w = a := by
    intro a ha haM
    obtain ⟨e, he, rfl⟩ := Submodule.mem_map.1 ha
    obtain ⟨w, hw, hpw⟩ := hlift _ _ haM
    have hk1 : e - w ∈ RingHom.ker p := by
      rw [RingHom.mem_ker, map_sub, hpw, AlgHom.toLinearMap_apply, sub_self]
    have hk2 : e - w ∈ W.part j ⊔ (maximalIdeal R ^ N1).restrictScalars O := by
      rw [sub_eq_add_neg]
      exact Submodule.add_mem_sup he
        (Submodule.neg_mem _ (Ideal.pow_le_pow_right (le_max_right _ _) hw))
    have hk := hclosed _ hk1 hk2
    refine ⟨w, ?_, hw, hpw⟩
    have h3 := Submodule.sub_mem _ he hk
    rwa [sub_sub_cancel] at h3
  let base : (R' ⧸ maximalIdeal R' ^ (max N0 N1)) → R := fun c =>
    if h : ∃ e, e ∈ W.part j ∧ Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (p e) = c
    then h.choose else 0
  have hbase : ∀ g, base (Ideal.Quotient.mk _ (x g)) ∈ W.part j ∧
      x g - p (base (Ideal.Quotient.mk _ (x g))) ∈ maximalIdeal R' ^ (max N0 N1) := by
    intro g
    obtain ⟨e, he, hpe⟩ := Submodule.mem_map.1 (hxp g)
    have h : ∃ e, e ∈ W.part j ∧ Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (p e) =
        Ideal.Quotient.mk _ (x g) := ⟨e, he, by rw [← hpe]; rfl⟩
    simp only [base]
    rw [dite_eq_left h]
    refine ⟨h.choose_spec.1, ?_⟩
    rw [← Ideal.Quotient.eq]
    exact h.choose_spec.2.symm
  have hw : ∀ g, ∃ w, w ∈ W.part j ∧ w ∈ maximalIdeal R ^ (max N0 N1) ∧
      p w = x g - p (base (Ideal.Quotient.mk _ (x g))) := by
    intro g
    apply hL
    · exact Submodule.sub_mem _ (hxp g) (Submodule.mem_map_of_mem (hbase g).1)
    · exact (hbase g).2
  choose w hwP hwM hwp using hw
  refine ⟨fun g => base (Ideal.Quotient.mk _ (x g)) + w g, ?_,
    fun g => Submodule.add_mem _ (hbase g).1 (hwP g), fun g => ?_⟩
  · unfold AdicCont at hxc ⊢
    intro N
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have hx0 := (IsLocallyConstant.iff_eventually_eq _).1 (hxc (max N (max N0 N1))) g0
    filter_upwards [hx0] with g hg
    have hd : x g - x g0 ∈ maximalIdeal R' ^ max N (max N0 N1) := Ideal.Quotient.eq.1 hg
    have hcls : Ideal.Quotient.mk (maximalIdeal R' ^ (max N0 N1)) (x g) =
        Ideal.Quotient.mk _ (x g0) :=
      Ideal.Quotient.eq.2 (Ideal.pow_le_pow_right (le_max_right _ _) hd)
    obtain ⟨v, hv, hpv⟩ := hlift _ _ hd
    have hM0 : maximalIdeal R ^ (max N0 N1) ≤ maximalIdeal R ^ N0 :=
      Ideal.pow_le_pow_right (le_max_left _ _)
    have heq : w g - w g0 = v := by
      apply hinj
      · exact Ideal.sub_mem _ (hM0 (hwM g)) (hM0 (hwM g0))
      · exact Ideal.pow_le_pow_right (le_trans (le_max_left _ _) (le_max_right _ _)) hv
      · rw [map_sub, hwp, hwp, hpv, hcls]
        ring
    apply Ideal.Quotient.eq.2
    show base (Ideal.Quotient.mk _ (x g)) + w g - (base (Ideal.Quotient.mk _ (x g0)) + w g0) ∈ _
    rw [hcls]
    have h4 : base (Ideal.Quotient.mk _ (x g0)) + w g -
        (base (Ideal.Quotient.mk _ (x g0)) + w g0) = v := by
      rw [← heq]
      ring
    rw [h4]
    exact Ideal.pow_le_pow_right (le_max_left _ _) hv
  · show p (base _ + w g) = x g
    rw [map_add (f := _), hwp]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartFilt
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PartialFiltrationCoeff
theorem UpperTheory.Reformulated.B.PartialFiltrationCoeff.part_filt_coeff :
    ∀ {O σ : Type} [inst : CommRing O]
    [inst_1 : IsLocalRing O] (M : ℕ),
    ∀ f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ M,
      ∀ (n : σ →₀ ℕ),
        (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f ∈
          IsLocalRing.maximalIdeal O ^ (M - (Finsupp.degree : (σ →₀ ℕ) → ℕ) n) := by
  intro O σ _ _ M
  classical
  induction M with
  | zero =>
    intro f _ n
    simp
  | succ M ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb n
      rw [MvPowerSeries.coeff_mul]
      refine Ideal.sum_mem _ ?_
      rintro ⟨p, q⟩ hpq
      have hsum : p + q = n := by simpa using hpq
      have hdeg : Finsupp.degree p + Finsupp.degree q = Finsupp.degree n := by
        rw [← hsum, map_add (f := _)]
      have hp := ih a ha p
      by_cases hq : q = 0
      · subst hq
        have hb0 : MvPowerSeries.coeff (0 : σ →₀ ℕ) b ∈ IsLocalRing.maximalIdeal O := by
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
          intro hu
          exact hb (MvPowerSeries.isUnit_iff_constantCoeff.mpr (by simpa using hu))
        have hmul := Ideal.mul_mem_mul hp hb0
        rw [← pow_succ] at hmul
        exact Ideal.pow_le_pow_right (by omega) hmul
      · have hq' : Finsupp.degree q ≠ 0 := fun h => hq ((Finsupp.degree_eq_zero_iff q).mp h)
        exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) hp)
    · intro x y hx hy n
      rw [map_add (f := _)]
      exact Ideal.add_mem _ (hx n) (hy n)
end

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem UpperTheory.V.Alg.part_filt_coeff {O σ : Type} [CommRing O] [IsLocalRing O] (M : ℕ) :
    ∀ f ∈ maximalIdeal (MvPowerSeries σ O) ^ M, ∀ n : σ →₀ ℕ,
      coeff n f ∈ maximalIdeal O ^ (M - n.degree) :=
  _root_.UpperTheory.Reformulated.B.PartialFiltrationCoeff.part_filt_coeff M

private theorem UpperTheory.V.Alg.part_filt_split {σ X : Type} [Finite σ] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (wt : σ → X) (j : X) :
    ∃ D : ℕ, ∀ n : σ →₀ ℕ, Finsupp.weight wt n = j → D < n.degree →
      ∃ g n' : σ →₀ ℕ, g ≠ 0 ∧ Finsupp.weight wt g = 0 ∧ g.degree ≤ D ∧ n = g + n' := by
  classical
  obtain ⟨g, hg, hcl, hj⟩ := UpperTheory.V.Alg.gordan σ X wt
  obtain ⟨μ, hμ, hμ'⟩ := hj j
  refine ⟨(g ∪ μ).sup Finsupp.degree, fun n hn hD => ?_⟩
  obtain ⟨m, hm, hmn⟩ := hμ' n hn
  obtain ⟨r, rfl⟩ := exists_add_of_le hmn
  have hr : Finsupp.weight wt r = 0 := by
    rw [map_add (f := _), hμ m hm] at hn
    simpa using hn
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : m.degree ≤ (g ∪ μ).sup Finsupp.degree :=
      Finset.le_sup (f := Finsupp.degree) (Finset.mem_union_right _ hm)
    rw [add_zero] at hD
    omega
  have key : ∀ r ∈ AddSubmonoid.closure (g : Set (σ →₀ ℕ)), r = 0 ∨ ∃ a ∈ g, a ≤ r := by
    intro r hr
    induction hr using AddSubmonoid.closure_induction with
    | mem x hx => exact Or.inr ⟨x, hx, le_rfl⟩
    | zero => exact Or.inl rfl
    | add x y _ _ hx hy =>
      rcases hx with rfl | ⟨a, ha, hax⟩
      · simpa using hy
      · exact Or.inr ⟨a, ha, hax.trans le_self_add⟩
  obtain ⟨a, ha, har⟩ := (key r (hcl r hr)).resolve_left hr0
  obtain ⟨b, rfl⟩ := exists_add_of_le har
  exact ⟨a, m + b, (hg a ha).1, (hg a ha).2,
    Finset.le_sup (f := Finsupp.degree) (Finset.mem_union_left _ ha), by abel⟩

private theorem UpperTheory.V.Alg.part_filt_monomial {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    {j : X} {n : σ →₀ ℕ} (hn : Finsupp.weight wt n = j) (c : O) : monomial n c ∈ wtPart O wt j := by
  classical
  intro m hm
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hm hn

theorem UpperTheory.V.Alg.part_filt :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (j : X) (n : ℕ), ∃ M : ℕ, W.part j ⊓ (maximalIdeal R ^ M).restrictScalars O ≤ (W.part 0 ⊓ (maximalIdeal R).restrictScalars O) ^ n * W.part 0 * W.part j := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W _ j k
  classical
  set Q : Submodule O R := W.part 0 ⊓ (maximalIdeal R).restrictScalars O with hQ
  have hloc : IsLocalHom (W.π : MvPowerSeries W.σ O →+* R) := IsLocalHom.of_surjective _ W.surj
  have hone : (1 : R) ∈ W.part 0 := ⟨1, one_mem_wtPart O W.wt, map_one W.π⟩

  have hmono : ∀ k : ℕ, ∃ N : ℕ, ∀ n : W.σ →₀ ℕ, Finsupp.weight W.wt n = j → N ≤ n.degree →
      W.π (monomial n 1) ∈ Q ^ k * W.part j := by
    obtain ⟨D, hD⟩ := UpperTheory.V.Alg.part_filt_split W.wt j
    intro k
    induction k with
    | zero =>
      refine ⟨0, fun n hn _ => ?_⟩
      rw [pow_zero, one_mul]
      exact ⟨_, UpperTheory.V.Alg.part_filt_monomial W.wt hn 1, rfl⟩
    | succ k ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨N + D + 1, fun n hn hd => ?_⟩
      obtain ⟨g, n', hg0, hgw, hgd, rfl⟩ := hD n hn (by omega)
      rw [map_add (f := _)] at hd
      rw [map_add (f := _), hgw, zero_add] at hn
      have h1 := hN n' hn (by omega)
      have h2 : W.π (monomial g 1) ∈ Q := by
        refine ⟨⟨_, UpperTheory.V.Alg.part_filt_monomial W.wt hgw 1, rfl⟩, ?_⟩
        intro hu
        have h3 : IsUnit (monomial g (1 : O)) := hloc.map_nonunit _ hu
        rw [MvPowerSeries.isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_monomial,
          if_neg hg0.symm] at h3
        exact not_isUnit_zero h3
      have h4 : (monomial (g + n') (1 : O) : MvPowerSeries W.σ O) = monomial g 1 * monomial n' 1 := by
        rw [monomial_mul_monomial, one_mul]
      rw [h4, map_mul, pow_succ', mul_assoc]
      exact Submodule.mul_mem_mul h2 h1

  have hconst : ∀ k : ℕ, ∀ c ∈ maximalIdeal O ^ k, algebraMap O R c ∈ Q ^ k := by
    intro k
    induction k with
    | zero =>
      intro c _
      rw [pow_zero]
      exact Submodule.algebraMap_mem c
    | succ k ih =>
      intro c hc
      rw [pow_succ] at hc
      refine Submodule.mul_induction_on hc (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · rw [map_mul, pow_succ]
        refine Submodule.mul_mem_mul (ih a ha) ⟨?_, ?_⟩
        · rw [Algebra.algebraMap_eq_smul_one]
          exact Submodule.smul_mem _ _ hone
        · exact fun hu => hb (IsLocalHom.map_nonunit (f := algebraMap O R) b hu)
      · rw [map_add (f := _)]
        exact add_mem ha hb
  obtain ⟨N, hN⟩ := hmono k
  refine ⟨N + k, ?_⟩
  rintro x ⟨⟨f, hf, hfx⟩, hx⟩
  have hfx' : W.π f = x := hfx
  have hle : maximalIdeal R ≤ (maximalIdeal (MvPowerSeries W.σ O)).map W.π := by
    intro y hy
    obtain ⟨g, rfl⟩ := W.surj y
    exact Ideal.mem_map_of_mem _ fun hu => hy (hu.map W.π)
  have hx' : x ∈ (maximalIdeal (MvPowerSeries W.σ O) ^ (N + k)).map W.π := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hle _ hx
  obtain ⟨g, hg, hgx⟩ := (Ideal.mem_map_iff_of_surjective W.π W.surj).1 hx'
  set h := wcomp O W.wt j g with hh
  have hhx : W.π h = x := by
    have h1 : f - g ∈ RingHom.ker W.π := by
      rw [RingHom.mem_ker, map_sub, hfx', hgx, sub_self]
    have h2 := W.homog _ h1 j
    have h3 : wcomp O W.wt j f = f := by
      ext n
      rw [coeff_wcomp]
      split_ifs with hn
      · rfl
      · exact (hf n hn).symm
    rw [map_sub, h3, RingHom.mem_ker, map_sub, hfx', sub_eq_zero] at h2
    exact h2.symm
  have hhj : h ∈ wtPart O W.wt j := wcomp_mem O W.wt j g
  have hhc : ∀ n : W.σ →₀ ℕ, n.degree < N → coeff n h ∈ maximalIdeal O ^ k := by
    intro n hn
    rw [hh, coeff_wcomp]
    split_ifs
    · exact Ideal.pow_le_pow_right (by omega) (UpperTheory.V.Alg.part_filt_coeff _ g hg n)
    · exact zero_mem _
  have hfin : {n : W.σ →₀ ℕ | n.degree < N}.Finite :=
    (Finsupp.finite_of_degree_le N).subset fun n (hn : n.degree < N) => hn.le
  set low : MvPowerSeries W.σ O := ∑ n ∈ hfin.toFinset, monomial n (coeff n h) with hlow
  have hlowc : ∀ m, coeff m low = if m.degree < N then coeff m h else 0 := by
    intro m
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hlow, map_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq]
    simp
  obtain ⟨μ, hμ, hspan⟩ := UpperTheory.V.Alg.part_span O R X W
    {n | Finsupp.weight W.wt n = j ∧ N ≤ n.degree} j fun n hn => hn.1
  obtain ⟨b, hb, hhigh⟩ := hspan (h - low) (by
    intro n hn
    rw [map_sub, hlowc]
    split_ifs with hd
    · exact sub_self _
    · rw [sub_zero]
      exact hhj n fun hw => hn ⟨hw, not_lt.1 hd⟩)
  have hsum : x = W.π low + W.π (h - low) := by rw [← map_add (f := _), add_sub_cancel, hhx]
  rw [hsum]
  refine add_mem ?_ ?_
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hlow, map_sum]
    refine Submodule.sum_mem _ fun n hn => ?_
    by_cases hw : Finsupp.weight W.wt n = j
    · have h1 : W.π (monomial n (coeff n h)) = algebraMap O R (coeff n h) * 1 * W.π (monomial n 1) := by
        rw [mul_one, ← Algebra.smul_def, ← map_smul, ← map_smul, smul_eq_mul, mul_one]
      rw [h1]
      exact Submodule.mul_mem_mul
        (Submodule.mul_mem_mul (hconst k _ (hhc n (hfin.mem_toFinset.1 hn))) hone)
        ⟨_, UpperTheory.V.Alg.part_filt_monomial W.wt hw 1, rfl⟩
    · rw [hhj n hw, map_zero, map_zero]
      exact zero_mem _
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hhigh, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [map_mul, mul_comm (Q ^ k), mul_assoc]
    exact Submodule.mul_mem_mul ⟨_, hb m, rfl⟩ (hN m (hμ hm).1 (hμ hm).2)
end
