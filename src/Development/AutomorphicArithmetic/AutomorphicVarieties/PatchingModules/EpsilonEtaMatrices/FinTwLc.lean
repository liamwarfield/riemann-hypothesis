module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LcOfOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.EvIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FinTwLc
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem finTw_lc {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  have hs : ∀ i j, ∀ x, ∀ᶠ y in nhds x, f y i j = f x i j := fun i j =>
    (IsLocallyConstant.iff_eventually_eq _).1 (h i j)
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have hall : ∀ᶠ y in nhds x, ∀ i j, f y i j = f x i j := by
    simp only [Filter.eventually_all]
    exact fun i j => hs i j x
  filter_upwards [hall] with y hy
  ext i j
  exact hy i j

theorem UpperTheory.V.Pa.finTw :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m : ℕ), PhiCond G0.Γ l → (TwZ k (x.Am m)).Finite := by
  intro l _ L G0 n x k m hΦ
  obtain ⟨_, _, hfinR, _, hlR, _, htR, _, _⟩ := finAm l G0.frame n x m k.g
  let χ : G0.Γ →* x.A := (algebraMap ℤ_[l] x.A).toMonoidHom.comp ((Units.coeHom ℤ_[l]).comp G0.ε)
  have hok := (ok1 l L G0 G0 (Glob.Hom.refl G0) n x k (x.Am m) χ).2.1
  obtain ⟨rep, hrep⟩ := adEx l G0.frame x.A (DD (x.Am m) k.g) n _ _ _ hok
  obtain ⟨_, hlce, hLC⟩ := lc1 l L G0 G0 (Glob.Hom.refl G0) n x k m
  have hLCrep := hLC _ _ rep hlce hrep
  haveI : Finite (DD (x.Am m) k.g) := hfinR
  have hl : ∀ v : pairedDualFirstOrderDualMatrixSpace n x.A (x.Am m) k.g x.a, l • v = 0 := by
    intro v
    apply Subtype.ext
    funext i j
    simp [hlR]
  have finite_addMonoidHom_zmod_of_finite (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Finite M] :
      Finite (M →+ ZMod l) := by
    haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
    exact Finite.of_injective (fun f : M →+ ZMod l => (f : M → ZMod l)) DFunLike.coe_injective
  
  have eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] (hl : ∀ m : M, l • m = 0)
      (m : M) (h : ∀ f : M →+ ZMod l, f m = 0) : m = 0 := by
    letI : Module (ZMod l) M := AddCommGroup.zmodModule hl
    let b := Module.Basis.ofVectorSpace (ZMod l) M
    apply b.repr.injective
    ext i
    have := h (b.coord i).toAddMonoidHom
    rw [LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
    simpa using this
  have finZ_local : ∀ (l : ℕ) [Fact l.Prime] (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M), PhiCond Γ l → LC ρ → (∀ m : M, l • m = 0) → Finite (Zl ρ) := by
    intro l _ R Γ M _ _ _ _ _ _ _ _ ρ hΦ hρ hl
    let N : Subgroup Γ :=
      { carrier := {g | ∀ m, ρ g m = m}
        mul_mem' := by
          intro a b ha hb m
          simp only [Set.mem_setOf_eq] at ha hb
          rw [map_mul, Module.End.mul_apply, hb, ha]
        one_mem' := by
          intro m
          simp
        inv_mem' := by
          intro a ha m
          simp only [Set.mem_setOf_eq] at ha
          have h1 := ha (ρ a⁻¹ m)
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h1
          exact h1.symm }
    have hN : IsOpen (N : Set Γ) := by
      have hset : (N : Set Γ) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
        ext g
        simp [N]
      rw [hset]
      exact isOpen_iInter_of_finite (fun m => (hρ m).isOpen_fiber m)
    haveI : Finite (Γ ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
    haveI : Finite (M →+ ZMod l) := finite_addMonoidHom_zmod_of_finite l M
    haveI := hΦ N hN
    have z1 : ∀ z ∈ Zl ρ, z 1 = 0 := by
      intro z hz
      have h := ((mem_Zl ρ).1 hz).2 1 1
      simpa using h
    have zN : ∀ z ∈ Zl ρ, ∀ a b : Γ, a ∈ N → z (a * b) = z a + z b := by
      intro z hz a b ha
      rw [((mem_Zl ρ).1 hz).2, ha]
    refine Finite.of_injective
      (β := (Γ ⧸ N → M) × ((M →+ ZMod l) →
        {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)}))
      (fun z => (fun q => z.1 q.out, fun f =>
        ⟨⟨⟨fun k => Multiplicative.ofAdd (f (z.1 k)), ?_⟩, ?_⟩, ?_⟩)) ?_
    · show Multiplicative.ofAdd (f (z.1 ((1 : N) : Γ))) = 1
      rw [Subgroup.coe_one, z1 _ z.2, map_zero, ofAdd_zero]
    · intro k k'
      show Multiplicative.ofAdd (f (z.1 ((k * k' : N) : Γ))) =
        Multiplicative.ofAdd (f (z.1 k)) * Multiplicative.ofAdd (f (z.1 k'))
      rw [Subgroup.coe_mul, zN _ z.2 _ _ k.2, map_add (f := _), ofAdd_add]
    · have hlc : IsLocallyConstant (fun k : N => Multiplicative.ofAdd (f (z.1 k))) :=
        (((mem_Zl ρ).1 z.2).1.comp_continuous continuous_subtype_val).comp _
      rw [MonoidHom.coe_ker]
      exact hlc.isOpen_fiber 1
    · intro z z' h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      apply Subtype.ext
      funext g
      have key : ∀ k : N, z.1 k = z'.1 k := by
        intro k
        have hf : ∀ f : M →+ ZMod l, f (z.1 k - z'.1 k) = 0 := by
          intro f
          have h3 := congrArg (fun ψ : {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)} =>
            Multiplicative.toAdd (ψ.1 k)) (congrFun h2 f)
          simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at h3
          rw [map_sub, h3, sub_self]
        exact sub_eq_zero.1 (eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul l M hl _ hf)
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul N g
      have hg : g = (QuotientGroup.mk g : Γ ⧸ N).out * ((k⁻¹ : N) : Γ) := by
        rw [hk]
        simp [mul_assoc]
      have h1' : z.1 (QuotientGroup.mk g : Γ ⧸ N).out = z'.1 (QuotientGroup.mk g : Γ ⧸ N).out :=
        congrFun h1 (QuotientGroup.mk g)
      rw [hg, ((mem_Zl ρ).1 z.2).2, ((mem_Zl ρ).1 z'.2).2, key, h1']
  have hfin := finZ_local l x.A G0.Γ (pairedDualFirstOrderDualMatrixSpace n x.A (x.Am m) k.g x.a) rep hΦ hLCrep hl
  have key : ∀ z ∈ TwZ k (x.Am m), ∃ y ∈ Zl rep, y G0.c = 0 ∧
      ∀ g : G0.frame.G₀, (y (g : G0.Γ) : Matrix _ _ _) = z g := by
    intro z hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    refine (polZ l G0.frame x.A (DD (x.Am m) k.g) n _ _ _ rep hrep).1 z h1 ?_ h3 h4
    apply finTw_lc
    intro i j
    exact (adicLC G0.frame.G₀ (DD (x.Am m) k.g) _ m _ htR).1 (h2 i j)
  let φ : TwZ k (x.Am m) → Zl rep := fun z => ⟨(key z.1 z.2).choose, (key z.1 z.2).choose_spec.1⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    funext g
    have ha := (key a.1 a.2).choose_spec.2.2 g
    have hb := (key b.1 b.2).choose_spec.2.2 g
    have he : (key a.1 a.2).choose = (key b.1 b.2).choose := congrArg Subtype.val hab
    rw [← ha, ← hb, he]
  exact Set.finite_coe_iff.mp (Finite.of_injective φ hinj)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.BdCard
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem lc_mat {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have : ∀ᶠ g in nhds g0, ∀ i j, f g i j = f g0 i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g0
  filter_upwards [this] with g hg
  exact Matrix.ext hg

private theorem block_le₂ {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (h : LC ρ) : Bl ρ ≤ Zl ρ := by
  intro z hz
  obtain ⟨m, hm⟩ := (mem_Bl ρ).1 hz
  obtain rfl : z = fun g => ρ g m - m := funext hm
  refine ⟨(h m).comp (· - m), fun g h => ?_⟩
  simp only [map_mul, map_sub, Module.End.mul_apply]
  abel

private theorem bd_card {l : ℕ} [Fact l.Prime] (F : GFrame l) {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
    {n : ℕ} (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (V : Submodule A (Matrix (Fin n) (Fin n) R))
    (rep : Representation A F.Γ V) (had : IsAd F ρ (fun _ => 1) V rep) (hlc : LC rep) :
    (Bd F ρ V).ncard = {z | z ∈ Bl rep ∧ z F.c = 0}.ncard := by
  have hP := (polZ l F A R n ρ _ V rep had).2
  obtain ⟨a1, a2⟩ := had
  simp only [one_smul] at a1 a2
  have e : Bd F ρ V = (fun (y : F.Γ → V) (g : F.G₀) => (y g : Matrix (Fin n) (Fin n) R)) ''
      {z | z ∈ Bl rep ∧ z F.c = 0} := by
    ext z
    constructor
    · rintro ⟨Y, hY, hT, rfl⟩
      refine ⟨fun g => rep g ⟨Y, hY⟩ - ⟨Y, hY⟩, ⟨(mem_Bl rep).2 ⟨_, fun _ => rfl⟩, ?_⟩, ?_⟩
      · refine sub_eq_zero.2 (Subtype.ext ?_)
        rw [a2]
        show -Yᵀ = Y
        rw [hT, neg_neg]
      · funext g
        show ((rep g ⟨Y, hY⟩ - ⟨Y, hY⟩ : V) : Matrix (Fin n) (Fin n) R) = _
        rw [Submodule.coe_sub, a1]
        rfl
    · rintro ⟨y, ⟨hy, hc⟩, rfl⟩
      obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hy
      refine ⟨Y, Y.2, ?_, funext fun g => ?_⟩
      · rw [hY, sub_eq_zero] at hc
        have := a2 Y
        rw [hc] at this
        exact neg_eq_iff_eq_neg.1 this.symm
      · show (y g : Matrix (Fin n) (Fin n) R) = _
        rw [hY, Submodule.coe_sub, a1]
        rfl
  rw [e, Set.InjOn.ncard_image]
  rintro y ⟨h1, h2⟩ y' ⟨h3, h4⟩ hh
  refine sub_eq_zero.1 ((hP (y - y') (block_le₂ rep hlc (sub_mem h1 h3)) ?_).2 fun g => ?_)
  · rw [Pi.sub_apply, h2, h4, sub_zero]
  · exact sub_eq_zero.2 (Subtype.ext (congrFun hh g))

theorem UpperTheory.V.Pa.selN :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m : ℕ) (rep : Representation x.A G.Γ (k.M1 (x.Am m))), l ≠ 2 → IsAd G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) (fun _ => 1) (k.M1 (x.Am m)) rep → Finite (Zl rep) → (Sel1 h (x.Am m) k).Finite ∧ (Sel1 h (x.Am m) k).ncard * Nat.card (k.M1 (x.Am m)) ≤ {z | z ∈ Zl rep ∧ (∀ v, z ∘ (G.η.ker.subtype.comp (G.φ v)) ∈ (Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation x.A (L.Gv v) _)).toAddSubgroup ⊔ k.Zb (x.Am m) v) ∧ ∀ u, ∀ g ∈ L.Ju u, z (G.φu u g) = 0}.ncard * Nat.card {y : k.M1 (x.Am m) // rep G.c y = y} ∧ (Bd1 h (x.Am m) k).ncard * Nat.card rep.invariants = Nat.card {y : k.M1 (x.Am m) // rep G.c y = y} := by
  intro l _ L G G0 h n x k m rep hl had hfin
  obtain ⟨-, -, fD, -, -, -, ht, h2, -⟩ := finAm l G0.frame n x m k.g
  have hlc : LC rep := (lc1 l L G G0 h n x k m).2.2 _ _ rep (IsLocallyConstant.const _) had
  obtain ⟨-, -, -, -, hine⟩ := rho1 l G0.frame n x k (x.Am m)
  haveI : Finite (k.M1 (x.Am m)) := Subtype.finite
  obtain ⟨c1, -, c3⟩ := cCount x.A G.Γ (k.M1 (x.Am m)) rep G.c G.c_sq (h2 hl)
  have hP := (polZ l G.frame x.A _ n _ _ _ rep had).1
  have a1 : ∀ (g : G.G₀) (Z : k.M1 (x.Am m)), (rep g Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) =
      k.ρ1 (x.Am m) (h.p₀ g) * Z * k.ρ1 (x.Am m) (h.p₀ g⁻¹) := fun g Z => (had.1 g Z).trans (one_smul _ _)
  have pφ : ∀ v g, h.p₀ (G.φ v g) = G0.φ v g := fun v g => Subtype.ext (h.φ v g)
  have pφu : ∀ u g, h.p₀ (G.φu u g) = G0.φu u g := fun u g => Subtype.ext (h.φu u g)
  let Z : AddSubgroup (G.Γ → k.M1 (x.Am m)) :=
    { carrier := {z | z ∈ Zl rep ∧ (∀ v, z ∘ (G.η.ker.subtype.comp (G.φ v)) ∈ (Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation x.A (L.Gv v) _)).toAddSubgroup ⊔ k.Zb (x.Am m) v) ∧ ∀ u, ∀ g ∈ L.Ju u, z (G.φu u g) = 0}
      add_mem' := fun ⟨p1, p2, p3⟩ ⟨q1, q2, q3⟩ => ⟨add_mem p1 q1, fun v => add_mem (p2 v) (q2 v), fun u g hg => by
        rw [Pi.add_apply, p3 u g hg, q3 u g hg, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun v => zero_mem _, fun _ _ _ => rfl⟩
      neg_mem' := fun ⟨p1, p2, p3⟩ => ⟨neg_mem p1, fun v => neg_mem (p2 v), fun u g hg => by
        rw [Pi.neg_apply, p3 u g hg, neg_zero]⟩ }
  have fZ : (Z : Set (G.Γ → k.M1 (x.Am m))).Finite :=
    (Set.toFinite (Zl rep : Set (G.Γ → k.M1 (x.Am m)))).subset fun z hz => hz.1
  have hB : (Bl rep).toAddSubgroup ≤ Z := by
    intro z hz
    refine ⟨block_le₂ rep hlc hz, fun v => AddSubgroup.mem_sup_left ?_, fun u g hg => ?_⟩
    · obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hz
      exact (mem_Bl _).2 ⟨Y, fun g => hY _⟩
    · obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hz
      rw [hY, sub_eq_zero]
      refine Subtype.ext ?_
      rw [a1, ← map_inv, pφu, pφu, hine u _ ⟨g, hg, rfl⟩, hine u _ ⟨g⁻¹, inv_mem hg, rfl⟩, one_mul, mul_one]
  have hc := c1 Z fZ hB fun z hz => hz.1.2
  have fS : {z | z ∈ Z ∧ z G.c = 0}.Finite := fZ.subset fun z hz => hz.1
  have hsub : Sel1 h (x.Am m) k ⊆ (fun (y : G.Γ → k.M1 (x.Am m)) (g : G.G₀) =>
      (y g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g))) '' {z | z ∈ Z ∧ z G.c = 0} := by
    rintro z ⟨s1, s2, s3, s4, s5, s6⟩
    obtain ⟨y, y1, y2, y3⟩ := hP z s1 (lc_mat z fun i j => (adicLC _ _ _ m _ ht).1 (s2 i j))
      (fun g g' => by rw [one_smul]; exact s3 g g') (fun g => by rw [one_smul]; exact s4 g)
    refine ⟨y, ⟨⟨y1, fun v => ?_, fun u g hg => Subtype.ext ?_⟩, y2⟩, funext y3⟩
    · obtain ⟨Y, hY, hloc⟩ := s6 v
      have hb : (fun g => rep g ⟨Y, hY⟩ - ⟨Y, hY⟩) ∈ Bl rep := (mem_Bl rep).2 ⟨_, fun _ => rfl⟩
      obtain ⟨w1, w2⟩ := sub_mem y1 (block_le₂ rep hlc hb)
      set β : G.Γ → k.M1 (x.Am m) := y - fun g => rep g ⟨Y, hY⟩ - ⟨Y, hY⟩ with hβ
      have hv : ∀ g : G.G₀, (β g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) =
          z g - dY G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) Y g := fun g => by
        rw [hβ, Pi.sub_apply, Submodule.coe_sub, Submodule.coe_sub, a1, y3]
        rfl
      refine AddSubgroup.mem_sup.2 ⟨fun g => rep (G.φ v g) ⟨Y, hY⟩ - ⟨Y, hY⟩, (mem_Bl _).2 ⟨_, fun _ => rfl⟩,
        fun g => β (G.φ v g), ⟨?_, fun g g' => ?_, fun g i j hij => ?_, fun g hg i => ?_⟩, ?_⟩
      · exact w1.comp_continuous (continuous_subtype_val.comp (G.φ_cont v))
      · show (β (G.φ v (g * g')) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) = β (G.φ v g) +
          k.ρ1 (x.Am m) (G0.φ v g) * β (G.φ v g') * k.ρ1 (x.Am m) (G0.φ v g)⁻¹
        rw [map_mul, Subgroup.coe_mul, w2, Submodule.coe_add, a1, map_inv, pφ]
      · show (k.wi1 (x.Am m) v * (β (G.φ v g) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * k.w1 (x.Am m) v) i j = 0
        rw [hv]
        exact (hloc g).1 i j hij
      · show (k.wi1 (x.Am m) v * (β (G.φ v g) : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * k.w1 (x.Am m) v) i i = 0
        rw [hv]
        exact (hloc g).2 hg i
      · funext g
        exact add_sub_cancel _ _
    · exact (y3 _).trans (s5 u _ ⟨g, hg, rfl⟩)
  refine ⟨(fS.image _).subset hsub, ?_, ?_⟩
  · refine le_trans (Nat.mul_le_mul_right _ (((Set.ncard_le_ncard hsub (fS.image _))).trans (Set.ncard_image_le fS))) ?_
    exact hc.symm.le
  · exact (congrArg (· * _) (bd_card G.frame _ _ rep had hlc)).trans c3
end
