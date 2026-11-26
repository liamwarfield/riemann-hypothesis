module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.FinTwO
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.RedOne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.TwistedCocycleApplyOne
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

section Abs

variable {K R M : Type} [Group K] [CommRing R] [Ring M] [Module R M] (ρ z : K → M) (χ : K → R)
  (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h) (c1 : χ 1 = 1) (cm : ∀ g h, χ (g * h) = χ g * χ h)
  (hz : ∀ g h, z (g * h) = z g + χ g • (ρ g * z h * ρ g⁻¹))

include h1 c1 hz in
private theorem twisted_cocycle_apply_one : z 1 = 0 := by
  have := hz 1 1
  rw [mul_one, inv_one, h1, c1, one_mul, mul_one, one_smul] at this
  exact left_eq_add.1 this

private theorem tw_inv {N : Type} [Monoid N] (ρ : K → N) (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h)
    {g : K} (hg : ρ g = 1) : ρ g⁻¹ = 1 := by
  have := hm g g⁻¹
  rw [mul_inv_cancel, h1, hg, one_mul] at this
  exact this.symm

include h1 hm hz in
private theorem tw_add {g : K} (hg : ρ g = 1) (hc : χ g = 1) (h : K) : z (g * h) = z g + z h := by
  rw [hz, tw_inv ρ h1 hm hg, hg, hc, one_mul, mul_one, one_smul]

include h1 hm c1 cm hz in
private theorem tw_U [TopologicalSpace K] (cρ : IsLocallyConstant ρ) (cχ : IsLocallyConstant χ)
    (cz : IsLocallyConstant z) :
    ∃ U : OpenNormalSubgroup K, ∀ g, g ∈ U ↔ ρ g = 1 ∧ χ g = 1 ∧ z g = 0 := by
  let S : Subgroup K :=
    { carrier := {g | ρ g = 1 ∧ χ g = 1 ∧ z g = 0}
      one_mem' := ⟨h1, c1, twisted_cocycle_apply_one ρ z χ h1 c1 hz⟩
      mul_mem' := fun {a b} ha hb => ⟨by rw [hm, ha.1, hb.1, one_mul], by rw [cm, ha.2.1, hb.2.1, one_mul],
        by rw [tw_add ρ z χ h1 hm hz ha.1 ha.2.1, ha.2.2, hb.2.2, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨tw_inv ρ h1 hm ha.1, tw_inv χ c1 cm ha.2.1, by
        have := tw_add ρ z χ h1 hm hz ha.1 ha.2.1 a⁻¹
        rw [mul_inv_cancel, twisted_cocycle_apply_one ρ z χ h1 c1 hz, ha.2.2, zero_add] at this
        exact this.symm⟩ }
  have hN : S.Normal := ⟨fun u hu g => ⟨by
      rw [hm, hm, hu.1, mul_one, ← hm, mul_inv_cancel, h1], by
      rw [cm, cm, hu.2.1, mul_one, ← cm, mul_inv_cancel, c1], by
      rw [mul_assoc, hz, tw_add ρ z χ h1 hm hz hu.1 hu.2.1, hu.2.2, zero_add, ← hz, mul_inv_cancel,
        twisted_cocycle_apply_one ρ z χ h1 c1 hz]⟩⟩
  have hO : IsOpen (S : Set K) := (cρ {1}).inter ((cχ {1}).inter (cz {0}))
  exact ⟨⟨⟨S, hO⟩, hN⟩, fun g => Iff.rfl⟩

end Abs

private theorem tw_lc {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have : ∀ᶠ g in nhds g0, ∀ i j, f g i j = f g0 i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g0
  filter_upwards [this] with g hg
  exact Matrix.ext hg

private theorem tw_core {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K P : Subgroup Γ) [P.Normal] (hK : IsOpen (K : Set Γ)) (hP : P ≤ K) :
    ∃ U : OpenNormalSubgroup Γ, P ≤ U.toSubgroup ∧ U.toSubgroup ≤ K := by
  haveI : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hK
  haveI : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hc : IsClosed (K.normalCore : Set Γ) := Subgroup.normalCore_isClosed K (K.isClosed_of_isOpen hK)
  have ho : IsOpen (K.normalCore : Set Γ) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hc
  exact ⟨{ toSubgroup := K.normalCore, isOpen' := ho, isNormal' := inferInstance },
    Subgroup.normal_le_normalCore.2 hP, K.normalCore_le⟩

private theorem phEq_one (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n)
    (m : ℕ) (hPL : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1)
    (z : G0.G₀ → Mm O n m) (cz : IsLocallyConstant z)
    (hz : ∀ g h : G0.G₀, z (g * h) = z g + epsm O G0 m g • (y.ρ0 m g * z h * y.ρ0 m g⁻¹))
    (j : Fin T.q) : ∀ᶠ N in atTop, y.ρ0 m ((T.h N).p₀ (T.ph N j)) = y.ρ0 m (T.sg j) ∧
      epsm O G0 m ((T.h N).p (T.ph N j)) = 1 ∧ z ((T.h N).p₀ (T.ph N j)) = z (T.sg j) := by
  obtain ⟨-, -, -, f4, f5⟩ := (omFacts l O).2 m
  have r1 : y.ρ0 m 1 = 1 := by
    show (Ideal.Quotient.mk (maximalIdeal O ^ m)).mapMatrix (mat y.ρ 1) = 1
    rw [map_one, map_one]
  have r2 : ∀ g h, y.ρ0 m (g * h) = y.ρ0 m g * y.ρ0 m h := fun g h => by
    show (Ideal.Quotient.mk (maximalIdeal O ^ m)).mapMatrix (mat y.ρ (g * h)) = _
    rw [map_mul, map_mul]
    rfl
  have c1 : IsLocallyConstant fun g : G0.G₀ => y.ρ0 m g := tw_lc _ fun a b => y.cont a b m
  have e1 : epsm O G0 m ((1 : G0.G₀) : G0.Γ) = 1 := by simp [epsm]
  have em : ∀ g h : G0.G₀, epsm O G0 m ((g * h : G0.G₀) : G0.Γ) = epsm O G0 m g * epsm O G0 m h := by
    intro g h
    simp [epsm]
  have c2 : IsLocallyConstant fun g : G0.G₀ => epsm O G0 m g := by
    have hc : Continuous fun g : G0.G₀ => ((G0.ε g : ℤ_[l]ˣ) : ℤ_[l]) :=
      Units.continuous_val.comp (G0.ε_cont.comp continuous_subtype_val)
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have ho : IsOpen {a : ℤ_[l] | PadicInt.toZModPow m a = 1} := by
      have : {a : ℤ_[l] | PadicInt.toZModPow m a = 1} = Metric.closedBall 1 ((l : ℝ) ^ (-(m : ℤ))) := by
        ext a
        rw [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
          ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
      rw [this]
      exact IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
    have h1 := (ho.preimage (hc.comp (continuous_mul_const g0⁻¹))).mem_nhds (x := g0) (by
      show PadicInt.toZModPow m ((G0.ε ((g0 * g0⁻¹ : G0.G₀) : G0.Γ) : ℤ_[l]ˣ) : ℤ_[l]) = 1
      rw [mul_inv_cancel, OneMemClass.coe_one, map_one, Units.val_one, map_one])
    filter_upwards [h1] with g hg
    have h2 : epsm O G0 m ((g * g0⁻¹ : G0.G₀) : G0.Γ) = 1 := f4 _ hg
    have h3 := em (g * g0⁻¹) g0
    rw [inv_mul_cancel_right, h2, one_mul] at h3
    exact h3
  obtain ⟨U, hU⟩ := tw_U (K := G0.G₀) (fun g => y.ρ0 m g) z (fun g => epsm O G0 m g) r1 r2 e1 em hz c1 c2 cz
  haveI := T.H.isNormal'
  obtain ⟨hn, -, hle, -⟩ := pl_props l G0.Γ T.H.toSubgroup T.H.toOpenSubgroup.isOpen
  have hsub : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → g ∈ U := fun g hg => by
    obtain ⟨a1, a2, a3⟩ := plKill l L G0 T O n y m G0 (Glob.Hom.refl G0) hPL z cz hz g hg
    exact (hU g).2 ⟨a2, a3, a1⟩
  obtain ⟨V, v1, v2⟩ := tw_core (U.toSubgroup.map G0.η.ker.subtype) (PL l T.H.toSubgroup)
    (G0.η_open.isOpenMap_subtype_val _ U.toOpenSubgroup.isOpen)
    fun a ha => ⟨⟨a, T.H_η a (hle ha)⟩, hsub _ ha, rfl⟩
  filter_upwards [T.ph_lim V j v1] with N hN
  obtain ⟨u, hu, e⟩ := v2 hN
  obtain ⟨u1, u2, u3⟩ := (hU u).1 hu
  have e' : (T.h N).p₀ (T.ph N j) = u * T.sg j := Subtype.ext (eq_mul_inv_iff_mul_eq.1 e).symm
  have hs : epsm O G0 m (T.sg j : G0.Γ) = 1 := by
    have : G0.ε (T.sg j) = 1 := T.sg_mem j
    simp [epsm, this]
  refine ⟨?_, ?_, ?_⟩
  · rw [e']
    exact (r2 _ _).trans (by rw [u1, one_mul])
  · show epsm O G0 m (((T.h N).p₀ (T.ph N j) : G0.G₀) : G0.Γ) = 1
    rw [e', em, u2, hs, one_mul]
  · rw [e', tw_add (K := G0.G₀) (fun g => y.ρ0 m g) z (fun g => epsm O G0 m g) r1 r2 hz u1 u2, u3, zero_add]

theorem UpperTheory.V.Th.phEqO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ), PhiCond G0.Γ l → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → ∀ᶠ N in atTop, ∀ j, y.ρ0 m ((T.h N).p₀ (T.ph N j)) = y.ρ0 m (T.sg j) ∧ epsm O G0 m ((T.h N).p (T.ph N j)) = 1 ∧ ∀ z ∈ Tw y m, z ((T.h N).p₀ (T.ph N j)) = z (T.sg j) := by
  intro l _ L G0 T O _ _ _ _ _ n y m hΦ hPL
  refine Filter.eventually_all.2 fun j => ?_
  have h0 := phEq_one l L G0 T O n y m hPL 0 (IsLocallyConstant.const 0) (fun g h => by simp) j
  have h1 : ∀ᶠ N in atTop, ∀ z ∈ Tw y m, z ((T.h N).p₀ (T.ph N j)) = z (T.sg j) := by
    refine (Filter.eventually_all_finite (finTwO l L G0 O n y m hΦ)).2 fun z hz => ?_
    exact (phEq_one l L G0 T O n y m hPL z hz.1 hz.2.1 j).mono fun N h => h.2.2
  filter_upwards [h0, h1] with N a b
  exact ⟨a.1, a.2.1, b⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OneLevelO
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.RedOneAlt
open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem cnt {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (Z B : AddSubgroup X) [Finite Z] (hB : B ≤ Z) (f : X →+ Y)
    (hf : ∀ b ∈ B, f b = 0) (S : Set Y) (hS : ∀ s ∈ S, ∃ z ∈ Z, f z = s) :
    S.Finite ∧ S.ncard * Nat.card B ≤ (Z : Set X).ncard := by
  let g : Z →+ Y := f.comp Z.subtype
  haveI : Finite g.range := Finite.of_surjective _ g.rangeRestrict_surjective
  have hsub : S ⊆ (g.range : Set Y) := fun s hs => by
    obtain ⟨z, hz, rfl⟩ := hS s hs
    exact ⟨⟨z, hz⟩, rfl⟩
  have hfin : (g.range : Set Y).Finite := Set.toFinite _
  refine ⟨hfin.subset hsub, ?_⟩
  have h1 : S.ncard ≤ Nat.card g.range := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub hfin
  have h2 : Nat.card B ≤ Nat.card g.ker :=
    Nat.card_le_card_of_injective (fun b : B => (⟨⟨b.1, hB b.2⟩, hf b.1 b.2⟩ : g.ker))
      fun a b e => Subtype.ext (congrArg (fun t : g.ker => t.1.1) e)
  have h3 : Nat.card Z = Nat.card g.range * Nat.card g.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv]
  rw [← Nat.card_coe_set_eq (Z : Set X), SetLike.coe_sort_coe, h3]
  exact Nat.mul_le_mul h1 h2

private theorem red_mul {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O) :
    red m (A * B) = red m A * red m B := Matrix.map_mul

private theorem red_one {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) :
    red m (1 : Matrix (Fin n) (Fin n) O) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem UpperTheory.V.Th.selTr :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (rep : Representation O G.Γ (Mm O n m)), IsAd0 h y m rep → LC rep → Finite (Zl rep) → (trFun h y m '' Sel h y m).Finite ∧ (trFun h y m '' Sel h y m).ncard * Nat.card (Bl rep) ≤ {z | z ∈ Zl rep ∧ (∀ v, z ∘ (G.η.ker.subtype.comp (G.φ v)) ∈ (Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v) ∧ ∀ u, ∀ g ∈ L.Ju u, z (G.φu u g) = 0}.ncard := by
  intro l _ L G G0 h O _ _ _ _ _ n y m rep hr hLC hF
  have hmul : ∀ g g', y.ρm h m (g * g') = y.ρm h m g * y.ρm h m g' := fun g g' => by
    simp only [Pt.ρm, map_mul, red_mul]
  have hone : y.ρm h m 1 = 1 := by simp only [Pt.ρm, map_one, red_one]
  have hrep : ∀ (g : G.G₀) Z, rep g Z = y.ρm h m g * Z * y.ρm h m g⁻¹ := fun g Z => (hr.1 g Z).trans (one_smul _ _)
  have hφ : ∀ v g, h.p₀ (G.φ v g) = G0.φ v g := fun v g => Subtype.ext (h.φ v g)
  have hρ : ∀ v g, y.ρm h m (G.φ v g) = y.ρ0 m (G0.φ v g) := fun v g => by rw [Pt.ρm, hφ]; rfl
  have hρ' : ∀ v g, y.ρm h m (G.φ v g)⁻¹ = y.ρ0 m (G0.φ v g)⁻¹ := fun v g => by rw [← map_inv, hρ, map_inv]
  let Z : AddSubgroup (G.Γ → Mm O n m) :=
    { carrier := {z | z ∈ Zl rep ∧ (∀ v, z ∘ (G.η.ker.subtype.comp (G.φ v)) ∈ (Bl (rep.comp (G.η.ker.subtype.comp (G.φ v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v) ∧ ∀ u, ∀ g ∈ L.Ju u, z (G.φu u g) = 0}
      add_mem' := by
        rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
        exact ⟨add_mem a1 b1, fun v => add_mem (a2 v) (b2 v), fun u g hg => by rw [Pi.add_apply, a3 u g hg, b3 u g hg, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun v => zero_mem _, fun _ _ _ => rfl⟩
      neg_mem' := by
        rintro a ⟨a1, a2, a3⟩
        exact ⟨neg_mem a1, fun v => neg_mem (a2 v), fun u g hg => by rw [Pi.neg_apply, a3 u g hg, neg_zero]⟩ }
  haveI : Finite Z := Finite.of_injective (fun z : Z => (⟨z.1, z.2.1⟩ : Zl rep))
    fun a b e => Subtype.ext (congrArg (fun t : Zl rep => t.1) e)
  let f : (G.Γ → Mm O n m) →+ (G.G₀ → Om O m) :=
    { toFun := fun z => trFun h y m fun g => z g
      map_zero' := funext fun g => by simp [trFun]
      map_add' := fun a b => funext fun g => by simp [trFun, Matrix.add_mul] }
  refine cnt Z (Bl rep).toAddSubgroup (fun b hb => ?_) f (fun b hb => ?_) _ ?_
  · obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hb
    obtain rfl : b = fun g => rep g Y - Y := funext hY
    refine ⟨⟨(hLC Y).comp (· - Y), fun g g' => by simp only [map_mul, Module.End.mul_apply, map_sub]; abel⟩,
      fun v => AddSubgroup.mem_sup_left ((mem_Bl _).2 ⟨Y, fun g => rfl⟩), fun u g hg => ?_⟩
    have e : y.ρ (h.p₀ (G.φu u g)) = 1 := y.ine u _ ⟨g, hg, Subtype.ext (h.φu u g).symm⟩
    have e1 : y.ρm h m (G.φu u g) = 1 := by rw [Pt.ρm, mat, MonoidHom.comp_apply, e, map_one, red_one]
    have e2 : y.ρm h m (G.φu u g)⁻¹ = 1 := by
      rw [Pt.ρm, map_inv, mat, MonoidHom.comp_apply, map_inv, e, inv_one, map_one, red_one]
    show rep (G.φu u g : G.G₀) Y - Y = 0
    rw [hrep, e1, e2, one_mul, mul_one, sub_self]
  · obtain ⟨Y, hY⟩ := (mem_Bl rep).1 hb
    funext g
    show (b g * y.ρm h m g).trace = 0
    rw [hY, hrep, sub_mul, mul_assoc _ _ (y.ρm h m g), ← hmul, inv_mul_cancel, hone, mul_one, Matrix.trace_sub,
      Matrix.trace_mul_comm, sub_self]
  · rintro _ ⟨z, ⟨z1, z2, z3, z4, z5⟩, rfl⟩
    have hP : IsUnit (red m (y.P : Matrix (Fin n) (Fin n) O)) :=
      ⟨⟨red m (y.P : Matrix (Fin n) (Fin n) O), red m ((y.P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O), by rw [← red_mul, Units.mul_inv, red_one],
        by rw [← red_mul, Units.inv_mul, red_one]⟩, rfl⟩
    obtain ⟨z', h1, -, h3⟩ := (polP l G.frame O (Om O m) n _ _ _ rep hP hr).1 z z1
      (fun g g' => by rw [one_smul]; exact z2 g g') (fun g => by rw [one_smul]; exact z3 g)
    refine ⟨z', ⟨h1, fun v => ?_, fun u g hg => (h3 _).trans (z4 u _ ⟨g, hg, rfl⟩)⟩, funext fun g => by
      show (z' g * _).trace = (z g * _).trace
      rw [h3]⟩
    obtain ⟨Y, hY⟩ := z5 v
    have hc : Continuous (G.η.ker.subtype.comp (G.φ v)) := continuous_subtype_val.comp (G.φ_cont v)
    have e : z' ∘ (G.η.ker.subtype.comp (G.φ v)) = (fun g => rep (G.φ v g : G.G₀) Y - Y) +
        fun g => z' (G.φ v g : G.G₀) - (rep (G.φ v g : G.G₀) Y - Y) := funext fun g => by simp
    rw [e]
    refine AddSubgroup.add_mem_sup ((mem_Bl _).2 ⟨Y, fun g => rfl⟩) ⟨?_, fun g g' => ?_, fun g => ?_⟩
    · exact (h1.1.comp_continuous hc).sub (((hLC Y).comp_continuous hc).comp (· - Y))
    · rw [← hρ, ← hρ', ← hrep]
      beta_reduce
      rw [map_mul, Subgroup.coe_mul, h1.2, map_mul, Module.End.mul_apply, map_sub, map_sub]
      abel
    · have := (hY g).1
      rw [dY, ← hrep] at this
      simp only [h3]
      exact this
end

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem natL (ZL B' M V U J A S' PV PU PJ K a b c1 c2 e f Sel B ci : ℕ) (hB : 0 < B') (hM : 0 < M)
    (h1 : ZL * B' * M ^ (V + (U + J)) * A ≤ M * S' * (PV * (PU * PJ))) (h2 : S' ≤ B' * K ^ c2)
    (h3 : PV * K ^ a ≤ M ^ V * K ^ e) (h4 : PU ≤ M ^ U) (h5 : PJ ≤ M ^ J * K ^ f) (h6 : K ^ b ≤ A)
    (h7 : Sel * B ≤ ZL) (h8 : B * ci = M) (h9 : ci ≤ K ^ c1) :
    Sel * K ^ (a + b) ≤ K ^ (c1 + c2 + e + f) := by
  have k1 : ZL * K ^ (a + b) * (B' * M ^ (V + (U + J))) ≤ M * K ^ (c2 + e + f) * (B' * M ^ (V + (U + J))) := by
    calc ZL * K ^ (a + b) * (B' * M ^ (V + (U + J))) = ZL * B' * M ^ (V + (U + J)) * K ^ b * K ^ a := by ring
      _ ≤ ZL * B' * M ^ (V + (U + J)) * A * K ^ a := by gcongr
      _ ≤ M * S' * (PV * (PU * PJ)) * K ^ a := by gcongr
      _ = M * S' * (PV * K ^ a) * PU * PJ := by ring
      _ ≤ M * (B' * K ^ c2) * (M ^ V * K ^ e) * M ^ U * (M ^ J * K ^ f) := by gcongr
      _ = M * K ^ (c2 + e + f) * (B' * M ^ (V + (U + J))) := by ring
  have k2 : ZL * K ^ (a + b) ≤ M * K ^ (c2 + e + f) := Nat.le_of_mul_le_mul_right k1 (by positivity)
  have hB0 : 0 < B := Nat.pos_of_mul_pos_right (h8 ▸ hM : 0 < B * ci)
  refine Nat.le_of_mul_le_mul_right (c := B) ?_ hB0
  calc Sel * K ^ (a + b) * B = Sel * B * K ^ (a + b) := by ring
    _ ≤ ZL * K ^ (a + b) := by gcongr
    _ ≤ B * ci * K ^ (c2 + e + f) := by rw [h8]; exact k2
    _ ≤ B * K ^ c1 * K ^ (c2 + e + f) := by gcongr
    _ = K ^ (c1 + c2 + e + f) * B := by ring

private theorem block_le₂ {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (h : LC ρ) : (Bl ρ).toAddSubgroup ≤ (Zl ρ).toAddSubgroup := by
  intro z hz
  obtain ⟨m, hm⟩ := (mem_Bl ρ).1 hz
  have : z = fun g => ρ g m - m := funext hm
  subst this
  refine (mem_Zl ρ).2 ⟨(h m).comp (fun y => y - m), fun g g' => ?_⟩
  simp only [map_mul, Module.End.mul_apply, map_sub]
  abel

private theorem lc_comp {R Γ D M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [Group D] [TopologicalSpace D]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (h : LC ρ) (φ : D →* Γ) (hφ : Continuous φ) :
    LC (ρ.comp φ : Representation R D M) := fun m => (h m).comp_continuous hφ

private theorem zl_comp {R Γ D M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [Group D] [TopologicalSpace D]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (φ : D →* Γ) (hφ : Continuous φ) {z : Γ → M}
    (hz : z ∈ Zl ρ) : z ∘ φ ∈ Zl (ρ.comp φ : Representation R D M) :=
  ⟨hz.1.comp_continuous hφ, fun g g' => by simp [hz.2]⟩

theorem UpperTheory.V.Th.oneLevelO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ) (q d : ℕ) (a : ArData G q d) (rep rep' : Representation O G.Γ (Mm O n m)) (e : L.Vl → ℕ) (f : Option (Fin q) → ℕ) (c₁ c₂ : ℕ), l ≠ 2 → Cnts a → IsAd0 h y m rep → IsAd1 h y m rep' → (∀ v, Finite (Zbor y m v) ∧ Nat.card (Zbor y m v) ≤ Nat.card (ResidueField O) ^ e v) → (∀ j, Nat.card (Representation.invariants (rep'.comp (a.ι (.inr (.inr j))) : Representation O (a.D (.inr (.inr j))) _)) ≤ Nat.card (ResidueField O) ^ f j) → Nat.card rep.invariants ≤ Nat.card (ResidueField O) ^ c₁ → (Finite (Zl rep') → {z | z ∈ Zl rep' ∧ ∀ j : Fin q, z ∘ a.ι (.inr (.inr (some j))) ∈ Bl (rep'.comp (a.ι (.inr (.inr (some j)))) : Representation O (a.D (.inr (.inr (some j)))) _)}.ncard ≤ Nat.card (Bl rep') * Nat.card (ResidueField O) ^ c₂) → (trFun h y m '' Sel h y m).Finite ∧ (trFun h y m '' Sel h y m).ncard * Nat.card (ResidueField O) ^ (m * (n + n.choose 2) * Fintype.card L.Vl + m * n.choose 2 * d) ≤ Nat.card (ResidueField O) ^ (c₁ + c₂ + ∑ v, e v + ∑ j, f j) := by
  intro l _ L G G0 h O _ _ _ _ _ n y m q d a rep rep' e f c₁ c₂ hl hC hrep hrep' hZb hf hc1 hc2
  classical
  obtain ⟨h2, hOm⟩ := omFacts l O
  obtain ⟨hfD, -, hlD, -⟩ := hOm m
  haveI := hfD
  haveI : Finite (Mm O n m) := inferInstanceAs (Finite (Fin n → Fin n → Om O m))
  obtain ⟨k, b, hk, hb⟩ := pairP l L G G0 h O n y m a.c_ε
  have hb := hb rep rep' hrep hrep'
  have hLC : LC rep := (adExP l L G G0 h O n y m).2.2 rep (Or.inl hrep)
  have hι : ∀ w, Continuous (a.ι w) := by
    rintro (v | u | j)
    · exact continuous_subtype_val.comp (G.φ_cont v)
    · exact continuous_subtype_val.comp (G.φu_cont u)
    · exact continuous_subtype_val.comp (a.φq_cont j)
  have hLCw : ∀ w, LC (rep.comp (a.ι w) : Representation O (a.D w) _) := fun w => lc_comp rep hLC _ (hι w)
  have hpu : ∀ u g, h.p₀ (G.φu u g) = G0.φu u g := fun u g => Subtype.ext (h.φu u g)
  have hρ : ∀ u, ∀ g ∈ L.Ju u, y.ρm h m (G.φu u g) = 1 := fun u g hg => by
    have h1 : y.ρ (G0.φu u g) = 1 := y.ine u _ ⟨g, hg, rfl⟩
    have h3 : mat y.ρ (G0.φu u g) = 1 := congrArg Units.val h1
    rw [Pt.ρm, hpu, h3, red]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hu : ∀ u, ∀ g ∈ L.Ju u, rep (G.φu u g : G.Γ) = 1 := fun u g hg => by
    refine LinearMap.ext fun Z => ?_
    have := hrep.1 (G.φu u g) Z
    have e1 := hρ u g⁻¹ (inv_mem hg)
    rw [map_inv] at e1
    rw [hρ u g hg, one_smul, one_mul] at this
    exact this.trans ((congrArg (Z * ·) e1).trans (mul_one Z))
  let 𝓛 : ∀ w, AddSubgroup (a.D w → Mm O n m) := fun w => match w with
    | .inl v => (Bl (rep.comp (a.ι (.inl v)) : Representation O (L.Gv v) _)).toAddSubgroup ⊔ Zbor y m v
    | .inr (.inl u) => (Zl (rep.comp (a.ι (.inr (.inl u))) : Representation O (L.Gu u) _)).toAddSubgroup ⊓
        AddSubgroup.pi (L.Ju u : Set (L.Gu u)) (fun _ => ⊥)
    | .inr (.inr j) => (Zl (rep.comp (a.ι (.inr (.inr j))) : Representation O (a.Dq j) _)).toAddSubgroup
  have hloc := fun v => locSup l L G G0 h O n y m rep v hrep hLC (hZb v).1
  have h𝓛 : ∀ w, (Bl (rep.comp (a.ι w) : Representation O (a.D w) _)).toAddSubgroup ≤ 𝓛 w ∧
      𝓛 w ≤ (Zl (rep.comp (a.ι w) : Representation O (a.D w) _)).toAddSubgroup := by
    rintro (v | u | j)
    · exact ⟨le_sup_left, (hloc v).1⟩
    · refine ⟨le_inf (block_le₂ _ (hLCw _)) fun z hz g hg => ?_, inf_le_left⟩
      obtain ⟨Y, hy⟩ := (mem_Bl _).1 hz
      have e1 : rep (G.φu u g : G.Γ) Y - Y = 0 := by rw [hu u g hg]; simp
      exact AddSubgroup.mem_bot.2 ((hy g).trans e1)
    · exact ⟨block_le₂ _ (hLCw _), le_rfl⟩
  obtain ⟨hF, hF', hgw⟩ := hC.gw k hk O _ _ rep rep' b hLC hb 𝓛 h𝓛
  obtain ⟨hS1, hS2⟩ := selTr l L G G0 h O n y m rep hrep hLC hF
  have hS3 := (cCount O G.Γ (Mm O n m) rep G.c G.c_sq (h2 hl)).2.1
  refine ⟨hS1, ?_⟩
  have hFs : (Zl rep : Set (G.Γ → Mm O n m)).Finite := Set.toFinite _
  have hFs' : (Zl rep' : Set (G.Γ → Mm O n m)).Finite := Set.toFinite _
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.card_sum, Fintype.card_sum] at hgw
  haveI : Finite (Bl rep') := Finite.of_surjective _ (LinearMap.surjective_rangeRestrict _)
  refine natL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Nat.card_pos Nat.card_pos hgw ?_ ?_ ?_ ?_ ?_
    (hS2.trans ?_) hS3 hc1
  · refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (hc2 hF')
    exact fun y hy => ⟨hy.1, fun j => hy.2 _ rfl⟩
  · rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_const, ← Finset.prod_mul_distrib,
      ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun v _ => ?_
    exact le_trans (hloc v).2.2 (Nat.mul_le_mul_left _ (hZb v).2)
  · rw [← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_le_prod' fun u _ => ?_
    have := (hC.unr u m O _ (rep.comp (a.ι (.inr (.inl u)))) (hLCw _) (fun Y => Matrix.ext fun i j => hlD (Y i j)) (hu u)).2
    rw [← Nat.card_coe_set_eq] at this
    exact this
  · rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun j _ => ?_
    have := (hC.locQ j k hk O _ _ (rep.comp (a.ι (.inr (.inr j)))) (rep'.comp (a.ι (.inr (.inr j)))) b (hLCw _)
      ⟨hb.left, hb.right, fun g y z => hb.equiv _ y z⟩).2
    rw [add_zero, pow_one] at this
    exact this.le.trans (Nat.mul_le_mul_left _ (hf j))
  · rw [pow_mul]
    conv_lhs => rw [← Fintype.card_fin d, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun i _ =>
      pow_choose_two_le_card_fixed_ad0_of_odd_involution l L G G0 h O n y m rep _ hl hrep (a.cw_sq i) (a.cw_η i)
  · refine Set.ncard_le_ncard ?_ (hFs.subset fun y hy => hy.1)
    rintro z ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    rintro (v | u | j)
    · exact h2 v
    · exact ⟨zl_comp rep _ (hι _) h1, fun g hg => h3 u g hg⟩
    · exact zl_comp rep _ (hι _) h1
end
