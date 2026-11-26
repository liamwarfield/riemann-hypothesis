module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfLe
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClsInt

section Count
variable {H Γ : Type} [Group H] [Group Γ] (ι : Γ →* H) (J J' : Subgroup H)

def toLev (a : H) : Bridge.stab ι J a →* J where
  toFun s := ⟨a⁻¹ * ι s * a, (Bridge.mem_stab _).1 s.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp [mul_assoc])

theorem sum_inv_card_stab (hle : J' ≤ J) (hN : J'.relIndex J ≠ 0) {Cl : Type} [Fintype Cl] (y : Cl → H)
    (hy : Bridge.IsReps ι J' y) (a : H) [Finite (Bridge.stab ι J a)] :
    ∑ k with (∃ γ, ∃ u ∈ J, y k = ι γ * a * u),
      ((J'.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab ι J' (y k)) : ℕ) : ℂ)⁻¹ =
      ((Nat.card (Bridge.stab ι J a) : ℕ) : ℂ)⁻¹ := by
  let X := J ⧸ J'.subgroupOf J
  have hX : Nat.card X = J'.relIndex J := rfl
  haveI : Finite X := Nat.finite_of_card_ne_zero (hX ▸ hN)
  letI : Fintype X := Fintype.ofFinite X
  letI : MulAction (Bridge.stab ι J a) X := MulAction.compHom X (toLev ι J a)
  have hsm : ∀ (s : Bridge.stab ι J a) (u : J), s • (u : X) = ((toLev ι J a s * u : J) : X) := fun _ _ => rfl
  choose idx hidx hu using fun h => (hy h)
  have hi : ∀ h k, idx h = k ↔ ∃ γ, ∃ w ∈ J', h = ι γ * y k * w := by
    intro h k
    constructor
    · rintro rfl
      obtain ⟨γ, w, e⟩ := hidx h
      exact ⟨γ, w, w.2, e⟩
    · rintro ⟨γ, w, hw, e⟩
      exact (hu h k ⟨γ, ⟨w, hw⟩, e⟩).symm
  let f : X → Cl := fun x => idx (a * (x.out : J))
  have hq : ∀ u v : J, (u : X) = (v : X) ↔ (u : H)⁻¹ * v ∈ J' := fun u v => QuotientGroup.eq
  have hf : ∀ (u : J) k, f (u : X) = k ↔ ∃ γ, ∃ w ∈ J', a * u = ι γ * y k * w := by
    intro u k
    have h0 : ((Quotient.out (u : X) : J) : H)⁻¹ * u ∈ J' := (hq _ _).1 (Quotient.out_eq _)
    change idx _ = k ↔ _
    rw [hi]
    constructor
    · rintro ⟨γ, w, hw, e⟩
      exact ⟨γ, _, J'.mul_mem hw h0, by rw [← mul_assoc, ← e]; group⟩
    · rintro ⟨γ, w, hw, e⟩
      exact ⟨γ, _, J'.mul_mem hw (J'.inv_mem h0), by rw [← mul_assoc, ← e]; group⟩
  have hS : ((Nat.card (Bridge.stab ι J a) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hN' : ((J'.relIndex J : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hcount : J'.relIndex J = ∑ k with (∃ γ, ∃ u ∈ J, y k = ι γ * a * u),
      (Finset.univ.filter fun x => f x = k).card := by
    rw [← hX, Nat.card_eq_fintype_card, ← Finset.card_univ]
    refine Finset.card_eq_sum_card_fiberwise fun x _ => ?_
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨γ, w, hw, e⟩ := (hf u _).1 rfl
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    refine ⟨γ⁻¹, u * w⁻¹, J.mul_mem u.2 (J.inv_mem (hle hw)), ?_⟩
    rw [map_inv, mul_assoc, ← mul_assoc a, e]; group
  have key : ∀ k, (∃ γ, ∃ u ∈ J, y k = ι γ * a * u) →
      (Finset.univ.filter fun x => f x = k).card * Nat.card (Bridge.stab ι J' (y k)) =
        Nat.card (Bridge.stab ι J a) := by
    rintro k ⟨γ₀, u₀, hu₀, e₀⟩
    let x₀ : X := ((⟨u₀, hu₀⟩ : J) : X)
    have h1 : MulAction.orbit (Bridge.stab ι J a) x₀ = ↑(Finset.univ.filter fun x => f x = k) := by
      ext x
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [hf, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨s, hs⟩
        rw [hsm, hq] at hs
        refine ⟨s * γ₀⁻¹, _, hs, ?_⟩
        change _ = _ * ((a⁻¹ * ι s * a * u₀)⁻¹ * u)
        rw [e₀, map_mul, map_inv]; group
      · rintro ⟨γ, w, hw, e⟩
        have e1 : a⁻¹ * ι (γ * γ₀) * a = u * w⁻¹ * u₀⁻¹ := by
          have : (u : H) = a⁻¹ * (ι γ * y k * w) := by rw [← e]; group
          rw [this, e₀, map_mul]; group
        refine ⟨⟨γ * γ₀, (Bridge.mem_stab _).2 ?_⟩, ?_⟩
        · rw [e1]; exact J.mul_mem (J.mul_mem u.2 (J.inv_mem (hle hw))) (J.inv_mem hu₀)
        · rw [hsm, hq]
          change (a⁻¹ * ι (γ * γ₀) * a * u₀)⁻¹ * u ∈ J'
          rw [e1, show ((u : H) * w⁻¹ * u₀⁻¹ * u₀)⁻¹ * u = w by group]
          exact hw
    have h2 : ∀ s : Bridge.stab ι J a, s ∈ MulAction.stabilizer (Bridge.stab ι J a) x₀ ↔
        γ₀ * s * γ₀⁻¹ ∈ Bridge.stab ι J' (y k) := by
      intro s
      rw [MulAction.mem_stabilizer_iff, hsm, eq_comm, hq, Bridge.mem_stab]
      change u₀⁻¹ * (a⁻¹ * ι s * a * u₀) ∈ J' ↔ _
      rw [e₀, map_mul, map_mul, map_inv, show (ι γ₀ * a * u₀)⁻¹ * (ι γ₀ * ι s * (ι γ₀)⁻¹) * (ι γ₀ * a * u₀) =
        u₀⁻¹ * (a⁻¹ * ι s * a * u₀) by group]
    have h3 : Nat.card (MulAction.stabilizer (Bridge.stab ι J a) x₀) = Nat.card (Bridge.stab ι J' (y k)) := by
      refine Nat.card_eq_of_bijective (fun s => ⟨γ₀ * s.1 * γ₀⁻¹, (h2 _).1 s.2⟩) ⟨fun s t e => ?_, fun t => ?_⟩
      · have := congrArg Subtype.val e
        simp only [mul_left_inj, mul_right_inj] at this
        exact Subtype.ext (Subtype.ext this)
      · have ht := (Bridge.mem_stab _).1 t.2
        have hm : γ₀⁻¹ * t * γ₀ ∈ Bridge.stab ι J a := by
          rw [Bridge.mem_stab, map_mul, map_mul, map_inv,
            show a⁻¹ * ((ι γ₀)⁻¹ * ι t * ι γ₀) * a = u₀ * ((ι γ₀ * a * u₀)⁻¹ * ι t * (ι γ₀ * a * u₀)) * u₀⁻¹ by group,
            ← e₀]
          exact J.mul_mem (J.mul_mem hu₀ (hle ht)) (J.inv_mem hu₀)
        have e : γ₀ * (γ₀⁻¹ * t * γ₀) * γ₀⁻¹ = t := by group
        exact ⟨⟨⟨_, hm⟩, (h2 _).2 (by rw [e]; exact t.2)⟩, Subtype.ext e⟩
    rw [← h3, ← Set.ncard_coe_finset, ← h1, ← Nat.card_coe_set_eq, ← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup _ x₀)
  have h4 : ∀ k ∈ Finset.univ.filter (fun k => ∃ γ, ∃ u ∈ J, y k = ι γ * a * u),
      ((J'.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab ι J' (y k)) : ℕ) : ℂ)⁻¹ =
      ((J'.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab ι J a) : ℕ) : ℂ)⁻¹ *
        (((Finset.univ.filter fun x => f x = k).card : ℕ) : ℂ) := by
    intro k hk
    have h5 := key k (Finset.mem_filter.1 hk).2
    have h6 := hS
    rw [← h5] at h6 ⊢
    push_cast at h6 ⊢
    have h7 := left_ne_zero_of_mul h6
    have h8 := right_ne_zero_of_mul h6
    field_simp
  rw [Finset.sum_congr rfl h4, ← Finset.mul_sum, ← Nat.cast_sum, ← hcount]
  field_simp

end Count

theorem integral_eq_sum_of_le {G H : Type} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ]
    (π : G →* H) (hπ : Function.Surjective π) (J J' : Subgroup H) (𝓖 : Set G) (h𝓖 : IsFundamentalDomain Γ 𝓖 ν)
    (ho : IsOpen (J.comap π : Set G)) (h1 : ν (J.comap π) = 1) (hle : J' ≤ J) (hN : J'.relIndex J ≠ 0)
    (Cl : Type) [Fintype Cl] (h : Cl → G) (hy : Bridge.IsReps (π.comp Γ.subtype) J' fun k => π (h k))
    (Φ : G → ℂ) (hl : ∀ γ ∈ Γ, ∀ x, Φ (γ * x) = Φ x) (hr : ∀ u, π u ∈ J → ∀ x, Φ (x * u) = Φ x) :
    ∫ x in 𝓖, Φ x ∂ν = ∑ k, ((J'.relIndex J : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (π.comp Γ.subtype) J' (π (h k))) : ℕ) : ℂ)⁻¹ * Φ (h k) := by
  set ι := π.comp Γ.subtype with hι
  choose σ hσ using hπ
  have hΦ : ∀ x, Φ (σ (π x)) = Φ x := fun x => by
    rw [← hr ((σ (π x))⁻¹ * x) (by rw [map_mul, map_inv, hσ, inv_mul_cancel]; exact J.one_mem),
      mul_inv_cancel_left]
  have hΦ' : ∀ (γ : Γ) z (k : J), Φ (σ (ι γ * z * k)) = Φ (σ z) := fun γ z k => by
    have : ι γ * z * k = π (γ * σ z * σ k) := by rw [map_mul, map_mul, hσ, hσ]; rfl
    rw [this, hΦ, hr _ (by rw [hσ]; exact k.2), hl _ γ.2]
  have hfin : ∀ z, Finite (Bridge.stab ι J z) := fun z => by
    have := GlobalTheory.InnerClassSum.finite_stab_of_measure ν Γ (J.comap π) h𝓖 (h1 ▸ one_ne_zero)
      (h1 ▸ ENNReal.one_ne_top) (σ z)
    refine Set.Finite.subset this fun γ hγ => ?_
    rw [Set.mem_setOf_eq, Subgroup.mem_comap, map_mul, map_mul, map_inv, hσ]
    exact (Bridge.mem_stab _).1 hγ
  let r : Setoid Cl :=
    { r := fun k l => ∃ γ, ∃ u ∈ J, π (h k) = ι γ * π (h l) * u
      iseqv :=
        ⟨fun k => ⟨1, 1, J.one_mem, by simp⟩,
          fun ⟨γ, u, hu, e⟩ => ⟨γ⁻¹, u⁻¹, J.inv_mem hu, by rw [e, map_inv]; group⟩,
          fun ⟨γ, u, hu, e⟩ ⟨δ, v, hv, e'⟩ => ⟨γ * δ, v * u, J.mul_mem hv hu, by rw [e, e', map_mul]; group⟩⟩ }
  have hq : ∀ k (i : Quotient r), Quotient.mk r k = i ↔ ∃ γ, ∃ u ∈ J, π (h k) = ι γ * π (h i.out) * u :=
    fun k i => Quotient.mk_eq_iff_out
  have hreps : Bridge.IsReps ι J fun i : Quotient r => π (h i.out) := by
    intro z
    obtain ⟨k, ⟨γ, w, e⟩, -⟩ := hy z
    refine ⟨Quotient.mk r k, ?_, ?_⟩
    · obtain ⟨δ, u, hu, e'⟩ := (hq k _).1 rfl
      exact ⟨γ * δ, ⟨u * w, J.mul_mem hu (hle w.2)⟩, by simp only [] at e ⊢; rw [e, e', map_mul]; group⟩
    · rintro i ⟨δ, u, e'⟩
      refine ((hq k i).2 ⟨γ⁻¹ * δ, u * (w : H)⁻¹, J.mul_mem u.2 (J.inv_mem (hle w.2)), ?_⟩).symm
      simp only [] at e e'
      have : π (h k) = (ι γ)⁻¹ * z * (w : H)⁻¹ := by rw [e]; group
      rw [this, e', map_mul, map_inv]; group
  have key := GlobalTheory.ClassUnfold.integral_eq_sum_of_surjective ν Γ π (fun z => ⟨σ z, hσ z⟩) J 𝓖 h𝓖 ho h1
    (Quotient r) _ hreps (fun _ => hfin _) (fun z => Φ (σ z)) hΦ'
  simp only [hΦ] at key
  rw [key, ← Finset.sum_fiberwise Finset.univ (Quotient.mk r)]
  refine Finset.sum_congr rfl fun i _ => ?_
  haveI := hfin (π (h i.out))
  rw [← sum_inv_card_stab ι J J' hle hN _ hy, Finset.sum_mul]
  refine Finset.sum_congr (Finset.filter_congr fun k _ => (hq k i).symm) fun k hk => ?_
  obtain ⟨γ, u, hu, e⟩ := (hq k i).1 (Finset.mem_filter.1 hk).2
  rw [← hΦ (h k), e, hΦ' γ _ ⟨u, hu⟩, hΦ]

theorem integral_eq_classSum_of_le : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), V.IsPosDef → V.SigOK → IsMeasDef V (Formalism.L2.DIV.lev D.sp.cm V.gram β L) ν 𝓕 → (∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.flag1L L)) → ∀ (J' : Subgroup (Bridge.Gf V)) (Cl : Type) [Fintype Cl] (h : Cl → GA D V), J' ≤ (levEnv V β L).J → J'.relIndex (levEnv V β L).J ≠ 0 → Bridge.IsReps (Bridge.ratF V) J' (fun k => fin V (h k)) → (∀ k, h k ∈ GfC V) → ∀ Φ : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ x, Φ (γ * x) = Φ x) → (∀ u : GA D V, fin V u ∈ (levEnv V β L).J → ∀ x, Φ (x * u) = Φ x) → ∫ x in 𝓕, Φ x ∂ν = ∑ k, ((J'.relIndex (levEnv V β L).J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab (Bridge.ratF V) J' (fin V (h k))) : ℕ) : ℂ)⁻¹ * Φ (h k) := by
  intro D V β L ν 𝓕 _ _ hν hL J' Cl _ h hle hN hy _ Φ hl hr
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  haveI := hν.1.1
  have hK : (levEnv V β L).J.comap (finHom V).rangeRestrict =
      (Formalism.L2.DIV.lev D.sp.cm V.gram β L).comap (Lev.finE V) := by
    ext g
    exact (hL (Lev.finE V g)).symm
  refine integral_eq_sum_of_le ν (GQ V) (finHom V).rangeRestrict (finHom V).rangeRestrict_surjective
    (levEnv V β L).J J' 𝓕 hν.2 ?_ ?_ hle hN Cl h hy Φ hl hr
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_level V β L] with κ hκ
    exact hκ.1
  · rw [hK]
    exact GlobalTheory.Mass.Levels.measure_comap_finE hν.1

end GlobalTheory.ClsInt
end

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftUnfold

theorem exists_fin_mul_real {D : D7} (V : HSp D) (u : GA D V) : ∃ k ∈ GfC V, ∃ a ∈ GinfC V, u = k * a ∧ fin V k = fin V u := by
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 (finHom V u)
  have hk : k ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
    (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 u.2).2⟩
  let k' : GA D V := ⟨k, hk⟩
  have e : finHom V k' = finHom V u := k2
  refine ⟨k', k1, k'⁻¹ * u, ?_, (mul_inv_cancel_left _ _).symm, Subtype.ext e⟩
  show finHom V (k'⁻¹ * u) = 1
  rw [map_mul, map_inv, e, inv_mul_cancel]

theorem integrand_right {H G' Gf W X : Type} [Group H] [Group G'] [Group Gf] [AddCommGroup W] [Module ℂ W]
    (om : H × G' →* Module.End ℂ (X → ℂ)) (ρ : H →* Module.End ℂ W) (p : H →* Gf) (L : W →ₗ[ℂ] (X → ℂ)) (f : Gf → W)
    (u k a : H) (hu : u = k * a) (c : ℂˣ) (hk : ρ k⁻¹ = 1) (ha : p a = 1) (hf : ∀ z, f (z * p k) = (c : ℂ) • f z)
    (hLk : ∀ w, om (k, 1) (L w) = (c : ℂ)⁻¹ • L w) (hLa : ∀ w, om (a, 1) (L w) = L (ρ a w)) (x : H) (g : G') :
    om (x * u, g) (L (ρ (x * u)⁻¹ (f (p (x * u))))) = om (x, g) (L (ρ x⁻¹ (f (p x)))) := by
  subst hu
  have e1 : (x * (k * a), g) = (x, g) * (k, (1 : G')) * (a, (1 : G')) := by simp [mul_assoc]
  have e2 : ρ a * ρ (x * (k * a))⁻¹ = ρ x⁻¹ := by
    rw [← map_mul, show a * (x * (k * a))⁻¹ = k⁻¹ * x⁻¹ by group, map_mul, hk, one_mul]
  rw [e1, map_mul om, map_mul om, Module.End.mul_apply, Module.End.mul_apply, hLa, ← Module.End.mul_apply (ρ a), e2, hLk,
    map_mul p, map_mul p, ha, mul_one, hf, map_smul (ρ x⁻¹), map_smul L, smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul]

theorem form_right {H Γ W : Type} [Group H] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) {J : Subgroup H} {χ : J →* ℂˣ} {f : H → W} (hf : f ∈ Bridge.AdForms ι ρ J χ) (k : J) (z : H) :
    f (z * k) = (χ k : ℂ) • f z := by
  have := hf 1 z k
  rwa [map_one, map_one, one_mul] at this

theorem integral_theta {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (hL : ∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β (Lev.flag1L L))
    {f : Bridge.Gf S → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ)
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ (levEnv S β L).J, ∀ w,
      om (k, 1) (Λ w) = (((levEnv S β L).χ ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : IsMeasDef S (Formalism.L2.DIV.lev D.sp.cm S.gram β L) ν 𝓕)
    (J' : Subgroup (Bridge.Gf S)) (Cl : Type) [Fintype Cl] (h : Cl → GA D S) (hle : J' ≤ (levEnv S β L).J)
    (hN : J'.relIndex (levEnv S β L).J ≠ 0) (hy : Bridge.IsReps (Bridge.ratF S) J' (fun k => fin S (h k)))
    (hh : ∀ k, h k ∈ GfC S) (g : GA D T) :
    ∫ x in 𝓕, thetaKO om x g (Λ (c.ext f x)) ∂ν = ∑ k, ((J'.relIndex (levEnv S β L).J : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (Bridge.ratF S) J' (fin S (h k))) : ℕ) : ℂ)⁻¹ * thetaKO om (h k) g (Λ (f (fin S (h k)))) := by
  rw [GlobalTheory.ClsInt.integral_eq_classSum_of_le D S β L ν 𝓕 hp hs hν hL J' Cl h hle hN hy hh
    (fun x => thetaKO om x g (Λ (c.ext f x))) ?_ ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [ext_fin c hc f (hh k)]
  · intro γ hγ x
    have e : (γ * x, g) = ((γ, 1) : GA D S × GA D T) * (x, g) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ, e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hΛ _))
  · intro u hu x
    refine (exists_fin_mul_real S u).elim fun k hk0 => hk0.2.elim fun a ha0 => ?_
    have hk := hk0.1
    have ha := ha0.1
    have e := ha0.2.2
    have hk' : fin S k ∈ (levEnv S β L).J := by rw [e]; exact hu
    have h1 : c.ρ k⁻¹ = 1 := hc.1 _ (inv_mem hk)
    have h2 : (finHom S).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    have h3 := form_right (Bridge.ratF S) c.coef.ρ hf ⟨fin S k, hk'⟩
    have h4 := integrand_right om c.ρ (finHom S).rangeRestrict Λ f u k a ha0.2.1 ((levEnv S β L).χ ⟨fin S k, hk'⟩)
      h1 h2 h3 (hΛk k hk hk') (hΛa a ha) x g
    exact congrFun h4 0


end GlobalTheory.LiftUnfold
