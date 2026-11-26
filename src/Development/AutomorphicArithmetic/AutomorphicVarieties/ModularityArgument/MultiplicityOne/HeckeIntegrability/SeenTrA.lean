module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.LevelTrAAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UnitHecke
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.HeckeIntegrability.SharedDedup_Tr_core

@[expose] public section

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.LFun GlobalTheory.PRep

private theorem hint_fst {G P : Type} [Group G] [Group P] [Subsingleton P] (K N : Subgroup G) (K' : Subgroup P)
    (u : G × P → ℂ) (hNK : N ≤ K) (hu : ∀ k ∈ N, ∀ x, u (x * k, 1) = u (x, 1)) (hi : N.relIndex K ≠ 0) :
    hint (K.prod K') u = ((N.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : G ⧸ N, u (q.out, 1) := by
  have hp : ∀ z : G × P, z = (z.1, 1) := fun z => Prod.ext rfl (Subsingleton.elim _ _)
  set L : Subgroup (G × P) := N.comap (MonoidHom.fst G P) with hL
  have hmap : (K.prod K').map (MonoidHom.fst G P) = K := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz.1
    · intro hx
      exact ⟨(x, 1), ⟨hx, K'.one_mem⟩, rfl⟩
  have hrel : L.relIndex (K.prod K') = N.relIndex K := by
    rw [hL, Subgroup.relIndex_comap, hmap]
  have hLK : L ≤ K.prod K' := fun z hz => by
    rw [hp z]
    exact ⟨hNK hz, K'.one_mem⟩
  have hLu : L ≤ rStab u := fun k hk x => by
    have h1 : x * k = (x.1 * k.1, 1) := Prod.ext rfl (Subsingleton.elim _ _)
    rw [h1, hu k.1 hk x.1, ← hp x]
  rw [GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_finite_level_sum _ _ L u hLK hLu (by rwa [hrel]), hrel]
  congr 1
  have hval : ∀ q : G ⧸ N, u (Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L)) = u (q.out, 1) := by
    intro q
    have hm : ((q.out, (1 : P)))⁻¹ * Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L) ∈ L :=
      QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm
    obtain ⟨k, hk⟩ : ∃ k : G × P, k ∈ L ∧ Quotient.out (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L) = (q.out, 1) * k :=
      ⟨_, hm, (mul_inv_cancel_left _ _).symm⟩
    rw [hk.2]
    exact hLu hk.1 _
  have hbij : Function.Bijective (fun q : G ⧸ N => (QuotientGroup.mk (q.out, (1 : P)) : (G × P) ⧸ L)) := by
    constructor
    · intro a b hab
      have h := QuotientGroup.eq.mp hab
      have h2 : (a.out)⁻¹ * b.out ∈ N := by simpa [hL] using h
      rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
      exact QuotientGroup.eq.mpr h2
    · intro c
      induction c using QuotientGroup.induction_on with
      | H z =>
        refine ⟨QuotientGroup.mk z.1, QuotientGroup.eq.mpr ?_⟩
        have h3 : ((QuotientGroup.mk z.1 : G ⧸ N).out)⁻¹ * z.1 ∈ N :=
          QuotientGroup.eq.mp (QuotientGroup.out_eq' _)
        simpa [hL] using h3
  rw [← finsum_comp _ hbij]
  exact finsum_congr hval

private theorem tr_core (hTr : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.TrLevel) (hCv : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp)
    {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K N : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hNo : IsOpen (N : Set G)) (hNc : IsCompact (N : Set G)) (hNK : N ≤ K)
    (hi : ((N.relIndex K : ℕ) : ℂ) ≠ 0) (hfd : FiniteDimensional ℂ (fixed ρ N))
    (f₁ f₂ F : G → ℂ) (h₁ : IsHecke N f₁) (h₂ : IsHecke N f₂)
    (hFeq : F = fun g => ((N.relIndex K : ℕ) : ℂ)⁻¹ * UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N f₁ f₂ g) :
    trOn (fixed ρ N) (Lv ρ N f₁ * Lv ρ N f₂) = ((N.relIndex K : ℕ) : ℂ) ^ 2 * trc ρ K F := _root_.DedupShared.dedup_tr_core_6 (G := G) (V := V) hTr hCv ρ K N hKo hKc hNo hNc hNK hi hfd f₁ f₂ F h₁ h₂ hFeq

theorem UpperTheory.V.Z.Mult.Pi.seenTrA :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.TrLevel → UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.CvOp → UpperTheory.V.Z.Mult.Pi.SeenTrA := by
  intro hTr hAdm hCv E _ _ _ n w hw τ N hNo hNK
  obtain ⟨-, -, hKo, hKc, -⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.unitHecke E n 0 0 w
  have hNc : IsCompact (N : Set (GLw n w)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen N hNo) hNK
  haveI : Finite ((KGL w (n := n) : Subgroup (GLw n w)) ⧸ N.subgroupOf (KGL w (n := n))) :=
    GlobalTheory.TwTrLevel.finite_quot (KGL w (n := n)) (KGL w (n := n)) N hKc hKo hNo le_rfl
  have hi : N.relIndex (KGL w (n := n)) ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hiC : ((N.relIndex (KGL w (n := n)) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hi
  intro φ₁ φ₂ hb
  refine tr_core hTr hCv τ.ρ (KGL w (n := n)) N hKo hKc hNo hNc hNK hiC (hAdm E n w τ N hNo) _ _ _ (hb false) (hb true) ?_
  funext g
  have h₁ := hb false
  have h₂ := hb true
  have hr : ∀ k ∈ N, ∀ x : GLw n w, two φ₁ φ₂ w false (x * k) * two φ₁ φ₂ w true ((x * k)⁻¹ * g) =
      two φ₁ φ₂ w false x * two φ₁ φ₂ w true (x⁻¹ * g) := by
    intro k hk x
    have e : (x * k)⁻¹ * g = k⁻¹ * (x⁻¹ * g) := by group
    rw [e, (h₁.2 k hk x).2, (h₂.2 k⁻¹ (N.inv_mem hk) _).1]
  have hcv : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv N (two φ₁ φ₂ w false) (two φ₁ φ₂ w true) g =
      ∑ᶠ q : GLw n w ⧸ N, two φ₁ φ₂ w false q.out * two φ₁ φ₂ w true (q.out⁻¹ * g) := by
    unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.cv
    rw [GlobalTheory.T.haarIntegralNormalizedOpenCompact_eq_finite_level_sum _ N N _ le_rfl (fun k hk x => hr k hk x) (by simp)]
    simp
  have hpr : ∀ x : GLw n w, ((x, 1) : GLw n w × GLw 0 w)⁻¹ * (g, 1) = (x⁻¹ * g, 1) := fun x =>
    Prod.ext rfl (Subsingleton.elim _ _)
  rw [hcv]
  unfold PositivityTheory.Rg.BcB.G8.seen
  rw [if_pos hw]
  rw [hint_fst (KGL w (n := n)) N (KGL w (n := 0)) _ hNK ?_ hi]
  · congr 1
    refine finsum_congr fun q => ?_
    rw [hpr]
    rfl
  · intro k hk x
    rw [hpr, hpr]
    exact hr k hk x
