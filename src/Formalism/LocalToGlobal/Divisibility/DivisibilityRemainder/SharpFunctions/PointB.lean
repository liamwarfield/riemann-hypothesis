module

public import Formalism.LocalToGlobal.PtKOfReal
public import Formalism.SharpRestriction.Divisibility.SlopeExcess.FamilyStatementOfScaledLemmas

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.HookProducts.LambdaZeroLeFourB
noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.FunSharp

open Formalism.BasicNotions Formalism.MainNotions

theorem lambda_zero_le_four_b {D : D7} (L : SizeData₂ D) (hS : SizesAt L) : lam0 D ≤ 4 * L.sc.b := by
  obtain ⟨-, -, hK, hKR, hT, -, -, -, -, -, -, -, -, hEta, hNodes, -, -, -, -, -, hG, -, -⟩ := hS
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hθ : 0 ≤ szTh L := by unfold szTh; have := L.sc.eps_pos; positivity
  have hxθ : 1 ≤ L.sc.x ^ szTh L := Real.one_le_rpow hx1.le hθ
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb0 : 0 ≤ L.sc.b := by unfold Scale.b; exact (Real.exp_pos _).le
  set A : ℝ := L.sc.x ^ szTh L * L.sc.L with hA
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith
  set F : ℝ := (D.R.f : ℝ) with hFdef
  set R : ℝ := (D.R.r : ℝ) with hRdef

  have hF1 : 1 ≤ F := by
    have h12 : A ≤ F * Real.log D.R.k := hKR.2.2.2.2.2.2.2.2.2.2.2.1
    by_contra hc
    have hf0 : D.R.f = 0 := by
      have : (D.R.f : ℝ) < 1 := not_le.mp hc
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    rw [hFdef, hf0] at h12
    simp at h12
    linarith

  have hR1 : 1 ≤ R := by
    have hfr : F ≤ R ^ 2 := hKR.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hR0 : 0 ≤ R := by positivity
    nlinarith

  have hT1 : 1 ≤ (D.R.t : ℝ) := hT.1
  have hK1 : 1 ≤ (D.R.k : ℝ) := by
    have h := hK.1
    have hp : 0 < L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) := Real.rpow_pos_of_pos (by linarith) _
    have hk0 : 0 < (D.R.k : ℝ) := lt_of_lt_of_le hp h
    have : 0 < D.R.k := by exact_mod_cast hk0
    exact_mod_cast this

  have hη1 : 1 ≤ L.etaSz := hT1.trans hEta.1
  have hden : 1 ≤ (D.R.t : ℝ) ^ 3 * F * (D.R.k : ℝ) ^ 3 := by
    have h1 : 1 ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ hT1
    have h2 : 1 ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hK1
    have h3 : 1 ≤ (D.R.t : ℝ) ^ 3 * F := by nlinarith
    nlinarith
  have hηb : L.etaSz ≤ L.sc.b := hEta.2.1.trans (div_le_self hb0 hden)
  have hηm : L.etaSz / D.R.m ≤ L.etaSz := by
    rcases Nat.eq_zero_or_pos D.R.m with h | h
    · rw [h, Nat.cast_zero, div_zero]; linarith
    · exact div_le_self (by linarith) (by exact_mod_cast h)
  have hQ : L.sc.x ^ szTh L * R ^ 19 * F ^ 5 * L.sc.L ≤ L.sc.b :=
    (hNodes.2.2.1.trans hηm).trans hηb

  have hF5 : F ≤ F ^ 5 := le_self_pow₀ hF1 (by norm_num)
  have hR19 : R ^ 2 ≤ R ^ 19 := pow_le_pow_right₀ hR1 (by norm_num)
  have hFR : F * R ^ 2 ≤ F ^ 5 * R ^ 19 := mul_le_mul hF5 hR19 (by positivity) (by positivity)
  have hQ' : F * R ^ 2 * A ≤ L.sc.b := by
    have : F * R ^ 2 * A ≤ F ^ 5 * R ^ 19 * A := mul_le_mul_of_nonneg_right hFR (by linarith)
    have e : F ^ 5 * R ^ 19 * A = L.sc.x ^ szTh L * R ^ 19 * F ^ 5 * L.sc.L := by rw [hA]; ring
    linarith
  have hFR0 : 0 ≤ F * R ^ 2 := by positivity
  have hFRb : F * R ^ 2 ≤ L.sc.b := le_trans (le_mul_of_one_le_right hFR0 hA1) hQ'

  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (1 : ℝ) ≤ D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).one_lt.le
  have hlog0 : 0 ≤ Real.log (2 * (D.host.g 0 : ℝ)) := Real.log_nonneg (by linarith)
  have hY : ∀ i, (D.host.g i : ℝ) ≤ 2 * (D.host.g 0 : ℝ) := fun i => (hG i 0).2.1
  have h0 := Formalism.MainNotions.DIV.Proofs.ScaledLatticeNorms.scaled_lattice_nonzero_holds D (D.host.g 0 : ℝ) hY
  have hlog : Real.log (2 * (D.host.g 0 : ℝ)) ≤ 1 + A := by
    rw [Real.log_mul (by norm_num) hg0.ne']
    have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have h3 : Real.log (D.host.g 0 : ℝ) ≤ A := (hG 0 0).2.2
    linarith
  calc lam0 D ≤ 2 * F * R ^ 2 * Real.log (2 * (D.host.g 0 : ℝ)) := h0
    _ ≤ 2 * F * R ^ 2 * (1 + A) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 2 * (F * R ^ 2) + 2 * (F * R ^ 2 * A) := by ring
    _ ≤ 4 * L.sc.b := by linarith

end Formalism.MainNotions.DIV.HookProducts.FunSharp
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.HookProducts.NormAtEqSqrtMajAt
open Module NumberField

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.FunSharp

variable {K : Type} [Field K] [NumberField K] [StarRing K]

private theorem norm_realize_sq_eq_sum_majAt_re {ι V : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 = ∑ v, (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_prod_type, Formalism.HermitianLatticesTheory.majAt, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two]
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, Complex.mul_re]
  ring

private theorem slope_map_eq_of_norm_eq {G E F : Type} [AddCommGroup G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (α : G →+ E) (β : G →+ F) (hn : ∀ g, ‖β g‖ = ‖α g‖) (H : AddSubgroup G) :
    Formalism.F.slope (H.map β).toIntSubmodule = Formalism.F.slope (H.map α).toIntSubmodule := by
  have hz : ∀ g, β g = 0 ↔ α g = 0 := fun g => by rw [← norm_eq_zero, hn g, norm_eq_zero]
  have key : ∀ {E₁ E₂ : Type} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
      (α₁ : G →+ E₁) (α₂ : G →+ E₂), (∀ g, ‖α₂ g‖ = ‖α₁ g‖) →
      DiscreteTopology (H.map α₁).toIntSubmodule → DiscreteTopology (H.map α₂).toIntSubmodule := by
    intro E₁ E₂ _ _ α₁ α₂ hn' hd
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff] at hd ⊢
    obtain ⟨ε, hε, h⟩ := hd
    refine ⟨ε, hε, fun y hy => ?_⟩
    obtain ⟨w, hw⟩ := y
    have hw' : w ∈ H.map α₂ := hw
    obtain ⟨g, hg, rfl⟩ := AddSubgroup.mem_map.1 hw'
    have hmem : α₁ g ∈ (H.map α₁).toIntSubmodule := AddSubgroup.mem_map_of_mem α₁ hg
    have h1 := h ⟨α₁ g, hmem⟩ (by
      have hy' := hy
      simp only [Subtype.dist_eq, ZeroMemClass.coe_zero, dist_zero_right] at hy' ⊢
      change ‖α₂ g‖ < ε at hy'
      change ‖α₁ g‖ < ε
      rw [← hn']
      exact hy')
    have h2 : α₁ g = 0 := congrArg Subtype.val h1
    have h3 : α₂ g = 0 := by rw [← norm_eq_zero, hn', h2, norm_zero]
    exact Subtype.ext h3
  have hd : DiscreteTopology (H.map β).toIntSubmodule ↔ DiscreteTopology (H.map α).toIntSubmodule :=
    ⟨key β α (fun g => (hn g).symm), key α β hn⟩
  by_cases hα : DiscreteTopology (H.map α).toIntSubmodule
  · obtain ⟨hc, hr⟩ := Formalism.HN.Rerealization.covol_rk_eq α β hn H hα (hd.2 hα)
    unfold Formalism.F.slope Formalism.F.deg
    rw [hc, hr]
  · have hβ : ¬ DiscreteTopology (H.map β).toIntSubmodule := fun h => hα (hd.1 h)
    unfold Formalism.F.slope Formalism.F.deg Formalism.F.covol
    rw [dite_eq_right hα, dite_eq_right hβ]
    simp

theorem muMax_tie (A : Formalism.BasicNotions.HLat K) {n : ℕ} (L : Submodule (𝓞 K) (Fin n → K))
    (XE : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (e : (Fin n → K) ≃ₗ[K] A.V)
    (hlat : A.L = L.map ((e : (Fin n → K) →ₗ[K] A.V).restrictScalars (𝓞 K)))
    (hmet : ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (e x) (e y) = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) XE v x y) :
    Formalism.HN.muMaxDef (Pi.basisFun K (Fin n)) XE L = A.muMax := by
  set f : (Fin n → K) →ₗ[𝓞 K] A.V := (e : (Fin n → K) →ₗ[K] A.V).restrictScalars (𝓞 K) with hf
  set g : A.V →ₗ[𝓞 K] (Fin n → K) := (e.symm : A.V →ₗ[K] (Fin n → K)).restrictScalars (𝓞 K) with hg
  have hgf : ∀ N : Submodule (𝓞 K) (Fin n → K), (N.map f).map g = N := by
    intro N
    rw [← Submodule.map_comp]
    have : g.comp f = LinearMap.id := by
      ext x; simp [hf, hg]
    rw [this, Submodule.map_id]
  have hfg : ∀ N : Submodule (𝓞 K) A.V, (N.map g).map f = N := by
    intro N
    rw [← Submodule.map_comp]
    have : f.comp g = LinearMap.id := by
      ext x; simp [hf, hg]
    rw [this, Submodule.map_id]
  have hn : ∀ x, ‖(Formalism.HermitianLatticesTheory.realize A.b A.X).comp f.toAddMonoidHom x‖ =
      ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE x‖ := by
    intro x
    have h1 := norm_realize_sq_eq_sum_majAt_re A.b A.X (e x)
    have h2 := norm_realize_sq_eq_sum_majAt_re (Pi.basisFun K (Fin n)) XE x
    simp_rw [hmet] at h1
    show ‖Formalism.HermitianLatticesTheory.realize A.b A.X (e x)‖ = _
    rw [← Real.sqrt_sq (norm_nonneg (Formalism.HermitianLatticesTheory.realize A.b A.X (e x))),
      ← Real.sqrt_sq (norm_nonneg (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE x)), h1, h2]
  have hslope : ∀ N : Submodule (𝓞 K) (Fin n → K),
      Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize A.b A.X) (N.map f) =
        Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE) N := by
    intro N
    unfold Formalism.HN.slope Formalism.HN.zl
    rw [Submodule.map_toAddSubgroup, AddSubgroup.map_map]
    exact slope_map_eq_of_norm_eq _ _ hn N.toAddSubgroup
  have hne : ∀ N : Submodule (𝓞 K) (Fin n → K), N ≠ ⊥ → N.map f ≠ ⊥ := by
    intro N hN h
    apply hN
    rw [← hgf N, h, Submodule.map_bot]
  have hne' : ∀ N : Submodule (𝓞 K) A.V, N ≠ ⊥ → N.map g ≠ ⊥ := by
    intro N hN h
    apply hN
    rw [← hfg N, h, Submodule.map_bot]
  have hmu : Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin n)) XE) L =
      Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize A.b A.X) A.L := by
    unfold Formalism.HN.muMax
    congr 1
    ext t
    constructor
    · rintro ⟨N, hNL, hN0, hs⟩
      refine ⟨N.map f, ?_, hne N hN0, (hslope N).trans hs⟩
      rw [hlat]; exact Submodule.map_mono hNL
    · rintro ⟨N, hNL, hN0, hs⟩
      refine ⟨N.map g, ?_, hne' N hN0, ?_⟩
      · rw [← hgf L]
        apply Submodule.map_mono
        rw [← hlat]; exact hNL
      · rw [← hslope, hfg]; exact hs
  unfold Formalism.BasicNotions.HLat.muMax Formalism.HN.muMaxDef
  rw [hmu]

end Formalism.MainNotions.DIV.HookProducts.FunSharp
end
end

noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
  Formalism.L2.RowDataTransport

namespace Formalism.L2.DIV.FunSharpTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

theorem muMax_heq {P : RowSideFamily ex} {Z1 Z2 : DefSub P.A3.fam3.amb3} (h : Z1 = Z2) {S1 : IndefData (P.A3.side3 P.Ps P.ψs Z1)}
    {S2 : IndefData (P.A3.side3 P.Ps P.ψs Z2)} (hS : HEq S1 S2) : S1.muMaxRR = S2.muMaxRR := by
  subst h
  cases hS
  rfl

end Formalism.L2.DIV.FunSharpTop

end
