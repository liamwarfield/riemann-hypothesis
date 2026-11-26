module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterTransferInvariantPairing
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceTwistSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopVectorMemExtraProjection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorSplitPlaceSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorSplitPlaceSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.TensorLatO

theorem isSBHalf_tensorAt_of_bounds {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (L : AddSubgroup (WO S T))
    (e : AE D) (he : e * p.e = 0) (hMap : ∀ u ∈ L, u.map (fun a => p.e * a) ∈ L)
    (A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (hAL : ∀ X : Matrix Y Y' k, (∀ r q, X r q ∈ 𝒪[k]) → A • p.up FS FT X ∈ L)
    (hBL : ∀ u ∈ L, ∀ r q, (B : k) * p.down FS FT u r q ∈ 𝒪[k])
    (Φ : WO S T → ℂ) (hΦ : IsSBHalf e L Φ) (Ψ : Matrix Y Y' k → ℂ) (hΨ : Ψ ∈ SB (Matrix Y Y' k)) :
    IsSBHalf (e + p.e) L (p.tensorAt FS FT Φ Ψ) := by
  classical
  unfold IsSBHalf at hΦ ⊢
  obtain ⟨hΦs, kΦ, hkΦ, hΦi, hΦl⟩ := hΦ
  obtain ⟨N, hN, hΨi, hΨl⟩ := GlobalTheory.SBUnif.uniform k Y Y' Ψ hΨ
  have hud : ∀ u : WO S T, p.up FS FT (p.down FS FT u) = u.map (fun a => p.e * a) := by
    intro u
    unfold Place.down Place.up
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
    ext i j
    exact p.ι_π _
  have hupn : ∀ (n : ℕ) (X : Matrix Y Y' k), p.up FS FT (n • X) = n • p.up FS FT X :=
    fun n X => map_nsmul (Witness.upH p FS FT) n X
  have hdownn : ∀ (n : ℕ) (u : WO S T), p.down FS FT (n • u) = n • p.down FS FT u :=
    fun n u => map_nsmul (Witness.downH p FS FT) n u
  have hsupp : ∀ t, p.tensorAt FS FT Φ Ψ t ≠ 0 →
      Φ (t - p.up FS FT (p.down FS FT t)) ≠ 0 ∧ Ψ (p.down FS FT t) ≠ 0 := fun t ht =>
    ⟨left_ne_zero_of_mul ht, right_ne_zero_of_mul ht⟩
  refine ⟨fun t ht => ?_, kΦ * (N * B * A), Nat.mul_pos hkΦ (Nat.mul_pos (Nat.mul_pos hN hB) hA),
    fun u hu hhu t => ?_, fun t ht => ?_⟩
  · obtain ⟨h1, -⟩ := hsupp t ht
    have hs := hΦs _ h1
    have hw := Witness.up_half p FS FT (p.down FS FT t)
    intro i j
    have a1 := hs i j
    have a2 := hw i j
    have e1 : t i j = (t - p.up FS FT (p.down FS FT t)) i j + p.up FS FT (p.down FS FT t) i j := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [e1]
    linear_combination (1 - p.e) * a1 + (1 - e) * a2 +
      (p.up FS FT (p.down FS FT t) i j + (t - p.up FS FT (p.down FS FT t)) i j) * he
  · set X := p.down FS FT u with hX
    have hXL : p.up FS FT X ∈ L := by rw [hX, hud]; exact hMap u hu
    have hYi : ∀ r q, (((kΦ * A : ℕ) : k) • ((B : k) • X)) r q ∈ 𝒪[k] := fun r q => by
      rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
      exact mul_mem (natCast_mem _ _) (hBL u hu r q)
    have hd : p.down FS FT (t + (kΦ * (N * B * A)) • u) = p.down FS FT t + (kΦ * (N * B * A)) • X := by
      rw [Witness.down_add, hdownn]
    have e3 : p.down FS FT t + (kΦ * (N * B * A)) • X =
        p.down FS FT t + (N : k) • (((kΦ * A : ℕ) : k) • ((B : k) • X)) := by
      congr 1
      rw [← Nat.cast_smul_eq_nsmul k, smul_smul, smul_smul]
      congr 1
      push_cast; ring
    set w : WO S T := (N * B * A) • (u - p.up FS FT X) with hw
    have e2 : t + (kΦ * (N * B * A)) • u - p.up FS FT (p.down FS FT t + (kΦ * (N * B * A)) • X) =
        (t - p.up FS FT (p.down FS FT t)) + kΦ • w := by
      rw [Witness.up_add, hupn, hw, smul_smul, nsmul_sub]
      abel
    have hwL : w ∈ L := nsmul_mem (sub_mem hu hXL) _
    have hwH : IsHalf e w := by
      intro i j
      rw [hw, hX, hud, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, nsmul_eq_mul]
      linear_combination ((N * B * A : ℕ) : AE D) * hhu i j - ((N * B * A : ℕ) : AE D) * u i j * he
    show Φ (t + (kΦ * (N * B * A)) • u - p.up FS FT (p.down FS FT (t + (kΦ * (N * B * A)) • u))) *
        Ψ (p.down FS FT (t + (kΦ * (N * B * A)) • u)) =
      Φ (t - p.up FS FT (p.down FS FT t)) * Ψ (p.down FS FT t)
    rw [hd, e2, e3, hΦi w hwL hwH, hΨi _ _ hYi]
  · obtain ⟨h1, h2⟩ := hsupp t ht
    have a1 := hΦl _ h1
    have a2 : A • p.up FS FT (N • p.down FS FT t) ∈ L := hAL _ fun r q => by
      rw [Matrix.smul_apply, nsmul_eq_mul]; exact hΨl _ h2 r q
    rw [hupn] at a2
    have e1 : (kΦ * (N * B * A)) • t = (N * B * A) • (kΦ • (t - p.up FS FT (p.down FS FT t))) +
        kΦ • (B • (A • (N • p.up FS FT (p.down FS FT t)))) := by
      rw [smul_smul, smul_smul, smul_smul, smul_smul, mul_comm (N * B * A) kΦ,
        show kΦ * B * A * N = kΦ * (N * B * A) by ring, ← nsmul_add, sub_add_cancel]
    rw [e1]
    exact add_mem (nsmul_mem a1 _) (nsmul_mem (nsmul_mem a2 B) kΦ)

end GlobalTheory.TensorLatO
end

noncomputable section

namespace GlobalTheory.TensorLatO

theorem isSBHalf_tensorAt_latO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → ∀ Ψ ∈ SB (Matrix P.Y P.Y' P.k), IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) ((ofSplit P.q).tensorAt P.FS P.FT Φ Ψ) := by
  classical
  intro D ψ S T M M' hS hT P e he Φ hΦ Ψ hΨ
  set L := latO S T (M : Set (Fin S.rank → D.host.E)) (M' : Set (Fin T.rank → D.host.E)) fun _ => True with hL
  set q := P.q with hq
  have hee : q.e * q.e = q.e := q.split.1

  have hMap : ∀ u ∈ L, u.map (fun a => (ofSplit q).e * a) ∈ L := fun u hu => by
    have h := GlobalTheory.SplitScalar.idem_smul_mem (LS := (M : Set (Fin S.rank → D.host.E)))
      (LT := (M' : Set (Fin T.rank → D.host.E))) hee u hu
    convert h using 1
    ext i j
    rfl

  obtain ⟨N₀, hN₀, h₀⟩ := GlobalTheory.FinPl.RdInt.exists_nat_mul_mem_fin
    (Sum.elim (fun x : Fin T.rank × P.Y => P.FT.β x.1 x.2) (fun x : P.Y' × Fin S.rank => P.FS.γ x.1 x.2))
  obtain ⟨K, hK, hmul⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT)
  have hAL : ∀ X : Matrix P.Y P.Y' P.k, (∀ r q, X r q ∈ 𝒪[P.k]) →
      (K * (N₀ * N₀)) • (ofSplit q).up P.FS P.FT X ∈ L := by
    intro X hX
    have hent := GlobalTheory.FinPl.RdInt.entry_mem P.FT.β P.FS.γ (fun i a => h₀ (Sum.inl (i, a)))
      (fun a j => h₀ (Sum.inr (a, j))) X hX
    have hh : IsHalf q.e ((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) := fun i j => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm]
      exact congrArg _ (Witness.up_half (ofSplit q) P.FS P.FT X i j)
    have hui : ∀ i j, toEAf D (((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) i j) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro i j
      have h1 : ((N₀ * N₀) • (ofSplit q).up P.FS P.FT X) i j =
          q.sec (((N₀ * N₀ : ℕ) : P.k) * (P.FT.β * X * P.FS.γ) i j) := by
        rw [← nsmul_eq_mul, map_nsmul]
        rfl
      rw [h1]
      exact GlobalTheory.PlaceCoord.toEAf_mem ((q.int_iff _).1 (hent i j))
    have h1 := hmul _ (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceCoord.infPart_split q.split) hh) hui
    rwa [mul_nsmul']

  obtain ⟨M₀, hM₀, hden⟩ := GlobalTheory.PlaceDatum.exists_den_latO (S := S) (T := T) hS.1.fg hT.1.fg
  obtain ⟨K₁, hK₁, h₁⟩ := GlobalTheory.FinPl.RdBound.exists_nat_mul_mem_family
    (fun x : P.Y × Fin T.rank => P.FT.γ x.1 x.2)
  obtain ⟨K₂, hK₂, h₂⟩ := GlobalTheory.FinPl.RdBound.exists_nat_mul_mem_family
    (fun x : Fin S.rank × P.Y' => P.FS.β x.1 x.2)
  have hBL : ∀ u ∈ L, ∀ i j, ((K₁ * M₀ * K₂ : ℕ) : P.k) * (ofSplit q).down P.FS P.FT u i j ∈ 𝒪[P.k] := by
    intro u hu i j
    have heu := GlobalTheory.SplitScalar.idem_smul_mem (LS := (M : Set (Fin S.rank → D.host.E)))
      (LT := (M' : Set (Fin T.rank → D.host.E))) hee u hu
    have hint : ∀ a b, (M₀ : P.k) * q.pr (u a b) ∈ 𝒪[P.k] := fun a b => by
      rw [q.int_iff]
      have h1 : q.sec ((M₀ : P.k) * q.pr (u a b)) = (M₀ : AE D) * (q.e • u) a b := by
        rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, q.sec_pr]
        rfl
      rw [h1]
      refine GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_
      rw [RingHom.map_mul, map_natCast]
      exact hden _ heu a b
    change (_ : P.k) * (P.FT.γ * Matrix.map u q.pr * P.FS.β) i j ∈ 𝒪[P.k]
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine sum_mem fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine sum_mem fun a _ => ?_
    have e : ((K₁ * M₀ * K₂ : ℕ) : P.k) * (P.FT.γ i a * Matrix.map u q.pr a b * P.FS.β b j) =
        ((K₁ : P.k) * P.FT.γ i a) * ((M₀ : P.k) * q.pr (u a b)) * ((K₂ : P.k) * P.FS.β b j) := by
      rw [Matrix.map_apply]; push_cast; ring
    rw [e]
    exact mul_mem (mul_mem (h₁ (i, a)) (hint a b)) (h₂ (b, j))
  exact isSBHalf_tensorAt_of_bounds (ofSplit q) P.FS P.FT L e he hMap (K * (N₀ * N₀)) (K₁ * M₀ * K₂)
    (Nat.mul_pos hK (Nat.mul_pos hN₀ hN₀)) (Nat.mul_pos (Nat.mul_pos hK₁ hM₀) hK₂) hAL hBL Φ hΦ Ψ hΨ

end GlobalTheory.TensorLatO
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorSplitPlaceSelfDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatHalf_tensor_split_place_selfDual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ Φ : WO S T → ℂ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → ∀ Ψ ∈ SB (Matrix P.Y P.Y' P.k), IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) ((ofSplit P.q).tensorAt P.FS P.FT Φ Ψ) := by
  first | exact @GlobalTheory.TensorLatO.isSBHalf_tensorAt_latO | exact GlobalTheory.TensorLatO.isSBHalf_tensorAt_latO | (intros; apply GlobalTheory.TensorLatO.isSBHalf_tensorAt_latO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalBimodelTranslation
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselEmbeddingEqLastGLRootExchange
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselEmbeddingEqLastGLRootExchange
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QPl.QStep

theorem gl₂_embX_eq_embA : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (g : GL Q.n₂ Q.k), ∃ a₀ : GA D S.B'.A, GlobalTheory.MixPer.embA S.B'.d S.B'.o a₀ = Q.gl₂ (embX (Q.c + 1) g) ∧ (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g := by
  intro D ψ σ S Q g
  obtain ⟨a₀, ha⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (ofSplit Q.q) Q.F.F₂ g
  exact ⟨a₀, GlobalTheory.LocGrp.isLoc_unique (ofSplit Q.q)
    (GlobalTheory.NormalFramePeriod.isLoc_embA (ofSplit Q.q) S.B' _ Q.F.F₂ Q.F.G₂ Q.F.bes' ha) (Q.loc₂ _), ha⟩

end GlobalTheory.QPl.QStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselEmbeddingEqLastGLRootExchangeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_besselEmbedding_eq_lastGL_rootExchange : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (g : GL Q.n₂ Q.k), ∃ a₀ : GA D S.B'.A, GlobalTheory.MixPer.embA S.B'.d S.B'.o a₀ = Q.gl₂ (embX (Q.c + 1) g) ∧ (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g := by
  exact @GlobalTheory.QPl.QStep.gl₂_embX_eq_embA
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorLastDefiniteLocalBiModelSecond
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorLastDefiniteLocalBiModelSecond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastOmb

theorem isComp_inv {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) :
    (ofSplit Q.q).IsComp S.χ₂ Q.μ₂⁻¹ := by
  intro t a ha
  have := Q.comp₂ t a ha
  rw [MonoidHom.inv_apply] at this
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, this, Circle.coe_inv, inv_inv]

theorem isLoc_one {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) :
    (ofSplit Q.q).IsLoc Q.F.F₁ (1 : GA D S.J.W₀) (1 : GL Q.n₁ Q.k) := by
  refine ⟨?_, ?_⟩
  · intro i j
    simp [GlobalTheory.MixModel.mt_one]
  · rw [GlobalTheory.MixModel.mt_one, Units.val_one, Matrix.mul_one, Q.F.F₁.βγ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem actO_one_of_away {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) {g : GL Q.n₂ Q.k}
    {a₀ : GA D S.B'.A} (hloc : (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g) (y : WO S.J.W₀ S.B'.A)
    (hy' : IsHalf (1 - (Q.q.e + cA D Q.q.e)) y) : actO S.J.W₀ S.B'.A 1 a₀ y = y := by
  have hsupp := GlobalTheory.LocGrp.suppAt_iff.1 hloc.1
  have he := Q.q.split
  set f : AE D := Q.q.e + cA D Q.q.e with hf
  have hce : cA D Q.q.e * cA D Q.q.e = cA D Q.q.e := by rw [← map_mul, he.1]
  have hff : f * (1 - f) = 0 := by
    rw [hf]; linear_combination (-1 : AE D) * he.1 - hce - 2 * he.2.1
  have hfy : f • y = 0 := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [← hy' i j, ← mul_assoc, hff, zero_mul]
  have hz : HMul.hMul (Formalism.L2.Theta.mt S.B'.A a₀ - 1) (show Matrix (Fin S.B'.A.rank) (Fin S.J.W₀.rank) (AE D) from y) = 0 := by
    rw [← hsupp, Matrix.smul_mul, ← Matrix.mul_smul]
    have h0 : ((ofSplit Q.q).e + cA D (ofSplit Q.q).e) • (show Matrix (Fin S.B'.A.rank) (Fin S.J.W₀.rank) (AE D) from y) = 0 := hfy
    rw [h0, Matrix.mul_zero]
  simp only [actO, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hz
  exact hz

theorem biComb_eq_sum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c₁ : WO A S →₀ ℂ) (c₂ : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) :
    biComb ψ A S A' c₁ c₂ C u =
      ∑ x ∈ c₁.support, (c₁ x * ψ (symplOH A S u x)) • GlobalTheory.SeeSaw.comb ψ S A' c₂ (C (u + x)) := by
  funext v
  simp only [biComb, GlobalTheory.SeeSaw.comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem weil_last_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₂ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (a₀ : GA D S.B'.A), (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g → ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → ∀ u, S.omb (1, a₀) (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u) = biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂')) u := by
  intro D ψ σ S Q c₁ c₂ hAway Λ hbi g a₀ hloc Ξ₁ Ξ₂ Ξ₂' hΞ u
  have hcomm : ∀ G, IsThetaFunO ψ S.J.W₀ S.B'.A G →
      S.omb (1, a₀) (GlobalTheory.SeeSaw.comb ψ S.J.W₀ S.B'.A c₂ G) = GlobalTheory.SeeSaw.comb ψ S.J.W₀ S.B'.A c₂ (S.omb (1, a₀) G) := by
    intro G hG
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.SeeSaw.comb, map_sum, map_smul]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [S.weilb.om_heis 1 a₀ y G hG, actO_one_of_away Q hloc y (hAway y hy)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [biComb_eq_sum, biComb_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul]
  obtain ⟨T₂, hT₂, hΛ⟩ := hbi.2 Ξ₁ (u + x)
  have e1 : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) (u + x) = T₂ Ξ₂ :=
    funext fun v => hΛ Ξ₂ _ (fun q => GlobalTheory.LocFlat.CFac.prodSB_apply _ _ _) v
  have e2 : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂') (u + x) = T₂ Ξ₂' :=
    funext fun v => hΛ Ξ₂' _ (fun q => GlobalTheory.LocFlat.CFac.prodSB_apply _ _ _) v
  have e3 : S.omb (1, a₀) (T₂ Ξ₂) = T₂ Ξ₂' := by
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.J.W₀ S.B'.A S.χ₂ S.χ₂ S.omb S.weilb Q.μ₂⁻¹ Q.μ₂⁻¹ (isComp_inv Q)
      (isComp_inv Q) Q.n₂ Q.n₁ Q.F.F₁ Q.F.F₂ T₂ hT₂ 1 1 a₀ g (isLoc_one Q) hloc Ξ₂ Ξ₂' ?_
    rw [hΞ, inv_inv]
    simp
  rw [e1, e2, hcomm _ (hT₂.theta _), e3]

end GlobalTheory.LastOmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorLastDefiniteLocalBiModelSecondStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_lastDefiniteLocal_biModel_second : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₂ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (a₀ : GA D S.B'.A), (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g → ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → ∀ u, S.omb (1, a₀) (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u) = biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂')) u := by
  first | exact @GlobalTheory.LastOmb.weil_last_local | exact GlobalTheory.LastOmb.weil_last_local | (intros; apply GlobalTheory.LastOmb.weil_last_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalBimodelTranslation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TriStep.valK_gl₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂))) → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂') (rTrans (Q.gl₂ (embX (Q.c + 1) g)) f) = ((nabs Q.k (Matrix.GeneralLinearGroup.det g) ^ ((((Q.c + 1 : ℕ) : ℝ) + 1) / 2 - ((σ + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f := by
  intro D ψ hψ σ S Q c₁ c₂ h₁ h₂ φ hφ Λ hΛ g Ξ₁ Ξ₂ Ξ₂' hΞ hC f hf
  obtain ⟨a₀, ha, hloc⟩ := (GlobalTheory.T.exists_besselEmbedding_eq_lastGL_rootExchange) D ψ σ S Q g
  have hop := (GlobalTheory.T.weilOperator_lastDefiniteLocal_biModel_second) D ψ σ S Q c₁ c₂ h₂ Λ hΛ g a₀ hloc Ξ₁ Ξ₂ Ξ₂' hΞ
  have hf0 : IsContAut S.B'.V f := by
    have := hf.1 1
    rwa [map_one, GlobalTheory.TriStep.rTrans_one] at this
  have hF := GlobalTheory.SeeSawLastValue.contAut_biLift (GlobalTheory.SeeSaw.biAct_all D) S.weila S.weilb S.B.cpt S.J.cpt S.B.vA S.J.v0 hφ hC
  have hB3 := ((GlobalTheory.SeeSaw.biAct_all D) ψ _ _ _ _ _ _ _ S.oma S.omb S.weila S.weilb _ hC).2.2.1
  have hshift : biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂'))) =
      rTrans a₀ (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)))) := by
    funext h
    simp only [biLift, rTrans]
    congr 1; funext h₁; congr 1; funext h₀; congr 1
    have e : ((h₁, h * a₀) : GA D S.J.W₀ × GA D S.B'.A) = (h₁, h) * (1, a₀) := by simp
    rw [e, map_mul, Module.End.mul_apply]
    refine congrArg (fun X => S.omb (h₁, h) X 0) ?_
    funext v
    rw [hB3]
    refine congrArg (fun X => S.oma (h₀, h₁) X 0) ?_
    funext u
    rw [hop u]
  have hc : Q.c + 1 = 2 * σ + 1 := Q.F.bes'.1
  have hexp : ((((Q.c + 1 : ℕ) : ℝ) + 1) / 2 - ((σ + 1 : ℕ) : ℝ)) = 0 := by
    rw [hc]; push_cast; ring
  rw [hexp, Real.rpow_zero, Complex.ofReal_one, one_mul]
  unfold GlobalTheory.TriStep.valK
  rw [hshift, ← ha]
  exact GlobalTheory.Core.Mi.per_rTrans D ψ σ S.B' _ f a₀ hψ hF hf0
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalBimodelTranslationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_bimodel_translation : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂))) → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂') (rTrans (Q.gl₂ (embX (Q.c + 1) g)) f) = ((nabs Q.k (Matrix.GeneralLinearGroup.det g) ^ ((((Q.c + 1 : ℕ) : ℝ) + 1) / 2 - ((σ + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f := by
  first | exact @GlobalTheory.TriStep.valK_gl₂ | exact GlobalTheory.TriStep.valK_gl₂ | (intros; apply GlobalTheory.TriStep.valK_gl₂ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpLowerBlockParameterProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelTwistPlaceInThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelTwistPlaceInThetaFunctions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.ChainTw.linModel_theta : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι ι', IsChart s k φ ι → IsChart s' (k + 1) φ ι' → ∀ μS μT ξl : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μS y = Circle.toUnits (c.chS (k + 1) x)) → (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → LiftsChar φ PP ξl (w.ξ PP) → ∀ P, ∃ (W : Submodule ℂ (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → ℂ)) (hW : ∀ g h, ∀ u ∈ W, GlobalTheory.ParHecke.omTwo μS μT g h u ∈ W) (hΦ : datum ξl⁻¹ ∈ W) (T : W →ₗ[ℂ] (WO s.V s'.V → ℂ)), T ⟨_, hΦ⟩ = p.pt P ∧ (∀ u, IsThetaFunO c.ψ s.V s'.V (T u)) ∧ ∀ g h (u : W), p.ω (ι g, ι' h) (T u) = T ⟨_, hW g h u u.2⟩ := by
  intro D hG c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT ξl hS hT hξ P
  obtain ⟨m, X, hX⟩ := GlobalTheory.Size.exists_isCovolOne s.V s'.V
  obtain ⟨hW, hΦ, T, h1, h2, h3, h4⟩ :=
    GlobalTheory.T.linearModel_splitPlace_twist_schwartzBruhat D hG c w hw k hk s s' hs hs' p hp PP hPP v φ hφ ι ι' hι hι' μS μT ξl hS hT hξ P m X hX
  exact ⟨_, hW, hΦ, T, h1, h2, h3⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelTwistPlaceInThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearModel_twistPlace_in_thetaFunctions : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι ι', IsChart s k φ ι → IsChart s' (k + 1) φ ι' → ∀ μS μT ξl : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μS y = Circle.toUnits (c.chS (k + 1) x)) → (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → LiftsChar φ PP ξl (w.ξ PP) → ∀ P, ∃ (W : Submodule ℂ (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → ℂ)) (hW : ∀ g h, ∀ u ∈ W, GlobalTheory.ParHecke.omTwo μS μT g h u ∈ W) (hΦ : datum ξl⁻¹ ∈ W) (T : W →ₗ[ℂ] (WO s.V s'.V → ℂ)), T ⟨_, hΦ⟩ = p.pt P ∧ (∀ u, IsThetaFunO c.ψ s.V s'.V (T u)) ∧ ∀ g h (u : W), p.ω (ι g, ι' h) (T u) = T ⟨_, hW g h u u.2⟩ := by
  first | exact @GlobalTheory.ChainTw.linModel_theta | exact GlobalTheory.ChainTw.linModel_theta | (intros; apply GlobalTheory.ChainTw.linModel_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpLowerBlockParameterProof
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.ChainTw.UpQProof

theorem isGen_of_injective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A B₀ : Type} [Fintype A] [DecidableEq A] [Fintype B₀] [DecidableEq B₀]
    {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GL (A ⊕ B₀) k) X} {ρ' : Representation ℂ (GL (A ⊕ B₀) k) Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ g y, f (ρ g y) = ρ' g (f y)) (hi : Function.Injective f) {ξ : kˣ →* ℂˣ} {ϖ : kˣ} {B : Multiset ℂˣ} {x : X}
    (h : GlobalTheory.ParHecke.IsGen ρ' ξ ϖ B (f x)) : GlobalTheory.ParHecke.IsGen ρ ξ ϖ B x := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, fun s R d hR => hi ?_⟩
  · intro g hg d hd
    apply hi
    rw [hf, h1 g hg d hd, map_smul]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, h3 s R d hR]
      simp only [map_smul, hf]


open ValuativeRel in
theorem seg_eq_segL {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (PP : Pl D.host.E) (hP : IsProjAt φ PP)
    {ϖ : (Fv D.host.F v)ˣ} (hϖ : valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) = uniformizer (Fv D.host.F v))
    (z : ℂˣ) (t : ℕ) : GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t := by
  have hq := (GlobalTheory.PlaceProjAt.under_resCard D v φ PP hP).2
  have hn := GlobalTheory.GLDoubling.nabs_unif hϖ
  unfold GlobalTheory.LFun.seg GlobalTheory.ParHecke.segL
  rw [Finset.range_val]
  refine Multiset.map_congr rfl fun n _ => ?_
  ext
  simp only [Units.val_mul, GlobalTheory.SmGL.val_absPow, hn, hq, GlobalTheory.LFun.npowU, Units.val_mk0, GlobalTheory.LFun.npow]
  congr 1
  rw [Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), ← Complex.cpow_neg]
  congr 1
  ring

theorem isUnram_of_lifts {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (PP : Pl D.host.E) (hP : IsProjAt φ PP)
    (a : (kP PP)ˣ →* ℂˣ) (μ μ' : (Fv D.host.F v)ˣ →* ℂˣ) (h : LiftsChar φ PP μ a) (h' : LiftsChar φ PP μ' a) :
    GlobalTheory.SplitWeil.IsUnram (μ * μ'⁻¹) := by
  intro y hy
  have hy1 : Valued.v (y : Fv D.host.F v) = 1 := (GlobalTheory.TameLiftChar.val_eq_one_iff _).1 hy
  obtain ⟨a0, ha0⟩ := ReciprocityTheory.Aut.adic_exists_approx v (y : Fv D.host.F v) hy1.le
  let x0 : 𝓞 D.host.E := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a0
  have hx0 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) = algebraMap (𝓞 D.host.F) (Fv D.host.F v) a0 := by
    have h1 : ((x0 : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F a0) := by
      show algebraMap (𝓞 D.host.E) D.host.E _ = _
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [h1, GlobalTheory.PlaceRed.rdQ_alg]
    rfl
  have hr1 : Valued.v ((y : Fv D.host.F v) - GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E)) < 1 := by rw [hx0]; exact ha0
  have hnot : x0 ∉ PP.asIdeal := by
    intro hm
    have h2 := (hP x0).1 hm
    have : Valued.v (y : Fv D.host.F v) < 1 := by
      have := Valuation.map_add_lt Valued.v hr1 h2
      simpa using this
    rw [hy1] at this
    exact lt_irrefl _ this
  have hne : (Ideal.Quotient.mk PP.asIdeal x0 : kP PP) ≠ 0 := fun h0 => hnot (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  let κ : (kP PP)ˣ := Units.mk0 _ hne
  have hR : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (y : Fv D.host.F v) (κ : kP PP) := ⟨x0, rfl, hr1⟩
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h y κ hR, h' y κ hR, mul_inv_cancel]

end GlobalTheory.ChainTw.UpQProof


open GlobalTheory.ChainTw.UpQProof in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.ChainTw.upQ_holds : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpQ D := by
  classical
  intro hP D hN c w hw k hk s s' hs hs' p hp u φ hu v₀ _
  intro PP hPP v φv hφv x ϖ hx ξl hξl ι' hι'
  obtain ⟨-, hch⟩ := GlobalTheory.TwistChart.charts_at_twist D c w hw k hk.le s hs PP hPP
  obtain ⟨-, -, ⟨ι, hι⟩, hμ⟩ := hch v φv hφv
  obtain ⟨μS, -, hμS⟩ := hμ (c.chS (k + 1))
  obtain ⟨μT, -, hμT⟩ := hμ (c.chT (k + 1))
  obtain ⟨W, hW, hΦ, T, hT0, hTθ, hTω⟩ :=
    GlobalTheory.T.linearModel_twistPlace_in_thetaFunctions D hN c w hw k hk s s' hs hs' p hp PP hPP v φv hφv ι ι' hι hι' μS μT ξl hμS hμT hξl φ
  have hsrc := hu v₀ PP hPP v φv hφv x ϖ hx ξl hξl ι hι
  obtain ⟨e, he, hx1, hx2, hϖ⟩ := hx
  have hSϖ : μS ϖ = Circle.toUnits (c.chS (k + 1) x) := hμS x ϖ ⟨e, he, hx1, hx2⟩
  have hTϖ : μT ϖ = Circle.toUnits (c.chT (k + 1) x) := hμT x ϖ ⟨e, he, hx1, hx2⟩
  have htame := (GlobalTheory.tameLift_isTame_not_isUnram D v φv PP (w.ξ PP) hφv (hw.ne PP hPP) ξl hξl).1
  obtain ⟨hres, -, -⟩ := GlobalTheory.ChainOnto.levRes_step D c hw.com k hk
  have hQ := hres PP (hw.union ▸ Finset.mem_union_right _ hPP)
  rw [hw.chiQ (k + 1) PP hPP, inv_inv] at hQ
  have hunS : GlobalTheory.SplitWeil.IsUnram (μS * ξl⁻¹) :=
    isUnram_of_lifts φv PP hφv (w.ξ PP) μS ξl (GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace D _ PP _ hQ.1 v φv hφv μS hμS) hξl
  have hunT : GlobalTheory.SplitWeil.IsUnram (μT * ξl⁻¹) :=
    isUnram_of_lifts φv PP hφv (w.ξ PP) μT ξl (GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace D _ PP _ hQ.2 v φv hφv μT hμT) hξl
  have hcard : Fintype.card (Blocks (k + 1) D.R.t) = Fintype.card (Blocks k D.R.t) + D.R.t := by
    simp [Blocks, Fintype.card_sigma]
    ring
  obtain ⟨hr, -, hfl⟩ := hs
  have hHaar : s.ν.IsHaarMeasure := hfl.haar
  have hFund : IsFundamentalDomain (GQ s.V) s.fd s.ν := hfl.fund
  have hθ : IsInfFam c.θ := hw.com.inf
  set F : GA D s.V → ℂ := PiLocalization₂.val u v₀ with hF
  have hFa := PiLocalization₂.val_autCusp c s u v₀
  let ρ0 : Representation ℂ (GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)) (GA D s.V → ℂ) :=
    (GlobalTheory.PRep.rightReg ℂ (GA D s.V) ℂ).comp ι
  let cy : GA D s.V → ℂ := fun g => conj (F g)
  let X : Submodule ℂ (GA D s.V → ℂ) := Submodule.span ℂ (Set.range fun a => ρ0 a cy)
  have hX : ∀ a, ∀ z ∈ X, ρ0 a z ∈ X := by
    intro a z hz
    have hle : Submodule.map (ρ0 a) X ≤ X := by
      rw [Submodule.map_span_le]
      rintro _ ⟨b, rfl⟩
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨a * b, rfl⟩
    exact hle ⟨z, hz, rfl⟩
  let ρ : Representation ℂ (GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)) X := GlobalTheory.PRep.sub ρ0 X hX
  have hcy : cy ∈ X := Submodule.subset_span ⟨1, by simp⟩
  have hXp : ∀ z ∈ X, (∀ u', IsThetaFunO c.ψ s.V s'.V u' → ∀ y, IntegrableOn (fun g => thetaKO p.ω g y u' * z g) s.fd s.ν) ∧
      (∀ γ ∈ GQ s.V, ∀ g, z (γ * g) = z g) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      refine ⟨fun u' hu' y => GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_mul_conj_integrableOn hP D c.ψ s.V s'.V (c.chS (k + 1))
        (c.chT (k + 1)) p.ω hp.weil c.θ hθ s.ν s.fd hHaar hFund u' F hu' hFa.1 hFa.2 (ι a) y, fun γ hγ g => ?_⟩
      show conj (F (γ * g * ι a)) = conj (F (g * ι a))
      rw [mul_assoc]
      exact congrArg conj (hFa.1.left γ hγ _)
    | zero => exact ⟨fun u' _ y => by simp, fun _ _ _ => rfl⟩
    | add z z' _ _ h1 h2 =>
      refine ⟨fun u' hu' y => ?_, fun γ hγ g => by simp [h1.2 γ hγ, h2.2 γ hγ]⟩
      rw [show (fun g => thetaKO p.ω g y u' * (z + z') g) = fun g => thetaKO p.ω g y u' * z g + thetaKO p.ω g y u' * z' g from
        funext fun g => by simp [mul_add]]
      exact (h1.1 u' hu' y).add (h2.1 u' hu' y)
    | smul a z _ h1 =>
      refine ⟨fun u' hu' y => ?_, fun γ hγ g => by simp [h1.2 γ hγ]⟩
      rw [show (fun g => thetaKO p.ω g y u' * (a • z) g) = fun g => a * (thetaKO p.ω g y u' * z g) from
        funext fun g => by simp [mul_left_comm]]
      exact (h1.1 u' hu' y).const_mul a
  let bf : W → X → GA D s'.V → ℂ := fun u' z y => ∫ g in s.fd, thetaKO p.ω g y (T u') * (z : GA D s.V → ℂ) g ∂s.ν
  let b : W →ₗ[ℂ] X →ₗ[ℂ] (GA D s'.V → ℂ) := LinearMap.mk₂ ℂ bf
    (fun u₁ u₂ z => by
      funext y
      show _ = bf u₁ z y + bf u₂ z y
      simp only [bf, ← integral_add ((hXp z z.2).1 _ (hTθ u₁) y) ((hXp z z.2).1 _ (hTθ u₂) y)]
      congr 1; funext g
      simp [thetaKO, add_mul])
    (fun a u₁ z => by
      funext y
      show _ = a * bf u₁ z y
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [thetaKO, mul_assoc])
    (fun u₁ z z' => by
      funext y
      show _ = bf u₁ z y + bf u₁ z' y
      simp only [bf, ← integral_add ((hXp z z.2).1 _ (hTθ u₁) y) ((hXp z' z'.2).1 _ (hTθ u₁) y)]
      congr 1; funext g
      simp [mul_add])
    (fun a u₁ z => by
      funext y
      show _ = a * bf u₁ z y
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [mul_left_comm])
  have hb : ∀ g h (u₁ : W) (z : X), b ⟨GlobalTheory.ParHecke.omTwo μS μT g h u₁, hW g h u₁ u₁.2⟩ (ρ g z) =
      (GlobalTheory.PRep.rightReg ℂ (GA D s'.V) ℂ).comp ι' h (b u₁ z) := by
    intro a a' u₁ z
    funext y
    show ∫ g in s.fd, thetaKO p.ω g y (T ⟨GlobalTheory.ParHecke.omTwo μS μT a a' u₁, hW a a' u₁ u₁.2⟩) * (z : GA D s.V → ℂ) (g * ι a) ∂s.ν =
      ∫ g in s.fd, thetaKO p.ω g (y * ι' a') (T u₁) * (z : GA D s.V → ℂ) g ∂s.ν
    rw [← hTω a a' u₁]
    simp_rw [thetaKO_om_apply]
    exact GlobalTheory.ChainOnto.setIntegral_fd_mul_right D s.V s.ν s.fd hHaar hFund
      (fun g => thetaKO p.ω g (y * ι' a') (T u₁) * (z : GA D s.V → ℂ) g)
      (fun γ hγ g => by simp only [thetaKO_left hp.weil (hTθ u₁) γ hγ, (hXp z z.2).2 γ hγ]) (ι a)
  have hx0 : GlobalTheory.ParHecke.IsGen ρ ξl ϖ (qPar c PP x k) ⟨cy, hcy⟩ :=
    isGen_of_injective X.subtype (fun _ _ => rfl) Subtype.val_injective hsrc
  have key := GlobalTheory.T.lowerBlockParameter_transfer_invariantPairing (Fv D.host.F v) (Fin D.R.r) (Blocks k D.R.t) (Blocks (k + 1) D.R.t) ϖ hϖ D.R.t hcard ξl μS μT
    htame hunS hunT W hW hΦ X ρ ⟨cy, hcy⟩ (qPar c PP x k) hx0 (GA D s'.V → ℂ) ((GlobalTheory.PRep.rightReg ℂ (GA D s'.V) ℂ).comp ι') b hb
  have hval : b ⟨GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.datum ξl⁻¹, hΦ⟩ ⟨cy, hcy⟩ = fun y => conj (p.up φ F y) := by
    funext y
    show ∫ g in s.fd, thetaKO p.ω g y (T ⟨GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.datum ξl⁻¹, hΦ⟩) * conj (F g) ∂s.ν =
      conj (∫ g in s.fd, conj (thetaKO p.ω g y (p.pt φ)) * F g ∂s.ν)
    rw [hT0, ← integral_conj]
    congr 1; funext g; simp
  rw [hval, hSϖ, hTϖ, ← seg_eq_segL φv PP hφv hϖ] at key
  exact key

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpLowerBlockParameterProofStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainThetaLiftUpLowerBlockParameter_proof : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, UpQ D := by
  first | exact @GlobalTheory.ChainTw.upQ_holds | exact GlobalTheory.ChainTw.upQ_holds | (intros; apply GlobalTheory.ChainTw.upQ_holds <;> assumption)
end
end
