module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalLatticeExistsScalarBoundAttained
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalLatticeExistsScalarBoundAttained
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

namespace GlobalTheory

theorem lattice_exists_scalar_bound_attained : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (L : Submodule 𝒪[k] (n → k)), L.IsFullLattice k → Nonempty n → ∃ c : k, c ≠ 0 ∧ (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ x ∈ L, ∃ j, x j = c := by
  intro k _ _ _ _ n _ L hL hn
  obtain ⟨s, hs⟩ := hL.fg

  have hex : ∃ x ∈ s, ∃ j, x j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hbot : L = ⊥ := by
      rw [← hs, Submodule.span_eq_bot]
      intro x hx
      funext j
      exact hcon x hx j
    have htop := hL.span_eq_top
    rw [hbot] at htop
    simp only [Submodule.bot_coe, Submodule.span_zero_singleton] at htop
    obtain ⟨j⟩ := hn
    have h1 : (Pi.single j (1 : k) : n → k) ∈ (⊤ : Submodule k (n → k)) := Submodule.mem_top
    rw [← htop, Submodule.mem_bot] at h1
    have := congrFun h1 j
    simp at this
  obtain ⟨x0, hx0, j0, hx0j⟩ := hex
  have hne : (s ×ˢ (Finset.univ : Finset n)).Nonempty := ⟨(x0, j0), by simp [hx0]⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (s ×ˢ (Finset.univ : Finset n))
    (fun q : (n → k) × n => valuation k (q.1 q.2)) hne
  have hc : p.1 p.2 ≠ 0 := by
    intro h0
    have := hmax (x0, j0) (by simp [hx0])
    simp only [h0, map_zero] at this
    have h' : valuation k (x0 j0) = 0 := le_antisymm this zero_le'
    exact hx0j ((Valuation.zero_iff _).mp h')
  refine ⟨p.1 p.2, hc, ?_, p.1, ?_, p.2, rfl⟩
  · intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      intro j
      show valuation k ((p.1 p.2)⁻¹ * y j) ≤ 1
      have hle := hmax (y, j) (by simpa using hy)
      simp only at hle
      have hvc : valuation k (p.1 p.2) ≠ 0 := by simpa using hc
      rw [map_mul, map_inv₀]
      calc (valuation k (p.1 p.2))⁻¹ * valuation k (y j)
          ≤ (valuation k (p.1 p.2))⁻¹ * valuation k (p.1 p.2) := by gcongr
        _ = 1 := inv_mul_cancel₀ hvc
    | zero => intro j; simp
    | add y z _ _ hy hz =>
      intro j
      simpa [mul_add] using add_mem (hy j) (hz j)
    | smul a y _ hy =>
      intro j
      have := mul_mem a.2 (hy j)
      convert this using 1
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      ring
  · rw [← hs]
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_product.mp hp).1)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalLatticeExistsScalarBoundAttainedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLattice_exists_scalar_bound_attained : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (L : Submodule 𝒪[k] (n → k)), L.IsFullLattice k → Nonempty n → ∃ c : k, c ≠ 0 ∧ (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ x ∈ L, ∃ j, x j = c := by
  exact @_root_.GlobalTheory.lattice_exists_scalar_bound_attained
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionStableLocalLatticeShape
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionStableLocalLatticeShape
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

theorem GlobalTheory.LatPairStab.stable_lattice_shape : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (L : Submodule 𝒪[k] (n → k)) (c : k), 3 ≤ Fintype.card n → c ≠ 0 → (∀ x ∈ L, ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → x + Pi.single b ((t : k) * x d) ∈ L) → (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∃ x ∈ L, ∃ j, x j = c) → (∀ x : n → k, x ∈ L ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∨ (∀ x : n → k, x ∈ L ↔ (∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ s : 𝒪[k], s ∈ IsLocalRing.maximalIdeal 𝒪[k] ∧ (s : k) = c⁻¹ * x i) := by
  intro k _ _ _ _ n _ _ i L c hcard hc hcl hbd hex
  obtain ⟨x₀, hx₀, j, hj⟩ := hex
  obtain ⟨a, hai, haj⟩ : ∃ a, a ≠ i ∧ a ≠ j := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset n) ⊆ {i, j} := fun b _ => by
      by_cases hbi : b = i
      · simp [hbi]
      · simp [h b hbi]
    have h1 := Finset.card_le_card hsub
    have h2 : ({i, j} : Finset n).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ] at h1
    omega

  have hsm : ∀ (s : 𝒪[k]) (b : n) (y : k), (s • (Pi.single b y : n → k) : n → k) = (Pi.single b ((s : k) * y) : n → k) := by
    intro s b y
    ext m
    by_cases hm : m = b
    · subst hm; simp [Subring.smul_def]
    · simp [hm, Subring.smul_def]

  have ha : ∀ t : 𝒪[k], Pi.single a ((t : k) * c) ∈ L := by
    intro t
    have h := L.sub_mem (hcl x₀ hx₀ a j t haj (Or.inl hai)) hx₀
    simpa [hj] using h
  have hca : Pi.single a c ∈ L := by simpa using ha 1

  have hsing : ∀ b, b ≠ i → ∀ t : 𝒪[k], Pi.single b ((t : k) * c) ∈ L := by
    intro b hbi t
    by_cases hba : b = a
    · subst hba; exact ha t
    · have h := L.sub_mem (hcl (Pi.single a c) hca b a t hba (Or.inl hbi)) hca
      simpa using h

  have hi : ∀ t : 𝒪[k], t ∈ IsLocalRing.maximalIdeal 𝒪[k] → Pi.single i ((t : k) * c) ∈ L := by
    intro t ht
    have h := L.sub_mem (hcl (Pi.single a c) hca i a t (Ne.symm hai) (Or.inr ht)) hca
    simpa [Ne.symm hai] using h

  have hsum : ∀ x : n → k, (∀ b, Pi.single b (x b) ∈ L) → x ∈ L := by
    intro x h
    rw [← Finset.univ_sum_single x]
    exact L.sum_mem (fun b _ => h b)
  have hoff : ∀ x : n → k, (∀ j, c⁻¹ * x j ∈ 𝒪[k]) → ∀ b, b ≠ i → Pi.single b (x b) ∈ L := by
    intro x hx b hb
    have e : x b = (c⁻¹ * x b) * c := by field_simp
    rw [e]
    exact hsing b hb ⟨_, hx b⟩
  by_cases hci : Pi.single i c ∈ L
  · left
    intro x
    refine ⟨hbd x, fun hx => hsum x fun b => ?_⟩
    by_cases hb : b = i
    · subst hb
      have e : Pi.single b (x b) = ((⟨c⁻¹ * x b, hx b⟩ : 𝒪[k]) • (Pi.single b c : n → k) : n → k) := by
        rw [hsm]; congr 1; show x b = (c⁻¹ * x b) * c; field_simp
      rw [e]; exact L.smul_mem _ hci
    · exact hoff x hx b hb
  · right
    have hm : ∀ x (hx : x ∈ L), (⟨c⁻¹ * x i, hbd x hx i⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      intro x hx
      by_contra hu
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hu
      obtain ⟨v, hv⟩ := hu

      have hy : x - Pi.single i (x i) ∈ L := by
        apply hsum
        intro b
        by_cases hb : b = i
        · subst hb; simp
        · have := hoff x (hbd x hx) b hb
          simpa [hb] using this
      have hxi : Pi.single i (x i) ∈ L := by
        have := L.sub_mem hx hy
        simpa using this
      apply hci
      have h1 : ((↑(v⁻¹) : 𝒪[k]) * (v : 𝒪[k])) = 1 := Units.inv_mul v
      rw [hv] at h1
      have h2 := congrArg (fun z : 𝒪[k] => (z : k)) h1
      simp only [Subring.coe_mul, OneMemClass.coe_one] at h2
      set w : k := ((↑(v⁻¹) : 𝒪[k]) : k)
      have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
      have e : Pi.single i c = ((↑(v⁻¹) : 𝒪[k]) • (Pi.single i (x i) : n → k) : n → k) := by
        rw [hsm]; congr 1
        show c = w * x i
        linear_combination -(c * h2) + (w * x i) * hcc
      rw [e]; exact L.smul_mem _ hxi
    intro x
    constructor
    · intro hx
      exact ⟨hbd x hx, ⟨c⁻¹ * x i, hbd x hx i⟩, hm x hx, rfl⟩
    · rintro ⟨hx, s, hs, hsx⟩
      refine hsum x fun b => ?_
      by_cases hb : b = i
      · subst hb
        have e : x b = (s : k) * c := by rw [hsx]; field_simp
        rw [e]; exact hi s hs
      · exact hoff x hx b hb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionStableLocalLatticeShapeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvectionStable_localLattice_shape : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (L : Submodule 𝒪[k] (n → k)) (c : k), 3 ≤ Fintype.card n → c ≠ 0 → (∀ x ∈ L, ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → x + Pi.single b ((t : k) * x d) ∈ L) → (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∃ x ∈ L, ∃ j, x j = c) → (∀ x : n → k, x ∈ L ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∨ (∀ x : n → k, x ∈ L ↔ (∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ s : 𝒪[k], s ∈ IsLocalRing.maximalIdeal 𝒪[k] ∧ (s : k) = c⁻¹ * x i) := by
  first | exact @GlobalTheory.LatPairStab.stable_lattice_shape | exact GlobalTheory.LatPairStab.stable_lattice_shape | (intros; apply GlobalTheory.LatPairStab.stable_lattice_shape <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionInvariantPairFunctionalResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionInvariantPairFunctionalResidue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

namespace GlobalTheory

theorem latPair_hasVal_residue_of_transvections : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (P : GlobalTheory.LatPair.Pair k n) (c : k), 2 ≤ Fintype.card n → c ≠ 0 → (∀ x : n → k, x ∈ P.lat ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∀ (x : n → k) (a : 𝓀[k]), P.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → P.HasVal (x + Pi.single b ((t : k) * x d)) a) → ∃ ε : 𝓀[k], ε ≠ 0 ∧ ∀ (x : n → k) (hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k]), P.HasVal x (IsLocalRing.residue 𝒪[k] ⟨c⁻¹ * x i, hx i⟩ * ε) := by
  intro k _ _ _ _ n _ _ i P c _hcard hc hlat hcl
  classical
  set e : n → (n → k) := fun b => c • (Pi.single b (1:k) : n → k) with he_def
  have hcoef : ∀ b j, c⁻¹ * e b j = (Pi.single b (1:k) : n → k) j := by
    intro b j
    by_cases h : j = b
    · subst h; simp [he_def, hc]
    · simp [he_def, Pi.single_apply, h]
  have hmem : ∀ b, e b ∈ P.lat := fun b => (hlat _).2 (fun j => by
    rw [hcoef]
    by_cases h : j = b
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · simp only [Pi.single_apply, h, if_false]; exact zero_mem _)
  let v : n → 𝓀[k] := fun b => P.fn ⟨e b, hmem b⟩
  have hv : ∀ b, P.HasVal (e b) (v b) := fun b => P.hasVal_fn ⟨e b, hmem b⟩
  have hzero : ∀ a, a ≠ i → v a = 0 := by
    intro a ha
    have h1 := hcl (e i) (v i) (hv i) a i 1 ha (Or.inl ha)
    have h2 : e i + Pi.single a (((1:𝒪[k]) : k) * e i i) = e i + e a := by
      congr 1
      funext j
      by_cases h : j = a
      · subst h; simp [he_def]
      · simp [he_def, Pi.single_apply, h]
    rw [h2] at h1
    have h3 := h1.sub (hv i)
    rw [add_sub_cancel_left, sub_self] at h3
    exact (hv a).unique h3
  have hsum : ∀ (s : n → 𝒪[k]) (S : Finset n),
      P.HasVal (∑ b ∈ S, s b • e b) (∑ b ∈ S, IsLocalRing.residue 𝒪[k] (s b) * v b) := by
    intro s S
    induction S using Finset.induction_on with
    | empty => simpa using (hv i).sub (hv i)
    | insert b S hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb]
      exact ((hv b).smul (s b)).add ih
  have hval : ∀ (x : n → k) (hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k]),
      P.HasVal x (IsLocalRing.residue 𝒪[k] ⟨c⁻¹ * x i, hx i⟩ * v i) := by
    intro x hx
    let s : n → 𝒪[k] := fun b => ⟨c⁻¹ * x b, hx b⟩
    have hx' : (∑ b, s b • e b) = x := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · change ((s j : 𝒪[k]) : k) * (c * (Pi.single j (1:k) : n → k) j) = x j
        simp only [s, Pi.single_eq_same, mul_one]
        field_simp
      · intro b _ hb
        change ((s b : 𝒪[k]) : k) * (c * (Pi.single b (1:k) : n → k) j) = 0
        simp [Pi.single_apply, Ne.symm hb]
      · simp
    have := hsum s Finset.univ
    rw [hx', Finset.sum_eq_single i (fun b _ hb => by rw [hzero b hb, mul_zero]) (by simp)] at this
    exact this
  refine ⟨v i, ?_, hval⟩
  intro h0
  apply P.fn_ne
  refine LinearMap.ext fun y => ?_
  have := hval y ((hlat y).1 y.2)
  rw [h0, mul_zero] at this
  exact (P.hasVal_fn y).unique this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionInvariantPairFunctionalResidueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvectionInvariant_pair_functional_residue : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (P : GlobalTheory.LatPair.Pair k n) (c : k), 2 ≤ Fintype.card n → c ≠ 0 → (∀ x : n → k, x ∈ P.lat ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∀ (x : n → k) (a : 𝓀[k]), P.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → P.HasVal (x + Pi.single b ((t : k) * x d)) a) → ∃ ε : 𝓀[k], ε ≠ 0 ∧ ∀ (x : n → k) (hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k]), P.HasVal x (IsLocalRing.residue 𝒪[k] ⟨c⁻¹ * x i, hx i⟩ * ε) := by
  first | exact @GlobalTheory.latPair_hasVal_residue_of_transvections | exact GlobalTheory.latPair_hasVal_residue_of_transvections | (intros; apply GlobalTheory.latPair_hasVal_residue_of_transvections <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NoTransvectionInvariantPairOnScaledKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NoTransvectionInvariantPairOnScaledKernel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

noncomputable section
namespace GlobalTheory.LatPair

theorem no_pair_on_scaled_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (P : GlobalTheory.LatPair.Pair k n) (c : k), 3 ≤ Fintype.card n → c ≠ 0 → (∀ x : n → k, x ∈ P.lat ↔ (∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ s : 𝒪[k], s ∈ IsLocalRing.maximalIdeal 𝒪[k] ∧ (s : k) = c⁻¹ * x i) → (∀ (x : n → k) (a : 𝓀[k]), P.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → P.HasVal (x + Pi.single b ((t : k) * x d)) a) → False := by
  intro k _ _ _ _ n _ _ i P c hn hc hlat hcl
  have hmem : ∀ b, b ≠ i → Pi.single b c ∈ P.lat := by
    intro b hb
    rw [hlat]
    refine ⟨fun j => ?_, ⟨0, zero_mem _, ?_⟩⟩
    · by_cases h : j = b
      · subst h; simp [hc]
      · rw [Pi.single_eq_of_ne h]; simp
    · rw [Pi.single_eq_of_ne (Ne.symm hb)]; simp
  have hzero : ∀ a, a ≠ i → P.HasVal (Pi.single a c) 0 := by
    intro a ha
    obtain ⟨d, hda, hdi⟩ : ∃ d, d ≠ a ∧ d ≠ i := by
      by_contra h
      push_neg at h
      have hsub : (Finset.univ : Finset n) ⊆ {a, i} := fun d _ => by
        by_cases hd : d = a
        · simp [hd]
        · simp [h d hd]
      have h1 := Finset.card_le_card hsub
      have h2 : ({a, i} : Finset n).card ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ] at h1
      omega
    obtain ⟨v, hv⟩ := (Pair.mem_lat_iff (P := P)).1 (hmem d hdi)
    obtain ⟨w, hw⟩ := (Pair.mem_lat_iff (P := P)).1 (hmem a ha)
    have h1 := hcl _ _ hv a d 1 (Ne.symm hda) (Or.inl ha)
    have hx : (Pi.single d c + Pi.single a (((1 : 𝒪[k]) : k) * (Pi.single d c : n → k) d) : n → k) = Pi.single d c + Pi.single a c := by
      simp
    rw [hx] at h1
    have h3 := h1.unique (hv.add hw)
    have hw0 : w = 0 := by linear_combination -h3
    exact hw0 ▸ hw
  obtain ⟨a, ha⟩ : ∃ a, a ≠ i := by
    by_contra h
    push_neg at h
    have : Fintype.card n ≤ 1 := Fintype.card_le_one_iff.2 (fun x y => (h x).trans (h y).symm)
    omega
  have hzi : ∀ t : 𝒪[k], t ∈ IsLocalRing.maximalIdeal 𝒪[k] → P.HasVal (Pi.single i ((t : k) * c)) 0 := by
    intro t ht
    have h1 := hcl _ _ (hzero a ha) i a t (Ne.symm ha) (Or.inr ht)
    rw [Pi.single_eq_same] at h1
    simpa using h1.sub (hzero a ha)
  apply P.fn_ne
  ext ⟨x, hx⟩
  obtain ⟨hxj, s, hs, hsx⟩ := (hlat x).1 hx
  have hsing : ∀ b, P.HasVal (Pi.single b (x b)) 0 := by
    intro b
    by_cases hb : b = i
    · subst hb
      have he : (s : k) * c = x b := by rw [hsx]; field_simp
      simpa [he] using hzi s hs
    · have h := (hzero b hb).smul ⟨c⁻¹ * x b, hxj b⟩
      have he : (⟨c⁻¹ * x b, hxj b⟩ : 𝒪[k]) • (Pi.single b c : n → k) = Pi.single b (x b) := by
        rw [← Pi.single_smul']; congr 1; change (c⁻¹ * x b) * c = x b; field_simp
      simpa [he] using h
  have hsum : P.HasVal (∑ b, Pi.single b (x b)) 0 :=
    Finset.sum_induction _ (fun y => P.HasVal y 0) (fun _ _ h h' => by simpa using h.add h')
      ⟨P.lat.zero_mem, map_zero P.fn⟩ (fun b _ => hsing b)
  rw [Finset.univ_sum_single] at hsum
  rw [LinearMap.zero_apply]
  exact hsum.2

end GlobalTheory.LatPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NoTransvectionInvariantPairOnScaledKernelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.no_transvectionInvariant_pair_on_scaledKernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (P : GlobalTheory.LatPair.Pair k n) (c : k), 3 ≤ Fintype.card n → c ≠ 0 → (∀ x : n → k, x ∈ P.lat ↔ (∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ s : 𝒪[k], s ∈ IsLocalRing.maximalIdeal 𝒪[k] ∧ (s : k) = c⁻¹ * x i) → (∀ (x : n → k) (a : 𝓀[k]), P.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → P.HasVal (x + Pi.single b ((t : k) * x d)) a) → False := by
  first | exact @GlobalTheory.LatPair.no_pair_on_scaled_kernel | exact GlobalTheory.LatPair.no_pair_on_scaled_kernel | (intros; apply GlobalTheory.LatPair.no_pair_on_scaled_kernel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeResiduePairEqScalarOfSameStabilizer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

noncomputable section

namespace GlobalTheory.LatPair.StabScal

section SlopeTestRemainingChoices
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]

def scal (s : k) (hs : s ≠ 0) : GL n k :=
  ⟨s • 1, s⁻¹ • 1, by rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hs, one_smul],
    by rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hs, one_smul]⟩

theorem scal_inv_smul (s : k) (hs : s ≠ 0) (x : n → k) : (scal s hs : GL n k)⁻¹ • x = s⁻¹ • x := by
  show (s⁻¹ • (1 : Matrix n n k)) *ᵥ x = _
  rw [Matrix.smul_mulVec, one_mulVec]

theorem scal_comm (s : k) (hs : s ≠ 0) (h : GL n k) : h * scal s hs = scal s hs * h := by
  ext1
  show h.val * (s • (1 : Matrix n n k)) = (s • (1 : Matrix n n k)) * h.val
  rw [mul_smul_comm, mul_one, smul_mul_assoc, one_mul]

def trv (b d : n) (t : k) (hbd : b ≠ d) : GL n k :=
  ⟨Matrix.transvection b d t, Matrix.transvection b d (-t),
   by rw [Matrix.transvection_mul_transvection_same b d hbd, add_neg_cancel, Matrix.transvection_zero],
   by rw [Matrix.transvection_mul_transvection_same b d hbd, neg_add_cancel, Matrix.transvection_zero]⟩

theorem transvection_mulVec' (b d : n) (t : k) (x : n → k) :
    Matrix.transvection b d t *ᵥ x = x + Pi.single b (t * x d) := by
  ext j
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.single_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, ite_and]
  by_cases h : b = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem trv_inv_smul (b d : n) (t : k) (hbd : b ≠ d) (x : n → k) :
    (trv b d t hbd)⁻¹ • x = x + Pi.single b (-t * x d) := transvection_mulVec' b d (-t) x

end SlopeTestRemainingChoices

theorem transvection_smul_stdPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i b d : n) (t : 𝒪[k]) (g : GL n k), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → g.val = Matrix.transvection b d (t : k) → g • GlobalTheory.LatPair.stdPair k i = GlobalTheory.LatPair.stdPair k i := by
  intro k _ _ _ _ n _ _ i b d t g hbd hbi hg
  have hinv : (g⁻¹ : GL n k).val = Matrix.transvection b d (-(t : k)) := by
    have h1 : (g⁻¹ : GL n k).val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g⁻¹ : GL n k).val = (g⁻¹ : GL n k).val * (g.val * Matrix.transvection b d (-(t : k))) := by
          rw [hg, Matrix.transvection_mul_transvection_same b d hbd, add_neg_cancel, Matrix.transvection_zero,
            mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have htO : (t : k) ∈ 𝒪[k] := t.2
  refine Pair.ext fun x a => ?_
  let y : n → k := x + Pi.single b (-(t : k) * x d)
  have hyj : ∀ j, y j = x j + (Pi.single b (-(t : k) * x d) : n → k) j := fun j => rfl
  have hsm : g⁻¹ • x = y := by
    show (g⁻¹ : GL n k).val *ᵥ x = _
    rw [hinv, transvection_mulVec']
  rw [Pair.smul_hasVal, hsm, stdPair_hasVal, stdPair_hasVal]
  have hd : y d = x d := by rw [hyj]; simp [Pi.single_apply, Ne.symm hbd]
  have hint : (∀ j, y j ∈ 𝒪[k]) ↔ ∀ j, x j ∈ 𝒪[k] := by
    constructor
    · intro hy j
      have hxd : x d ∈ 𝒪[k] := by rw [← hd]; exact hy d
      have : x j = y j + (Pi.single b ((t : k) * x d) : n → k) j := by
        rw [hyj]
        simp only [Pi.single_apply]
        split_ifs <;> ring
      rw [this]
      refine add_mem (hy j) ?_
      rw [Pi.single_apply]
      split_ifs
      · exact mul_mem htO hxd
      · exact zero_mem _
    · intro hx j
      rw [hyj, Pi.single_apply]
      split_ifs
      · exact add_mem (hx j) (mul_mem (neg_mem htO) (hx d))
      · simpa using hx j
  have hres : ∀ (hx : ∀ j, x j ∈ 𝒪[k]) (hy : ∀ j, y j ∈ 𝒪[k]),
      IsLocalRing.residue 𝒪[k] ⟨y i, hy i⟩ = IsLocalRing.residue 𝒪[k] ⟨x i, hx i⟩ := by
    intro hx hy
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    by_cases hb : b = i
    · subst hb
      have hm : t ∈ IsLocalRing.maximalIdeal 𝒪[k] := hbi.resolve_left (not_not.2 rfl)
      have : (⟨y b, hy b⟩ : 𝒪[k]) - ⟨x b, hx b⟩ = -(t * ⟨x d, hx d⟩) := by
        apply Subtype.ext
        push_cast
        rw [hyj, Pi.single_eq_same]
        ring
      rw [this]
      exact neg_mem (Ideal.mul_mem_right _ _ hm)
    · have : (⟨y i, hy i⟩ : 𝒪[k]) - ⟨x i, hx i⟩ = 0 := by
        apply Subtype.ext
        show y i - x i = 0
        rw [hyj]
        simp [Pi.single_apply, Ne.symm hb]
      rw [this]
      exact zero_mem _
  constructor
  · rintro ⟨hy, rfl⟩
    exact ⟨hint.1 hy, (hres _ hy).symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨hint.2 hx, hres hx _⟩

theorem eq_scalar_smul_of_stab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (P P' : GlobalTheory.LatPair.Pair k n), 3 ≤ Fintype.card n → (∀ g : GL n k, g • P = P ↔ g • P' = P') → ∃ (g : GL n k) (s : k), s ≠ 0 ∧ g.val = s • (1 : Matrix n n k) ∧ P' = g • P := by
  intro k _ _ _ _ n _ _ P P' hn hst
  obtain ⟨i⟩ : Nonempty n := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (GL n k) (stdPair k i) P
  set Q := h⁻¹ • P' with hQ
  clear_value Q
  have hstQ : ∀ g : GL n k, g • stdPair k i = stdPair k i → g • Q = Q := by
    intro g hg
    have h1 : (h * g * h⁻¹) • P = P := by rw [← hh, smul_smul, show h * g * h⁻¹ * h = h * g by group, mul_smul, hg]
    have h2 := (hst _).1 h1
    rw [hQ, smul_smul]
    calc (g * h⁻¹) • P' = h⁻¹ • (h * g * h⁻¹) • P' := by rw [smul_smul]; congr 1; group
      _ = h⁻¹ • P' := by rw [h2]
  have hcl : ∀ (x : n → k) (a : 𝓀[k]), Q.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d →
      (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → Q.HasVal (x + Pi.single b ((t : k) * x d)) a := by
    intro x a hx b d t hbd hbi
    have hg : trv b d ((-t : 𝒪[k]) : k) hbd • stdPair k i = stdPair k i :=
      transvection_smul_stdPair k n i b d (-t) _ hbd (hbi.imp id (fun h => (IsLocalRing.maximalIdeal 𝒪[k]).neg_mem_iff.2 h)) rfl
    have h2 : (trv b d ((-t : 𝒪[k]) : k) hbd • Q).HasVal x a := by rw [hstQ _ hg]; exact hx
    rw [Pair.smul_hasVal, trv_inv_smul] at h2
    convert h2 using 3
    push_cast
    ring
  have hlat : ∀ x ∈ Q.lat, ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) →
      x + Pi.single b ((t : k) * x d) ∈ Q.lat := fun x hx b d t hbd hbi =>
    (hcl x _ (Q.hasVal_fn ⟨x, hx⟩) b d t hbd hbi).mem
  have hbound : ∃ c : k, c ≠ 0 ∧ (∀ x ∈ Q.lat, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧
      ∃ x ∈ Q.lat, ∃ j, x j = c := by
    first
    | exact GlobalTheory.T.localLattice_exists_scalar_bound_attained k n Q.lat Q.isLat ⟨i⟩
    | exact GlobalTheory.T.localLattice_exists_scalar_bound_attained k n Q.lat Q.isLat.toIsLattice ⟨i⟩
  obtain ⟨c, hc0, hcb, hca⟩ := hbound
  rcases GlobalTheory.T.transvectionStable_localLattice_shape k n i Q.lat c hn hc0 hlat hcb hca with hA | hB
  swap
  · exact (GlobalTheory.T.no_transvectionInvariant_pair_on_scaledKernel k n i Q c hn hc0 hB hcl).elim
  obtain ⟨ε, hε0, hε⟩ := GlobalTheory.T.transvectionInvariant_pair_functional_residue k n i Q c (by omega) hc0 hA hcl
  obtain ⟨w, hw⟩ := IsLocalRing.residue_surjective (R := 𝒪[k]) ε
  have hwu : IsUnit w := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, hw]
    exact hε0
  obtain ⟨u, hu⟩ := hwu
  have huw : (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) * (w : k) = 1 := by
    have h1 : ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) * w = 1 := by rw [← hu, Units.inv_mul]
    have h2 := congrArg (fun z : 𝒪[k] => (z : k)) h1
    simpa using h2
  have hw0 : (w : k) ≠ 0 := fun h0 => by simp [h0] at huw
  have hint : ∀ y : k, (w : k) * y ∈ 𝒪[k] → y ∈ 𝒪[k] := by
    intro y hy
    have : y = (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) * ((w : k) * y) := by rw [← mul_assoc, huw, one_mul]
    rw [this]
    exact mul_mem (u⁻¹ : 𝒪[k]ˣ).val.2 hy
  set s := c * (w : k)⁻¹ with hs_def
  have hs : s ≠ 0 := mul_ne_zero hc0 (inv_ne_zero hw0)
  have key : ∀ y : k, s⁻¹ * y = (w : k) * (c⁻¹ * y) := by
    intro y
    rw [hs_def, mul_inv, inv_inv]
    ring
  have hQs : Q = (scal s hs : GL n k) • stdPair k i := by
    refine Pair.ext fun x a => ?_
    rw [Pair.smul_hasVal, stdPair_hasVal, scal_inv_smul]
    constructor
    · intro hQx
      have hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k] := (hA x).1 hQx.mem
      refine ⟨fun j => ?_, ?_⟩
      · rw [Pi.smul_apply, smul_eq_mul, key]
        exact mul_mem w.2 (hx j)
      · rw [hQx.unique (hε x hx), ← hw, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Pi.smul_apply, smul_eq_mul, key]
        push_cast
        ring
    · rintro ⟨hx', rfl⟩
      have hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k] := fun j => hint _ (by have := hx' j; rwa [Pi.smul_apply, smul_eq_mul, key] at this)
      convert hε x hx using 1
      rw [← hw, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Pi.smul_apply, smul_eq_mul, key]
      push_cast
      ring
  refine ⟨(scal s hs : GL n k), s, hs, rfl, ?_⟩
  calc P' = h • Q := by rw [hQ, smul_inv_smul]
    _ = h • (scal s hs : GL n k) • stdPair k i := by rw [hQs]
    _ = (scal s hs : GL n k) • P := by rw [← hh, smul_smul, smul_smul, scal_comm]

end GlobalTheory.LatPair.StabScal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeResiduePairEqScalarOfSameStabilizerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeResiduePair_eq_scalar_of_same_stabilizer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (P P' : GlobalTheory.LatPair.Pair k n), 3 ≤ Fintype.card n → (∀ g : GL n k, g • P = P ↔ g • P' = P') → ∃ (g : GL n k) (s : k), s ≠ 0 ∧ g.val = s • (1 : Matrix n n k) ∧ P' = g • P := by
  first | exact @GlobalTheory.LatPair.StabScal.eq_scalar_smul_of_stab | exact GlobalTheory.LatPair.StabScal.eq_scalar_smul_of_stab | (intros; apply GlobalTheory.LatPair.StabScal.eq_scalar_smul_of_stab <;> assumption)
end
