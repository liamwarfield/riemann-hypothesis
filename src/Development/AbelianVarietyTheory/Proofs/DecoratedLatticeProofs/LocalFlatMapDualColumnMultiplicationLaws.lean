module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CapelliLowestGelfandConj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapDualColumnMultiplicationLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapDualColumnMultiplicationLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section

namespace GlobalTheory.FlatColLaw

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_iota (p : Place D k) (x : k) : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]

theorem iota_mul (p : Place D k) (x : k) (m : AE D) : p.ι x * m = p.ι (x * p.π m) := by
  have h2 := p.ι_π (p.ι x * m)
  rw [map_mul, p.π_ι] at h2
  rw [h2, ← mul_assoc, e_iota]

theorem xi_ne (p : Place D k) : p.xi ≠ 0 := by
  have h : p.xi * p.pr D.host.xi0⁻¹ = 1 := by
    rw [Place.xi, Place.pr, Place.pr, ← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one,
      map_one]
  exact left_ne_zero_of_mul_eq_one h

theorem map_iota_mul (p : Place D k) {a b c : ℕ} (zk : Matrix (Fin a) (Fin b) k) (x : Mx D b c) :
    (zk.map p.ι : Mx D a b) ⬝ x = (zk * x.map p.π).map p.ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, iota_mul]

theorem trace_map_iota (p : Place D k) {a : ℕ} (x : Matrix (Fin a) (Fin a) k) :
    (x.map p.ι : Mx D a a).trace = p.ι x.trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem map_iota_pi (p : Place D k) {a b : ℕ} (x : Matrix (Fin a) (Fin b) k) : (x.map p.ι).map p.π = x := by
  ext i j
  exact p.π_ι _

theorem hO_extY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (w : WO S T) (a : Mx D T.rank ρ) :
    hO S T w (d.extY T a) = pairS T (w ⬝ d.jX) a := by
  rw [d.hO_coordS]
  simp only [HypDec.extY_apply, Matrix.mul_assoc, HypDec.pY_jY, HypDec.pY_j0, HypDec.pY_jX, Matrix.mul_one,
    Matrix.mul_zero, pairS, hO_eq_trace S₀, adj_zero, Matrix.zero_mul, trace_zero, add_zero]

theorem pairS_giA_adj (T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) (z : Mx D ρ T.rank) :
    pairS T x (giA T ⬝ adj z) = (z ⬝ x).trace := by
  rw [pairS, adj_mul, adj_adj, adj_giA, Matrix.mul_assoc, giA_gA_cancel]

theorem psi_sympl_extY (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (hχ : p.IsChar ψ ψk)
    {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (zk : Matrix (Fin ρ) (Fin T.rank) k) (w : WO S T) :
    ψ (symplO S T w (d.extY T (giA T ⬝ adj (zk.map p.ι : Mx D ρ T.rank)))) =
      (ψk ((zk * (w ⬝ d.jX : Mx D T.rank ρ).map p.π).trace) : ℂ) := by
  rw [hχ, symplO, hO_extY, pairS_giA_adj, map_iota_mul, trace_map_iota]
  rfl

theorem isHalf_mul_left {e : AE D} {a b c : ℕ} (x : Mx D a b) {y : Mx D b c} (h : IsHalf e y) : IsHalf e (x ⬝ y) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, h l j]

theorem isHalf_mul_right {e : AE D} {a b c : ℕ} {x : Mx D a b} (y : Mx D b c) (h : IsHalf e x) : IsHalf e (x ⬝ y) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, h i l]

theorem isHalf_adj (p : Place D k) {a b : ℕ} (zk : Matrix (Fin a) (Fin b) k) :
    IsHalf (cA D p.e) (adj (zk.map p.ι : Mx D a b)) := fun i j =>
  (map_mul (cA D) p.e (p.ι (zk j i))).symm.trans (congrArg (cA D) (e_iota p _))

theorem exists_mxAt (p : Place D k) : ∃ v : GlobalTheory.FinPl.Pl D, ∀ (a b : ℕ) (x : Mx D a b), IsHalf (cA D p.e) x →
    GlobalTheory.FinPl.MxAt (· = v) x := by
  obtain ⟨_, h0, v, ε, h1, h2⟩ := p.split
  obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 h1
  refine ⟨v, fun a b x hx i j => GlobalTheory.FinPl.Model.mem_idAt_iff.2 ?_⟩
  rw [← h2, add_mul, hx i j, ← hx i j, ← mul_assoc, h0, zero_mul, zero_add]

theorem trace_mul_uni {ρ : ℕ} (M : Mx D ρ ρ) (hM : ∀ i j, j < i → M i j = 0) (u : UX D ρ) :
    (M ⬝ u.1.1).trace = M.trace := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hu := u.2
  rw [Matrix.diag_apply, Matrix.diag_apply, GlobalTheory.UniIndexPrime.diag_mul hM (fun a b h => (hu a b).1 h), (hu i i).2, mul_one]

theorem col_mul {K m l o o' : Type} [Field K] [Fintype l] (M : Matrix m l K) (E : Matrix l o K) (F : Matrix l o' K) (j : o)
    (j' : o') {κ : K} (hκ : κ ≠ 0) (h : ∀ x, F x j' = κ * E x j) (r : m) : (M * E) r j = κ⁻¹ * (M * F) r j' := by
  simp only [Matrix.mul_apply, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by field_simp

theorem row_mul {K m l o : Type} [Field K] [Fintype l] {ρ : ℕ} (i₀ : Fin ρ) (a : K) (G : Matrix m l K) (r : m)
    (X : Matrix l o K) (i : Fin ρ) (j : o) :
    ((Matrix.of fun i' β => if i' = i₀ then a * G r β else 0 : Matrix (Fin ρ) l K) * X) i j =
      if i = i₀ then a * (G * X) r j else 0 := by
  by_cases h : i = i₀ <;> simp [Matrix.mul_apply, h, Finset.mul_sum, mul_assoc]

theorem trace_row_mul {K m l : Type} [Field K] [Fintype l] {ρ : ℕ} (i₀ : Fin ρ) (a : K) (G : Matrix m l K) (r : m)
    (X : Matrix l (Fin ρ) K) :
    ((Matrix.of fun i' β => if i' = i₀ then a * G r β else 0 : Matrix (Fin ρ) l K) * X).trace = a * (G * X) r i₀ := by
  simp only [Matrix.trace, Matrix.diag_apply, row_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem law_dual_col : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ GlobalTheory.RootEx.Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatBF st (Tm Φ') = flatBF st (Tm Φ) := by
  intro D _ hFL _ k _ _ _ _ _ _ p ν _ ψ ψk hχ ρ B J st s hs n n' _ _ _ _ c FA F₀ FV G₀ FW _ hbes hjac Tm hTm r q hq b Φ Φ' hΦ'
  obtain ⟨i, rfl, hi, hfree⟩ := hq
  have hc : c = 2 * ρ := hjac.1
  have hκ : ∀ m : ℕ, s * p.xi ^ m ≠ 0 := fun m => mul_ne_zero hs (pow_ne_zero _ (xi_ne p))
  let i₀ : Fin ρ := ⟨i.val, hi⟩
  let zk : Matrix (Fin ρ) (Fin J.W.rank) k :=
    Matrix.of fun i' β => if i' = i₀ then b * (s * p.xi ^ (ρ - i.val)) * FW.γ r β else 0
  let a : Mx D J.W.rank ρ := giA J.W ⬝ adj (zk.map p.ι : Mx D ρ J.W.rank)
  have ha : IsHalf (cA D p.e) a := isHalf_mul_left _ (isHalf_adj p zk)
  have hy : IsHalf (cA D p.e) (B.d.extY J.W a) := isHalf_mul_right _ ha
  have hW : ∀ j : Fin ρ, (FW.γ * J.d.jX.map p.π) r j = (s * p.xi ^ (ρ - j.val))⁻¹ *
      (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inr ⟨j.val, by omega⟩) := fun j => by
    rw [← FW.γβ]
    exact col_mul _ _ _ _ _ (hκ _) (hjac.2.2.1 j ⟨j.val, by omega⟩ rfl) r
  have hB : ∀ t, ψ (symplO B.V J.W (p.up FV FW t) (B.d.extY J.W a)) = (ψk (b * t r (Sum.inr i)) : ℂ) := fun t => by
    rw [psi_sympl_extY p hχ, trace_row_mul, Place.up, map_iota_mul, map_iota_pi, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, FW.γβ, Matrix.one_mul,
      col_mul _ _ FV.β i₀ (Sum.inr i) (hκ _) (hbes.2.2.1 i₀ i rfl), Matrix.mul_assoc, FV.γβ, Matrix.mul_one, mul_assoc,
      mul_inv_cancel_left₀ (hκ _)]
  have hD : ψ (symplO B.V J.W (B.d.extX J.W (xZero J.d)) (B.d.extY J.W a)) =
      (ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) := by
    rw [psi_sympl_extY p hχ, trace_row_mul, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one, xZero, hW,
      mul_assoc, mul_inv_cancel_left₀ (hκ _)]
    congr 3
    rcases r with r | r
    · simp [basePt]
    · simp [basePt, Matrix.one_apply, Fin.ext_iff, i₀]
  have hU : GlobalTheory.FinPl.UInv J.W (xZero J.d) a := fun u => by
    rw [pairS_giA_adj, pairS_giA_adj, ← Matrix.mul_assoc]
    refine trace_mul_uni _ (fun i' j hj => ?_) u
    rw [map_iota_mul, Matrix.map_apply, row_mul]
    split_ifs with h
    · subst h
      rw [xZero, hW, Matrix.one_apply_ne, mul_zero, mul_zero, map_zero]
      rintro rfl
      exact hfree hj
    · exact map_zero _
  obtain ⟨v, hv⟩ := exists_mxAt p
  have hlaw := ((hFL ψ (· = v)).1 ρ B J st).Heisenberg₂.dual _ (hTm.theta Φ) a (hv _ _ a ha) hU
  have hmod := hTm.modul _ hy Φ ((ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) • Φ') fun t => by
    rw [hB, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hΦ', ← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      ← mul_add, add_sub_cancel]
  rw [← hmod, hD, map_smul, GlobalTheory.HandHom.flatBF_smul] at hlaw
  exact smul_right_injective _ (Circle.coe_ne_zero _) hlaw

end GlobalTheory.FlatColLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapDualColumnMultiplicationLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFlatMap_dualColumn_multiplicationLaws : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ GlobalTheory.RootEx.Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatBF st (Tm Φ') = flatBF st (Tm Φ) := by
  first | exact @GlobalTheory.FlatColLaw.law_dual_col | exact GlobalTheory.FlatColLaw.law_dual_col | (intros; apply GlobalTheory.FlatColLaw.law_dual_col <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceSchwartzBruhatActsAsSupportedCombinati
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceSchwartzBruhatActsAsSupportedCombinati
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.CombProof

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

section Comb

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem comb_eq_sum (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = c.sum fun u a => a • heisO ψ S T u f := rfl

theorem comb_zero_left (f : WO S T → ℂ) : comb ψ S T 0 f = 0 := by
  rw [comb_eq_sum, Finsupp.sum_zero_index]

theorem comb_add_left (c₁ c₂ : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (c₁ + c₂) f = comb ψ S T c₁ f + comb ψ S T c₂ f := by
  rw [comb_eq_sum, comb_eq_sum, comb_eq_sum]
  exact Finsupp.sum_add_index' (fun i => zero_smul ℂ (heisO ψ S T i f)) fun i a b => add_smul a b (heisO ψ S T i f)

theorem comb_smul_left (a : ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T (a • c) f = a • comb ψ S T c f := by
  rw [comb_eq_sum, comb_eq_sum, Finsupp.sum_smul_index' (fun i => zero_smul ℂ (heisO ψ S T i f)), Finsupp.smul_sum]
  simp only [smul_smul, smul_eq_mul]

theorem comb_single (u : WO S T) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T (Finsupp.single u a) f = a • heisO ψ S T u f := by
  rw [comb_eq_sum, Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T u f))]

variable {S T} {P : Pl D → Prop}

theorem combAt_zero : CombAt P (0 : WO S T →₀ ℂ) := fun u hu => by simp at hu

open Classical in
theorem combAt_add {c₁ c₂ : WO S T →₀ ℂ} (h₁ : CombAt P c₁) (h₂ : CombAt P c₂) : CombAt P (c₁ + c₂) :=
  fun u hu => (Finset.mem_union.1 (Finsupp.support_add hu)).elim (h₁ u) (h₂ u)

theorem combAt_smul (a : ℂ) {c : WO S T →₀ ℂ} (h : CombAt P c) : CombAt P (a • c) :=
  fun u hu => h u (Finsupp.support_smul hu)

theorem combAt_single {u : WO S T} (hu : MxAt P u) (a : ℂ) : CombAt P (Finsupp.single u a) := fun u' hu' => by
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu')]
  exact hu

end Comb

section Rd
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {S T : HSp D}

theorem rd_add (α : Frame p S n') (β : Frame p T n) (t s : WO S T) : rd α β (t + s) = rd α β t + rd α β s := by
  unfold rd
  rw [Matrix.map_add p.pr (map_add p.pr), Matrix.mul_add, Matrix.add_mul]

theorem rd_nsmul (α : Frame p S n') (β : Frame p T n) (N : ℕ) (t : WO S T) : rd α β (N • t) = (N : k) • rd α β t := by
  unfold rd
  have : (N • t).map p.pr = (N : k) • t.map p.pr := by
    ext i j
    simp [Matrix.map_apply, nsmul_eq_mul, map_mul, map_natCast]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

end Rd

theorem isSBHalf_extFun : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D)
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ Ψ ∈ SB (Matrix n n' k), IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (extFun α β Ψ) := by
  classical
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT Ψ hΨ
  obtain ⟨Na, hNa, ha⟩ := GlobalTheory.FinPl.RdBound.exists_nat_mul_rd_mem D k p n n' S T α β LS LT hS hT
  obtain ⟨Nb, hNb, hb⟩ := GlobalTheory.FinPl.exists_nsmul_mem_latO_of_rd_int D k p n n' S T α β LS LT hS hT
  obtain ⟨Nc, hNc, hc1, hc2⟩ := GlobalTheory.SBUnif.uniform k n n' Ψ hΨ
  have hhalf_add : ∀ {t u : WO S T}, IsHalf p.e u → (IsHalf p.e (t + u) ↔ IsHalf p.e t) := fun {t u} hu =>
    forall_congr' fun i => forall_congr' fun j => by
      rw [Matrix.add_apply, mul_add, hu i j, add_left_inj]
  have hhalf_nsmul : ∀ (N : ℕ) {t : WO S T}, IsHalf p.e t → IsHalf p.e (N • t) := fun N t ht i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, ht i j]
  refine ⟨fun t ht => ?_, Na * Nb * Nc, Nat.mul_pos (Nat.mul_pos hNa hNb) hNc, fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (by simp [extFun, h])
  · have hu' : IsHalf p.e ((Na * Nb * Nc) • u) := hhalf_nsmul _ hh
    unfold extFun
    rw [if_congr (hhalf_add hu') rfl rfl]
    split_ifs with h
    · rw [rd_add, rd_nsmul, show ((Na * Nb * Nc : ℕ) : k) • rd α β u = (Nc : k) • (((Nb : k) * Na) • rd α β u) by
        rw [smul_smul]; push_cast; ring_nf]
      refine hc1 _ _ fun i j => ?_
      rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]
      exact mul_mem (by exact_mod_cast (algebraMap ℤ 𝒪[k] Nb).2) (ha u hu hh i j)
    · rfl
  · have hth : IsHalf p.e t := by
      by_contra h
      exact ht (by simp [extFun, h])
    have hΨt : Ψ (rd α β t) ≠ 0 := by simpa [extFun, hth] using ht
    have h1 := hb (Nc • t) (hhalf_nsmul _ hth) fun i j => by
      rw [rd_nsmul, Matrix.smul_apply, smul_eq_mul]
      exact hc2 _ hΨt i j
    rw [show (Na * Nb * Nc) • t = Na • (Nb • (Nc • t)) by rw [smul_smul, smul_smul, mul_assoc]]
    exact nsmul_mem h1 Na

variable {D : D7}

theorem dualPair {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : AE D} {v : Pl D} (hs : IsSplitIdem D e) {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (heq : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) :
    let Λ := latO S T (LS : Set _) (LT : Set _) (· = v)
    (∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1) ∧
    (∀ x ∈ half S T e, (∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) → x ∈ Λ ⊓ half S T e) ∧
    (∀ y ∈ half S T (cA D e), (∀ u ∈ Λ ⊓ half S T e, ψ (symplO S T u y) = 1) → y ∈ Λ ⊓ half S T (cA D e)) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧ ∀ t ∈ Λ ⊓ half S T e, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T e, t = r + k • u) ∧
    (∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ) := by
  intro Λ
  have he := hs.1
  have hec := hs.2.1
  have he' : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (AE D) ε * e = e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by rw [← heq]; linear_combination he' + hec
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T LS LT hS.1.fg hT.1.fg fun w => w = v
  refine ⟨fun u hu y hy => (hdual u (infPart_half hε heε hu.2)).1 (latO_le_top _ hu.1) y (latO_le_top _ hy.1),
    mem_of_dual hε hdual he heε heε', fun y hy h => ?_, fun k hk => ?_, fun y hy => ?_⟩
  · refine mem_of_dual hε hdual he' heε' (by rwa [cA_cA]) y hy fun u hu => ?_
    rw [cA_cA] at hu
    rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, idem_smul_mem hε he heε (latO_le_top _ hu), ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  · obtain ⟨k, hk, hky⟩ := exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y (infPart_half hε heε' hy)
    refine ⟨k, hk, ?_⟩
    have := (idem_smul_mem hε he' heε' hky).1
    rwa [smul_comm, (mem_half S T).1 hy] at this

theorem extFun_comb : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ Ψ ∈ SB (Matrix n n' k), ∃ c : WO S T →₀ ℂ, CombAt (· = p.v) c ∧ ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 f₀ Tm → Tm (extFun α β Ψ) = comb ψ S T c f₀ := by
  classical
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ S T α β LS LT hS hT Ψ hΨ
  obtain ⟨ε, hε, heq⟩ := p.above
  have hs := p.split
  have he := hs.1
  have hec := hs.2.1
  have he' : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by
    rw [← heq]; linear_combination he' + hec
  obtain ⟨hLL', hX, -, hfin, hden⟩ := dualPair hψ hS hT hs hε heq
  set Λ := latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) with hΛ
  have hΦ := isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y; rw [symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y; rw [symplO_add_right, AddChar.map_add_eq_mul]
    · intro y; rw [symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y; rw [symplO_zero_right, AddChar.map_zero_eq_one]
  have hm : extFun α β Ψ ∈
      waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T p.e) (half S T (cA D p.e)) (Λ ⊓ half S T p.e) := by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact mem_waveSpan hb inf_le_right inf_le_right hLL' hX (half_div S T p.e) (half_div S T _) tf hfin _
      (fun t ht => (isHalf_iff S T).1 (h1 t ht)) k hk (fun u hu => h2 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨h3 t ht, (half S T p.e).nsmul_mem ((isHalf_iff S T).1 (h1 t ht)) _⟩

  have hεid : algebraMap (AF D.host.F) (AE D) ε ∈ idAt D (· = p.v) := by
    obtain ⟨a, rfl, -, h0⟩ := id hε
    exact LatMem.tmul_mem_idAt (fun w hw => h0 w hw) 1
  have hsupp : ∀ {e' : AE D}, algebraMap (AF D.host.F) (AE D) ε * e' = e' → ∀ x ∈ half S T e', ∀ i j,
      x i j ∈ idAt D (· = p.v) := fun {e'} h x hx i j => by
    have h1 := (isHalf_iff S T).2 hx i j
    have : x i j = algebraMap (AF D.host.F) (AE D) ε * x i j := by
      linear_combination (algebraMap (AF D.host.F) (AE D) ε - 1) * h1 - x i j * h
    rw [this]
    exact Ideal.mul_mem_right _ _ hεid
  have hmx : ∀ x ∈ half S T p.e, ∀ y ∈ half S T (cA D p.e), MxAt (· = p.v) (x + y) := fun x hx y hy i j => by
    rw [Matrix.add_apply]
    exact add_mem (hsupp heε x hx i j) (hsupp heε' y hy i j)
  generalize extFun α β Ψ = Φ at hm
  induction hm using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hh
    refine ⟨Finsupp.single (x + y) (ψ (symplOH S T x y)), combAt_single (hmx x hx y hy) _, fun f₀ Tm h => ?_⟩
    have s0 := GlobalTheory.isSBHalf_halfInd p.e Λ
    have s1 : IsSBHalf p.e Λ fun t => ψ (symplO S T t y) * halfInd p.e Λ t := by
      obtain ⟨k, hk, hk'⟩ := hden y hy
      obtain ⟨a1, k', hk1, a2, a3⟩ := s0
      refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
        fun t ht => ?_⟩
      · have e1 : halfInd p.e Λ (t + (k * k') • u) = halfInd p.e Λ t := by
          rw [mul_nsmul]
          exact a2 _ (nsmul_mem hu k) ((isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hh) k)) t
        have e2 : ψ (symplO S T ((k * k') • u) y) = 1 := by
          rw [mul_nsmul']
          exact (hb.nsmul k _ y).trans
            (hLL' _ (nsmul_mem (AddSubgroup.mem_inf.2 ⟨hu, (isHalf_iff S T).1 hh⟩) k') _ ⟨hk', nsmul_mem hy k⟩)
        simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
      · rw [mul_nsmul']
        exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
    have e1 : wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T p.e) x y =
        fun t => (fun t => ψ (symplO S T t y) * halfInd p.e Λ t) (t + x) := by
      rw [halfInd_eq_ind]; rfl
    have v1 := h.vac
    rw [one_smul] at v1
    rw [e1, h.trans _ s1 x ((isHalf_iff S T).2 hx), h.modul _ s0 y ((isHalf_iff S T).2 hy), v1, comb_single]
    exact heisL_heisL S T ψ x y f₀
  | zero => exact ⟨0, combAt_zero, fun f₀ Tm _ => by rw [LinearMap.map_zero, comb_zero_left]⟩
  | add f g _ _ hf hg =>
    obtain ⟨c₁, hc₁, h₁⟩ := hf
    obtain ⟨c₂, hc₂, h₂⟩ := hg
    exact ⟨c₁ + c₂, combAt_add hc₁ hc₂, fun f₀ Tm h => by
      rw [LinearMap.map_add (f := _), h₁ f₀ Tm h, h₂ f₀ Tm h, comb_add_left]⟩
  | smul a f _ hf =>
    obtain ⟨c, hc, h₁⟩ := hf
    exact ⟨a • c, combAt_smul a hc, fun f₀ Tm h => by rw [LinearMap.map_smul, h₁ f₀ Tm h, comb_smul_left]⟩

end GlobalTheory.FinPl.CombProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceSchwartzBruhatActsAsSupportedCombinatiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceSchwartzBruhat_acts_as_supported_combination : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ Ψ ∈ SB (Matrix n n' k), ∃ c : WO S T →₀ ℂ, CombAt (· = p.v) c ∧ ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v)) 1 f₀ Tm → Tm (extFun α β Ψ) = comb ψ S T c f₀ := by
  first | exact @GlobalTheory.FinPl.CombProof.extFun_comb | exact GlobalTheory.FinPl.CombProof.extFun_comb | (intros; apply GlobalTheory.FinPl.CombProof.extFun_comb <;> assumption)
end
end
