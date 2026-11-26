module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointBaseLatticeCoordsIntegralLastInPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLatticeDualZIdealMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramified
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.InvStep

variable {D : D7}

theorem diag_inv {ρ : ℕ} (t : GL (Fin ρ) (AE D)) (ht : ∀ i j, i ≠ j → t.1 i j = 0) :
    t.1 = diagonal (fun k => t.1 k k) ∧ (t⁻¹).1 = diagonal (fun k => (t⁻¹).1 k k) ∧
      ∀ k, t.1 k k * (t⁻¹).1 k k = 1 := by
  have h1 : t.1 = diagonal (fun k => t.1 k k) := by
    ext a b
    by_cases h : a = b
    · subst h; simp
    · rw [diagonal_apply_ne _ h, ht a b h]
  have hm : t.1 * (t⁻¹).1 = 1 := t.mul_inv
  have h3 : ∀ a b, t.1 a a * (t⁻¹).1 a b = (1 : Matrix (Fin ρ) (Fin ρ) (AE D)) a b := by
    intro a b
    have := congrFun (congrFun hm a) b
    rw [h1, diagonal_mul] at this
    exact this
  have h4 : ∀ k, t.1 k k * (t⁻¹).1 k k = 1 := fun k => by
    have := h3 k k; rwa [one_apply_eq] at this
  refine ⟨h1, ?_, h4⟩
  ext a b
  by_cases h : a = b
  · subst h; simp
  · rw [diagonal_apply_ne _ h]
    have e := h3 a b
    rw [one_apply_ne h] at e
    calc (t⁻¹).1 a b = (t⁻¹).1 a a * (t.1 a a * (t⁻¹).1 a b) := by
          rw [← mul_assoc, mul_comm ((t⁻¹).1 a a), h4, one_mul]
      _ = 0 := by rw [e, mul_zero]

theorem mat_mem_idAt {P : Pl D → Prop} {m n k l : ℕ} (A : Mx D m n) (M : Mx D n k) (B : Mx D k l)
    (hM : ∀ a b, M a b ∈ idAt D P) (i : Fin m) (j : Fin l) : (A ⬝ M ⬝ B) i j ∈ idAt D P := by
  rw [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun b _ => Ideal.mul_mem_right _ _ ?_
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (hM a b)

theorem levi_sub_one_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {P : Pl D → Prop} {t : GL (Fin ρ) (AE D)}
    (ht : d.levi t ∈ grpAt S P) (i j : Fin ρ) : t.1 i j - (1 : Mx D ρ ρ) i j ∈ idAt D P := by
  have hm : ∀ a b, (mt S (d.levi t) - 1) a b ∈ idAt D P := by
    intro a b
    have h := (MonoidHom.mem_ker).1 ht
    have h2 := congrArg (fun u : GL (Fin S.rank) (AE D ⧸ idAt D P) => u.1 a b) h
    simp only [Units.val_one] at h2
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    have e1 : ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (idAt D P))).comp (matHom S) (d.levi t)).1 =
      (mt S (d.levi t)).map (Ideal.Quotient.mk (idAt D P)) := rfl
    rw [e1, Matrix.map_apply] at h2
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e : t.1 - 1 = d.pX ⬝ (mt S (d.levi t) - 1) ⬝ d.jX := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, d.pX_jX, Matrix.mul_assoc, ← blockX, blockX_levi]
  rw [← Matrix.sub_apply, e]
  exact mat_mem_idAt _ _ _ hm i j

theorem symplO_extX_extY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x y : Mx D T.rank ρ) :
    symplO S T (d.extX T x) (d.extY T y) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * pairS T x y) := by
  have h := d.hO_ext T x 0 0 y 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplO, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero]

theorem trace_single_mul {ρ : ℕ} (i : Fin ρ) (β : AE D) (M : Mx D ρ ρ) :
    (Matrix.single i i β ⬝ M).trace = β * M i i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

theorem adj_single {ρ : ℕ} (i : Fin ρ) (β : AE D) : adj (Matrix.single i i β) = Matrix.single i i (cA D β) := by
  ext a b
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ⟨h1.2, h1.1⟩ h2 | exact absurd ⟨h2.2, h2.1⟩ h1 | exact map_zero _


set_option maxHeartbeats 1000000 in
theorem vac_fix_Y : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (LS : Lat S) (LT : Lat T) (v : Pl D), Tame D v → ∀ f, Vac ψ S T LS LT (· = v) f → ∀ y : Mx D T.rank ρ, d.extY T y ∈ latO S T (LS : Set _) (LT : Set _) (· = v) → heisO ψ S T (d.extY T y) f = f := by
  intro D ψ S S₀ T ρ d LS LT v hT f hf y hy
  have hsm : ∀ (c : AE D) (z : Mx D T.rank ρ), c • d.extY T z = d.extY T (c • z) := by
    intro c z
    rw [HypDec.extY_apply, HypDec.extY_apply, Matrix.smul_mul]
  have hadd : ∀ y₁ y₂ : Mx D T.rank ρ, heisO ψ S T (d.extY T (y₁ + y₂)) f =
      heisO ψ S T (d.extY T y₁) (heisO ψ S T (d.extY T y₂) f) := by
    intro y₁ y₂
    funext w
    simp only [heisO, map_add (f := _)]
    rw [GlobalTheory.OrientedHeis.symplOH_add_left, HypDec.symplOH_extY_extY, add_zero, GlobalTheory.OrientedHeis.symplOH_add_right,
      AddChar.map_add_eq_mul, add_assoc]
    ring
  rcases hT.2 with h2 | ⟨e, ε, he, hε, hb⟩
  · have hε : IsPlaceIdem D v (GlobalTheory.SplitIdem.placeHom D.host.F v 1) :=
      ⟨singleV D.host.F v 1, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _,
        fun w hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
    obtain ⟨a, ha, ha2⟩ : ∃ a : AE D, finPart D a ∈ intAE D ∧
        2 * a = algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v 1) := by
      obtain ⟨yv, hyv⟩ := ((GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v 2).2 h2).exists_right_inv
      rw [map_ofNat] at hyv
      have hy' : (2 : Fv D.host.F v) * yv = 1 := congrArg Subtype.val hyv
      refine ⟨algebraMap (AF D.host.F) (AE D) (GlobalTheory.SplitIdem.placeHom D.host.F v yv), ?_, ?_⟩
      · exact AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf D.host.F v yv, 1, rfl⟩
      · rw [two_mul, ← map_add (f := _), ← map_add (f := _), ← two_mul, hy']
    have h1 : 2 • (a • d.extY T y) = d.extY T y := by
      rw [two_nsmul, ← add_smul, ← two_mul, ha2, GlobalTheory.VecInvInert.idem_smul_eq hε hy]
    have h3 := hf.2.1 (a • d.extY T y) (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha _ hy)
    rwa [h1] at h3
  · have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
    have hint : ∀ c : AE D, c * c = c → finPart D c ∈ intAE D := fun c hc =>
      GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hc])
    have hu : d.extY T y = d.extY T (e • y) + d.extY T (cA D e • y) := by
      rw [← hsm, ← hsm, ← add_smul, hb, GlobalTheory.VecInvInert.idem_smul_eq hε hy]
    have f1 : heisO ψ S T (d.extY T (e • y)) f = f := by
      rw [← hsm]
      exact hf.2.2 e he _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ e (hint e he.1) _ hy) (fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he.1])
    have f2 : heisO ψ S T (d.extY T (cA D e • y)) f = f := by
      rw [← hsm]
      exact hf.2.2 _ he' _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (hint _ he'.1) _ hy) (fun i j => by rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he'.1])
    rw [hu, ← map_add (f := _), hadd, f2, f1]

end GlobalTheory.FinPl.InvStep

namespace GlobalTheory.FinPl.InvStep


set_option maxHeartbeats 1000000 in
theorem inv_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 hF f hf t htd ht hne i
  obtain ⟨-, h2, -⟩ := diag_inv t htd
  have hc1 : (t⁻¹).1 i i - 1 ∈ idAt D (· = v) := by
    have := levi_sub_one_mem J.d (P := (· = v)) (t := t⁻¹) (by rw [map_inv]; exact inv_mem ht) i i
    rwa [one_apply_eq] at this
  refine GlobalTheory.T.integral_of_addChar_trivial_on_homLattice_line D ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ B.d J.d LV LV₀ LW LW₀ v hG.tame hG.sdV hG.sdW hG.monoV
    hG.monoW hG.cols i _ hc1 ?_
  intro b hb hY
  have hfix := vac_fix_Y D ψ B.V B.V₀ J.W ρ B.d LV LW v hG.tame f hf _ hY
  have hθ : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ _ hf.1
  have hg : heisO ψ B.V J.W (actO B.V J.W 1 (J.d.levi t) (B.d.extY J.W (J.d.jY ⬝ Matrix.single i i b)))
      (s.om (1, J.d.levi t) f) = s.om (1, J.d.levi t) f := by
    rw [← s.weil.om_heis 1 (J.d.levi t) _ f hf.1, hfix]
  have hact : actO B.V J.W 1 (J.d.levi t) (B.d.extY J.W (J.d.jY ⬝ Matrix.single i i b)) =
      B.d.extY J.W (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) := by
    rw [actO_eq, inv_one, mt_one, Matrix.mul_one, HypDec.extY_apply, HypDec.extY_apply, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, HypDec.levi_jY, Matrix.mul_assoc J.d.jY]
  have hS : ∀ a c, Matrix.single i i b a c ∈ idAt D (· = v) := by
    intro a c
    rw [Matrix.single_apply]
    split_ifs
    · exact hb
    · exact zero_mem _
  have hMx : MxAt (· = v) (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) := by
    intro a c
    have := mat_mem_idAt (J.d.jY ⬝ adj (t⁻¹).1) (Matrix.single i i b) 1 hS a c
    rwa [Matrix.mul_one, Matrix.mul_assoc] at this
  have hpair : ∀ U : Mx D ρ ρ, pairS J.W (J.d.jX ⬝ U) (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) =
      cA D b * ((t⁻¹).1 i i * U i i) := by
    intro U
    rw [pairS, adj_mul, adj_mul, adj_adj, adj_single, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc (gA J.W), ← Matrix.mul_assoc (adj J.d.jY), HypDec.gram_YX, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc, trace_single_mul]
    congr 1
    conv_lhs => rw [h2]
    rw [diagonal_mul]
  have hUI : UInv J.W (xZero J.d) (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)) := by
    intro u
    have h1 : u.1.1 i i = 1 := ((mem_UX.1 u.2) i i).2
    have e := hpair 1
    rw [Matrix.mul_one] at e
    rw [xZero, hpair, e, h1, one_apply_eq]
  have hd := hF.Heisenberg₂.dual _ hθ _ hMx hUI
  rw [hact] at hg
  rw [hg] at hd
  have hψ : ψ (symplO B.V J.W (B.d.extX J.W (xZero J.d))
      (B.d.extY J.W (J.d.jY ⬝ (adj (t⁻¹).1 ⬝ Matrix.single i i b)))) = 1 := by
    obtain ⟨w, hw⟩ := Function.ne_iff.1 hne
    have h1 := congrFun hd w
    simp only [Pi.smul_apply, smul_eq_mul] at h1 hw
    exact mul_right_cancel₀ hw (h1.symm.trans (one_mul _).symm)
  rw [← hψ, symplO_extX_extY, symplO_extX_extY]
  congr 3
  have e := hpair 1
  rw [Matrix.mul_one, one_apply_eq, mul_one] at e
  rw [xZero, e, pairS, adj_mul, adj_single, Matrix.mul_assoc, ← Matrix.mul_assoc (gA J.W), ← Matrix.mul_assoc (adj J.d.jY),
    HypDec.gram_YX, Matrix.one_mul, trace_single_mul, Matrix.single_apply, if_pos ⟨rfl, rfl⟩]

end GlobalTheory.FinPl.InvStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvDiagTorusIntegralBesselJacobiUnramifiedStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_diag_torus_integral_besselJacobi_unramified : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.InvStep.inv_int | exact GlobalTheory.FinPl.InvStep.inv_int | (intros; apply GlobalTheory.FinPl.InvStep.inv_int <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelCharacterEqBesselCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelCharacterEqBesselCharacter
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZeroChar

theorem map_conj_local {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) {β : GL (Fin (c.V 0).rank) (Lev.EAf D)} {b : GA D (c.V 0)}
    {π' : Lev.EAf D →+* G.k} (hπ : ∀ a, π' (toEAf D a) = G.q.pr a) {n : GA D (c.V 0)}
    {q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k}
    (hloc : (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) n q)
    (σ : Fin (c.V 0).rank → XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) (hσ : Function.Bijective σ)
    (hM : MovedTo (ofSplit G.q) (c.V 0) b β
      (((G.FY 0 (G.s + 1) (Nat.zero_add _)).β * ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val).submatrix id σ)) :
    ((β⁻¹ * finE (c.V 0) (b⁻¹ * n * b) * β).val).map π' =
      ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _))⁻¹).val * q.val *
        ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val).submatrix σ σ := by
  set F := G.FY 0 (G.s + 1) (Nat.zero_add _) with hF
  set B := (G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _) with hB
  set p := ofSplit G.q with hp
  have hβ := GlobalTheory.LocMod.StepVec.map_eq_of_movedTo p F (π' := π') hπ B.val σ hM
  have hfin : ∀ g : GA D (c.V 0), (finE (c.V 0) g).val.map π' = (mt (c.V 0) g).map p.π := by
    intro g
    rw [GlobalTheory.LevSplit.finE_val]
    ext i j
    exact hπ _
  have hBB : (B⁻¹).val * B.val = 1 := Units.inv_mul B
  have hmt : ∀ g h : GA D (c.V 0), (mt (c.V 0) (g * h)).map p.π = (mt (c.V 0) g).map p.π * (mt (c.V 0) h).map p.π :=
    fun g h => Matrix.map_mul
  have ht1 : (mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π = 1 := by
    rw [← hmt, mul_inv_cancel]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  set W := (mt (c.V 0) b⁻¹).map p.π * F.β * B.val with hW
  set W' := (B⁻¹).val * F.γ * (mt (c.V 0) b).map p.π with hW'
  have hWW : W' * W = 1 := by
    rw [hW, hW']
    calc (B⁻¹).val * F.γ * (mt (c.V 0) b).map p.π * ((mt (c.V 0) b⁻¹).map p.π * F.β * B.val)
        = (B⁻¹).val * (F.γ * ((mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π) * F.β) * B.val := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ht1, Matrix.mul_one, F.γβ, Matrix.mul_one, hBB]
  have hβ' : β.val.map π' = W.submatrix id σ := by
    rw [hβ]; rfl
  have hinv : (β⁻¹).val.map π' = W'.submatrix σ id := by
    refine Matrix.left_inv_eq_left_inv (A := β.val.map π') ?_ ?_
    · rw [← Matrix.map_mul, Units.inv_mul]; exact Matrix.map_one _ (map_zero _) (map_one _)
    · rw [hβ', ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hWW]
      exact Matrix.submatrix_one_equiv (Equiv.ofBijective σ hσ)
  have hn : (mt (c.V 0) n).map p.π = F.β * q.val * F.γ := hloc.2
  rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hinv, hfin, hβ', hmt, hmt, hn]
  have hs : ∀ (X : Matrix (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) (Fin (c.V 0).rank) G.k)
      (Mid : Matrix (Fin (c.V 0).rank) (Fin (c.V 0).rank) G.k)
      (Z : Matrix (Fin (c.V 0).rank) (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k),
      X.submatrix σ id * Mid * Z.submatrix id σ = (X * Mid * Z).submatrix σ σ := fun X Mid Z => Matrix.ext fun i j => rfl
  rw [hs]
  congr 1
  rw [hW, hW']
  calc (B⁻¹).val * F.γ * (mt (c.V 0) b).map p.π *
        ((mt (c.V 0) b⁻¹).map p.π * (F.β * q.val * F.γ) * (mt (c.V 0) b).map p.π) *
        ((mt (c.V 0) b⁻¹).map p.π * F.β * B.val)
      = (B⁻¹).val * (F.γ * ((mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π) * F.β) * q.val *
        (F.γ * ((mt (c.V 0) b).map p.π * (mt (c.V 0) b⁻¹).map p.π) * F.β) * B.val := by
        simp only [Matrix.mul_assoc]
    _ = (B⁻¹).val * q.val * B.val := by simp only [ht1, Matrix.mul_one, F.γβ]


set_option maxHeartbeats 1000000 in
theorem psi_red_at {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Pl D.host.E) (b : GA D (c.V 0))
    (β : GL (Fin (c.V 0).rank) (Lev.EAf D)) (hL : GlobalTheory.LevZero.LocAt G PP b β) (hr : D.R.r ≤ (c.V 0).rank) (n : GA D (c.V 0))
    (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1)) G.k) (p : ℕ) (hq : q ∈ GlobalTheory.RootEx.N G.k _ (G.s + 1) p)
    (hloc : (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) n q) (hS : finE (c.V 0) (b⁻¹ * n * b) ∈ St β)
    (hblk : redFn β PP (finE (c.V 0) (b⁻¹ * n * b)) ∈ blockTri (blk2 D.R.r)) (z : 𝓞 D.host.E)
    (hz : Ideal.Quotient.mk PP.asIdeal z = edgeSum (GlobalTheory.chainEdge D.R.k) (upperLeftBlock hr (redFn β PP (finE (c.V 0) (b⁻¹ * n * b))))) :
    (G.S.ψ (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (ofSplit G.q).pr (z : D.host.E)) : ℂ) = (G.S.ψ (GlobalTheory.RootEx.simpleSum q) : ℂ) := by
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D G.k G.q PP hL.idem
  obtain ⟨e, he, hM⟩ := hL.frame (G.s + 1) (Nat.zero_add _)
  have hσ : Function.Bijective (fun i => stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm i)) :=
    (e.symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _))).bijective
  have hmat := map_conj_local G hπ hloc _ hσ hM
  obtain ⟨y, hy⟩ := hS
  have hI : β⁻¹ * finE (c.V 0) (b⁻¹ * n * b) * β = intGL _ _ _ y := by
    rw [← hy]
    simp [frGL, MulAut.conj_apply]
    group
  rw [hI] at hmat
  rw [← hy, redFn_frGL] at hz hblk
  unfold edgeSum at hz
  rw [upper_block_val_submatrix hr hblk] at hz
  have hrk : D.R.r = D.R.k + (G.s + 1) := by
    have := G.hs
    unfold Ranks.r
    omega
  have hN := (GlobalTheory.RootEx.Radical.mem_N_iff q).1 hq
  have hsum : (∑ i : Fin D.R.r, ∑ j : Fin D.R.r, if GlobalTheory.chainEdge D.R.k i j then
      ((((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _))⁻¹).val * q.val *
        ((G.S.T (Fin D.R.t)).bas 0 (G.s + 1) (Nat.zero_add _)).val)
        (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr i)))
        (stdOrd (Fin D.R.k) (Fin D.R.t) 0 (G.s + 1) (Nat.zero_add _) (e.symm (Fin.castLE hr j))) else 0) =
      (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q :=
    GlobalTheory.NChainChar.edge_sum_typeFrame D.R.k D.R.t G.s (c.V 0).rank D.R.r p hr hrk e he G.S.ϖ q hN
  set w : Formalism.L2.Herm.intAf D.host.F D.host.E := ∑ i : Fin D.R.r, ∑ j : Fin D.R.r,
    if GlobalTheory.chainEdge D.R.k i j then y.val (Fin.castLE hr i) (Fin.castLE hr j) else 0 with hw
  have hres : resS D.host.F PP w = Ideal.Quotient.mk PP.asIdeal z := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, hw, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rfl
    · exact map_zero _
  have hker := (hred.ker (w - Formalism.L2.DIV.oToS D.host.F D.host.E z)).1 (by
    rw [map_sub, hres, Formalism.L2.DIV.resS_oToS, sub_self])
  have hpw : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) w = (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum, hw, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · have := congrFun (congrFun hmat (Fin.castLE hr i)) (Fin.castLE hr j)
      exact this
    · exact map_zero _
  have hpz : π' ((Formalism.L2.DIV.oToS D.host.F D.host.E z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
      (ofSplit G.q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
  have hv : ValuativeRel.valuation G.k ((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) < 1 := by
    have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (w - Formalism.L2.DIV.oToS D.host.F D.host.E z) =
        -((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) := by
      rw [map_sub, hpw]
      rw [show (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
        π' ((Formalism.L2.DIV.oToS D.host.F D.host.E z : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) from rfl, hpz]
      ring
    rw [h1, Valuation.map_neg] at hker
    exact hker
  have hone : G.S.ψ (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * ((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q)) = 1 := by
    refine (G.S.cond _).2 ?_ _ le_rfl
    have h5 := (G.S.unif _).1 hv
    have h6 : ValuativeRel.valuation G.k (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (G.S.ϖ : G.k)) = ValuativeRel.valuation G.k ((1 : G.kˣ) : G.k) := by
      rw [Units.inv_mul, Units.val_one]
    rw [← h6, map_mul, map_mul]
    exact mul_le_mul_right h5 _
  have e2 : ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (ofSplit G.q).pr (z : D.host.E) =
      ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * ((ofSplit G.q).pr (z : D.host.E) - (G.S.ϖ : G.k) * GlobalTheory.RootEx.simpleSum q) +
        GlobalTheory.RootEx.simpleSum q := by
    have : ((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (G.S.ϖ : G.k) = 1 := by rw [Units.inv_mul]
    linear_combination (GlobalTheory.RootEx.simpleSum q) * this
  rw [e2, AddChar.map_add_eq_mul, hone, one_mul]

theorem levChi_eq_psiBes : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → levChi (c.V 0) st.β st.L (b⁻¹ * n * b) = psiBes c.ψ (c.bes 0 D.R.rS h0).d 1 (vecB (c.bes 0 D.R.rS h0).o (c.bes 0 D.R.rS h0).ζ) n := by
  intro D c v cm st b G h0 hB PP n q hq hloc hlev
  obtain ⟨hr, ξ, hL⟩ := hB.mem.lev
  have hL' : st.L = Lev.datY (c.V 0).rank D.R.r D.R.t 0 hr cm.Pg ∅ cm.P cm.chi ξ Lev.Frm.B := hL
  have hl := hlev.2
  rw [hL'] at hl
  change finE (c.V 0) (b⁻¹ * n * b) ∈ lev _ _ _ _ at hl
  rw [mem_lev, mem_parLev] at hl
  have hP : (fun PP : cm.Pg => upperLeftBlock hr (redFn st.β PP.1 (finE (c.V 0) (b⁻¹ * n * b)))) ∈ cm.P.H := hl.2
  have hchi : levChi (c.V 0) st.β st.L (b⁻¹ * n * b) = ((cm.P.chi ⟨_, hP⟩ : ℂˣ) : ℂ) := by
    rw [hL']
    unfold levChi levFn
    rw [extendOne_of_mem _ hl.2]
    have e1 : (Lev.datY (c.V 0).rank D.R.r D.R.t 0 hr cm.Pg ∅ cm.P cm.chi ξ Lev.Frm.B).s = 0 := rfl
    have e2 : (Lev.datY (c.V 0).rank D.R.r D.R.t 0 hr cm.Pg ∅ cm.P cm.chi ξ Lev.Frm.B).Q = ∅ := rfl
    simp only [e1, e2, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one]
    rfl
  rw [hchi]
  choose x hx using (hB.grp _).1 hP
  rw [hB.chr ⟨_, hP⟩ x hx, Units.coe_prod, Finset.prod_eq_single PP]
  · obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := PP.1.asIdeal)
      (edgeSum (GlobalTheory.chainEdge D.R.k) (upperLeftBlock hr (redFn st.β PP.1 (finE (c.V 0) (b⁻¹ * n * b)))))
    rw [GlobalTheory.LevZero.lam_eq_of_red (G PP) PP.1 (hB.loc PP).idem (x PP) _ (hx PP) z hz]
    rw [psi_red_at (G PP) PP.1 b st.β (hB.loc PP) hr n q _ hq hloc hl.1.2.1 (blockTri_blkOf_le _ _ (hl.1.2.2.1 PP.1 PP.2)) z hz]
    rw [GlobalTheory.LocBesChar.psiBes_isLoc D (G PP).k (ofSplit (G PP).q) c.ψ (G PP).S.ψ (G PP).char D.R.rS
      (c.B 0 D.R.rS h0) ((G PP).sc 0) _ ((G PP).s + 1) ((G PP).FX 0 (by omega)) ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _))
      ((G PP).bes 0 D.R.rS h0 ((G PP).s + 1) (Nat.zero_add _)) n q hq hloc]
  · intro PP' _ hne
    obtain ⟨e, he⟩ := hB.com.split
    have h1 := GlobalTheory.NChainChar.redFn_conj_eq_one he PP.2 (hB.loc PP).idem hloc.1 b hl.1.2.1 PP'.2
      (fun h => hne (Subtype.ext h).symm)
    have h2 : Ideal.Quotient.mk PP'.1.asIdeal (0 : 𝓞 D.host.E) = edgeSum (GlobalTheory.chainEdge D.R.k)
        (upperLeftBlock hr (redFn st.β PP'.1 (finE (c.V 0) (b⁻¹ * n * b)))) := by
      rw [h1, map_zero]
      unfold upperLeftBlock
      rw [blockDiagonalExtendByOnePrimeField_one]
      symm
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with hij
      · rw [Units.val_one, Matrix.one_apply_ne]
        intro e; rw [e] at hij; exact absurd hij.1 (by omega)
      · rfl
    rw [GlobalTheory.LevZero.lam_eq_of_red (G PP') PP'.1 (hB.loc PP').idem (x PP') _ (hx PP') 0 h2]
    simp [GlobalTheory.LocMod.Place.pr]
  · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.LevZeroChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndexZeroLevelCharacterEqBesselCharacterStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexZeroLevelCharacter_eq_besselCharacter : ∀ {D : D7} {c : Comm D} {v : VCom c} (cm : GlobalTheory.ChainOnto.Com D) (st : StAt (c.V 0)) (b : GA D (c.V 0)) (G : cm.Pg → GLoc v) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), GlobalTheory.LevZero.Bot cm st b G → ∀ (PP : cm.Pg) (n : GA D (c.V 0)) (q : GL (XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → b⁻¹ * n * b ∈ levS (c.V 0) st.β st.L → levChi (c.V 0) st.β st.L (b⁻¹ * n * b) = psiBes c.ψ (c.bes 0 D.R.rS h0).d 1 (vecB (c.bes 0 D.R.rS h0).o (c.bes 0 D.R.rS h0).ζ) n := by
  first | exact @GlobalTheory.LevZeroChar.levChi_eq_psiBes | exact GlobalTheory.LevZeroChar.levChi_eq_psiBes | (intros; apply GlobalTheory.LevZeroChar.levChi_eq_psiBes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualIsotropicLineMemCompletionIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualIsotropicLineMemCompletionIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DualLine

variable {D : D7}

theorem idV_le_idAt {𝔞 : FI D} {v : Pl D} {a : AE D} (ha : a ∈ idV 𝔞 v) : a ∈ idAt D (· = v) := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, -, hα, b, -, rfl⟩ := hx
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt (fun w hw => hα w hw) b
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx

theorem cA_mem_idAt {v : Pl D} {a : AE D} (h : a ∈ idAt D (· = v)) : cA D a ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPl.Model.mem_idAt_iff] at h ⊢
  rw [← Algebra.smul_def] at h ⊢
  conv_rhs => rw [← h]
  rw [GlobalTheory.HeisDisj.cA_smul]

theorem cA_mem_idV_one {v : Pl D} {c : AE D} (hc : c ∈ idV (1 : FI D) v) : cA D c ∈ idV (1 : FI D) v := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    obtain ⟨o', ho'⟩ := GlobalTheory.FinPl.LatMem.star_int o
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, (o' : D.host.E), (FractionalIdeal.mem_one_iff _).2 ⟨o', rfl⟩, ?_⟩
    show pairA D.host.F 0 α ⊗ₜ[D.host.F] star ((o : D.host.E)) = _
    rw [ho']
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem mul_incA_mem {S : HSp D} {L : Lat S} {v : Pl D} {c : AE D} (hc : c ∈ idV (1 : FI D) v)
    {s : Fin S.rank → D.host.E} (hs : s ∈ L) : (fun a => c * incA D (s a)) ∈ latV S L (· = v) := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hx
    obtain ⟨o, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    refine AddSubgroup.subset_closure ⟨α, hαi, fun w hw => hα w hw, 1, rfl, o • s, L.smul_mem o hs, ?_⟩
    funext l
    show (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] s l) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Pi.smul_apply, Algebra.smul_def]
  | zero =>
    have : (fun a => (0 : AE D) * incA D (s a)) = 0 := funext fun a => zero_mul _
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : (fun a => (x + y) * incA D (s a)) = (fun a => x * incA D (s a)) + fun a => y * incA D (s a) :=
      funext fun a => add_mul _ _ _
    rw [this]; exact add_mem hx hy
  | neg x _ hx =>
    have : (fun a => (-x) * incA D (s a)) = -fun a => x * incA D (s a) := funext fun a => neg_mul _ _
    rw [this]; exact neg_mem hx

end GlobalTheory.DualLine

namespace GlobalTheory.DualLine

variable {D : D7}

def hA (S : HSp D) (w y : Fin S.rank → AE D) : AE D := ∑ a, ∑ b, cA D (y a) * gA S a b * w b

theorem hA_add_left (S : HSp D) (w w' y : Fin S.rank → AE D) : hA S (w + w') y = hA S w y + hA S w' y := by
  simp only [hA, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_neg_left (S : HSp D) (w y : Fin S.rank → AE D) : hA S (-w) y = -hA S w y := by
  simp only [hA, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hA_zero_left (S : HSp D) (y : Fin S.rank → AE D) : hA S 0 y = 0 := by
  simp only [hA, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem hA_add_right (S : HSp D) (w y y' : Fin S.rank → AE D) : hA S w (y + y') = hA S w y + hA S w y' := by
  simp only [hA, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hA_neg_right (S : HSp D) (w y : Fin S.rank → AE D) : hA S w (-y) = -hA S w y := by
  simp only [hA, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem hA_zero_right (S : HSp D) (w : Fin S.rank → AE D) : hA S w 0 = 0 := by
  simp only [hA, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]

theorem hA_mem {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) {v : Pl D} {w y : Fin S.rank → AE D}
    (hw : w ∈ latV S L (· = v)) (hy : y ∈ latV S L (· = v)) : hA S w y ∈ idV (1 : FI D) v := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy' =>
    obtain ⟨β, hβi, hβ, c, hc, x', hx', rfl⟩ := hy'
    rw [Set.mem_singleton_iff] at hc
    subst hc
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨α, hαi, hα, c, hc, x, hx, rfl⟩ := hw'
      rw [Set.mem_singleton_iff] at hc
      subst hc
      obtain ⟨b, hb⟩ := (hL.2 x).1 hx x' hx'
      have hp : pairA D.host.F 0 β * pairA D.host.F 0 α = pairA D.host.F 0 (β * α) := Prod.ext (zero_mul _) rfl
      have e : hA S (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
          pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (b : D.host.E) := by
        rw [hb, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        show (pairA D.host.F 0 β ⊗ₜ[D.host.F] star (1 * x' a)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram a k) *
          (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x k)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp, one_mul, one_mul]
      rw [e]
      exact AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβi hαi,
        fun w hw => by rw [map_mul, hβ w hw, zero_mul], (b : D.host.E), (FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩, rfl⟩
    | zero => rw [hA_zero_left]; exact zero_mem _
    | add w w' _ _ h h' => rw [hA_add_left]; exact add_mem h h'
    | neg w _ h => rw [hA_neg_left]; exact neg_mem h
  | zero => rw [hA_zero_right]; exact zero_mem _
  | add y y' _ _ h h' => rw [hA_add_right]; exact add_mem h h'
  | neg y _ h => rw [hA_neg_right]; exact neg_mem h

end GlobalTheory.DualLine

namespace GlobalTheory.DualLine

variable {D : D7}

theorem cA_cA' (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul c e => show c ⊗ₜ[D.host.F] star (star e) = _; rw [star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cA_gA (S : HSp D) (a b : Fin S.rank) : cA D (gA S a b) = incA D (S.gram b a) :=
  congrArg (incA D) (GlobalTheory.LatVac.gram_star S a b)

theorem mem_of_hA {S : HSp D} {L : Lat S} (hL : IsSelfDualC S L) {v : Pl D} {y : Fin S.rank → AE D}
    (hyAt : ∀ a, y a ∈ idAt D (· = v)) (h : ∀ w ∈ latV S L (· = v), hA S w y ∈ idV (1 : FI D) v) :
    y ∈ latV S L (· = v) := by
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hL
  set ι : AE D := pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) with hι
  set w : Fin m → Fin S.rank → AE D := fun i l =>
    pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 * s' i l) with hwdef
  have hw : ∀ i, w i ∈ latV S L (· = v) := fun i => AddSubgroup.subset_closure
    ⟨_, GlobalTheory.FinPl.LatMem.indicatorAdele_mem_integralAdeles' _ _, GlobalTheory.FinPl.LatMem.indicatorAdele_supported _ _, 1, rfl, s' i, hs' i, rfl⟩
  have hcw : ∀ i l, cA D (w i l) = ι * incA D (star (s' i l)) := fun i l => by
    show pairA D.host.F 0 _ ⊗ₜ[D.host.F] star (1 * s' i l) = (pairA D.host.F 0 _ ⊗ₜ[D.host.F] (1 : D.host.E)) *
      ((1 : AF D.host.F) ⊗ₜ[D.host.F] star (s' i l))
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, one_mul]
  have hyeq : y = ∑ i, fun a => cA D (hA S (w i) y) * incA D (s i a) := by
    funext a
    rw [Finset.sum_apply]
    have e1 : y a = ∑ a', y a' * ι * incA D (∑ i, s i a * ∑ k, star (s' i k) * S.gram k a') := by
      simp only [hdual]
      rw [Finset.sum_eq_single a (fun b _ hb => by rw [if_neg (Ne.symm hb), map_zero, mul_zero])
        (fun h => absurd (Finset.mem_univ a) h), if_pos rfl, map_one, mul_one]
      exact (GlobalTheory.FinPl.LatMem.mul_indP (hyAt a)).symm
    rw [e1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hA, map_sum, map_mul, cA_cA', cA_gA, hcw, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hyeq]
  exact sum_mem fun i _ => mul_incA_mem (cA_mem_idV_one (h _ (hw i))) (hs i)

end GlobalTheory.DualLine

namespace GlobalTheory.DualLine

theorem dualLine_mem_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D), IsSelfDualC S L → MonoId d L L₀ 𝔟 v → ∀ i : Fin ρ, 𝔟 i ≠ 0 →
      ∀ t ∈ idAt D (· = v), colMul d.jY i t ∈ latV S L (· = v) ↔ cA D t ∈ idV (𝔟 i)⁻¹ v := by
  intro D ψ hψ S S₀ ρ d L L₀ 𝔟 v hL hM i hb t ht
  have I2 := (GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v).2.1 (𝔟 i) 1 hb one_ne_zero (cA D t) (cA_mem_idAt ht)
  rw [one_mul] at I2
  have hH : ∀ w, hA S w (colMul d.jY i t) = cA D t * (d.pX *ᵥ w) i := by
    intro w
    rw [d.pX_eq]
    simp only [hA, colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, map_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    show cA D t * cA D (d.jY a i) * gA S a b * w b = cA D t * (cA D (d.jY a i) * gA S a b * w b)
    ring
  have hPX : ∀ a, (d.pX *ᵥ colMul d.jX i a) i = a := by
    intro a
    have h1 := congrFun (congrFun d.pX_jX i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simp only [Matrix.mulVec, dotProduct, colMul]
    calc ∑ k, d.pX i k * (a * d.jX k i) = a * ∑ k, d.pX i k * d.jX k i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = a := by rw [h1, mul_one]
  constructor
  · intro hy
    refine I2.1 fun a ha => ?_
    have hx := (hM.2 i a (idV_le_idAt ha)).2 ha
    have h2 := hA_mem hL hx hy
    rwa [hH, hPX] at h2
  · intro hc
    have hall := I2.2 hc
    refine mem_of_hA hL (fun k => Ideal.mul_mem_right _ _ ht) fun w hw => ?_
    rw [hH]
    have hwAt := GlobalTheory.FinPlLoc.latV_idAt hw
    have heAt : (d.pX *ᵥ w) i ∈ idAt D (· = v) := by
      show ∑ b, d.pX i b * w b ∈ idAt D (· = v)
      exact
      Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ (d.pX i b) (hwAt b)
    exact hall _ ((hM.2 i _ heAt).1 (((hM.1 w).1 hw).1 i))

end GlobalTheory.DualLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualIsotropicLineMemCompletionIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualIsotropicLine_mem_completion_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D), IsSelfDualC S L → MonoId d L L₀ 𝔟 v → ∀ i : Fin ρ, 𝔟 i ≠ 0 →
      ∀ t ∈ idAt D (· = v), colMul d.jY i t ∈ latV S L (· = v) ↔ cA D t ∈ idV (𝔟 i)⁻¹ v := by
  first | exact @GlobalTheory.DualLine.dualLine_mem_iff | exact GlobalTheory.DualLine.dualLine_mem_iff | (intros; apply GlobalTheory.DualLine.dualLine_mem_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineMultipleMemSplitCoreLatticeCompletionIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfLineMultipleMemIffIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfLineMultipleMemIffIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ConjHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem vecMul_jA_eq_zero (p : SplitPt D k) {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) ᵥ* o.jA.map p.pr = 0 := by
  have h0 : o.iAᴴ * HSpace.gram S₀ * o.iB = 0 := by
    have := congrArg Matrix.conjTranspose o.orth
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc, gram_conjTranspose] using this
  have h1 : o.iAᴴ *ᵥ (HSpace.gram S₀ *ᵥ vecB o ζ) = 0 := by
    rw [vecB, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]
  funext l
  have h2 : ∑ i, star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) * o.iA i l =
      star ((o.iAᴴ *ᵥ (HSpace.gram S₀ *ᵥ vecB o ζ)) l) := by
    rw [Matrix.mulVec, dotProduct, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply, star_mul', star_star, mul_comm]
  have h3 : ((fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) ᵥ* o.jA.map p.pr) l =
      (p.pr.comp (incA D)) (∑ i, star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) * o.iA i l) := by
    show ∑ i, (p.pr.comp (incA D)) (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)) * (p.pr.comp (incA D)) (o.iA i l) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul]
  rw [h3, h2, h1, Pi.zero_apply, star_zero, map_zero]
  rfl

theorem sum_mul_star_eq {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    ∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  have e1 : ∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i) = vecB o ζ ⬝ᵥ star (HSpace.gram S₀ *ᵥ vecB o ζ) := rfl
  rw [e1, Matrix.star_mulVec, gram_conjTranspose, dotProduct_comm, ← Matrix.dotProduct_mulVec, vecB,
    Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem sumFrame_dot (p : SplitPt D k) {n : Type} [Fintype n] [DecidableEq n] {S₀ A L : HSp D} (o : OrthDec S₀ A L)
    (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (hsum : IsSumFrame o ζ α α₀)
    (x' : n ⊕ Fin 1 → k) :
    (α₀.b *ᵥ x') ⬝ᵥ (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) =
      x' (Sum.inr 0) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) := by
  have e2 : ((o.jA.map p.pr * α.b) *ᵥ (x' ∘ Sum.inl)) ⬝ᵥ
      (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) = 0 := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul, vecMul_jA_eq_zero]
    simp only [Matrix.zero_vecMul, zero_dotProduct]
  have e3 : ((replicateCol (Fin 1) fun i => p.pr (ratV (vecB o ζ) i)) *ᵥ (x' ∘ Sum.inr)) ⬝ᵥ
      (fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)))) =
        x' (Sum.inr 0) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) := by
    rw [← sum_mul_star_eq]
    show ∑ i, (∑ j : Fin 1, (p.pr.comp (incA D)) (vecB o ζ i) * x' (Sum.inr j)) *
        (p.pr.comp (incA D)) (star ((HSpace.gram S₀ *ᵥ vecB o ζ) i)) =
      x' (Sum.inr 0) * (p.pr.comp (incA D)) (∑ i, vecB o ζ i * star ((HSpace.gram S₀ *ᵥ vecB o ζ) i))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    simp only [Fin.sum_univ_one, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsum, Matrix.fromCols_mulVec, add_dotProduct, e2, e3]
  exact zero_add _

theorem pair_eq (p : SplitPt D k) (S₀ : HSp D) (z : Fin S₀.rank → D.host.E) (c : AE D) (x : Fin S₀.rank → k) :
    ∑ i, ∑ j, x i * p.pr (cA D (incA D (HSpace.gram S₀ i j))) * (p.pr (cA D c) * p.pr (incA D (star (z j))))
      = p.pr (cA D c) * (x ⬝ᵥ fun i => p.pr (incA D (star ((HSpace.gram S₀ *ᵥ z) i)))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, Finset.mul_sum, Matrix.mulVec, star_sum, map_sum, FrameLat.cA_incA, star_mul', map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem conj_half : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → IsSumFrame o ζ α α₀ → α₀.IsLat M (lastKer Λ) → ∀ c : AE D, ((fun r => cA D p.e * (c * incA D (vecB o ζ r))) ∈ latV S₀ M (· = p.v) ↔ p.pr (cA D c) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k]) := by
  intro D k _ _ _ _ p n _ _ S₀ A L o ζ α α₀ M Λ hM hsum hlat c
  have hy : (fun r => cA D p.e * (c * incA D (vecB o ζ r))) =
      fun r => cA D (p.sec (p.pr (cA D c) * p.pr (incA D (star (vecB o ζ r))))) := by
    funext r
    have : p.pr (cA D c) * p.pr (incA D (star (vecB o ζ r))) = p.pr (cA D (c * incA D (vecB o ζ r))) := by
      simp only [map_mul, FrameLat.cA_incA]
    rw [this, p.sec_pr, map_mul, Formalism.L2.Theta.cA_cA]
  rw [hy, FrameLat.csec_mem_iff hM]
  constructor
  · intro H
    obtain ⟨x1, hx1l, hx1r⟩ : ∃ x1 : n ⊕ Fin 1 → k, x1 ∘ Sum.inl = 0 ∧ x1 (Sum.inr 0) = 1 :=
      ⟨Sum.elim 0 (fun _ => 1), Sum.elim_comp_inl _ _, rfl⟩
    have hx' : x1 ∈ lastKer Λ := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer, hx1l, hx1r]
      exact ⟨zero_mem _, one_mem _⟩
    have hx := H (α₀.b *ᵥ x1) ((hlat _).1 hx')
    rw [pair_eq, sumFrame_dot p o ζ α α₀ hsum, hx1r, one_mul] at hx
    exact hx
  · intro H x hx
    have hxx : x = α₀.b *ᵥ (α₀.b' *ᵥ x) := by rw [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec]
    rw [hxx] at hx ⊢
    have hl := ((GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer).1 ((hlat _).2 hx)).2
    rw [pair_eq, sumFrame_dot p o ζ α α₀ hsum]
    convert mul_mem hl H using 1
    ring

end GlobalTheory.FinPl.ConjHalf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfLineMultipleMemIffIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateHalf_lineMultiple_mem_iff_integral : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → IsSumFrame o ζ α α₀ → α₀.IsLat M (lastKer Λ) → ∀ c : AE D, ((fun r => cA D p.e * (c * incA D (vecB o ζ r))) ∈ latV S₀ M (· = p.v) ↔ p.pr (cA D c) * p.pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.FinPl.ConjHalf.conj_half | exact GlobalTheory.FinPl.ConjHalf.conj_half | (intros; apply GlobalTheory.FinPl.ConjHalf.conj_half <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineMultipleMemSplitCoreLatticeCompletionIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LineIdeal

theorem e_half : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (α : Frame p A n) (α₀ : Frame p S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : Submodule 𝒪[k] (n → k)), IsSumFrame o ζ α α₀ → α₀.IsLat M (lastKer Λ) → ∀ c : AE D, ((fun r => p.e * (c * incA D (vecB o ζ r))) ∈ latV S₀ M (· = p.v) ↔ p.pr c ∈ 𝒪[k]) := by

  intro D k _ _ _ _ p n _ _ S₀ A L o ζ α α₀ M Λ hsum hlat c
  have key : (fun r => p.e * (c * incA D (vecB o ζ r))) =
      fun r => p.sec ((α₀.b *ᵥ Pi.single (Sum.inr 0) (p.pr c)) r) := by
    funext r
    have hb : α₀.b r (Sum.inr 0) = p.pr (incA D (vecB o ζ r)) := by
      rw [hsum]; rfl
    have hv : (α₀.b *ᵥ Pi.single (Sum.inr 0) (p.pr c)) r = α₀.b r (Sum.inr 0) * p.pr c := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hv, hb, ← map_mul, p.sec_pr, mul_comm (incA D _) c]
  rw [key, ← hlat, GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer]
  have h1 : (Pi.single (Sum.inr 0) (p.pr c) : n ⊕ Fin 1 → k) ∘ Sum.inl = 0 := by
    funext j; simp
  simp [h1]

theorem mem_latV_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ c : AE D, c ∈ idAt D P → ((fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M P ↔ (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k])) := by

  intro D k _ _ _ _ ι p I P hP n _ _ S₀ A L o ζ hζ α α₀ M Λ hM hfr c hc
  have hyid : ∀ r, (fun r => c * incA D (vecB o ζ r)) r ∈ idAt D P := fun r => Ideal.mul_mem_right _ _ hc
  have hloc : (fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M P ↔ ∀ i,
      GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M (· = (p i).v) := by
    constructor
    · intro h i
      exact GlobalTheory.FinPlLoc.smul_latV _ (GlobalTheory.FinPlLoc.idem_mem_intAt _) h
    · intro h
      refine (GlobalTheory.FinPlLoc.part_lat P S₀ M _ hM.1).2 ⟨hyid, fun v hv e he => ?_⟩
      obtain ⟨i, rfl⟩ := (hP.mem v).1 hv
      have h1 : e • (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) =
          e • (fun r => c * incA D (vecB o ζ r)) := by
        rw [smul_smul, mul_comm, (GlobalTheory.FinPlLoc.mem_idAt_iff _ e).1 he.1]
      rw [← h1]
      exact GlobalTheory.FinPlLoc.smul_latV _ he (h i)
  rw [hloc]
  refine forall_congr' fun i => ?_
  have hεid : ∀ r, (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r ∈ idAt D (· = (p i).v) :=
    fun r => Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_intAt _).1
  rw [GlobalTheory.FinPl.SplitParts.mem_latV_iff_parts D k (p i) S₀ M _ hεid]
  have he : GlobalTheory.FinPlLoc.idem D (· = (p i).v) * (p i).e = (p i).e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (FrameLat.e_mem_idAt (p i))
  have hce_id : cA D (p i).e ∈ idAt D (· = (p i).v) := by
    have := Ideal.sub_mem _ (FrameLat.sum_mem_idAt (p i)) (FrameLat.e_mem_idAt (p i))
    rwa [add_sub_cancel_left] at this
  have hce : GlobalTheory.FinPlLoc.idem D (· = (p i).v) * cA D (p i).e = cA D (p i).e :=
    (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 hce_id
  have e1 : (fun r => (p i).e * (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r) =
      fun r => (p i).e * (c * incA D (vecB o ζ r)) := by
    funext r
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (p i).e, he]
  have e2 : (fun r => cA D (p i).e * (GlobalTheory.FinPlLoc.idem D (· = (p i).v) • (fun r => c * incA D (vecB o ζ r))) r) =
      fun r => cA D (p i).e * (c * incA D (vecB o ζ r)) := by
    funext r
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (cA D (p i).e), hce]
  rw [e1, e2, e_half D k (p i) n S₀ A L o ζ (α i) (α₀ i) M (Λ i) (hfr i).1 (hfr i).2 c,
    GlobalTheory.T.conjugateHalf_lineMultiple_mem_iff_integral D k (p i) n S₀ A L o ζ (α i) (α₀ i) M (Λ i) hM (hfr i).1 (hfr i).2 c]

end GlobalTheory.LineIdeal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineMultipleMemSplitCoreLatticeCompletionIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ c : AE D, c ∈ idAt D P → ((fun r => c * incA D (vecB o ζ r)) ∈ latV S₀ M P ↔ (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ)) ∈ 𝒪[k])) := by
  first | exact @GlobalTheory.LineIdeal.mem_latV_iff | exact GlobalTheory.LineIdeal.mem_latV_iff | (intros; apply GlobalTheory.LineIdeal.mem_latV_iff <;> assumption)
end
end
