module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabilizerInCongruenceHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjOfUnimod
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core Formalism.L2.SG.Pf.IndexCocycleOrbits

namespace Formalism.L2.SG.Pf.ProdEP2Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem idxRatio_conj_of_unimod {G : Type} [Group G] (A B : Subgroup G) (s : G) (hBA : B ≤ A) (hf : B.relIndex A ≠ 0)
    (hU : IdxRatio A (cj s A) = 1) : IdxRatio A (cj s B) = (B.relIndex A : ℝ) := by
  rw [idxCocycle G A (cj s B) (cj s A) (cj_le hBA) (by rw [relIndex_cj]; exact hf), hU, relIndex_cj, mul_one]

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) {p : PlF D}

def UnimodAt (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  ∀ s ∈ StP M δ u u' w p, IdxRatio (Ag M δ u u' (p := p) w) (cj s (Ag M δ u u' (p := p) w)) = 1

theorem locIdx_at' (w : Point D.host.E (D.R.rS + 1)) (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hL : IsLoUni L) (hU : IsUpUni U) (v : ℝ) (hN : CountAt M δ u u' w hA L U hL hU v)
    (hO : UnimodAt M δ u u' (p := p) w) :
    IdxRatio (AP M δ u u' w p) (CPL M δ u u' w hA L U hL hU) = v := by
  rw [idxRatio_map]
  obtain ⟨N, π, hR, hHN, hg, hBA, hfA, hv⟩ := hN
  have hC := cShape M δ u u' hA L U hL hU w
  have hCS : cj (g0 M δ hA L U hL hU) (KP M p ⊓ StabX p (XP M δ u u' w L U)) ≤ StP M δ u u' w p := by
    rw [← hC]
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  show IdxRatio (Ag M δ u u' w) (Cg M δ u u' w hA L U hL hU) = v
  rw [hC, cj_eq_cj_img hR hHN hg hCS, idxRatio_conj_of_unimod _ _ _ hBA hfA (hO _ (hR.mem _ hg)), hv]

variable (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def StepsU : Prop :=
  ∀ (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D),
    CountAt M δ u u' w (hE.1 p) L U hE.2.2.2.2.2.2.2.1 hE.2.2.2.2.2.2.2.2.1
      (Formalism.L2.SG.LsDatumB.wtL M δ (D.mem u).A.T (D.mem u').A.T p w
        (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p)) ∧
    UnimodAt M δ u u' (p := p) w

theorem locIdxC_of_count (h : StepsU M δ u u' F0 what₂) : LocIdxC M δ u u' F0 what₂ := by
  intro γ w F' L U hE p
  obtain ⟨hN, hO⟩ := h γ w F' L U hE p
  exact locIdx_at' M δ u u' w _ L U _ _ _ hN hO

end Formalism.L2.SG.Pf.ProdEP2Cut
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolAct
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolAct

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def sbs {D : Formalism.BasicNotions.D7} (b : MatR D) : MatR D := Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * b * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS

def LiftData (γ : TermDef.Term D u u' F0 what₂) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (a' : GLR D) (b : MatR D) (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  IsLoUni (a' : MatR D) ∧ IsUpUni b ∧ (a' : MatR D) * ZhatOM (ZhatL (lf D F0) F') * b = ZhatOM (ZhatL (lf D F0) F') ∧
    Formalism.L2.SG.Pf.StabIntSh.EntryShape D (a' : MatR D) b ∧
    ν ∈ NLam γ.lam (lf D F0) ∧ m ∈ NLam γ.lam F' ∧
    (∀ c, ν (frame (lf D F0) c) = ∑ d, (a' : MatR D).conjTranspose d c • frame (lf D F0) d) ∧
    (∀ c, m (frame F' c) = ∑ d, sbs b d c • frame F' d) ∧
    F₂ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam (ZhatL (lf D F0) F') ∧
    TermDef.Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls F₂ ∧
    ∀ c, frame F₂ c = ν⁻¹ (m (frame F' c))

def MoveCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ (a' : GLR D) (b : MatR D), IsLoUni (a' : MatR D) → IsUpUni b →
      (a' : MatR D) * ZhatOM (ZhatL (lf D F0) F') * b = ZhatOM (ZhatL (lf D F0) F') →
      Formalism.L2.SG.Pf.StabIntSh.EntryShape D (a' : MatR D) b →
      ∃ ν m F₂, LiftData u u' F0 what₂ γ F' a' b ν m F₂

def OntoCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam (ZhatL (lf D F0) F'),
      TermDef.Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls F'' →
      ∃ (a' : GLR D) (b : MatR D) (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V), LiftData u u' F0 what₂ γ F' a' b ν m F''

def FibreCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ (a₁ : GLR D) (b₁ : MatR D) (ν₁ m₁ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₁ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (a₂ : GLR D) (b₂ : MatR D) (ν₂ m₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (x₁ x₂ : GLR D), (x₁ : MatR D) = L⁻¹ * (a₁ : MatR D) * L → (x₂ : MatR D) = L⁻¹ * (a₂ : MatR D) * L →
      LiftData u u' F0 what₂ γ F' a₁ b₁ ν₁ m₁ F₁ → LiftData u u' F0 what₂ γ F' a₂ b₂ ν₂ m₂ F₂ →
      (CntLocal.NilradicalFlagMoved F0 γ.lam F₁ F₂ ↔ x₁⁻¹ * x₂ ∈ PairVal.stabAut D u u' F0 what₂ γ F' L)

end Formalism.L2.SG.Pf.ZsVolAct

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BaseAt
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TauSecondValue
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TauTau
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

def sgnU : GLp p :=
  ⟨Formalism.L2.SG.LsDatumB.sgnP p, Formalism.L2.SG.LsDatumB.sgnP p, Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p,
    Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p⟩

def tau : GG p →* GG p where
  toFun x := (x.1, MulOpposite.op (sgnU p * x.2.unop * sgnU p))
  map_one' := by
    have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
    ext1
    · rfl
    · apply MulOpposite.unop_injective
      show sgnU p * (1 : GLp p) * sgnU p = 1
      rw [mul_one, hs]
  map_mul' x y := by
    have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
    ext1
    · rfl
    · apply MulOpposite.unop_injective
      simp only [Prod.snd_mul, MulOpposite.unop_mul, MulOpposite.unop_op]
      calc sgnU p * (y.2.unop * x.2.unop) * sgnU p
          = sgnU p * y.2.unop * (sgnU p * sgnU p) * x.2.unop * sgnU p := by rw [hs]; group
        _ = _ := by group

theorem tau_tau (x : GG p) : tau p (tau p x) = x := by
  have hs : sgnU p * sgnU p = 1 := Units.ext (Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ p)
  ext1
  · rfl
  · apply MulOpposite.unop_injective
    show sgnU p * (sgnU p * x.2.unop * sgnU p) * sgnU p = x.2.unop
    calc sgnU p * (sgnU p * x.2.unop * sgnU p) * sgnU p = (sgnU p * sgnU p) * x.2.unop * (sgnU p * sgnU p) := by
          group
      _ = _ := by rw [hs]; group

end Formalism.L2.SG.Pf.CountAt
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

theorem sconj_apply (ρ : MP p) (a b : Fin (D.R.rS + 1)) :
    (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) a b =
      (-1 : (D.s.atP p).Ep) ^ (D.R.rS - a.val) * ρ a b * (-1) ^ (D.R.rS - b.val) := by
  simp [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem sconj_up {ρ : MP p} (h : IsUpUni ρ) :
    IsUpUni (Formalism.L2.SG.LsDatumB.sgnP p * ρ * Formalism.L2.SG.LsDatumB.sgnP p) := by
  intro a b
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rw [sconj_apply, (h a b).1 hab]; simp
  · subst hab
    rw [sconj_apply, (h a a).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]; simp

theorem tau_second_value (x : GG p) : (((tau p x).2.unop : GLp p) : MP p) =
    Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p := rfl

theorem tau_mem_UP {x : GG p} (hx : x ∈ UP p) : tau p x ∈ UP p :=
  ⟨hx.1, by rw [tau_second_value]; exact sconj_up p hx.2⟩

theorem tau_mem_KP {x : GG p} (hx : x ∈ KP M p) : tau p x ∈ KP M p := by
  refine ⟨hx.1, ?_⟩
  show Formalism.MainNotions.S.TieN.IntUp (M p) (((tau p x).2.unop : GLp p) : MP p)
  rw [tau_second_value]
  obtain ⟨h1, h2, h3⟩ := hx.2
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩
  · rw [sconj_apply, h1 a, mul_one, ← pow_add, ← two_mul, pow_mul]; simp
  · rw [sconj_apply, h2 a b hab]; simp
  · rw [sconj_apply]
    exact Subring.mul_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _) (h3 a b))
      (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

def phi (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) (Z : MP p) : MP p :=
  Z * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w

theorem phi_smul (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) {x : GG p}
    (hx : x ∈ UP p) (Z : MP p) : phi p δ T T' w (x • Z) = tau p x • phi p δ T T' w Z := by
  have hss := Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ (D := D) p
  have hc : ((x.1 : GLp p) : MP p) * Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w *
      (Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p) =
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w := by
    have hu := sconj_up p hx.2
    refine Formalism.L2.SG.Pf.FibQ.corner_fix p (fun a b h => (hx.1 a b).1 h) (fun a => (hx.1 a a).2 rfl)
      (fun a b h => (hu a b).1 h) (fun a => (hu a a).2 rfl) (fun a b h => ?_)
    simp only [Formalism.L2.SG.Pf.LocOrbSumPf.shM, Matrix.of_apply]
    rw [if_neg h]
  simp only [phi, smul_def, tau_second_value]
  show ((x.1 : GLp p) : MP p) * Z * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p +
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w =
    ((x.1 : GLp p) : MP p) * (Z * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ T T' p w) *
      (Formalism.L2.SG.LsDatumB.sgnP p * ((x.2.unop : GLp p) : MP p) * Formalism.L2.SG.LsDatumB.sgnP p)
  rw [Matrix.mul_add, Matrix.add_mul, hc]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.L2.SG.LsDatumB.sgnP p) (Formalism.L2.SG.LsDatumB.sgnP p), hss, Matrix.one_mul]

theorem phi_inj (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) {Z Z' : MP p}
    (h : phi p δ T T' w Z = phi p δ T T' w Z') : Z = Z' := by
  have hss := Formalism.L2.SG.Pf.FibQ.permSign_mul_self₂ (D := D) p
  unfold phi at h
  have h2 := add_right_cancel h
  calc Z = Z * Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.LsDatumB.sgnP p := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]
    _ = Z' * Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.LsDatumB.sgnP p := by rw [h2]
    _ = Z' := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]

end Formalism.L2.SG.Pf.CountAt
end
end

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)

def BaseAt (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) : Prop :=
  ∃ c : UP p, phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = (c : GG p) • a.mat ∧
    ∀ x : UP p, ((x : GG p) • phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) =
      phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) ↔ (x : GG p) • a.mat = a.mat)

end Formalism.L2.SG.Pf.CountAt
end
end
