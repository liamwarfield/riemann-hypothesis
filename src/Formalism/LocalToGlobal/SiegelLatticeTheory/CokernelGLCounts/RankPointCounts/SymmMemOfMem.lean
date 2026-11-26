module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlLineHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnitaryNormalVectorCount
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SRat {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {s | s ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) ∧ s F.fl.z - F.fl.z ∈ Xsp F}

def NmlPtDC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t1 t2 : TauC Y u u', Gt t1 ≠ 0 → Gt t2 ≠ 0 → ptPN t1 = γ → ptPN t2 = γ →
          (Y.tO u u').rowOf t1 = (Y.tO u u').rowOf t2 →
          ∃ σ ∈ SRat (lf D (X.Fu u)), ∃ s' ∈ SRat (lf D (X.Fu u')), t2.lin = σ * t1.lin * s'

def UnitaryNormalVectorCount : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
        ∀ t0 t1 t2 : TauC Y u u', Gt t0 ≠ 0 → Gt t1 ≠ 0 → Gt t2 ≠ 0 →
          RelC Y u u' t0 t1 → RelC Y u u' t0 t2 → t1.G = t0.G → t2.G = t0.G →
          (∃ σ ∈ SRat (lf D (X.Fu u)), ∃ s' ∈ SRat (lf D (X.Fu u')), t2.lin = σ * t1.lin * s') →
          coefA Y u u' t0 t1 = coefA Y u u' t0 t2 → coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2 →
          nmlOf Y u u' t1 = nmlOf Y u u' t2

theorem nmlSep_of (hP : NmlPtDC) (hG : UnitaryNormalVectorCount) : NmlSep := by
  intro Cg cb Cw cT CT C0
  obtain ⟨A1, B1, h1⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨A2, B2, h2⟩ := hG Cg cb Cw cT CT C0
  refine ⟨max A1 A2, max B1 B2, fun C' Cl hC hl D large₂ X Y u u' hctx γ hγ t0 t1 t2 g0 g1 g2 p0 p1 p2 r1 r2 ca ca' => ?_⟩
  have hdc := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hl) D large₂ X Y u u' hctx γ hγ t1 t2 g1 g2 p1 p2
    (r1.1.trans r2.1.symm)
  have e0 := gval_occ (t := t0) (hG := p0 ▸ hγ)
  have e1 := gval_occ (t := t1) (hG := p1 ▸ hγ)
  have e2 := gval_occ (t := t2) (hG := p2 ▸ hγ)
  have hG1 : t1.G = t0.G := by
    rw [Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t1), Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t0)]
    rw [e1, e0, p1, p0]
  have hG2 : t2.G = t0.G := by
    rw [Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t2), Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t0)]
    rw [e2, e0, p2, p0]
  exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hl) D large₂ X Y u u' hctx t0 t1 t2 g0 g1 g2 r1 r2
    hG1 hG2 hdc ca ca'

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TauExists
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FvecMemAsp
noncomputable section

open Module Matrix
open Formalism.MainNotions.S Formalism.BasicNotions

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

def Asp (F : FlagG S r T) (F' : FlagG S r T') : Submodule E S.V :=
  Submodule.span E (Set.range (Sum.elim F.fvec F'.fvec))

def Hsp (F : FlagG S r T) (F' : FlagG S r T') : Submodule E S.V := Lat.orth S (Asp F F')

theorem fvec_mem_Asp (F : FlagG S r T) (F' : FlagG S r T') (a : Fin (r + 1)) : F.fvec a ∈ Asp F F' :=
  Submodule.subset_span ⟨Sum.inl a, rfl⟩

theorem fvec'_mem_Asp (F : FlagG S r T) (F' : FlagG S r T') (a : Fin (r + 1)) : F'.fvec a ∈ Asp F F' :=
  Submodule.subset_span ⟨Sum.inr a, rfl⟩

theorem X_le_Asp (F : FlagG S r T) (F' : FlagG S r T') : F.X ≤ Asp F F' := by
  rw [FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have := fvec_mem_Asp F F' (Fin.castSucc a)
  simpa [FlagG.fvec, Fin.snoc_castSucc] using this

theorem z_mem_Asp (F : FlagG S r T) (F' : FlagG S r T') : F.z ∈ Asp F F' := by
  have := fvec_mem_Asp F F' (Fin.last r)
  simpa [FlagG.fvec, Fin.snoc_last] using this

theorem Asp_symm (F : FlagG S r T) (F' : FlagG S r T') : Asp F' F = Asp F F' := by
  unfold Asp
  rw [Set.Sum.elim_range, Set.Sum.elim_range, Set.union_comm]

theorem hT_A_H {F : FlagG S r T} {F' : FlagG S r T'} {a w : S.V} (ha : a ∈ Asp F F') (hw : w ∈ Hsp F F') :
    S.hT a w = 0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 hw a ha

theorem hT_H_A {F : FlagG S r T} {F' : FlagG S r T'} {a w : S.V} (ha : a ∈ Asp F F') (hw : w ∈ Hsp F F') :
    S.hT w a = 0 := by rw [hT_swap, hT_A_H ha hw, star_zero]

theorem finrank_Asp (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) :
    finrank E (Asp F F') = 2 * r + 2 := by
  rw [Asp, finrank_span_eq_card (PI.PairCorankPos.W.linIndep F F' hG), Fintype.card_sum, Fintype.card_fin]
  ring

theorem Asp_inf_Hsp (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) : Asp F F' ⊓ Hsp F F' = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxH⟩ := Submodule.mem_inf.1 hx
  exact (Submodule.mem_bot E).2 (CorankRelation.span_pair_orth_eq_zero F F' hG x hxA fun i =>
    (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 hxH _ (Submodule.subset_span ⟨i, rfl⟩))

theorem finrank_Hsp (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) :
    finrank E (Hsp F F') + (2 * r + 2) = finrank E S.V := by
  have := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (Asp F F')
  rw [finrank_Asp F F' hG] at this
  exact this

theorem isCompl_AH (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) :
    IsCompl (Asp F F') (Hsp F F') := by
  refine ⟨disjoint_iff.2 (Asp_inf_Hsp F F' hG), codisjoint_iff.2 ?_⟩
  refine Submodule.eq_top_of_finrank_eq ?_
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Asp F F') (Hsp F F')
  rw [Asp_inf_Hsp F F' hG, finrank_bot, add_zero, finrank_Asp F F' hG] at h1
  have h2 := finrank_Hsp F F' hG
  omega

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

noncomputable section

open Module Matrix
open Formalism.MainNotions.S Formalism.BasicNotions

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

private theorem sub_mem_X_of_mem_Asp_of_hT_orth {F : FlagG S r T} {F' : FlagG S r T'} (hG : Gflag F F' ≠ 0) (hT : T ≠ 0)
    (hTs : star T = T) (σ : S.V →ₗ[E] S.V) (hσf : ∀ x ∈ F.X, σ x - x ∈ F.X) (hσz : σ F.z - F.z ∈ F.X)
    (hσω : σ (omp F F') - omp F F' ∈ F.X) {a : S.V} (ha : a ∈ Asp F F')
    (hX : ∀ x ∈ F.X, S.hT x a = 0) : σ a - a ∈ F.X := by
  classical
  have hz : F.z ∈ Asp F F' := by
    simpa [FlagG.fvec, Fin.snoc_last] using fvec_mem_Asp F F' (Fin.last r)
  have hom : omp F F' ∈ Asp F F' := by
    unfold omp
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (fvec'_mem_Asp F F' b)
  have homX : ∀ x ∈ F.X, S.hT x (omp F F') = 0 := by
    intro x hx
    have hle : F.X ≤ LinearMap.ker (S.hT.flip (omp F F')) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      simpa [brS] using brS_omp_e F F' i
    simpa using hle hx
  have hzX : ∀ x ∈ F.X, S.hT x F.z = 0 := by
    intro x hx
    have h := brS_swap (S := S) x F.z
    simp only [brS] at h
    rw [h, hT_z_X F hx, star_zero]
  have hzz : S.hT F.z F.z = -T := F.z_norm
  have hzo : S.hT F.z (omp F F') = Dl F F' (r + 1) := by simpa [brS] using pairing_omegaPrime_z F F'
  have hoz : S.hT (omp F F') F.z = star (Dl F F' (r + 1)) := by
    have h := brS_swap (S := S) (omp F F') F.z
    simp only [brS] at h
    rw [h, hzo]
  have hoo : S.hT (omp F F') (omp F F') = -T' * (Dl F F' r * star (Dl F F' r)) := by
    simpa [brS] using brS_omp_omp F F'
  obtain ⟨y0, hy0⟩ : ∃ y0 : S.V, y0 = T • omp F F' + Dl F F' (r + 1) • F.z := ⟨_, rfl⟩
  have hy0A : y0 ∈ Asp F F' := by
    rw [hy0]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hom) (Submodule.smul_mem _ _ hz)
  have hXy0 : ∀ x ∈ F.X, S.hT x y0 = 0 := by
    intro x hx
    rw [hy0]
    simp [homX x hx, hzX x hx]
  have hzy0 : S.hT F.z y0 = 0 := by
    rw [hy0]
    simp only [map_add (f := _), map_smul, smul_eq_mul, hzo, hzz]
    ring
  have hy0z : S.hT y0 F.z = 0 := by
    rw [hy0]
    simp only [map_add (f := _), map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, hoz, hzz, hTs]
    ring
  have hy0o : S.hT y0 (omp F F') = T * (-T' * (Dl F F' r * star (Dl F F' r))) + star (Dl F F' (r + 1)) * Dl F F' (r + 1) := by
    rw [hy0]
    simp only [map_add (f := _), map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, hoo, hzo, hTs]
  have hy0y0 : S.hT y0 y0 = T * Gflag F F' := by
    have e : S.hT y0 y0 = T * S.hT y0 (omp F F') + Dl F F' (r + 1) * S.hT y0 F.z := by
      conv_lhs => rw [show S.hT y0 y0 = S.hT y0 (T • omp F F' + Dl F F' (r + 1) • F.z) by rw [← hy0]]
      simp only [map_add (f := _), map_smul, smul_eq_mul]
    rw [e, hy0o, hy0z]
    simp only [Gflag]
    ring
  have hy0ne : S.hT y0 y0 ≠ 0 := by
    rw [hy0y0]
    exact mul_ne_zero hT hG
  have horth : ∀ u : S.V, (∀ x ∈ F.X, S.hT x u = 0) → S.hT F.z u = 0 → u ∈ Asp F F' →
      u ∈ Qsp F (Hsp F F') := by
    intro u h1 h2 h3
    have hle : F.X ⊔ E ∙ F.z ⊔ Hsp F F' ≤ LinearMap.ker (S.hT.flip u) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro x hx
        simpa using h1 x hx
      · rw [Submodule.span_singleton_le_iff_mem]
        simpa using h2
      · intro x hx
        simpa using hT_H_A h3 hx
    simp only [Qsp, Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    simpa using hle hx
  obtain ⟨v, hv⟩ : ∃ v : S.V, v = a - (-(S.hT F.z a) / T) • F.z - (S.hT y0 a / (T * Gflag F F')) • y0 :=
    ⟨_, rfl⟩
  have hvA : v ∈ Asp F F' := by
    rw [hv]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ ha (Submodule.smul_mem _ _ hz))
      (Submodule.smul_mem _ _ hy0A)
  have hvXo : ∀ x ∈ F.X, S.hT x v = 0 := by
    intro x hx
    rw [hv]
    simp [hX x hx, hzX x hx, hXy0 x hx]
  have hzv : S.hT F.z v = 0 := by
    rw [hv]
    simp only [map_sub, map_smul, smul_eq_mul, hzz, hzy0]
    field_simp
    ring
  have hy0v : S.hT y0 v = 0 := by
    rw [hv]
    simp only [map_sub, map_smul, smul_eq_mul, hy0z, hy0y0]
    field_simp
    ring
  have hy0Q : y0 ∈ Qsp F (Hsp F F') := horth y0 hXy0 hzy0 hy0A
  have hvQ : v ∈ Qsp F (Hsp F F') := horth v hvXo hzv hvA
  have hvX : v ∈ F.X := line F hT (Hsp F F') (fun x hx h hh => hT_A_H (X_le_Asp F F' hx) hh)
      (fun h hh => hT_A_H hz hh)
      (fun x hx hxH => by
        have hm : x ∈ Asp F F' ⊓ Hsp F F' := ⟨X_le_Asp F F' hx, hxH⟩
        rwa [Asp_inf_Hsp F F' hG, Submodule.mem_bot] at hm)
      (by have := finrank_Hsp F F' hG; omega)
      hy0Q (by simpa [brS] using hy0ne) hvQ (by simpa [brS] using hy0v)
  have hW : ∀ u, u ∈ F.X.comap (σ - LinearMap.id) ↔ σ u - u ∈ F.X := fun u => by simp
  have hy0W : σ y0 - y0 ∈ F.X := by
    have e : σ y0 - y0 = T • (σ (omp F F') - omp F F') + Dl F F' (r + 1) • (σ F.z - F.z) := by
      rw [hy0]
      simp only [map_add (f := _), map_smul, smul_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hσω) (Submodule.smul_mem _ _ hσz)
  have hav : a = v + (-(S.hT F.z a) / T) • F.z + (S.hT y0 a / (T * Gflag F F')) • y0 := by
    rw [hv]
    abel
  rw [← hW, hav]
  exact Submodule.add_mem _ (Submodule.add_mem _ ((hW v).2 (hσf v hvX))
    (Submodule.smul_mem _ _ ((hW _).2 hσz))) (Submodule.smul_mem _ _ ((hW _).2 hy0W))

theorem tau_exists (F : FlagG S r T) (F1 : FlagG S r T') (hG : Gflag F F1 ≠ 0) (hT : T ≠ 0) (hTs : star T = T)
    (hT' : T' ≠ 0) (hTs' : star T' = T') (σ ς : S.V ≃ₗ[E] S.V) (hσi : σ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hσf : ∀ x ∈ F.X, σ x - x ∈ F.X) (hσX : ∀ x ∈ F.X, σ.symm x ∈ F.X) (hσz : σ F.z - F.z ∈ F.X)
    (hςf : ∀ x ∈ F1.X, ς x - x ∈ F1.X) (hςz : ς F1.z - F1.z ∈ F1.X)
    (hσω : σ (omp F F1) - omp F F1 ∈ F.X) (hςω : ς (omp F1 F) - omp F1 F ∈ F1.X)
    (h3 : ∀ w ∈ Hsp F F1, ∃ w0 ∈ Hsp F F1, σ w - w0 ∈ F.X ∧ ς w - w0 ∈ F1.X) :
    ∃ τ : S.V ≃ₗ[E] S.V, τ ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ a ∈ Asp F F1, τ a = a) ∧
      (∀ y ∈ Lat.orth S F.X, τ y - σ y ∈ F.X) ∧ (∀ y ∈ Lat.orth S F1.X, τ y - ς y ∈ F1.X) := by
  classical
  have hc := isCompl_AH F F1 hG
  have hσ : ∀ x y, S.hT (σ x) (σ y) = S.hT x y := hσi
  choose p hpH hpσ hpς using fun w : Hsp F F1 => h3 w.1 w.2
  have huniq : ∀ (w : Hsp F F1) (u : S.V), u ∈ Hsp F F1 → σ w - u ∈ F.X → p w = u := by
    intro w u hu hσu
    have hd : p w - u ∈ Asp F F1 ⊓ Hsp F F1 := by
      refine ⟨X_le_Asp F F1 ?_, Submodule.sub_mem _ (hpH w) hu⟩
      have h := Submodule.sub_mem _ hσu (hpσ w)
      rwa [sub_sub_sub_cancel_left] at h
    rw [Asp_inf_Hsp F F1 hG, Submodule.mem_bot] at hd
    exact sub_eq_zero.mp hd
  let Pl : Hsp F F1 →ₗ[E] S.V :=
    { toFun := p
      map_add' := fun w1 w2 => huniq (w1 + w2) (p w1 + p w2) (Submodule.add_mem _ (hpH w1) (hpH w2)) (by
        have h := Submodule.add_mem _ (hpσ w1) (hpσ w2)
        rw [Submodule.coe_add, map_add (f := _)]
        convert h using 1
        abel)
      map_smul' := fun c w => huniq (c • w) (c • p w) (Submodule.smul_mem _ c (hpH w)) (by
        have h := Submodule.smul_mem _ c (hpσ w)
        rw [Submodule.coe_smul, map_smul]
        convert h using 1
        rw [smul_sub]) }
  have hp0 : p 0 = 0 := map_zero Pl
  let τl : S.V →ₗ[E] S.V := (Asp F F1).subtype ∘ₗ (Asp F F1).projectionOnto (Hsp F F1) hc +
    Pl ∘ₗ (Hsp F F1).projectionOnto (Asp F F1) hc.symm
  have hsplit : ∀ y, ∃ a ∈ Asp F F1, ∃ w : Hsp F F1, y = a + w ∧ τl y = a + p w := fun y =>
    ⟨_, Submodule.projection_apply_mem hc y, (Hsp F F1).projectionOnto (Asp F F1) hc.symm y,
      (Submodule.projection_add_projection_eq_self hc y).symm, rfl⟩
  have hσXH : ∀ x ∈ F.X, ∀ w : Hsp F F1, S.hT (σ w) x = 0 ∧ S.hT x (σ w) = 0 := by
    intro x hx w
    have hx' : σ.symm x ∈ Asp F F1 := X_le_Asp F F1 (hσX x hx)
    have e : x = σ (σ.symm x) := (σ.apply_symm_apply x).symm
    constructor
    · rw [e, hσ]
      exact hT_H_A hx' w.2
    · rw [e, hσ]
      exact hT_A_H hx' w.2
  have hpp : ∀ w w' : Hsp F F1, S.hT (p w) (p w') = S.hT (w : S.V) w' := by
    intro w w'
    obtain ⟨x, hx, hxe⟩ : ∃ x ∈ F.X, p w = σ w - x := ⟨σ w - p w, hpσ w, by abel⟩
    obtain ⟨x', hx', hxe'⟩ : ∃ x' ∈ F.X, p w' = σ w' - x' := ⟨σ w' - p w', hpσ w', by abel⟩
    rw [hxe, hxe']
    simp only [map_sub, LinearMap.sub_apply, hσ, (hσXH x hx w').2, (hσXH x' hx' w).1,
      hT_X_X F hx hx', sub_zero]
  have hiso : ∀ x y, S.hT (τl x) (τl y) = S.hT x y := by
    intro x y
    obtain ⟨a, ha, w, hx, hτx⟩ := hsplit x
    obtain ⟨a', ha', w', hy, hτy⟩ := hsplit y
    rw [hτx, hτy, hx, hy]
    simp only [map_add (f := _), LinearMap.add_apply, hT_A_H ha (hpH w'), hT_H_A ha' (hpH w),
      hT_A_H ha w'.2, hT_H_A ha' w.2, hpp, add_zero, zero_add]
  have hinj : Function.Injective τl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine S.nondeg.1 x fun y => ?_
    rw [← hiso x y, hx, map_zero, LinearMap.zero_apply]
  refine ⟨LinearEquiv.ofInjectiveEndo τl hinj, ?_, ?_, ?_, ?_⟩
  · show ∀ x y, S.hT (LinearEquiv.ofInjectiveEndo τl hinj x) (LinearEquiv.ofInjectiveEndo τl hinj y) =
      S.hT x y
    intro x y
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    exact hiso x y
  · intro a ha
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    obtain ⟨a', ha', w, hs, hτa⟩ := hsplit a
    have hw0 : (w : S.V) = 0 := by
      have hwA : (w : S.V) ∈ Asp F F1 := by
        have e : (w : S.V) = a - a' := by rw [hs]; abel
        rw [e]
        exact Submodule.sub_mem _ ha ha'
      have hm : (w : S.V) ∈ Asp F F1 ⊓ Hsp F F1 := ⟨hwA, w.2⟩
      rwa [Asp_inf_Hsp F F1 hG, Submodule.mem_bot] at hm
    have hw : w = 0 := Subtype.ext hw0
    rw [hτa, hw, hp0, add_zero]
    rw [hs, hw0, add_zero]
  · intro y hy
    have hyo : ∀ x ∈ F.X, S.hT x y = 0 := by
      simpa [Lat.orth, Submodule.mem_iInf] using hy
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    obtain ⟨a, ha, w, hs, hτy⟩ := hsplit y
    have hX : ∀ x ∈ F.X, S.hT x a = 0 := by
      intro x hx
      have e : a = y - w := by rw [hs]; abel
      rw [e, map_sub, hyo x hx, hT_A_H (X_le_Asp F F1 hx) w.2, sub_zero]
    have key := sub_mem_X_of_mem_Asp_of_hT_orth hG hT hTs σ.toLinearMap hσf hσz hσω ha hX
    rw [hτy, hs, map_add (f := _)]
    have e : a + p w - (σ a + σ w) = -(σ.toLinearMap a - a) - (σ w - p w) := by
      simp only [LinearEquiv.coe_coe]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ key) (hpσ w)
  · intro y hy
    have hyo : ∀ x ∈ F1.X, S.hT x y = 0 := by
      simpa [Lat.orth, Submodule.mem_iInf] using hy
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    obtain ⟨a, ha, w, hs, hτy⟩ := hsplit y
    have hX : ∀ x ∈ F1.X, S.hT x a = 0 := by
      intro x hx
      have hxA : x ∈ Asp F F1 := by
        rw [← Asp_symm F F1]
        exact X_le_Asp F1 F hx
      have e : a = y - w := by rw [hs]; abel
      rw [e, map_sub, hyo x hx, hT_A_H hxA w.2, sub_zero]
    have hG' : Gflag F1 F ≠ 0 := by rw [Gflag_swap]; exact hG
    have ha' : a ∈ Asp F1 F := by rw [Asp_symm]; exact ha
    have key := sub_mem_X_of_mem_Asp_of_hT_orth hG' hT' hTs' ς.toLinearMap hςf hςz hςω ha' hX
    rw [hτy, hs, map_add (f := _)]
    have e : a + p w - (ς a + ς w) = -(ς.toLinearMap a - a) - (ς w - p w) := by
      simp only [LinearEquiv.coe_coe]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ key) (hpς w)

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Grp

variable {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)

theorem symm_mem_of_mem (s : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Submodule D.host.E (VS D).V)
    (h : ∀ x ∈ U, s x ∈ U) : ∀ x ∈ U, s.symm x ∈ U := by
  intro x hx
  let f : U →ₗ[D.host.E] U :=
    (s : (VS D).V →ₗ[D.host.E] (VS D).V).restrict (p := U) (q := U) (fun y hy => h y hy)
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply s.injective
    exact congrArg Subtype.val hab
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨x, hx⟩
  have hyx : s y.1 = x := congrArg Subtype.val hy
  rw [← hyx, LinearEquiv.symm_apply_apply]
  exact y.2

theorem Xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  exact Formalism.L2.SG.Pf.xflag_mono_td F (Nat.le_succ j)

theorem Xflag_le_X (j : ℕ) : Xflag F j ≤ Xsp F := by
  exact PI.DCRelEquiv.UnitaryGroupMassFormula.Xflag_le_X F j

theorem X_eq_Xflag : Xsp F = Xflag F D.R.rS := by
  exact (Formalism.L2.SG.Pf.xflag_r F).symm

theorem flag_pres {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j)
    (j : ℕ) : ∀ x ∈ Xflag F j, s x ∈ Xflag F j := by
  intro x hx
  cases j with
  | zero =>
    rw [Formalism.L2.SG.Pf.xflag_zero_td F, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem _
  | succ j =>
    have h1 := Xflag_mono F j (hs j x hx)
    have h2 := Submodule.add_mem _ h1 hx
    rwa [sub_add_cancel] at h2

theorem flag_inv {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) :
    ∀ j, ∀ x ∈ Xflag F (j + 1), s.symm x - x ∈ Xflag F j := by
  intro j x hx
  have hy : s.symm x ∈ Xflag F (j + 1) :=
    symm_mem_of_mem s (Xflag F (j + 1)) (flag_pres F hs (j + 1)) x hx
  have h1 := hs j (s.symm x) hy
  rw [LinearEquiv.apply_symm_apply] at h1
  have h2 := Submodule.neg_mem _ h1
  rwa [neg_sub] at h2

theorem flag_mul {s t : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) (ht : ∀ j, ∀ x ∈ Xflag F (j + 1), t x - x ∈ Xflag F j) :
    ∀ j, ∀ x ∈ Xflag F (j + 1), (s * t) x - x ∈ Xflag F j := by
  intro j x hx
  have htx : t x ∈ Xflag F (j + 1) := flag_pres F ht (j + 1) x hx
  have h1 := Submodule.add_mem _ (hs j (t x) htx) (ht j x hx)
  show s (t x) - x ∈ Xflag F j
  rwa [sub_add_sub_cancel] at h1

theorem X_pres {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : ∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) :
    ∀ x ∈ Xsp F, s x ∈ Xsp F := by
  intro x hx
  rw [X_eq_Xflag F] at hx ⊢
  exact flag_pres F hs _ x hx

theorem SRat_inv {s : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : s ∈ SRat F) : s.symm ∈ SRat F := by
  simp only [SRat, Set.mem_setOf_eq] at hs ⊢
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hs.1, flag_inv F hs.2.1, ?_⟩
  have h1 := symm_mem_of_mem s (Xsp F) (X_pres F hs.2.1) _ hs.2.2
  have h2 := Submodule.neg_mem _ h1
  rw [map_sub, LinearEquiv.symm_apply_apply, neg_sub] at h2
  exact h2

theorem SRat_mul {s t : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hs : s ∈ SRat F) (ht : t ∈ SRat F) : s * t ∈ SRat F := by
  simp only [SRat, Set.mem_setOf_eq] at hs ht ⊢
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hs.1 ht.1, flag_mul F hs.2.1 ht.2.1, ?_⟩
  have hw := ht.2.2
  have hsw := X_pres F hs.2.1 _ hw
  have key : (s * t) F.fl.z - F.fl.z = (s F.fl.z - F.fl.z) +
      (s (t F.fl.z - F.fl.z) - (t F.fl.z - F.fl.z)) + (t F.fl.z - F.fl.z) := by
    show s (t F.fl.z) - F.fl.z = _
    rw [map_sub]; abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.add_mem _ hs.2.2 (Submodule.sub_mem _ hsw hw)) hw

theorem perp_pres {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hi : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hX : ∀ x ∈ Xsp F, n.symm x ∈ Xsp F) : ∀ y ∈ orth (VS D) (Xsp F), n y ∈ orth (VS D) (Xsp F) := by
  have hi' : ∀ a b, (VS D).hT (n a) (n b) = (VS D).hT a b := hi
  intro y hy
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
  intro x hx
  have h1 := hi' (n.symm x) y
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1]
  exact hy _ (hX x hx)

theorem NRat_inv {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) : n.symm ∈ NRat F := by
  simp only [NRat, Set.mem_setOf_eq] at hn ⊢
  have hX : ∀ x ∈ Xsp F, n.symm x ∈ Xsp F := symm_mem_of_mem n (Xsp F) (X_pres F hn.2.1)
  have hO := perp_pres F hn.1 hX
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).inv_mem hn.1, flag_inv F hn.2.1, ?_⟩
  intro x hx
  have hy := symm_mem_of_mem n (orth (VS D) (Xsp F)) hO x hx
  have h2 := Submodule.neg_mem _ (hn.2.2 _ hy)
  rw [LinearEquiv.apply_symm_apply, neg_sub] at h2
  exact h2

theorem NRat_mul {n m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NRat F) (hm : m ∈ NRat F) : n * m ∈ NRat F := by
  simp only [NRat, Set.mem_setOf_eq] at hn hm ⊢
  refine ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).mul_mem hn.1 hm.1, flag_mul F hn.2.1 hm.2.1, ?_⟩
  intro x hx
  have hw := hm.2.2 x hx
  have hnw := X_pres F hn.2.1 _ hw
  have key : (n * m) x - x = (n x - x) + (n (m x - x) - (m x - x)) + (m x - x) := by
    show n (m x) - x = _
    rw [map_sub]; abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.add_mem _ (hn.2.2 x hx) (Submodule.sub_mem _ hnw hw)) hw

end Grp

end Formalism.L2.SG.NGCut.NormalVectorPairings
