module

public import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KppOffCOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumBCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClassFrameCut
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermsAtPtFinite
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HermitianCombinationZ

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Attr

variable {D : D7} {X : HidaSetting D}

abbrev GTu (Y : Full X) (u : D.what₂.Word) : Type :=
  GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)

def jT {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) : ℕ :=
  D.R.rS - Module.finrank D.host.E (Isp (lf D (X.Fu u)).fl (frq X t.rep).fl)

def labT {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) : ℕ → D.host.E :=
  fun l => if l ≤ jT t then Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l else 0

def relSet (Y : Full X) (u : D.what₂.Word) : Set (GTu Y u) := (Y.tO u u).degSet ∩ {t | t.relevant}

def massC (Y : Full X) (u : D.what₂.Word) : ℝ := massRows D (X.Fu u) (Y.what₂ u)

def dpiC (X : HidaSetting D) (u : D.what₂.Word) : ℝ := (Module.finrank ℂ (X.Vpi u) : ℝ)

def H1C (large₂ : SizeData₂ D) (CH : ℝ) : ℝ := large₂.sc.b ^ (CH * (D.R.m : ℝ))

end Attr

section Steps

def TypeAt {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (CH Cs C Ch Cp : ℝ) : Prop :=
  ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, ∀ (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * massC Y u * ((k2a large₂ CH Cs C j' δ' * k2e large₂ CH Ch Cp j' δ') *
        (k2a large₂ CH Cs C j'' δ'' * k2e large₂ CH Ch Cp j'' δ''))

def IrrVecC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    FundExists X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    OOIntAll X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    ∀ t ∈ (Y.tO u u).degSet, ¬ t.relevant → (Y.tO u u).vec t = 0

def JPosC : Prop :=
  ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ t ∈ relSet Y u, 1 ≤ jT t

def DelC : Prop :=
  ∀ Cg cb Cw cT CT C0 CH : ℝ, 0 ≤ CH → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
      ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
        k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2

def CosetsC : Prop :=
  ∀ Cg cb Cw cT CT C0 CH : ℝ, 0 ≤ CH → ∃ Cc : ℝ, 0 ≤ Cc ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
      ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E),
        (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
        ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ))

def DimFormC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    0 ≤ (Y.tO u u).Gam1 ∧ (Y.tO u u).Gam1 * massC Y u * dpiC X u ≤ Formalism.L2.SG.RowsConc.duC X Y u

def PgLeC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.PgC Y ≤ 2

end Steps

end Formalism.L2.SG.KappaOffDiagonal
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovariantRepresentation
noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.KappaOffDiagonal

open Matrix

namespace Formalism.L2.SG.CovariantRepresentation


open Formalism.L2.SG.TermOp.Vanish in
def ShiftCore : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (R Γ : Subgroup G) [Countable Γ] (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : G → V) (Ω : Set G) (h : G) (ν : Measure G),
    IsClosed (R : Set G) → Γ ≤ R → (∃ K : Set G, IsCompact K ∧ ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K) →
    (∀ r, r ∈ R ↔ h⁻¹ * r * h ∈ R) →
    SigmaFinite ν → ν ≠ 0 → ν (R : Set G)ᶜ = 0 → (∀ K : Set G, IsCompact K → ν K < ⊤) →
    (∀ r ∈ R, ν.map (fun x => r * x) = ν) → ν.map (fun x => x⁻¹) = ν → ν.map (fun x => h⁻¹ * x * h) = ν →
    (∀ r ∈ R, ∀ x, f (r * x) = f x) → IsSF (Γ : Set G) Ω → IntegrableOn f Ω μ →
    ∫ x in Ω, f x ∂μ = ∫ x in (fun x => h⁻¹ * x) '' Ω, f x ∂μ


open Formalism.L2.SG.TermOp.Vanish in
def FixNormC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    ∀ h ∈ pointwiseStabilizerInfinite X t.rep, ∀ r, r ∈ Rset t ↔ h⁻¹ * r * h ∈ Rset t


section Plumb

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}

theorem rv_ratLink {x : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hl : RatLink X x γ)
    (v : InfinitePlace X.B.I.F) (y : (VS D).V) :
    uMat (x.1 v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd (γ y)) := by
  obtain ⟨M, -, hx, -, hc⟩ := hl
  rw [hc, hx v]
  unfold rv
  have hw : (fun i => X.B.I.φ v (((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y) i)) =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *ᵥ
        fun i => X.B.I.φ v (X.crd y i) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  by_cases hP : IsUnit (X.B.I.P v).det
  · rw [Matrix.mul_assoc _ (X.B.I.P v), Matrix.mul_nonsing_inv _ hP, Matrix.mul_one]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hP]
    simp

theorem basis_mem_fixedSubspace (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') (a : Fin D.R.rS) : X.eX a ∈ fixedSubspaceOfRepresentative X q := by
  unfold fixedSubspaceOfRepresentative FlagG.Xplus FlagG.X
  refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
  refine Submodule.subset_span ⟨a, ?_⟩
  show (X.Fu u).e a = X.eX a
  rw [X.Fu_e u]

theorem zu_mem_fixedSubspaceOfRepresentative (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : X.zu u ∈ fixedSubspaceOfRepresentative X q := by
  unfold fixedSubspaceOfRepresentative FlagG.Xplus
  refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
  show X.zu u ∈ Submodule.span D.host.E {(X.Fu u).z}
  rw [X.flagZVector u]
  exact Submodule.mem_span_singleton_self _

theorem frq_fl (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') :
    (frq X q).fl = mapFlag q.1.2 q.2.2.1 (X.Fu u') := by
  unfold frq mapLF
  split
  · rfl
  · exact absurd q.2.2.1 ‹_›

theorem ge_mem_fixedSubspace (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') (a : Fin D.R.rS) : q.1.2 (X.eX a) ∈ fixedSubspaceOfRepresentative X q := by
  unfold fixedSubspaceOfRepresentative
  refine Submodule.mem_sup_right ?_
  rw [frq_fl]
  unfold FlagG.Xplus FlagG.X
  refine Submodule.mem_sup_left (Submodule.subset_span ⟨a, ?_⟩)
  show q.1.2 ((X.Fu u').e a) = q.1.2 (X.eX a)
  rw [X.Fu_e u']

theorem gz_mem_fixedSubspace (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : q.1.2 (X.zu u') ∈ fixedSubspaceOfRepresentative X q := by
  unfold fixedSubspaceOfRepresentative
  refine Submodule.mem_sup_right ?_
  rw [frq_fl]
  unfold FlagG.Xplus
  refine Submodule.mem_sup_right ?_
  show q.1.2 (X.zu u') ∈ Submodule.span D.host.E {q.1.2 (X.Fu u').z}
  rw [X.flagZVector u']
  exact Submodule.mem_span_singleton_self _

theorem fix_rv {q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'} {h : X.B.I.Ginf} (hh : h ∈ pointwiseStabilizerInfinite X q)
    {y : (VS D).V} (hy : y ∈ fixedSubspaceOfRepresentative X q) (v : InfinitePlace X.B.I.F) :
    uMat (h v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd y) := by
  dsimp [pointwiseStabilizerInfinite, Hset] at hh
  first
  | exact hh _ ⟨y, hy, rfl⟩ v
  | exact hh v _ ⟨y, hy, rfl⟩
  | exact hh.2 _ ⟨y, hy, rfl⟩ v
  | exact hh.2 v _ ⟨y, hy, rfl⟩
  | (clear hy; done)

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (a : Formalism.REAL.UJ ε) : uMat a⁻¹ * uMat a = 1 := by
  delta uMat
  simp

theorem fix'_rv {q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'} {h : X.B.I.Ginf} (hh : h ∈ pointwiseStabilizerInfinite X q)
    {y : (VS D).V} (hy : q.1.2 y ∈ fixedSubspaceOfRepresentative X q) (v : InfinitePlace X.B.I.F) :
    uMat ((q.1.1.1⁻¹ * h * q.1.1.1) v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd y) := by
  have h1 := rv_ratLink q.2.1 v y
  have h2 := fix_rv hh hy v
  have hm : uMat ((q.1.1.1⁻¹ * h * q.1.1.1) v) =
      uMat ((q.1.1.1 v)⁻¹) * uMat (h v) * uMat (q.1.1.1 v) := by
    delta uMat
    simp
  rw [hm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2, ← h1, Matrix.mulVec_mulVec,
    uMat_inv_mul, Matrix.one_mulVec]

theorem inS_of_fix {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (he : ∀ a, g *ᵥ e a = e a) (hz : g *ᵥ z = z) : InS e z g := by
  delta InS
  exact ⟨fun a => by simp [Matrix.sub_mulVec, he], by simp [Matrix.sub_mulVec, hz]⟩

theorem rootCoord_fix {n r : ℕ} (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) (he : ∀ a, g *ᵥ e a = e a) (hz : g *ᵥ z = z) (a : Fin r) :
    rootCoord ε e f z g a = rootCoord ε e f z 1 a := by
  delta rootCoord
  have hn : g *ᵥ nxt e z a = nxt e z a := by
    delta nxt
    split <;> simp [he, hz]
  rw [hn, Matrix.one_mulVec]

theorem psiR_fix {n r : ℕ} (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) (he : ∀ a, g *ᵥ e a = e a) (hz : g *ᵥ z = z) :
    psiR ε gg e f z g = psiR ε gg e f z 1 := by
  delta psiR
  simp only [rootCoord_fix ε e f z g he hz]

theorem psiInfU_fix (X : HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf)
    (he : ∀ v a, uMat (s v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : ∀ v, uMat (s v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)) :
    X.psiInfU u s = X.psiInfU u 1 := by
  dsimp [HidaSetting.psiInfU]
  delta psiInf
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [psiR_fix _ _ _ _ _ _ (he v) (hz v)]
  congr 1

theorem one_mem_SinfU (X : HidaSetting D) (u : D.what₂.Word) : (1 : X.B.I.Ginf) ∈ X.SinfU u := by
  dsimp [HidaSetting.SinfU, Sinf]
  intro v
  exact inS_of_fix _ _ _ (fun a => by delta uMat; simp) (by delta uMat; simp)

theorem psiInfU_one (X : HidaSetting D) (u : D.what₂.Word) : X.psiInfU u 1 = 1 := by
  have h1 : ∀ x, X.Wu u x = X.psiInfU u 1 • X.Wu u x := fun x => by
    have e : X.Wu u (1 * x) = X.psiInfU u 1 • X.piU u 1 (X.Wu u x) := (X.Wu_spec u).1 1 (one_mem_SinfU X u) x
    rwa [one_mul, (X.piU_rep u).1, ContinuousLinearMap.one_apply] at e
  by_contra hne
  have h0 : ∀ x, X.Wu u x = 0 := fun x => by
    have h2 : (1 - X.psiInfU u 1) • X.Wu u x = 0 := by rw [sub_smul, one_smul, ← h1 x, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  have := (X.Wu_spec u).2.2.2.2
  simp [h0] at this

end Plumb

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.TermOp.Vanish

section Gen

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
  [InnerProductSpace ℂ V']

theorem comp_rk1 (A : V →L[ℂ] V) (v : V) (w : V') : A.comp (rk1 v w) = rk1 (A v) w := by
  ext x
  simp [rk1, map_smul]

theorem rankOne_map_left_eq_comp (B : V' ≃ₗᵢ[ℂ] V') (v : V) (w : V') :
    (rk1 v w).comp (B.toContinuousLinearEquiv : V' →L[ℂ] V') = rk1 v (B.symm w) := by
  ext x
  simp only [rk1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  congr 1
  simp
  rw [← B.inner_map_map (B.symm w) x, LinearIsometryEquiv.apply_symm_apply]

end Gen

variable {D : D7} (X : HidaSetting D)

def piIsoT (u : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.SinfU u) : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u :=
  ((X.piU u s).toLinearMap.isometryOfInner (fun x y => (X.piU_rep u).2.2.1 s hs x y)).toLinearIsometryEquiv rfl

variable {X}

end Main

end Formalism.L2.SG.CovariantRepresentation
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalInvariants
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut

namespace Formalism.L2.SG.NGCut.NormalInvariants

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PG {D : D7} (TT : ℕ) (γ : PN.Pts D.host.E D.R.rS) : ℝ := ∏ w : InfinitePlace D.host.E, w (GPt TT γ)

def NmlInv : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
        (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS),
        (∃ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν) →
        1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∃ (J J' : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (m m' : D.host.E)
          (κ : NuC D → D.host.E × D.host.E),
          J ≠ 0 ∧ J' ≠ 0 ∧ m ≠ 0 ∧ m' ≠ 0 ∧
          (∀ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν →
            (κ ν).1 ∈ J ∧ (κ ν).1 * star (κ ν).1 = m ∧ (κ ν).2 ∈ J' ∧ (κ ν).2 * star (κ ν).2 = m') ∧
          (∀ ν₁ ν₂, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν₁ →
            PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν₂ → κ ν₁ = κ ν₂ → ν₁ = ν₂) ∧
          |((Algebra.norm ℚ m : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2 ∧
          |((Algebra.norm ℚ m' : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J' : ℚ) : ℝ) ^ 2 *
            ((Tu D u' : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2

def NormCount : Prop :=
  ∀ (D : D7) (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (m : D.host.E), J ≠ 0 → m ≠ 0 →
    ∀ S : Finset D.host.E, (∀ x ∈ S, x ∈ J ∧ x * star x = m) →
      (S.card : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 ≤ 8 * (D.R.f : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)|

private theorem eight_mul_sq_le_eightyOne_pow (f : ℕ) : 8 * f ^ 2 ≤ 81 ^ f := by
  induction f with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num
    · have h1 : 1 ≤ n := h
      rw [pow_succ 81 n]
      nlinarith [ih, h1]

theorem nat_bound (f : ℕ) : (64 : ℝ) * (f : ℝ) ^ 4 ≤ 6561 ^ f := by
  have h' : ((8 * f ^ 2 : ℕ) : ℝ) ≤ ((81 ^ f : ℕ) : ℝ) := by exact_mod_cast eight_mul_sq_le_eightyOne_pow f
  push_cast at h'
  have e : (6561 : ℝ) ^ f = (81 : ℝ) ^ f * (81 : ℝ) ^ f := by
    rw [← mul_pow]
    norm_num
  rw [e]
  calc (64 : ℝ) * (f : ℝ) ^ 4 = (8 * (f : ℝ) ^ 2) * (8 * (f : ℝ) ^ 2) := by ring
    _ ≤ (81 : ℝ) ^ f * (81 : ℝ) ^ f := mul_le_mul h' h' (by positivity) (by positivity)

theorem rd_one_le (D : D7) : 1 ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow
  · have h := NumberField.discr_ne_zero D.host.E
    have h' : (1 : ℤ) ≤ |discr D.host.E| := Int.one_le_abs h
    exact_mod_cast h'
  · positivity

theorem ngPt_eq {D : D7} (TT : ℕ) (γ : PN.Pts D.host.E D.R.rS) :
    NGPt D.host.rdE TT γ = ((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹ * PG TT γ := by
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
    first
    | ring
    | rfl
    | omega
    | (simp only [Formalism.BasicNotions.Ranks.ord]; ring)
  have hcard : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
    have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E
    have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
    have h3 := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero D.host.E
    omega
  unfold NGPt PG
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, inv_pow]

theorem rd_cancel (D : D7) :
    D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
      (((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) ^ 6 = 1 := by
  have h0 : D.host.rdE ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos (rd_one_le D))
  rw [inv_pow, ← pow_mul, ← pow_mul]
  rw [show 12 * D.R.rS * (D.R.rS + 1) * D.R.f = 2 * D.R.rS * (D.R.rS + 1) * (D.R.f * 6) by ring]
  exact mul_inv_cancel₀ (pow_ne_zero _ h0)

theorem count_bound (f : ℕ) (T T' P c1 c2 : ℝ) (hT1 : 3 ≤ T) (hT2 : 3 ≤ T') (hP1 : 1 ≤ P)
    (hc1 : c1 ≤ 8 * (f : ℝ) ^ 2 * (T ^ (2 * f) * P ^ 2)) (hc2 : c2 ≤ 8 * (f : ℝ) ^ 2 * (T' ^ (2 * f) * P ^ 2))
    (_h1 : 0 ≤ c1) (h2 : 0 ≤ c2) :
    c1 * c2 ≤ (T * T') ^ (6 * f) * P ^ 6 := by
  have hf := nat_bound f
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hT0' : (0 : ℝ) ≤ T' := by linarith
  have hTT0 : (0 : ℝ) ≤ T * T' := mul_nonneg hT0 hT0'
  have hTT : (9 : ℝ) ≤ T * T' := by nlinarith
  have h4 : (6561 : ℝ) ≤ (T * T') ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9) hTT 4
    norm_num at this
    exact this
  have h9 : (6561 : ℝ) ^ f ≤ (T * T') ^ (4 * f) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) h4 f
  have hP : P ^ 4 ≤ P ^ 6 := pow_le_pow_right₀ hP1 (by norm_num)
  have hB : (0 : ℝ) ≤ 8 * (f : ℝ) ^ 2 * (T ^ (2 * f) * P ^ 2) :=
    mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hT0 _) (sq_nonneg _))
  have hA : c1 * c2 ≤ (8 * (f : ℝ) ^ 2 * (T ^ (2 * f) * P ^ 2)) * (8 * (f : ℝ) ^ 2 * (T' ^ (2 * f) * P ^ 2)) :=
    mul_le_mul hc1 hc2 h2 hB
  calc c1 * c2 ≤ _ := hA
    _ = (64 * (f : ℝ) ^ 4) * ((T * T') ^ (2 * f) * P ^ 4) := by
        rw [mul_pow]
        ring
    _ ≤ (T * T') ^ (4 * f) * ((T * T') ^ (2 * f) * P ^ 6) :=
        mul_le_mul (hf.trans h9) (mul_le_mul_of_nonneg_left hP (pow_nonneg hTT0 _))
          (mul_nonneg (pow_nonneg hTT0 _) (by positivity)) (pow_nonneg hTT0 _)
    _ = (T * T') ^ (6 * f) * P ^ 6 := by ring

theorem stepNormals_of (hA : NmlInv) (hB : NormCount) (hO : StepNormOne) : StepNormals := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, hA2⟩ := hA Cg cb Cw cT CT C0
  obtain ⟨o₀, p₀, hO2⟩ := hO Cg cb Cw cT CT C0
  refine ⟨max a₀ o₀, max b₀ p₀, fun C' Cl h1 h2 D large₂ X Y u u' hc νL νB ng => ?_⟩
  intro cl γ S hS
  have hrd := rd_one_le D
  have hv : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
  have hstand := hc.2.1
  show (S.card : ℝ) ≤ ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
    (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f)) *
    NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6
  have eR : (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
      (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f)) *
      ((((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ) ^ 6 =
      (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6 := by
    have hR := rd_cancel D
    calc _ = (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
          (((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) ^ 6) *
          ((((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6) := by
          ring
      _ = _ := by rw [hR, one_mul]
  rw [hv, ngPt_eq, eR]
  have hT1 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.1
  have hT2 : (3 : ℝ) ≤ ((Tu D u' : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.2.1
  rcases S.eq_empty_or_nonempty with hSe | ⟨ν0, hν0⟩
  · rw [hSe]
    simp only [Finset.card_empty, Nat.cast_zero]
    refine mul_nonneg (pow_nonneg (by nlinarith) _) ?_
    rw [show PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6 = (PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 3) ^ 2 by ring]
    exact sq_nonneg _
  have hocc : ∃ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) cl γ ν := ⟨ν0, hS ν0 hν0⟩
  have hIsPt : PN.IsPt (Y.tO u u') (NOf2 Y u u' νL νB ng) γ := ⟨cl, ν0, hS ν0 hν0⟩
  have hNG0 := (hO2 C' Cl (le_trans (le_max_right _ _) h1) (le_trans (le_max_right _ _) h2) D large₂ X Y u u' hc
    νL νB ng γ hIsPt).1
  obtain ⟨J, J', m, m', κ, hJ, hJ', hm, hm', hmem, hinj, hN, hN'⟩ :=
    hA2 C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2) D large₂ X Y u u' hc νL νB ng cl γ hocc hNG0
  have hNG := hNG0
  rw [ngPt_eq] at hNG
  have hP1 : 1 ≤ PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ := by
    have hX : 1 ≤ (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := one_le_pow₀ (one_le_pow₀ hrd)
    have hpos : 0 < (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := lt_of_lt_of_le one_pos hX
    rw [inv_mul_eq_div, le_div_iff₀ hpos, one_mul] at hNG
    linarith

  let T1 := S.image (fun ν => (κ ν).1)
  let T2 := S.image (fun ν => (κ ν).2)
  have hcard : S.card ≤ T1.card * T2.card := by
    calc S.card = (S.image κ).card :=
          (Finset.card_image_of_injOn fun a ha b hb h => hinj a b (hS a ha) (hS b hb) h).symm
      _ ≤ (T1 ×ˢ T2).card := Finset.card_le_card (by
          intro p hp
          obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
          exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hν, Finset.mem_image_of_mem _ hν⟩)
      _ = T1.card * T2.card := Finset.card_product _ _
  have hB1 := hB D J m hJ hm T1 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).1, (hmem ν (hS ν hν)).2.1⟩)
  have hB2 := hB D J' m' hJ' hm' T2 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).2.2.1, (hmem ν (hS ν hν)).2.2.2⟩)
  have hJp : 0 < ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J) (Ne.symm h0)
    exact_mod_cast this
  have hJp' : 0 < ((FractionalIdeal.absNorm J' : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J' ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J') (Ne.symm h0)
    exact_mod_cast this
  generalize PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ = P at hN hN' hP1 ⊢
  generalize ((Tu D u : ℕ) : ℝ) = T at hN hT1 ⊢
  generalize ((Tu D u' : ℕ) : ℝ) = T' at hN' hT2 ⊢
  generalize ((FractionalIdeal.absNorm J : ℚ) : ℝ) = nJ at hB1 hN hJp
  generalize ((FractionalIdeal.absNorm J' : ℚ) : ℝ) = nJ' at hB2 hN' hJp'
  generalize |((Algebra.norm ℚ m : ℚ) : ℝ)| = nm at hB1 hN
  generalize |((Algebra.norm ℚ m' : ℚ) : ℝ)| = nm' at hB2 hN'
  have hc1 : (T1.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB1.trans (mul_le_mul_of_nonneg_left hN (by positivity))
    have h' : (T1.card : ℝ) * nJ ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  have hc2 : (T2.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T' ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB2.trans (mul_le_mul_of_nonneg_left hN' (by positivity))
    have h' : (T2.card : ℝ) * nJ' ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T' ^ (2 * D.R.f) * P ^ 2)) * nJ' ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  calc (S.card : ℝ) ≤ (T1.card : ℝ) * T2.card := by exact_mod_cast hcard
    _ ≤ _ := count_bound D.R.f T T' P _ _ hT1 hT2 hP1 hc1 hc2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)

def NormCountG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (m : E), J ≠ 0 → m ≠ 0 →
    ∀ S : Finset E, (∀ x ∈ S, x ∈ J ∧ x * NumberField.IsCMField.complexConj E x = m) →
      (S.card : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 ≤
        2 * (Module.finrank ℚ E : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)|

theorem normCount_of (h : NormCountG) : NormCount := by
  intro D J m hJ hm S hS
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
    first
    | ring
    | rfl
    | omega
    | (simp only [Formalism.BasicNotions.Ranks.ord]; ring)
  have h1 := h D.host.E J m hJ hm S (fun x hx => ⟨(hS x hx).1, (hS x hx).2⟩)
  have hf : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by rw [hfin]; push_cast; ring
  rw [hf] at h1
  calc (S.card : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2
      ≤ 2 * (2 * (D.R.f : ℝ)) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)| := h1
    _ = 8 * (D.R.f : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)| := by ring

end Formalism.L2.SG.NGCut.NormalInvariants
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumPf
noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbSumPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def orbR (M : Loc.Model F E) {n : ℕ} (Z : Matrix (Fin n) (Fin n) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {Z' | ∃ l ρ : Matrix (Fin n) (Fin n) E, Formalism.MainNotions.S.TieN.IntLow M l ∧ Formalism.MainNotions.S.TieN.IntUp M ρ ∧ Z' = l * Z * ρ}

def zAt {m : ℕ} (a : Loc.Pt E (m + 1)) (xy : (Loc.IL (m + 1) → E) × (Loc.IN a → E)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
  Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2

def muA (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) :
    Measure ((Loc.IL (m + 1) → E) × (Loc.IN a → E)) :=
  (Measure.pi fun _ : Loc.IL (m + 1) => M.mu).prod (Measure.pi fun _ : Loc.IN a => M.mu)

def IsZO (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E)) :
    Prop :=
  ∃ xy, (∀ i j, zAt a xy i j ∈ M.R) ∧ O = orbR M (zAt a xy)

def wtZ (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E)) : ℝ :=
  (muA M a {xy | zAt a xy ∈ O}).toReal

def OrbCut (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) : Prop :=
  ∀ (k : ℂ) (V : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E) → ℂ),
    (∀ O, ¬ IsZO M a O → V O = 0) →
    (∀ O, IsZO M a O → ∃ xy, zAt a xy ∈ O ∧ V O = k * M.bbIntegrand a c xy * (wtZ M a O : ℂ)) →
    HasSum V (k * M.BB a c) ∧ Summable (fun O => ‖V O‖)

end Loc

section Shift

variable {D : Formalism.BasicNotions.D7}

def shM (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : MatP D p :=
  Matrix.of fun a b => if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ T T' p w else 0

def ModShift (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : Prop :=
  ∀ a, modPt δ T T' p w = some a → a.mat = modMat δ T T' p w + shM δ T T' p w

def NAutNe (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) : Prop :=
  ∀ c : (M p).Cls D.R.rS, (M p).nAut c ≠ 0

end Shift

end Formalism.L2.SG.Pf.LocOrbSumPf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClassFrameNormal
noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm

namespace ClassFrameNormal

open MeasureTheory

section Gen

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

theorem oo_map_mulLeft {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [CompleteSpace V] (Ph : G → V) (Ph' : G → V') (γ s s' : G) (a b : ℂ)
    (A : V ≃ₗᵢ[ℂ] V) (B : V' ≃ₗᵢ[ℂ] V') (hA : ∀ x, Ph (s * x) = a • A (Ph x))
    (hB : ∀ x, Ph' (s' * x) = b • B (Ph' x)) :
    Formalism.L2.SG.TermOp.OO (μ.map (fun x => s * x)) Set.univ Ph Ph' (s * γ * s'⁻¹) =
      (a * conj b) • ((A.toContinuousLinearEquiv : V →L[ℂ] V).comp
        ((Formalism.L2.SG.TermOp.OO μ Set.univ Ph Ph' γ).comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V'))) := by
  classical
  have hEF : ∀ F : V' →L[ℂ] V,
      (B.toContinuousLinearEquiv.arrowCongr A.toContinuousLinearEquiv) F =
        (A.toContinuousLinearEquiv : V →L[ℂ] V).comp
          (F.comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V')) := by
    intro F
    ext ξ
    simp [ContinuousLinearEquiv.arrowCongr_apply]
  have hmap : ∀ f : G → (V' →L[ℂ] V),
      ∫ x, f x ∂(μ.map fun x => s * x) = ∫ x, f (s * x) ∂μ :=
    fun f => (MeasurableEquiv.mulLeft s).measurableEmbedding.integral_map f
  have hpt : ∀ x, Formalism.L2.SG.TermOp.rk1 (Ph (s * x)) (Ph' ((s * γ * s'⁻¹)⁻¹ * (s * x))) =
      (a * conj b) • (B.toContinuousLinearEquiv.arrowCongr A.toContinuousLinearEquiv)
        (Formalism.L2.SG.TermOp.rk1 (Ph x) (Ph' (γ⁻¹ * x))) := by
    intro x
    have h1 : (s * γ * s'⁻¹)⁻¹ * (s * x) = s' * (γ⁻¹ * x) := by group
    rw [h1, hA, hB, hEF, Formalism.L2.SG.RealObj.InfCut.rank_one_smul_isometry]
  unfold Formalism.L2.SG.TermOp.OO
  rw [Measure.restrict_univ, Measure.restrict_univ, hmap]
  simp_rw [hpt]
  rw [integral_smul, ContinuousLinearEquiv.integral_comp_comm, hEF]

end Gen

end ClassFrameNormal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def LiftAtSomeC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∃ w, s.1.toTerm.atPt w

def LiftDecompC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) γ) ∧
      ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u',
        s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹

def DFrameAtS (sc : ℝ) : Prop :=
  0 < sc → ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) →
    (∀ v, 0 < Formalism.L2.SG.RealObj.GX X u u' D.host.rdE (Formalism.L2.SG.RealObj.gamW X u u' w) v) →
      ∃ h h', Formalism.L2.SG.RealObj.IsDFrameX X u u' sc i0 i0' (Formalism.L2.SG.RealObj.gamW X u u' w) h h'

def LiftGPosC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ v, 0 < Formalism.L2.SG.RealObj.GX X u u' D.host.rdE
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) v

def FormTranspC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ g ∈ X.SinfU u, ∀ g' ∈ X.SinfU u',
      s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ →
      Formalism.L2.SG.TermOp.OOt s.1 = ((vR s.1.toTerm : ℝ) : ℂ) •
        (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
         Formalism.L2.SG.TermOp.OO
          ((νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).map (fun x => g * x))
          Set.univ (X.Wu u) (X.Wu u') s.1.pt.1)

def PhaseTieC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ g ∈ X.SinfU u, ∀ g' ∈ X.SinfU u',
      s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ →
      Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf)
                ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) s.1.pt) *
        (X.psiInfU u g * conj (X.psiInfU u' g')) =
        Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)

end Formalism.L2.SG.Pf.RowForm
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataClose
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.TermsAtFiniteOf
noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sigOK_holds (D : D7) : (VS D).SigOK := D.sp.Y_sig 0

end PI.TermsAtPtFiniteW
end
end

noncomputable section

namespace Formalism.L2.SG.DataCut

theorem densInputAt_of_loc {D : Formalism.BasicNotions.D7} (hL : DensLocBound D) : Formalism.L2.SG.DataInst.DensInputAt D :=
  densInputAt_of hL (Formalism.L2.SG.Pf.alpBound_holds D) (Formalism.L2.SG.Pf.placesOver_holds D)

end Formalism.L2.SG.DataCut
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeviTens
noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal PI.SchurPlaces.LeviLA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem frameAt (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    Frame (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u))
      (X.wfr u v) :=
  { ee := fun a b => by
      simp only [HidaSetting.eR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ee, map_zero]
    ef := fun a b => by
      simp only [HidaSetting.eR, HidaSetting.fR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ef]; split_ifs <;> simp
    ff := fun a b => by
      simp only [HidaSetting.fR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.ff, map_zero]
    ez := fun a => by
      simp only [HidaSetting.eR, HidaSetting.zR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, (X.zu_orth u a).1, map_zero]
    fz := fun a => by
      simp only [HidaSetting.fR, HidaSetting.zR]; rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, (X.zu_orth u a).2, map_zero]
    ew := fun a b => ((X.wfr_perp u v b).1 a).1
    fw := fun a b => ((X.wfr_perp u v b).1 a).2
    zw := fun b => (X.wfr_perp u v b).2
    ww := X.wfr_on u v
    zz := by
      simp only [HidaSetting.zR]
      rw [Formalism.L2.SG.PoincareInHH.Cut.hJ_crd, X.zu_norm, map_neg, map_natCast]
      exact neg_ne_zero.2 (Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero)
    card := by
      have h1 := X.n_eq; have h2 := D.R.r_eq; have h3 := D.R.rS_two; omega }

theorem wfrSpan : WfrSpan := by
  intro D X u v y hef hz
  exact perp_efz (frameAt X u v) y hef hz

theorem leviTens : LeviTens := by
  intro D X u h hh x
  have hS : ∀ v, InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (uMat (h v)) := hh
  choose V hVu hVe hVf hVz hVw hVN using fun v =>
    levi_place (frameAt X u v) ((h v : Formalism.REAL.UJ (X.B.I.ε v)) : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
      (h v).2 (hS v)
  let s0 : X.B.I.Ginf := fun v => ⟨V v, hVu v⟩
  have hs0 : ∀ v, uMat (s0 v) = (V v : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) := fun v => rfl
  have hn : ∀ v, uMat ((s0⁻¹ * h) v) =
      (((V v)⁻¹ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) *
        uMat (h v) := fun v => rfl
  have hs0S : s0 ∈ X.SinfU u := by
    intro v
    refine ⟨fun a => ?_, ?_⟩
    · rw [hs0, sub_mulVec, one_mulVec, hVe v a, sub_self]; exact zero_mem _
    · rw [hs0, sub_mulVec, one_mulVec, hVz v, sub_self]; exact zero_mem _
  have hnN : s0⁻¹ * h ∈ X.NinfU u := fun v => by rw [show uMat ((s0⁻¹ * h) v) = _ from hn v]; exact hVN v
  have hnS : s0⁻¹ * h ∈ X.SinfU u := fun v => (hnN v).1
  have hsplit : h = s0 * (s0⁻¹ * h) := by rw [mul_inv_cancel_left]
  have hpi : X.piU u h = X.piU u s0 := by
    rw [hsplit, (X.piU_rep u).2.1 s0 hs0S _ hnS, (X.piU_rep u).2.2.2.1 _ hnN, mul_one]
  have hs0H : s0 ∈ Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) := by
    intro v p hp
    rw [hs0]
    rcases hp with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hp
    · exact hVe v a
    · exact hVf v a
    · rw [Set.mem_singleton_iff] at hp; subst hp; exact hVz v
  have hmat : ∀ v, matW X.B.I (X.wfr u v) v s0 = matW X.B.I (X.wfr u v) v h := fun v => by
    ext a b; exact hVw v a b
  rw [hpi, X.tensU_equiv u s0 hs0H x]
  simp only [hmat]

end PI.SchurPlaces
end
end
