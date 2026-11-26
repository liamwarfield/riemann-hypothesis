module

public import Formalism.LocalToGlobal.AlgebraicTheory.StatementEig
public import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt

@[expose] public section

section -- merged from Formalism.LocalToGlobal.KernelLattices.KerStd
noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.H (cmL CmOK matH stdLat pow4 imgLat relIdx IsIsom)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.GD (LocNorm)
open Formalism.L2.AlgTh (KerStd lamF)

section Defs

variable {D : D7} {X : Fields} (s : Seam D X)

def Seam.flatV (a b : ℕ) : (DVar X.Tau a b → ℂ) ≃ₗ[ℂ] TaylorLogMetric.VC D a b where
  toFun z := fun τ i j => z (s.iT.symm τ, i, j)
  invFun w := fun k => w (s.iT k.1) k.2.1 k.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by funext k; simp
  right_inv w := by funext τ i j; simp

def Seam.laF (T : TaylorLogMetric.Tor D) {a b : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) :
    AddSubgroup (DVar X.Tau a b → ℂ) :=
  (TaylorLogMetric.La D T L L').comap (s.flatV a b).toLinearMap.toAddMonoidHom

def Seam.StdAtP (p : ℕ) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) : Prop :=
  TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D n) (s.lat N)

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

def Base.IsCm (a₀ : ℕ) (b₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) : Prop :=
  B.L = cmL a₀ b₀ D.host.d ha hd lam hlam ∧ B.ω₀ = lam * a₀

def Base.latA : AddSubgroup (Fin 4 × D.what₂.Tau → ℂ) :=
  imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)

def Base.KappaAt (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : Prop :=
  ∀ u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ),
    IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau))
      (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) →
    relIdx (stdLat B.L (Fin 4 × D.what₂.Tau)) (imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) B.latA) ≠ 0 →
    ¬ p ∣ relIdx (stdLat B.L (Fin 4 × D.what₂.Tau)) (imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) B.latA) →
    relIdx (imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) B.latA) (stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 →
    ‖ι B.kappa‖ ^ 2 * ‖ι (LinearMap.det (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))‖ = 1

def Base.LocNormMM (a₀ : ℕ) (b₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime]
    (ι : ℂ ≃+* ℂ_[p]) : Prop :=
  LocNorm a₀ b₀ D.host.d ha hd lam hlam (hOne B.L D.what₂.Tau) B.lamM B.thMM p ι

end Defs

def KappaOn (Q : D7 → ℕ → Prop) (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), Q D p → B.KappaAt p ι

def KappaAll (D : D7) : Prop := KappaOn (fun _ _ => True) D

def KappaSplit (D : D7) : Prop := KappaOn SplitK D

def LamTie : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), s.Ok →
    lamF (ambOf s B χ cD) N N' = s.laF B.tor (s.lat N) (s.lat N')

def KerStdLatOn (Q : D7 → ℕ → Prop) : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
    s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → CmOK a₀ b₀ c₀ D.host.d →
    (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    Even a → Even b → IsSdLat N → IsSdLat N' → s.StdAtP p N → s.StdAtP p N' →
    ¬ (p : ℤ) ∣ NumberField.discr X.E → (∀ τ, ‖ι (cD τ)‖ ≤ 1) → 5 ≤ p → Q D p →
    KerStd (ambOf s B χ cD) N N' a₀ b₀ c₀ ha hd lam hlam p ι

def KerStdExOn (Q : D7 → ℕ → Prop) : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ →
    ∃ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d ∧
      (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ ∧
      ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]),
        Even a → Even b → IsSdLat N → IsSdLat N' → s.StdAtP p N → s.StdAtP p N' →
        ¬ (p : ℤ) ∣ NumberField.discr X.E → (∀ τ, ‖ι (cD τ)‖ ≤ 1) → 5 ≤ p → Q D p →
        KerStd (ambOf s B χ cD) N N' a₀ b₀ c₀ ha hd lam hlam p ι

def KerStdEx : Prop := KerStdExOn fun _ _ => True

end Formalism.L2.Ker
end
end

section -- merged from Formalism.LocalToGlobal.KernelLattices.KerMtPin
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def twMt (D : D7) (ξ : D.Dt →* ℂˣ) : ℕ → D.Dt →* ℂˣ := fun j =>
  if 1 ≤ j ∧ j ≤ D.R.m then D.muTil j * ξ else D.muTil j

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

def KerEntTied.IsUnitNormOneQuotient {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) : Prop :=
  Function.Surjective q ∧
  ∀ (k : t.X.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (t.seam.iE (k : t.X.E)) = t.seam.iE (k : t.X.E) →
    q (ratId t.X.F t.X.E k) = D.e1Dt z

def KerEntTied.XiTil {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) (μ : D.what₂.Tup)
    (ξ : D.Dt →* ℂˣ) : Prop :=
  ∀ x, ξ (q x) = Units.map t.seam.σ₀.toMonoidHom ((t.tup μ : Chr t.X.F t.X.E t.X.K) x)

def KerEntTied.MtTwAt {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (q : (AfE t.X.F t.X.E)ˣ →* D.Dt) (P : D.what₂.Tup → Prop) : Prop :=
  ∀ μ, μ ≠ D.what₂.mu0 → P μ → ∃ ξ : D.Dt →* ℂˣ, t.XiTil q μ ξ ∧ ∀ u, (t.O u μ).mt = twMt D ξ

def KerEntTied.MtTwOn {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (P : D.what₂.Tup → Prop) : Prop :=
  ∃ q : (AfE t.X.F t.X.E)ˣ →* D.Dt, t.IsUnitNormOneQuotient q ∧ t.MtTwAt q P

def KerEntTied.MtTwTie {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : Prop := t.MtTwOn fun _ => True

end Comparison₂

end Formalism.L2.Ker
end
end
