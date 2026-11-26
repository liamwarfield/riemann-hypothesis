module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.SquareAgree

variable {D : D7}

theorem kapX_mem (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (g : GA D X) :
    (reindex e e (Formalism.L2.Theta.mt X g))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (reindex e e (Formalism.L2.Theta.mt X g)).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := by
  have k : (Formalism.L2.Theta.mt X g)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ * (Formalism.L2.Theta.mt X g).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ := by
    have := congrArg transpose (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram X g)
    rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
    exact this
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ) = reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ) := rfl
  rw [hJ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul, e1]
  simp only [reindex_apply, transpose_submatrix, submatrix_mul_equiv, ← Matrix.submatrix_map]
  rw [k]

end GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

variable {D : D7}

def kapX (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (g : GA D X) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J :=
  ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X g), by
    show (reindex e e (Formalism.L2.Theta.mt X g))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (reindex e e (Formalism.L2.Theta.mt X g)).map (cA D) = _
    exact kapX_mem X e hJ g⟩

theorem mat_kapX (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (g : GA D X) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (kapX X e hJ g) = reindex e e (Formalism.L2.Theta.mt X g) := rfl

section Datum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}

def IsDatum (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ) {Z : Type}
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z) (Φ : (Fin n × Fin d → AF F) → ℂ) (f : Z → ℂ) : Prop :=
  Φ ∈ GlobalTheory.WeilM.schA F _ ∧ ∀ u, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u Φ) = f (crd u)

def algD (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) :
    Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ f φ, f ∈ M.Pol ψ emb ∧ (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ v = M.vac v) ∧
    Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ}

theorem rho_zero (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    M.co.rho ψ 0 Φ = Φ := by
  funext x
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

end Datum

end GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

variable {D : D7}

structure IsOver (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁))
    (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X) : Prop where

  psi : Bs.ψ = ψ

  alpha : Xc.α = α

  beta : Xc.β = β

  JW : Γ.V.J = (1 : D.host.E) • W.gram

  JW₁ : Γ.V'.J = (-1 : D.host.E) • W₁.gram

  JX : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ

  measW : Γ.M.μ = ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 JW)

  domW : Γ.M.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 JW '' 𝓕

  measW₁ : Γ.M'.μ = ν₁.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) JW₁)

  domW₁ : Γ.M'.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) JW₁ '' 𝓕₁

  weilA : ∀ Φ f, IsDatum Γ.M ψ cA Φ f → ∀ g h,
    IsDatum Γ.M ψ cA (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 JW g, kapX X e JX h) Φ) (ωA (g, h) f)

  weilB : ∀ Φ f, IsDatum Γ.M' ψ cB Φ f → ∀ g h,
    IsDatum Γ.M' ψ cB (om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) JW₁ g, kapX X e JX h) Φ) (ωB (g, h) f)

  algA : ∀ Φ ∈ algF ψ θ true A B, ∃ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ

  algA' : ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ true A B, IsDatum Γ.M ψ cA ΦD Φ

  algB : ∀ Φ ∈ algF ψ θ false A₁ B, ∃ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M' ψ cB ΦD Φ

  algB' : ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB ΦD Φ

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}

theorem IsOver.theta_eq_A (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) {Φ : _} {f : WO W X → ℂ}
    (hD : IsDatum Γ.M ψ cA Φ f) (g : GA D W) (h : GA D X) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW g) (kapX X e hO.JX h) = thetaKO ωA g h f := by
  have := (hO.weilA Φ f hD g h).2 0
  rw [rho_zero, map_zero] at this
  exact this

theorem IsOver.theta_eq_B (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) {Φ : _} {f : WO W₁ X → ℂ}
    (hD : IsDatum Γ.M' ψ cB Φ f) (g : GA D W₁) (h : GA D X) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ g) (kapX X e hO.JX h) = thetaKO ωB g h f := by
  have := (hO.weilB Φ f hD g h).2 0
  rw [rho_zero, map_zero] at this
  exact this

end GlobalTheory.SquareAgree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RealQuot

section LA

variable {ι Q : Type} [AddCommGroup Q] [Module ℂ Q]

def IsStab (ρ : ι → Module.End ℂ Q) (N : Submodule ℂ Q) : Prop := ∀ i, ∀ x ∈ N, ρ i x ∈ N

def HoweCond (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) : Prop :=
  (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ Q), StrictMono N → (∀ k, IsStab ρ (N k) ∧ C ≤ N k) → m ≤ L) ∧
  ∀ N N' : Submodule ℂ Q, IsStab ρ N → C ≤ N → N ≠ ⊤ → IsStab ρ N' → C ≤ N' → N' ≠ ⊤ → N ⊔ N' ≠ ⊤

def rad (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) : Submodule ℂ Q :=
  sSup {N | IsStab ρ N ∧ C ≤ N ∧ N ≠ ⊤}

theorem isStab_rad (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) : IsStab ρ (rad ρ C) := by
  intro i
  have h : rad ρ C ≤ (rad ρ C).comap (ρ i) := by
    refine sSup_le fun N hN => ?_
    intro x hx
    exact le_sSup hN (hN.1 i x hx)
  exact fun x hx => h hx

def radAct (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (i : ι) : Module.End ℂ (Q ⧸ rad ρ C) :=
  (rad ρ C).mapQ (rad ρ C) (ρ i) fun x hx => isStab_rad ρ C i x hx

theorem radAct_mk (ρ : ι → Module.End ℂ Q) (C : Submodule ℂ Q) (i : ι) (x : Q) :
    radAct ρ C i (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ i x) := rfl

end LA

section Fock

variable {D : D7}

def actT (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (eS : D.what₂.Tau → ℚ) (τ : D.what₂.Tau)
    (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) : Module.End ℂ (PolF D X.rank M.rank) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ((frSgn ε A).ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) + ((eS τ : ℂ) * Y.trace) • 1

def actS (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (eT : D.what₂.Tau → ℚ) (τ : D.what₂.Tau)
    (Z : Matrix (Fin M.rank) (Fin M.rank) ℂ) : Module.End ℂ (PolF D X.rank M.rank) :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ((frSgn ε A).ε τ) (B.ε τ) ((A.fr τ * Z * (A.fr τ)⁻¹).map (starRingEnd ℂ)) -
    ((eT τ : ℂ) * Z.trace) • 1

def coinv (ε : Bool) {M X : HSp D} (A : Fr M) (B : Fr X) (eT : D.what₂.Tau → ℚ) : Submodule ℂ (PolF D X.rank M.rank) :=
  Submodule.span ℂ {P | ∃ τ, ∃ Z ∈ lieAt M τ, ∃ P₀, P = actS ε A B eT τ Z P₀}

abbrev LieIx (X : HSp D) : Type := {x : D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ // x.2 ∈ lieAt X x.1}

end Fock

section LALemmas

theorem isStab_sup {ι Q : Type} [AddCommGroup Q] [Module ℂ Q] {ρ : ι → Module.End ℂ Q} {N N' : Submodule ℂ Q}
    (h : IsStab ρ N) (h' : IsStab ρ N') : IsStab ρ (N ⊔ N') := by
  intro i x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (h i y hy) (h' i z hz)

theorem rad_ne_top : ∀ (ι Q : Type) [AddCommGroup Q] [Module ℂ Q] (ρ : ι → Module.End ℂ Q) (C N₀ : Submodule ℂ Q),
  GlobalTheory.RealQuot.HoweCond ρ C → GlobalTheory.RealQuot.IsStab ρ N₀ → C ≤ N₀ → N₀ ≠ ⊤ → GlobalTheory.RealQuot.rad ρ C ≠ ⊤ := by
  intro ι Q _ _ ρ C N₀ hH hs hC hne
  obtain ⟨⟨L, hL⟩, hsum⟩ := hH
  let S : Set (Submodule ℂ Q) := {N | IsStab ρ N ∧ C ≤ N ∧ N ≠ ⊤}
  have wf : WellFounded (fun x y : S => y.1 < x.1) := by
    refine ⟨fun x => ?_⟩
    by_contra hx
    obtain ⟨f, -, hf⟩ := not_acc_iff_exists_descending_chain.1 hx
    have mono : StrictMono fun n => (f n).1 := strictMono_nat_of_lt_succ hf
    have := hL (L + 1) (fun k => (f k).1) (mono.comp Fin.val_strictMono) fun k => ⟨(f k).2.1, (f k).2.2.1⟩
    omega
  obtain ⟨M, -, hM⟩ := wf.has_min Set.univ ⟨⟨N₀, hs, hC, hne⟩, trivial⟩
  have hmax : ∀ N ∈ S, N ≤ M.1 := by
    intro N hN
    have hs' : M.1 ⊔ N ∈ S := ⟨isStab_sup M.2.1 hN.1, le_sup_of_le_left M.2.2.1,
      hsum _ _ M.2.1 M.2.2.1 M.2.2.2 hN.1 hN.2.1 hN.2.2⟩
    by_contra h
    exact hM ⟨_, hs'⟩ trivial (lt_of_le_of_ne le_sup_left fun e => h (e ▸ le_sup_right))
  have e : rad ρ C = M.1 := le_antisymm (sSup_le hmax) (le_sSup M.2)
  rw [e]
  exact M.2.2.2

theorem rad_le_ker : ∀ (ι Q Pi : Type) [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Pi] [Module ℂ Pi] (ρ : ι → Module.End ℂ Q)
  (C : Submodule ℂ Q) (σ : ι → Module.End ℂ Pi) (β : Q →ₗ[ℂ] Pi),
  (∀ i, β ∘ₗ ρ i = σ i ∘ₗ β) → C ≤ LinearMap.ker β → GlobalTheory.RealQuot.rad ρ C ≠ ⊤ →
  (∀ N : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N → ∃ N' : Submodule ℂ Pi, GlobalTheory.RealQuot.IsStab σ N' ∧ IsCompl N N') →
  GlobalTheory.RealQuot.rad ρ C ≤ LinearMap.ker β := by
  intro ι Q Pi _ _ _ _ ρ C σ β hi hk hrad hss
  by_contra hne
  have hKs : IsStab ρ (LinearMap.ker β) := fun i x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply, hx, map_zero]
  have hK : LinearMap.ker β ≠ ⊤ := fun h => hne (h ▸ le_top)
  have hTs : IsStab σ ((rad ρ C).map β) := by
    rintro i _ ⟨x, hx, rfl⟩
    exact ⟨ρ i x, isStab_rad ρ C i x hx, by rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply]⟩
  obtain ⟨N', hN's, hc⟩ := hss _ hTs
  have hUs : IsStab ρ (N'.comap β) := fun i x hx => by
    show β (ρ i x) ∈ N'
    rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply]
    exact hN's i _ hx
  have hCU : C ≤ N'.comap β := fun x hx => by
    show β x ∈ N'
    rw [LinearMap.mem_ker.1 (hk hx)]
    exact N'.zero_mem
  have hsup : rad ρ C ⊔ N'.comap β = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : β x ∈ (rad ρ C).map β ⊔ N' := hc.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨t, ht, n, hn, htn⟩ := Submodule.mem_sup.1 h1
    obtain ⟨r, hr, rfl⟩ := ht
    have h2 : x - r ∈ N'.comap β := by
      show β (x - r) ∈ N'
      rw [map_sub, ← htn, add_sub_cancel_left]
      exact hn
    have h3 := Submodule.add_mem_sup hr h2
    rwa [add_sub_cancel] at h3
  by_cases hU : N'.comap β = ⊤
  · apply hne
    intro x hx
    have h1 : β x ∈ (rad ρ C).map β := ⟨x, hx, rfl⟩
    have h2 : β x ∈ N' := by
      have : x ∈ N'.comap β := hU ▸ Submodule.mem_top
      exact this
    have h3 : β x ∈ (rad ρ C).map β ⊓ N' := Submodule.mem_inf.2 ⟨h1, h2⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at h3
    exact h3
  · exact hrad (eq_top_iff.2 (hsup ▸ sup_le le_rfl (le_sSup ⟨hUs, hCU, hU⟩)))

end LALemmas

theorem hasInfExp_div : ∀ (D : D7) (α β : (AE D)ˣ →* Circle) (τ : D.what₂.Tau) (a b : ℚ), HasInfExp D α τ a → HasInfExp D β τ b →
  HasInfExp D (β / α) τ (b - a) := by
  intro D α β τ a b hA hB
  obtain ⟨m, hm, ex, hα⟩ := hA
  obtain ⟨n, hn, -, hβ⟩ := hB
  refine ⟨n - m, by push_cast; rw [hm, hn]; ring, ex, fun θ hθ x h1 h2 => ?_⟩
  have eα := hα θ hθ x h1 h2
  have eβ := hβ θ hθ x h1 h2
  set w : ℂ := θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ) with hw
  have hdiv : (((β / α) x : Circle) : ℂ) = ((β x : Circle) : ℂ) / ((α x : Circle) : ℂ) := by
    rw [MonoidHom.div_apply, Circle.coe_div]
  rw [hdiv, eα, eβ]
  rcases eq_or_ne w 0 with h0 | h0
  · have hm0 : m = 0 := by
      by_contra hm0
      have := eα
      rw [h0, _root_.zero_zpow _ hm0] at this
      exact Circle.coe_ne_zero _ this
    have hn0 : n = 0 := by
      by_contra hn0
      have := eβ
      rw [h0, _root_.zero_zpow _ hn0] at this
      exact Circle.coe_ne_zero _ this
    subst hm0 hn0
    simp
  · rw [zpow_sub₀ h0]

end GlobalTheory.RealQuot

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleRead

variable {D : D7}

def toUX (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J :=
  ⟨⟨(mt X g).submatrix e e, (mt X g⁻¹).submatrix e e,
    by rw [Matrix.submatrix_mul_equiv]; simp only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]; exact Matrix.submatrix_one_equiv e,
    by rw [Matrix.submatrix_mul_equiv]; simp only [Formalism.L2.Theta.mt, map_inv, Units.inv_mul]; exact Matrix.submatrix_one_equiv e⟩, by
    subst hJ
    have k : (mt X g)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ * (mt X g).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ := by
      have := congrArg transpose (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram X g)
      rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
      exact this
    show ((mt X g).submatrix e e)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e) *
      ((mt X g).submatrix e e).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((X.gramᵀ).submatrix e e) = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ).submatrix e e := rfl
    have e2 : ((mt X g).submatrix e e).map (cA D) = ((mt X g).map (cA D)).submatrix e e := rfl
    rw [e1, e2, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, k]⟩

theorem toUX_val (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X) : (toUX X e hJ g).1.1 = (mt X g).submatrix e e := rfl

end GlobalTheory.TripleRead

namespace GlobalTheory.TripleRead

variable {D : D7}

structure IsReading (ψ : AddChar (AF D.host.F) ℂ) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop where

  ψ : Bs.ψ = ψ

  JW : Γ.V.J = (1 : D.host.E) • W.gram

  JW₁ : Γ.V'.J = (-1 : D.host.E) • W₁.gram

  JX : Γ.W.J = D.host.xi0 • (X.gramᵀ).submatrix e e

  cart : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Γ.V.θ w = A.cart τ ∧ Γ.V'.θ w = -A₁.cart τ ∧
    Γ.W.θ w = ((B.cart τ).submatrix e e).map conj

  α : Xc.α = α

  β : Xc.β = β

def ptO {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) (x : Matrix (Fin d) (Fin m) (AE D)) :
    Matrix (Fin m) (Fin k) (AE D) :=
  ((x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹)ᵀ).submatrix id e

def thO {m k : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) {d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d) (Φ : (Fin m × Fin k → AF D.host.F) → ℂ) (x : Matrix (Fin d) (Fin m) (AE D)) : ℂ :=
  GlobalTheory.WeilM.thetaSum D.host.F (Mo.co.rho ψ (ptO G e x) Φ)

def IsTransp (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) {M X : HSp D} {k : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k} (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Y Z) (ω : WRep M X) (e : Fin k ≃ Fin X.rank)
    (gM : GA D M → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Y.J) (gX : GA D X → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Z.J) : Prop :=
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin k), ∀ g h,
    thO Mo ψ (sgn ε M).gram e (om (gM g, gX h) Φ) = ω (g, h) (thO Mo ψ (sgn ε M).gram e Φ)

end GlobalTheory.TripleRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory

open Polynomial

theorem dixmier_aeval_injective {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (hT : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V))) (p : ℂ[X]) (hp : p ≠ 0) :
    Function.Injective (aeval T p) := by
  have hs := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) IsAlgClosed.card_roots_eq_natDegree
  have hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have key : ∀ m : Multiset ℂ, Function.Injective (aeval T (m.map fun a => X - C a).prod) := by
    intro m
    induction m using Multiset.induction_on with
    | empty =>
      simp only [Multiset.map_zero, Multiset.prod_zero, map_one, Module.End.one_eq_id, LinearMap.id_coe]
      exact Function.injective_id
    | cons a m ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
      refine Function.Injective.comp ?_ ih
      rw [hlin]; exact hT a
  rw [← hs, map_mul, Module.End.mul_eq_comp, LinearMap.coe_comp]
  refine Function.Injective.comp ?_ (key _)
  rw [aeval_C, Algebra.algebraMap_eq_smul_one]
  intro x y hxy
  simp only [LinearMap.smul_apply, Module.End.one_apply] at hxy
  exact smul_right_injective V (leadingCoeff_ne_zero.mpr hp) hxy

theorem dixmier_commutant_scalar (ι V : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0)
    (hirr : ∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤)
    (T : Module.End ℂ V) (hT : ∀ i, T * ρ i = ρ i * T) : ∃ c : ℂ, T = c • 1 := by
  by_contra hne
  push_neg at hne
  have hcomm : ∀ c : ℂ, ∀ i, (T - c • 1) * ρ i = ρ i * (T - c • 1) := by
    intro c i; rw [sub_mul, mul_sub, hT i, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hinj : ∀ c : ℂ, Function.Injective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.ker_eq_bot]
    rcases hirr (LinearMap.ker (T - c • 1)) (fun i x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [← Module.End.mul_apply, hcomm c i, Module.End.mul_apply, hx, map_zero]) with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp (LinearMap.ker_eq_top.mp h)) (hne c)
  obtain ⟨v₀, hv₀⟩ : ∃ v : V, v ≠ 0 := by
    by_contra h; push_neg at h
    exact hne 0 (LinearMap.ext fun v => (h _).trans (h _).symm)
  have hsurj : ∀ c : ℂ, Function.Surjective ⇑(T - c • (1 : Module.End ℂ V)) := by
    intro c
    rw [← LinearMap.range_eq_top]
    rcases hirr (LinearMap.range (T - c • 1)) (fun i x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨ρ i y, by rw [← Module.End.mul_apply, hcomm c i, Module.End.mul_apply]⟩) with h | h
    · exfalso
      have h1 : (T - c • 1) v₀ ∈ LinearMap.range (T - c • 1) := LinearMap.mem_range_self _ _
      rw [h, Submodule.mem_bot] at h1
      exact hv₀ (hinj c (by rw [h1, map_zero]))
    · exact h
  let S : ℂ → V ≃ₗ[ℂ] V := fun c => LinearEquiv.ofBijective (T - c • 1) ⟨hinj c, hsurj c⟩
  let w : ℂ → V := fun c => (S c).symm v₀
  have hw : ∀ c, (T - c • (1 : Module.End ℂ V)) (w c) = v₀ := fun c => (S c).apply_symm_apply v₀
  have hlin : ∀ a : ℂ, aeval T (X - C a) = T - a • 1 := by
    intro a; simp [Algebra.algebraMap_eq_smul_one]
  have hli : LinearIndependent ℂ w := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    let q : ℂ → ℂ[X] := fun c => ∏ d ∈ s.erase c, (X - C d)
    have hq : ∀ c ∈ s, aeval T (∏ d ∈ s, (X - C d)) (w c) = aeval T (q c) v₀ := by
      intro c hc
      rw [← Finset.mul_prod_erase s _ hc, mul_comm, map_mul, Module.End.mul_apply, hlin, hw]
    have h0 : aeval T (∑ c ∈ s, g c • q c) v₀ = 0 := by
      have h2 := congrArg (aeval T (∏ d ∈ s, (X - C d))) hsum
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zero, map_sum] at h2
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply, ← h2]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [LinearMap.map_smul, hq c hc, map_smul, LinearMap.smul_apply]
    have hp0 : ∑ c ∈ s, g c • q c = 0 := by
      by_contra hp
      exact hv₀ (dixmier_aeval_injective T hinj _ hp (by rw [h0, map_zero]))
    have h3 := congrArg (Polynomial.eval i) hp0
    rw [eval_finsetSum, Finset.sum_eq_single i] at h3
    · simp only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul, eval_zero] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h
        obtain ⟨d, hd, hd0⟩ := h
        exact (Finset.ne_of_mem_erase hd) (sub_eq_zero.mp hd0).symm
    · intro c hc hci
      simp only [eval_smul, q, eval_prod, eval_sub, eval_X, eval_C, smul_eq_mul]
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hci, hi⟩) (sub_self i), mul_zero]
    · intro h; exact absurd hi h
  have h4 := hli.cardinal_le_rank
  rw [Cardinal.mk_complex] at h4
  exact absurd (h4.trans hrank) (not_le.mpr Cardinal.aleph0_lt_continuum)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LiftRows.Inh
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem goodTypes_of_typesTrue (hL : R.toLevCh.Is A.μ0) (h : GlobalTheory.Mem.Top.TypesTrue D.ntypes R.C.P R.C.W) :
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R := by
  intro k
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  refine ⟨_, (h.teich k).symm, h.ser k, fun v j PP hPP a u ha hu => Or.inl ?_⟩
  have hl := h.isCharLab k v j
  have hp := D.host.g_prime k
  have ha0 : (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) ≠ 0 := by
    rw [ha]; intro h0
    have := (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_order 1 one_pos
    rw [h0, pow_one] at this
    have h2 := hp.two_le
    have h3 : orderOf (0 : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = 0 := orderOf_eq_zero_iff'.2 fun n hn => by simp [hn.ne']
    omega
  have hcop : a.Coprime (D.host.g k) := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    exact ha0 ((CharP.cast_eq_zero_iff _ (D.host.g k) a).2 hd)
  have han : a ≠ 0 := by rintro rfl; exact ha0 (by simp)
  have h1 := hl.2 (ZMod.unitOfCoprime a hcop) (by rw [ZMod.coe_unitOfCoprime, map_natCast, ha])
  rw [← h1]
  have hE : (a : D.host.E) ≠ 0 := by exact_mod_cast han
  have h2 := (R.C.isMu0 j).atg k PP hPP a hcop (Units.mk0 _ hE) rfl
  have h3 := hL.chi j PP ((hL.Pg PP).2 ⟨k, hPP⟩) (a : 𝓞 D.host.E) (Units.mk0 _ hE) u (by simp) (by rw [hu, map_natCast])
  rw [h2, MonoidHom.inv_apply, _root_.inv_inj] at h3
  rw [h3, MonoidHom.pow_apply]

end GlobalTheory.LiftRows.Inh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLine
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLine
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.HeisDeriv

variable {F : Type} [Field F] [NumberField F]

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_sum {κ : Type} [Fintype κ] (g : κ → AF F) : evI F (∑ i, g i) = ∑ i, evI F (g i) := by
  classical
  induction (Finset.univ : Finset κ) using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, evI_add, ih]

theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ _ t :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem mul_realAd_eq_zero {a : AF F} (ha : evI F a = 0) (t : ℝ) : a * realAd F t = 0 := by
  have h1 : a.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp ha
  have h2 : (realAd F t).2 = 0 := rfl
  show ((a.1 * (realAd F t).1, a.2 * (realAd F t).2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
  rw [h1, h2, zero_mul, mul_zero]

end GlobalTheory.HeisDeriv

namespace GlobalTheory.HeisDeriv

open scoped Classical

variable {F : Type} [Field F] [NumberField F]


variable (F) in
def trForm {κ : Type} [Fintype κ] (y : κ → AF F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).comp
      (∑ i, (LinearMap.mulRight ℝ (evI F (y i))).comp (LinearMap.proj i)))

theorem trForm_apply {κ : Type} [Fintype κ] (y : κ → AF F) (z : κ → mixedEmbedding.mixedSpace F) :
    trForm F y z = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, z i * evI F (y i)) := by
  simp [trForm, LinearMap.sum_apply]


variable (F) in
def mult {κ : Type} [Fintype κ] (y : κ → AF F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
  (-(2 * Real.pi * Complex.I)) • (Complex.ofRealCLM.comp (trForm F y))

theorem mult_apply {κ : Type} [Fintype κ] (y : κ → AF F) (z : κ → mixedEmbedding.mixedSpace F) :
    mult F y z = -(2 * Real.pi * Complex.I) * (trForm F y z : ℂ) := by
  simp [mult]


variable (F) in
def heisD {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F) (y : κ → AF F) :
    SInf F κ →ₗ[ℂ] SInf F κ :=
  (LineDeriv.lineDerivOpCLM ℂ (SInf F κ) v + SchwartzMap.smulLeftCLM ℂ (⇑(mult F y))).toLinearMap

theorem heisD_apply {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F) (y : κ → AF F) (f : SInf F κ)
    (z : κ → mixedEmbedding.mixedSpace F) :
    heisD F v y f z = fderiv ℝ f z v + mult F y z * f z := by
  have h : (⇑(mult F y)).HasTemperateGrowth := (mult F y).hasTemperateGrowth
  simp [heisD, h, SchwartzMap.lineDerivOp_apply_eq_fderiv]

end GlobalTheory.HeisDeriv

namespace GlobalTheory.HeisDeriv

open scoped Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem exists_heisLine_deriv {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f (D f) := by
  set x₁ := (M.co.e u).1 with hx₁
  set y₁ := (M.co.e u).2 with hy₁
  set v : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x₁ i) with hv
  refine ⟨heisD F v y₁, fun f r hr x => ?_⟩
  set z : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F (x i) with hz
  set P : ℝ := trForm F y₁ z with hP
  set Q : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) with hQ
  have hline : ∀ t : ℝ, M.heisLine ψ u t (tens (evI F) f r) x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * (P + t * Q) : ℝ) : ℂ)) * (f (z + t • v) * r x) := by
    intro t
    have he : M.co.e (realAd F t • u) = realAd F t • M.co.e u := map_smul _ _ _
    simp only [Model.heisLine, Darboux.rho, he, schr, tens, Prod.smul_fst, Prod.smul_snd, ← hx₁, ← hy₁]
    have hAt1 : At (evI F) (realAd F t • x₁) := fun a ha => by
      rw [smul_smul, mul_realAd_eq_zero ha, zero_smul]
    rw [hr.1 x _ hAt1]
    set A : AF F := x ⬝ᵥ (realAd F t • y₁) + ⅟(2 : AF F) * ((realAd F t • x₁) ⬝ᵥ (realAd F t • y₁)) with hAdef
    have hA : A = realAd F t * (x ⬝ᵥ y₁ + realAd F t * (⅟(2 : AF F) * (x₁ ⬝ᵥ y₁))) := by
      simp only [hAdef, dotProduct_smul, smul_dotProduct, smul_eq_mul]; ring
    have hAt2 : At (evI F) A := fun a ha => by
      rw [hA, smul_eq_mul, ← mul_assoc, mul_realAd_eq_zero ha, zero_mul]
    have hxy : evI F (x ⬝ᵥ y₁) = ∑ i, z i * evI F (y₁ i) := by
      simp only [dotProduct, evI_sum, evI_mul, hz]
    have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) = t * (P + t * Q) := by
      rw [hA, evI_mul, evI_add, evI_mul, evI_realAd, ← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_add (f := _),
        map_smul, hxy, hP, trForm_apply, hQ, smul_eq_mul, smul_eq_mul]
    have harg : (fun i => evI F ((x + realAd F t • x₁) i)) = z + t • v := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_realAd, hz, hv]
      rw [Algebra.smul_def]
    rw [hψ.2.2 A hAt2, htr, harg]
  have h1 : HasDerivAt (fun t : ℝ => t * (P + t * Q)) P 0 := by
    have := (hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) P).add ((hasDerivAt_id (0 : ℝ)).mul_const Q))
    exact this.congr_deriv (by simp)
  have h2 := (h1.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h3 : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h4 : HasDerivAt (fun t : ℝ => f (z + t • v)) (fderiv ℝ f z v) 0 := by
    have := (f.hasFDerivAt (z + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ) h3
    simpa [Function.comp_def] using this
  have h5 := h2.mul (h4.mul_const (r x))
  refine (h5.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => hline t)
  simp only [tens, heisD_apply, mult_apply, ← hz, ← hP]
  simp
  ring

end GlobalTheory.HeisDeriv


open GlobalTheory.HeisDeriv in
theorem GlobalTheory.HeisDeriv.exists_actsD_heisLine : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f (D f) :=
  fun M ψ hψ u _ => exists_heisLine_deriv M ψ hψ u
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchSchwartzDerivativeHeisenbergLineStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_archSchwartz_derivative_heisenbergLine : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ f : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f (D f) := by
  first | exact @GlobalTheory.HeisDeriv.exists_actsD_heisLine | exact GlobalTheory.HeisDeriv.exists_actsD_heisLine | (intros; apply GlobalTheory.HeisDeriv.exists_actsD_heisLine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSymplecticLieEqExpOneParam
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSymplecticLieEqExpOneParam
open scoped Matrix

noncomputable section

namespace GlobalTheory.SymplecticOneParam

variable {l : Type} [Fintype l] [DecidableEq l]

theorem eq_exp_of_continuous_oneParameter (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ) (hc : Continuous g)
    (h0 : g 0 = 1) (hadd : ∀ s t, g (s + t) = g s * g t) :
    HasDerivAt g (deriv g 0) 0 ∧ ∀ t : ℝ, g t = NormedSpace.exp (t • deriv g 0) := by
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (l ⊕ l) (l ⊕ l) ℝ) := FiniteDimensional.complete ℝ _
  have hsm := GlobalTheory.contDiff_of_continuous_oneParameter (Matrix (l ⊕ l) (l ⊕ l) ℝ) g hc h0 hadd
  have hdiff : Differentiable ℝ g := hsm.differentiable (by simp)
  set Z := deriv g 0 with hZ
  have hd0 : HasDerivAt g Z 0 := (hdiff 0).hasDerivAt
  have hdt : ∀ t, HasDerivAt g (g t * Z) t := by
    intro t
    have h1 : HasDerivAt (fun s => g (s - t)) Z t := by
      have h := hd0
      rw [← sub_self t] at h
      exact h.comp_sub_const t t
    have h2 := h1.const_mul (g t)
    have h3 : (fun s => g t * g (s - t)) = g := by
      funext s; rw [← hadd, add_sub_cancel]
    rwa [h3] at h2
  refine ⟨hd0, fun t => ?_⟩
  set h : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun s => g s * NormedSpace.exp (s • (-Z)) with hh
  have hderh : ∀ s, HasDerivAt h 0 s := by
    intro s
    have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Z) s
    have := (hdt s).fun_mul he
    have key : g s * Z * NormedSpace.exp (s • -Z) + g s * (-Z * NormedSpace.exp (s • -Z)) = 0 := by
      rw [neg_mul, mul_neg, mul_assoc, add_neg_cancel]
    exact this.congr_deriv key
  have hconst : h t = h 0 := is_const_of_deriv_eq_zero (fun s => (hderh s).differentiableAt)
    (fun s => (hderh s).deriv) t 0
  have hh0 : h 0 = 1 := by simp [hh, h0]
  have hinv : NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z) = 1 := by
    rw [smul_neg, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  calc g t = g t * (NormedSpace.exp (t • (-Z)) * NormedSpace.exp (t • Z)) := by rw [hinv, mul_one]
    _ = h t * NormedSpace.exp (t • Z) := by rw [hh, mul_assoc]
    _ = NormedSpace.exp (t • Z) := by rw [hconst, hh0, one_mul]

theorem exists_mem_sp_eq_exp : ∀ (l : Type) [Fintype l] [DecidableEq l] (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ),
    Continuous g → g 0 = 1 →
    (∀ s t, g (s + t) = g s * g t) → (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ t : ℝ, g t = NormedSpace.exp (t • Z) := by
  intro l _ _ g hc h0 hadd hsym
  obtain ⟨hd, hexp⟩ := eq_exp_of_continuous_oneParameter g hc h0 hadd
  refine ⟨deriv g 0, ?_, hexp⟩
  set Z := deriv g 0 with hZ
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  let T : Matrix (l ⊕ l) (l ⊕ l) ℝ →L[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℝ :=
    LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (l ⊕ l) (l ⊕ l) ℝ ℝ).toLinearMap
  have hT : HasDerivAt (fun t => (g t)ᵀ) Zᵀ 0 := T.hasFDerivAt.comp_hasDerivAt 0 hd
  have hF := (hT.mul_const (Matrix.J l ℝ)).fun_mul hd
  have hconst : (fun t => (g t)ᵀ * Matrix.J l ℝ * g t) = fun _ => Matrix.J l ℝ := by
    funext t
    have := SymplecticGroup.transpose_mem (hsym t)
    rw [SymplecticGroup.mem_iff, Matrix.transpose_transpose] at this
    exact this
  rw [hconst] at hF
  have huniq := hF.unique (hasDerivAt_const (0 : ℝ) (Matrix.J l ℝ))
  rw [h0, Matrix.transpose_one, mul_one, one_mul, add_eq_zero_iff_eq_neg] at huniq
  show Z ∈ skewAdjointMatricesLieSubalgebra (Matrix.J l ℝ)
  rw [mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint,
    Matrix.IsAdjointPair, huniq, mul_neg]

end GlobalTheory.SymplecticOneParam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSymplecticLieEqExpOneParamStatement
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLie_eq_exp_oneParam : ∀ (l : Type) [Fintype l] [DecidableEq l] (g : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ), Continuous g → g 0 = 1 →
    (∀ s t, g (s + t) = g s * g t) → (∀ t, g t ∈ Matrix.symplecticGroup l ℝ) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ t : ℝ, g t = NormedSpace.exp (t • Z) := by
  first | exact @GlobalTheory.SymplecticOneParam.exists_mem_sp_eq_exp | exact GlobalTheory.SymplecticOneParam.exists_mem_sp_eq_exp | (intros; apply GlobalTheory.SymplecticOneParam.exists_mem_sp_eq_exp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeConjRead

open Classical

variable {D : D7}

def colMat {n : ℕ} (w : Fin n → Fin n → EAf D) : Matrix (Fin n) (Fin n) (EAf D) := Matrix.of fun i j => w j i

def pairAt (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) :
    Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D :=
  if GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 then
    flagV D.R.rS D.R.k (Yc D 0).rank (f0T X h) (e0T X h) (bwdT X h) (z0T X h)
  else flagV D.R.rS D.R.k (Yc D 0).rank (f0T X h) (e0T X h) (fun i => bwT X h (Fin.rev i)) (z0T X h)

def hY (D : D7) (x y : Fin (Yc D 0).rank → EAf D) : EAf D :=
  Formalism.UG.hform (GlobalTheory.StdFrames.sg D) (GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram) x y

def SmallAt (PP : Pl D.host.E) (x : EAf D) : Prop := Valued.v (GlobalTheory.StdFrames.cpt PP x) < 1

def PairTable {M A : Type} [Ring A] (p : M → M → A) (sm : A → Prop) {ρ k : ℕ} (e f : Fin ρ → M) (b b' : Fin k → M)
    (z : M) : Prop :=
  (∀ a c, sm (p (f a) (e c) - if a = c then 1 else 0)) ∧ (∀ a j, sm (p (f a) (b j))) ∧ (∀ a, sm (p (f a) z)) ∧
  (∀ a c, sm (p (f a) (f c))) ∧
  (∀ i a, sm (p (b' i) (e a))) ∧ (∀ i j, sm (p (b' i) (b j) - if i = j then 1 else 0)) ∧ (∀ i, sm (p (b' i) z)) ∧
  (∀ i a, sm (p (b' i) (f a))) ∧
  (∀ a, sm (p z (e a))) ∧ (∀ j, sm (p z (b j))) ∧ sm (p z z + 1) ∧ (∀ a, sm (p z (f a))) ∧
  (∀ a c, sm (p (e a) (e c))) ∧ (∀ a j, sm (p (e a) (b j))) ∧ (∀ a, sm (p (e a) z)) ∧
  (∀ a c, sm (p (e a) (f c) - if a = c then 1 else 0))

def sgnD {A : Type} [Ring A] (ρ k : ℕ) {n : ℕ} (a : Fin n) : A := if a.1 = ρ + k then -1 else 1

end GlobalTheory.SeeConjRead
end
end
