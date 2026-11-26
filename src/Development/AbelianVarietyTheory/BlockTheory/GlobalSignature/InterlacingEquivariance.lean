module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance
open MvPolynomial NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

def brOne (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    MvPolynomial (Fin N × Fin N) K →ₗ[K] MvPolynomial (Fin n × Fin n) K :=
  (rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n)).toLinearMap ∘ₗ
    (VV K fun _ : Unit => sg).subtype ∘ₗ
      Br.brStdP (K := K) hN (fun _ : Unit => lam) (fun _ : Unit => sg) ∘ₗ
        (rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N))).toLinearMap

theorem brOne_rename (K : Type) [Field K] {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (G : VV K fun _ : Unit => lam) :
    brOne K hN lam sg (rename Prod.snd (G : Pol K Unit N)) =
      rename Prod.snd ((Br.brStd hN (fun _ : Unit => lam) (fun _ : Unit => sg) G : VV K fun _ : Unit => sg) : Pol K Unit n) := by
  have h : rename (fun v : Fin N × Fin N => (((), v) : Unit × Fin N × Fin N))
      (rename Prod.snd (G : Pol K Unit N)) = (G : Pol K Unit N) := by
    rw [rename_rename]
    exact rename_id_apply _
  simp only [brOne, Br.brStd, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h, Submodule.subtype_apply]

theorem interlace_iff {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    Br.Interlace hN lam sg ↔ Formalism.MainNotions.PrimeDegreeVariant.Interlace hN.symm lam sg := by
  refine forall_congr' fun i => ?_
  simp only [Br.aBr, Br.bBr, Br.iS, Br.iC]
  omega

def OnePlace : Prop :=
  ∀ (N n : ℕ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n),
    Br.Interlace hN lam sg → Br.SameShift lam sg →
      Formalism.MainNotions.PrimeDegreeVariant.IsBr hN.symm lam sg (brOne ℂ hN lam sg)

def Equivariance : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → Br.BrEquiv K hN lam sg

def Integrality : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n), Br.BrIntegral K hN lam sg

def Members : Prop :=
  ∀ (X : Fields) (Word : Type) (R : Ranks) (W : Wts X Word R), W.Ok → ∀ (u : Word) (τ : X.Tau),
    Br.Interlace (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) ∧ Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ)

def Tensor : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n),
    (∀ τ, Br.Interlace hN (lam τ) (sg τ)) → (∀ τ, Br.SameShift (lam τ) (sg τ)) →
    ∀ (f : ι → MvPolynomial (Fin N × Fin N) K) (G : VV K lam), (∀ τ, f τ ∈ nablaSq K N (lam τ)) → (G : Pol K ι N) = ten f →
      ((Br.brStd hN lam sg G : VV K sg) : Pol K ι n) = ten fun τ => brOne K hN (lam τ) (sg τ) (f τ)

theorem members_sameShift {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (hW : W.Ok) (u : Word) (τ : X.Tau) :
    Br.SameShift (W.lamTrue u R.m τ) (W.sgTrue τ) :=
  (lamTrue_sgTrue_detShift W hW u τ).symm

end GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding

open NumberField MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal TensorProduct

abbrev RCosets {G G' : Type} [Group G] [Group G'] (j : G' →* G) : Type :=
  Quotient (QuotientGroup.rightRel j.range)

def IsQuotMeasure {G G' : Type} [Group G] [Group G'] [MeasurableSpace G] [MeasurableSpace G']
    (j : G' →* G) (μ : Measure G) (μ' : Measure G') (ν : Measure (RCosets j)) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f →
    ∫⁻ g, f g ∂μ = ∫⁻ c : RCosets j, ∫⁻ h, f (j h * c.out) ∂μ' ∂ν

section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def coords (W : HSpace E) (x : W.V) : Fin 1 → Fin W.rank → E := fun _ i => W.frame.repr x i

end Coord

def latTensor {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Set (Fin M → E)) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ℝ≥0∞ :=
  (latHat F E L : Set (Fin M → Af F ⊗[F] E)).indicator (fun _ => (1 : ℝ≥0∞)) (projFin X 0) *
    Φi (projInf X)

def atInv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
    (h : HA (AF F) σ J) (y : Fin 1 → Fin M → E) : ℝ≥0∞ :=
  Φ (h⁻¹ • ratTup (F := F) (AF F) y)

def IsInfQuotIntegral (D : D7) : letI := D.host.cmStar; ∀ (W : HSpace D.host.E) (_P _Q _P' _Q' : ℕ)
    (_x : W.V) (_Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞)
    (_I : ℝ≥0∞), Prop :=
  letI := D.host.cmStar
  fun W P Q P' Q' x Φi I =>
  AllSome (fun θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) =>
    ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) fun θ =>
  AllSome (fun A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ =>
    ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) fun A =>
  let xr : D.what₂.Tau → (Fin P ⊕ Fin Q → ℂ) :=
    fun ρ => A ρ *ᵥ fun i => embOf D ρ (coords W x 0 i)
  AllSome (fun C : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ =>
    ∀ ρ, (C ρ)ᴴ * Formalism.UG.Jpq P Q * C ρ = Formalism.UG.Jpq P' Q' ∧
      ((C ρ)ᴴ * Formalism.UG.Jpq P Q) *ᵥ xr ρ = 0) fun C =>
  AllSome (fun j : (D.what₂.Tau → UpqT P' Q') →* (D.what₂.Tau → UpqT P Q) =>
    ∀ b ρ, UpqT.mat (j b ρ) * C ρ = C ρ * UpqT.mat (b ρ) ∧
      UpqT.mat (j b ρ) *ᵥ xr ρ = xr ρ) fun j =>
  AllSome (fun o : (D.what₂.Tau → UpqT P Q) →
      (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) =>
    ∀ g ρ, (A ρ *ᵥ fun i => θ ρ (o g 0 i)) = UpqT.mat (g ρ)⁻¹ *ᵥ xr ρ) fun o =>
  AllSome (IsQuotMeasure j (Measure.pi fun _ => D.cd.cd P Q) (Measure.pi fun _ => D.cd.cd P' Q'))
    fun ν => ∫⁻ c : RCosets j, Φi (o c.out) ∂ν = I

def HidaSetting {E : Type} [Field E] [NumberField E] [StarRing E] (W W' : HSpace E)
    (P Q P' Q' : ℕ) (s : Bool) (x : W.V) (ι : W'.V →ₗ[E] W.V) : Prop :=
  W.SigOK ∧ (∀ τ, W.sig τ = (P, Q)) ∧ 3 ≤ W.rank ∧
  (if s then P = P' + 1 ∧ Q = Q' else P = P' ∧ Q = Q' + 1) ∧
  W.hT x x = (if s then 1 else -1) ∧ x ∈ W.L0 ∧
  HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧
  W'.SigOK ∧ (∀ τ, W'.sig τ = (P', Q'))

def UnfoldAt (D : D7) : letI := D.host.cmStar; ∀ (W _W' : HSpace D.host.E) (_P _Q _P' _Q' : ℕ)
    (_s : Bool) (_x : W.V), Prop :=
  letI := D.host.cmStar
  fun W W' P Q P' Q' s x =>
  ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (μ' : Measure (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsVolMeas D W P Q μ → IsVolMeas D W' P' Q' μ' →
  ∀ (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (𝓕' : Set (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W'.gram) 𝓕' μ' →
    μ 𝓕 < ⊤ → μ' 𝓕' < ⊤ →
  ∀ Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞, Measurable Φi →
    ∃ I : ℝ≥0∞, IsInfQuotIntegral D W P Q P' Q' x Φi I ∧
      ∫⁻ h in 𝓕, ∑' x' : {x' : W.V // W.hT x' x' = (if s then 1 else -1)},
        atInv D.sp.cm.sig W.gram (latTensor (L0c D W) Φi) h (coords W x'.1) ∂μ = μ' 𝓕' * I

def Unfolding (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W W' : HSpace D.host.E) (P Q P' Q' : ℕ) (s : Bool) (x : W.V) (ι : W'.V →ₗ[D.host.E] W.V),
    HidaSetting W W' P Q P' Q' s x ι → (∀ y : W'.V, y ∈ W'.L0 ↔ ι y ∈ W.L0) →
    UnfoldAt D W W' P Q P' Q' s x

end GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold

open NumberField MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped ENNReal TensorProduct

abbrev RightCosets {G' G : Type} [Group G'] [Group G] (j : G' →* G) : Type :=
  Quotient (QuotientGroup.rightRel j.range)

def IsQuotientMeasure {G' G : Type} [Group G'] [Group G] [MeasurableSpace G'] [MeasurableSpace G]
    (j : G' →* G) (m' : Measure G') (m : Measure G) (ν : Measure (RightCosets j)) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f →
    ∫⁻ g, f g ∂m = ∫⁻ c, ∫⁻ g', f (j g' * Quotient.out c) ∂m' ∂ν

def IsStabEmb {P' Q' P Q : ℕ} (x₀ : Fin P ⊕ Fin Q → ℂ) (j : UpqT P' Q' →* UpqT P Q) : Prop :=
  ∃ C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ,
    Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q' ∧
    (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x₀ = 0 ∧
    ∀ g' : UpqT P' Q', UpqT.mat (j g') *ᵥ x₀ = x₀ ∧ UpqT.mat (j g') * C = C * UpqT.mat g'

def piEmb {T : Type} {P' Q' P Q : ℕ} (j : T → (UpqT P' Q' →* UpqT P Q)) :
    (T → UpqT P' Q') →* (T → UpqT P Q) where
  toFun g ρ := j ρ (g ρ)
  map_one' := by funext ρ; simp
  map_mul' g h := by funext ρ; simp

def infCoord {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M P Q : ℕ}
    (θ : Ainf F ⊗[F] E →+* ℂ) (A : Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ)
    (Y : Fin 1 → Fin M → Ainf F ⊗[F] E) : Fin P ⊕ Fin Q → ℂ :=
  A *ᵥ fun i => θ (Y 0 i)

def phiLat {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Set (Fin M → E)) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ℝ≥0∞ :=
  (latHat F E L : Set (Fin M → Af F ⊗[F] E)).indicator 1 (projFin X 0) * Φi (projInf X)

def atInv {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
    (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) : ℝ≥0∞ :=
  Φ (h⁻¹ • ratTup (F := F) (AF F) x)

def coordTup {E : Type} [Field E] [NumberField E] [StarRing E] (W : HSpace E) (x : W.V) :
    Fin 1 → Fin W.rank → E :=
  fun _ i => W.frame.repr x i

def UnfoldAt (D : D7) : letI := D.host.cmStar;
    ∀ (W W' : HSpace D.host.E) (_P _Q _P' _Q' : ℕ) (_β : D.host.E) (_x : W.V), Prop :=
  letI := D.host.cmStar
  fun W W' P Q P' Q' β x =>
  ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (μ' : Measure (HA (AF D.host.F) D.sp.cm.sig W'.gram))
    (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram))
    (𝓕' : Set (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
    IsVolMeas D W P Q μ → IsVolMeas D W' P' Q' μ' →
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ →
    IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W'.gram) 𝓕' μ' →
    μ 𝓕 < ⊤ → μ' 𝓕' < ⊤ →
    AllSome (fun θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) =>
      ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) fun θ =>
    AllSome (fun A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ =>
      ∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) fun A =>
    AllSome (fun j : D.what₂.Tau → (UpqT P' Q' →* UpqT P Q) =>
      ∀ ρ, IsStabEmb (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i)) (j ρ)) fun j =>
    AllSome (IsQuotientMeasure (piEmb j) (Measure.pi fun _ => D.cd.cd P' Q')
      (Measure.pi fun _ => D.cd.cd P Q)) fun ν =>
    AllSome (fun pt : (D.what₂.Tau → UpqT P Q) →
        (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) =>
      ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) =
        UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => embOf D ρ (coordTup W x 0 i))) fun pt =>
    ∀ Φi : (Fin 1 → Fin W.rank → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℝ≥0∞, Measurable Φi →
      ∫⁻ h in 𝓕, ∑' x' : {x' : W.V // W.hT x' x' = β},
          atInv D.sp.cm.sig W.gram (phiLat (L0c D W) Φi) h (coordTup W x'.1) ∂μ =
        μ' 𝓕' * ∫⁻ c, Φi (pt (Quotient.out c)) ∂ν

def Unfolding (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∀ x : W.V, W.hT x x = (if s then 1 else -1) → x ∈ W.L0 →
    ∀ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
      HSpace.IsIsomEmb W' W ι → LinearMap.range ι = LinearMap.ker (W.hT x) → W'.SigOK →
      (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) →
      (∀ y, y ∈ W'.L0 ↔ ι y ∈ W.L0) →
      UnfoldAt D W W' P Q (if s then P - 1 else P) (if s then Q else Q - 1) (if s then 1 else -1) x

theorem IsStabEmb.inv_mul_fix {P' Q' P Q : ℕ} {x₀ : Fin P ⊕ Fin Q → ℂ} {j : UpqT P' Q' →* UpqT P Q}
    (hj : IsStabEmb x₀ j) (g' : UpqT P' Q') (g : UpqT P Q) :
    UpqT.mat (j g' * g)⁻¹ *ᵥ x₀ = UpqT.mat g⁻¹ *ᵥ x₀ := by
  obtain ⟨C, -, -, h⟩ := hj
  have h1 := (h g'⁻¹).1
  have e : UpqT.mat (j g' * g)⁻¹ = UpqT.mat g⁻¹ * UpqT.mat (j g'⁻¹) := by
    rw [_root_.mul_inv_rev, ← map_inv]; rfl
  rw [e, ← Matrix.mulVec_mulVec, h1]

end GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers

open scoped TensorProduct Pointwise
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

section Lat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def IsSelfDualLat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin M → E)) = ⊤ ∧
    ∀ y : Fin M → E, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (hE σ J x y)

def perpIn (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) : Set (Fin M → E) :=
  {y | y ∈ L ∧ hE σ J x y = 0}

variable (R : Type) [CommRing R] [Algebra F R]

def actV (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (y : Fin M → R ⊗[F] E) : Fin M → R ⊗[F] E :=
  (h • (fun _ => y : Fin 1 → Fin M → R ⊗[F] E)) 0

theorem actV_eq (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (y : Fin M → R ⊗[F] E) :
    actV R σ J h y = ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec y := rfl

theorem actV_one (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (y : Fin M → R ⊗[F] E) : actV R σ J 1 y = y := by
  unfold actV
  rw [one_smul]

theorem actV_mul (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g h : HA R σ J)
    (y : Fin M → R ⊗[F] E) : actV R σ J (g * h) y = actV R σ J g (actV R σ J h y) := by
  unfold actV
  rw [mul_smul]
  rfl

def stabLat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Λ : AddSubgroup (Fin M → R ⊗[F] E)) : Subgroup (HA R σ J) where
  carrier := {h | ∀ y, y ∈ Λ ↔ actV R σ J h y ∈ Λ}
  one_mem' := by intro y; rw [actV_one]
  mul_mem' := by
    intro a b ha hb y
    rw [actV_mul]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro g hg y
    have := hg (actV R σ J g⁻¹ y)
    rw [← actV_mul, mul_inv_cancel, actV_one] at this
    exact this.symm

end Lat

def UnramifiedAtFinite (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Prop :=
  ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 F) P

def OrbitConcl (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) (β : F) : Prop :=
  (∀ y ∈ latHat F E (L : Set (Fin M → E)), qR (Af F) σ J y = algebraMap F (Af F) β →
      ∃ k ∈ stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))),
        actV (Af F) σ J k (fun i => inclR (F := F) (Af F) (x i)) = y) ∧
  ({h : HA (Af F) σ J | actV (Af F) σ J h⁻¹ (fun i => inclR (F := F) (Af F) (x i)) ∈
        latHat F E (L : Set (Fin M → E))} =
      (Hstab (Af F) σ J (fun _ => x) : Set (HA (Af F) σ J)) *
        (stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))) : Set (HA (Af F) σ J))) ∧
  (stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))) ⊓ Hstab (Af F) σ J (fun _ => x) =
      stabLat (Af F) σ J (latHat F E (perpIn σ J L x)) ⊓ Hstab (Af F) σ J (fun _ => x))

def StabTransitive : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLat σ J L →
    ∀ β : F, (β = 1 ∨ β = -1) →
    ∀ x ∈ L, hE σ J x x = algebraMap F E β → OrbitConcl F E σ J L x β

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsSplitting (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=
  (∀ a : v.adicCompletion F, φ ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
  (∀ x, φ (sigR σ (v.adicCompletion F) x) = swapR _ (φ x)) ∧
  (∀ x, x ∈ intV E v ↔
    (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F)

variable {v : HeightOneSpectrum (𝓞 F)}
  (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

def prP : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.fst _ _).comp φ.toRingHom

def prPbar : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.snd _ _).comp φ.toRingHom

def primeOf (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) : Ideal (intV E v) :=
  Ideal.span {a : intV E v | Valued.v (p a) < 1}

def partOf {n : Type} (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (Λ : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F)) :
    Submodule (v.adicCompletionIntegers F) (n → v.adicCompletion F) :=
  Submodule.span (v.adicCompletionIntegers F)
    ((fun x : n → E ⊗[F] v.adicCompletion F => fun i => p (x i)) '' (Λ : Set _))

abbrev locLat {n : Type} [Fintype n] [DecidableEq n] (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (n → E)) : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) Λ

end Local

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

abbrev dualLb (L : ColLevel R F E sp gp C A clsLat) : Submodule (𝓞 E) (Fin R.k → E) :=
  Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)

def IsOverLattice (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (Fin R.k → E)) = ⊤ ∧
  dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E)) ∧
  L.Lb ≤ N ∧ N ≤ dualLb L ∧
  ∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∉ v.asIdeal → locLat v N = locLat v L.Lb

def LocalAtT (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal)
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=

  IsSplitting sp.cm.sig v φ ∧

  (∀ x : locLat v (dualLb L), (∀ i, prP φ (x.1 i) = 0) → L.fT v h x = 0) ∧

  Nonempty ((locLat v (dualLb L) ⧸ (locLat v L.Lb).submoduleOf (locLat v (dualLb L))) ≃ₗ[intV E v]
    (intV E v ⧸ primeOf (prP φ)) × (intV E v ⧸ primeOf (prPbar φ))) ∧

  partOf (prP φ) (locLat v N) = partOf (prP φ) (locLat v (dualLb L)) ∧
  partOf (prPbar φ) (locLat v N) = partOf (prPbar φ) (locLat v L.Lb) ∧

  (∀ g' : GL (Fin R.k) (v.adicCompletion F),
    ∃! g : UPts sp.cm.sig sp.gram0 (v.adicCompletion F), bc (prP φ) g.1 = g') ∧

  (∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
    g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ bc (prP φ) g ∈ stabGL (partOf (prP φ) (locLat v N))) ∧

  (∃ b : GL (Fin R.k) (v.adicCompletion F),
    (∀ y : Fin R.k → v.adicCompletion F,
      (b : Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)) *ᵥ y ∈ partOf (prP φ) (locLat v N) ↔
        ∀ i, y i ∈ v.adicCompletionIntegers F) ∧
    ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
      g ∈ levelVL sp.cm.sig sp.gram0 v N ↔ b⁻¹ * bc (prP φ) g * b ∈
        (bc (n := Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range) ∧

  ∃ (f : partOf (prP φ) (locLat v N) →ₗ[v.adicCompletionIntegers F]
      IsLocalRing.ResidueField (v.adicCompletionIntegers F))
    (ε : L.fM v h ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F)),
    (∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = prP φ a →
      ∀ m, ε (a • m) = a' • ε m) ∧
    (∀ (x : locLat v (dualLb L)) (y : partOf (prP φ) (locLat v N)),
      (∀ i, y.1 i = prP φ (x.1 i)) → f y = ε (L.fT v h x)) ∧
    f ≠ 0 ∧
    (∀ y, f ((A.T : v.adicCompletionIntegers F) • y) = 0) ∧
    (∀ y, f y = 0 ↔ y.1 ∈ partOf (prP φ) (locLat v L.Lb)) ∧
    ∀ g, g ∈ L.Uloc v ↔
      g ∈ levelVL sp.cm.sig sp.gram0 v N ∧ bc (prP φ) g ∈ stabFun (partOf (prP φ) (locLat v N)) f

def HasOverLattice (L : ColLevel R F E sp gp C A clsLat) : Prop :=
  (∀ i : Fin 2, A.T ≠ gp i) ∧
  ∃ N : Submodule (𝓞 E) (Fin R.k → E), IsOverLattice L N ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (h : (A.T : 𝓞 F) ∈ v.asIdeal), ∃ φ, LocalAtT L N v h φ) ∧
    (∀ v, L.Uloc v ≤ levelVL sp.cm.sig sp.gram0 v N) ∧
    L.U ≤ levelAfL sp.cm.sig sp.gram0 N

end Level

def SelfDualOverBase : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word),
    letI := D.host.cmStar
    Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T → HasOverLattice (Lv u)

end GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.OverPlaceIntegralForm
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

def stabRow {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (φ : n → A) :
    Subgroup (GL n A) where
  carrier := {g | φ ᵥ* (g : Matrix n n A) = φ}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : φ ᵥ* (a : Matrix n n A) = φ := ha
    have hb' : φ ᵥ* (b : Matrix n n A) = φ := hb
    show φ ᵥ* ((a * b : GL n A) : Matrix n n A) = φ
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, ha', hb']
  inv_mem' := by
    intro g hg
    have hg' : φ ᵥ* (g : Matrix n n A) = φ := hg
    show φ ᵥ* ((g⁻¹ : GL n A) : Matrix n n A) = φ
    conv_lhs => rw [← hg']
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]

section Local

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def toIntV : 𝓞 E →+* intV E v :=
  ((inclE (F := F) (v.adicCompletion F)).comp (algebraMap (𝓞 E) E)).codRestrict (intV E v)
    (fun a => Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E a, ⟨a, rfl⟩⟩, rfl⟩))

variable {E} {n : Type}

abbrev latV (Λ : Submodule (𝓞 E) (n → E)) :
    Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (intV E v) Λ

variable {v}

def pr₁ (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (x : n → E ⊗[F] v.adicCompletion F) : n → v.adicCompletion F := fun i => (s (x i)).1

def pr₂ (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (x : n → E ⊗[F] v.adicCompletion F) : n → v.adicCompletion F := fun i => (s (x i)).2

def IsSplitting (σ : E →ₐ[F] E) (P Pb : HeightOneSpectrum (𝓞 E))
    (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) : Prop :=
  P ≠ Pb ∧
  v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) = P.asIdeal * Pb.asIdeal ∧
  (∀ a : v.adicCompletion F, s ((1 : E) ⊗ₜ[F] a) = (a, a)) ∧
  (∀ x, s (sigR σ (v.adicCompletion F) x) = swapR _ (s x)) ∧
  (∀ x, x ∈ intV E v ↔
    (s x).1 ∈ v.adicCompletionIntegers F ∧ (s x).2 ∈ v.adicCompletionIntegers F) ∧
  (∀ a : 𝓞 E, a ∈ P.asIdeal ↔ Valued.v (s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).1 < 1) ∧
  (∀ a : 𝓞 E, a ∈ Pb.asIdeal ↔ Valued.v (s ((a : E) ⊗ₜ[F] (1 : v.adicCompletion F))).2 < 1)

end Local

section Level

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

abbrev baseDual (L : ColLevel R F E sp gp C A clsLat) : Submodule (𝓞 E) (Fin R.k → E) :=
  Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)

def OverAt (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal) : Prop :=
  ∃ (P Pb : HeightOneSpectrum (𝓞 E))
    (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),

    IsSplitting sp.cm.sig P Pb s ∧

    (∀ x : latV v (baseDual L), pr₁ s (x : Fin R.k → _) = 0 → L.fT v hv x = 0) ∧

    (∀ x : latV v (baseDual L),
      L.fT v hv x = 0 ↔ pr₁ s (x : Fin R.k → _) ∈ pr₁ s '' (latV v L.Lb : Set (Fin R.k → _))) ∧

    Nonempty ((latV v (baseDual L) ⧸ (latV v L.Lb).submoduleOf (latV v (baseDual L))) ≃ₗ[intV E v]
      ((intV E v ⧸ P.asIdeal.map (toIntV E v)) × (intV E v ⧸ Pb.asIdeal.map (toIntV E v)))) ∧

    pr₁ s '' (latV v N : Set (Fin R.k → _)) = pr₁ s '' (latV v (baseDual L) : Set (Fin R.k → _)) ∧
    pr₂ s '' (latV v N : Set (Fin R.k → _)) = pr₂ s '' (latV v L.Lb : Set (Fin R.k → _)) ∧

    (∃ hle : latV v N ≤ latV v (baseDual L),
      (L.fT v hv).comp (Submodule.inclusion hle) ≠ 0 ∧
      L.Uloc v = levelVL sp.cm.sig sp.gram0 v N ⊓
        stabFun (latV v N) ((L.fT v hv).comp (Submodule.inclusion hle))) ∧

    ∃ (h : GL (Fin R.k) (v.adicCompletion F))
      (φ : Fin R.k → v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
      (e : L.fM v hv ≃+
        v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)),
      pr₁ s '' (latV v N : Set (Fin R.k → _)) =
        Set.range (fun y : Fin R.k → v.adicCompletionIntegers F =>
          (h : Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)) *ᵥ fun i => (y i : v.adicCompletion F)) ∧
      Set.BijOn (fun g : GL (Fin R.k) (E ⊗[F] v.adicCompletion F) =>
          h⁻¹ * bc ((RingHom.fst _ _).comp s.toRingHom) g * h)
        (levelVL sp.cm.sig sp.gram0 v N)
        (bc (n := Fin R.k) (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).range ∧
      φ ≠ 0 ∧
      (∀ (x : latV v (baseDual L)) (y : Fin R.k → v.adicCompletionIntegers F),
        pr₁ s (x : Fin R.k → _) =
          (h : Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)) *ᵥ (fun i => (y i : v.adicCompletion F)) →
        e (L.fT v hv x) = ∑ i, φ i * Ideal.Quotient.mk _ (y i)) ∧
      ∀ g ∈ UPts sp.cm.sig sp.gram0 (v.adicCompletion F),
        g ∈ L.Uloc v ↔ h⁻¹ * bc ((RingHom.fst _ _).comp s.toRingHom) g * h ∈
          congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
            (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (stabRow φ)

def IsOverLattice (L : ColLevel R F E sp gp C A clsLat) (N : Submodule (𝓞 E) (Fin R.k → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧
  Submodule.span E (N : Set (Fin R.k → E)) = ⊤ ∧
  dualSet (sp.cm.sig : E →+* E) sp.gram0 N = (N : Set (Fin R.k → E)) ∧
  L.Lb ≤ N ∧
  (N : Set (Fin R.k → E)) ⊆ dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb ∧
  (∀ v : HeightOneSpectrum (𝓞 F), (A.T : 𝓞 F) ∉ v.asIdeal → latV v N = latV v L.Lb) ∧
  (∀ (v : HeightOneSpectrum (𝓞 F)) (hv : (A.T : 𝓞 F) ∈ v.asIdeal), OverAt L N v hv) ∧
  L.U ≤ levelAfL sp.cm.sig sp.gram0 N

end Level

def OverLatticeAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  letI := D.host.cmStar
  Formalism.MainNotions.StandardLattice.SplitsF D (D.mem u).A.T →
    (∀ i : Fin 2, (D.mem u).A.T ≠ D.host.g i) ∧
    ∃ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E), IsOverLattice (Lv u) N

def OverLattice : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), OverLatticeAt D Lv u

end GlobalTheory.IndefiniteRowSideFullHecke.OverPlaceIntegralForm

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeIndex
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

def IsSelfDualLat {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (N : Submodule (𝓞 E) (n → E)) : Prop :=
  Module.Finite (𝓞 E) N ∧ Submodule.span E (N : Set (n → E)) = ⊤ ∧
    (N : Set (n → E)) = dualSet σ J N

def IsSelfDualDefiniteLattice (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) : Prop :=
  letI := D.host.cmStar
  IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N

def stabHat (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  levelAfL D.sp.cm.sig D.sp.gram0 N

def levelU (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    Subgroup (GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :=
  letI := D.host.cmStar
  (Lv u).U

def IndexAt (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Prop :=
  (∀ i : Fin 2, SplitsF D (D.host.g i)) → SplitsF D (D.mem u).A.T →
    ∀ N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E), IsSelfDualDefiniteLattice D N →
      levelU D Lv u ≤ stabHat D N →
      (((levelU D Lv u).relIndex (stabHat D N) : ℕ) : ℝ) =
        idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def StabiliserLevelIndexFormula : Prop :=
  ∀ (D : D7) (Lv : LevelData D) (u : D.what₂.Word), IndexAt D Lv u

theorem factorT_pos (D : D7) (u : D.what₂.Word) :
    0 < (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f := by
  have hT : (1 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.one_lt
  have hk : D.R.k ≠ 0 := by
    have := D.R.m_add_three_le_k
    omega
  have hTk : (1 : ℝ) < ((D.mem u).A.T : ℝ) ^ D.R.k := one_lt_pow₀ hT hk
  exact pow_pos (by linarith) _

theorem stabHat_le (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    letI := D.host.cmStar
    stabHat D N ≤ UPts D.sp.cm.sig D.sp.gram0 (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  intro g hg
  unfold stabHat levelAfL level at hg
  exact (Subgroup.mem_inf.mp hg).1

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IsometryTransportFrames
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

section Spaces

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def HasSig (W : HSpace E) (P Q : ℕ) : Prop := W.SigOK ∧ ∀ τ : E →+* ℂ, W.sig τ = (P, Q)

def withLat (W : HSpace E) (L : Submodule (𝓞 E) W.V) (hL : Submodule.IsLattice E L)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) : HSpace E :=
  { W with L0 := L, standardTuple_isLattice := hL, baseLattice_isUnimodular := hU }

def frameMat (W₁ W₂ : HSpace E) (e : W₁.V →ₗ[E] W₂.V) : Matrix (Fin W₂.rank) (Fin W₁.rank) E :=
  LinearMap.toMatrix W₁.frame W₂.frame e

def CarriesLat (W₁ W₂ : HSpace E) (e : W₁.V ≃ₗ[E] W₂.V) : Prop := ∀ x : W₁.V, x ∈ W₁.L0 ↔ e x ∈ W₂.L0

end Spaces

def IsConjBy {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M₁ M₂ : ℕ}
    (J₁ : Matrix (Fin M₁) (Fin M₁) E) (J₂ : Matrix (Fin M₂) (Fin M₂) E) (T : Matrix (Fin M₂) (Fin M₁) E)
    (φ : HA (AF F) σ J₁ → HA (AF F) σ J₂) : Prop :=
  ∀ h : HA (AF F) σ J₁,
    ((HA.mat (AF F) σ J₂ (φ h) : GL (Fin M₂) (AF F ⊗[F] E)) : Matrix (Fin M₂) (Fin M₂) (AF F ⊗[F] E)) *
        T.map (inclR (F := F) (AF F)) =
      T.map (inclR (F := F) (AF F)) *
        ((HA.mat (AF F) σ J₁ h : GL (Fin M₁) (AF F ⊗[F] E)) : Matrix (Fin M₁) (Fin M₁) (AF F ⊗[F] E))

def LatticeIndep (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), HasSig W P Q →
    ∀ (L : Submodule (𝓞 D.host.E) W.V) (hL : Submodule.IsLattice D.host.E L)
      (hU : Formalism.HermitianLatticesTheory.IsUnimodular W.hT L) (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)),
      IsVolMeas D W P Q μ ↔ IsVolMeas D (withLat W L hL hU) P Q μ

def IsometryTransport (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSig W₁ P Q → HasSig W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, HSpace.IsIsomEmb W₁ W₂ e.toLinearMap → CarriesLat W₁ W₂ e →
      ∃ φ : HA (AF D.host.F) D.sp.cm.sig W₁.gram ≃ₜ* HA (AF D.host.F) D.sp.cm.sig W₂.gram,
        IsConjBy D.sp.cm.sig W₁.gram W₂.gram (frameMat W₁ W₂ e.toLinearMap) φ ∧
        (∀ h, h ∈ HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram ↔
          φ h ∈ HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) ∧
        (∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram),
          IsVolMeas D W₁ P Q μ ↔ IsVolMeas D W₂ P Q (μ.map φ)) ∧
        (∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W₁.gram))
            (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W₁.gram)),
          IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₁.gram) 𝓕 μ ↔
            IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₂.gram) (φ '' 𝓕) (μ.map φ))

def VolEqOfIsometric (D : D7) : Prop :=
  letI := D.host.cmStar
  VolTie D → ∀ (W₁ W₂ : HSpace D.host.E) (P Q : ℕ), HasSig W₁ P Q → HasSig W₂ P Q →
    ∀ e : W₁.V ≃ₗ[D.host.E] W₂.V, HSpace.IsIsomEmb W₁ W₂ e.toLinearMap → D.vol W₁ = D.vol W₂

def VolIndep (D : D7) : Prop := LatticeIndep D ∧ IsometryTransport D ∧ VolEqOfIsometric D

end GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerCompletions
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts

open scoped TensorProduct Pointwise
open NumberField IsDedekindDomain
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

def UnramifiedAtFinite (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def IsSelfDualLattice (L : Submodule (𝓞 E) (Fin M → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin M → E)) = ⊤ ∧
    ∀ y : Fin M → E, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (hE σ J x y)

def perpPart (L : Set (Fin M → E)) (x : Fin M → E) : Set (Fin M → E) :=
  {y | y ∈ L ∧ hE σ J x y = 0}

def actVec (k : HA (Af F) σ J) (y : Fin M → Af F ⊗[F] E) : Fin M → Af F ⊗[F] E :=
  ((HA.mat (Af F) σ J k : GL (Fin M) (Af F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec y

def ratVec (F : Type) [Field F] [NumberField F] [Algebra F E] (x : Fin M → E) :
    Fin M → Af F ⊗[F] E := fun i => inclR (Af F) (x i)

omit [NumberField E] in
theorem actVec_one (y : Fin M → Af F ⊗[F] E) : actVec σ J 1 y = y := by
  show ((1 : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec y = y
  simp

omit [NumberField E] in
theorem actVec_mul (g k : HA (Af F) σ J) (y : Fin M → Af F ⊗[F] E) :
    actVec σ J (g * k) y = actVec σ J g (actVec σ J k y) := by
  show (((HA.mat (Af F) σ J g) * (HA.mat (Af F) σ J k) : GL (Fin M) (Af F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _).mulVec y = _
  unfold actVec
  rw [Units.val_mul, Matrix.mulVec_mulVec]

def stabHat (L : Set (Fin M → E)) : Subgroup (HA (Af F) σ J) where
  carrier := {k | ∀ y, y ∈ latHat F E L ↔ actVec σ J k y ∈ latHat F E L}
  one_mem' := by intro y; rw [actVec_one]
  mul_mem' := by
    intro a b ha hb y
    rw [actVec_mul]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro g hg y
    have := hg (actVec σ J g⁻¹ y)
    rw [← actVec_mul, mul_inv_cancel, actVec_one] at this
    exact this.symm

abbrev stabVec (x : Fin M → E) : Subgroup (HA (Af F) σ J) := Hstab (Af F) σ J (fun _ => x)

def OrbitClaims (L : Set (Fin M → E)) (x : Fin M → E) (β : F) : Prop :=
  (∀ y ∈ latHat F E L, qR (Af F) σ J y = algebraMap F (Af F) β →
    ∃ k ∈ stabHat σ J L, actVec σ J k (ratVec F x) = y) ∧
  {h : HA (Af F) σ J | actVec σ J h⁻¹ (ratVec F x) ∈ latHat F E L} =
    (stabVec σ J x : Set (HA (Af F) σ J)) * (stabHat σ J L : Set (HA (Af F) σ J)) ∧
  stabHat σ J L ⊓ stabVec σ J x = stabHat σ J (perpPart σ J L x) ⊓ stabVec σ J x

end Lattice

def StabTransitive : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLattice σ J L →
    ∀ (β : F), (β = 1 ∨ β = -1) →
    ∀ x ∈ L, hE σ J x x = algebraMap F E β →
      OrbitClaims σ J (L : Set (Fin M → E)) x β

section Basic₂

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)


omit [NumberField E] in
theorem mem_stabVec (x : Fin M → E) (k : HA (Af F) σ J) :
    k ∈ stabVec σ J x ↔ actVec σ J k (ratVec F x) = ratVec F x := by
  constructor
  · intro h
    exact congrFun (MulAction.mem_stabilizer_iff.1 h) 0
  · intro h
    exact MulAction.mem_stabilizer_iff.2 (funext fun _ => h)

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts
end
end
