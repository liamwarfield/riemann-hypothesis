module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.WeylElementTransposeMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LocAddOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.IsUnitDetInFrame

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def RD_k.vac {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Submodule ℂ (Mx F E d.m d.n → ℂ) :=
  Submodule.span ℂ {f | ∃ g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ, g ∈ SB _ ∧
    f = fun X => (∏ w, fP 1 (R.loc w X)) * g fun k => (d.crd X k).2}
structure LiftedSchrodingerDatum (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Type 1 where
  n : ℕ
  Y : Spc F E n
  κ : Type
  [fin : Fintype κ]
  dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) κ
  om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)
  S : UA σ d.A.J →* Module.End ℂ ((κ → AF F) → ℂ)
  l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ
  b : GL (Fin n ⊕ Fin n) E
  K : Subgroup (G2 σ Y)
  a : G2 σ Y → ℝ
  ok : _root_.PositivityTheory.SiegelWeilFormula.Wk_k (σ := σ) d.B d.A Y d.r d.s d.χ κ dd om S l b K a d.μ d.D
attribute [instance] _root_.PositivityTheory.SiegelWeilFormula.LiftedSchrodingerDatum.fin
abbrev LiftedSchrodingerDatum.sd {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LiftedSchrodingerDatum d) : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ :=
  { B := d.B, m := d.m, n := L.n, A := d.A, Y := L.Y, r := d.r, s := d.s, χ := d.χ, κ := L.κ, dd := L.dd, om := L.om, S := L.S,
    l := L.l, b := L.b, K := L.K, a := L.a, μ := d.μ, D := d.D, bs := d.bs, ok := L.ok }
structure LD_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) extends _root_.PositivityTheory.SiegelWeilFormula.LiftedSchrodingerDatum d where
  i₀ : Fin d.n
  em : Fin n → Fin d.n
  inj : Function.Injective em
  rng : ∀ i, i ≠ i₀ ↔ i ∈ Set.range em
  j : G2 σ Y →* d.G
  cont : Continuous j
  j_in : ∀ g, (inFrame d.b (j g)).submatrix (Sum.map em em) (Sum.map em em) = inFrame b g
  j_out : ∀ g, ∀ u ∈ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin d.n ⊕ Fin d.n)), ∀ v,
    inFrame d.b (j g) u v = (1 : Matrix _ _ (AE F E)) u v ∧ inFrame d.b (j g) v u = (1 : Matrix _ _ (AE F E)) v u
  res : ∀ Φ ∈ d.sch, ∀ Φ' ∈ toLiftedSchrodingerDatum.sd.sch,
    (∀ X : Mx F E d.m d.n, (∀ a, X a i₀ = 0) → toLiftedSchrodingerDatum.sd.T Φ' (X.submatrix id em) = d.T Φ X) →
    ∀ g (X : Mx F E d.m d.n), (∀ a, X a i₀ = 0) → toLiftedSchrodingerDatum.sd.T (om g Φ') (X.submatrix id em) = d.T (d.om (j g) Φ) X
namespace LD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def _root_.PositivityTheory.SiegelWeilFormula.LD_k.IsRes (Φ : d.Fn) (Φ' : L.sd.Fn) : Prop :=
  Φ' ∈ L.sd.sch ∧ ∀ X : Mx F E d.m d.n, (∀ a, X a L.i₀ = 0) → L.sd.T Φ' (X.submatrix id L.em) = d.T Φ X
def _root_.PositivityTheory.SiegelWeilFormula.LD_k.ratV : AddSubgroup (Fin L.n → AE F E) := AddSubgroup.closure (Set.range (GlobalTheory.ThK.incV F : (Fin L.n → E) → _))
def _root_.PositivityTheory.SiegelWeilFormula.LD_k.UData (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E)) (𝓤 : Set (Fin L.n → AE F E)) : Prop :=
  (∀ u, ∃ a', inFrame d.b (uM u) = Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (u j)) 0 0 a') ∧
    ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain L.ratV 𝓤 ν ∧ ν 𝓤 = 1
def _root_.PositivityTheory.SiegelWeilFormula.LD_k.IsSub (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) : Prop :=
  (∀ i, T.1.1 L.i₀ i = 0 ∧ T.1.1 i L.i₀ = 0) ∧ T'.1.1 = T.1.1.submatrix L.em L.em
end LD
def MainV_k (c : ℂ) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Prop := ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ x,
  HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)
def MainC_k (c : ℂ) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Prop := ∀ Φ, d.KFin Φ → ∀ x,
  HolValueAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I Φ x)
def WhitAt_k (c : ℂ) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) : Prop :=
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T → ∀ x,
    HolValueAt (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
      (s0 d.m d.n) (c * d.orb T (d.om x Φ))
def EisWk_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁
def WhitEq_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.m = d.n → ∀ Φ, d.KFin Φ → _root_.PositivityTheory.SiegelWeilFormula.WhitAt_k 2 d Φ
def WhitLow_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), d.m < d.n → ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → _root_.PositivityTheory.SiegelWeilFormula.WhitAt_k 0 d Φ
def MainEq_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.m = d.n → _root_.PositivityTheory.SiegelWeilFormula.MainC_k 2 d
def LDEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), 2 ≤ d.n → Nonempty (_root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def VacK_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), (∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac) ∧ R.vac ≤ R.fock ∧
  ∀ (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd), ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∃ Φ', L.IsRes Φ Φ' ∧ L.sd.T Φ' ∈ R'.vac
def IwaQ_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ x : d.G, ∃ (q : d.G) (g : L.sd.G) (k : d.G) (r : ℝ) (c : ℂ), k ∈ d.K ∧
  x = q * L.j g * k ∧ 0 < r ∧ (∀ g' : L.sd.G, d.a (L.j g' * x) = r * L.a (g' * g)) ∧
  ∀ Φ ∈ d.sch, ∀ g' (X : Mx F E d.m d.n), (∀ a, X a L.i₀ = 0) →
    d.T (d.om (L.j g' * q) Φ) X = c * d.T (d.om (L.j g') Φ) X
def CTSplit_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ s₁ f, IsSec d.K d.χ s₁ f → d.Eis f s₁ → ∃ t : ℝ, ∀ z : ℂ, t < z.re →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ nb' lam' 𝓖', CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖' →
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ T T', L.IsSub T T' → ∃ c₂ : d.G → ℂ,
    (∀ x, ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T (uM u * x) ∂ν =
      fc d.B.ψ L.b nb' lam' 𝓖' (GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) fun g =>
        ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) T' 1 + c₂ x) ∧
    ∀ w (τ : ℝ) (y : GR d.n) x, IsDil (Pi.single L.i₀ 1) τ y →
      c₂ (R.ι w y * x) = Complex.exp (τ * (d.n - 2 * z)) * c₂ x
def UEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), (∃ uM ν 𝓤, L.UData uM ν 𝓤) ∧ ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ w (φ : d.G → ℂ), Continuous φ →
  (∀ u ∈ L.ratV, ∀ x, φ (uM u * x) = φ x) →
  (∀ u (y : GR d.n), uM u = R.ι w y → ∀ x, φ (uM u * x) = φ x) → ∀ u x, φ (uM u * x) = φ x
def FcConj_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 →
  (∀ T, ¬ IsND T → ∃ γ ∈ rat2 σ d.Y, ∃ T₀ T', L.IsSub T₀ T' ∧ ∀ φ : d.G → ℂ, Continuous φ →
    (∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g) → ∀ x, fc d.B.ψ d.b nb lam 𝓖 φ T x = fc d.B.ψ d.b nb lam 𝓖 φ T₀ (γ * x)) ∧
  ∀ uM ν 𝓤, L.UData uM ν 𝓤 → ∀ T T', L.IsSub T T' → ∀ φ : d.G → ℂ, Continuous φ →
    (∀ γ' ∈ rat2 σ d.Y, ∀ g, φ (γ' * g) = φ g) → ∀ u ∈ L.ratV, ∀ x,
      fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T x
def OrbRes_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), (d.m < d.n → ∀ T, IsND T → ∀ Φ, d.orb T Φ = 0) ∧
  ∀ (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) T T', L.IsSub T T' → ∀ Φ Φ', L.IsRes Φ Φ' → d.orb T Φ = L.sd.orb T' Φ'
def Step_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d), ∀ R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd, d.m < d.n → _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R' → _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R
def StepOf_k : Prop :=
  HolLead → HolT → _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocInst_k → _root_.PositivityTheory.SiegelWeilFormula.GSplit_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.EisWk_k →
    _root_.PositivityTheory.SiegelWeilFormula.LamBd_k → _root_.PositivityTheory.SiegelWeilFormula.LamSing_k → _root_.PositivityTheory.SiegelWeilFormula.FourierZero_k → _root_.PositivityTheory.SiegelWeilFormula.Unfold_k → _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k → _root_.PositivityTheory.SiegelWeilFormula.VacK_k → _root_.PositivityTheory.SiegelWeilFormula.IwaQ_k → _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k → _root_.PositivityTheory.SiegelWeilFormula.UEx_k → _root_.PositivityTheory.SiegelWeilFormula.FcConj_k → _root_.PositivityTheory.SiegelWeilFormula.OrbRes_k → _root_.PositivityTheory.SiegelWeilFormula.Step_k
def VacAll_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ c : ℂ, _root_.PositivityTheory.SiegelWeilFormula.MainV_k c R → _root_.PositivityTheory.SiegelWeilFormula.MainC_k c d
def MainLe_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.m ≤ d.n → _root_.PositivityTheory.SiegelWeilFormula.MainC_k 2 d
def MainLeOf_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.RDEx_k → _root_.PositivityTheory.SiegelWeilFormula.LDEx_k → _root_.PositivityTheory.SiegelWeilFormula.VacK_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → _root_.PositivityTheory.SiegelWeilFormula.MainEq_k → _root_.PositivityTheory.SiegelWeilFormula.Step_k → _root_.PositivityTheory.SiegelWeilFormula.VacAll_k → _root_.PositivityTheory.SiegelWeilFormula.MainLe_k
def FieldOf_k : Prop := _root_.GlobalTheory.ThK.Dbl.EisBL_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.SWStdLt_k → _root_.PositivityTheory.SiegelWeilFormula.MainLe_k → _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Place
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.cm (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsCMExt F E σ := d.ok.good.cm
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.std (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsStd d.B.ψ := d.ok.good.std
theorem continuous_cw_k (w : InfinitePlace F) {p q : Type} : Continuous (fun X : Matrix p q (AE F E) => d.cw w X) :=
  continuous_id.matrix_map (continuous_piInf (d.B.emb w))
theorem cw_ext_k {p q : Type} {X Z : Matrix p q (AE F E)} (h1 : ∀ w, d.cw w X = d.cw w Z) (h2 : finOne F • X = finOne F • Z) :
    X = Z :=
  mat_ext d.cm d.B.emb h1 h2
theorem cw_cA_k (w : InfinitePlace F) {p q : Type} (X : Matrix p q (AE F E)) : d.cw w (X.map (cA σ)) = (d.cw w X).map star :=
  map_cA d.cm _ X
end PositivityTheory.SiegelWeilFormula.Place
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem sigma_sigma_of_good_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (a : E) : σ (σ a) = a := by
  obtain ⟨-, -, -, h⟩ := hB.cm
  let τ : E →+* ℂ := Classical.arbitrary _
  apply τ.injective
  rw [h, h, star_star]
theorem coefData_exists_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) :
    ∃ nb lam 𝓖, CoefData (σ := σ) (Y := Y) b nb lam 𝓖 := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB
  obtain ⟨hlc, hsc, ht2, hbo⟩ := nA_top hσ hb
  obtain ⟨K, hK, hc⟩ := nF_cocompact hσ hb
  obtain ⟨lam, 𝓖, hlam, h𝓖, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (nA σ Y b) (nF σ Y b) K hK hc).1
  exact ⟨nbE σ Y b, lam, 𝓖, isNMap_nbE hσ hb, hlam, h𝓖, h1⟩
theorem coefEx_k : _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k := fun _F _E _ _ _ _ _ _σ d => _root_.PositivityTheory.SiegelWeilFormula.kfour.coefData_exists_k d.ok.good d.ok.frame
end PositivityTheory.SiegelWeilFormula.kfour
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAway
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def SD_k.IsAwayW (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : Prop :=
  ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.GoodAway (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : Prop :=
  d.IsAwayW w Ψ ∧ Ψ ≠ 0 ∧ ∀ f, IsSw f → R.tens w f Ψ ∈ d.schM
end RD
def GoodAwayEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F), ∃ Ψ, R.GoodAway w Ψ
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TP
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}
end Gen
structure Tools_k : Prop where
  swFull : _root_.GlobalTheory.ThK.Dbl.SWFullX_k
  boxSec : _root_.GlobalTheory.ThK.Dbl.BoxSecX_k
  dbl : _root_.GlobalTheory.ThK.Dbl.DblX_k
  stab2 : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k
  cpt : _root_.GlobalTheory.ThK.Dbl.CptAll_k
  basic : _root_.GlobalTheory.ThK.ThetaBasic_k
  polSch : _root_.GlobalTheory.ThK.Dbl.PolSch_k
  unfold0 : _root_.GlobalTheory.ThK.Dbl.Unfold0_k
  pairEx : _root_.PositivityTheory.ThKG.Tow.PairEx_k
  split : _root_.GlobalTheory.ThK.Dbl.SplitModel_k
  vacFix : _root_.GlobalTheory.ThK.Dbl.VacFix2_k
  acts : _root_.GlobalTheory.ThK.ActsEx_k
  lie1 : GlobalTheory.RealLift.LieFirst
  lie2 : GlobalTheory.RealLift.LieSecond
section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
end CM
def TLift_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E), _root_.UpperTheory.TP.W.GoodK (cj E) B →
    ∀ (n : ℕ), 1 ≤ n → ∀ X : Spc (maximalRealSubfield E) E n, X.J = 1 → X.IsHerm (cj E) B n 0 →
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (W : Spc (maximalRealSubfield E) E d) (δ : E), W.J = δ • (1 : Matrix (Fin d) (Fin d) E) →
      W.IsSkew (cj E) B d 0 → ∀ (χX χW : Chr (maximalRealSubfield E) E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ),
      IsHecke (maximalRealSubfield E) E χX → IsHecke (maximalRealSubfield E) E χW →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χW d →
      HasExp B.emb χX mX → HasExp B.emb χW mW →
      ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (lam : InfinitePlace (maximalRealSubfield E) → DomWeight n),
        GlobalTheory.UnitaryBC.IsAutRepU U → (∀ w, GlobalTheory.UnitaryBC.HasWeightAt U (B.emb w).1 (lam w)) →
        (∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k) → ∃ U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ), IsLift B χX χW mX mW lam U U'
def HgtFst_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B n 0 →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∃ t₀ : ℝ, ∀ μ : Measure (UA σ X.J), μ.IsHaarMeasure → ∀ t, t₀ ≤ t → Integrable (fun g => a (e (g, 1)) ^ t) μ
def Rallis_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n → 1 ≤ d →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ t₀ : ℝ, (∀ t, t₀ ≤ t → Integrable (fun g => a (e (g, 1)) ^ t) M.μ) → t₀ < (d : ℝ) / 2 →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ Φ ∈ PolData B M, ∀ φ, IsFn φ →
      Integrable (fun g => coef om ν Φ g * star (mc M φ g)) M.μ ∧
        (lift M om Φ φ = 0 → ∫ g, coef om ν Φ g * star (mc M φ g) ∂M.μ = 0)
def Decomp_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B n 0 → ∀ S : Finset (Pl F),
    (∃ j : gInf σ X × gAt σ X S × gOff σ X S ≃ₜ* UA σ X.J, ∀ x, j x = x.1.1 * x.2.1.1 * x.2.2.1) ∧
    IsCompact (gInf σ X : Set (UA σ X.J)) ∧ IsClosed (gAt σ X S : Set (UA σ X.J)) ∧ IsClosed (gOff σ X S : Set (UA σ X.J)) ∧
    IsCompact {g : UA σ X.J | IntAll g} ∧ IsOpen {g : UA σ X.J | IntAll g} ∧ (∀ g ∈ gInf σ X, IntAll g) ∧
    (∀ b ∈ gAt σ X S, ∃ c : Pl F → UA σ X.J, (∀ v, c v ∈ locGrp σ X v) ∧ (∀ v ∈ S, OffAt v ((c v)⁻¹ * b)) ∧
      ∀ H : Subgroup (UA σ X.J), (∀ v ∈ S, c v ∈ H) → b ∈ H) ∧
    ∀ g : UA σ X.J, {v | ¬ IntAt v g}.Finite
def BumpAny_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n → 2 * n ≤ d →
    ∀ v, ∀ N ∈ 𝓝 (1 : UA σ X.J), ∃ H φ, IsBump B M om v H φ ∧ (H : Set (UA σ X.J)) ⊆ N
def Datum_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ S : Finset (Pl F), UnrOff χW (S : Set (Pl F)) →
    ∀ (H : Pl F → Subgroup (UA σ X.J)) φ, IsFin M φ → (∀ v ∈ S, IsBump B M om v (H v) (φ v)) → (∀ v ∉ S, φ v = M.vac v) →
    ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → coef om ν (pure f₀ φ) 1 ≠ 0 ∧
      ∀ x ∈ gInf σ X, ∀ b ∈ gAt σ X S, ∀ c ∈ gOff σ X S, (b ∉ ⨆ v ∈ S, H v → coef om ν (pure f₀ φ) (x * b * c) = 0) ∧
        ∃ s : ℂ, ‖s‖ = a (e (c, 1)) ^ ((d : ℝ) / 2) ∧ (IntAll c → s = 1) ∧
          ∀ x' ∈ gInf σ X, ∀ b' ∈ ⨆ v ∈ S, H v, coef om ν (pure f₀ φ) (x' * b' * c) = s * coef om ν (pure f₀ φ) x'
def Tail_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B n 0 →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ (μ : Measure (UA σ X.J)) (t : ℝ), μ.IsHaarMeasure → Integrable (fun g => a (e (g, 1)) ^ t) μ → ∀ S₀ : Finset (Pl F),
      ∃ S : Finset (Pl F), S₀ ⊆ S ∧ ∀ μC : Measure (gOff σ X S), μC.IsHaarMeasure →
        ∫⁻ c in {c : gOff σ X S | ¬ IntAll c.1}, ENNReal.ofReal (a (e (c.1, 1)) ^ t) ∂μC < μC {c | IntAll c.1}
def RealPair_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' → n ≤ d →
    ∀ (δ : E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ), X.J = 1 → W.J = δ • (1 : Matrix (Fin d) (Fin d) E) → HasExp B.emb χX mX →
    HasExp B.emb χW mW → ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (lam : InfinitePlace (maximalRealSubfield E) → DomWeight n),
      GlobalTheory.UnitaryBC.IsAutRepU U → (∀ w, GlobalTheory.UnitaryBC.HasWeightAt U (B.emb w).1 (lam w)) →
      (∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k) → ∃ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 ∧ ∃ φ ∈ U, φ ≠ 0 ∧ SameType om e U f₀ φ ∧
        ∀ w, ∃ lam', IsLiftWt (lam w) (mX w) (mW w) lam' ∧ HasType B M om e' f₀ w lam'
def SchurStep_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' →
    ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → ∀ f₀, f₀ ≠ 0 → ∀ φ, φ ≠ 0 → SameType om e U f₀ φ →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ φf, IsFin M φf → ∀ μA : Measure (gInf (cj E) X), μA.IsHaarMeasure →
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ c ∈ gOff (cj E) X ∅, ∫ x, coef om ν (pure f₀ φf) x.1 * star (mc M (φ ∘ e.symm) (x.1 * c)) ∂μA =
      κ * coef om ν (pure f₀ φf) 1 * star (mc M (φ ∘ e.symm) c)
def NonVan_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' → 2 * n ≤ d →
    ∀ K a (ε : UA (cj E) X.J × UA (cj E) X.J →* G2 (cj E) X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (ε (g, g'))) →
    ∀ t₀ : ℝ, (∀ t, t₀ ≤ t → Integrable (fun g => a (ε (g, 1)) ^ t) M.μ) → t₀ < (d : ℝ) / 2 →
    ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → ∀ φ, φ ≠ 0 →
      SameType om e U f₀ φ → ∃ φf, IsFin M φf ∧ lift M om (pure f₀ φf) (φ ∘ e.symm) ≠ 0
def LiftAut_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' →
    ∃ Θ : PolData B M →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₛₗ[starRingEnd ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ),
      ∀ (Φ : PolData B M) φ, GlobalTheory.UnitaryBC.IsAutFormU φ → Θ Φ φ = lift M om Φ.1 (φ ∘ e.symm) ∘ e' ∧ GlobalTheory.UnitaryBC.IsAutFormU (Θ Φ φ) ∧
        ∀ g h, ∃ Φ₁ : PolData B M, Φ₁.1 = om (e g, e' h) Φ.1 ∧
          Θ Φ₁ (GlobalTheory.UnitaryBC.RU E n g φ) = GlobalTheory.UnitaryBC.RU E d h (Θ Φ φ)
def ReadLift_k : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E) (n d : ℕ) (X : Spc (maximalRealSubfield E) E n) (W : Spc (maximalRealSubfield E) E d)
    (M : Model (cj E) X W) (χX χW : Chr (maximalRealSubfield E) E) (om : Rep (cj E) X W), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J), IsBr X e → IsBr W e' →
    ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ))
      (pr : (GlobalTheory.UnitaryBC.UA E d → ℂ) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ)), GlobalTheory.UnitaryBC.IsAutRepU U → GlobalTheory.UnitaryBC.IsAutRepU U' →
      (∀ f, GlobalTheory.UnitaryBC.IsAutFormU f → pr f ∈ U' ∧ ∀ x, pr (GlobalTheory.UnitaryBC.RU E d x f) = GlobalTheory.UnitaryBC.RU E d x (pr f)) →
      ∀ f₀ ∈ M.Pol B.ψ B.emb, ∀ φ ∈ U, ∀ φf, IsFin M φf → pr (lift M om (pure f₀ φf) (φ ∘ e.symm) ∘ e') ≠ 0 →
      (∀ w lam', HasType B M om e' f₀ w lam' → GlobalTheory.UnitaryBC.HasWeightAt U' (B.emb w).1 lam') ∧
      ∀ (v : Pl (maximalRealSubfield E)) (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v) τ τ', CompAt U (splitPrime t) τ → CompAt U' (splitPrime t) τ' →
        LocPair t χX χW τ τ'
theorem tLift_of_k (T : _root_.UpperTheory.TP.Tools_k) (hH : _root_.GlobalTheory.ThK.Dbl.HgtEx_k) (h1 : BrEx) (h2 : _root_.UpperTheory.TP.HgtFst_k) (h3 : _root_.UpperTheory.TP.RealPair_k) (h4 : _root_.UpperTheory.TP.NonVan_k) (h5 : _root_.UpperTheory.TP.LiftAut_k) (h6 : ProjEx)
    (h7 : _root_.UpperTheory.TP.ReadLift_k) : _root_.UpperTheory.TP.TLift_k := by
  intro E _ _ _ B hB n hn X hXJ hX
  obtain ⟨⟨K, a, hK, ha, -⟩, ε, -, hε⟩ := hH _ E (cj E) B n X n 0 hB (Or.inl hX)
  obtain ⟨t₀, ht₀⟩ := h2 _ E (cj E) B n X hB hX K a ε hK ha hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * t₀)
  refine ⟨max N (2 * n), fun d hd W δ hWJ hW χX χW mX mW hχX hχW rX rW eX eW U lam hU hwt hdom => ?_⟩
  have hd1 : 2 * n ≤ d := (le_max_right _ _).trans hd
  have hd2 : t₀ < (d : ℝ) / 2 := by
    have : (N : ℝ) ≤ d := by exact_mod_cast (le_max_left _ _).trans hd
    linarith
  have hδ : δ ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty (InfinitePlace (maximalRealSubfield E)) := inferInstance
    obtain ⟨-, A, hA⟩ := hW.sig w
    have := congrFun (congrFun hA (Sum.inl ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
    simp [hWJ] at this
  obtain ⟨⟨M, hM⟩, hom⟩ := T.pairEx _ E (cj E) B hB n d X W n 0 d 0 hX hW
  obtain ⟨om, hP⟩ := hom χX χW hχX hχW rX rW M hM
  obtain ⟨e, he⟩ := h1 E n X 1 one_ne_zero (by rw [hXJ, one_smul])
  obtain ⟨e', he'⟩ := h1 E d W δ hδ hWJ
  obtain ⟨f₀, hf₀, hf0, φ, hφ, hφ0, hS, hT⟩ := h3 E B n d X W M χX χW om hP hn e e' he he' (by omega) δ mX mW hXJ hWJ eX eW U lam hU hwt hdom
  obtain ⟨φf, hfin, hne⟩ := h4 E B n d X W M χX χW om hP hn e e' he he' hd1 K a ε hK ha hε t₀ (ht₀ M.μ hM.haar) hd2 U hU f₀ hf₀ hf0 φ hφ0 hS
  obtain ⟨Θ, hΘ⟩ := h5 E B n d X W M χX χW om hP hn e e' he he'
  have hmem : pure f₀ φf ∈ PolData B M := Submodule.subset_span ⟨f₀, hf₀, φf, hfin.1, hfin.2, rfl⟩
  obtain ⟨q1, q2, -⟩ := hΘ ⟨_, hmem⟩ φ (hU.aut φ hφ)
  have hne' : Θ ⟨_, hmem⟩ φ ≠ 0 := by
    rw [q1]
    intro h0
    apply hne
    funext h
    have := congrFun h0 (e'.symm h)
    simpa using this
  obtain ⟨U', pr, hU', hpr, hp⟩ := h6 E d _ q2 hne'
  rw [q1] at hpr
  obtain ⟨r1, r2⟩ := h7 E B n d X W M χX χW om hP hn e e' he he' U U' pr hU hU' hp f₀ hf₀ φ hφ φf hfin hpr
  exact ⟨U', hU', fun w => (hT w).imp fun lam' h => ⟨r1 w lam' h.2, h.1⟩, r2⟩
end UpperTheory.TP
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourW
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem auxiliaryExistence_holds : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ν, 𝓕, hν, h𝓕, h1⟩ := exists_cov (F := F) (E := E) d.m d.n
  obtain ⟨i1, i2, i3, i4⟩ := doubled_group_topological_properties σ d.Y
  exact ⟨⟨ν, hν, 𝓕, h𝓕, h1⟩, exists_w d.ok.frame, i1, i2, i3, i4⟩
end PositivityTheory.SiegelWeilFormula.kfour
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDict
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def IsPureBy_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) (P : InfinitePlace F → PX d.m d.n)
    (gf : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ) : Prop :=
  (∀ v, IsLocallyConstant (gf v) ∧ HasCompactSupport (gf v)) ∧
    (∀ᶠ v in cofinite, gf v = Set.indicator {c | ∀ k, c k ∈ v.adicCompletionIntegers F} 1) ∧
    d.T Φ = fun X => (∏ w, fP (P w) (R.loc w X)) * ∏ᶠ v, gf v (fun k => HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd X k).2)
def Jd_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) : Matrix (Fin d.m) (Fin d.m) E := (η • d.A.J)ᵀ
structure Rel_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (T : nF σ d.Y d.b) (η : E)
    (T₀ : Matrix (Fin d.n) (Fin d.n) E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) : Prop where
  levi : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1
  rat : T.1.1 = incM F T₀
  ne : η ≠ 0
  herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j
  hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)
  th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y)
  frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star
  gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1
def RelEx_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ, d.KFin Φ → ∀ P gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf →
  ∀ x t u, inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1 → ∀ T : nF σ d.Y d.b, IsND T →
  ∃ (η : E) (T₀ : Matrix (Fin d.n) (Fin d.n) E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) (l : InfinitePlace F → ℝ) (εs : InfinitePlace F → Fin d.m → Bool)
    (Φg : (Fin d.n → Fin d.m → AF F ⊗[F] E) → ℂ) (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (ν : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)),
    _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g ∧ (∀ Y, Φg Y = d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ)) ∧
    (∀ y : Fin d.m → E, HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y = 0 → y = 0) ∧ (∃ e : InfinitePlace F → Bool, εs = fun i _ => e i) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) ∧ (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧
    (Td η T₀).det ≠ 0 ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F d.B.ψ ∧ Gen.IsPlaces σ d.B.ψ θ l ∧ Gen.IsFrames (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) θ εs fr ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin Φg (Gen.phiInf θ l fr g P) Φf ∧
    HeckeCharacterZeroLocus.SiegelWeilU.SdW F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (AF F) d.B.ψ d.n μ ∧
    HeckeCharacterZeroLocus.SiegelWeilU.SdHerm F E σ (AF F) d.B.ψ d.n ν
def HeightDict_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) x t u T η T₀ hOf θ fr g, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w →
  ∃ (lv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (C : ℝ), 0 < C ∧
    (∀ v, (lv v).IsAddHaarMeasure) ∧ (∀ v, Gen.IsCO (L₁ v) ∧ Gen.IsCO (L₂ v)) ∧
    (∀ᶠ v in cofinite, (L₁ v : Set (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v ∧
      (L₂ v : Set (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v) ∧
    ∀ β, 0 < Gen.nuA θ g lv L₁ L₂ (hOf β).1 ∧ d.a (w * nb β * x) = C * (Gen.nuA θ g lv L₁ L₂ (hOf β).1)⁻¹
def MeasDict_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) x t u T η T₀ hOf θ fr g, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Rel_k d R x t u T η T₀ hOf θ fr g →
  (∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ν,
    HeckeCharacterZeroLocus.SiegelWeilU.SdHerm F E σ (AF F) d.B.ψ d.n ν → MeasurableEmbedding hOf ∧ MeasurePreserving hOf lam ν) ∧
  ∀ μ νc, HeckeCharacterZeroLocus.SiegelWeilU.SdW F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (AF F) d.B.ψ d.n μ → d.IsCov νc →
    MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) ∧ MeasurePreserving toMx μ νc
def ThetaDict_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E), η ≠ 0 → (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) →
  ∃ μH 𝓕, HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) μH ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) μH 𝓕 ∧
    ∀ (T : nF σ d.Y d.b) T₀, T.1.1 = incM F T₀ → ∀ Φ ∈ d.sch,
      d.orb T Φ = HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (fun Y => d.T Φ (toMx Y))
        {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) X = Td η T₀})
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockAlg
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FockDecK
theorem UpperTheory.Reformulated.B.Glb2.fock_dec_k :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {d : PositivityTheory.SiegelWeilFormula.SD_k σ} (R : PositivityTheory.SiegelWeilFormula.RD_k d)
      (w : NumberField.InfinitePlace F),
      ∀ f ∈ R.fock,
        ∃ (k : ℕ) (P : Fin k → PositivityTheory.Rg.Sw.PX d.m d.n) (Ψ : Fin k → PositivityTheory.SiegelWeilFormula.Mx F E d.m d.n → ℂ),
          (∀ (i : Fin k), Ψ i ∈ R.away w) ∧ f = ∑ i : Fin k, R.tens w (PositivityTheory.SiegelWeilFormula.fP (P i)) (Ψ i) := by
  intro F E _ _ _ _ _ σ d R w f hf
  obtain ⟨k, c, u, rfl⟩ := Submodule.mem_span_set'.1 hf
  choose P g hg hu using fun i => (u i).2
  refine ⟨k, fun i => P i w, fun i => c i • _, fun i => Submodule.smul_mem _ (c i)
    (Submodule.subset_span ⟨P i, g i, hg i, rfl⟩), Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hu i]
  funext X
  simp only [PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm (PositivityTheory.SiegelWeilFormula.fP _ _), ← mul_assoc (PositivityTheory.SiegelWeilFormula.fP _ _),
    @Finset.mul_prod_erase _ _ _ (_) _ (fun v => PositivityTheory.SiegelWeilFormula.fP (P i v) (R.loc v X)) _
      (Finset.mem_univ w)]
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
theorem tens_add_k (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (Ψ Ψ' : Mx F E d.m d.n → ℂ) :
    R.tens w f (Ψ + Ψ') = R.tens w f Ψ + R.tens w f Ψ' := by
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.add_apply, mul_add]
theorem tens_smul_k (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (a : ℂ) (Ψ : Mx F E d.m d.n → ℂ) :
    R.tens w f (a • Ψ) = a • R.tens w f Ψ := by
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Pi.smul_apply, smul_eq_mul]
  ring
def tensL_k (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) : (Mx F E d.m d.n → ℂ) →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := R.tens w f
  map_add' := _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_add_k R w f
  map_smul' a Ψ := _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_smul_k R w f a Ψ
omit R in
theorem cw_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (X Z : Mx F E d.m d.n) : d.cw w (X + Z) = d.cw w X + d.cw w Z :=
  Matrix.map_add _ (map_add _) X Z
theorem loc_add_of_k (w : InfinitePlace F) (X Z : Mx F E d.m d.n) (h : d.cw w Z = 0) : R.loc w (X + Z) = R.loc w X := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.cw_add_k, h, add_zero]
omit R in
theorem crd_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X Z : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) :
    d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
  rw [Matrix.add_apply, map_add (f := _), Finsupp.add_apply]
omit R in
theorem crd_fin_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Z : Mx F E d.m d.n) (h : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd Z k).2 = 0 := by
  have e1 : d.crd (finOne F • Z) k = finOne F * d.crd Z k := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
    rw [Matrix.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  have e2 : d.crd (finOne F • Z) k = 0 := by
    rw [h]
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
    rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
  have e3 : (finOne F * d.crd Z k).2 = (d.crd Z k).2 := by
    show (finOne F).2 * (d.crd Z k).2 = _
    rw [show (finOne F).2 = 1 from rfl, one_mul]
  rw [← e3, ← e1, e2]
  rfl
theorem away_inv_k (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) :
    ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X := by
  intro X Z hZ hf
  induction hΨ using Submodule.span_induction generalizing X with
  | mem x hx =>
    obtain ⟨P, g, -, rfl⟩ := hx
    have e1 : ∀ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' (X + Z)) = fP (P w') (R.loc w' X) := fun w' hw' => by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.loc_add_of_k R w' X Z (hZ w' (Finset.ne_of_mem_erase hw'))]
    have e2 : (fun k => (d.crd (X + Z) k).2) = fun k => (d.crd X k).2 := by
      funext k
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_add_k]
      show (d.crd X k).2 + (d.crd Z k).2 = _
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_fin_k d Z hf k, add_zero]
    show (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' (X + Z))) * g (fun k => (d.crd (X + Z) k).2) =
      (∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g (fun k => (d.crd X k).2)
    rw [Finset.prod_congr rfl e1, e2]
  | zero => rfl
  | add x y _ _ hx hy => simp only [Pi.add_apply, hx, hy]
  | smul a x _ hx => simp only [Pi.smul_apply, hx]
theorem away_tens_k (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) (P : PX d.m d.n) :
    R.tens w (fP P) Ψ ∈ R.fock := by
  have h : R.away w ≤ R.fock.comap (_root_.PositivityTheory.SiegelWeilFormula.KFock.tensL_k R w (fP P)) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨P', g, hg, rfl⟩
    refine Submodule.subset_span ⟨Function.update P' w P, g, hg, ?_⟩
    funext X
    show fP P (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P' w') (R.loc w' X)) * g fun k => (d.crd X k).2) =
      (∏ w', fP (Function.update P' w P w') (R.loc w' X)) * g fun k => (d.crd X k).2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, mul_assoc]
    congr 2
    exact Finset.prod_congr rfl fun w' hw' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw')]
  exact h hΨ
theorem fock_dec_k (w : InfinitePlace F) (f : Mx F E d.m d.n → ℂ) (hf : f ∈ R.fock) :
    ∃ (k : ℕ) (P : Fin k → PX d.m d.n) (Ψ : Fin k → Mx F E d.m d.n → ℂ),
      (∀ i, Ψ i ∈ R.away w) ∧ f = ∑ i, R.tens w (fP (P i)) (Ψ i) :=
  by apply _root_.UpperTheory.Reformulated.B.Glb2.fock_dec_k <;> assumption
omit R in
theorem T_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Φ' : d.Fn) : d.T (Φ + Φ') = d.T Φ + d.T Φ' := by
  funext X
  show d.l (d.dd.rho d.B.ψ _ (Φ + Φ')) = d.l (d.dd.rho d.B.ψ _ Φ) + d.l (d.dd.rho d.B.ψ _ Φ')
  rw [← map_add (f := _)]
  congr 1
  funext y
  simp [Darboux.rho, schr, mul_add]
omit R in
theorem T_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (a : ℂ) (Φ : d.Fn) : d.T (a • Φ) = a • d.T Φ := by
  funext X
  show d.l (d.dd.rho d.B.ψ _ (a • Φ)) = a • d.l (d.dd.rho d.B.ψ _ Φ)
  rw [← map_smul]
  congr 1
  funext y
  simp [Darboux.rho, schr, mul_left_comm]
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockArch
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem crd_cmb_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (c : Fin d.m × Fin d.n × Fin 2 → AF F) : d.crd (d.cmb c) = c := by
  funext k
  obtain ⟨i, j, l⟩ := k
  have e : d.cmb c i j = ∑ k, c (i, j, k) • (Algebra.TensorProduct.basis (AF F) d.bs) k := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  show (Algebra.TensorProduct.basis (AF F) d.bs).repr (d.cmb c i j) l = c (i, j, l)
  rw [e, Module.Basis.repr_sum_self]
theorem detIm_ne_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) :
    ((d.B.emb w).1 (d.bs 0)).im * ((d.B.emb w).1 (d.bs 1)).re -
      ((d.B.emb w).1 (d.bs 0)).re * ((d.B.emb w).1 (d.bs 1)).im ≠ 0 := by
  have hcm : IsCMExt F E σ := d.ok.good.cm
  haveI : IsTotallyReal F := hcm.1
  haveI : IsTotallyComplex E := hcm.2.1
  set τ : E →+* ℂ := (d.B.emb w).1 with hτ
  have hw : w.IsReal := IsTotallyReal.isReal w
  have hreal : ∀ f : F, (τ (algebraMap F E f)).im = 0 := by
    intro f
    have e1 : τ (algebraMap F E f) = w.embedding f := RingHom.congr_fun (d.B.emb w).2 f
    have e3 : ComplexEmbedding.conjugate w.embedding = w.embedding :=
      ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
    have e4 := RingHom.congr_fun e3 f
    rw [ComplexEmbedding.conjugate_coe_eq] at e4
    rw [e1]
    exact Complex.conj_eq_iff_im.mp e4
  have hexp : ∀ e : E, τ e = τ (algebraMap F E (d.bs.repr e 0)) * τ (d.bs 0) +
      τ (algebraMap F E (d.bs.repr e 1)) * τ (d.bs 1) := by
    intro e
    conv_lhs => rw [← d.bs.sum_repr e]
    simp [Fin.sum_univ_two, Algebra.smul_def, map_add (f := _), map_mul]
  obtain ⟨e, he⟩ : ∃ e : E, (τ e).im ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
    rw [InfinitePlace.isComplex_mk_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    refine RingHom.ext fun x => ?_
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_eq_iff_im.mpr (hne x)
  intro hD
  apply he
  have h1 := hexp 1
  have h2 := hexp e
  set p := τ (algebraMap F E (d.bs.repr 1 0)) with hp
  set q := τ (algebraMap F E (d.bs.repr 1 1)) with hq
  set p' := τ (algebraMap F E (d.bs.repr e 0)) with hp'
  set q' := τ (algebraMap F E (d.bs.repr e 1)) with hq'
  have ip : p.im = 0 := hreal _
  have iq : q.im = 0 := hreal _
  have ip' : p'.im = 0 := hreal _
  have iq' : q'.im = 0 := hreal _
  rw [map_one] at h1
  have h1re := congrArg Complex.re h1
  have h1im := congrArg Complex.im h1
  have h2im := congrArg Complex.im h2
  simp only [Complex.one_re, Complex.one_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, ip, iq,
    ip', iq', zero_mul, sub_zero, add_zero] at h1re h1im h2im
  linear_combination -(p'.re * (τ (d.bs 0)).re + q'.re * (τ (d.bs 1)).re) * h1im - (p.re * q'.re - q.re * p'.re) * hD +
    (p'.re * (τ (d.bs 0)).im + q'.re * (τ (d.bs 1)).im) * h1re + h2im
def realLinearCoordinates (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hr : ∀ w : InfinitePlace F, w.IsReal) :
    (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) where
  toFun r w a j := star (∑ i, ((R.fr w)⁻¹).1 a i *
    ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))
  map_add' r s := by
    funext w a j
    simp only [Pi.add_apply, Prod.fst_add, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, mul_add, star_add]
  map_smul' c r := by
    funext w a j
    simp only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul, Prod.smul_fst, smul_eq_mul, Complex.ofReal_mul]
    conv_rhs => rw [show (c : ℂ) = star (c : ℂ) from (Complex.conj_ofReal c).symm, ← star_mul']
    congr 1
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
theorem realLinearCoordinates_injective (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hr : ∀ w : InfinitePlace F, w.IsReal) : Function.Injective (_root_.PositivityTheory.SiegelWeilFormula.KFock.realLinearCoordinates d R hr) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro r hr0
  have hz : ∀ w i j, ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l) = 0 := by
    intro w
    let Z : Matrix (Fin d.m) (Fin d.n) ℂ := fun i j => ∑ l : Fin 2, (((r (i, j, l)).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l)
    have h1 : ((R.fr w)⁻¹).1 * Z = 0 := by
      ext a j
      have h := congrFun (congrFun (congrFun hr0 w) a) j
      have h' : star (∑ i, ((R.fr w)⁻¹).1 a i * Z i j) = 0 := h
      rw [star_eq_zero] at h'
      rw [Matrix.mul_apply]
      exact h'
    have h2 : Z = 0 := by
      have e : Z = (R.fr w).1 * (((R.fr w)⁻¹).1 * Z) := by
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      rw [e, h1, Matrix.mul_zero]
    intro i j
    exact congrFun (congrFun h2 i) j
  funext k
  obtain ⟨i, j, l⟩ := k
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · have h := hz v.1 i j
    rw [Fin.sum_univ_two] at h
    have hi := real_indep (_root_.PositivityTheory.SiegelWeilFormula.KFock.detIm_ne_k d v.1) h
    have ev : (⟨v.1, hr v.1⟩ : {w : InfinitePlace F // w.IsReal}) = v := Subtype.ext rfl
    rw [ev] at hi
    fin_cases l
    · exact hi.1
    · exact hi.2
  · exact absurd v.2 (InfinitePlace.not_isComplex_iff_isReal.mpr (hr v.1))
theorem archEquiv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∃ L : (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ),
      ∀ (c : Fin d.m × Fin d.n × Fin 2 → AF F) (w : InfinitePlace F),
        L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) w = R.loc w (d.cmb c) := by
  have hcm : IsCMExt F E σ := d.ok.good.cm
  haveI : IsTotallyReal F := hcm.1
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  have hdim : Module.finrank ℝ (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) =
      Module.finrank ℝ (InfinitePlace F → Fin d.m → Fin d.n → ℂ) := by
    simp only [Module.finrank_pi_fintype, mixedEmbedding.finrank, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, Fintype.card_prod, Fintype.card_fin]
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← InfinitePlace.card_add_two_mul_card_eq_rank,
      IsTotallyReal.nrComplexPlaces_eq_zero]
    ring
  have hinj := _root_.PositivityTheory.SiegelWeilFormula.KFock.realLinearCoordinates_injective d R hr
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  refine ⟨(LinearEquiv.ofBijective (_root_.PositivityTheory.SiegelWeilFormula.KFock.realLinearCoordinates d R hr) ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun c w => ?_⟩
  funext a j
  show star (∑ i, ((R.fr w)⁻¹).1 a i * ∑ l : Fin 2,
      ((((InfiniteAdeleRing.ringEquiv_mixedSpace F (c (i, j, l)).1).1 ⟨w, hr w⟩ : ℝ) : ℂ) * (d.B.emb w).1 (d.bs l))) =
    star ((((R.fr w)⁻¹).1 * d.cw w (d.cmb c)) a j)
  rw [Matrix.mul_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  show _ = piInf (d.B.emb w) (∑ l, c (i, j, l) ⊗ₜ[F] d.bs l)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  rfl
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AdDecompK
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def SD_k.Indep (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : Prop :=
  ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X
def AdDecomp_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ ε w, d.IsW ε w → ∀ (e : AF F), e * e = e → ∀ x : d.G,
  e • inFrame d.b x = e • (1 : Matrix _ _ (AE F E)) →
  ∃ (x₁ x₂ x₃ x₄ : d.G) (t c b : Mx F E d.n d.n) (a a' : GL (Fin d.n) (AE F E)), x = x₁ * (w * x₂ * w⁻¹) * x₃ * x₄ ∧
    inFrame d.b x₁ = Matrix.fromBlocks 1 t 0 1 ∧ inFrame d.b x₂ = Matrix.fromBlocks 1 c 0 1 ∧
    inFrame d.b x₃ = Matrix.fromBlocks a.1 0 0 a'.1 ∧ inFrame d.b x₄ = Matrix.fromBlocks 1 b 0 1 ∧
    e • t = 0 ∧ e • c = 0 ∧ e • b = 0 ∧ e • a.1 = e • (1 : Mx F E d.n d.n) ∧ e • a'.1 = e • (1 : Mx F E d.n d.n)
def AwayAct_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ w (x : d.G), d.cw w (inFrame d.b x) = 1 →
  ∃ A : (Mx F E d.m d.n → ℂ) → Mx F E d.m d.n → ℂ, ∀ Ψ, d.Indep w Ψ → d.Indep w (A Ψ) ∧
    ∀ f, IsSw f → ∀ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ → d.T (d.om x Φ) = R.tens w f (A Ψ)
def FinAct_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ x : d.G, (∀ w, d.cw w (inFrame d.b x) = 1) →
  ∀ g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F),
    ∀ f : Mx F E d.m d.n → ℂ, (∀ X Z, (∀ w, d.cw w Z = 0) → f (X + Z) = f X) → ∀ Φ ∈ d.sch,
      d.T Φ = (fun X => f X * g fun k => (d.crd X k).2) → d.T (d.om x Φ) = fun X => f X * g' fun k => (d.crd X k).2
end PositivityTheory.SiegelWeilFormula
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCut
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def IsLevi_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : Prop :=
  ∃ t u : GL (Fin d.n) (AE F E), inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1
def IsPureT_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Φ : d.Fn) : Prop :=
  ∃ (P : InfinitePlace F → PX d.m d.n)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ),
    (∀ v, IsLocallyConstant (g v) ∧ HasCompactSupport (g v)) ∧
    (∀ᶠ v in cofinite, g v = Set.indicator {c | ∀ k, c k ∈ v.adicCompletionIntegers F} 1) ∧
    d.T Φ = fun X => (∏ w, fP (P w) (R.loc w X)) *
      ∏ᶠ v, g v (fun k => HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd X k).2)
def PureSpan_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ, d.KFin Φ → d.T Φ ∈ R.fock →
    ∃ (k : ℕ) (c : Fin k → ℂ) (Φs : Fin k → d.Fn), (∀ i, d.KFin (Φs i) ∧ _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureT_k R (Φs i)) ∧ Φ = ∑ i, c i • Φs i
def CellFormula_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) ν, d.IsCov ν → ∀ ε w, d.IsW ε w → ∀ Φ ∈ d.sch, ∀ (g x : d.G) (β : Mx F E d.n d.n),
    inFrame d.b g = Matrix.fromBlocks 1 β 0 1 →
      d.sec0 Φ (w * g * x) = ∫ Z, d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram Z Z))) * d.T (d.om x Φ) Z ∂ν
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayDecG
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem inFrame_mul_k (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y :=
  GlobalTheory.EisBL.DoubledParabolic.inFrame_mul d.b x y
theorem inFrame_one_k : inFrame d.b (1 : d.G) = 1 :=
  GlobalTheory.EisBL.DoubledParabolic.inFrame_one d.b
theorem inFrame_inj_k {x y : d.G} (h : inFrame d.b x = inFrame d.b y) : x = y :=
  PositivityTheory.SiegelWeilFormula.kunf.inFrame_injective d.b h
theorem isUnit_det_inFrame_k (x : d.G) : IsUnit (inFrame d.b x).det :=
  Matrix.isUnit_det_of_left_inverse (GlobalTheory.EisBL.DoubledParabolic.inFrame_inv_mul d.b x)
variable {d} {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
include hε
theorem inU_inFrame_k (x : d.G) : (inFrame d.b x)ᵀ * jF d.n ε * (inFrame d.b x).map (cA σ) = jF d.n ε :=
  PositivityTheory.SiegelWeilFormula.kunf.frame_eq hε x
theorem exists_of_inU_k (M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hM : Mᵀ * jF d.n ε * M.map (cA σ) = jF d.n ε) : ∃ x : d.G, inFrame d.b x = M := by
  set J : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := jF d.n ε with hJ
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hJJ : J * (((ε : ℤ) : AE F E) • J) = 1 := by
    rw [Matrix.mul_smul, hJ, jF, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    congr 1 <;> simp [smul_smul, hεε]
  have hT : Mᵀ * (J * M.map (cA σ) * (((ε : ℤ) : AE F E) • J)) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hM, hJJ]
  have hu : IsUnit Mᵀ.det := Matrix.isUnit_det_of_right_inverse hT
  rw [Matrix.det_transpose] at hu
  exact PositivityTheory.SiegelWeilFormula.kunf.exists_of_frame hε M M⁻¹ (Matrix.mul_nonsing_inv M hu) hM
end
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end
