module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure RealSide (D : D7) : Type 1 where
  Γ : Type
  [grp : Group Γ]
  [fin : Fintype Γ]
  Pl0 : Type
  I0 : Type
  T : Type
  A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m
  core : Formalism.L2.Pj.CoreJ D
  [alg : Algebra core.Q.c.F D.what₂.LL]
  R : RealDat3 D A3 core.Q.c.F
  F : Face3 D A3
  cG : G0 R.Pg D.R.r ≃* G0g D.nd
  geo : GlobalTheory.RealGeo.GeoHalf core R.toRealDat fun _ => 1
  char : R.Char3 F
  phs : ∀ j, R.phs j = 1
  guard : FWT.QGuard R.toRealDat
  valKs : GlobalTheory.RealGeo.ValKs R.toRealDat
  idem : ∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)
  unif : R.toRealDat.LUnif
  integral : R.toRealDat.LIntegral
  inGeo : GlobalTheory.RealGeo.InGeo geo
  finT : Finite T
  host : HostHyp D
  std : ∀ j, FWT.VStd D j
  size : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV

attribute [instance] RealSide.grp RealSide.fin RealSide.alg

variable {D : D7}

structure FieldOk (X : RealSide D) : Prop where
  galois : IsGalois ℚ ↥D.LL0
  star : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0
  vals : Formalism.L2.Host.ValLL0 D X.R.C
  ray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange
  roots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange
  split : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK

structure SerSide (X : RealSide D) (E : IntegralHeckeForms.XD D) : Type 1 where
  S : NX.RatDat D.ntw
  YS : NX.NExpRealS X.R X.cG S
  sup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b),
    x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b
  H : NX.NExpRealH X.R X.cG S YS
  reads : GlobalTheory.ExportPin.Reads X.R X.cG S YS H.hL
  del : ∀ i b P, P ∉ D.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (algebraMap (D.ntw.O0 i) (D.ntw.O i)
      ((if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))
  Z : ExportTie YS X.geo.v₀
  U_eq : ∀ g : X.Γ, X.cG (X.R.eG g) ∈ D.nexp.U ↔ g ∈ X.F.P0
  psi_eq : ∀ i b (g : X.F.P0) (h : X.cG (X.R.eG g) ∈ D.nexp.U),
    Z.ρ.e i b (D.nexp.psiU i b ⟨_, h⟩ : (FractionRing (D.ntw.O i))ˣ) = (D.what₂.embLL (X.F.ψ0 g : D.what₂.LLˣ))⁻¹
  low : ∀ i (P : PlE D.host), ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK * (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') : ℕ) :
    𝓞 D.host.E) ∈ P.asIdeal → P ∈ D.ntw.S0 i
  Sb : ∀ i, ∀ P ∈ X.R.Sb, P ∈ D.ntw.S0 i
  B_range : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, LinearMap.range (D.nexp.embB i j b) =
    D.nexp.Bsup i j b ⊓ (V0 D.nexp i j b).restrictScalars (D.ntw.O i)
  hk_emb : ∀ i j b k P (x : D.ntw.B i j b), 1 ≤ j → j ≤ D.R.m → HkIdx i k P →
    D.nexp.embB i j b (D.ntw.hk i j b k P x) = D.nexp.hkF i j b k P (D.nexp.embB i j b x)
  hk_split : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k P, HkIdx i k P →
    ((LinearMap.charpoly (D.ntw.hk i j b k P)).map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)))).Splits
  off : OffRange D
  all : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b a, a ∈ E.Dat0 i j b

def BaseTup {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (i : D.ntw.Tw) : Prop :=
  ∀ j b, ∃ t : X.T, X.R.xi t = (Y.Z.ρ.B i j b).de.chi ∧ X.R.Q t = (Y.Z.ρ.B i j b).de.Q

structure GalSide (D : D7) : Type 1 where
  wd : GlobalTheory.RowTie.WDTie D.nd D.naut
  lab : GlobalTheory.HeightCounting.LabTrue D wd
  cf : CharFrame D
  chr : GlobalTheory.HeightCounting.CharSide D cf
  triple : GlobalTheory.Triple.IsTriple D
  lam : GlobalTheory.LamTie.LamDat D
  lamOk : lam.Ok
  lamTie : GlobalTheory.LamTie.IsLamTie D.ntw lam
  rank : 100 ≤ D.R.r
  primes : ∀ k, 2 * D.R.r ≤ D.host.g k

section Abstract

variable {ρ : Setup D.ntw} (hρ : ρ.Good) (rd : Rds D.nexp ρ)

structure Laws : Prop where
  faithful : ∀ i j b, Faithful (rd i j b)
  act : ∀ i j b, ActRead (rd i j b)
  hecke : ∀ i j b, HeckeRead (rd i j b)
  rat : ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, Rat hρ (rd i j b)

def XiType : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b Q M, InRange D.ntw i Q → ∀ s h P, ρ.IsDatum i j b s h P →
  (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a x, rd i j b x = ρ.xi i j b D.nexp Q M h P a →
    x ∈ Fm0 D.nexp i ((j : ℕ) + 1) b

def XiBdd : Prop := ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b s h P, ρ.IsDatum i j b s h P → ∃ c : ℕ, ∀ Q M, InRange D.ntw i Q →
  (∀ v ∈ Q, ((normProd s : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal) → ∀ a x, rd i j b x = ρ.xi i j b D.nexp Q M h P a →
    ((D.ntw.l i : D.ntw.O i) ^ c) • x ∈ D.nexp.Bsup i ((j : ℕ) + 1) b

def SpanGood (i : D.ntw.Tw) : Prop := ∀ (j : Fin D.R.m) b, ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b,
  rd i j b x ∈ Submodule.span ℂ {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ f = ρ.theta i j b h P}

def SumOnto (i : D.ntw.Tw) : Prop := ∀ (j : Fin D.R.m) b, ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b,
  ∃ F ∈ Submodule.span ℂ (ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)),
    rd i j b x = ρ.sum i j b 0 ∅ 1 F

end Abstract

structure Inputs (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ) : Prop where
  a1 : BlochKatoReduction.adm1 (BlochKatoReduction.bk0 D)
  a2 : BlochKatoReduction.adm2 D
  a8 : BlochKatoReduction.adm8 D
  good : AllGood D.nexp
  sig : D.nexp.sig_all
  a9 : BlochKatoReduction.adm9 D N0
  a10 : BlochKatoReduction.adm10 D
  univChar : GlobalTheory.UnivChar.IsUnivChar D.nexp
  off : OffRange D
  rel : ThURel D.nexp
  l3 : IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp
  t4 : IntegralHeckeForms.admT4 D.nexp E
  type : TypeKept E
  univ : UnivSup D E
  supG : SupG D
  supFull : SupFull D
  supHk : SupHk D
  commG : CommG D
  comm : HkComm D
  ss : HkSS D
  hyp : ∀ i, D.ntw.NonzeroIndexPlace i → BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) i

end GlobalTheory.TwInputs

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspSubsetBaseForms
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverRead.Test

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct

variable {D : D7} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ}

theorem rd_apply (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f₂ : Rul C.d.Xo₂ C.d.c₂) (g : GA D (T.V j σ)) :
    C.rd a f₂ g = C.cc₂ (C.dict₂ g).1 * ((lieFac (T.Q.Dw j) (xiR D) a : ℂ) * T.mu j σ g *
      rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2) := by
  simp only [Cover.rd, Pi.smul_apply, smul_eq_mul, adel_muPin]
  ring

theorem zero_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : 0 ∈ C.ratForms a n := by
  refine ⟨0, ⟨Submodule.zero_mem _, by rw [map_zero]; exact Submodule.zero_mem _⟩, ?_⟩
  funext g
  rw [rd_apply, map_zero]
  simp

theorem add_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {φ ψ : GA D (T.V j σ) → ℂ}
    (hφ : φ ∈ C.ratForms a n) (hψ : ψ ∈ C.ratForms a n) : φ + ψ ∈ C.ratForms a n := by
  obtain ⟨f, hf, rfl⟩ := hφ
  obtain ⟨f', hf', rfl⟩ := hψ
  refine ⟨f + f', ⟨Submodule.add_mem _ hf.1 hf'.1, by rw [map_add (f := _)]; exact Submodule.add_mem _ hf.2 hf'.2⟩, ?_⟩
  funext g
  simp only [Pi.add_apply, rd_apply, map_add (f := _)]
  ring

theorem smul_mem_ratForms (C : Cover T j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : C.d.c₂.F)
    {φ : GA D (T.V j σ) → ℂ} (hφ : φ ∈ C.ratForms a n) : C.σ₂ x • φ ∈ C.ratForms a n := by
  obtain ⟨f, hf, rfl⟩ := hφ
  refine ⟨x • f, ⟨Submodule.smul_mem _ _ hf.1, by rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hf.2⟩, ?_⟩
  funext g
  simp only [Pi.smul_apply, rd_apply, map_smulₛₗ, smul_eq_mul]
  ring

end GlobalTheory.CoverRead.Test
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Scale

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks)

def IsScaleAt {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ)
    (c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (Rl.cV j).W) (c : ℂ) : Prop :=
  ∀ F : VV D.what₂.LL (FWT.lamV D j),
    harmFn (Wc D j).rank B.w B.F.BS (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 F)) =
      c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)

variable {Rl}

theorem IsScaleAt.ioP_eq {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)} {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ}
    {c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (Rl.cV j).W} {c : ℂ} (h : IsScaleAt Rl B u c0 c)
    {H : Submodule ℂ (PolF D (Wc D j).rank (Vc D j).rank)}
    (hinj : ∀ P ∈ H, harmFn (Wc D j).rank B.w B.F.BS P = 0 → P = 0)
    {F : VV D.what₂.LL (FWT.lamV D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hP : P ∈ H)
    (hio : Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 F) ∈ H)
    (hPF : harmFn (Wc D j).rank B.w B.F.BS P =
      coefFn D.what₂.embLL (FWT.lamV D j) (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) :
    Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0 F) = c • P :=
  sub_eq_zero.1 (hinj _ (H.sub_mem hio (H.smul_mem c hP)) (by rw [map_sub, map_smul, h F, hPF, sub_self]))

theorem RealPin.phase_mul_thetaKO {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (h : RealPin Rl cG ρ) (i : D.ntw.Tw)
    {j : Fin D.R.m} (b : Bool) {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ} {w : (Rl.cV j).W}
    {P : PolF D (Wc D j).rank (Vc D j).rank} {c : ℂ} (hP : Rl.ioP j (PiTensorProduct.tprod ℂ u) w = c • P) (ph : ℂ)
    (om : PairRep (Vc D j) (Wc D j)) (s : GA D (Vc D j)) (f : WO (Vc D j) (Wc D j) → ℂ) :
    (fun g => ph * thetaKO om s g (harmVec Rl.toRealDat j u w f)) = (ph * c) • series (ρ.B i j b).F om f s P := by
  have e : harmVec Rl.toRealDat j u w f = (ρ.B i j b).F.fock f (c • P) := by
    rw [← hP, GlobalTheory.ExportSeries.Frame.fock, h.psi, h.inf, h.cartT, h.onbT, funext (h.onbS i j b)]
    rfl
  rw [e, mul_smul, ← map_smul]
  rfl

end Scale

section Phase

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (j : Fin D.R.m) {σ : T.Q.c.F →+* ℂ}
  (hV : T.V ((j : ℕ) + 1) σ = Wc D j)


variable {T j hV} in
theorem isRat_mul {C : Cover T ((j : ℕ) + 1) σ} {κ : WeightFamilies.Wt D ((j : ℕ) + 1)} {φ : GA D (Wc D j) → ℂ} (h : IsRat T j hV C κ φ)
    {a : ℂ} (ha : a ∈ C.σ₂.fieldRange) : IsRat T j hV C κ fun g => a * φ g := by
  obtain ⟨φ', h1, rfl⟩ := h
  obtain ⟨x, rfl⟩ := ha
  refine ⟨C.σ₂ x • φ', GlobalTheory.CoverRead.Test.smul_mem_ratForms C _ _ x h1, ?_⟩
  have key : ∀ {V W : HSp D} (e : V = W) (z : ℂ) (ψ : GA D V → ℂ), castDict e (z • ψ) = fun g => z * castDict e ψ g := by
    rintro V _ rfl z ψ
    rfl
  exact key hV _ _


variable {T R j hV} in
theorem seriesRatOn_mul {C : Cover T ((j : ℕ) + 1) σ} {κ : WeightFamilies.Wt D ((j : ℕ) + 1)} {u : ∀ τ, lowT (R.MW j (sg0 D A)) τ}
    {c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W} {ph : ℂ} (h : SeriesRatOn T R j hV C κ u c0 ph)
    {a : ℂ} (ha : a ∈ C.σ₂.fieldRange) : SeriesRatOn T R j hV C κ u c0 (a * ph) := by
  intro s hs f hf w hw
  obtain ⟨h1, h2⟩ := h s hs f hf w hw
  refine ⟨?_, fun δ δc hδ => ⟨fun dd hdd => ?_, fun om hom => ?_⟩⟩
  · simpa only [mul_assoc] using isRat_mul h1 ha
  · simpa only [mul_assoc, mul_left_comm a] using isRat_mul ((h2 δ δc hδ).1 dd hdd) ha
  · simpa only [mul_assoc] using isRat_mul ((h2 δ δc hδ).2 om hom) ha

def IsRatPhase (κ : WeightFamilies.Wt D ((j : ℕ) + 1)) (u : ∀ τ, lowT (R.MW j (sg0 D A)) τ)
    (c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W) (ph : ℂ) : Prop :=
  ∀ C : Cover T ((j : ℕ) + 1) σ, GoodCover T R j C κ.n → (embLL0 D).fieldRange ≤ C.σ₂.fieldRange →
    SeriesRatOn T R j hV C κ u c0 ph

variable {T R j hV}

theorem IsRatPhase.mul {κ : WeightFamilies.Wt D ((j : ℕ) + 1)} {u : ∀ τ, lowT (R.MW j (sg0 D A)) τ}
    {c0 : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W} {ph : ℂ} (h : IsRatPhase T R j hV κ u c0 ph)
    {a : ℂ} (ha : a ∈ (embLL0 D).fieldRange) : IsRatPhase T R j hV κ u c0 (a * ph) :=
  fun C hC hL => seriesRatOn_mul (h C hC hL) (hL ha)

end Phase

section Scalar

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m}
  (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) (B : Base (Vc D j) (Wc D j))

def IsRatScalar (ν : ℂ) : Prop :=
  ∃ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L ∧
    ∃ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) ∧
      ∃ c ph : ℂ, c ≠ 0 ∧ ‖ph‖ = 1 ∧ ν = ph * c ∧ IsScaleAt Rl B u (c0L j) c ∧
        IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph

variable {T Rl κ v₀ hV B}

theorem IsRatScalar.intro {gramR c0R c0L} (h : Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L) {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ}
    (hu : ∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) {c ph : ℂ} (hc : c ≠ 0) (hph : ‖ph‖ = 1)
    (hs : IsScaleAt Rl B u (c0L j) c) (hr : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph) :
    IsRatScalar T Rl κ v₀ hV B (ph * c) :=
  ⟨gramR, c0R, c0L, h, u, hu, c, ph, hc, hph, rfl, hs, hr⟩

theorem IsRatScalar.isScale {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) :
    ∃ c ph : ℂ, c ≠ 0 ∧ ‖ph‖ = 1 ∧ ν = ph * c ∧ IsScale Rl v₀ B c := by
  obtain ⟨g, cR, cL, h0, u, hu, c, ph, h1, h2, h3, h4, -⟩ := h
  exact ⟨c, ph, h1, h2, h3, g, cR, cL, h0, u, hu, h4⟩

theorem IsRatScalar.ne_zero {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) : ν ≠ 0 := by
  obtain ⟨c, ph, h1, h2, rfl, -⟩ := h.isScale
  exact mul_ne_zero (fun e => by simp [e] at h2) h1

theorem IsRatScalar.mul {ν : ℂ} (h : IsRatScalar T Rl κ v₀ hV B ν) {a : ℂ} (ha : a ∈ (embLL0 D).fieldRange) (h0 : ‖a‖ = 1) :
    IsRatScalar T Rl κ v₀ hV B (a * ν) := by
  obtain ⟨g, cR, cL, h1, u, hu, c, ph, h2, h3, rfl, h4, h5⟩ := h
  exact ⟨g, cR, cL, h1, u, hu, c, a * ph, h2, by rw [norm_mul, h0, h3, one_mul], (mul_assoc _ _ _).symm, h4, h5.mul ha⟩

end Scalar

end GlobalTheory.SeriesTie

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SmulMemRatForms
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀)

def eKs : S.Ks ≃+* T0.Q.c.F := (YS.fi (NX.idxOf D 1)).eK

theorem eKs_LL (a : S.Ks) : algebraMap T0.Q.c.F D.what₂.LL (eKs YS a) = algebraMap S.Ks D.what₂.LL a := (YS.fi _).eK_LL a

def sideK (i : D.ntw.Tw) (b : Bool) : T0.Q.c.F →+* FractionRing (D.ntw.O i) :=
  (NX.ιK S i b).comp (eKs YS).symm.toRingHom

theorem sideK_eKs (i : D.ntw.Tw) (b : Bool) (a : S.Ks) : sideK YS i b (eKs YS a) = NX.ιK S i b a :=
  congrArg (NX.ιK S i b) ((eKs YS).symm_apply_apply a)

def cuspOf (j : Fin D.R.m) : NX.FmK S ((j : ℕ) + 1) ≃+ Cu T0 κ j :=
  AddEquiv.trans (N := (Rl.FW j).WK)
    { toFun := fun x => ⟨(YS.fi j).e (Subtype.val x), ((YS.fi j).wk _).1 (Subtype.property x)⟩
      invFun := fun y => ⟨(YS.fi j).e.symm y.1, ((YS.fi j).wk _).2 (by rw [LinearEquiv.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => Subtype.ext ((YS.fi j).e.symm_apply_apply _)
      right_inv := fun y => Subtype.ext ((YS.fi j).e.apply_symm_apply _)
      map_add' := fun x y => Subtype.ext ((YS.fi j).e.map_add _ _) }
    (fw.e j).symm.toAddEquiv

theorem e_cuspOf (j : Fin D.R.m) (x : NX.FmK S ((j : ℕ) + 1)) :
    (fw.e j (cuspOf YS fw j x) : Fin (Rl.nW j) → D.what₂.LL) = (YS.fi j).e (Subtype.val x) :=
  congrArg Subtype.val ((fw.e j).apply_symm_apply _)

theorem cuspOf_smul (j : Fin D.R.m) (a : S.Ks) (x : NX.FmK S ((j : ℕ) + 1)) :
    cuspOf YS fw j (a • x) = eKs YS a • cuspOf YS fw j x := by
  refine (fw.e j).injective (Subtype.ext ?_)
  rw [e_cuspOf, (fw.e j).map_smul, Submodule.coe_smul, e_cuspOf, ← algebraMap_smul D.what₂.LL (eKs YS a), eKs_LL,
    ← (YS.fi j).e.map_smul, algebraMap_smul]
  rfl

theorem cuspOf_mem_sec (j : Fin D.R.m) (x : NX.FmK S ((j : ℕ) + 1)) :
    (cuspOf YS fw j x : T0.R ((j : ℕ) + 1)) ∈ sec (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (wtA (κ j)) (κ j).n :=
  cusp_le_sec _ _ _ _ _ (cuspOf YS fw j x).2

theorem evW_eq_phiC (j : Fin D.R.m) (hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j)
    (hev : fw.Evaluates) (x : NX.FmK S ((j : ℕ) + 1)) :
    GlobalTheory.SeriesTie.evW YS v₀ j (Subtype.val x) = phiC T0 hV (wtA (κ j)) (cuspOf YS fw j x : T0.R ((j : ℕ) + 1)) := by
  have h := hev j (sg0 D A3.A) (base_embedding_good T0 Rl.toRealDat fw.alg_eq fw.laws.pins.2.2.1) hV (cuspOf YS fw j x)
  refine Eq.trans ?_ h
  change _ = (Rl.HW j _).e ((Rl.FW j).j _ (fw.e j (cuspOf YS fw j x) : Fin (Rl.nW j) → D.what₂.LL)) (v₀ j _)
  rw [e_cuspOf]
  rfl

theorem realRd_eq_phiC {ρ : GlobalTheory.SeriesTie.Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ)
    (hV : T0.V ((j : ℕ) + 1) (res T0 (sg0 D A3.A)) = Wc D j) (hev : fw.Evaluates) (a : NX.KB S i b)
    (x : NX.FmK S ((j : ℕ) + 1)) :
    GlobalTheory.SeriesTie.realRd YS v₀ hρ i j b ν
                 ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] x : NX.KB S i b ⊗[S.Ks] _)) =
      (ν⁻¹ * ρ.e i b a) • phiC T0 hV (wtA (κ j)) (cuspOf YS fw j x : T0.R ((j : ℕ) + 1)) := by
  rw [GlobalTheory.SeriesTie.realRd_tmul, evW_eq_phiC YS fw j hV hev]

def charAt (P : PlE D.host) : ℕ := ringChar (𝓞 D.host.E ⧸ P.asIdeal)

theorem charAt_mem (P : PlE D.host) : (charAt P : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem charAt_prime (P : PlE D.host) : (charAt P).Prime := by
  have := P.isPrime
  have : Finite (𝓞 D.host.E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  exact (CharP.char_is_prime_or_zero (𝓞 D.host.E ⧸ P.asIdeal) _).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 D.host.E ⧸ P.asIdeal) _)

section Side

variable {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)

def embC : T0.Q.c.F →+* ℂ_[D.ntw.l i] := iC.comp (sideK YS i b)

def placeC : HeightOneSpectrum (𝓞 T0.Q.c.F) := placeAt (embC YS iC b)

abbrev FrC (j : ℕ) : Type := FrPt (T0.Q.Xo j) T0.Q.c (PAt (embC YS iC b))

abbrev Pts (j : ℕ) : Type := PtC (T0.Q.Xo j) T0.Q.c (embC YS iC b)

def kurAt : Subfield (FractionRing (D.ntw.O i)) := (kurC (embC YS iC b)).comap iC


variable {iC b} in
def valAt (j : Fin D.R.m) (z : FrC YS iC b ((j : ℕ) + 1)) : NX.Fm S i ((j : ℕ) + 1) b →+ ℂ_[D.ntw.l i] :=
  TensorProduct.liftAddHom (R := S.Ks) (M := NX.KB S i b) (N := NX.FmK S ((j : ℕ) + 1))
    { toFun := fun a =>
        { toFun := fun x => iC a * valC z (cuspOf YS fw j x : T0.R ((j : ℕ) + 1))
          map_zero' := by rw [map_zero]; exact (congrArg _ (valC_zero z)).trans (mul_zero _)
          map_add' := fun x y => by rw [map_add (f := _), ← mul_add]; exact congrArg _ (valC_add z _ _) }
      map_zero' := by ext x; exact (congrArg (· * _) (map_zero iC)).trans (zero_mul _)
      map_add' := fun a a' => by ext x; exact (congrArg (· * _) (map_add iC a a')).trans (add_mul _ _ _) }
    fun c a x => by
      change iC ((show FractionRing (D.ntw.O i) from NX.ιK S i b c) * (show FractionRing (D.ntw.O i) from a)) * _ = iC a * valC z (cuspOf YS fw j (c • x) : T0.R _)
      rw [cuspOf_smul, Submodule.coe_smul, valC_smul, map_mul, ← sideK_eKs YS, mul_comm (iC (sideK YS i b _)), mul_assoc]
      rfl

variable {iC b}

theorem valAt_tmul (j : Fin D.R.m) (z : FrC YS iC b ((j : ℕ) + 1)) (a : NX.KB S i b) (x : NX.FmK S ((j : ℕ) + 1)) :
    valAt YS fw j z (a ⊗ₜ[S.Ks] x : NX.KB S i b ⊗[S.Ks] _) = iC a * valC z (cuspOf YS fw j x : T0.R ((j : ℕ) + 1)) := rfl

theorem valAt_smul (j : Fin D.R.m) (z : FrC YS iC b ((j : ℕ) + 1)) (a : FractionRing (D.ntw.O i))
    (x : NX.Fm S i ((j : ℕ) + 1) b) : valAt YS fw j z (a • x) = iC a * valAt YS fw j z x := by
  have key : ∀ (a : NX.KB S i b) (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)),
      valAt YS fw j z (a • x) = iC a * valAt YS fw j z x := fun a x => by
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero]; exact (map_zero _).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
    | add x y hx hy =>
      rw [smul_add]
      exact (map_add _ _ _).trans (by rw [hx, hy, ← mul_add]; exact congrArg _ (map_add _ _ _).symm)
    | tmul a' f =>
      rw [TensorProduct.smul_tmul', valAt_tmul, valAt_tmul, ← mul_assoc]
      exact congrArg (· * _) (map_mul iC a a')
  exact key a x

def wtChar (κj : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) {j : ℕ} {φ : T0.Q.c.F →+* ℂ_[D.ntw.l i]} (t : Ix (T0.Q.Dw j) → (PAt φ)ˣ) :
    ℂ_[D.ntw.l i] := toCp φ (wchar (ex (T0.Q.Dw j) κj n) t)

theorem valAt_frBor (j : Fin D.R.m) {z z' : FrC YS iC b ((j : ℕ) + 1)} {t : Ix (T0.Q.Dw ((j : ℕ) + 1)) → (PAt (embC YS iC b))ˣ}
    (h : FrBor t z z') (x : NX.Fm S i ((j : ℕ) + 1) b) :
    valAt YS fw j z' x = wtChar (wtA (κ j)) (κ j).n t * valAt YS fw j z x := by
  have hL := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp _ _ _ _ (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c).1
  have key : ∀ x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      valAt YS fw j z' x = wtChar (wtA (κ j)) (κ j).n t * valAt YS fw j z x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans ((congrArg _ (map_zero _)).trans (mul_zero _)).symm
    | add x y hx hy => exact (map_add _ _ _).trans (by rw [hx, hy, ← mul_add]; exact congrArg _ (map_add _ _ _).symm)
    | tmul a f =>
      rw [valAt_tmul, valAt_tmul, valC, hL.wt _ _ _ (cuspOf_mem_sec YS fw j f) _ t z z' (hL.test _ _) (hL.test _ _) h, map_mul,
        mul_left_comm]
      rfl
  exact key x


variable (S) in
def ratForms (j : ℕ) (b : Bool) (L : Subfield (FractionRing (D.ntw.O i))) : AddSubgroup (NX.Fm S i j b) :=
  AddSubgroup.closure {x | ∃ a ∈ L, ∃ f : NX.FmK S j, x = (show NX.KB S i b from a) ⊗ₜ[S.Ks] f}

theorem tmul_mem_ratForms {j : ℕ} {L : Subfield (FractionRing (D.ntw.O i))} {a : NX.KB S i b} (ha : a ∈ L) (f : NX.FmK S j) :
    (a ⊗ₜ[S.Ks] f : NX.KB S i b ⊗[S.Ks] _) ∈ ratForms S j b L := AddSubgroup.subset_closure ⟨a, ha, f, rfl⟩

theorem smul_mem_ratForms {j : ℕ} {L : Subfield (FractionRing (D.ntw.O i))} {a : FractionRing (D.ntw.O i)} (ha : a ∈ L)
    {x : NX.Fm S i j b} (hx : x ∈ ratForms S j b L) : a • x ∈ ratForms S j b L := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a', ha', f, rfl⟩ := hx
    exact tmul_mem_ratForms (L.mul_mem ha ha') f
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem span_ratForms (j : ℕ) (L : Subfield (FractionRing (D.ntw.O i))) :
    Submodule.span (FractionRing (D.ntw.O i)) (ratForms S j b L : Set (NX.Fm S i j b)) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have key : ∀ x : NX.KB S i b ⊗[S.Ks] NX.FmK S j,
      x ∈ Submodule.span (FractionRing (D.ntw.O i)) (ratForms S j b L : Set (NX.Fm S i j b)) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul a f =>
      have h := Submodule.smul_mem _ (show FractionRing (D.ntw.O i) from a)
        (Submodule.subset_span (R := FractionRing (D.ntw.O i)) (tmul_mem_ratForms (b := b) L.one_mem f))
      have e : (a • ((1 : NX.KB S i b) ⊗ₜ[S.Ks] f) : NX.KB S i b ⊗[S.Ks] NX.FmK S j) = a ⊗ₜ[S.Ks] f := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      exact e ▸ h
  exact key x

variable (iC b) (j : Fin D.R.m)

def urBall (B : ℝ) : Set (NX.Fm S i ((j : ℕ) + 1) b) :=
  {x | x ∈ ratForms S _ b (kurAt YS iC b) ∧ ∀ z : Pts YS iC b ((j : ℕ) + 1), ‖valAt YS fw j z.1 x‖ ≤ B}

def Detects : Prop :=
  ∀ x : NX.Fm S i ((j : ℕ) + 1) b, (∀ z : Pts YS iC b ((j : ℕ) + 1), valAt YS fw j z.1 x = 0) → x = 0

def SupDescent : Prop := NX.Bsup S i ((j : ℕ) + 1) b = Submodule.span (D.ntw.O i) (urBall YS fw iC b j 1)

def HeckeIs (k : ℕ) (P : PlE D.host) (u : ℂ_[D.ntw.l i]) : Prop :=
  ∀ (z : Pts YS iC b ((j : ℕ) + 1)) (quot : HkKer P.asIdeal (charAt P) k z.1 → FrC YS iC b ((j : ℕ) + 1)),
    (∀ C, IsHkQuot P.asIdeal (charAt P) k z.1 C (quot C)) → ∀ f : D.nexp.Fm i ((j : ℕ) + 1) b,
      valAt YS fw j z.1 (YS.eF i _ b (Nat.le_add_left _ _) j.2 (D.nexp.hkF i _ b k P f)) =
        u * ∑ᶠ C, valAt YS fw j (quot C) (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)

def HeckeGeo : Prop :=
  ∀ k P, HkIdx i k P → ∃ s : T0.Q.c.F, ‖embC YS iC b s‖ = 1 ∧ HeckeIs YS fw iC b j k P (embC YS iC b s)

def HeckeStable : Prop := ∀ k P, HkIdx i k P → ∀ (z : Pts YS iC b ((j : ℕ) + 1)) (C : HkKer P.asIdeal (charAt P) k z.1),
  ∃ z' : Pts YS iC b ((j : ℕ) + 1), IsHkQuot P.asIdeal (charAt P) k z.1 C z'.1


omit j in
def KerCard (j k : ℕ) (P : PlE D.host) (n : ℕ) : Prop :=
  ∀ (b : Bool) (z : Pts YS iC b j), Nonempty (Fin n ≃ HkKer P.asIdeal (charAt P) k z.1)

def HeckeCount : Prop := ∀ k P, HkIdx i k P → ∃ n, KerCard YS iC ((j : ℕ) + 1) k P n

end Side

end GlobalTheory.GeoTie

end
end
