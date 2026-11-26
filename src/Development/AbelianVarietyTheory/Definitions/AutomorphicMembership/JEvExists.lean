module

public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsBaseTwoWords
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsPotential

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeo

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Data

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

structure PreChar : Prop where
  lev : R.toLevCh.Is A.μ0
  red_R : R.grp_red_R
  red_L : R.grp_red_L
  record : R.grp_record
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP

def ValKs : Prop :=
  ∀ (i : Fin D.R.m) (x : (AE D)ˣ), infPart D (x : AE D) = 1 →
    ∃ y : Ks, ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = D.what₂.embLL (algebraMap Ks D.what₂.LL y)

def FrameKs (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL]
    (MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ)) : Prop :=
  (∀ i σ σ', σ.comp (algebraMap Ks D.what₂.LL) = σ'.comp (algebraMap Ks D.what₂.LL) →
    ∀ ρ, x0Mat (MW i σ) ρ = x0Mat (MW i σ') ρ) ∧
  ∀ i σ, (∀ ρ, labE σ (lab σ ρ) = tauE D ρ) →
    ∀ τ a, (MW i σ).ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)

def LevKs (F : Face D A) : Prop :=
  (∀ p, ((F.ψ0 p : D.what₂.LLˣ) : D.what₂.LL) ∈ (algebraMap Ks D.what₂.LL).range) ∧
    ∀ g, (idemOf A.X).coeff g ∈ (algebraMap Ks D.what₂.LL).range

structure MjTie (F : Face D A) where
  eW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H
  eW_range : ∀ i, LinearMap.range (eW i) = (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e
  eW_norm : ∀ i x, ‖eW i x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2
  eW_lat : ∀ (i : Fin D.R.m) x, x ∈ (D.what₂.MjLat ((i : ℕ) + 1)).carrier ↔
    ∃ y ∈ (R.FW i).MK, y ∈ (R.FW i).Wgood F.P0 F.ψ0⁻¹ (fun g => (idemOf A.X).coeff g) ∧ eW i x = (R.FW i).j (sg0 D A) y

end Data

abbrev reCore (T : CoreJ D) (dict : ∀ j σ, GA D (T.V j σ) → Σ k, Frame ((T.U j σ).X k).Ψ D.R.r)
    (mu : ∀ j σ, GA D (T.V j σ) → ℂ) (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle)
    (x₀ : ℕ → (T.Q.c.F →+* ℂ) → (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ)
    (cE : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) : CoreJ D :=
  { Q := T.Q, U := T.U, V := T.V, dict := dict, mu := mu, Kf := T.Kf, pb := T.pb, cE := cE, chiW := chiW, x₀ := x₀,
    iota := T.iota }

abbrev setCE (T : CoreJ D) (cE : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) : CoreJ D :=
  reCore T T.dict T.mu T.chiW T.x₀ cE

section Forms

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))


open Classical in
def geoRho (i : Fin D.R.m) : G →* ((Fin (nTop T κ i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (nTop T κ i) → D.what₂.LL)) :=
  if h : HasB T.Q.c.F (Cu T κ i) (nTop T κ i) ∧ ∃ ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i),
      ∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c (O i).lev2 g (f : T.R ((i : ℕ) + 1))
  then rhoB D.what₂.LL h.1.some h.2.choose else 1

def formsGeo (i : Fin D.R.m) :
    Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nTop T κ i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G :=
  { formsN T R κ v₀ i (nTop T κ i) with ρ := geoRho T R κ O i }

abbrev geoR : RealDat D A T.Q.c.F := updFW R (nTop T κ) (formsGeo T R κ v₀ O)

def Fired (ph : Fin D.R.m → ℂ) : Prop :=
  (∀ i, (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) (ph i)) ∧
  ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)

end Forms


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure GeoHalf (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (ph : Fin D.R.m → ℂ) : Type 1 where
  κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)
  v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec
  fw : FWTie T R κ v₀
  bar : BarTie fw
  O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)
  pins : ∀ i, OMPins T R κ v₀ O i
  rhoGeo : RhoGeo fw O
  equivAll : EquivAll T R κ O
  cTie : ∀ i, CTie T R κ v₀ O i
  phase : ∀ i, R.LUnif → PhaseTie T R κ v₀ O ph i

structure InGeo {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {ph : Fin D.R.m → ℂ}
    (B : GeoHalf T R ph) : Prop where
  jEvExists : JEvExists T R B.κ B.v₀
  jEvBar : JEvBar T R B.κ
  evInj : EvInj T R B.v₀
  jUnif : JUnif T R B.κ B.v₀
  geoAct : GeoAct T R B.κ B.v₀
  latFull : LatFull T B.κ
  dimMatch : DimMatch T R B.κ

end GlobalTheory.RealGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

def assemble (B : Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) : D7 where
  R := B.R
  host := B.host
  sp := B.sp
  vol := G.vol
  vol_pos := G.vol_pos
  what₂ := W.what₂
  eTau := Equiv.refl _
  hc := B.hc
  wordFin := B.wordFin
  u₀ := B.u₀
  hcW := B.hcW
  hcW_base := B.hcW_base
  hcW_v := B.hcW_v
  hcW_b := B.hcW_b
  hcW_e := B.hcW_e
  hcW_first := B.hcW_first
  hcW_last := B.hcW_last
  mem := C.mem
  nfLL := B.nfLL
  starLL := B.starLL
  tcLL := B.tcLL
  galLL := B.galLL
  starLL_cx := B.starLL_cx
  div := V.div
  div_good := V.div_good
  embE := B.embE
  embE_φ₀ := B.embE_φ₀
  conjF := B.toPre.conjF
  conjF_eq := B.toPre.conjF_eq
  embE_conj := B.embE_conj
  LL0 := B.LL0
  hostField_le_fixedField := B.hostField_le_fixedField
  O_int := B.O_int
  O_contains := B.O_contains
  plEq := Equiv.refl _
  val_eq := Formalism.BasicNotions.Examples₂.placesOf_val_eq B.LL
  ram_eq := Formalism.BasicNotions.Examples₂.placesOf_ram_eq B.LL
  conj_val := Formalism.BasicNotions.Examples₂.placesOf_conj_val B.LL
  T_level := fun u => by rw [C.A_T]; exact B.T_level u
  T_norm := fun u => by rw [C.A_T]; exact B.T_norm u
  sp_T := by rw [C.A_T]; exact B.sp_T
  cOf := B.cOf
  cOf_ne := B.cOf_ne
  cOf_eq := fun u => by rw [C.A_T, C.A_T]; exact B.cOf_eq u
  T_win := fun u => by
    simp only [ColumnsAtT.Tstar, ColumnsAtT.Xu, C.A_T, C.A_duStar, C.A_Dstar, C.A_GamP]
    exact B.T_win u
  GamP_eq := fun u => (C.A_GamP u).trans (C.A_GamP B.u₀).symm
  T_ne_pde := fun u => by rw [C.A_T]; exact B.T_ne_pde u
  Dstar_eq := C.A_Dstar
  clsLat := C.clsLat
  clsLat_lat u i c :=
    show Submodule.IsFullLattice B.host.E (C.clsLat u i c) from C.clsLat_lat u i c
  eMu := W.eMu
  eMt := W.eMt0
  perCol_base_eq_PtilCol := W.perCol_base_eq_PtilCol
  Bu_linL := W.Bu_linL
  Bu_linR := W.Bu_linR
  chTw := C.chTw
  memberColumns_twistedChain_base := C.memberColumns_twistedChain_base
  e0Tw := C.e0Tw
  PTw := C.PTw
  eMtTw := W.eMtTw
  perCol_tie := W.perCol_tie
  jEE := V.jEE
  jEE_basis := V.jEE_basis
  jN := V.jN
  jN_basis := V.jN_basis
  Dall_eq := V.Dall_eq
  delP_eq := V.delP_eq
  Dt := C.Dt
  instDt := C.instDt
  detCls := C.detCls
  muTil := C.muTil
  chiD := C.chiD
  UO := C.UO
  chiD_UO := C.chiD_UO
  e1Dt := C.e1Dt
  rest_detCharacter_on_unitary_eq := C.rest_detCharacter_on_unitary_eq
  relDet := C.relDet
  relDet_self := C.relDet_self
  relDet_mul := C.relDet_mul
  relDet_smul := C.relDet_smul
  rhoDet_eq_inv_muTilde_chiD_pow := C.rhoDet_eq_inv_muTilde_chiD_pow
  rhoDetPrime_eq_muTilde_mul_chi_pow := C.rhoDetPrime_eq_muTilde_mul_chi_pow
  dsig := S.dsig
  dsig_pos := S.dsig_pos
  s := S.s
  s_split := S.s_split
  s_HH := S.s_HH
  s_Cu := S.s_Cu
  s_PlF := S.s_PlF
  loc := N.loc
  locA := N.locA
  locT := N.locT
  nd := N.nd
  ntw := N.ntw
  naut := N.naut
  nbc := N.nbc
  nexp := N.nexp
  ntypes := N.ntypes
  nStage_trivialCharacter_compat := N.nStage_trivialCharacter_compat
  nStage_trivialCharacter_coeff_eq := N.nStage_trivialCharacter_coeff_eq
  nth := N.nth
  nbr := N.nbr
  nbr_ind := N.nbr_ind
  self_good := N.self_good
  ntwbr := N.ntwbr
  ntwbr_ind := N.ntwbr_ind
  loc_tie := N.loc_tie
  bc_tie := N.bc_tie
  rbar_tie := N.rbar_tie
  mtpar_tie := N.mtpar_tie
  Z_tie := N.Z_tie
  Zgood_tie := N.Zgood_tie
  etaJ_tie := N.etaJ_tie
  fm := C.fm
  eMu_isom := W.eMu_isom
  nuIn := V.nuIn
  nuIn_inj := V.nuIn_inj
  nuIn_range := V.nuIn_range
  nuIn_jN := V.nuIn_jN
  nuIn_norm := V.nuIn_norm
  jEE_norm := V.jEE_norm
  s_Cu_isom := S.s_Cu_isom
  sEE := S.sEE
  cd := G.cd
  jet := G.jet
  jetU := G.jetU
  jetL := G.jetL
  jetL' := G.jetL'
  jetW := G.jetW
  jetW_l := G.jetW_l
  jetTau := G.jetTau
  jetW1 := G.jetW1
  resChar_thetaJetPlaceDegOne := G.resChar_thetaJetPlaceDegOne
  jetTau1 := G.jetTau1
  jetU1 := G.jetU1
  jetL1 := G.jetL1
  jetL1' := G.jetL1'
  gx := G.gx
  gat := G.gat
  gat_d := G.gat_d
  Y_sigval := B.Y_sigval

section
variable (B : Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C)

end

structure Stages where
  B : Base
  C : Cols B
  W : RowsRest B C
  V : DivStage B C W
  S : SStage B C W
  N : NStage B C W
  G : GJStage B C

def Stages.toD7 (X : Stages) : D7 := assemble X.B X.C X.W X.V X.S X.N X.G

end GlobalTheory.Mem

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
noncomputable section
namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem NumberField IsDedekindDomain

def ShaOK (B : Pre) (s : ℕ → ℕ → ℚ) : Prop :=
  ∃ ldat : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData B.host.E (AlgebraicClosure B.host.E) p,
    ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < B.R.t → ∀ n : ℕ,
      Formalism.GaloisCohomology.shaLen (ldat p) (e : ℤ) = (n : ℕ∞) → s p e = (n : ℚ)

abbrev Chi (B : Pre) : Type := ∀ k : Fin 2, Fin B.R.f → Fin B.R.m → (ZMod (B.host.g k))ˣ

structure IsSer (r g N : ℕ) (e : Polynomial (ZMod g) → MonoidAlgebra ℂ (GL (Fin r) (ZMod g))) : Prop where
  idem : ∀ f, e f * e f = e f
  central : ∀ f a, e f * a = a * e f
  orth : ∀ f f', f ≠ f' → e f * e f' = 0
  zero : ∀ f, e f = 0 ↔ ¬ (f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0)
  sum : ∃ S : Finset (Polynomial (ZMod g)),
    (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0) ∧ ∑ f ∈ S, e f = 1
  rat : ∀ f x, (e f).coeff x ∈
    IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))}

end GlobalTheory.MemN
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSStageUnconditional
noncomputable section

namespace GlobalTheory.Mem.SpectralModel

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Loc NumberField IsDedekindDomain

def CodeWords (B : Pre) : Prop :=
  ∃ (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool), 0 < Del ∧ Function.Injective letter ∧
    (∀ (w : B.Word) (τ : Tau B.R) (l : ℕ) (h : l + 1 < B.R.k - 1),
      (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) ∧
    ∀ (w : B.Word) (τ : Tau B.R) (l : ℕ) (h : l < B.R.k - 2),
      (B.hcW w τ).u ⟨l + 1, by omega⟩ =
        (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)

def ColsPos {B : Base} (C : Cols B) : Prop :=
  ∀ u, (∀ x ∈ (C.mem u).A.Mu0, ∀ y ∈ (C.mem u).A.Mu0,
      starRingEnd ℂ ((C.fm u).ipC 0 y x) = (C.fm u).ipC 0 x y) ∧
    ∀ x ∈ (C.mem u).A.Mu0, x ≠ 0 → 0 < ((C.fm u).ipC 0 x x).re

theorem conjF_ne (B : Pre) : B.conjF ≠ AlgHom.id B.host.F B.host.E := by
  letI := B.host.cmStar
  intro h
  have hs : Function.Surjective (algebraMap B.host.F B.host.E) := fun a =>
    (B.sp.cm.fixed a).1 (AlgHom.congr_fun h a)
  have h2 := B.sp.cm.deg2
  have h1 : Module.finrank B.host.F B.host.E = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap B.host.F B.host.E)
      ⟨(algebraMap B.host.F B.host.E).injective, hs⟩).finrank_eq, Module.finrank_self]
  omega

theorem ncard_primesOver (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)).ncard = (placesOver E p).ncard := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  have hne : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [← Set.ncard_image_of_injective (placesOver E p) (f := fun v => v.asIdeal)
    (fun _ _ h => HeightOneSpectrum.ext h)]
  congr 1
  ext P
  constructor
  · rintro ⟨hP, hl⟩
    refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hne P⟩, ?_, rfl⟩
    have := (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).1 (Ideal.mem_span_singleton_self _)
    simpa [placesOver] using this
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨hmax.eq_of_le ?_ ?_⟩⟩
    · exact Ideal.comap_ne_top _ v.isPrime.ne_top
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      simpa [placesOver] using hv

theorem exists_atP (B : Pre) (p : HeightOneSpectrum (𝓞 B.host.F)) :
    ∃ L : LocAt B.host.F B.host.E B.conjF p,
      (L.split.isSome ↔ resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)) := by
  letI := B.host.cmStar
  obtain ⟨L, hL⟩ := GlobalTheory.LocalData.exists_locAt B.host.F B.host.E B.conjF B.sp.cm.deg2 p
  by_cases h : resChar p ∈ ({B.host.g 0, B.host.g 1} : Finset ℕ)
  · have hk : ∃ k, resChar p = B.host.g k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> exact ⟨_, h⟩
    obtain ⟨k, hk⟩ := hk
    obtain ⟨S⟩ := GlobalTheory.LocSplit.nonempty_splitAt B.host.F B.host.E B.conjF B.sp.cm.deg2 (conjF_ne B) p L
      (by rw [hk, ncard_primesOver _ _ (B.host.g_prime k), B.g_split])
    exact ⟨{ L with split := some S }, by simpa using h⟩
  · exact ⟨L, by simp [hL, h]⟩

def ColSp {B : Base} (C : Cols B) (u : B.Word) : Type := (C.mem u).A.Mu0

instance {B : Base} (C : Cols B) (u : B.Word) : AddCommGroup (ColSp C u) :=
  inferInstanceAs (AddCommGroup (C.mem u).A.Mu0)
instance {B : Base} (C : Cols B) (u : B.Word) : Module ℂ (ColSp C u) :=
  inferInstanceAs (Module ℂ (C.mem u).A.Mu0)
instance {B : Base} (C : Cols B) (u : B.Word) : FiniteDimensional ℂ (ColSp C u) := (C.mem u).A.Mu0_fd

def colEq {B : Base} (C : Cols B) (u : B.Word) : ColSp C u ≃ₗ[ℂ] (C.mem u).A.Mu0 := LinearEquiv.refl ℂ _

@[reducible] def core {B : Base} (C : Cols B) (h : ColsPos C) (u : B.Word) : InnerProductSpace.Core ℂ (ColSp C u) where
  inner x y := (C.fm u).ipC 0 (colEq C u x).1 (colEq C u y).1
  conj_inner_symm x y := (h u).1 _ (colEq C u x).2 _ (colEq C u y).2
  re_inner_nonneg x := by
    by_cases hx : (colEq C u x).1 = 0
    · simp [hx, MemberForms.ipC]
    · exact ((h u).2 _ (colEq C u x).2 hx).le
  add_left x y z := by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib]
  smul_left x y r := by
    simp only [MemberForms.ipC, map_smul, Submodule.coe_smul, Pi.smul_apply, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  definite x hx := by
    by_contra h0
    have h1 : (colEq C u x).1 ≠ 0 := fun h1 => h0 ((colEq C u).injective (Subtype.ext (by simpa using h1)))
    have := (h u).2 _ (colEq C u x).2 h1
    rw [show (C.fm u).ipC 0 (colEq C u x).1 (colEq C u x).1 = 0 from hx] at this
    simp at this

theorem exists_conjIsom (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] {a b : ℕ}
    (onb : OrthonormalBasis (Fin a) ℂ V) (hab : a ≤ b) : Nonempty (V →ₗᵢ⋆[ℂ] EuclideanSpace ℂ (Fin b)) := by
  classical
  let e : EuclideanSpace ℂ (Fin a) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin b) :=
    LinearMap.isometryOfOrthonormal
      ((EuclideanSpace.basisFun (Fin a) ℂ).toBasis.constr ℂ
        (fun i => EuclideanSpace.basisFun (Fin b) ℂ (Fin.castLE hab i)))
      (v := (EuclideanSpace.basisFun (Fin a) ℂ).toBasis) (EuclideanSpace.basisFun (Fin a) ℂ).orthonormal
      (by
        have := (EuclideanSpace.basisFun (Fin b) ℂ).orthonormal.comp _ (Fin.castLE_injective hab)
        have he : ⇑((EuclideanSpace.basisFun (Fin a) ℂ).toBasis.constr ℂ
            (fun i => EuclideanSpace.basisFun (Fin b) ℂ (Fin.castLE hab i))) ∘
            ⇑(EuclideanSpace.basisFun (Fin a) ℂ).toBasis =
            ⇑(EuclideanSpace.basisFun (Fin b) ℂ) ∘ Fin.castLE hab := by
          funext i
          simp only [Function.comp, Module.Basis.constr_basis]
        rw [he]; exact this)
  let c : EuclideanSpace ℂ (Fin a) →ₗᵢ⋆[ℂ] EuclideanSpace ℂ (Fin a) :=
    { toFun := fun x => WithLp.toLp 2 (fun i => star (x i))
      map_add' := fun x y => by ext i; simp
      map_smul' := fun r x => by ext i; simp
      norm_map' := fun x => by simp [EuclideanSpace.norm_eq] }
  exact ⟨(e.comp c).comp onb.repr.toLinearIsometry⟩

theorem exists_sStage {B : Base} {C : Cols B} (W : RowsRest B C) (h1 : CodeWords B.toPre) (h2 : ColsPos C)
    (h3 : W.Drows ≤ W.Dall) (d : Tau B.R → ℝ) (hd : ∀ ρ, 0 < d ρ)
    (P : ∀ u, (C.mem u).A.Mu0 →ₗ[ℂ] EuclideanSpace ℂ (Fin W.Dall)) :
    ∃ S : SStage B C W, S.dsig = d ∧ (∀ u u', Nonempty (S.s.Term u u')) ∧
      ∃ e : S.s.HH ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin W.Dall), ∀ u x, e (S.s.Pu u x) = P u (S.s_Cu u x) := by
  obtain ⟨Del, letter, hD, hl, hg, hu⟩ := h1
  choose L hL using exists_atP B.toPre
  obtain ⟨j⟩ := exists_conjIsom W.EE W.onb h3
  letI nN : ∀ u, NormedAddCommGroup (ColSp C u) := fun u => (core C h2 u).toNormedAddCommGroup
  letI nI : ∀ u, InnerProductSpace ℂ (ColSp C u) := fun u => InnerProductSpace.ofCore (core C h2 u).toCore
  refine ⟨{
    dsig := d
    dsig_pos := hd
    s := {
      cdScale := fun _ _ => 1
      cdScale_pos := fun _ _ => one_pos
      Del := Del
      Del_pos := hD
      cloud_gap := hg
      letter := letter
      letter_inj := hl
      u_letter := hu
      HH := EuclideanSpace ℂ (Fin W.Dall)
      Cu := ColSp C
      cuN := nN
      cuI := nI
      cuF := fun u => (C.mem u).A.Mu0_fd
      Pu := fun u => LinearMap.toContinuousLinearMap (P u ∘ₗ (colEq C u).toLinearMap)
      volN := fun _ => 1
      volH := fun _ => 1
      volN_pos := fun _ => one_pos
      volH_pos := fun _ => one_pos
      Term := fun _ _ => Unit
      aTerm := fun _ _ _ => 0
      isId := fun _ => True
      inS := fun _ => True
      relevant := fun _ => True
      FeqF := fun _ => True
      Gterm := fun _ => 0
      atP := L
      PlF := HeightOneSpectrum (𝓞 B.host.F)
      BBne := fun _ _ => False
      generic := fun _ => False
      Pair := fun _ _ => Unit
      pfst := id
      psnd := id
      s0 := fun _ => 0
      scalarPair := fun _ => False
      pval := fun _ => 0
      ptOf := fun _ => ⟨[(1, B.R.rS + 1)], by simp, by simp⟩
      cTerm := fun _ => 1
      massPair := fun _ => 1
      meanCount := fun _ _ _ => 0 }
    s_split := hL
    s_HH := by simp
    s_Cu := colEq C
    s_PlF := Equiv.refl _
    s_Cu_isom := fun _ _ _ => rfl
    sEE := j }, rfl, fun _ _ => ⟨()⟩, LinearIsometryEquiv.refl ℂ _, fun _ _ => rfl⟩

theorem colsPos_of {B : Base} {C : Cols B} {W : RowsRest B C} (S : SStage B C W) : ColsPos C := by
  intro u
  refine ⟨fun x hx y hy => ?_, fun x hx h0 => ?_⟩
  · have a := S.s_Cu_isom u ((S.s_Cu u).symm ⟨x, hx⟩) ((S.s_Cu u).symm ⟨y, hy⟩)
    have b := S.s_Cu_isom u ((S.s_Cu u).symm ⟨y, hy⟩) ((S.s_Cu u).symm ⟨x, hx⟩)
    simp only [LinearEquiv.apply_symm_apply] at a b
    rw [← a, ← b, inner_conj_symm]
  · have a := S.s_Cu_isom u ((S.s_Cu u).symm ⟨x, hx⟩) ((S.s_Cu u).symm ⟨x, hx⟩)
    simp only [LinearEquiv.apply_symm_apply] at a
    rw [← a]
    refine re_inner_self_pos (𝕜 := ℂ) |>.2 ?_
    intro h
    exact h0 (congrArg Subtype.val ((S.s_Cu u).symm.map_eq_zero_iff.1 h))

theorem rows_le_of {B : Base} {C : Cols B} {W : RowsRest B C} (S : SStage B C W) : W.Drows ≤ W.Dall := by
  have hli : Orthonormal ℂ (fun i => S.sEE (W.onb i)) := by
    refine ⟨fun i => by rw [S.sEE.norm_map]; exact W.onb.orthonormal.1 i, fun i k hik => ?_⟩
    have h0 : inner ℂ (W.onb i) (W.onb k) = 0 := W.onb.orthonormal.2 hik
    have key : ∀ z : ℂ, ‖S.sEE (W.onb i) + starRingEnd ℂ z • S.sEE (W.onb k)‖ = ‖W.onb i + z • W.onb k‖ := fun z => by
      rw [← S.sEE.norm_map, map_add (f := _), map_smulₛₗ]
    have k1 := congrArg (· ^ 2) (key 1)
    have k2 := congrArg (· ^ 2) (key Complex.I)
    simp only [@norm_add_sq ℂ, inner_smul_right, h0, norm_smul, S.sEE.norm_map] at k1 k2
    simp at k1 k2
    exact Complex.ext k1 k2
  have := hli.linearIndependent.fintype_card_le_finrank
  rwa [Fintype.card_fin, S.s_HH] at this

end GlobalTheory.Mem.SpectralModel

end
end
