module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OrZeroOf
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}

def levCh (L : Formalism.IndefR.Links.LevCh D T) (f : T' → T) : Formalism.IndefR.Links.LevCh D T' where
  C := L.C
  xiH t := L.xiH (f t)
  mu0 := L.mu0
  eta := L.eta
  xi t := L.xi (f t)
  Pg := L.Pg
  Q t := L.Q (f t)
  chi := L.chi
  xiR t := L.xiR (f t)
  ΛY := L.ΛY
  ΛX := L.ΛX
  ΛV := L.ΛV
  ΛW := L.ΛW
  βY := L.βY
  βX := L.βX
  βV := L.βV
  βW := L.βW

theorem levCh_is {L : Formalism.IndefR.Links.LevCh D T} {f : T' → T} (hf : Function.Injective f) {μ : T'} (h : L.Is (f μ)) :
    (levCh L f).Is μ := by
  exact {
    mu0 := h.mu0
    eta := h.eta
    xi := fun t => h.xi (f t)
    xi_inj := h.xi_inj.comp hf
    xi_base := h.xi_base
    xi_fin := fun t => h.xi_fin (f t)
    xi_triv := fun t => h.xi_triv (f t)
    xi_tame := fun t => h.xi_tame (f t)
    Pg := h.Pg
    Q_pl := fun t => h.Q_pl (f t)
    Q_off := fun t => h.Q_off (f t)
    Q_de := fun p hp => (h.Q_de p hp).imp fun _ h' t => h' (f t)
    Q_ram := fun t => h.Q_ram (f t)
    chi := h.chi
    xiR := fun t => h.xiR (f t)
    βY := h.βY
    βX := h.βX
    βV := h.βV
    βW := h.βW
  }

section Two

variable {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (f : T' → T) (μ : T')


set_option maxHeartbeats 2000000 in
def dat2 (R : RealDat D (A.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : RealDat D (A.comap f μ) Ks where
  toLevCh := levCh R.toLevCh f
  hv0 := R.hv0
  eG := R.eG
  pl := R.pl
  Sb := R.Sb
  θ := R.θ
  ψ := R.ψ
  MY := R.MY
  MX := R.MX
  MW := R.MW
  cX := R.cX
  cV := R.cV
  B := ⟨fun t => R.B.R (f t), fun i t => R.B.L i (f t), R.B.rankR, R.B.rankL⟩
  prX := R.prX
  HX t := R.HX (f t)
  HV i t := R.HV i (f t)
  HE := R.HE
  HW := R.HW
  gE := R.gE
  gW := R.gW
  jX t := R.jX (f t)
  jV i t := R.jV i (f t)
  νY t := R.νY (f t)
  fdY t := R.fdY (f t)
  ν0 := R.ν0
  fd0 := R.fd0
  νX t := R.νX (f t)
  fdX t := R.fdX (f t)
  νV i t := R.νV i (f t)
  fdV i t := R.fdV i (f t)
  νW := R.νW
  fdW := R.fdW
  ωY t := R.ωY (f t)
  ωX t := R.ωX (f t)
  ωP i t := R.ωP i (f t)
  vac := R.vac
  vacX := R.vacX
  vacP := R.vacP
  vY t := R.vY (f t)
  vX t := R.vX (f t)
  vP i t := R.vP i (f t)
  ItY := R.ItY
  ItX := R.ItX
  ioY t := R.ioY (f t)
  ioX t := R.ioX (f t)
  Th t := R.Th (f t)
  BV := R.BV
  ioP := R.ioP
  thF i t := R.thF i (f t)
  thG i t := R.thG i (f t)
  nW := R.nW
  FW := R.FW
  mu := mu
  twPl := tw
  kap := R.kap
  lam i t := R.lam i (f t)
  err0 := R.err0

def bare2 (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ) :
    Face D A where
  P0 := P0
  ψ0 := ψ0
  P1 := P1
  ψ1 := ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

variable {f μ} {R : RealDat D (A.comap id (f μ)) Ks} (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
  (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}


set_option maxHeartbeats 2000000 in
theorem isGrp (h : R.IsGrp (bare2 _ P0 ψ0 P1 ψ1)) : (dat2 f μ R mu tw).IsGrp (bare2 _ P0 ψ0 P1 ψ1) :=
  ⟨fun t => h.red_R (f t), fun i t => h.red_L i (f t), h.levels, h.record, h.chiW⟩


set_option maxHeartbeats 2000000 in
theorem isFam (h : R.IsFam) : (dat2 f μ R mu tw).IsFam := by
  obtain ⟨g, c, l, ht⟩ := h.tie
  exact ⟨⟨g, c, l, ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, fun t => ht.ok (f t), ht.gramR_eq, ht.mapR, ht.mapL,
    fun t => ht.coefR (f t), fun i t => ht.coefL i (f t)⟩, h.Sb, fun t => h.roots (f t), h.pl_onto, fun t => h.degR (f t),
    fun i t => h.degL i (f t), fun i t => h.muVal i (f t), h.etaVal⟩


set_option maxHeartbeats 2000000 in
theorem isModels (h : R.IsModels) : (dat2 f μ R mu tw).IsModels :=
  ⟨h.inf, h.vpos, h.cX, h.cV, h.prX, fun t => h.HX (f t), fun i t => h.HV i (f t), h.HE, h.HW, h.gE, h.gW, fun t => h.jX (f t),
    fun i t => h.jV i (f t), fun t => h.νY (f t), fun t => h.νY' (f t), h.ν0, fun t => h.νX (f t), fun i t => h.νV i (f t),
    h.νW, h.BV, h.order⟩


set_option maxHeartbeats 2000000 in
theorem exAt (e : R.ExAt) : (dat2 f μ R mu tw).ExAt :=
  ⟨fun k hk => (e.ItY k hk).imp fun _ h t => h (f t), e.ItX.imp fun _ h t => h (f t), fun t => e.ioY (f t), fun t => e.ioX (f t),
    fun t => e.Th (f t), fun i => (e.ioP i).imp fun _ h t => h (f t), fun i t => e.thF i (f t), fun i t => e.thG i (f t)⟩

theorem orZero_of {X : Type} [Zero X] {p : X → Prop} {x : X} (h : p x) : OrZero p x :=
  ⟨fun _ => h, fun hn => absurd ⟨x, h⟩ hn⟩


set_option maxHeartbeats 2000000 in
theorem isChainW (h : R.IsChainW) (e : R.ExAt) : (dat2 f μ R mu tw).IsChainW :=
  ⟨fun t => h.ωY (f t), fun t => h.ωX (f t), fun t => h.vY (f t), fun t => h.vX (f t), fun t => h.ptY (f t), fun t => h.ptX (f t),
    fun k hk => orZero_of fun t => (h.ItY k hk).1 (e.ItY k hk) (f t), orZero_of fun t => h.ItX.1 e.ItX (f t),
    fun t => h.ioY (f t), fun t => h.ioX (f t), fun t => h.Th (f t)⟩


set_option maxHeartbeats 2000000 in
theorem isThPW (h : R.IsThPW) (e : R.ExAt) : (dat2 f μ R mu tw).IsThPW :=
  ⟨fun i t => h.ωP i (f t), fun i t => h.vP i (f t), fun i t => h.pt_theta i (f t),
    fun i => orZero_of fun t => (h.ioP i).1 (e.ioP i) (f t), fun i t => h.thF i (f t), fun i t => h.thG i (f t)⟩

theorem baseW (hf : Function.Injective f) (h : R.BaseW (bare2 _ P0 ψ0 P1 ψ1)) (e : R.ExAt) :
    (dat2 f μ R mu tw).BaseW (bare2 _ P0 ψ0 P1 ψ1) :=
  ⟨levCh_is hf h.lev, isGrp mu tw h.grp, isFam mu tw h.fam, isModels mu tw h.models, isChainW mu tw h.chain e, isThPW mu tw h.thP e⟩

end Two

end GlobalTheory.Mem.R3.Res

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RestrictedCharacterDataValid
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (f : T' → T) (μ : T')

def dat3 (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : RealDat3 D (A3.comap f μ) Ks where
  toRealDat := dat2 (A := A3.A) f μ R.toRealDat mu tw
  plI := R.plI
  SF := R.SF
  phs := R.phs
  lam3 i t := R.lam3 i (f t)

def bare3 (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* D.what₂.LLˣ) : Face3 D A3 where
  P0 := P0
  ψ0 := ψ0
  P1 := P1
  ψ1 := ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

variable {f μ} {R : RealDat3 D (A3.comap id (f μ)) Ks} (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
  (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}


set_option maxHeartbeats 2000000 in
theorem isInert (h : R.IsInert) : (dat3 f μ R mu tw).IsInert := by
  exact ⟨⟨h.tie.plI_inj, fun t Q => h.tie.okI (f t) Q⟩, h.onto, fun t => h.hR (f t), fun i t => h.hL i (f t), h.SF⟩



structure NewTup (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : Prop where

  sub : tw ⊆ R.twPl

  conj : ∀ w, Formalism.DivisionValues.conjPl w ∈ tw ↔ w ∈ tw

  on : ∀ w ∈ tw, f (mu w) = R.mu w

  off : ∀ w, w ∉ tw → mu w = μ

  used : ∀ t, t = μ ∨ ∃ w, mu w = t


variable {mu tw} in
theorem isTup (hf : Function.Injective f) (h : R.IsTup) (n : NewTup R mu tw) : (dat3 f μ R mu tw).IsTup := by
  constructor
  case mu_off => exact n.off
  case mu_used => exact n.used
  case mu_ne =>
    intro w hw heq
    change mu w = μ at heq
    apply h.mu_ne w (n.sub hw)
    rw [← n.on w hw, heq]
    rfl
  case mu_conj =>
    intro w
    change mu (Formalism.DivisionValues.conjPl w) = mu w
    by_cases hw : w ∈ tw
    · apply hf
      have hc : Formalism.DivisionValues.conjPl w ∈ tw := (n.conj w).2 hw
      rw [n.on _ hc, n.on w hw]
      exact h.mu_conj w
    · have hc : Formalism.DivisionValues.conjPl w ∉ tw := fun hc => hw ((n.conj w).1 hc)
      rw [n.off _ hc, n.off w hw]
  case mu_on =>
    intro w hw
    obtain ⟨ψw, Qw, h1, h2⟩ := h.mu_on w (n.sub hw)
    refine ⟨ψw, Qw, h1, ?_⟩
    change R.xiH (f (mu w)) = R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψw
    rw [n.on w hw]
    exact h2



set_option maxHeartbeats 2000000 in
theorem keep {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Keep (A3 := A3.comap id (f μ)) R.toRealDat (bare3 _ P0 ψ0 P1 ψ1).lv2 cG) :
    Keep (A3 := A3.comap f μ) (dat3 f μ R mu tw).toRealDat (bare3 _ P0 ψ0 P1 ψ1).lv2 cG := by
  constructor
  case std => exact h.std
  case signs => exact h.signs
  case frames => exact h.frames
  case beta => exact h.beta
  case prX => exact h.prX
  case grp => exact h.grp
  case psi => exact h.psi
  case guard => exact ⟨fun t => h.guard.1 (f t), fun t => h.guard.2 (f t)⟩
  case valKs => exact h.valKs
  case frameKs => exact h.frameKs
  case levKs => exact h.levKs


end GlobalTheory.Mem.R3.Res

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InGeoIff
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.FWT Formalism.L2.Pj

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T T' : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {f : T' → T} {μ : T'}
  {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D (A.comap id (f μ)) C.Q.c.F}
  (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T') (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL)))


set_option maxHeartbeats 1600000 in
def omDat {i : Fin D.R.m} (O : OMDat C.toCore R i Unit fun _ => (A.comap id (f μ)).μ0) :
    OMDat C.toCore (dat2 f μ R mu tw) i Unit fun _ => (A.comap f μ).μ0 := { O with }


set_option maxHeartbeats 1600000 in
def fwTie {κ v₀} (t : FWTie C R κ v₀) : FWTie C (dat2 f μ R mu tw) κ v₀ :=
  { alg_eq := t.alg_eq, e := t.e, ks := t.ks, kap := t.kap, pt := t.pt, nrm_eq := t.nrm_eq, laws := t.laws, chiR := t.chiR,
    hv₀ := t.hv₀, x0 := t.x0, ev0 := t.ev0, ev := t.ev }


set_option maxHeartbeats 1600000 in
theorem omPins {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (O : ∀ i, OMDat C.toCore R i Unit fun _ => (A.comap id (f μ)).μ0) (i : Fin D.R.m) (h : OMPins C R κ v₀ O i) :
    OMPins C (dat2 f μ R mu tw) κ v₀ (fun i => omDat mu tw (O i)) i := by
  refine ⟨h.1, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h.2
  obtain ⟨g, c, l, ht, hb⟩ := h1.c0
  refine ⟨⟨h1.field, h1.std, ?_, ⟨g, c, l, ⟨ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, fun t => ht.ok (f t), ht.gramR_eq,
    ht.mapR, ht.mapL, fun t => ht.coefR (f t), fun i t => ht.coefL i (f t)⟩, hb⟩, h1.lev⟩, fun t => ⟨(h2 t).reps, (h2 t).B, (h2 t).xi, (h2 t).phi, (h2 t).half⟩,
    h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  exact h1.v0


set_option maxHeartbeats 1600000 in
def geoHalf {ph : Fin D.R.m → ℂ} (g : GlobalTheory.RealGeo.GeoHalf C R ph) : GlobalTheory.RealGeo.GeoHalf C (dat2 f μ R mu tw) ph :=
  ⟨g.κ, g.v₀, fwTie mu tw g.fw, g.bar, fun i => omDat mu tw (g.O i), fun i => omPins mu tw g.O i (g.pins i), g.rhoGeo, g.equivAll,
    g.cTie, g.phase⟩


set_option maxHeartbeats 1600000 in
theorem inGeo {ph : Fin D.R.m → ℂ} {g : GlobalTheory.RealGeo.GeoHalf C R ph} (h : GlobalTheory.RealGeo.InGeo g) :
    GlobalTheory.RealGeo.InGeo (geoHalf mu tw g) :=
  ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩


set_option maxHeartbeats 1600000 in
theorem inGeo_iff {ph : Fin D.R.m → ℂ} {g : GlobalTheory.RealGeo.GeoHalf C R ph} :
    GlobalTheory.RealGeo.InGeo (geoHalf mu tw g) ↔ GlobalTheory.RealGeo.InGeo g :=
  ⟨fun h => ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩, inGeo mu tw⟩

end GlobalTheory.Mem.R3.Res

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InclUInjective
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}

def plB (X : Stages) : X.B.places.Pl ≃ HeightOneSpectrum (𝓞 X.toD7.what₂.LL) := X.toD7.plEq

theorem plB_conj (w : X.B.places.Pl) : plB X (X.B.places.conj w) = Formalism.DivisionValues.conjPl (plB X w) := by
  have hc := plConjEq X.toD7
  exact hc w

def ConjStable (X : Stages) (Wt : Set X.B.places.Pl) : Prop := ∀ w ∈ Wt, X.B.places.conj w ∈ Wt

theorem ConjStable.symm_mem_iff {Wt : Set X.B.places.Pl} (h : ConjStable X Wt) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    (plB X).symm (Formalism.DivisionValues.conjPl v) ∈ Wt ↔ (plB X).symm v ∈ Wt := by
  constructor
  · intro hv
    have e : X.B.places.conj ((plB X).symm (Formalism.DivisionValues.conjPl v)) = (plB X).symm v := by
      apply (plB X).injective
      rw [plB_conj, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
    rw [← e]
    exact h _ hv
  · intro hv
    have e : X.B.places.conj ((plB X).symm v) = (plB X).symm (Formalism.DivisionValues.conjPl v) := by
      apply (plB X).injective
      rw [plB_conj, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [← e]
    exact h _ hv

theorem tuOf_mono (I : ColIn X.B px) {U U' : Set I.ι} (h : U' ⊆ U) : tuOf I U' ⊆ tuOf I U := by
  intro τ hτ
  obtain ⟨a, ha, rfl⟩ := (mem_tuOf I).1 hτ
  exact (mem_tuOf I).2 ⟨a, h ha, rfl⟩

def inclU (I : ColIn X.B px) {U U' : Set I.ι} (h : U' ⊆ U) : TupU I U' → TupU I U := TupF.incl (tuOf_mono I h)

theorem inclU_injective {U U' : Set I.ι} (h : U' ⊆ U) : Function.Injective (inclU I h) := by
  intro s t hst
  have hv : (inclU I h s).1 = (inclU I h t).1 := congrArg Subtype.val hst
  exact Subtype.ext hv

theorem ixOf_inclU {U U' : Set I.ι} (h : U' ⊆ U) (t : TupU I U') : ixOf I U (inclU I h t) = ixOf I U' t := rfl

variable {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

theorem plB_mem_twPl (w : X.B.places.Pl) : plB X w ∈ z.R.twPl ↔ w ∈ Wt := by
  exact (z.mu w).1

theorem xi_mu {w : X.B.places.Pl} (hw : w ∈ Wt) : I.xi (ixOf I (usedOf I T Wt) (z.R.mu (plB X w))) = T.xiTw I.C w := by
  have hm := (z.mu w).2
  rw [if_pos hw] at hm
  exact hm

theorem mu_mem (h : Wt' ⊆ Wt) {v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)} (hv : (plB X).symm v ∈ Wt') :
    (z.R.mu v).1 ∈ tuOf I (usedOf I T Wt') := by
  have hx := z.xi_mu (h hv)
  rw [Equiv.apply_symm_apply] at hx
  have hu : ixOf I (usedOf I T Wt) (z.R.mu v) ∈ usedOf I T Wt' := ⟨(plB X).symm v, hv, hx⟩
  have hm := (tup_mem_tuOf I).2 hu
  rwa [tup_ixOf] at hm


open Classical in
def resMu (h : Wt' ⊆ Wt) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) : TupU I (usedOf I T Wt') :=
  if hv : (plB X).symm v ∈ Wt' then ⟨(z.R.mu v).1, Or.inr (z.mu_mem h hv)⟩ else mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))


open Classical in
def resTw (Wt' : Set X.B.places.Pl) : Finset (HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :=
  z.R.twPl.filter fun v => (plB X).symm v ∈ Wt'

theorem mem_twPl (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) : v ∈ z.R.twPl ↔ (plB X).symm v ∈ Wt := by
  have hm := z.plB_mem_twPl ((plB X).symm v)
  rwa [Equiv.apply_symm_apply] at hm

theorem mem_resTw (h : Wt' ⊆ Wt) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) : v ∈ z.resTw Wt' ↔ (plB X).symm v ∈ Wt' := by
  classical
  unfold resTw
  rw [Finset.mem_filter, z.mem_twPl]
  exact ⟨fun hv => hv.2, fun hv => ⟨h hv, hv⟩⟩

theorem inclU_resMu (h : Wt' ⊆ Wt) {v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)} (hv : (plB X).symm v ∈ Wt') :
    inclU I (usedOf_mono I T h) (z.resMu h v) = z.R.mu v := by
  have e : z.resMu h v = ⟨(z.R.mu v).1, Or.inr (z.mu_mem h hv)⟩ := dif_pos hv
  rw [e]
  rfl

theorem resMu_off (h : Wt' ⊆ Wt) {v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)} (hv : (plB X).symm v ∉ Wt') :
    z.resMu h v = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt')) := by
  exact dif_neg hv

theorem resMu_used (h : Wt' ⊆ Wt) (t : TupU I (usedOf I T Wt')) :
    t = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt')) ∨ ∃ v, z.resMu h v = t := by
  obtain ⟨τ, hτ | hτ⟩ := t
  · left
    exact Subtype.ext hτ
  · right
    obtain ⟨a, ha, rfl⟩ := (mem_tuOf I).1 hτ
    obtain ⟨w, hw, hxa⟩ := ha
    refine ⟨plB X w, ?_⟩
    have hw' : (plB X).symm (plB X w) ∈ Wt' := by
      rw [Equiv.symm_apply_apply]
      exact hw

    have hau : a ∈ usedOf I T Wt := usedOf_mono I T h ⟨w, hw, hxa⟩
    obtain ⟨ta, hta⟩ : ∃ ta : TupU I (usedOf I T Wt), ta.1 = I.tup a :=
      ⟨⟨I.tup a, Or.inr ((tup_mem_tuOf I).2 hau)⟩, rfl⟩
    have hix : ixOf I (usedOf I T Wt) ta = a := ixOf_eq I hta.symm
    have hs := z.xi_mu (h hw)
    have hxi : z.R.toLevCh.xiH ta = z.R.toLevCh.xiH (z.R.mu (plB X w)) := by
      rw [z.lev.xiH, z.lev.xiH, hix, hs, hxa]

    have he := z.lev.is.xi_inj hxi
    have e : z.resMu h (plB X w) = ⟨(z.R.mu (plB X w)).1, Or.inr (z.mu_mem h hw')⟩ := dif_pos hw'
    rw [e]
    apply Subtype.ext
    show (z.R.mu (plB X w)).1 = I.tup a
    rw [← he]
    exact hta

theorem muOf_res (h : Wt' ⊆ Wt) : MuOf X I T Wt' (z.resMu h) (z.resTw Wt') := by
  intro w
  have hpl : (plB X).symm (X.toD7.plEq w) = w := (plB X).symm_apply_apply w
  refine ⟨?_, ?_⟩
  · rw [z.mem_resTw h, hpl]
  · by_cases hw : w ∈ Wt'
    · rw [if_pos hw]
      have hw' : (plB X).symm (X.toD7.plEq w) ∈ Wt' := by
        rw [hpl]
        exact hw
      rw [← ixOf_inclU (usedOf_mono I T h), z.inclU_resMu h hw']
      exact z.xi_mu (h hw)
    · rw [if_neg hw]
      have hw' : (plB X).symm (X.toD7.plEq w) ∉ Wt' := by
        rw [hpl]
        exact hw
      rw [z.resMu_off h hw', ixOf_mu0F]

      have hb := z.lev.is.xi_base
      rw [z.lev.xiH, ixOf_mu0F] at hb
      exact hb


set_option maxHeartbeats 1000000 in
def resR (h : Wt' ⊆ Wt) : RealDat3 X.toD7 (famR X I hX (usedOf I T Wt') z.Xg z.tr) z.core.Q.c.F :=
  Res.dat3 (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (inclU I (usedOf_mono I T h))
    (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) z.R (z.resMu h) (z.resTw Wt')


set_option maxHeartbeats 1000000 in
theorem newTup (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') :
    Res.NewTup (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (f := inclU I (usedOf_mono I T h))
      (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) z.R (z.resMu h) (z.resTw Wt') := by
  constructor
  case sub =>
    intro v hv
    exact (z.mem_twPl v).2 (h ((z.mem_resTw h v).1 hv))
  case conj =>
    intro v
    rw [z.mem_resTw h, z.mem_resTw h]
    exact hc.symm_mem_iff v
  case on =>
    intro v hv
    exact z.inclU_resMu h ((z.mem_resTw h v).1 hv)
  case off =>
    intro v hv
    exact z.resMu_off h fun hv' => hv ((z.mem_resTw h v).2 hv')
  case used =>
    exact z.resMu_used h

end Dat

end Record

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DefiniteSideNonzeroIndexPlacesAnyColumnsScale
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem cx_zs_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) (κ lam e) : (reErr (reScal Y κ lam) e).zs = Y.zs := rfl

theorem cx_liftMat_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) : (reErr (reScal Y κ lam) e).liftMat cr b j t = Y.liftMat cr b j t := by
  have h : (reErr (reScal Y κ lam) e).liftMatC cr b j t = Y.liftMatC cr b j t := by
    unfold CxData.liftMatC
    rfl
  exact congrArg (kMat Bs.v0.embedding) h

theorem cx_Iw_scal {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (b : Bool) (j : Bs.J) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) :
    ((reErr (reScal Y κ lam) e).data cr b).Iw j t w = (Y.data cr b).Iw j t w :=
  congrArg (fun M => Formalism.DivisionValues.idx w (Y.M b j) (Formalism.DivisionValues.matLat M ((lv (fc Y.zs) b).Tl j t))) (cx_liftMat_scal Y cr κ lam e b j t)

theorem definiteComplexNonzeroIndexPlaces_rescale_errors {Bs : DefBase K} {A : DefAmb Bs} (Y : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (κ lam e)
    (N : IndefNum Bs) (w : HeightOneSpectrum (𝓞 K)) : (reErr (reScal Y κ lam) e).W1 cr N w ↔ Y.W1 cr N w :=
  exists_congr fun j => or_congr (not_congr (Eq.congr_left (cx_Iw_scal Y cr κ lam e false j _ _)))
    (or_congr (not_congr (Eq.congr_left (cx_Iw_scal Y cr κ lam e false j _ _))) Iff.rfl)

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} (Y : CxData A3.fam3.amb3) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
  (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (Dc Dc' : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
  (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Sp' : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc' Zs))
  (Zsc Zsc' : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)

theorem cx_tC_face (j : Fin m) (t : T) :
    Y.tC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false j t = Y.tC (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false j t := rfl

theorem cx_liftMat_face (j : Fin m) (t : T) :
    Y.liftMat (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false j t = Y.liftMat (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false j t :=
  congrArg (fun g => kMat A3.fam3.base3.v0.embedding (relMat (Y.w0C false j) g)) (cx_tC_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j t)

theorem cx_Iw_face (j : Fin m) (t : T) (w : HeightOneSpectrum (𝓞 K)) :
    (Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') false).Iw j t w = (Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j t w :=
  congrArg (fun M => Formalism.DivisionValues.idx w (Y.M false j) (Formalism.DivisionValues.matLat M ((A3.side3 P0 ψ0 Y.zs).Tl j t)))
    (cx_liftMat_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j t)

theorem definiteSide_nonzeroIndexPlaces_any_columns_scale (N : IndefNum A3.fam3.base3) (w : HeightOneSpectrum (𝓞 K)) :
    Y.W1 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc' Sp' Zsc') N w ↔ ∃ j : Fin m,
      ((Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j A3.A.μ0 w ≠ 0 ∨
        Formalism.DivisionValues.jw ((A3.side3 P0 ψ0 Y.zs).HT j A3.A.μ0) w ((A3.side3 P0 ψ0 Y.zs).Tl j A3.A.μ0) ≠ 0 ∨ N.F0 w j ≠ 0) ∨
      ((Y.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false).Iw j A3.A.μ0 (Formalism.DivisionValues.conjPl w) ≠ 0 ∨
        Formalism.DivisionValues.jw ((A3.side3 P0 ψ0 Y.zs).HT j A3.A.μ0) (Formalism.DivisionValues.conjPl w) ((A3.side3 P0 ψ0 Y.zs).Tl j A3.A.μ0) ≠ 0 ∨
          N.F0 (Formalism.DivisionValues.conjPl w) j ≠ 0) := by
  refine exists_congr fun j => ?_
  rw [← cx_Iw_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j, ← cx_Iw_face Y P0 ψ0 P1 ψ1 Dc Dc' Sp Sp' Zsc Zsc' j]
  have key : ∀ a b c d e f : Prop, (a ∨ b ∨ c ∨ d ∨ e ∨ f) ↔ (a ∨ c ∨ e) ∨ (b ∨ d ∨ f) := fun _ _ _ _ _ _ => by tauto
  exact key _ _ _ _ _ _

end Cx

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def NzAt (R : RealDat3 D A3 Ks) (F : Face3 D A3) (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) (j : Fin D.R.m)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  (s0Of R F).Iw j A3.A.μ0 w ≠ 0 ∨
    Formalism.DivisionValues.jw ((A3.side3 F.P0 F.ψ0 (zsOf R F)).HT j A3.A.μ0) w ((A3.side3 F.P0 F.ψ0 (zsOf R F)).Tl j A3.A.μ0) ≠ 0 ∨ F0 w j ≠ 0


set_option maxHeartbeats 1000000 in
theorem toCx3_upd_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    ((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc) = reErr (reScal (R.toCx3 F) (fun _ => kap) lam) err := rfl


set_option maxHeartbeats 1000000 in
theorem complexSide_nonzeroIndexPlaces_iff (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs))
    (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (N : IndefNum A3.fam3.base3)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc)).W1 (reFace F Dc Sp Zsc).cr N w ↔
      ∃ j, NzAt R F N.F0 j w ∨ NzAt R F N.F0 j (Formalism.DivisionValues.conjPl w) := by
  have e := toCx3_upd_reFace R F kap lam err Dc Sp Zsc
  rw [e]
  exact (definiteComplexNonzeroIndexPlaces_rescale_errors (R.toCx3 F) _ _ _ _ N w).trans (definiteSide_nonzeroIndexPlaces_any_columns_scale (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 F.Dc Dc F.Sp Sp F.Zsc Zsc N w)


set_option maxHeartbeats 1000000 in
theorem complexSide_nonzeroIndexPlaces_iff_self (R : RealDat3 D A3 Ks) (F : Face3 D A3) (N : IndefNum A3.fam3.base3) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (R.toCx3 F).W1 F.cr N w ↔ ∃ j, NzAt R F N.F0 j w ∨ NzAt R F N.F0 j (Formalism.DivisionValues.conjPl w) :=
  definiteSide_nonzeroIndexPlaces_any_columns_scale (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Dc F.Sp F.Sp F.Zsc F.Zsc N w


set_option maxHeartbeats 1000000 in
theorem nzAt_res {f : T' → T} {μ : T'} (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    NzAt (Res.dat3 f μ R mu tw) (Res.bare3 _ P0 ψ0 P1 ψ1) F0 j w ↔ NzAt R (Res.bare3 _ P0 ψ0 P1 ψ1) F0 j w := Iff.rfl


set_option maxHeartbeats 1000000 in
theorem complexSide_numberContents_eq_scaleAtSubspaces (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam err) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs))
    (Sp : ∀ Zs, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (C CH : ℝ) :
    (((R.updS kap lam).withErr err).num (reFace F Dc Sp Zsc) C CH).F0 = (Zsc (zsOf R F)).F0 := by
  have e := toCx3_upd_reFace R F kap lam err Dc Sp Zsc
  have e2 : (((R.updS kap lam).withErr err).toCx3 (reFace F Dc Sp Zsc)).zs = (R.toCx3 F).zs :=
    (congrArg CxData.zs e).trans (cx_zs_scal (R.toCx3 F) _ _ _)
  have e3 : ∀ (F' : Face3 D A3) (s : DefSub A3.fam3.amb3), ((F'.fc s).Z.num C CH).F0 = (F'.Zsc s).F0 := fun _ _ => rfl
  exact (e3 (reFace F Dc Sp Zsc) _).trans (congrArg (fun s => (Zsc s).F0) e2)

end Generic

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat

theorem _root_.GlobalTheory.Mem.R3.columnChoiceReferenceFace_eq_bareFaceTwoLevels (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) :
    face0 X I hX U Xg tr = Res.bare3 (famR X I hX U Xg tr) (lev0 I) (chr0 I) (lev1 I) (chr1 I) := rfl


set_option maxHeartbeats 2000000 in
def resGeo (h : Wt' ⊆ Wt) : GlobalTheory.RealGeo.GeoHalf z.core (z.resR h).toRealDat fun _ => 1 :=
  Res.geoHalf (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') z.geo




set_option maxHeartbeats 2000000 in
theorem levOf_resR (h : Wt' ⊆ Wt) : LevOf X I (usedOf I T Wt') (z.resR h).toLevCh :=
  ⟨Res.levCh_is (L := z.R.toLevCh) (inclU_injective (usedOf_mono I T h)) z.lev.is,
    z.lev.C,
    fun t => z.lev.xiH (inclU I (usedOf_mono I T h) t),
    z.lev.Pg,
    fun t => z.lev.Q (inclU I (usedOf_mono I T h) t),
    z.lev.beta⟩

end Dat

end Record

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InGeoGeoScalIff
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Res

section Geo

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {ph : Fin D.R.m → ℂ}


set_option maxHeartbeats 2000000 in
def geoScal (g : GlobalTheory.RealGeo.GeoHalf C R ph) (kap lam err) :
    GlobalTheory.RealGeo.GeoHalf C ({ R.upd6 kap lam with err0 := err } : RealDat D A C.Q.c.F) ph :=
  ⟨g.κ, g.v₀, GlobalTheory.RealGeo.Upd.updFWT C R kap lam err g.fw, g.bar, fun i => GlobalTheory.RealGeo.Upd.updO C R kap lam err (g.O i),
    fun i => GlobalTheory.RealGeo.Upd.omPins_upE kap lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩


end Geo

section Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]




def KapFixed (S : RealDat3 D A3 Ks) (κ : ℝ) : Prop :=
  Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ ∧
    ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0


open Classical in
def kapNew (S : RealDat3 D A3 Ks) : ℝ := if h : ∃ κ, KapFixed S κ then h.choose else S.kap

theorem kapNew_eq (S : RealDat3 D A3 Ks) {κ : ℝ} (h : KapFixed S κ) : kapNew S = κ := by
  have h' : ∃ κ, KapFixed S κ := ⟨κ, h⟩
  unfold kapNew
  rw [dite_eq_left h']
  obtain ⟨t, p, hp, hl⟩ := h.2
  exact Lift.IsKap.unique h'.choose_spec.1 h.1 t p hp hl

theorem kapNew_of_not (S : RealDat3 D A3 Ks) (h : ¬ ∃ κ, KapFixed S κ) : kapNew S = S.kap := dif_neg h

theorem kapNew_of_scal (S : RealDat3 D A3 Ks) (h : S.scal_kap) : kapNew S = S.kap := by
  by_cases h' : ∃ κ, KapFixed S κ
  · obtain ⟨κ, hκ⟩ := h'
    exact (kapNew_eq S hκ).trans (h κ hκ.1 hκ.2).symm
  · exact kapNew_of_not S h'


variable {f : T' → T} {μ : T'} {R : RealDat3 D (A3.comap id (f μ)) Ks} {mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T'}
  {tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}



end Generic

end Res

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat








end Dat

end Record

end GlobalTheory.Mem.R3

end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl} (z : Dat X I hX T Wt)

namespace Dat




set_option maxHeartbeats 2000000 in
theorem inGeo_resGeo_iff (h : Wt' ⊆ Wt) : GlobalTheory.RealGeo.InGeo (z.resGeo h) ↔ GlobalTheory.RealGeo.InGeo z.geo :=
  Res.inGeo_iff (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') (g := z.geo)

variable (F0 : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → Fin X.toD7.R.m → ℝ)

theorem mem_nonzero_index_places_iff_at_place_or_conjugate (w : X.B.places.Pl) :
    w ∈ z.W1 F0 ↔ ∃ j, NzAt z.R z.F F0 j (plB X w) ∨ NzAt z.R z.F F0 j (Formalism.DivisionValues.conjPl (plB X w)) := by
  refine exists_congr fun j => ⟨?_, ?_⟩
  · rintro ⟨w', rfl | rfl, h⟩
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩

theorem nonzero_index_places_conj_stable : ConjStable X (z.W1 F0) := by
  intro w hw
  rw [mem_nonzero_index_places_iff_at_place_or_conjugate] at hw ⊢
  rw [plB_conj, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  exact hw.imp fun _ h => h.symm


set_option maxHeartbeats 2000000 in
theorem nzAt_resR (h : Wt' ⊆ Wt) (j : Fin X.toD7.R.m) (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    NzAt (z.resR h) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) F0 j v ↔ NzAt z.R (face0 X I hX (usedOf I T Wt) z.Xg z.tr) F0 j v := by
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels, columnChoiceReferenceFace_eq_bareFaceTwoLevels]
  exact nzAt_res (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) z.R (z.resMu h) (z.resTw Wt') (lev0 I) (chr0 I) (lev1 I) (chr1 I) F0 j v

theorem complex_side_places_iff_mem_nonzero_index_places (kap lam err) (Dc Sp Zsc) (N : IndefNum (famR X I hX (usedOf I T Wt) z.Xg z.tr).fam3.base3) (hN : N.F0 = F0)
    (w : X.B.places.Pl) :
    (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr N (X.toD7.plEq w) ↔ w ∈ z.W1 F0 := by
  subst hN
  exact (complexSide_nonzeroIndexPlaces_iff z.R z.F kap lam err Dc Sp Zsc N (plB X w)).trans (z.mem_nonzero_index_places_iff_at_place_or_conjugate N.F0 w).symm

theorem complex_side_face_numbers_iff_mem_nonzero_index_places (kap lam err) (Dc Sp Zsc) (C CH : ℝ) (hZ : (Zsc (zsOf z.R z.F)).F0 = F0) (w : X.B.places.Pl) :
    (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr
      (((z.R.updS kap lam).withErr err).num (reFace z.F Dc Sp Zsc) C CH) (X.toD7.plEq w) ↔ w ∈ z.W1 F0 :=
  z.complex_side_places_iff_mem_nonzero_index_places F0 kap lam err Dc Sp Zsc _ ((complexSide_numberContents_eq_scaleAtSubspaces z.R z.F kap lam err Dc Sp Zsc C CH).trans hZ) w

theorem twisted_places_eq_complex_side_of_eq_nonzero_index (hW : z.W1 F0 = Wt) (kap lam err) (Dc Sp Zsc) (C CH : ℝ) (hZ : (Zsc (zsOf z.R z.F)).F0 = F0)
    (v : HeightOneSpectrum (𝓞 X.toD7.what₂.LL)) :
    v ∈ ((z.R.updS kap lam).withErr err).twPl ↔
      (((z.R.updS kap lam).withErr err).toCx3 (reFace z.F Dc Sp Zsc)).W1 (reFace z.F Dc Sp Zsc).cr
        (((z.R.updS kap lam).withErr err).num (reFace z.F Dc Sp Zsc) C CH) v := by
  obtain ⟨w, rfl⟩ := (plB X).surjective v
  exact (z.plB_mem_twPl w).trans ((Set.ext_iff.1 hW w).symm.trans (z.complex_side_face_numbers_iff_mem_nonzero_index_places F0 kap lam err Dc Sp Zsc C CH hZ w).symm)


section Ex

variable (e : z.R.toRealDat.ExAt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt')







end Ex

section ExW

variable (e : z.R.toRealDat.ExAt) (h : z.W1 F0 ⊆ Wt)

end ExW


end Dat

end Record

end GlobalTheory.Mem.R3

end
