module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistDataLowerBlockUniversalCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNewThetaDataSeriesClassSumsLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScalarP
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.SerCopy

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

abbrev DN (x : St P) (N : TwNew (Dof x)) : D7 := (w.st (oTw x N).Z).toD7

def oth (x : St P) (N : TwNew (Dof x)) : Oth (B := B) (C := w.C) (P.q.W x.o.η x.o.hη) := ⟨x.o.V, x.o.S, nTw x N, x.o.G⟩

variable {x : St P}

def baN {N : TwNew (Dof x)} (N' : TwNew (Dof x)) {j : Fin (DN x N).R.m} (X : ExportSeries.Base (Vc (DN x N) j) (Wc (DN x N) j)) :
    ExportSeries.Base (Vc (DN x N') ((j))) (Wc (DN x N') ((j))) :=
  (@baT B (@ColW.C B f T w) (@RowPk.Over.Z B f T w (@Pre2.Z₀ B f T K w P) (@Pre2.hX B f T K w P) (@Pre2.Wt B f T K w P) (@Pre2.z B f T K w P) (@Pre2.q B f T K w P) (@oTw K B f T w P x N)) (@RowPk.Over.Z B f T w (@Pre2.Z₀ B f T K w P) (@Pre2.hX B f T K w P) (@Pre2.Wt B f T K w P) (@Pre2.z B f T K w P) (@Pre2.q B f T K w P) (@oTw K B f T w P x N')) (Vc (@DN K B f T w P x N) j) (Wc (@DN K B f T w P x N) j) X)

set_option maxHeartbeats 8000000 in
theorem isNormN {N : TwNew (Dof x)} (N' : TwNew (Dof x)) {j : Fin (DN x N).R.m}
    {X : ExportSeries.Base (Vc (DN x N) j) (Wc (DN x N) j)} {ν : ℂ} (h : IsNorm (D := DN x N) (datTw x N).R (datTw x N).geo.v₀ X ν) :
    IsNorm (D := DN x N') (datTw x N').R (datTw x N').geo.v₀ (j := (j)) (@baN K B f T w P x N N' j X) ν := by
  obtain ⟨h0, c, ⟨g, c0R, c0L, hF, u, hu, hh⟩, hn⟩ := h
  exact ⟨h0, c, ⟨(g), (c0R), (c0L),
    (by with_unfolding_all exact famTie_imp (a := (oTw x N).Z) (oTw x N').Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF), (u), (hu), (hh)⟩, (hn)⟩

variable {N₁ : TwNew (Dof x)} {kKs : (datTw x N₁).core.Q.c.F →+* ↥(DN x N₁).LL0}
  {hk : ∀ y : (datTw x N₁).core.Q.c.F, ((kKs y : ↥(DN x N₁).LL0) : (DN x N₁).what₂.LL) = algebraMap (datTw x N₁).core.Q.c.F (DN x N₁).what₂.LL y}
  {YS : NExpRealS (datTw x N₁).R (datTw x N₁).cG (ratDatR (datTw x N₁).R (datTw x N₁).cG kKs hk)} {X : NExpTied (DN x N₁)} {hF Pq}
  (p : PreTie YS (datTw x N₁).geo.v₀ X hF Pq)

def nP : TwNew (Dof x) := ⟨N₁.tw, PreTie.ex (D := DN x N₁) (Ks := (datTw x N₁).core.Q.c.F) p, N₁.h0, PreTie.nth (D := DN x N₁) (Ks := (datTw x N₁).core.Q.c.F) p, N₁.br, N₁.hbr⟩

def kP : (datTw x (nP p)).core.Q.c.F →+* ↥(DN x (nP p)).LL0 := (kKs)

theorem hkP : ∀ y, ((kP p y : ↥(DN x (nP p)).LL0) : (DN x (nP p)).what₂.LL) =
    algebraMap (datTw x (nP p)).core.Q.c.F (DN x (nP p)).what₂.LL y := (hk)

abbrev sP : RatDat (DN x (nP p)).ntw := ratDatR (datTw x (nP p)).R (datTw x (nP p)).cG (kP p) (hkP p)

def ysP : NExpRealS (datTw x (nP p)).R (datTw x (nP p)).cG (sP p) where
  fi := (YS.fi)
  geq := (YS.geq)
  rho := (YS.rho)
  chi := (YS.chi)
  eF := (YS.eF)
  bsup := (YS.bsup)
  act := (YS.act)

def rhoP : Setup (DN x (nP p)).ntw :=
  (by with_unfolding_all exact ((@seT B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ))) : _))

theorem goodP : (rhoP p).Good :=
  (by with_unfolding_all exact ((@seGood B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ)) ((p.good))) : _))

theorem pinP : RealPin (datTw x (nP p)).R (datTw x (nP p)).cG (rhoP p) :=
  ⟨(p.pin.psi), (p.pin.inf), (p.pin.cartT), (p.pin.onbS), (p.pin.onbT), (p.pin.latS), (p.pin.latT), (p.pin.frS),
    (p.pin.frT), (p.pin.vac), (p.pin.Pg), (p.pin.grp), (p.pin.mu0), (p.pin.eta), (p.pin.delta), (p.pin.deltaPl),
    (p.pin.ap), (p.pin.am)⟩

theorem ratP (i : (DN x N₁).ntw.Tw) (j : Fin (DN x N₁).R.m) (b : Bool) (ν : ℂ) :
    SeriesTie.Rat (goodP p) (realRd (ysP p) (datTw x (nP p)).geo.v₀ (goodP p) ((i)) ((j)) b ν) ↔
      SeriesTie.Rat p.good (realRd YS (datTw x N₁).geo.v₀ p.good i j b ν) :=
  ⟨fun h => (by with_unfolding_all exact ((@ratT' B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ)) ((i)) ((j)) b
      ((p.ex)) (((realRd YS (datTw x N₁).geo.v₀ p.good i j b ν))) ((p.good)) ((h))) : _)),
    fun h => (by with_unfolding_all exact ((@ratT B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ)) ((i)) ((j)) b
      ((p.ex)) (((realRd YS (datTw x N₁).geo.v₀ p.good i j b ν))) ((p.good)) ((h))) : _))⟩

theorem normP (i : (DN x N₁).ntw.Tw) (j : Fin (DN x N₁).R.m) (b : Bool) (ν : ℂ) :
    IsNorm (datTw x (nP p)).R (datTw x (nP p)).geo.v₀ ((rhoP p).B ((i)) ((j)) b) ν ↔
      IsNorm (datTw x N₁).R (datTw x N₁).geo.v₀ (p.ρ.B i j b) ν :=
  ⟨fun h => (@isNormN K B f T w P x (@nP K B f T w P x N₁ kKs hk YS X hF Pq p) N₁ j (@Setup.B (@DN K B f T w P x (@nP K B f T w P x N₁ kKs hk YS X hF Pq p)) (@DN K B f T w P x (@nP K B f T w P x N₁ kKs hk YS X hF Pq p)).nd (@DN K B f T w P x (@nP K B f T w P x N₁ kKs hk YS X hF Pq p)).ntw (@rhoP K B f T w P x N₁ kKs hk YS X hF Pq p) i j b) ν h), fun h => (by with_unfolding_all exact ((isNormN (nP p) h) :))⟩

theorem scalarP (i : (DN x N₁).ntw.Tw) (j : Fin (DN x N₁).R.m) (b : Bool) :
    IsScalar (ysP p) (datTw x (nP p)).geo.v₀ (goodP p) ((i)) ((j)) b (p.ν i j b) :=
  ⟨(p.scalar i j b).ne, fun h => (normP p i j b _).2 ((p.scalar i j b).norm (h.imp fun ν => (normP p i j b ν).1)),
    fun h => (ratP p i j b _).2 ((p.scalar i j b).rat (h.imp fun ν h' => ⟨(normP p i j b ν).1 h'.1, (ratP p i j b ν).1 h'.2⟩))⟩

def exP (hu : GlobalTheory.UnivChar.IsUnivChar (DN x N₁).nexp) : ExportTie (ysP p) (datTw x (nP p)).geo.v₀ where
  ρ := rhoP p
  good := goodP p
  pin := pinP p
  vec := (p.vec)
  ν := (p.ν)
  scalar := fun i j b => (scalarP p i j b)
  tie := fun i j b => (by with_unfolding_all exact ((@cellT B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ)) ((i)) ((j)) b
      ((p.ex)) (((realRd YS (datTw x N₁).geo.v₀ p.good ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (p.ν ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)))) ((p.good))
      (((p.tie ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)))) : _))
  hecke := fun i j b => (by with_unfolding_all exact ((@heckeTieT B w.C _ (oth x N₁) (oth x (nP p)) (((DN x N₁).nd)) (((DN x N₁).ntw)) ((p.ρ)) ((i))
      ((j)) b ((p.ex)) (((realRd YS (datTw x N₁).geo.v₀ p.good ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (p.ν ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b))))
      (((p.hecke ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b)))) : _))
  univ := (hu)

set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
def expP : NExpTied (DN x (nP p)) :=
  -- Use the fieldwise construction of `keepExp` at the stage produced by `nP`.
  { X with
    acgWt := X.acgWt
    modWt := X.modWt
    fdWt := X.fdWt
    thU_empty := fun i j b M d hj hj' => p.hU i j b M d hj hj'
    mtV := fun i j b k Q ψ hj hj' hA => by
      letI : AddCommGroup (X.Wt i j b) := X.acgWt i j b
      letI : Module (FractionRing ((DN x (nP p)).ntw.O i)) (X.Wt i j b) := X.modWt i j b
      exact { X.mtV i j b k Q ψ hj hj' hA with } }

def pvP (PV : ∀ j : Fin (DN x (nP p)).R.m, principalLevelFrame.RowPsi (Vc (DN x (nP p)) j) (DN x (nP p)).R.nV) (j : Fin (DN x N₁).R.m) :
    principalLevelFrame.RowPsi (Vc (DN x N₁) j) (DN x N₁).R.nV :=
  ⟨((PV j).ψ), ((PV j).inj), ((PV j).into), ((PV j).onto)⟩

set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
def serP (hu : GlobalTheory.UnivChar.IsUnivChar (DN x N₁).nexp) (ho : NoOff (DN x N₁))
    (hs : ∀ i j b h1 h2 (y : (DN x N₁).nexp.Fm i j b), y ∈ (DN x N₁).nexp.Bsup i j b ↔
      YS.eF i j b h1 h2 y ∈ Bsup (ratDatR (datTw x N₁).R (datTw x N₁).cG kKs hk) i j b)
    (PV : ∀ j : Fin (DN x (nP p)).R.m, principalLevelFrame.RowPsi (Vc (DN x (nP p)) j) (DN x (nP p)).R.nV) {hF'}
    (hPV : ∀ j, GlobalTheory.MtRead.IdFrame hF' (PV j)) {cf : CharFrame (DN x (nP p))} (Z : GlobalTheory.LamTie.LamDat (DN x (nP p)))
    (hZ : Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 (DN x (nP p)) ∧ GlobalTheory.LamTie.IsLamTieFull (DN x (nP p)).ntw Z) :
    SerAt (ysP p) (datTw x (nP p)).geo.v₀ (expP p) PV cf ((Pq)) where
  ex := exP p hu
  bad := (p.bad)
  ch := (p.ch)
  join := by
    intro i j b k Q ψ hA hOK
    have hjoin := p.join (pvP p PV) (fun j => hPV j) i j b k Q ψ hA hOK
    with_unfolding_all exact hjoin
  sup := (hs)
  off := (ho)
  lam := Z
  lam_ok := hZ.1
  lam_teich := hZ.2.1
  lam_C := hZ.2.2.1
  lam_q := hZ.2.2.2.1
  lam_tie := hZ.2.2.2.2

end GlobalTheory.HeightCounting.SerCopy

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTauFamily
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)

theorem GlobalTheory.TwInputs.tauG_read (hGAR : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ) (hV : ValLL0 D cf)
    (i : D.ntw.Tw) (b : Bool) (j : Fin D.R.m) (k : Fin 2) (v : D.nd.PlG k) (x : (ZMod (D.host.g k))ˣ)
    (u : 𝓞 D.host.E) (hu0 : (u : D.host.E) ≠ 0)
    (hxu0 : (((x : ZMod (D.host.g k)).val : 𝓞 D.host.E) - u) ∈ (NX.pG D ⟨k, v⟩).asIdeal)
    (hl0 : NX.pG D ⟨k, v⟩ ∉ placesOver D.host.E (D.ntw.l i)) :
    (((cf.mu0 j).locK (NX.pG D ⟨k, v⟩) (Units.mk0 (u : D.host.E) hu0) : ℂˣ) : ℂ) ^ (D.host.g k - 1) = 1 ∧
    ∀ y : ↥D.LL0, embLL0 D y = (((cf.mu0 j).locK (NX.pG D ⟨k, v⟩) (Units.mk0 (u : D.host.E) hu0) : ℂˣ) : ℂ) →
      ((Bs.exp.tauG i (j.1 + 1) b ⟨k, v⟩ x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = sideEmb D.ntw i b y := by
  have hgp : (D.host.g k).Prime := D.host.g_prime k
  haveI : Fact (D.host.g k).Prime := ⟨hgp⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  obtain ⟨ρ⟩ := GlobalTheory.Triple.Reading.nonempty (X := D.ntw) i b
  obtain ⟨n, hn⟩ := GlobalTheory.TwChiGal.firstTwistCharacter_eq_ladic_heckeCharacter D cf Bs.chiD Bs.chi Bs.eta_eq Bs.ringSpec_normalisedCharacter_eq Bs.del_eq hV art ha i b ρ j
  have hl : ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := hl0
  have hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hspl := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) hgp (D.nd.g_split k) (D.naut.plGw k v) hgw
  have hN : normV (D.naut.plGw k v) = D.host.g k := by
    rw [← hspl.1, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hg2 := hgp.two_le
  have hAw : IsPlaceOver (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) := D.nd.plOm.2 _
  have hu : u ∉ (D.naut.plGw k v).asIdeal := by
    intro h
    have h1 : (((x : ZMod (D.host.g k)).val : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := by
      have := (D.naut.plGw k v).asIdeal.add_mem hxu0 h
      rwa [sub_add_cancel] at this
    obtain ⟨a, c, hac⟩ : IsCoprime (((x : ZMod (D.host.g k)).val : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) :=
      (ZMod.val_coe_unit_coprime x).cast
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hac]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hgw)
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap D.host.E D.nd.Om (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E))
    (show 0 < normV (D.naut.plGw k v) - 1 by omega)
  have hxu : IsUnitAt (D.naut.plGw k v) (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) := by
    show Valued.v (((u : D.host.E) : (D.naut.plGw k v).adicCompletion D.host.E)) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hu
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art ha
    (D.naut.plGw k v) _ hAw _ hgw hspl.2.1 π hπ (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) u hxu
    (by simp [atFin])
  have hTR : NX.TameRep (D.naut.plGw k v) 1 σ u :=
    ⟨_, hAw, hσI, _, π, hgw, hspl.2.1, hπ, by simpa using hσval⟩
  have e1 := hn.loc (Or.inl hl) hσart.symm
  obtain ⟨h1, -, h3, -, h5⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec (GlobalTheory.Triple.hframe cf) (l := D.ntw.l i)
  have hdel : (cf.delAt (D.ntw.l i)).UnrAt (D.naut.plGw k v) :=
    h5.unr _ (GlobalTheory.GalChar.notMem_of_ne (D.host.g_prime k) h1 (h3 k).symm (D.naut.plGw_over k v))
  rw [GlobalTheory.Triple.blockChar, GlobalTheory.GalChar.block_loc (cf.isEta.unr _) hxu, GlobalTheory.Triple.muBase] at e1
  change _ = (((cf.mu0 j).loc _ _ * (cf.delAt (D.ntw.l i)).loc _ _ : ℂˣ) : ℂ) at e1
  rw [hdel _ hxu, mul_one] at e1
  have hm : ((normV (D.naut.plGw k v) - 1 : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    rw [hN]
    intro h
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := (D.naut.plGw k v).asIdeal.sub_mem hgw h
    rwa [Nat.cast_sub (by omega), Nat.cast_one, sub_sub_cancel] at this
  have hex : ∃ s : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, NX.TameRep (D.naut.plGw k v) 1 s u := ⟨σ, hTR⟩
  have e2 : NX.tameVal (D.ntw.chi1 i (j.1 + 1) b) (D.naut.plGw k v) 1 u = D.ntw.chi1 i (j.1 + 1) b σ := by
    unfold NX.tameVal
    rw [dif_pos hex]
    refine GlobalTheory.T.tameChar_eq_of_tameRep_congr (D.naut.plGw k v) (D.ntw.twistBaseCoefficientRing_isAdic i) _ (D.ntw.twistCharacterFamily_continuous i (j.1 + 1) b) (by omega) hm
      (fun A hA s hs => ?_) _ _ u u hex.choose_spec hTR (by rw [sub_self]; exact zero_mem _)
    rw [hN]
    exact D.ntw.twistCharacterFamily_tame i (j.1 + 1) b k _ hgw hl A hA s hs
  have e3 := Bs.exp.tau_galois_first_character i (j.1 + 1) b ⟨k, v⟩ x u (by omega) (by omega) hl0 hxu0
  rw [Bs.exp.sgnG_one, Bs.exp.sgnT_one, one_mul] at e3
  have e1' : ρ.ι (ρ.κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) ((D.ntw.chi1 i (j.1 + 1) b σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))) =
      (((cf.mu0 j).locK (NX.pG D ⟨k, v⟩) (Units.mk0 (u : D.host.E) hu0) : ℂˣ) : ℂ) := e1
  have ht : (D.ntw.chi1 i (j.1 + 1) b σ) ^ (D.host.g k - 1) = 1 :=
    D.ntw.twistCharacterFamily_tame i (j.1 + 1) b k _ hgw hl _ hAw σ hσI
  refine ⟨?_, fun y hy => ?_⟩
  · rw [← e1', ← map_pow, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ht]
    simp
  · have e4 : GlobalTheory.Triple.embSide D.ntw i b y =
        algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) ((D.ntw.chi1 i (j.1 + 1) b σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
      apply ρ.κ.injective
      apply ρ.ι.injective
      rw [ρ.read, hy, e1']
    have e5 : sideEmb D.ntw i b y = (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
      (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)) (GlobalTheory.Triple.embSide D.ntw i b y) := by
      cases b <;> rfl
    rw [e5, e4, ← e2]
    refine e3.trans ?_
    simp only [IsFractionRing.map, IsLocalization.map_eq]
    rfl

theorem GlobalTheory.TwInputs.exists_tau_family : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∃ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ, ∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → NX.pG D kv ∉ placesOver D.host.E (D.ntw.l i) → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0) := by
  intro hGAR D cf Rw low Pq S hL eig θ Bs hV hroot
  have key : ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k), ∃ t : (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ,
      ∀ i b x, NX.pG D kv ∉ placesOver D.host.E (D.ntw.l i) →
        ((Bs.exp.tauG i (j.1 + 1) b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
          sideEmb D.ntw i b ((t x : (↥D.LL0)ˣ) : ↥D.LL0) := by
    rintro j ⟨k, v⟩
    have hgp : (D.host.g k).Prime := D.host.g_prime k
    haveI : Fact (D.host.g k).Prime := ⟨hgp⟩
    obtain ⟨p, hpg, hp⟩ := Nat.exists_infinite_primes (D.host.g k + 1)
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨⟨w, hw⟩⟩ := Formalism.BasicNotions.Examples₂.PlOver.plNe D p
    obtain ⟨i₀, hi, -⟩ := Bs.cover w
    have hk : D.ntw.l i₀ ≠ D.host.g k := by rw [hi, hw]; omega
    have hl₀ : NX.pG D ⟨k, v⟩ ∉ placesOver D.host.E (D.ntw.l i₀) := GlobalTheory.Triple.Model.notMem_l (X := D.ntw) hk v
    have hy : ∀ x : (ZMod (D.host.g k))ˣ, ∃ y : ↥D.LL0, ∀ i b, NX.pG D ⟨k, v⟩ ∉ placesOver D.host.E (D.ntw.l i) →
        ((Bs.exp.tauG i (j.1 + 1) b ⟨k, v⟩ x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
          sideEmb D.ntw i b y := by
      intro x
      have hx0 : (x : ZMod (D.host.g k)).val ≠ 0 := by
        rw [Ne, ZMod.val_eq_zero]
        exact x.ne_zero
      have hu0 : ((((x : ZMod (D.host.g k)).val : ℕ) : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
        exact_mod_cast hx0
      have hxu : (((x : ZMod (D.host.g k)).val : 𝓞 D.host.E) - ((x : ZMod (D.host.g k)).val : 𝓞 D.host.E)) ∈
          (NX.pG D ⟨k, v⟩).asIdeal := by
        rw [sub_self]; exact zero_mem _
      have h0 := (GlobalTheory.TwInputs.tauG_read hGAR D cf Rw low Pq S hL eig θ Bs hV i₀ true j k v x _ hu0 hxu hl₀).1
      obtain ⟨y, hy⟩ := hroot k _ (by rw [mul_comm, pow_mul, h0, one_pow])
      exact ⟨y, fun i b hl =>
        (GlobalTheory.TwInputs.tauG_read hGAR D cf Rw low Pq S hL eig θ Bs hV i b j k v x _ hu0 hxu hl).2 y hy⟩
    choose Y hY using hy
    have hinj := (sideEmb D.ntw i₀ true).injective
    let f : (ZMod (D.host.g k))ˣ →* ↥D.LL0 :=
      { toFun := Y
        map_one' := hinj (by rw [← hY 1 i₀ true hl₀, map_one, map_one, Units.val_one])
        map_mul' := fun a c => hinj (by
          rw [map_mul, ← hY _ i₀ true hl₀, ← hY _ i₀ true hl₀, ← hY _ i₀ true hl₀, map_mul, Units.val_mul]) }
    exact ⟨f.toHomUnits, fun i b x hl => hY x i b hl⟩
  choose t ht using key
  refine ⟨fun j kv => if h : j - 1 < D.R.m then t ⟨j - 1, h⟩ kv else 1, ?_⟩
  intro i j b kv x h1 h2 hl
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have h : j' + 1 - 1 < D.R.m := by omega
  simp only [dif_pos h]
  exact ht ⟨j', h⟩ kv i b x hl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondStepNoFormsOutsideLiftRange
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
noncomputable section

namespace GlobalTheory.HeightCounting.CutOff

section Generic

def cut (p : Prop) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] : Submodule R M where
  carrier := {x | ¬ p → x = 0}
  add_mem' := fun {a b} ha hb h => by rw [ha h, hb h, add_zero]
  zero_mem' := fun _ => rfl
  smul_mem' := fun c x hx h => by rw [hx h, smul_zero]

variable {p : Prop} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem cut_subsingleton (h : ¬ p) : Subsingleton ↥(cut p R M) := ⟨fun a b => Subtype.ext ((a.2 h).trans (b.2 h).symm)⟩

def cutEnd (p : Prop) (f : Module.End R M) : Module.End R ↥(cut p R M) :=
  f.restrict (p := cut p R M) (q := cut p R M) fun x hx h => by rw [hx h, map_zero]

theorem cutEnd_one : cutEnd p (1 : Module.End R M) = 1 := LinearMap.ext fun _ => rfl

theorem cutEnd_mul (f g : Module.End R M) : cutEnd p (f * g) = cutEnd p f * cutEnd p g := LinearMap.ext fun _ => rfl

def cutAct (p : Prop) {G : Type} [Group G] (ρ : G →* (M ≃ₗ[R] M)) : G →* (↥(cut p R M) ≃ₗ[R] ↥(cut p R M)) where
  toFun g := LinearEquiv.ofLinear (cutEnd p (ρ g).toLinearMap) (cutEnd p (ρ g).symm.toLinearMap)
    (LinearMap.ext fun x => Subtype.ext ((ρ g).apply_symm_apply x)) (LinearMap.ext fun x => Subtype.ext ((ρ g).symm_apply_apply x))
  map_one' := LinearEquiv.ext fun x => Subtype.ext (by
    change ρ 1 x = x
    rw [map_one]; rfl)
  map_mul' g h := LinearEquiv.ext fun x => Subtype.ext (by
    change ρ (g * h) x = ρ g (ρ h x)
    rw [map_mul]; rfl)

def cutTop (h : p) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] : ↥(cut p R M) ≃ₗ[R] M where
  toFun x := x.1
  invFun x := ⟨x, fun hn => absurd h hn⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem cut_free [IsDomain R] [IsPrincipalIdealRing R] [Module.Free R M] [Module.Finite R M] : Module.Free R ↥(cut p R M) := by
  by_cases h : p
  · exact Module.Free.of_equiv (cutTop h R M).symm
  · haveI := cut_subsingleton (R := R) (M := M) h
    infer_instance

theorem cut_finite [Module.Finite R M] : Module.Finite R ↥(cut p R M) := by
  by_cases h : p
  · exact Module.Finite.equiv (cutTop h R M).symm
  · haveI := cut_subsingleton (R := R) (M := M) h
    infer_instance

theorem cut_split [IsDomain R] [Module.Free R M] [Module.Finite R M] [Module.Free R ↥(cut p R M)] [Module.Finite R ↥(cut p R M)]
    {K : Type} [CommRing K] (φ : R →+* K) (f : Module.End R M)
    (hf : ∃ s : Multiset K, (LinearMap.charpoly f).map φ = (s.map fun a => Polynomial.X - Polynomial.C a).prod) :
    ∃ s : Multiset K, (LinearMap.charpoly (cutEnd p f)).map φ = (s.map fun a => Polynomial.X - Polynomial.C a).prod := by
  by_cases h : p
  · have e : (cutTop h R M).conj (cutEnd p f) = f := LinearMap.ext fun _ => rfl
    rw [← LinearEquiv.charpoly_conj (cutTop h R M), e]
    exact hf
  · haveI := cut_subsingleton (R := R) (M := M) h
    refine ⟨0, ?_⟩
    have h1 : LinearMap.charpoly (cutEnd p f) = 1 := by
      rw [← (LinearMap.charpoly_monic _).natDegree_eq_zero, LinearMap.charpoly_natDegree]
      exact Module.finrank_zero_of_subsingleton
    rw [h1]; simp

theorem cut_span (h : p) {K : Type} [CommRing K] [Algebra R K] (T : Set (K ⊗[R] M)) (T' : Set (K ⊗[R] ↥(cut p R M)))
    (hT : Submodule.span K T = ⊤)
    (hh : ∀ x ∈ T, ∀ y, (∀ (f : Module.End R M) (a : K), f.baseChange K x = a • x → (cutEnd p f).baseChange K y = a • y) → y ∈ T') :
    Submodule.span K T' = ⊤ := by
  let e : K ⊗[R] M ≃ₗ[K] K ⊗[R] ↥(cut p R M) := LinearEquiv.baseChange R K _ _ (cutTop h R M).symm
  have he : ∀ (f : Module.End R M) x, (cutEnd p f).baseChange K (e x) = e (f.baseChange K x) := fun f x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [eq_top_iff, ← e.range, ← Submodule.map_top, ← hT, Submodule.map_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hh x hx _ fun f a hf => by
    change (cutEnd p f).baseChange K (e x) = a • e x
    rw [he, hf, map_smul]

theorem cut_lift {G : Type} [Group G] (ρ : G →* (M ≃ₗ[R] M)) (a : MonoidAlgebra R G) (x : ↥(cut p R M)) :
    ((MonoidAlgebra.lift R (Module.End R ↥(cut p R M)) G
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (cutAct p ρ)) a x : ↥(cut p R M)) : M) =
    MonoidAlgebra.lift R (Module.End R M) G (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) a x := by
  induction a using MonoidAlgebra.induction_on with
  | of g => rw [MonoidAlgebra.lift_of, MonoidAlgebra.lift_of]; rfl
  | add f g hf hg => simp only [map_add (f := _), LinearMap.add_apply, Submodule.coe_add, hf, hg]
  | smul r f hf => simp only [map_smul, LinearMap.smul_apply, Submodule.coe_smul, hf]

variable {K : Type} [CommRing K] [Algebra R K] {V : Type} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def cutVal (p : Prop) (R : Type) [CommRing R] (K : Type) [CommRing K] [Algebra R K] (V : Type) [AddCommGroup V] [Module K V]
    [Module R V] [IsScalarTower R K V] : ↥(cut p K V) →ₗ[R] V where
  toFun x := x.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cutEmb (p : Prop) (K : Type) [CommRing K] [Algebra R K] {V : Type} [AddCommGroup V] [Module K V]
    [Module R V] [IsScalarTower R K V] (f : M →ₗ[R] V) : ↥(cut p R M) →ₗ[R] ↥(cut p K V) where
  toFun x := ⟨f x.1, fun h => by rw [x.2 h, map_zero]⟩
  map_add' x y := Subtype.ext (map_add f x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul f c x.1)

theorem cutEmb_inj {f : M →ₗ[R] V} (hf : Function.Injective f) : Function.Injective (cutEmb p K f) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

theorem cut_comap_span (S : Set V) (h0 : (0 : V) ∈ S) :
    (Submodule.span R S).comap (cutVal p R K V) = Submodule.span R (Subtype.val ⁻¹' S : Set ↥(cut p K V)) := by
  by_cases h : p
  · exact (Submodule.span_preimage_eq (f := cutVal p R K V) ⟨0, h0⟩ fun x _ => ⟨⟨x, fun hn => absurd h hn⟩, rfl⟩).symm
  · haveI := cut_subsingleton (R := K) (M := V) h
    exact Subsingleton.elim _ _

theorem cut_span_top (S : Set M) (h0 : (0 : M) ∈ S) (hS : Submodule.span R S = ⊤) :
    Submodule.span R (Subtype.val ⁻¹' S : Set ↥(cut p R M)) = ⊤ := by
  by_cases h : p
  · rw [← Submodule.comap_top (cut p R M).subtype, ← hS]
    exact (Submodule.span_preimage_eq (f := (cut p R M).subtype) ⟨0, h0⟩ fun x _ => ⟨⟨x, fun hn => absurd h hn⟩, rfl⟩)
  · haveI := cut_subsingleton (R := R) (M := M) h
    exact Subsingleton.elim _ _

theorem cut_range {G : Type} [Group G] (ρ : G →* (V ≃ₗ[K] V)) (a : MonoidAlgebra K G) (U : Subgroup G) (ψ : U → K)
    (f : M →ₗ[R] V) (B : Submodule R V)
    (hB : LinearMap.range f = B ⊓ ((⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - ψ u • LinearMap.id)).map
      (MonoidAlgebra.lift K (Module.End K V) G (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ) a)).restrictScalars R) :
    LinearMap.range (cutEmb p K f) = B.comap (cutVal p R K V) ⊓
      ((⨅ u : U, LinearMap.ker ((cutAct p ρ u).toLinearMap - ψ u • LinearMap.id)).map
        (MonoidAlgebra.lift K (Module.End K ↥(cut p K V)) G
          (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (cutAct p ρ)) a)).restrictScalars R := by
  by_cases h : p
  · ext x
    have h1 : x ∈ LinearMap.range (cutEmb p K f) ↔ x.1 ∈ LinearMap.range f :=
      ⟨fun ⟨y, hy⟩ => ⟨y.1, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ => ⟨⟨y, fun hn => absurd h hn⟩, Subtype.ext hy⟩⟩
    have h2 : ∀ y : ↥(cut p K V), y ∈ (⨅ u : U, LinearMap.ker ((cutAct p ρ u).toLinearMap - ψ u • LinearMap.id)) ↔
        y.1 ∈ (⨅ u : U, LinearMap.ker ((ρ u).toLinearMap - ψ u • LinearMap.id)) := fun y => by
      rw [Submodule.mem_iInf, Submodule.mem_iInf]
      exact forall_congr' fun u => Subtype.ext_iff
    rw [h1, hB]
    refine and_congr Iff.rfl ⟨?_, ?_⟩
    · rintro ⟨y, hy, e⟩
      exact ⟨⟨y, fun hn => absurd h hn⟩, (h2 _).2 hy, Subtype.ext ((cut_lift ρ a _).trans e)⟩
    · rintro ⟨y, hy, e⟩
      exact ⟨y.1, (h2 _).1 hy, (cut_lift ρ a y).symm.trans (congrArg Subtype.val e)⟩
  · haveI := cut_subsingleton (R := K) (M := V) h
    exact Subsingleton.elim _ _

end Generic

variable (D : D7)

abbrev Rg (j : ℕ) : Prop := 1 ≤ j ∧ j ≤ D.R.m

def cutTw : NTw D.R D.host D.what₂ D.LL0 D.nd :=
  { D.ntw with
    B := fun i j b => ↥(cut (Rg D j) (D.ntw.O i) (D.ntw.B i j b))
    acgB := fun _ _ _ => inferInstance
    modB := fun _ _ _ => inferInstance
    freeB := fun _ _ _ => cut_free
    finB := fun _ _ _ => cut_finite
    Theta := fun _ _ _ => ⊥
    ThetaPsi := fun _ _ _ _ _ _ => ⊥
    ThetaPsi_one := fun _ _ _ _ => (Submodule.baseChange_bot _).symm
    hk := fun i j b k P => cutEnd (Rg D j) (D.ntw.hk i j b k P)
    hk_zero := fun i j b P => by rw [D.ntw.hk_zero, cutEnd_one] }

abbrev FmC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Type := ↥(cut (Rg D j) (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b))

abbrev BC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Type := ↥(cut (Rg D j) (D.ntw.O i) (D.ntw.B i j b))

def actC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : G0g D.nd →* (FmC D i j b ≃ₗ[FractionRing (D.ntw.O i)] FmC D i j b) :=
  cutAct (Rg D j) (D.nexp.actG i j b)

def bsupC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (D.ntw.O i) (FmC D i j b) :=
  (D.nexp.Bsup i j b).comap (cutVal (Rg D j) (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b))

def twPsiC (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (_ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) :
    FmC D i j b →ₗ[D.ntw.O i] (D.ntw.Ok i k ⊗[D.ntw.O i] FmC D i j b) :=
  TensorProduct.mk (D.ntw.O i) (D.ntw.Ok i k) (FmC D i j b) 1

theorem twPsiC_one (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (f : FmC D i j b) :
    twPsiC D i j b k 1 f = (1 : D.ntw.Ok i k) ⊗ₜ[D.ntw.O i] f := rfl

def twDelC (i : D.ntw.Tw) (j : ℕ) (b : Bool) (Q : Finset (PlE D.host)) (M : ℕ) :
    FmC D i j b →ₗ[D.ntw.O i] (FmC D i j b ⊗[D.ntw.O i] AddMonoidAlgebra (D.ntw.O i) (DelQM D.host (D.ntw.l i) Q M)) := 0

def thPC (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) :
    D.nexp.MtV i j b k Q ψ →ₗ[D.ntw.Ok i k] (D.ntw.Ok i k ⊗[D.ntw.O i] FmC D i j b) := 0

def hkC (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) : Module.End (FractionRing (D.ntw.O i)) (FmC D i j b) :=
  cutEnd (Rg D j) (D.nexp.hkF i j b k P)

def embC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : BC D i j b →ₗ[D.ntw.O i] FmC D i j b :=
  cutEmb (Rg D j) (FractionRing (D.ntw.O i)) (D.nexp.embB i j b)

theorem embC_inj (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Function.Injective (embC D i j b) := cutEmb_inj (D.nexp.embB_inj i j b)

def eHC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Module.End (FractionRing (D.ntw.O i)) (FmC D i j b) :=
  cutEnd (Rg D j) (D.nexp.eH i j b)

theorem eHC_idem (i : D.ntw.Tw) (j : ℕ) (b : Bool) : eHC D i j b * eHC D i j b = eHC D i j b :=
  (cutEnd_mul _ _).symm.trans (congrArg (cutEnd (Rg D j)) (D.nexp.eH_idem i j b))

def cutEx : NExp D.R D.host D.what₂ D.LL0 D.nd (cutTw D) :=
  { Fm := FmC D
    acgFm := fun (i : D.ntw.Tw) j b => (inferInstance : AddCommGroup (FmC D i j b))
    modFmK := fun (i : D.ntw.Tw) j b => (inferInstance : Module (FractionRing (D.ntw.O i)) (FmC D i j b))
    modFmO := fun (i : D.ntw.Tw) j b => (inferInstance : Module (D.ntw.O i) (FmC D i j b))
    towFm := fun (i : D.ntw.Tw) j b => (inferInstance : IsScalarTower (D.ntw.O i) (FractionRing (D.ntw.O i)) (FmC D i j b))
    fdFm := fun (i : D.ntw.Tw) j b => (cut_finite : Module.Finite (FractionRing (D.ntw.O i)) (FmC D i j b))
    actG := actC D
    U := D.nexp.U
    psiU := D.nexp.psiU
    eAlg := D.nexp.eAlg
    eLL0 := D.nexp.eLL0
    eAlg_def := D.nexp.eAlg_def
    eAlg_idem := D.nexp.eAlg_idem
    eAlg_central := D.nexp.eAlg_central
    Bsup := bsupC D
    Dat := fun _ _ _ => Empty
    th := fun _ _ _ d => d.elim
    lev := fun _ _ _ d => d.elim
    thPsi := fun _ _ _ _ _ _ d => d.elim
    thPsi_one := fun _ _ _ _ d => d.elim
    thU := fun _ _ _ _ _ d => d.elim
    twPsi := twPsiC D
    twPsi_one := twPsiC_one D
    twDel := twDelC D
    delU := D.nexp.delU
    delU_unr := D.nexp.delU_unr
    delU_l := D.nexp.delU_l
    delU_anti := D.nexp.delU_anti
    delU_open := D.nexp.delU_open
    delU_res := D.nexp.delU_res
    delU_conj := D.nexp.delU_conj
    MtV := D.nexp.MtV
    acgMt := D.nexp.acgMt
    modMtK := D.nexp.modMtK
    modMtO := D.nexp.modMtO
    towMt := D.nexp.towMt
    fdMt := D.nexp.fdMt
    MtLat := D.nexp.MtLat
    MtLat_fg := D.nexp.MtLat_fg
    MtLat_span := D.nexp.MtLat_span
    thP := thPC D
    hkF := hkC D
    embB := embC D
    embB_inj := embC_inj D
    eH := eHC D
    eH_idem := eHC_idem D }

def valC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : FmC D i j b →+ D.nexp.Fm i j b :=
  (cut (Rg D j) (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)).subtype.toAddMonoidHom

def evC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : FmC D i j b →+ (D.nth.Pt i j → ℂ_[D.ntw.l i]) := (D.nth.ev i j b).comp (valC D i j b)

def urC (i : D.ntw.Tw) (j : ℕ) (b : Bool) : AddSubgroup (FmC D i j b) := (D.nth.FmUr i j b).comap (valC D i j b)

theorem evC_inj (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Function.Injective (evC D i j b) :=
  (D.nth.ev_inj i j b).comp Subtype.val_injective

theorem span_ur (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    Submodule.span (FractionRing (D.ntw.O i)) (urC D i j b : Set (FmC D i j b)) = ⊤ :=
  cut_span_top _ (D.nth.FmUr i j b).zero_mem (D.nth.FmUr_span i j b)

theorem bsup_ur (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    bsupC D i j b = Submodule.span (D.ntw.O i) {f : FmC D i j b | f ∈ urC D i j b ∧ ∀ y, ‖evC D i j b f y‖ ≤ 1} := by
  unfold bsupC
  rw [D.nth.Bsup_def]
  exact cut_comap_span _ ⟨(D.nth.FmUr i j b).zero_mem, fun y => by simp⟩

def cutTh : NTh D.R D.host D.what₂ D.LL0 D.nd (cutTw D) (cutEx D) :=
  { D.nth with
    ev := evC D
    ev_smul := fun i j b a f y => D.nth.ev_smul i j b a (valC D i j b f) y
    ev_inj := evC_inj D
    datPhi := fun _ _ _ d => Empty.elim d
    datP := fun _ _ _ d => Empty.elim d
    hk_ev := fun i j b k P h1 h2 h3 h4 f y => D.nth.hk_ev i j b k P h1 h2 h3 h4 (valC D i j b f) y
    FmUr := urC D
    FmUr_smul := fun i j b a f ha hf => D.nth.FmUr_smul i j b a (valC D i j b f) ha hf
    FmUr_span := span_ur D
    Bsup_def := bsup_ur D }

def cutN : TwNew D := ⟨cutTw D, cutEx D, D.nStage_trivialCharacter_coeff_eq, cutTh D, D.ntwbr, D.ntwbr_ind⟩

def cutExp (E : NExpTied D) : NExpTied (cutN D).toD7 :=
  { E with
    acgWt := E.acgWt
    modWt := E.modWt
    fdWt := E.fdWt
    thU_empty := fun _ _ _ _ d => Empty.elim d
    mtV := fun i j b k Q ψ hj hj' hA =>
      letI : AddCommGroup (E.Wt i j b) := E.acgWt i j b
      letI : Module (FractionRing ((cutN D).toD7.ntw.O i)) (E.Wt i j b) := E.modWt i j b
      { E.mtV i j b k Q ψ hj hj' hA with } }

theorem cut_sigSpan (h : D.ntw.SigSpan) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Submodule.span (FractionRing (D.ntw.O i))
      {x : TensorProduct (D.ntw.O i) (FractionRing (D.ntw.O i)) (BC D i j b) | ∃ s : D.ntw.Sig i, D.ntw.jS i s = j ∧
        D.ntw.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
          ((cutEnd (Rg D j) (D.ntw.hk i j b k P)).baseChange (FractionRing (D.ntw.O i))) x =
            algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (D.ntw.hEig i s k P) • x} = ⊤ :=
  cut_span (p := Rg D j) ⟨h1, h2⟩ _ _ (h i j b h1 h2) fun _ ⟨s, e1, e2, hs⟩ _ hy =>
    ⟨s, e1, e2, fun k P a1 a2 a3 a4 => hy _ _ (hs k P a1 a2 a3 a4)⟩

theorem cut_hkSplit {F : TwFrameC D} {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ)
    (P : PlE D.host) (hP : P ∉ D.ntw.S0 i) :
    haveI : Module.Free (D.ntw.O i) (BC D i j b) := cut_free
    haveI : Module.Finite (D.ntw.O i) (BC D i j b) := cut_finite
    ∃ s : Multiset (FractionRing (D.ntw.O i)),
      (LinearMap.charpoly (cutEnd (Rg D j) (D.ntw.hk i j b k P))).map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))) =
        (s.map fun a => Polynomial.X - Polynomial.C a).prod :=
  haveI : Module.Free (D.ntw.O i) (BC D i j b) := cut_free
  haveI : Module.Finite (D.ntw.O i) (BC D i j b) := cut_finite
  cut_split _ _ (T.hk_split i j b k P hP)

theorem cut_bRange {F : TwFrameC D} {low : Finset ℕ} (T : TwistFrameLowIndexCompatibility D F low) (i : D.ntw.Tw) (j : ℕ) (b : Bool) :
    LinearMap.range (embC D i j b) = bsupC D i j b ⊓
      ((⨅ u : D.nexp.U, LinearMap.ker ((actC D i j b u).toLinearMap -
        ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • LinearMap.id)).map
        (MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (FmC D i j b)) (G0g D.nd)
          (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (actC D i j b)) (D.nexp.eAlg i b))).restrictScalars
            (D.ntw.O i) :=
  cut_range (p := Rg D j) (D.nexp.actG i j b) (D.nexp.eAlg i b) D.nexp.U
    (fun u => ((D.nexp.psiU i b u : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i))) (D.nexp.embB i j b)
    (D.nexp.Bsup i j b) (T.B_range i j b)

def topC (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hj : 1 ≤ j) (hj' : j ≤ D.R.m) :
    FmC D i j b ≃ₗ[FractionRing (D.ntw.O i)] D.nexp.Fm i j b :=
  cutTop (p := Rg D j) ⟨hj, hj'⟩ (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)

variable (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
  (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
  (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
  (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)

def eFC (Bs : SideB D cf Rw low Pq S hL eig θ) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hj : 1 ≤ j) (hj' : j ≤ D.R.m) :
    FmC D i j b ≃ₗ[FractionRing (D.ntw.O i)] Formalism.IndefR.NX.Fm S i j b :=
  (topC D i j b hj hj').trans (Bs.eF i j b hj hj')

theorem hkEmbC (Bs : SideB D cf Rw low Pq S hL eig θ) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (P : PlE D.host) (x : BC D i j b)
    (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (a3 : P ∉ D.ntw.S0 i) (a4 : IsSplitPl D.host P) (a5 : k ≤ D.R.r) :
    embC D i j b (cutEnd (Rg D j) (D.ntw.hk i j b k P) x) = hkC D i j b k P (embC D i j b x) :=
  Subtype.ext (Bs.hk_emb i j b k P x.1 a1 a2 a3 a4 a5)


set_option maxHeartbeats 4000000 in
def cutSideB (Bs : SideB D cf Rw low Pq S hL eig θ) :
    SideB (cutN D).toD7 ((cutN D).cf cf) ((cutN D).row Rw) low Pq ((cutN D).rat S) hL eig θ :=
  { Bs with
    twF := { Bs.twF with }
    tw := { Bs.tw with
      hk_split := cut_hkSplit D Bs.tw
      B_range := cut_bRange D Bs.tw }
    chiD := { Bs.chiD with }
    chi := { Bs.chi with }
    exp := cutExp D Bs.exp
    pq := fun i j b k Q ψ hj hj' hA => Bs.pq i j b k Q ψ hj hj' hA
    eF := eFC D cf Rw low Pq S hL eig θ Bs
    bsup := fun (i : D.ntw.Tw) j b hj hj' x => Bs.bsup i j b hj hj' (valC D i j b x)
    act := fun (i : D.ntw.Tw) j b hj hj' g x => Bs.act i j b hj hj' g (valC D i j b x)
    hkEq := fun (i : D.ntw.Tw) j b hj hj' k P x => Bs.hkEq i j b hj hj' k P (valC D i j b x)
    hk_emb := hkEmbC D cf Rw low Pq S hL eig θ Bs
    sigSpan := cut_sigSpan D Bs.sigSpan }

theorem cut_lamTie (Z : GlobalTheory.LamTie.LamDat D) (h : GlobalTheory.LamTie.IsLamTieFull D.ntw Z) : GlobalTheory.LamTie.IsLamTieFull (cutN D).tw Z := h

theorem fmC_subsingleton (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hn : ¬ (1 ≤ j ∧ j ≤ D.R.m)) : Subsingleton (FmC D i j b) :=
  cut_subsingleton hn

theorem cut_noOff : GlobalTheory.HeightCounting.SerCopy.NoOff (cutN D).toD7 := fmC_subsingleton D

end GlobalTheory.HeightCounting.CutOff

end

theorem _root_.GlobalTheory.T.secondStep_no_forms_outside_liftRange : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∃ N : TwNew D, (∀ Z : GlobalTheory.LamTie.LamDat D, GlobalTheory.LamTie.IsLamTieFull D.ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧ (∀ i', ∃ i, N.tw.S0 i' = D.ntw.S0 i ∧ N.tw.l i' = D.ntw.l i) ∧ GlobalTheory.HeightCounting.SerCopy.NoOff N.toD7 ∧ Nonempty (SideB N.toD7 (N.cf cf) (N.row Rw) low Pq (N.rat S) hL eig θ) :=
  fun D cf Rw low Pq S hL eig θ Bs => ⟨GlobalTheory.HeightCounting.CutOff.cutN D, GlobalTheory.HeightCounting.CutOff.cut_lamTie D, fun i => ⟨i, rfl, rfl⟩,
    GlobalTheory.HeightCounting.CutOff.cut_noOff D, ⟨GlobalTheory.HeightCounting.CutOff.cutSideB D cf Rw low Pq S hL eig θ Bs⟩⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedEqDatTw
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Mem.R3

theorem dat_ext_heq {X : Stages} {px : PreX X.B.toPre} {I : Col2.ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
    {Wt : Set X.B.places.Pl} {d₁ d₂ : Dat X I hX T Wt} (hXg : d₁.Xg = d₂.Xg) (htr : d₁.tr = d₂.tr)
    (hcore : d₁.core = d₂.core) (hR : HEq d₁.R d₂.R) (hcG : HEq d₁.cG d₂.cG) (hgeo : HEq d₁.geo d₂.geo) : d₁ = d₂ := by
  cases d₁ with
  | @mk Xg tr core alg alg_eq R cG geo pins lev idG good mu fieldValues_mem_fixedField Ks_le =>
  cases d₂ with
  | @mk Xg' tr' core' alg' alg_eq' R' cG' geo' pins' lev' idG' good' mu' le_LL0' Ks_le' =>
  dsimp only at hXg htr hcore hR hcG hgeo
  subst hXg htr hcore
  have halg : alg = alg' := Algebra.algebra_ext _ _ fun y => X.B.embLL.injective ((alg_eq y).trans (alg_eq' y).symm)
  subst halg
  cases eq_of_heq hR
  cases eq_of_heq hcG
  cases eq_of_heq hgeo
  rfl

end GlobalTheory.Mem.R3

namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw

theorem coreJ_coreJ {B : Base} {C : Cols B} {a : Late B C} (b c : Late B C) (T : Formalism.L2.Pj.CoreJ a.D) :
    coreJ (a := b) c (coreJ b T) = coreJ c T := (by with_unfolding_all exact ((Eq.refl (coreJ c T)) :))

theorem moved_eq_datTw : ∀ {K : GlobalTheory.Mem.Top.Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : GlobalTheory.Mem.Top.TwDat B} {w : GlobalTheory.Mem.Top.Bl.ColW B f T} {P : GlobalTheory.Mem.R3.Rw.Pre2 K w} (x : GlobalTheory.Mem.R3.Rw.St P) (N : TwNew (GlobalTheory.HeightCounting.Up.Dof x)) (m : GlobalTheory.Mem.R3.Rw.Moved (GlobalTheory.HeightCounting.Up.oTw x N)), m.Copy → HEq m.z.R (GlobalTheory.Mem.R3.Tr.real3 (a := x.o.Z) (GlobalTheory.HeightCounting.Up.oTw x N).Z (iK := x.m.z.alg) x.m.z.R) → HEq m.z.cG x.m.z.cG → HEq m.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := x.o.Z) (GlobalTheory.HeightCounting.Up.oTw x N).Z (iK := x.m.z.alg) x.m.z.geo) → m.z = GlobalTheory.HeightCounting.Up.datTw x N := by
  intro K B f T w P x N m hc hR hcG hgeo
  have h1 : x.m.z.core = coreJ (a := P.Z₀) x.o.Z P.z.core := (by with_unfolding_all exact ((eq_of_heq x.copy.core) :))
  have h2 : m.z.core = coreJ (a := P.Z₀) (oTw x N).Z P.z.core := (by with_unfolding_all exact ((eq_of_heq hc.core) :))
  have h3 : coreJ (a := x.o.Z) (oTw x N).Z x.m.z.core = coreJ (a := P.Z₀) (oTw x N).Z P.z.core :=
    (congrArg (coreJ (a := x.o.Z) (oTw x N).Z) h1).trans (coreJ_coreJ _ _ _)
  have h4 : HEq (datTw x N).cG x.m.z.cG := (by with_unfolding_all exact ((HEq.refl x.m.z.cG) :))
  exact dat_ext_heq (d₁ := m.z) (d₂ := datTw x N) ((by with_unfolding_all exact ((m.Xg.trans x.m.Xg.symm) :))) ((by with_unfolding_all exact ((m.tr.trans x.m.tr.symm) :)))
    ((by with_unfolding_all exact ((h2.trans h3.symm) :))) ((by with_unfolding_all exact (hR :))) (hcG.trans h4.symm) ((by with_unfolding_all exact (hgeo :)))

end GlobalTheory.HeightCounting.Up
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3.Tr
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.SerCopy

def lamT {D : D7} (N : TwNew D) (Z : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat N.toD7 := ⟨N.cf Z.C, Z.q0, Z.w0, Z.c, Z.chi⟩

theorem lamT_spec {D : D7} (N : TwNew D) {cf : CharFrame D} {Z : GlobalTheory.LamTie.LamDat D}
    (h : Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull N.tw Z) :
    (lamT N Z).Ok ∧ (lamT N Z).Teich ∧ (lamT N Z).C = N.cf cf ∧ (lamT N Z).q0 = AbsolutelyIrreducibleSpan.q0 N.toD7 ∧
      GlobalTheory.LamTie.IsLamTieFull N.toD7.ntw (lamT N Z) :=
  ⟨⟨(by with_unfolding_all exact (h.1.places :)), (by with_unfolding_all exact (h.1.aux :)), (by with_unfolding_all exact (h.1.big :))⟩, (by with_unfolding_all exact (h.2.1 :)), congrArg N.cf h.2.2.1, (by with_unfolding_all exact (h.2.2.2.1 :)), (by with_unfolding_all exact (h.2.2.2.2 :))⟩

theorem exists_prepared (hA : GlobalTheory.Published.GlobalArtinReciprocity) {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ} (Bs : SideB D cf Rw low Pq S hL eig θ) (hV : ValLL0 D cf)
    (hr : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) :
    ∃ N : TwNew D, (∀ Z : GlobalTheory.LamTie.LamDat D, GlobalTheory.LamTie.IsLamTieFull D.ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z) ∧
      (∀ i', ∃ i, N.tw.S0 i' = D.ntw.S0 i ∧ N.tw.l i' = D.ntw.l i) ∧ NoOff N.toD7 ∧ GlobalTheory.UnivChar.IsUnivChar N.toD7.nexp ∧
      ∃ Bs' : SideB N.toD7 (N.cf cf) (N.row Rw) low Pq (N.rat S) hL eig θ, TauTrue Bs'.exp := by
  obtain ⟨N, h1, h2, h3, ⟨B1⟩⟩ := GlobalTheory.T.secondStep_no_forms_outside_liftRange D cf Rw low Pq S hL eig θ Bs
  obtain ⟨τ, hτ⟩ := GlobalTheory.TwInputs.exists_tau_family hA N.toD7 _ _ _ _ _ _ _ _ B1
    ⟨(by with_unfolding_all exact (hV.mu0 :)), (by with_unfolding_all exact (hV.eta :)), (by with_unfolding_all exact (hV.chiPsi :)), (by with_unfolding_all exact (hV.del :)), (by with_unfolding_all exact (hV.del' :))⟩ ((by with_unfolding_all exact (hr :)))
  obtain ⟨⟨tw, ex, h0, th, br, hbr⟩, e, g1, g2, B2, g3⟩ := GlobalTheory.T.exists_twistData_lowerBlock_universalCharacter N.toD7 _ _ _ _ _ _ _ _ B1 τ hτ
  dsimp only at e
  subst e
  exact ⟨⟨N.tw, (by with_unfolding_all exact (ex :)), (by with_unfolding_all exact (h0 :)), (by with_unfolding_all exact (th :)), (by with_unfolding_all exact (br :)), (by with_unfolding_all exact (hbr :))⟩, h1, h2, (by with_unfolding_all exact ((g1 h3) :)), (by with_unfolding_all exact (g2 :)), (by with_unfolding_all exact (B2 :)), (by with_unfolding_all exact (g3 :))⟩

theorem sideB_tau_congr {D : D7} {cf cf' : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S S' : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S'.WL j)}
    {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (e1 : cf = cf') (e4 : Pq = Pq') (e5 : S = S') (e6 : HEq hL hL')
    (h : ∃ Bs : SideB D cf Rw low Pq S hL eig θ, TauTrue Bs.exp) : ∃ Bs : SideB D cf' Rw low Pq' S' hL' eig θ, TauTrue Bs.exp := by
  subst e1 e4 e5
  cases e6
  exact h

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def PreAt {Z : w.Lt} (z : Dat (w.st Z) w.I P.hX T P.Wt) (Rw : RowSide (w.st Z).toD7)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (w.st Z).toD7.host.E)) → PlE (w.st Z).toD7.host) {α : Type} (h₀ : α)
    (eig : ℕ → (w.st Z).toD7.what₂.FT → ℕ → PlE (w.st Z).toD7.host → ↥(w.st Z).toD7.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((w.st Z).toD7.host.g kk)) →* (↥(w.st Z).toD7.LL0)ˣ) : Prop :=
  z.R.C = TC.cf w.I w.l Z ∧ ∃ kKs hk hL, HEq hL h₀ ∧
    ∃ (Bs : SideB (w.st Z).toD7 z.R.C Rw (lowAll (w.st Z).toD7) Pq (ratDatR z.R z.cG kKs hk) hL eig θ) (hF : _),
      TauTrue Bs.exp ∧ Nonempty (PreTie (ysOf Bs) z.geo.v₀ Bs.exp hF Pq)

theorem preAt_congr {Z : w.Lt} {z z' : Dat (w.st Z) w.I P.hX T P.Wt} {Rw Rw' Pq Pq'} {α α' : Type} {h₀ : α} {h₀' : α'}
    {eig eig' θ θ'} (e0 : z = z') (e1 : Rw = Rw') (e2 : Pq = Pq') (e3 : HEq h₀ h₀') (e4 : eig = eig') (e5 : θ = θ')
    (h : PreAt (P := P) z Rw Pq h₀ eig θ) : PreAt (P := P) z' Rw' Pq' h₀' eig' θ' := by
  subst e0 e1 e2 e4 e5
  obtain ⟨g1, k, hk, hf, g2, g3⟩ := h
  exact ⟨g1, k, hk, hf, g2.trans e3, g3⟩

section Install

variable {x : St P} {N₁ : TwNew (Dof x)}
  {kKs : (Up.datTw x N₁).core.Q.c.F →+* ↥(DN x N₁).LL0}
  {hk : ∀ y : (Up.datTw x N₁).core.Q.c.F,
    ((kKs y : ↥(DN x N₁).LL0) : (DN x N₁).what₂.LL) =
      algebraMap (Up.datTw x N₁).core.Q.c.F (DN x N₁).what₂.LL y}
  {cf : CharFrame (DN x N₁)} {Rw : RowSide (DN x N₁)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield (DN x N₁).host.E)) → PlE (DN x N₁).host}
  {hf : ∀ j, ℕ → PlE (DN x N₁).host →
    Module.End (DN x N₁).what₂.LL ((ratDatR (Up.datTw x N₁).R (Up.datTw x N₁).cG kKs hk).WL j)}
  {eig : ℕ → (DN x N₁).what₂.FT → ℕ → PlE (DN x N₁).host → ↥(DN x N₁).LL0}
  {θ : ∀ kk : Fin 2, Multiplicative (ZMod ((DN x N₁).host.g kk)) →* (↥(DN x N₁).LL0)ˣ}
  {Bs : SideB (DN x N₁) cf Rw (lowAll (DN x N₁)) Pq
    (ratDatR (Up.datTw x N₁).R (Up.datTw x N₁).cG kKs hk) hf eig θ}
  {hF : (DN x N₁).host.F = maximalRealSubfield (DN x N₁).host.E}

abbrev kwP (p : PreTie (ysOf Bs) (Up.datTw x N₁).geo.v₀ Bs.exp hF Pq) : TwNew (DN x N₁) :=
  keepTw (DN x N₁) p.Dat (PreTie.th (D := DN x N₁) p) p.lev p.thPsi p.h1 p.thU p.thP p.MtLat p.h2 p.h3 p.nth

def bsP (p : PreTie (ysOf Bs) (Up.datTw x N₁).geo.v₀ Bs.exp hF Pq) :
    SideB (kwP p).toD7 ((kwP p).cf cf) ((kwP p).row Rw)
      (lowAll (DN x (SerCopy.nP p))) Pq
      ((kwP p).rat (ratDatR (Up.datTw x N₁).R (Up.datTw x N₁).cG kKs hk)) hf eig θ := by
    exact keepSideB (DN x N₁) p.Dat (PreTie.th (D := DN x N₁) p) p.lev p.thPsi
      p.h1 p.thU p.thP p.MtLat p.h2 p.h3 p.nth p.hU cf Rw _ Pq _ hf eig θ Bs

end Install


end GlobalTheory.HeightCounting.SerCopy

end
