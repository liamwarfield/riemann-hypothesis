module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleWeightDescendsToPolynomialModule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHausdorffOfProjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2Extension
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up.ListCarry
open GlobalTheory.Mem.R3.Tr GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.TwInputs.Move


open Classical in
def movePl {D : D7} {I : Type} {L : Formalism.IndefR.Links.LevCh D I} (P : Places L)
    (h4 : ∀ t, ∀ PP ∈ L.Q t, ((q0 D : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) (v : HeightOneSpectrum (𝓞 D.host.F))
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hv : ((q0 D : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) (hS : v ∉ S1 D)
    (hu : u.under (𝓞 D.host.F) = v) (hs : ∃ e : Formalism.L2.Theta.AE D, Formalism.L2.NTheta.IsIdemAt e u) : Places L where
  v0 := v
  basePlace_over_qZero := hv
  w := Function.update P.w v u
  w_over x hx := by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [Function.update_self]; exact hu
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem hx hS)]
      exact P.w_over x (Finset.mem_insert_of_mem hx)
  w_split x hx := by
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [Function.update_self]; exact hs
    · rw [Function.update_of_ne (ne_of_mem_of_not_mem hx hS)]
      exact P.w_split x (Finset.mem_insert_of_mem hx)
  w_g x k hx := by
    have : x ∈ S1 D := (S1_mem_OmF D).2 (by
      fin_cases k
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx))
    rw [Function.update_of_ne (ne_of_mem_of_not_mem this hS)]
    exact P.w_g x k hx
  w_de p hp := (P.w_de p hp).imp fun 𝔭 h x hx => by
    have : x ∈ S1 D := (S1_mem_OmF D).2 (by
      rcases hp with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr hx)))
    rw [Function.update_of_ne (ne_of_mem_of_not_mem this hS)]
    exact h x hx
  w_Q t PP hP h := by
    rw [Function.update_of_ne (ne_of_mem_of_not_mem h hS)]
    exact P.w_Q t PP hP h
  levelPlace_ne_basePlace t PP hP e := by
    subst e
    refine h4 t PP hP ?_
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((q0 D : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal := hv
    rwa [map_natCast] at this

theorem movePl_w {D : D7} {I : Type} {L : Formalism.IndefR.Links.LevCh D I} (P : Places L) (h4 v u hv hS hu hs) :
    (movePl P h4 v u hv hS hu hs).w v = u := by
  simp only [movePl, Function.update_self]

theorem listPin_copy {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyTw D D' ι e)
    (hj : HEq D.ntw.jL D'.ntw.jL) (hs : HEq D.ntw.s2 D'.ntw.s2) (hX : HEq D.ntw.Xv D'.ntw.Xv) {I I' : Type}
    {Lc : Formalism.IndefR.Links.LevCh D I} {Lc' : Formalism.IndefR.Links.LevCh D' I'} {μ0 : I'} (hL : Lc'.Is μ0)
    (hmu : HEq Lc'.C.mu0 Lc.C.mu0) (hd : HEq Lc'.C.del Lc.C.del) (hd' : HEq Lc'.C.del' Lc.C.del')
    (hP : (∀ k, q0 D' ≠ D'.host.g k) → Nonempty (Places Lc'))
    (h4 : ∀ t, ∀ PP ∈ Lc'.Q t, ((q0 D' : ℕ) : 𝓞 D'.host.E) ∉ PP.asIdeal) {CF b : ℝ} (hp : ListPin D Lc CF b) :
    ListPin D' Lc' CF b := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h.gal
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h.set
  have b1 := h.sp
  have b2 := h.Tau
  have b3 := h.instTau
  have b4 := h.eTau
  have b5 := h.hc
  cases D'
  dsimp only at a1 a2 a3 b1 b2 b3 b4 b5 nOm ninstOm nalgOm nplOm nPlG xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth hj hs hX
  subst a1; subst a2; subst a3; subst b1
  rename Rows.Data _ => rows'
  cases rows'
  dsimp only at b2 b3 b4 b5
  subst b2; subst b3; subst b4; subst b5
  rename NData _ _ _ => N'
  cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  rename NTw _ _ _ _ _ => X'
  cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth hj hs hX
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hj; subst hs; subst hX
  obtain ⟨G, hF, hT⟩ := hp
  have hmu := eq_of_heq hmu
  have hd := eq_of_heq hd
  have hd' := eq_of_heq hd'
  have h0 := G.ch.basePlace_not_mem_chiGridBadPlaces
  obtain ⟨P₀⟩ := hP fun k e => h0 ((S1_mem_OmF D).2 (by
    have e' : q0 D = D.host.g k := e
    have := G.pl.basePlace_over_qZero
    rw [e'] at this
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)))
  have hm : G.pl.v0 ∈ G.pl.S0 := G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl)
  let P : Places Lc' := movePl P₀ h4 G.pl.v0 (G.pl.w G.pl.v0) G.pl.basePlace_over_qZero h0 (G.pl.under_w hm) ((G.pl.w_split G.pl.v0 hm))
  have hw : P.w P.v0 = G.pl.w G.pl.v0 := movePl_w ..
  obtain ⟨h1, h2⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA _).2 I' Lc' P ⟨1, CF, b⟩
  obtain ⟨V⟩ := GlobalTheory.ChiGridModel.nonempty_vertices _ I' Lc' _ _ (GlobalTheory.ChiGrid.colY_isV _ I' Lc' μ0 hL 0 (Nat.zero_le _)).sd h1 h2
  let X : Chars P 1 := ⟨G.ch.chiH, (G.ch.chi), (G.ch.chi_eq), (G.ch.triv), (G.ch.inf), (G.ch.unr),
    (G.ch.lev1), (G.ch.wild), (G.ch.lev0)⟩
  refine ⟨⟨P, X, V⟩, ⟨fun i a c v hv => ?_, fun v hv => ?_⟩, fun i hi => ?_⟩
  · obtain ⟨y, hy⟩ := hF.values i a c v hv
    exact ⟨e.symm y, by rw [← h.embLL0_eq, e.apply_symm_apply]; exact hy⟩
  · obtain ⟨z, hz⟩ := hF.roots v hv
    exact ⟨e.symm z, hz.map_of_injective (f := e.symm) e.symm.injective⟩
  · obtain ⟨t0, j, t1, t2⟩ := hT i ((h.inW1 i i HEq.rfl).2 hi)
    have hl : ∀ l a c, (lamOf (⟨P, X, V⟩ : GridData Lc' ⟨1, CF, b⟩)).lam0 l a c = (lamOf G).lam0 l a c := fun l a c => by
      change Lc'.C.mu0 a * (if l = D.host.pde then Lc'.C.del' else Lc'.C.del) * _ = _
      rw [hmu, hd, hd']
      rfl
    have hw' : (lamOf (⟨P, X, V⟩ : GridData Lc' ⟨1, CF, b⟩)).w0 = (lamOf G).w0 := hw
    refine ⟨by rw [hw']; exact t0, j, fun x => ?_, ?_⟩
    · exact (congrArg j (h.embLL0_eq x).symm).trans ((t1 (e x)).trans (congrArg _ (eq_of_heq (h.emb0 i i HEq.rfl x))))
    · simp only [GlobalTheory.LamTie.IsLam, BlochKatoReduction.Gen.SOk, hl, hw']
      exact t2

theorem twistPlaces_not_over_leastSplitAuxiliaryPrime {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt) : ∀ t, ∀ PP ∈ z.R.toRealDat.toLevCh.Q t,
      ((q0 (w.st Z).toD7 : ℕ) : 𝓞 (w.st Z).toD7.host.E) ∉ PP.asIdeal := by
  intro t PP hP hq
  have hprime := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (w.st Z).toD7).1
  have two : ∀ p : ℕ, p.Prime → ((p : ℕ) : 𝓞 B.host.E) ∈ PP.asIdeal → q0 (w.st Z).toD7 = p := fun p hp hm => by
    by_contra hne
    have hc : IsCoprime ((q0 (w.st Z).toD7 : ℕ) : 𝓞 B.host.E) ((p : ℕ) : 𝓞 B.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hprime hp).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    exact PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hq) (Ideal.mul_mem_left _ _ hm)))
  have hd : f.del.UnrAt PP := f.isDel.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).1 (two _ B.host.pde_prime h)
  have hd' : f.del'.UnrAt PP := f.isDel'.unr PP fun h => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrime_ne_typePrimes (w.st Z).toD7).2 (two _ B.host.pde'_prime h)
  have hps : ∀ v, (T.psi v).UnrAt PP := fun v => by
    by_contra hn
    obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 PP hn
    have hmem := Ideal.absNorm_mem PP.asIdeal
    have e := two _ h1 hmem
    exact h2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e.symm))))))
  refine (z.lev.is.Q_ram t PP).2 (Or.inl hP) ?_
  rw [z.lev.xiH t]
  have hm : w.I.xi (GlobalTheory.Mem.R3.ixOf w.I _ t) ∈ T.set f := w.xi_range ▸ ⟨_, rfl⟩
  rcases hm with (h | h | h) | ⟨v, h⟩
  · rw [h]; intro x _; rfl
  · exact h ▸ hd
  · exact (h : _ = _) ▸ hd'
  · rw [← h]
    unfold TwDat.xiTw
    split_ifs
    · exact HChar.UnrAt.mul hd' (hps v)
    · exact HChar.UnrAt.mul hd (hps v)

theorem fr_heq {A A' : Pre} (h : A' = A) {f : Top.Fr A} {f' : Top.Fr A'} (hf : HEq f' f) :
    HEq f'.mu0 f.mu0 ∧ HEq f'.del f.del ∧ HEq f'.del' f.del' := by
  subst h; cases hf; exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem lev_fr {K : Ctx} {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) :
    HEq x.m.z.R.toRealDat.toLevCh.C.mu0 f.mu0 ∧ HEq x.m.z.R.toRealDat.toLevCh.C.del f.del ∧
      HEq x.m.z.R.toRealDat.toLevCh.C.del' f.del' := by
  rw [(GlobalTheory.HeightCounting.Up.ListModel.lev_at_state x).1]
  obtain ⟨h1, h2, h3⟩ := fr_heq rfl (heq_of_eq w.C_eq)
  exact ⟨(h1), (h2), (h3)⟩

theorem listPin_copyN {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyN D N ι e)
    {D'' : D7} (hD : D'' = N.toD7) {I I' : Type}
    {Lc : Formalism.IndefR.Links.LevCh D I} {Lc' : Formalism.IndefR.Links.LevCh D'' I'} {μ0 : I'} (hL : Lc'.Is μ0)
    (hmu : HEq Lc'.C.mu0 Lc.C.mu0) (hd : HEq Lc'.C.del Lc.C.del) (hd' : HEq Lc'.C.del' Lc.C.del')
    (hP : (∀ k, q0 D'' ≠ D''.host.g k) → Nonempty (Places Lc'))
    (h4 : ∀ t, ∀ PP ∈ Lc'.Q t, ((q0 D'' : ℕ) : 𝓞 D''.host.E) ∉ PP.asIdeal) {CF b : ℝ} (hp : ListPin D Lc CF b) :
    ListPin D'' Lc' CF b := by
  subst hD
  exact listPin_copy h.cp h.jL h.s2 h.Xv hL hmu hd hd' hP h4 hp

end GlobalTheory.HeightCounting.Up.ListCarry

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellWeightOfAdmissibleTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightMatricesMatchOfCoeffSpaceIso
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightMatricesMatchOfCoeffSpaceIso
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

namespace GlobalTheory.CoefMatch

theorem vvmatch_repr {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) (y : VV K lam) (i : VVIdx lam) :
    (Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge).repr (mapVV φ lam y) i = φ ((bVV K lam).repr y i) := by
  classical
  set B' := Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge
  have hy : mapVV φ lam y = ∑ k, φ ((bVV K lam).repr y k) • B' k := by
    conv_lhs => rw [← (bVV K lam).sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smulₛₗ, Module.Basis.mk_apply]
  rw [hy, Module.Basis.repr_sum_self]

theorem wtMatch_of_coef : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {ι : Type} [Fintype ι] {K : Type} [Field K] (φ : K →+* ℂ) (emb : ι → L →+* K)
    (lam : ι → DomWeight n) {W₀ W' : Type} [AddCommGroup W₀] [Module K W₀]
    [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀)
    (ρ' : Representation ℂ (GQ L n) W') (T : W₀ ≃ₗ[K] VV K lam),
    (∀ γ x, T (ρ₀ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T x)) →
    ∀ (T' : W' ≃ₗ[ℂ] VV ℂ lam),
    (∀ γ x, T' (ρ' γ x) =
      rhoVr (fun t => φ.comp (emb t)) lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T' x)) →
    GlobalTheory.LevCmp.WtMatch φ ρ₀ ρ' := by
  intro L _ _ _ n ι _ K _ φ emb lam W₀ W' _ _ _ _ ρ₀ ρ' T hT T' hT'
  classical
  set B' := Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge with hB'
  refine ⟨VVIdx lam, inferInstance, inferInstance, (bVV K lam).map T.symm, B'.map T'.symm, fun γ => ?_⟩
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  simp only [Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
  rw [hT', hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hj : B' j = mapVV φ lam (bVV K lam j) := Module.Basis.mk_apply _ _ _
  rw [hj, ← GlobalTheory.ConjTwist.mapVV_rhoVr, hB', vvmatch_repr]

end GlobalTheory.CoefMatch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightMatricesMatchOfCoeffSpaceIsoStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightMatrices_match_of_coeffSpace_iso :
    ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {ι : Type} [Fintype ι] {K : Type} [Field K] (φ : K →+* ℂ) (emb : ι → L →+* K)
    (lam : ι → DomWeight n) {W₀ W' : Type} [AddCommGroup W₀] [Module K W₀]
    [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀)
    (ρ' : Representation ℂ (GQ L n) W') (T : W₀ ≃ₗ[K] VV K lam),
    (∀ γ x, T (ρ₀ γ x) = rhoVr emb lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T x)) →
    ∀ (T' : W' ≃ₗ[ℂ] VV ℂ lam),
    (∀ γ x, T' (ρ' γ x) =
      rhoVr (fun t => φ.comp (emb t)) lam (Formalism.L2.Col.mtwRat (L := L) (n := n) γ) (T' x)) →
    GlobalTheory.LevCmp.WtMatch φ ρ₀ ρ' :=
  @GlobalTheory.CoefMatch.wtMatch_of_coef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchingMatricesOfBaseChangeRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchingMatricesOfBaseChangeRepresentation
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

namespace GlobalTheory.BcMatch

theorem bcmatch_main : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K K' : Type} [Field K] [Field K'] (f : K →+* K') (e : K' →+* ℂ) {W₀ W W' : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup W] [Module K' W] [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀) (ρ : Representation K' (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W'), (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι K W₀) (b₁ : Module.Basis ι K' W), ∀ γ, LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map f) → GlobalTheory.LevCmp.WtMatch (e.comp f) ρ₀ ρ' → GlobalTheory.LevCmp.WtMatch e ρ ρ' := by
  intro L _ _ _ n K K' _ _ f e W₀ W W' _ _ _ _ _ _ ρ₀ ρ ρ' hb hm
  obtain ⟨ι, _, _, b₀, b₁, hb⟩ := hb
  obtain ⟨κ, _, _, c₀, c', hc⟩ := hm
  set P : Matrix ι κ K := b₀.toMatrix c₀ with hP
  set Q : Matrix κ ι K := c₀.toMatrix b₀ with hQ
  have hPQ : P * Q = 1 := Module.Basis.toMatrix_mul_toMatrix_flip b₀ c₀
  have hQP : Q * P = 1 := Module.Basis.toMatrix_mul_toMatrix_flip c₀ b₀
  have hPQf : P.map f * Q.map f = 1 := by rw [← Matrix.map_mul, hPQ, Matrix.map_one _ f.map_zero f.map_one]
  have hQPf : Q.map f * P.map f = 1 := by rw [← Matrix.map_mul, hQP, Matrix.map_one _ f.map_zero f.map_one]
  let std := Pi.basisFun K' κ
  let E : (κ → K') ≃ₗ[K'] W := LinearEquiv.ofLinear (Matrix.toLin std b₁ (P.map f)) (Matrix.toLin b₁ std (Q.map f))
    (by rw [← Matrix.toLin_mul, hPQf, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, hQPf, Matrix.toLin_one])
  let d : Module.Basis κ K' W := std.map E
  have hd1 : b₁.toMatrix d = P.map f := by
    ext i j
    rw [Module.Basis.toMatrix_apply]
    have : d j = ∑ k, (P.map f) k j • b₁ k := by
      show E (std j) = _
      exact Matrix.toLin_self _ _ _ _
    rw [this, Module.Basis.repr_sum_self]
  have hd2 : d.toMatrix b₁ = Q.map f := by
    ext j i
    rw [Module.Basis.toMatrix_apply]
    simp [d, E, std, Matrix.toLin_self, Pi.single_apply]
  refine ⟨κ, inferInstance, inferInstance, d, c', fun γ => ?_⟩
  rw [hc γ, ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix d b₁ d b₁ (ρ γ), hd1, hd2, hb γ,
    ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix c₀ b₀ c₀ b₀ (ρ₀ γ), ← hP, ← hQ]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map]
  rfl

end GlobalTheory.BcMatch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchingMatricesOfBaseChangeRepresentationStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

open Formalism.L2.DIV GlobalTheory.CoefModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matchingMatrices_of_baseChange_representation : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K K' : Type} [Field K] [Field K'] (f : K →+* K') (e : K' →+* ℂ) {W₀ W W' : Type} [AddCommGroup W₀] [Module K W₀] [AddCommGroup W] [Module K' W] [AddCommGroup W'] [Module ℂ W'] (ρ₀ : Representation K (GQ L n) W₀) (ρ : Representation K' (GQ L n) W) (ρ' : Representation ℂ (GQ L n) W'), (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b₀ : Module.Basis ι K W₀) (b₁ : Module.Basis ι K' W), ∀ γ, LinearMap.toMatrix b₁ b₁ (ρ γ) = (LinearMap.toMatrix b₀ b₀ (ρ₀ γ)).map f) → GlobalTheory.LevCmp.WtMatch (e.comp f) ρ₀ ρ' → GlobalTheory.LevCmp.WtMatch e ρ ρ' := by
  first | exact @GlobalTheory.BcMatch.bcmatch_main | exact GlobalTheory.BcMatch.bcmatch_main | (intros; apply GlobalTheory.BcMatch.bcmatch_main <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section
namespace GlobalTheory.LevCmp
open _root_.Formalism.L2.DIV GlobalTheory.CoefModel

section Gen2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem match_mtwRat (γ : GQ L n) : (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
    ((Formalism.L2.Col.mtwRat (L := L) (n := n) γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom :=
  (congrArg Units.val (Formalism.L2.Col.mtwInc_mtwRatFun γ)).symm

theorem domWeight_ext {N : ℕ} {a b : DomWeight N} (h : a.w = b.w) : a = b := by
  cases a; cases b; subst h; rfl

end Gen2


end GlobalTheory.LevCmp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexTypePlaceCharacterEqSuperdiagAddCharMulLo
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.XUniRead

section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem red_zero (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {q : ℕ} (hq : q.Prime)
    (red : v.adicCompletionIntegers (maximalRealSubfield L) →+* ZMod q)
    (y : v.adicCompletionIntegers (maximalRealSubfield L))
    (hy : Valued.v (y : v.adicCompletion (maximalRealSubfield L)) < 1) : red y = 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharZero (v.adicCompletion (maximalRealSubfield L)) :=
    charZero_of_injective_algebraMap (algebraMap (maximalRealSubfield L) _).injective
  have hp : (RingHom.ker red).IsPrime := RingHom.ker_isPrime red
  have hne : RingHom.ker red ≠ ⊥ := by
    intro h
    have h1 : ((q : ℕ) : v.adicCompletionIntegers (maximalRealSubfield L)) ∈ RingHom.ker red := by
      rw [RingHom.mem_ker, map_natCast, ZMod.natCast_self]
    rw [h, Ideal.mem_bot] at h1
    have h2 := congrArg (fun z : v.adicCompletionIntegers (maximalRealSubfield L) =>
      (z : v.adicCompletion (maximalRealSubfield L))) h1
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h2
    exact hq.ne_zero h2
  have hm : RingHom.ker red = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (hp.isMaximal hne)
  rw [← RingHom.mem_ker, hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨z, hz⟩ := hu.exists_right_inv
  have h2 := congrArg (fun z : v.adicCompletionIntegers (maximalRealSubfield L) =>
      Valued.v (z : v.adicCompletion (maximalRealSubfield L))) hz
  simp only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h2
  have hz1 : Valued.v (z : v.adicCompletion (maximalRealSubfield L)) ≤ 1 := z.2
  have h3 := mul_le_mul_right hz1 (Valued.v (y : v.adicCompletion (maximalRealSubfield L)))
  rw [h2, mul_one] at h3
  exact absurd hy (not_lt.2 h3)

private theorem intLift_coe (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (y : v.adicCompletionIntegers (maximalRealSubfield L)) :
    NX.intLift v (y : v.adicCompletion (maximalRealSubfield L)) = y := by
  unfold NX.intLift
  rw [dite_eq_left y.2]

private theorem sum_top {R : Type} [CommRing R] {n r : ℕ} (h : r ≤ n) (X : Matrix (Fin n) (Fin n) R) :
    (∑ a : Fin n, ∑ b : Fin n, if a.val + 1 = b.val ∧ b.val < r then X a b else 0) = NX.supSum r (NX.topR h X) := by
  unfold NX.supSum NX.topR
  symm
  refine Finset.sum_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _)
    (fun a _ ha => Finset.sum_eq_zero fun b _ => if_neg fun hh => ha ⟨⟨a.val, by omega⟩, by simp, Fin.ext rfl⟩) fun a _ => ?_
  refine Finset.sum_of_injOn (Fin.castLE h) (Fin.castLE_injective h).injOn (fun _ _ => Finset.mem_univ _)
    (fun b _ hb => if_neg fun hh => hb ⟨⟨b.val, hh.2⟩, by simp, Fin.ext rfl⟩) fun b _ => ?_
  refine if_congr ?_ rfl rfl
  simp only [Fin.val_castLE, b.2, and_true]
  exact eq_comm

private theorem supSum_small {R : Type} [CommRing R] {r : ℕ} (h : ¬ 2 ≤ r) (M : Matrix (Fin r) (Fin r) R) :
    NX.supSum r M = 0 := by
  unfold NX.supSum
  exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => if_neg (by have := b.2; omega)

private theorem loc_read (s : SplitPlace L) {n r : ℕ} (h : r ≤ n) {q : ℕ} (hq : q.Prime)
    (red : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* ZMod q)
    (x : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (hx : NG.UniRT s r x) :
    NX.IsUniTri r (NX.redMat s.v red (NX.topR h x.val)) ∧ IsUnit (red (NX.intLift s.v (NX.detT r x.val))) ∧
    ((NX.intLift s.v (NX.detT r x.val) : s.v.adicCompletionIntegers (maximalRealSubfield L)) :
      s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r x ∧
    ∃ y : s.v.adicCompletionIntegers (maximalRealSubfield L),
      (y : s.v.adicCompletion (maximalRealSubfield L)) = NG.supDiag s r x ∧
      red y = NX.supSum r (NX.redMat s.v red (NX.topR h x.val)) := by
  obtain ⟨⟨⟨X0, hX0⟩, hll⟩, huni⟩ := hx
  obtain ⟨X, hXu, hX⟩ : ∃ X : Matrix (Fin n) (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)),
      IsUnit X.det ∧ ∀ a b, x.val a b = (X a b : s.v.adicCompletion (maximalRealSubfield L)) :=
    ⟨X0.val, Matrix.isUnits_det_units X0, fun a b => by rw [← hX0]; rfl⟩
  have hr : ∀ a b, NX.redMat s.v red (NX.topR h x.val) a b = red (X (Fin.castLE h a) (Fin.castLE h b)) := fun a b => by
    simp only [NX.redMat, NX.topR, Matrix.submatrix_apply]
    rw [hX, intLift_coe]
  have hd : NX.detT r x.val = ((NX.detT r X : s.v.adicCompletionIntegers (maximalRealSubfield L)) :
      s.v.adicCompletion (maximalRealSubfield L)) := by
    unfold NX.detT
    refine Eq.trans ?_ (RingHom.map_det (s.v.adicCompletionIntegers (maximalRealSubfield L)).subtype _).symm
    congr 1
    exact Matrix.ext fun a b => hX _ _
  refine ⟨⟨fun a b hab => ?_, fun a => ?_⟩, ?_, ?_, NX.supSum r (NX.topR h X), ?_, ?_⟩
  · rw [hr]
    refine red_zero _ hq red _ ?_
    rw [← hX]
    exact (huni _ _ a.2 b.2).1 hab
  · rw [hr, ← sub_eq_zero, ← map_one red, ← map_sub]
    refine red_zero _ hq red _ ?_
    have := (huni (Fin.castLE h a) (Fin.castLE h a) a.2 a.2).2 rfl
    rw [hX] at this
    exact this
  · rw [hd, intLift_coe]
    have h1 := hXu.map red
    rw [RingHom.map_det, Matrix.twoBlockTriangular_det' (red.mapMatrix X) (fun a : Fin n => r ≤ a.val)
      (fun a ha b hb => red_zero _ hq red _ (by rw [← hX]; exact hll a b ha (not_le.1 hb)))] at h1
    have h2 := isUnit_of_mul_isUnit_left h1
    unfold NX.detT
    rw [RingHom.map_det]
    exact h2
  · rw [hd, intLift_coe, ← hd]
    rfl
  · unfold NG.supDiag
    rw [sum_top h]
    unfold NX.supSum
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact (hX _ _).symm
    · rfl
  · unfold NX.supSum
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact (hr _ _).symm
    · exact map_zero _

end Loc

end GlobalTheory.XUniRead

theorem _root_.GlobalTheory.T.complex_typePlaceCharacter_eq_superdiag_addChar_mul_lowerDet : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (kv0 : Σ kk : Fin 2, D.nd.PlG kk)
    (s : SplitPlace D.host.E) (red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv0.1))
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ),
    (∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (hu' : u ∈ Formalism.IndefR.NX.U D.nd),
      ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
        GlobalTheory.SeriesTie.sideEmb D.ntw i b ((psiUOf D.nd (NX.xiRed D) θ ⟨u, hu'⟩ : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (τ : (ZMod (D.host.g kv0.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (τ' : (ZMod (D.host.g kv0.1))ˣ →* (↥D.LL0)ˣ),
    (∀ x, ((τ x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = GlobalTheory.SeriesTie.sideEmb D.ntw i b ((τ' x : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (e : NX.Kk D i k →+* ℂ), SideRead i b k e →
    ∀ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ),
    (2 ≤ D.R.r → ∀ y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      ψ₀ (y : s.v.adicCompletion (maximalRealSubfield D.host.E)) =
        embLL0 D ((θ kv0.1 (Multiplicative.ofAdd (NX.xiRed D kv0 * red y)) : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ),
    (∀ (y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (hy : IsUnit (red y))
      (uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ), (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = y →
        ((ξ uu : ℂˣ) : ℂ) = embLL0 D ((τ' hy.unit : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (x : GL (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E))), NG.UniRT s D.R.r x →
    ∀ uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
      (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.detDD s D.R.r x →
      e (NX.gVal D i k b kv0 s red τ (x : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletion (maximalRealSubfield D.host.E)))) =
        ψ₀ (NG.supDiag s D.R.r x) * ((ξ uu : ℂˣ) : ℂ) := by
  intro D X i k b kv0 s red θ hpsi τ τ' hτ e he ψ₀ hψ₀ ξ hξ x hx uu huu
  classical
  obtain ⟨h1, h2, h3, y, hy, hry⟩ := GlobalTheory.XUniRead.loc_read s (n := D.R.nV) (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV)
    (D.host.g_prime kv0.1) red x hx
  unfold NX.gVal
  erw [dite_eq_left h2]
  rw [map_mul, hτ, he, hξ _ h2 uu (huu.trans h3.symm)]
  congr 1
  generalize hM : NX.redMat s.v red (NX.topR (Nat.le_add_right D.R.r D.R.t : D.R.r ≤ D.R.nV) x.val) = M
  erw [hM] at h1 hry
  have hdet : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular h1.1, Finset.prod_eq_one fun a _ => h1.2 a]
    exact isUnit_one
  have hval := NX.glOf_val M hdet
  generalize hu : (Pi.mulSingle kv0 (NX.glOf M) : G0g D.nd) = u
  have hu0 : (u kv0).val = M := by rw [← hu, Pi.mulSingle_eq_same, hval]
  have hu1 : ∀ kv, kv ≠ kv0 → (u kv).val = 1 := fun kv hkv => by rw [← hu, Pi.mulSingle_eq_of_ne hkv]; rfl
  have hm' : u ∈ Formalism.IndefR.NX.U D.nd := fun kv => by
    by_cases hkv : kv = kv0
    · subst hkv; rw [hu0]; exact h1
    · rw [hu1 kv hkv]; exact ⟨Matrix.blockTriangular_one, fun a => Matrix.one_apply_eq a⟩
  have hm : u ∈ D.nexp.U := by rw [X.U_eq]; exact hm'
  unfold NX.psiUTot
  rw [dite_eq_left hm, hpsi u hm hm', he, psiUOf_apply, Fintype.prod_eq_single kv0 (fun kv hkv => by
    rw [hu1 kv hkv, NX.supSum_one, mul_zero, ofAdd_zero, map_one]), hu0, ← hy]
  by_cases hr : 2 ≤ D.R.r
  · rw [hψ₀ hr y, hry]
  · have h0 : NG.supDiag s D.R.r x = 0 := by
      unfold NG.supDiag
      exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => if_neg (by omega)
    rw [hy, h0, GlobalTheory.XUniRead.supSum_small hr, mul_zero, ofAdd_zero, map_one, Units.val_one, map_one, AddChar.map_zero_eq_one]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionPairingRationalOnRationalPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BuRatOfCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalOrthogonalProjectionSemilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalOrthogonalProjectionSemilinear
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_rational_orthogonal_projection_of_finrank_le (K : Type) [Field K] (σ : K →+* ℂ) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W)
    (hj : ∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) :
    ∀ (d : ℕ) (N : Submodule K (Fin n → K)), Module.finrank K N ≤ d → ∀ (x : Fin n → K),
      ∃ y ∈ N, ∀ m ∈ N, ⟪j m, j x - j y⟫_ℂ = 0 := by
  intro d
  induction d with
  | zero =>
    intro N hN x
    refine ⟨0, N.zero_mem, ?_⟩
    have hb : N = ⊥ := by
      rw [← Submodule.finrank_eq_zero]; omega
    intro m hm
    subst hb
    rw [Submodule.mem_bot] at hm
    subst hm
    simp
  | succ d ih =>
    intro N hN x
    by_cases h : ∃ v ∈ N, j v ≠ 0
    · obtain ⟨v, hvN, hv⟩ := h
      let f : (Fin n → K) →ₛₗ[σ] ℂ := (innerₛₗ ℂ (j v)).comp j
      have hf : ∀ z, f z = ⟪j v, j z⟫_ℂ := fun z => rfl
      let N' := N ⊓ LinearMap.ker f
      have hvv : ⟪j v, j v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv
      have hlt : N' < N := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro heq
        have hvN' : v ∈ N' := heq ▸ hvN
        have h2 : f v = 0 := hvN'.2
        rw [hf] at h2
        exact hvv h2
      have hN' : Module.finrank K N' ≤ d := by
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      obtain ⟨a, ha⟩ := hj v v
      obtain ⟨b, hb⟩ := hj v x
      have hsa : σ a ≠ 0 := by rw [ha]; exact hvv
      obtain ⟨y', hy'N, hy'⟩ := ih N' hN' (x - (b / a) • v)
      refine ⟨(b / a) • v + y', N.add_mem (N.smul_mem _ hvN) (inf_le_left (a := N) hy'N), ?_⟩
      have key : j x - j ((b / a) • v + y') = j (x - (b / a) • v) - j y' := by
        simp only [map_add (f := _), map_sub]; abel
      rw [key]
      have hy'k : ⟪j v, j y'⟫_ℂ = 0 := by
        have : f y' = 0 := hy'N.2
        rwa [hf] at this
      have hv0 : ⟪j v, j (x - (b / a) • v) - j y'⟫_ℂ = 0 := by
        rw [inner_sub_right, map_sub, inner_sub_right, hy'k, map_smulₛₗ, inner_smul_right, ← ha, ← hb,
          map_div₀, div_mul_cancel₀ _ hsa]
        ring
      intro m hm
      obtain ⟨e, he⟩ := hj v m
      have hm' : m - (e / a) • v ∈ N' := by
        refine ⟨N.sub_mem hm (N.smul_mem _ hvN), ?_⟩
        show f (m - (e / a) • v) = 0
        rw [hf, map_sub, inner_sub_right, map_smulₛₗ, inner_smul_right, ← ha, ← he, map_div₀,
          div_mul_cancel₀ _ hsa, sub_self]
      have hsplit : j m = σ (e / a) • j v + j (m - (e / a) • v) := by
        rw [map_sub, map_smulₛₗ]; abel
      rw [hsplit, inner_add_left, inner_smul_left, hv0, mul_zero, zero_add]
      exact hy' _ hm'
    · push_neg at h
      refine ⟨0, N.zero_mem, ?_⟩
      intro m hm
      rw [h m hm, inner_zero_left]

theorem exists_mem_sub_mem_orthogonal_span_of_inner_mem_range : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W), (∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) → ∀ (N : Submodule K (Fin n → K)) (x : Fin n → K), ∃ y ∈ N, j x - j y ∈ (Submodule.span ℂ (j '' (N : Set (Fin n → K))))ᗮ := by
  intro K _ σ W _ _ _ n j hj N x
  obtain ⟨y, hyN, hy⟩ := exists_rational_orthogonal_projection_of_finrank_le K σ W n j hj _ N le_rfl x
  refine ⟨y, hyN, ?_⟩
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨m, hm, rfl⟩ := hu
    exact hy m hm
  | zero => exact inner_zero_left _
  | add u w _ _ hu hw => rw [inner_add_left, hu, hw, add_zero]
  | smul c u _ hu => rw [inner_smul_left, hu, mul_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalOrthogonalProjectionSemilinearStatement
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_orthogonal_projection_semilinear : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (n : ℕ) (j : (Fin n → K) →ₛₗ[σ] W), (∀ x y, ⟪j x, j y⟫_ℂ ∈ Set.range σ) → ∀ (N : Submodule K (Fin n → K)) (x : Fin n → K), ∃ y ∈ N, j x - j y ∈ (Submodule.span ℂ (j '' (N : Set (Fin n → K))))ᗮ := by
  first | exact @GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range | exact GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range | (intros; apply GlobalTheory.exists_mem_sub_mem_orthogonal_span_of_inner_mem_range <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Matrix
open scoped InnerProductSpace

namespace GlobalTheory

theorem buRat_of_coordinates : ∀ (D : D7) (μ : D.what₂.Tup), μ = D.what₂.mu0 → ∀ {n nV d : ℕ} (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ) (V : Matrix (Fin n) (Fin nV) D.what₂.LL) (Pq : Matrix (Fin d) (Fin nV) D.what₂.LL) (eRR : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V) (a : D.what₂.Word → ℕ) (eNu : ∀ u, (Fin (a u) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), Formalism.BasicNotions.Rows.BuDefQ D.what₂ → (∀ x y, ⟪jA x, jA y⟫_ℂ ∈ Set.range D.what₂.embLL) → D.what₂.V0 μ = Submodule.span ℂ (Set.range fun F0 => jA (V.mulVec F0)) → (∀ F0, D.what₂.iota μ (jA (V.mulVec F0)) = D.jEE (eRR (Pq.mulVec F0))) → Function.Surjective Pq.mulVec → (∀ u x F0, D.what₂.perCol u μ (D.jN u (eNu u x)) (jA (V.mulVec F0)) ∈ Set.range D.what₂.embLL) → Formalism.MainNotions.WeightDegreeSizes.RationalMapValues D := by
  intro D μ hμ n nV d jA V Pq eRR a eNu hB hinner hV hι hPq hper
  subst hμ
  intro u φ x
  obtain ⟨x', rfl⟩ := (eNu u).surjective φ
  obtain ⟨y, rfl⟩ := eRR.surjective x
  obtain ⟨G, rfl⟩ := hPq y
  have key := span_range_inf_ker_le_of_basis D.what₂.embLL D.div.RR.b (jA.comp V.mulVecLin) D.jEE
    (D.what₂.iota D.what₂.mu0) (eRR.toLinearMap ∘ₗ Pq.mulVecLin) D.jEE_basis.1 hι
  have hset : {x | (eRR.toLinearMap ∘ₗ Pq.mulVecLin) x = 0} = ((LinearMap.ker Pq.mulVecLin : Submodule D.what₂.LL (Fin nV → D.what₂.LL)) : Set (Fin nV → D.what₂.LL)) := by
    ext z
    simp
  have hU : D.what₂.Usp D.what₂.mu0 = Submodule.span ℂ ((jA.comp V.mulVecLin) ''
      ((LinearMap.ker Pq.mulVecLin : Submodule D.what₂.LL (Fin nV → D.what₂.LL)) : Set (Fin nV → D.what₂.LL))) := by
    rw [← hset, ← key, Formalism.BasicNotions.Rows.Data.Usp, hV]
    rfl
  obtain ⟨G', hG', hperp⟩ := GlobalTheory.T.exists_rational_orthogonal_projection_semilinear D.what₂.LL D.what₂.embLL (D.what₂.Amb D.what₂.mu0) nV (jA.comp V.mulVecLin)
    (fun x y => hinner _ _) (LinearMap.ker Pq.mulVecLin) G
  have hG'0 : Pq.mulVec G' = 0 := hG'
  set q : D.what₂.Amb D.what₂.mu0 := jA (V.mulVec (G - G')) with hq
  have hqeq : q = (jA.comp V.mulVecLin) G - (jA.comp V.mulVecLin) G' := by
    rw [hq, ← map_sub]
    rfl
  have hqV : q ∈ D.what₂.V0 D.what₂.mu0 := by
    rw [hV]
    exact Submodule.subset_span ⟨G - G', rfl⟩
  have hqU : q ∈ (D.what₂.Usp D.what₂.mu0)ᗮ := by
    rw [hU, hqeq]
    exact hperp
  have hqQ : q ∈ D.what₂.Qsp D.what₂.mu0 := ⟨hqV, hqU⟩
  have hιq : D.what₂.iota D.what₂.mu0 q = D.jEE (eRR (Pq.mulVec G)) := by
    rw [hq, hι, Matrix.mulVec_sub, hG'0, sub_zero]
  obtain ⟨z, hz⟩ := hper u x' (G - G')
  refine ⟨z, ?_⟩
  rw [hB u, ← hιq, D.what₂.sec_iota _ q hqQ, hz]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionPairingRationalOnRationalPoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3

theorem divisionPairing_rational_on_rationalPoints : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y), Pins R F cG → Holds R F → Formalism.MainNotions.WeightDegreeSizes.RationalMapValues D := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z C hPins hHolds
  have hR := complex_data_conditions_base_level_of_primitive_links hHolds.ok hHolds.sep hPins.char hHolds.prim
  have hW := hR.wf true
  have h2 := (hR.what₂ true).1
  have hI := (GlobalTheory.T.rowSide_definition_both_levels hC D G Pl0 I0 T A3 Ks R F cG X0 Y Z hPins hHolds).1
  have hPq := hW.Pq_surj A3.fam3.base3.μ0
  have hV := GlobalTheory.range_op_eq_span_of_formsTie D.what₂.embLL (Y.jA A3.fam3.base3.μ0) _ _ _
      (rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0) (Y.formsA A3.fam3.base3.μ0)
      (GlobalTheory.range_goodProjector_eq_range_goodCoordinates D A3.A 1 hHolds.ok.ok2 F.P1 F.ψ1 A3.fam3.base3.μ0)
  have hι : ∀ G0, D.what₂.iota (Y.tup A3.fam3.base3.μ0) (Y.jA A3.fam3.base3.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0).mulVec G0)) =
      D.jEE (Z.eRR (((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0).mulVec G0)) := by
    intro G0
    have h := hI.iota A3.fam3.base3.μ0 G0
    rw [Formalism.BasicNotions.Examples₂.NZ.sharp_iota] at h
    refine h.trans ?_
    show D.jEE (Z.eRR (((R.toCx3 F).rowMat F.cr true A3.fam3.base3.μ0).mulVec _)) = _
    rw [CxData.rowMat_base _ F.cr true h2]
    exact congrArg (fun v => D.jEE (Z.eRR v)) (Matrix.one_mulVec _)
  exact GlobalTheory.buRat_of_coordinates D (Y.tup A3.fam3.base3.μ0) Y.tup0 (Y.jA A3.fam3.base3.μ0)
    (rV0 D A3.A F.P1 F.ψ1 A3.fam3.base3.μ0) ((F.fc (R.toCx3 F).zs).Df1.Pq A3.fam3.base3.μ0) Z.eRR
    (fun u => (F.Dc (R.toCx3 F).zs).a (C.wU u)) C.eNu Y.bu
    (fun x y => ⟨_, ((Y.formsA A3.fam3.base3.μ0).inner x y).symm⟩) hV hι hPq
    (fun u x F0 => ⟨_, C.pt u A3.fam3.base3.μ0 x F0⟩)

end GlobalTheory.Mem.R3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionPairingRationalOnRationalPointsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisionPairing_rational_on_rationalPoints' : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (C : ReadC R F X0 Y), Pins R F cG → Holds R F → Formalism.MainNotions.WeightDegreeSizes.RationalMapValues D := by
  first | exact @GlobalTheory.Mem.R3.divisionPairing_rational_on_rationalPoints | exact GlobalTheory.Mem.R3.divisionPairing_rational_on_rationalPoints | (intros; apply GlobalTheory.Mem.R3.divisionPairing_rational_on_rationalPoints <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlacesUnionRamifiedPlacesFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlacesUnionRamifiedPlacesFinite
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem overPl_subsingleton {L : Type} [Field L] (w : HeightOneSpectrum (𝓞 L)) :
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) | NG.OverPl w v}.Subsingleton := by
  intro v hv v' hv'
  exact HeightOneSpectrum.ext (hv.symm.trans hv')

theorem placesOver_finite_of_ne_zero (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem gPl_union_qPl_finite : ∀ (D : D7) (η : HChar D.host.E), (gPl D ∪ qPl D η).Finite := by
  intro D η
  have hS : (⋃ k : Fin 2, placesOver D.host.E (D.host.g k)).Finite :=
    Set.finite_iUnion fun k => placesOver_finite_of_ne_zero _ _ (D.host.g_prime k).ne_zero
  have hR : {w | ¬ η.UnrAt w}.Finite := GlobalTheory.Mem.UnrAe.finite_ramified η
  refine Set.Finite.union ?_ ?_
  · refine (hS.biUnion fun w _ => (overPl_subsingleton w).finite).subset ?_
    rintro v ⟨w, hw, k, hk⟩
    exact Set.mem_biUnion (Set.mem_iUnion.2 ⟨k, hk⟩) hw
  · refine (hR.biUnion fun w _ => (overPl_subsingleton w).finite).subset ?_
    rintro v ⟨_, w, hw, hu⟩
    exact Set.mem_biUnion (x := w) hu hw

end GlobalTheory.LevCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlacesUnionRamifiedPlacesFiniteStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaces_union_ramifiedPlaces_finite : ∀ (D : D7) (η : HChar D.host.E), (gPl D ∪ qPl D η).Finite := by
  first | exact @GlobalTheory.LevCmp.gPl_union_qPl_finite | exact GlobalTheory.LevCmp.gPl_union_qPl_finite | (intros; apply GlobalTheory.LevCmp.gPl_union_qPl_finite <;> assumption)
end
end
