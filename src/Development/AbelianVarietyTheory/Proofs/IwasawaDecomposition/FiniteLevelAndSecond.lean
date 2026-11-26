module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstructionStartingChoicesOfFineAdelicData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BareStatementOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionToLocalLanglandsA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StatementCOfCasselmanWallach
public import Development.AutomorphicArithmetic.UnitTensorPairings.GaloisRepTransportOfCopyAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lb1OfRestagingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Detects
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSumLeOfLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientIntegralFramedPointCompleteField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistOfSeedCharacterPowers
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistOfSeedCharacterPowers
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.GoodPrimeSelection

theorem heq_sigma_app {P P' Tw Tw' Y Y' : Type} (hP : P = P') (hTw : Tw = Tw') (hY : Y = Y')
    {RCG : Tw → Finset Y → Type} {RCG' : Tw' → Finset Y' → Type} {gR : ∀ i Q, CommGroup (RCG i Q)} {gR' : ∀ i Q, CommGroup (RCG' i Q)}
    {Ok : Tw → ℕ → Type} {Ok' : Tw' → ℕ → Type} {cO : ∀ i k, CommRing (Ok i k)} {cO' : ∀ i k, CommRing (Ok' i k)}
    (hRCG : HEq RCG RCG') (hgR : HEq gR gR') (hOk : HEq Ok Ok') (hcO : HEq cO cO')
    {twI : P → Tw} {twI' : P' → Tw'} (h1 : HEq twI twI') {Q : P → Finset Y} {Q' : P' → Finset Y'} (h2 : HEq Q Q')
    {k : P → ℕ} {k' : P' → ℕ} (h3 : HEq k k')
    {psi : ∀ w, RCG (twI w) (Q w) →* (Ok (twI w) (k w))ˣ} {psi' : ∀ w, RCG' (twI' w) (Q' w) →* (Ok' (twI' w) (k' w))ˣ}
    (h4 : HEq psi psi') {w : P} {w' : P'} (hw : HEq w w') :
    HEq (⟨twI w, Q w, k w, psi w⟩ : Σ (i : Tw) (Q : Finset Y) (k : ℕ), RCG i Q →* (Ok i k)ˣ)
      (⟨twI' w', Q' w', k' w', psi' w'⟩ : Σ (i : Tw') (Q : Finset Y') (k : ℕ), RCG' i Q →* (Ok' i k)ˣ) := by
  subst hP hTw hY
  cases hRCG; cases hgR; cases hOk; cases hcO; cases h1; cases h2; cases h3; cases h4; cases hw
  rfl

theorem heq_sigma_pow {Tw Tw' Y Y' : Type} (hTw : Tw = Tw') (hY : Y = Y')
    {RCG : Tw → Finset Y → Type} {RCG' : Tw' → Finset Y' → Type} {gR : ∀ i Q, CommGroup (RCG i Q)} {gR' : ∀ i Q, CommGroup (RCG' i Q)}
    {Ok : Tw → ℕ → Type} {Ok' : Tw' → ℕ → Type} {cO : ∀ i k, CommRing (Ok i k)} {cO' : ∀ i k, CommRing (Ok' i k)}
    (hRCG : HEq RCG RCG') (hgR : HEq gR gR') (hOk : HEq Ok Ok') (hcO : HEq cO cO')
    {p : Σ (i : Tw) (Q : Finset Y) (k : ℕ), RCG i Q →* (Ok i k)ˣ} {p' : Σ (i : Tw') (Q : Finset Y') (k : ℕ), RCG' i Q →* (Ok' i k)ˣ}
    (hp : HEq p p') (b : Bool) (c : ℤ) :
    HEq (⟨p.1, p.2.1, p.2.2.1, BlochKatoReduction.Gen.psiAt b (p.2.2.2 ^ c)⟩ : Σ (i : Tw) (Q : Finset Y) (k : ℕ), RCG i Q →* (Ok i k)ˣ)
      (⟨p'.1, p'.2.1, p'.2.2.1, BlochKatoReduction.Gen.psiAt b (p'.2.2.2 ^ c)⟩ : Σ (i : Tw') (Q : Finset Y') (k : ℕ), RCG' i Q →* (Ok' i k)ˣ) := by
  subst hTw hY
  cases hRCG; cases hgR; cases hOk; cases hcO; cases hp
  rfl

theorem disjoint_of_heq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H')
    {A B : Finset (PlE H)} {A' B' : Finset (PlE H')} (hA : HEq A A') (hB : HEq B B') (h : Disjoint A B) : Disjoint A' B' := by
  subst hR; cases hH; cases hA; cases hB; exact h

theorem plE_eq {R R' : Ranks} (hR : R = R') {H : Host R} {H' : Host R'} (hH : HEq H H') : PlE H = PlE H' := by
  subst hR; cases hH; rfl

theorem auxiliaryPrime_eq_of_same_ranks_host {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) : AbsolutelyIrreducibleSpan.q0 D = AbsolutelyIrreducibleSpan.q0 D' := by
  cases D; cases D'
  dsimp only at hR hH
  subst hR; cases hH
  rfl

theorem discr_eq {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) :
    (NumberField.discr D.host.E).natAbs.primeFactors = (NumberField.discr D'.host.E).natAbs.primeFactors := by
  cases D; cases D'
  dsimp only at hR hH
  subst hR; cases hH
  rfl

theorem mem_avD_iff {D : D7} (i : D.ntw.Tw) (v : PlE D.host) :
    v ∈ avD D (avDesign D) i ↔ ∃ p ∈ avPrimes D ∪ avPrimesDesign D i, v ∈ placesOver D.host.E p := by
  classical
  unfold avD
  rw [Finset.mem_union, mem_avRec, mem_avDesign]
  constructor
  · rintro (⟨p, hp, hv⟩ | ⟨p, hp, hv⟩)
    · exact ⟨p, Finset.mem_union_left _ hp, hv⟩
    · exact ⟨p, Finset.mem_union_right _ hp, hv⟩
  · rintro ⟨p, hp, hv⟩
    rcases Finset.mem_union.1 hp with hp | hp
    · exact Or.inl ⟨p, hp, hv⟩
    · exact Or.inr ⟨p, hp, hv⟩

theorem avD_heq {D D' : D7} (h : SameExport D D') {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') :
    HEq (avD D (avDesign D) i) (avD D' (avDesign D') i') := by
  have hl : D.ntw.l i = D'.ntw.l i' := ((same_basic h.gal h.set h.frm).2.2.2.2 i i' hi).1
  have hd : avPrimesDesign D i = avPrimesDesign D' i' := by
    unfold avPrimesDesign
    rw [hl, auxiliaryPrime_eq_of_same_ranks_host h.gal.R h.gal.host, discr_eq h.gal.R h.gal.host]
  refine heq_places h.gal.R h.gal.host (s := avPrimes D ∪ avPrimesDesign D i) (mem_avD_iff i) ?_
  intro v
  rw [mem_avD_iff i' v, h.av, hd]

def normE {D : D7} (xd : ThData D) (h : XdAll xd) : IntegralHeckeForms.XD D where
  Dat0 i j b := if 1 ≤ j ∧ j ≤ D.R.m then Set.univ else ∅
  theta_base_equivariant i j b a ha u := by
    by_cases hj : 1 ≤ j ∧ j ≤ D.R.m
    · exact xd.thetaBase_invariant_action i j b a (by rw [h i j b hj.1 hj.2]; trivial) u
    · rw [if_neg hj] at ha
      exact ha.elim

theorem normE_eq {D : D7} (xd : ThData D) (h : XdAll xd) :
    ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, (normE xd h).Dat0 i j b = (twEOf xd).Dat0 i j b := by
  intro i j hj b
  rw [Finset.mem_Icc] at hj
  show (if 1 ≤ j ∧ j ≤ D.R.m then Set.univ else ∅) = xd.xd0 i j b
  rw [if_pos hj, h i j b hj.1 hj.2]

theorem heq_ite_univ {T T' : Type} (hT : T = T') {Dat : T → ℕ → Bool → Type} {Dat' : T' → ℕ → Bool → Type}
    (hD : HEq Dat Dat') {m m' : ℕ} (hm : m = m') :
    HEq (fun i j b => (if 1 ≤ j ∧ j ≤ m then Set.univ else ∅ : Set (Dat i j b)))
      (fun i j b => (if 1 ≤ j ∧ j ≤ m' then Set.univ else ∅ : Set (Dat' i j b))) := by
  subst hT hm; cases hD; rfl

theorem normE_heq {D D' : D7} (h : SameExport D D') (xd : ThData D) (hx : XdAll xd) (xd' : ThData D') (hx' : XdAll xd') :
    HEq (normE xd hx).Dat0 (normE xd' hx').Dat0 :=
  heq_ite_univ (eq_of_heq h.set.Tw) h.frm.Dat (by rw [h.gal.R])

theorem goodTw_swap {D : D7} {E E' : IntegralHeckeForms.XD D} (hE : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, E.Dat0 i j b = E'.Dat0 i j b)
    {N0 : D.ntw.Tw → ℕ} {i : D.ntw.Tw} {e : ℝ} {S : ∀ (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)}
    {A Q : Finset (PlE D.host)} {k : ℕ} {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ}
    (h : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S A Q k ψ) : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E' N0 i e S A Q k ψ := by
  unfold IntegralHeckeForms.GoodTw at h ⊢
  obtain ⟨h1, ⟨eB, h0, hs, hI⟩, h3, h4⟩ := h
  refine ⟨h1, ⟨eB, h0, hs, fun j hj b => ?_⟩, fun j hj b => ?_, h4⟩
  · have := hI j hj b
    unfold IntegralHeckeForms.SgJ at this ⊢
    rwa [← hE i j hj b]
  · have := h3 j hj b
    unfold IntegralHeckeForms.SgJ at this ⊢
    rwa [← hE i j hj b]

theorem ok_swap {D : D7} {I I' : TwIn D} (hE : ∀ i, ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b, I.E.Dat0 i j b = I'.E.Dat0 i j b)
    (hS : I.S = I'.S) {i : D.ntw.Tw} (h : I.Ok i) : I'.Ok i := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun j hj b => ?_, fun j hj b => ?_⟩
  · have := h1 j hj b
    unfold TwIn.Sg IntegralHeckeForms.SgJ IntegralHeckeForms.FullRk at this ⊢
    rw [← hE i j hj b]
    exact this
  · have := h2 j hj b
    unfold TwIn.Sg IntegralHeckeForms.SgJ at this ⊢
    rw [← hE i j hj b, ← hS]
    exact this

theorem good_pack {D D' : D7} (h : SameExport D D') {I : TwIn D} {I' : TwIn D'} (hE : HEq I.E.Dat0 I'.E.Dat0)
    (hN : HEq I.N0 I'.N0) (hS : HEq I.S I'.S) {p : TwPack D} {p' : TwPack D'} (hp : HEq p p')
    {A : Finset (PlE D.host)} {A' : Finset (PlE D'.host)} (hA : HEq A A')
    (hg : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 p.1 (twEps D p.1) (I.S p.1) A p.2.1 p.2.2.1 p.2.2.2) :
    IntegralHeckeForms.GoodTw D'.nexp (BlochKatoReduction.bk0 D') I'.E I'.N0 p'.1 (twEps D' p'.1) (I'.S p'.1) A' p'.2.1 p'.2.2.1 p'.2.2.2 := by
  obtain ⟨-, -, -, h1, h2⟩ := same_basic h.gal h.set h.frm
  obtain ⟨h3, h4, h5, h6⟩ := h1 p p' hp
  obtain ⟨h7, h8, -⟩ := h2 _ _ h3
  obtain ⟨i, Q, k, ψ⟩ := p
  obtain ⟨i', Q', k', ψ'⟩ := p'
  dsimp only at h3 h4 h5 h6 h7 h8 hg ⊢
  subst h5
  have he : twEps D' i' = twEps D i := by rw [twEps, twEps, h7]
  rw [he]
  exact goodTw_transfer h.gal h.set h.frm (B := BlochKatoReduction.bk0 D) (B' := BlochKatoReduction.bk0 D') h.br rfl rfl hE hN h3 _ (h8 _ _ hS).1 hA h4 k h6 hg

theorem psiAt_pow_pow {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) (a c : ℤ) :
    ∃ e : ℤ, e.natAbs = a.natAbs * c.natAbs ∧ BlochKatoReduction.Gen.psiAt b ((ψ ^ a) ^ c) = ψ ^ e := by
  obtain ⟨e, he, h⟩ := Formalism.MainNotions.N.TwAll.psiAt_side_zpow true b ψ (a * c)
  refine ⟨e, by rw [he, Int.natAbs_mul], ?_⟩
  rw [← zpow_mul, h]
  simp [BlochKatoReduction.Gen.psiAt]

theorem goodO_of_seed : ∀ (D₁ D₂ D₃ : D7) (A : D₁.ntw.Tw → Finset (PlE D₁.host)) (σ : Seed D₁ A) (C₂ : NChoice D₂)
    (C₃ : NChoice D₃) (xd : ThData D₃) (u : D₃.what₂.places.Pl → D₁.what₂.places.Pl), SameExport D₁ D₂ → Kept C₂ C₃ →
    avPrimes D₂ = avPrimes D₃ → D₂.what₂.places.Pl = D₃.what₂.places.Pl → XdAll xd → (∀ i, avD D₁ (avDesign D₁) i ⊆ A i) →
    (∀ v₂ v₃, HEq v₂ v₃ → TwistedAt D₃ v₃ → TwistedAt D₁ (u v₃) ∧ ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l (σ.s (u v₃))) ∧
      HEq (rawPack C₂ v₂) (GlobalTheory.HeightCounting.twPackPow D₁ a (σ.pack (u v₃)))) → GoodO D₃ C₃ xd := by
  intro D₁ D₂ D₃ A σ C₂ C₃ xd u h12 hK hav hPl hxd hA hu
  have h23 : SameExport D₂ D₃ := ⟨hK.gal, hK.set, hK.forms, hK.br, hav⟩
  have h13 : SameExport D₁ D₃ := h12.trans h23
  obtain ⟨hTw, -, hSS, hcomp, hsame⟩ := same_basic h13.gal h13.set h13.frm
  have hY : PlE D₁.host = PlE D₃.host := plE_eq h13.gal.R h13.gal.host

  have key : ∀ v, TwistedAt D₃ v → TwistedAt D₁ (u v) ∧ ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l (σ.s (u v))) ∧
      HEq (GlobalTheory.HeightCounting.twPackPow D₁ a (σ.pack (u v))) (rawPack C₃ v) := by
    intro v hv
    obtain ⟨ht, a, ha, hp⟩ := hu (cast hPl.symm v) v (cast_heq _ _) hv
    refine ⟨ht, a, ha, hp.symm.trans ?_⟩
    exact heq_sigma_app (RCG := D₂.ntw.RCG) (RCG' := D₃.ntw.RCG) (gR := D₂.ntw.grpRCG) (gR' := D₃.ntw.grpRCG)
      (Ok := D₂.ntw.Ok) (Ok' := D₃.ntw.Ok) (cO := D₂.ntw.crOk) (cO' := D₃.ntw.crOk)
      hPl (eq_of_heq hK.set.Tw) (plE_eq hK.gal.R hK.gal.host) hK.set.RCG hK.set.grpRCG hK.set.Ok hK.set.crOk
      hK.twI hK.Q hK.k hK.psi (cast_heq _ _)
  have hN0 : (D₁.ntw.Tw → ℕ) = (D₃.ntw.Tw → ℕ) := by rw [hTw]
  let I₁ : TwIn D₁ := ⟨normE σ.xd σ.all, σ.N0, σ.S⟩
  let In : TwIn D₃ := ⟨normE xd hxd, cast hN0 σ.N0, cast hSS σ.S⟩
  let I₃ : TwIn D₃ := ⟨twEOf xd, cast hN0 σ.N0, cast hSS σ.S⟩
  have hE : HEq I₁.E.Dat0 In.E.Dat0 := normE_heq h13 σ.xd σ.all xd hxd
  have hN : HEq I₁.N0 In.N0 := (cast_heq _ _).symm
  have hS : HEq I₁.S In.S := (cast_heq _ _).symm
  have h1n : ∀ i, ∀ j ∈ Finset.Icc 1 D₁.R.m, ∀ b, (twEOf σ.xd).Dat0 i j b = (normE σ.xd σ.all).Dat0 i j b :=
    fun i j hj b => (normE_eq σ.xd σ.all i j hj b).symm
  have h3n : ∀ i, ∀ j ∈ Finset.Icc 1 D₃.R.m, ∀ b, In.E.Dat0 i j b = I₃.E.Dat0 i j b := normE_eq xd hxd

  have pw : ∀ v, TwistedAt D₃ v → ∀ c : ℤ, Nat.Coprime c.natAbs (D₃.ntw.l (C₃.twI v)) →
      ∀ (B₁ : Finset (PlE D₁.host)) (B₃ : Finset (PlE D₃.host)), HEq B₁ B₃ → B₁ ⊆ A (σ.s (u v)) →
      I₃.Ok (C₃.twI v) ∧ IntegralHeckeForms.GoodTw D₃.nexp (BlochKatoReduction.bk0 D₃) I₃.E I₃.N0 (C₃.twI v) (twEps D₃ (C₃.twI v)) (I₃.S (C₃.twI v)) B₃
        (C₃.Q v) (C₃.k' v) (BlochKatoReduction.Gen.psiAt (C₃.sd v) (C₃.psi' v ^ c)) := by
    intro v hv c hc B₁ B₃ hB hBA
    obtain ⟨ht, a, ha, hp⟩ := key v hv
    have hl : D₁.ntw.l (σ.s (u v)) = D₃.ntw.l (C₃.twI v) := (hsame _ _ (hcomp _ _ hp).1).1
    have hq := heq_sigma_pow (RCG := D₁.ntw.RCG) (RCG' := D₃.ntw.RCG) (gR := D₁.ntw.grpRCG) (gR' := D₃.ntw.grpRCG)
      (Ok := D₁.ntw.Ok) (Ok' := D₃.ntw.Ok) (cO := D₁.ntw.crOk) (cO' := D₃.ntw.crOk)
      hTw hY h13.set.RCG h13.set.grpRCG h13.set.Ok h13.set.crOk hp (C₃.sd v) c
    obtain ⟨e, he, hpe⟩ := psiAt_pow_pow (C₃.sd v) (σ.ψ (σ.s (u v))) a c
    have hce : Nat.Coprime e.natAbs (D₁.ntw.l (σ.s (u v))) := by
      rw [he]
      exact Nat.Coprime.mul_left ha (hl ▸ hc)
    obtain ⟨hok, hg⟩ := σ.good (u v) ht
    have g1 := goodTw_swap h1n (hg e hce)
    rw [← hpe] at g1
    have g2 : IntegralHeckeForms.GoodTw D₁.nexp (BlochKatoReduction.bk0 D₁) I₁.E I₁.N0 (σ.s (u v)) (twEps D₁ (σ.s (u v))) (I₁.S (σ.s (u v))) B₁
        (σ.Q (σ.s (u v))) (σ.k (σ.s (u v))) (BlochKatoReduction.Gen.psiAt (C₃.sd v) ((σ.ψ (σ.s (u v)) ^ a) ^ c)) :=
      expGood_anti (I := I₁) (p := ⟨σ.Q (σ.s (u v)), σ.k (σ.s (u v)), _⟩) hBA g1
    have ok1 : I₁.Ok (σ.s (u v)) := ok_swap (I := ⟨twEOf σ.xd, σ.N0, σ.S⟩) (I' := I₁) h1n rfl hok
    have g3 := good_pack h13 hE hN hS hq hB g2
    have ok3 := (SameExport.good h13 hE hN hS hq
      ⟨ok1, expGood_anti (I := I₁) (p := ⟨σ.Q (σ.s (u v)), σ.k (σ.s (u v)), _⟩)
        ((avRec_subset_avD D₁ (avDesign D₁) _).trans (hA _)) g1⟩).1
    exact ⟨ok_swap h3n rfl ok3, goodTw_swap h3n g3⟩
  refine ⟨⟨I₃, rfl, fun v hv => ?_, fun v hv _ => ?_⟩, fun v v' hv hv' hne => ?_⟩
  · obtain ⟨ht, a, ha, hp⟩ := key v hv
    exact ⟨(pw v hv 1 (by simp) _ _ h13.avRec ((avRec_subset_avD D₁ (avDesign D₁) _).trans (hA _))).1,
      fun c hc => (pw v hv c hc _ _ h13.avRec ((avRec_subset_avD D₁ (avDesign D₁) _).trans (hA _))).2⟩
  · obtain ⟨ht, a, ha, hp⟩ := key v hv
    have h := (pw v hv 1 (by simp) _ _ (avD_heq h13 (hcomp _ _ hp).1) (hA _)).2
    rw [zpow_one] at h
    exact h
  · obtain ⟨ht, a, ha, hp⟩ := key v hv
    obtain ⟨ht', a', ha', hp'⟩ := key v' hv'
    obtain ⟨hi, hQ, -, -⟩ := hcomp _ _ hp
    obtain ⟨hi', hQ', -, -⟩ := hcomp _ _ hp'
    refine disjoint_of_heq h13.gal.R h13.gal.host hQ hQ' (σ.sep (u v) (u v') ht ht' fun he => hne ?_)
    exact eq_of_heq ((hi.symm.trans (heq_of_eq he)).trans hi')

end GlobalTheory.HeightCounting.Up.GoodPrimeSelection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistOfSeedCharacterPowersStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodTwist_of_seed_character_powers : ∀ (D₁ D₂ D₃ : D7) (A : D₁.ntw.Tw → Finset (PlE D₁.host)) (σ : Seed D₁ A) (C₂ : NChoice D₂) (C₃ : NChoice D₃) (xd : ThData D₃) (u : D₃.what₂.places.Pl → D₁.what₂.places.Pl), SameExport D₁ D₂ → Kept C₂ C₃ → avPrimes D₂ = avPrimes D₃ → D₂.what₂.places.Pl = D₃.what₂.places.Pl → XdAll xd → (∀ i, avD D₁ (avDesign D₁) i ⊆ A i) → (∀ v₂ v₃, HEq v₂ v₃ → TwistedAt D₃ v₃ → TwistedAt D₁ (u v₃) ∧ ∃ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l (σ.s (u v₃))) ∧ HEq (rawPack C₂ v₂) (GlobalTheory.HeightCounting.twPackPow D₁ a (σ.pack (u v₃)))) → GoodO D₃ C₃ xd := by
  first | exact @GlobalTheory.HeightCounting.Up.GoodPrimeSelection.goodO_of_seed | exact GlobalTheory.HeightCounting.Up.GoodPrimeSelection.goodO_of_seed | (intros; apply GlobalTheory.HeightCounting.Up.GoodPrimeSelection.goodO_of_seed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsAtOfPlUnder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.Mem.Top.TwChar (plUnder incl embLL_incl mem_plUnder)

theorem readsAt_of_plUnder (X X' : Stages) (h : Enl X.B X'.B) (hc : Carried X.toD7 X'.toD7) (v' : X'.B.places.Pl)
    (i : X.toD7.ntw.Tw) (i' : X'.toD7.ntw.Tw) (b : Bool) (hi : HEq i i')
    (hr : ReadsAt (D := X.toD7) i b (plUnder h v')) : ReadsAt (D := X'.toD7) i' b v' := by
  intro x'

  have hx : X'.B.embLL ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) ∈ X'.B.embLL '' (X'.B.LL0 : Set X'.B.LL) :=
    ⟨_, (x' : ↥X'.toD7.LL0).2, rfl⟩
  rw [h.2.2.1] at hx
  obtain ⟨y, hy, hye⟩ := hx
  have hint' : IsIntegral ℤ (X.B.embLL y) := by
    rw [hye]
    exact (RingOfIntegers.isIntegral_coe x').map
      ((X'.toD7.what₂.embLL.comp (algebraMap ↥X'.toD7.LL0 X'.toD7.what₂.LL)).toIntAlgHom)
  have hint : IsIntegral ℤ (⟨y, hy⟩ : ↥X.toD7.LL0) := by
    refine (isIntegral_algHom_iff ((X.toD7.what₂.embLL.comp (algebraMap ↥X.toD7.LL0 X.toD7.what₂.LL)).toIntAlgHom) ?_).1 (by exact hint')
    exact X.toD7.what₂.embLL.injective.comp (algebraMap ↥X.toD7.LL0 X.toD7.what₂.LL).injective
  let x : 𝓞 ↥X.toD7.LL0 := ⟨⟨y, hy⟩, hint⟩
  have e : X.toD7.what₂.embLL ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL) =
      X'.toD7.what₂.embLL ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) := hye

  obtain ⟨h1, h2⟩ := hc.emb i i' hi x x' e
  have hside : HEq (sideEmb i b (x : ↥X.toD7.LL0)) (sideEmb i' b (x' : ↥X'.toD7.LL0)) := by
    cases b
    · simpa [sideEmb] using h2
    · simpa [sideEmb] using h1
  have hleft := ((same_basic hc.exp.gal hc.exp.set hc.exp.frm).2.2.2.2 i i' hi).2.2 _ _ hside

  have hmap : RingOfIntegers.mapRingHom (incl h) (algebraMap (𝓞 ↥X.toD7.LL0) (𝓞 X.toD7.what₂.LL) x) =
      algebraMap (𝓞 ↥X'.toD7.LL0) (𝓞 X'.toD7.what₂.LL) x' := by
    apply RingOfIntegers.ext
    apply X'.B.embLL.injective
    exact (embLL_incl h ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL)).trans e
  have hright : 0 < X.toD7.what₂.places.val (plUnder h v') ((x : ↥X.toD7.LL0) : X.toD7.what₂.LL) ↔
      0 < X'.toD7.what₂.places.val v' ((x' : ↥X'.toD7.LL0) : X'.toD7.what₂.LL) := by
    refine (TwistChoice.val_pos_iff_mem X.toD7 (plUnder h v') x).trans
      (Iff.trans ?_ (TwistChoice.val_pos_iff_mem X'.toD7 v' x').symm)
    have hm := mem_plUnder h v' (algebraMap (𝓞 ↥X.toD7.LL0) (𝓞 X.toD7.what₂.LL) x)
    rw [hmap] at hm
    exact hm
  exact hleft.symm.trans ((hr x).trans hright)

end GlobalTheory.HeightCounting.Up
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsSymm
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations

theorem sameGalois_symm {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂} (h : SameGalois N N') :
    SameGalois N' N := ⟨h.R.symm, h.host.symm, h.loc.symm, h.Om.symm, h.instOm.symm, h.algOm.symm, h.plOm.symm, h.PlG.symm⟩

theorem twistDataAgreeAcrossCoefficients_symm {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'} (h : TwistDataAgreeAcrossCoefficients X X') : TwistDataAgreeAcrossCoefficients X' X :=
  ⟨h.cc.symm, h.Tw.symm, h.l.symm, h.O0.symm, h.crO0.symm, h.algO0.symm, h.topO0.symm, h.O.symm, h.crO.symm, h.algO.symm, h.Ok.symm, h.crOk.symm, h.algOk.symm, h.zk.symm, h.pD.symm, h.chi1.symm, h.Sig.symm, h.finSig.symm, h.jS.symm, h.side.symm, h.rhoS.symm, h.S0.symm, h.hEig.symm, h.abelian₂.symm, h.sideL.symm, h.RCG.symm, h.grpRCG.symm, h.finRCG.symm, h.art.symm, h.th.symm⟩

theorem sameForms_symm {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'} (h : SameForms Y Y') :
    SameForms Y' Y :=
  ⟨h.Fm.symm, h.acgFm.symm, h.modFmK.symm, h.modFmO.symm, h.actG.symm, h.U.symm, h.psiU.symm, h.eAlg.symm, h.Dat.symm, h.th.symm, h.lev.symm, h.thPsi.symm, h.MtV.symm, h.acgMt.symm, h.modMtK.symm, h.modMtO.symm, h.MtLat.symm, h.thP.symm, h.hkF.symm⟩

theorem heq_app {α α' β β' : Type} (hα : α = α') (hβ : β = β') {f : α → β} {f' : α' → β'} (hf : HEq f f') {x : α} {x' : α'}
    (hx : HEq x x') : HEq (f x) (f' x') := by
  subst hα; subst hβ
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hx
  rfl

theorem move_set {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂} (h1 : SameGalois N N')
    (B' : Finset (PlE D'.host)) : ∃ B : Finset (PlE D.host), HEq B B' ∧
      ∀ (Q : Finset (PlE D.host)) (Q' : Finset (PlE D'.host)), HEq Q Q' → Disjoint Q B → Disjoint Q' B' := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2
  exact ⟨B', HEq.rfl, fun Q Q' hQ h => by obtain rfl := eq_of_heq hQ; exact h⟩


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem move_pack {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'} (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X')
    {i : X.Tw} {i' : X'.Tw} (hi : HEq i i') {Q : Finset (PlE D.host)} {k : ℕ} (ψ : X.RCG i Q →* (X.Ok i k)ˣ) :
    ∃ (Q' : Finset (PlE D'.host)) (ψ' : X'.RCG i' Q' →* (X'.Ok i' k)ˣ), HEq Q Q' ∧ ∀ a : ℤ, HEq (ψ ^ a) (ψ' ^ a) := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hi
  exact ⟨Q, ψ, HEq.rfl, fun _ => HEq.rfl⟩


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem move_xd {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X') (h3 : SameForms Y Y') (m : ℕ)
    (x0 : ∀ i j b, Set (Y.Dat i j b))
    (hP : ∀ i j b, ∀ a ∈ x0 i j b, ∀ u : Y.U, Y.actG i j b u (Y.th i j b a) =
      ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • Y.th i j b a)
    (N0 : X.Tw → ℕ) (S : ∀ i j b, Finset (Y.Dat i j b)) :
    ∃ x0' : ∀ i j b, Set (Y'.Dat i j b), (∀ i j b, ∀ a ∈ x0' i j b, ∀ u : Y'.U, Y'.actG i j b u (Y'.th i j b a) =
      ((Y'.psiU i b u : (FractionRing (X'.O i))ˣ) : FractionRing (X'.O i)) • Y'.th i j b a) ∧ HEq x0 x0' ∧
      ((∀ i j b, 1 ≤ j → j ≤ m → x0 i j b = Set.univ) → ∀ i j b, 1 ≤ j → j ≤ m → x0' i j b = Set.univ) ∧
      (∃ N0' : X'.Tw → ℕ, HEq N0 N0') ∧ ∃ S' : ∀ i j b, Finset (Y'.Dat i j b), HEq S S' := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK, ymodMtO, yMtLat, ythP, yhkF⟩ := h3
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg yDat yth ylev ythPsi yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yU; subst ypsiU; subst yeAlg; subst yDat; subst yth; subst ylev; subst ythPsi; subst yMtV; subst yacgMt; subst ymodMtK; subst ymodMtO; subst yMtLat; subst ythP; subst yhkF
  exact ⟨x0, hP, HEq.rfl, id, ⟨N0, HEq.rfl⟩, S, HEq.rfl⟩

end GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations

namespace GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations

theorem exists_disjoint_choice {α ι : Type} [DecidableEq α] {Z : ι → Type} (c : ∀ i, Z i → Finset α) (P : ∀ i, Z i → Prop)
    (h : ∀ i (B : Finset α), ∃ z, P i z ∧ Disjoint (c i z) B) (T : Finset ι) :
    ∃ f : ∀ i, Z i, (∀ i, P i (f i)) ∧ ∀ i ∈ T, ∀ i' ∈ T, i ≠ i' → Disjoint (c i (f i)) (c i' (f i')) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    choose f hf using fun i => h i ∅
    exact ⟨f, fun i => (hf i).1, by simp⟩
  | insert a T ha ih =>
    obtain ⟨f, hf, hf'⟩ := ih
    obtain ⟨z, hz, hz'⟩ := h a (T.biUnion fun i => c i (f i))
    have key : ∀ i ∈ T, Disjoint (c a (Function.update f a z a)) (c i (Function.update f a z i)) := fun i hi => by
      rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hi)]
      exact Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem (fun i => c i (f i)) hi) hz'
    refine ⟨Function.update f a z, fun i => ?_, fun i hi i' hi' hne => ?_⟩
    · by_cases hi : i = a
      · subst hi; rwa [Function.update_self]
      · rw [Function.update_of_ne hi]; exact hf i
    · rcases Finset.mem_insert.1 hi with h1 | h1 <;> rcases Finset.mem_insert.1 hi' with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · subst h1; exact key i' h2
      · subst h2; exact (key i h1).symm
      · rw [Function.update_of_ne (by rintro rfl; exact ha h1), Function.update_of_ne (by rintro rfl; exact ha h2)]
        exact hf' i h1 i' h2 hne

theorem epsilon_congr {β : Type} {p q : β → Prop} (h1 h2 : Nonempty β) (h : p = q) :
    @Classical.epsilon _ h1 p = @Classical.epsilon _ h2 q := by
  subst h; rfl

end GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations

namespace GlobalTheory.HeightCounting.Up


open GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations in
set_option maxHeartbeats 4000000 in
theorem nonempty_seed_of_kept : ∀ (D₁ D₀ : D7) (C₁ : NChoice D₁) (C₀ : NChoice D₀) (xd : ThData D₀), Kept C₁ C₀ → D₁.what₂.places.Pl = D₀.what₂.places.Pl → (∀ v v₀, HEq v v₀ → TwistedAt D₁ v → TwistedAt D₀ v₀) → NChTie D₁ C₁ → (∀ v, C₁.twI (D₁.what₂.places.conj v) = C₁.twI v) → {v | TwistedAt D₁ v}.Finite → IsGalois ℚ ↥D₁.LL0 → (∀ v, TwistedAt D₀ v → D₀.ntw.NonzeroIndexPlace (C₀.twI v)) → ExportAt D₀ C₀ xd → XdAll xd → ∀ A, Nonempty (Seed D₁ A) := by
  intro D₁ D₀ C₁ C₀ xd hK hPl htw hT hc hfin hG hW hE hX A
  classical
  have g1 := sameGalois_symm hK.gal
  have g2 := twistDataAgreeAcrossCoefficients_symm hK.set
  have g3 := sameForms_symm hK.forms
  obtain ⟨N0, S, hp, hs⟩ := hE
  obtain ⟨x1, hx1P, hxd, hxall, ⟨N1, hN⟩, S1, hS⟩ := move_xd g1 g2 g3 D₀.R.m xd.xd0 xd.thetaBase_invariant_action N0 S
  let xd₁ : ThData D₁ := ⟨x1, hx1P⟩
  have hm : D₁.R.m = D₀.R.m := by rw [hK.gal.R]
  have hall : XdAll xd₁ := fun i j b h1 h2 => hxall hX i j b h1 (hm ▸ h2)
  have hTw : D₀.ntw.Tw = D₁.ntw.Tw := eq_of_heq g2.Tw
  obtain ⟨-, -, -, -, hb⟩ := same_basic g1 g2 g3
  have key : ∀ r, TwistedAt D₁ r → TwIn.Ok (⟨twEOf xd₁, N1, S1⟩ : TwIn D₁) (C₁.twI r) ∧
      ∀ B : Finset (PlE D₁.host), ∃ (Q : Finset (PlE D₁.host)) (k : ℕ)
        (ψ : D₁.ntw.RCG (C₁.twI r) Q →* (D₁.ntw.Ok (C₁.twI r) k)ˣ), ∀ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l (C₁.twI r)) →
          IntegralHeckeForms.GoodTw D₁.nexp (BlochKatoReduction.bk0 D₁) (twEOf xd₁) N1 (C₁.twI r) (twEps D₁ (C₁.twI r)) (S1 (C₁.twI r)) B Q k (ψ ^ a) := by
    intro r hr
    have hr₀ : TwistedAt D₀ (cast hPl r) := htw r (cast hPl r) (cast_heq hPl r).symm hr
    have hii : HEq (C₀.twI (cast hPl r)) (C₁.twI r) := heq_app hPl.symm hTw hK.twI.symm (cast_heq hPl r)
    obtain ⟨hl, hSS, -⟩ := hb _ _ hii
    obtain ⟨hSet, hOk⟩ := hs _ hr₀
    refine ⟨?_, fun B => ?_⟩
    · have h9 := fun j (hj : j ∈ Finset.Icc 1 D₁.R.m) b => fullRk_basisOf_transfer g1 g2 g3 (E := twEOf xd) (E' := twEOf xd₁)
        hxd hii j b ((hSS S S1 hS).2 j b) ⟨hOk.1 j (hm ▸ hj) b, hOk.2 j (hm ▸ hj) b⟩
      exact ⟨fun j hj b => (h9 j hj b).1, fun j hj b => (h9 j hj b).2⟩
    · obtain ⟨B₀, hB, -⟩ := move_set g1 B
      obtain ⟨Q₀, k, ψ₀, hG0⟩ := hp _ (hW _ hr₀) hSet _ (twEps_pos _ _) hOk.1 (S (C₀.twI (cast hPl r))) hOk.2 B₀
      obtain ⟨Q₁, ψ₁, hQ, hψ⟩ := move_pack g1 g2 hii ψ₀
      refine ⟨Q₁, k, ψ₁, fun a ha => ?_⟩
      have he : twEps D₁ (C₁.twI r) = twEps D₀ (C₀.twI (cast hPl r)) := by rw [twEps, twEps, hl]
      have ha' : IsCoprime a (D₀.ntw.l (C₀.twI (cast hPl r)) : ℤ) :=
        Int.isCoprime_iff_gcd_eq_one.2 (by rw [hl]; simpa [Int.gcd] using ha)
      rw [he]
      exact goodTw_transfer g1 g2 g3 (B := BlochKatoReduction.bk0 D₀) (B' := BlochKatoReduction.bk0 D₁) hK.br.symm rfl rfl hxd hN hii _
        (hSS S S1 hS).1 hB hQ k (hψ a) (hG0 a ha')
  let rep : D₁.what₂.places.Pl → D₁.what₂.places.Pl := fun v =>
    @Classical.epsilon _ ⟨v⟩ fun r => TwistedAt D₁ r ∧ OverOnePair D₁ v r
  have hrep : ∀ v, TwistedAt D₁ v → TwistedAt D₁ (rep v) ∧ OverOnePair D₁ v (rep v) := fun v hv =>
    Classical.epsilon_spec (p := fun r => TwistedAt D₁ r ∧ OverOnePair D₁ v r) ⟨v, hv, overOnePair_refl v⟩
  have hrep_eq : ∀ v v', OverOnePair D₁ v v' → rep v' = rep v := fun v v' h =>
    epsilon_congr _ _ (funext fun r => propext ⟨fun ⟨h1, h2⟩ => ⟨h1, h.trans hG h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, (h.symm hG).trans hG h2⟩⟩)
  let s : D₁.what₂.places.Pl → D₁.ntw.Tw := fun v => if TwistedAt D₁ v then C₁.twI (rep v) else C₁.twI v
  have hs_tw : ∀ v, TwistedAt D₁ v → s v = C₁.twI (rep v) := fun v hv => if_pos hv
  have hs_un : ∀ v, ¬ TwistedAt D₁ v → s v = C₁.twI v := fun v hv => if_neg hv
  let P : ∀ i : D₁.ntw.Tw, (Σ (Q : Finset (PlE D₁.host)) (k : ℕ), D₁.ntw.RCG i Q →* (D₁.ntw.Ok i k)ˣ) → Prop :=
    fun i z => ∀ r, TwistedAt D₁ r → C₁.twI r = i → ∀ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l i) →
      IntegralHeckeForms.GoodTw D₁.nexp (BlochKatoReduction.bk0 D₁) (twEOf xd₁) N1 i (twEps D₁ i) (S1 i) (A i) z.1 z.2.1 (z.2.2 ^ a)
  have hch : ∀ i (B : Finset (PlE D₁.host)), ∃ z, P i z ∧ Disjoint z.1 B := by
    intro i B
    by_cases hex : ∃ r, TwistedAt D₁ r ∧ C₁.twI r = i
    · obtain ⟨r, hr, rfl⟩ := hex
      obtain ⟨Q, k, ψ, hq⟩ := (key r hr).2 (A (C₁.twI r) ∪ B)
      refine ⟨⟨Q, k, ψ⟩, fun r' _ _ a ha => (goodTw_union (hq a ha)).1, ?_⟩
      have h1 := (goodTw_union (hq 1 (by simp))).2
      exact h1
    · exact ⟨⟨∅, 0, 1⟩, fun r hr he => absurd ⟨r, hr, he⟩ hex, Finset.disjoint_empty_left _⟩
  obtain ⟨f, hf, hf'⟩ := exists_disjoint_choice (Z := fun i => Σ (Q : Finset (PlE D₁.host)) (k : ℕ),
    D₁.ntw.RCG i Q →* (D₁.ntw.Ok i k)ˣ) (fun _ z => z.1) P hch (hfin.toFinset.image s)
  have goodAt : ∀ i, (∃ r, TwistedAt D₁ r ∧ C₁.twI r = i) → TwIn.Ok (⟨twEOf xd₁, N1, S1⟩ : TwIn D₁) i ∧
      ∀ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l i) →
        IntegralHeckeForms.GoodTw D₁.nexp (BlochKatoReduction.bk0 D₁) (twEOf xd₁) N1 i (twEps D₁ i) (S1 i) (A i) (f i).1 (f i).2.1 ((f i).2.2 ^ a) := by
    rintro i ⟨r, hr, rfl⟩
    exact ⟨(key r hr).1, hf _ r hr rfl⟩
  have hmem : ∀ v, TwistedAt D₁ v → s v ∈ hfin.toFinset.image s := fun v hv =>
    Finset.mem_image_of_mem s (hfin.mem_toFinset.2 hv)
  refine ⟨⟨s, fun v => ?_, fun v => ?_, fun v v' hv hv' ho => ?_, xd₁, hall, N1, S1, fun i => (f i).1, fun i => (f i).2.1,
    fun i => (f i).2.2, fun v hv => goodAt (s v) ⟨rep v, (hrep v hv).1, (hs_tw v hv).symm⟩,
    fun v v' hv hv' hne => hf' _ (hmem v hv) _ (hmem v' hv') hne⟩⟩
  · by_cases hv : TwistedAt D₁ v
    · rw [hs_tw v hv]
      exact ReadsAt.of_pair hG (readsAt_of_tie hT (rep v)) ((hrep v hv).2.symm hG)
    · exact ⟨C₁.sd v, by rw [hs_un v hv]; exact readsAt_of_tie hT v⟩
  · by_cases hv : TwistedAt D₁ v
    · rw [hs_tw v hv, hs_tw _ ((twistedAt_conj D₁ v).2 hv), hrep_eq v _ (overOnePair_conj v)]
    · rw [hs_un v hv, hs_un _ (fun h => hv ((twistedAt_conj D₁ v).1 h)), hc v]
  · rw [hs_tw v hv, hs_tw v' hv', hrep_eq v v' (Or.inl ho)]

end GlobalTheory.HeightCounting.Up
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GensJAlgebraic
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.L2.Col (qOf rowSG cAof cBof IsSel QE)

namespace GlobalTheory.Mem.Top.ReW

open GlobalTheory.Mem.Col2.JetEx

def stepSetJ (P : Pre) (J : AmbIn P.host) (χ : HChar P.host.E)
    (k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E))) : Set ℂ :=
  jetSet (hostAmb J (chiId χ)) (P.R.N k.2.1) (P.R.N (k.2.1 + 1)) k.2.2.1
    ((∏ Q ∈ k.2.2.2, qOf Q) ^ (P.R.m + 1) * (P.T k.1 * (∏ Q ∈ k.2.2.2, qOf Q) ^ (P.R.m + 1))) (totDeg P k.1 k.2.1)

def allSetJ (P : Pre) (J : AmbIn P.host) (χ : HChar P.host.E) (Ξ : Set (HChar P.host.E)) : Set ℂ :=
  ⋃ k ∈ {k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E)) |
      (k.2.1 < P.R.m ∧ (∀ Q ∈ k.2.2.1, Q ∈ badP P Ξ) ∧ ∀ Q ∈ k.2.2.2, Q ∈ badP P Ξ) ∧ FinAlg (stepSetJ P J χ k)}, stepSetJ P J χ k

theorem finAlg_allSetJ (P : Pre) (J : AmbIn P.host) (χ : HChar P.host.E) {Ξ : Set (HChar P.host.E)} (h : Ξ.Finite) :
    FinAlg (allSetJ P J χ Ξ) := by
  have hb := badPrimes_finite₂ P h
  have hs : {S : Finset (HeightOneSpectrum (𝓞 P.host.E)) | ∀ Q ∈ S, Q ∈ badP P Ξ}.Finite :=
    hb.toFinset.powerset.finite_toSet.subset fun S hS =>
      Finset.mem_coe.2 (Finset.mem_powerset.2 fun Q hQ => hb.mem_toFinset.2 (hS Q hQ))
  refine finAlg_biUnion ?_ fun k hk => hk.2
  exact (Set.finite_univ.prod ((Set.finite_Iio P.R.m).prod (hs.prod hs))).subset fun k hk => ⟨trivial, hk.1⟩


open Classical in
def gensJ (P : Pre) (J : AmbIn P.host) (χ : HChar P.host.E) (Ξ : Set (HChar P.host.E)) : Finset ℂ :=
  if h : FinAlg (allSetJ P J χ Ξ) then h.choose else ∅

theorem gensJ_algebraic (P : Pre) (J : AmbIn P.host) (χ : HChar P.host.E) (Ξ : Set (HChar P.host.E)) :
    ∀ z ∈ gensJ P J χ Ξ, IsAlgebraic ℚ z := by
  unfold gensJ
  split_ifs with h
  · exact h.choose_spec.1
  · simp

theorem allSetJ_subset (P : Pre) (J : AmbIn P.host) (χ : HChar P.host.E) {Ξ : Set (HChar P.host.E)} (h : Ξ.Finite)
    {K : Subfield ℂ} (hK : ∀ z ∈ gensJ P J χ Ξ, z ∈ K) : allSetJ P J χ Ξ ⊆ K := by
  have h1 := finAlg_allSetJ P J χ h
  rw [gensJ, dite_eq_left h1] at hK
  exact h1.choose_spec.2.trans (Subfield.closure_le.2 hK)

theorem jetsIn_of_isTw {B : Base} {X : PreX B.toPre} (hL : StagesInhab.HasLetters B.toPre) {I : ColIn B X} (h : I.Ok)
    (ht : TC.IsTw I) (hK : ∀ z ∈ gensJ B.toPre I.J I.C.chiPsi (Set.range I.xi), z ∈ B.embLL.fieldRange) : I.JetsIn := by
  have hall := allSetJ_subset B.toPre I.J I.C.chiPsi (Set.finite_range I.xi) hK
  refine I.jetsIn_iff.2 fun a u i hi N N' c x hx e he => ?_
  have hM : I.modulus a u = (∏ Q ∈ rowSG (B.primes X) I.sel (I.tup a), qOf Q) ^ (B.R.m + 1) *
      (B.T u * (∏ Q ∈ rowSG (B.primes X) I.sel (I.tup a), qOf Q) ^ (B.R.m + 1)) := by
    unfold ColIn.modulus cAof cBof
    rw [ht.cst_eq a, Finset.prod_coe_sort _ qOf]
    rfl
  have hS : stepSetJ B.toPre I.J I.C.chiPsi (u, i, I.Sb a u, rowSG (B.primes X) I.sel (I.tup a)) =
      jetSet I.A (B.R.N i) (B.R.N (i + 1)) (I.Sb a u) (I.modulus a u) (totDeg B.toPre u i) := by
    rw [hM, ColIn.A]
    exact (jetSet_amb B _ _ _ _ _ _ _).symm
  have hpos : 0 < I.modulus a u := by
    rw [hM]
    have := Finset.prod_pos fun Q (_ : Q ∈ rowSG (B.primes X) I.sel (I.tup a)) =>
      Nat.pos_of_ne_zero (by simpa using qPow_ne_zero Q 1 : qOf Q ≠ 0)
    have := (B.T_prime u).pos
    positivity
  refine hall (Set.mem_iUnion₂.2 ⟨(u, i, I.Sb a u, rowSG (B.primes X) I.sel (I.tup a)),
    ⟨⟨hi, Sb_subset h a u, rowSG_subset h a⟩, ?_⟩, ?_⟩)
  · rw [hS]
    exact finAlg_step hL h a u _ _ _ _ hpos
  · rw [hS]
    exact ⟨N, N', c, x, e, hx, degree_eq_totDeg B u i e he, rfl⟩

end GlobalTheory.Mem.Top.ReW

end

noncomputable section

open Formalism.L2.Col (qOf rowSG cAof cBof IsSel QE)

namespace GlobalTheory.Mem.Top.ReW

open GlobalTheory.Mem.Col2.InEx

theorem exists_bound : ∃ S : ∀ P : Pre, AmbIn P.host → Fr P → Set (HChar P.host.E) → Finset ℂ,
    (∀ P J g Ξ, ∀ z ∈ S P J g Ξ, IsAlgebraic ℚ z) ∧
    ∀ (B : Base) (X : PreX B.toPre) (f : Fr B.toPre) (T : TwDat B)
      (sel : HeightOneSpectrum (𝓞 B.fields.F) → HeightOneSpectrum (𝓞 B.fields.E)) (J : AmbIn B.host),
      (letI := B.host.cmStar; DiagSpaces B.sp) → (∀ u, (B.duStar u : ℝ) = duStarOf B.host (B.hcW u)) →
      StagesInhab.HasLetters B.toPre → Oriented X f.P → IsSel B.fields sel → J.Ok →
      (∀ z ∈ S B.toPre J f (T.set f), ∃ x : B.LL, B.embLL x = z) →
      ∃ I : ColIn B X, I.Ok ∧ TC.IsTw I ∧ I.JetsIn ∧ I.C = f ∧ I.S = avoid B.toPre ∧ Set.range I.xi = T.set f ∧
        I.sel = sel ∧ I.J = J ∧
        (∀ a P, ∃ z : B.LL, B.embLL z = (((I.xi a).val P : ℂˣ) : ℂ)) ∧
        (∀ a, ∀ P ∈ I.Q a, ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (𝓞 B.fields.E ⧸ P.asIdeal))) ∧
        GlobalTheory.Mem.Per.FieldOK B.host B.embLL B.embE := by
  classical
  choose M hM _ _ m1 m2 _ _ _ _ using fun (B : Pre) (f : Top.Fr B) =>
    FrameVal.frame_values B.R B.host _ f fun j τ => (B.hc τ).e_int j
  choose α hα gα using fun (B : Pre) (f : Top.Fr B) => @DatHecke.exists_gen (M B f) (hM B f)
  choose M' hM' _ hok using fun B : Pre => PerField.exists_fieldOK B.R B.host ⊥ inferInstance
  choose β hβ gβ using fun B : Pre => @DatHecke.exists_gen (M' B) (hM' B)
  choose r hr using fun q : ℕ => IsAlgClosed.exists_pow_nat_eq (q : ℂ) (n := 2) two_pos
  choose Z hZ gZ using fun (B : Pre) (Ξ : Set (HChar B.host.E)) => exists_holds (2 * B.R.m) Ξ
  refine ⟨fun P J g Ξ => insert (α P g) (insert (β P) (Z P Ξ ∪ (Finset.univ.image fun k => r (P.host.g k)) ∪
    gensJ P J g.chiPsi Ξ)), ?_, ?_⟩
  · intro P J g Ξ z hz
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hz
    rcases hz with rfl | rfl | ((h | ⟨k, rfl⟩) | h)
    · exact hα P g
    · exact hβ P
    · exact hZ P Ξ z h
    · exact IsAlgebraic.of_pow two_pos (by rw [hr]; exact isAlgebraic_natCast _)
    · exact gensJ_algebraic P J _ Ξ z h
  intro B X f T sel J hsp hdu hL hX hsel hJ hS
  have hα' := hS _ (Finset.mem_insert_self _ _)
  have hβ' := hS _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hZ' : ∀ z ∈ Z B.toPre (T.set f), ∃ x, B.embLL x = z := fun z hz => hS z (by simp [hz])
  have hr' : ∀ k, ∃ x, B.embLL x = r (B.host.g k) := fun k => hS _ (by simp)
  have hG' : ∀ z ∈ gensJ B.toPre J f.chiPsi (T.set f), ∃ x, B.embLL x = z := fun z hz => hS z (by simp [hz])
  have i1 := gα B.toPre f B.LL B.embLL hα'
  have hf := (TwFin.tw_fin B f T).1
  have ht := isTwist_of_mem_set B f T
  have hold : ∀ ξ ∈ T.set f, Holds B.embLL (2 * B.R.m) ξ := fun ξ hξ => gZ B.toPre _ hf B.LL B.embLL hZ' ξ hξ (ht ξ hξ).1
  obtain ⟨I0, h0, e1, e2, e3, e4, e5, hc⟩ := exists_colIn B X f hX hsp hdu (avoid B.toPre)
    (fun u => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Exists.intro u rfl))))), B.T_ne_pde u⟩)
    (fun i => ⟨Or.inr (Or.inl (Exists.intro i rfl)), (B.host.pde_ne_g i).1.symm, (B.host.pde_ne_g i).2.symm⟩)
    (fun _ hp h => mem_avoid_of_dvd _ hp h)
    _ hf (.inl (.inl rfl)) (.inl (.inr (.inl rfl))) (.inl (.inr (.inr rfl))) ht hold
    (fun j => valuesIn_of (m1 _ f j) _ i1) (valuesIn_of (m2 _ f) _ i1) (fun i => by
      obtain ⟨s, hs⟩ := hr' i
      exact ⟨s, B.embLL.injective (by rw [map_pow, hs, hr, map_natCast])⟩) sel hsel J hJ
  have hD : TC.Deep I0 := fun a P hP => by rw [(hc a).2.2.2 P hP]
  have hI : (TC.canon I0).Ok := TC.canon_ok h0 hD
  refine ⟨(TC.canon I0), hI, TC.canon_isTw I0, jetsIn_of_isTw hL hI (TC.canon_isTw I0) fun z hz => ?_, e1, e2, e3, e4, e5,
    fun a P => ?_, fun a P hP => ?_, hok B.toPre B.LL B.embLL B.embE B.embE_φ₀ (gβ B.toPre B.LL B.embLL hβ')⟩
  · have hz' : z ∈ gensJ B.toPre J f.chiPsi (T.set f) := by
      rw [show (TC.canon I0).J = J from e5, show (TC.canon I0).C = f from e1,
        show Set.range (TC.canon I0).xi = T.set f from e3] at hz
      exact hz
    exact RingHom.mem_fieldRange.2 (hG' z hz')
  · have hx : I0.xi a ∈ T.set f := e3 ▸ ⟨a, rfl⟩
    exact RingHom.mem_range.1 ((hold _ hx).1 _)
  · have hx : I0.xi a ∈ T.set f := e3 ▸ ⟨a, rfl⟩
    have htw : Chr.IsTwist B.host I0.S (I0.xi a) := e2 ▸ ht _ hx
    obtain ⟨P', hP', hn⟩ := exists_ram_of_mem_QE B h0.sel_ok (I0.tup a) htw (h0.xi_reads a) hP
    obtain ⟨ζ, hζ⟩ := ((hold _ hx).2 P' hP').2
    have hm := B.R.two_le_m
    have hq : 0 < Ideal.absNorm P'.asIdeal := Nat.pos_of_ne_zero fun h => P'.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    refine ⟨ζ ^ (Ideal.absNorm P'.asIdeal ^ (2 * B.R.m - 1)), ?_⟩
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hn]
    exact hζ.pow (pow_pos hq _) (by rw [← pow_succ]; congr 1; omega)

end GlobalTheory.Mem.Top.ReW

end

noncomputable section

namespace GlobalTheory.Mem.Top.ReW

open GlobalTheory.Mem.Col2.InEx

theorem valuesIn_lift {L : Type} [Field L] [NumberField L] {χ : HChar L} {s : ℝ} {C C' : Type} [Field C] [Field C']
    {σ : C →+* ℂ} {σ' : C' →+* ℂ} (h : χ.ValuesIn s σ) (hσ : ∀ y, ∃ x, σ' x = σ y) : χ.ValuesIn s σ' := fun v hv => by
  obtain ⟨y, hy⟩ := h v hv
  obtain ⟨x, hx⟩ := hσ y
  exact ⟨x, hx.trans hy⟩

theorem extend_pinned : EvG fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), K.Over B.toPre →
    Pinned K B f T w → ∃ (A : ℕ → Finset ℕ) (S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ),
    (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) ∧ ∀ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl B B' → HEq f' f →
    T'.Avoids A → (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) → ∃ w' : ColW B' f' T',
    Pinned K B' f' T' w' ∧ HEq w'.px w.px ∧ HEq w'.I.sel w.I.sel ∧ HEq w'.I.J w.I.J ∧ HEq w'.δ w.δ := by
  classical
  obtain ⟨S, hSa, hS⟩ := exists_bound
  refine evG_all fun K B f T w hO ⟨cp⟩ => ?_
  refine ⟨fun _ => ∅, fun P g Ξ => if h : P = B.toPre then S P (h ▸ w.I.J) g Ξ else ∅, fun P g Ξ z hz => ?_, ?_⟩
  · dsimp only at hz
    by_cases h : P = B.toPre
    · rw [dite_eq_left h] at hz
      exact hSa _ _ _ _ z hz
    · rw [dite_eq_right h] at hz
      simp at hz
  intro B' f' T' hE hf _ hS₂
  have hK := Enl.KsC_eq hE
  have hrng : ∀ y : B.LL0, ∃ x : B'.LL0, B'.embLL x = B.embLL y := fun y => by
    have : B.embLL y.1 ∈ B'.embLL '' (B'.LL0 : Set B'.LL) := hE.2.2.1 ▸ ⟨y.1, y.2, rfl⟩
    obtain ⟨x, hx, hxy⟩ := this
    exact ⟨⟨x, hx⟩, hxy⟩
  have hL := GlobalTheory.Mem.Col2.JetEx.hasLetters_of_over hO
  have hP := (base_fields_primes_ok B w.px).2.1
  have hX : Oriented w.px f.P := fun k v => by
    have h1 := w.ok.pibar k v
    rw [DatHecke.mem_vG hP, w.C_eq] at h1
    rw [← h1]
    exact (iff_of_eq (congrArg (· ∈ v.asIdeal) (RingOfIntegers.ext (B.fields_conjO_coe _)))).symm
  have hsp := of_over hO
  obtain ⟨⟨B0, C0, W0, V0, S0, N0, G0⟩, hB0, -⟩ := StagesInhab.exists_stages_over B hL 1
  dsimp only at hB0
  subst hB0
  have hv := w.val C0 W0 V0 S0 N0 G0
  have e1 := hE.1
  clear hE
  cases B0
  dsimp only at e1
  subst e1
  have ef := eq_of_heq hf
  subst ef
  dsimp only at hS₂
  rw [dite_eq_left rfl] at hS₂
  obtain ⟨I, hI, hTw, hJets, hC, hSS, hxi, hsel, hJ, hval, hroot, hfld⟩ :=
    hS B' w.px f' T' w.I.sel w.I.J hsp.1 hsp.2 hL hX w.ok.sel_ok w.ok.amb_ok hS₂
  have hval0 : ∀ C W V S N G, Formalism.L2.Host.ValLL0 (assemble B' C W V S N G) (Fr.at ⟨B', C, W, V, S, N, G⟩ f') :=
    fun C W V S N G => ⟨fun j => valuesIn_lift (hv.mu0 j) hrng, valuesIn_lift hv.eta hrng, valuesIn_lift hv.chiPsi hrng,
      valuesIn_lift hv.del hrng, valuesIn_lift hv.del' hrng⟩
  let w' : ColW B' f' T' :=
    { px := w.px
      I := I
      ok := hI
      C_eq := hC
      S_eq := hSS
      xi_range := hxi
      pins := ⟨w.pins.iX, w.pins.cof⟩
      l := TC.laws_of_ok I hI
      l0 := StepZero.law0 I hI _
      δ := w.δ
      exact := hK.trans w.exact
      fld := hfld
      val := hval0 }
  have cp' : ColPin w' :=
    { isTw := hTw
      jets := hJets
      hX := (base_fields_primes_ok B' w.px).1
      above := fun v => by rw [hsel]; exact cp.above v
      half := by rw [hsel]; exact cp.half
      d3b := cp.d3b
      selectedPlacesAgree := by rw [hsel]; exact cp.selectedPlacesAgree
      vals := fun a P _ => hval a P
      roots := hroot }
  exact ⟨w', ⟨cp'⟩, HEq.rfl, heq_of_eq hsel, heq_of_eq hJ, HEq.rfl⟩

end GlobalTheory.Mem.Top.ReW

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondGOfHalves
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem secondG_congr {α : Type*} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {f : Fr P} {f' : Fr P'} (h : P = P') (hf : HEq f f') :
    g P f = g P' f' := by
  subst h
  rw [eq_of_heq hf]

end GlobalTheory.Mem.Top.GroupRetwisting
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
open GlobalTheory.Mem.Top.TwChar (plUnder RootIso FrobPick avoidPlaces subset_avoidPlaces)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.Up

theorem pass_of {Q : V4.Slot} {p q r : AtP} (hp : Step KPx (fun _ _ _ _ => True) p) (hq : Step KPx (fun _ _ _ _ => True) q)
    (h : EvG fun K => ∀ B f T, K.Over B.toPre → KPx B f → T = TwDat.untw B T.pl → p K B f T →
      ∀ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
        (N : NStage B C W) (G : GJStage B C) (c : V4.Core K ⟨B, C, W, V, S, N, G⟩ f T), Q K ⟨B, C, W, V, S, N, G⟩ f T c →
        ExportAt (assemble B C W V S N G) c.O.nch c.O.xd →
        ∀ (A : ℕ → Finset ℕ) (S₂ : ∀ P : Pre, Fr P → Set (HChar P.host.E) → Finset ℂ), (∀ P g Ξ, ∀ z ∈ S₂ P g Ξ, IsAlgebraic ℚ z) →
          ∃ (B' : Base) (f' : Fr B'.toPre) (T' : TwDat B'), Enl B B' ∧ HEq f' f ∧ T'.pl = T.pl ∧ T'.Avoids A ∧
            (∀ z ∈ S₂ B'.toPre f' (T'.set f'), ∃ x : B'.LL, B'.embLL x = z) ∧ KPx B' f' ∧ (q K B' f' T' → r K B' f' T')) :
    Pass KPx Q r := by
  classical
  refine (EvG.inter (EvG.inter hp hq) h).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨hp, hq⟩, hr⟩ := H
  have hs' : large₂ K fun B f T => KPx B f → q K B f T :=
    (hq.inter (lg_forced K)).imp fun _ _ _ _ G a => G.1 a G.2 trivial
  obtain ⟨S₁, P₁, A₀, S₂₀, a₁, a₂, hlg⟩ := hs'
  have hb : large₂ K fun B f T => (∀ z ∈ S₁ B.toPre f B.KsC, z ∈ B.fixedCoefficientFieldInComplex) ∧ P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex ⊆ T.pl :=
    ⟨S₁, P₁, fun _ _ _ _ _ => ∅, S₂₀, a₁, a₂, fun _ _ _ _ h p _ => ⟨h.1, p⟩⟩
  refine (hp.inter hb).imp ?_
  rintro B f T hO ⟨hp, h₁, hpl₁⟩ hKP hT C W V S N G c q hx A S₂ hS₂
  obtain ⟨B', f', T', e, hf, hpl, hAv, hS', hK', hfin⟩ := hr B f T hO hKP hT (hp hKP c.forced trivial) C W V S N G c q hx
    (fun l => A l ∪ A₀ B.toPre f B.KsC B.fixedCoefficientFieldInComplex l) (fun P g Ξ => S₂ P g Ξ ∪ S₂₀ P g B.KsC B.fixedCoefficientFieldInComplex Ξ)
    (fun P g Ξ z hz => (Finset.mem_union.1 hz).elim (hS₂ P g Ξ z) (a₂ P g _ _ Ξ z))
  have hP : B'.toPre = B.toPre := e.1
  have hk : B'.KsC = B.KsC := e.KsC_eq
  have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := e.fixedCoefficientField_eq
  have hO' : K.Over B'.toPre := hP ▸ hO
  have hLL : ∀ z ∈ S₂₀ B'.toPre f' B'.KsC B'.fixedCoefficientFieldInComplex (T'.set f'), z ∈ B'.LLC := by
    intro z hz
    rw [hk, hl] at hz
    obtain ⟨x, rfl⟩ := hS' z (Finset.mem_union_right _ hz)
    exact ⟨x, rfl⟩
  have hq' := hlg B' f' T' hO'
    ⟨by rw [hk, hl, secondG_congr S₁ hP hf]; exact h₁, hLL⟩
    (by rw [hk, hl, secondG_congr P₁ hP hf, hpl]; exact hpl₁)
    (fun w v hv hA => hAv w v hv (Finset.mem_union_right _ (by
      rw [hk, hl, secondG_congr A₀ hP hf] at hA; exact hA))) hK'
  exact ⟨B', f', T', e, hf, hpl, fun w v hv hA => hAv w v hv (Finset.mem_union_left _ hA),
    fun z hz => hS' z (Finset.mem_union_left _ hz), hfin hq'⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

theorem muIsW_st {P : Pre2 K w} (x : St P) : V4.MuIsW (w.st x.o.Z) f T P.Wt w.I.xi :=
  { inj := w.ok.xi_inj
    range := w.xi_range
    mu0 := w.l.xi0
    star := by
      show w.I.xi w.I.muStar = f.del
      rw [w.ok.xi_star, w.C_eq]
    star' := by
      show w.I.xi w.I.muStar' = f.del'
      rw [w.ok.xi_star', w.C_eq]
    tw := P.q.mu.tw
    on := P.q.mu.on
    off := P.q.mu.off
    sub := P.sub
    supp := P.supp }

theorem twisted_st {P : Pre2 K w} (x : St P) (v : B.places.Pl) : TwistedAt (Dof x) v ↔ v ∈ P.Wt :=
  (TupTieW.tupTied_of_muIsW (w.st x.o.Z) f T P.Wt w.I.xi (muIsW_st x)).1 v

theorem below_plUnder {B' : Base} {f' : Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} (h : Enl B B') (Z : w.Lt) (Z' : w'.Lt)
    (v' : B'.places.Pl) : Below (w.D Z) (w'.D Z') (plUnder h v') v' := by
  intro x x' e
  have : x' = RingOfIntegers.mapRingHom (TwChar.incl h) x :=
    RingOfIntegers.ext (B'.embLL.injective (e.symm.trans (TwChar.embLL_incl h _).symm))
  subst this
  exact TwChar.mem_plUnder h v' x

theorem overOne_plUnder_of {B' : Base} {f' : Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} (h : Enl B B') (Z : w.Lt) (Z' : w'.Lt)
    {v₁ v₂ : B'.places.Pl} (ho : OverOne (w'.D Z') v₁ v₂) : OverOne (w.D Z) (plUnder h v₁) (plUnder h v₂) := by
  have hm : ∀ x : B.LL0, TwChar.incl h (x : B.LL) ∈ B'.LL0 := fun x => by
    obtain ⟨y, hy, e⟩ : B.embLL (x : B.LL) ∈ B'.embLL '' (B'.LL0 : Set B'.LL) := h.2.2.1 ▸ ⟨x, x.2, rfl⟩
    rwa [← B'.embLL.injective (e.trans (TwChar.embLL_incl h _).symm)]
  let j : B.LL0 →+* B'.LL0 := ((TwChar.incl h).comp B.LL0.val.toRingHom).codRestrict B'.LL0 hm
  intro x
  let x' : 𝓞 ↥(w'.D Z').LL0 := RingOfIntegers.mapRingHom j x
  have key : ∀ v : B'.places.Pl, 0 < (w.D Z).what₂.places.val (plUnder h v) ((x : ↥(w.D Z).LL0) : (w.D Z).what₂.LL) ↔
      0 < (w'.D Z').what₂.places.val v ((x' : ↥(w'.D Z').LL0) : (w'.D Z').what₂.LL) :=
    fun v => (val_pos_iff_mem (w.D Z) _ x).trans (((TwChar.mem_plUnder h v _).trans (iff_of_eq (congrArg
      (· ∈ HeightOneSpectrum.asIdeal v) (RingOfIntegers.ext rfl)))).trans (val_pos_iff_mem (w'.D Z') v x').symm)
  exact (key v₁).trans ((ho x').trans (key v₂).symm)

theorem exists_of_position {P : CP} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B} {c : V4.Core K X f T} (h : positionOf P K X f T c) :
    ExportAt X.toD7 c.O.nch c.O.xd → ∃ (w : ColW X.B f T) (Z : w.Lt) (c' : V4.Core K (w.st Z) f T), P K X.B f T w Z c' ∧
      ExportAt (w.st Z).toD7 c'.O.nch c'.O.xd :=
  positionOf_ind (R := fun K X f T c => ExportAt X.toD7 c.O.nch c.O.xd → ∃ (w : ColW X.B f T) (Z : w.Lt)
    (c' : V4.Core K (w.st Z) f T), P K X.B f T w Z c' ∧ ExportAt (w.st Z).toD7 c'.O.nch c'.O.xd)
    (fun _ _ _ _ w Z c h e => ⟨w, Z, c, h, e⟩) h

theorem SameGal.trans {D D' D'' : D7} (h : SameGal D D') (h' : SameGal D' D'') : SameGal D D'' :=
  ⟨⟨h.gal.R.trans h'.gal.R, h.gal.host.trans h'.gal.host, h.gal.loc.trans h'.gal.loc, h.gal.Om.trans h'.gal.Om,
    h.gal.instOm.trans h'.gal.instOm, h.gal.algOm.trans h'.gal.algOm, h.gal.plOm.trans h'.gal.plOm, h.gal.PlG.trans h'.gal.PlG⟩,
    h.pl.trans h'.pl⟩

theorem enl_refl (B : Base) : Enl B B := ⟨rfl, rfl, rfl, subset_rfl⟩

theorem avPrimes_st (Z Z' : w.Lt) : avPrimes (w.st Z).toD7 = avPrimes (w.st Z').toD7 := rfl

end GlobalTheory.HeightCounting.Up
