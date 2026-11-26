module

public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.LocalRingCardinality.SpanPowerMembership.RelDet
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
public import Formalism.LocalRingCardinality.SpanPowerMembership.GPlacesExampleNatAct
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtB
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.LocalRingCardinality.SpanPowerMembership.GatSetting

@[expose] public section

section -- merged from Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

structure LocalGap {R : Ranks} (H : Host R) where

  nloc : LocTheory

  nlocA : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (nloc l)

  nlocT : ∀ (l : ℕ) [Fact l.Prime], LocTied l (nloc l) (nlocA l)

theorem LocalGap.tame {R : Ranks} {H : Host R} (_G : LocalGap H) : TameHyp H := tameHyp H

def LocalGap.cd {R : Ranks} {H : Host R} (_G : LocalGap H) : CDHaar := CD.cdHaar

variable (H : Host R0) (T : ℕ) [hT : Fact T.Prime]

abbrev Tau0 : Type := ↥(R0.Psi)

theorem exampleClassGroupCard_pos {R : Ranks} (H : Host R) : 0 < exampleClassGroupCard H := by
  unfold exampleClassGroupCard
  refine Finset.prod_pos (fun k _ => pow_pos ?_ _)
  have : NeZero (H.g k) := ⟨(H.g_prime k).ne_zero⟩
  exact Nat.card_pos

abbrev rowsH : Rows.Data R0 :=
  toyRowsOfNumberField H.E H.φ₀ (@placesOf H.E _ _ H.cmStar) Tau0 card_examplePsi_eq (dstarOf T) (shaExample H)
    (shaExample_nonneg H) (exampleClassGroupCard H) (exampleClassGroupCard_pos H)

abbrev memT : Member R0 Tau0 (fun _ => hc0) := trivialMember Tau0 T (dstarOf T) (dstarOf_pos T)

theorem nHypH (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    NHyp H (rowsH H T) :=
  { hsha := fun p _ e _ _ => shaExample_eq H p e
    hcard := rfl
    hg := hg }

theorem normAt_empty {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] [IsEmpty ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x = 0 := by
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]

def spH (pz : H.E) (hpz : pz * H.conj pz = (T : H.E)) :
    @Spaces R0 H.F H.E _ _ _ _ H.cmStar _ :=
  letI := H.cmStar
  spacesExample star_isIntegral (cmData H) T hT.out pz
    (by rw [star_eq_conj H pz, mul_comm]; exact hpz)
    (exists_adelic_neg_one H (cmData H).sig (fun x => star_eq_conj H x))

abbrev sDataH (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H) :
    Formalism.MainNotions.S.Draft.SData R0 H.F H.E (conjF H) Unit Tau0 (fun _ _ => hc0) :=
  toySData (conjF H) (fun _ _ => hc0) 1 one_pos (fun _ _ l h => exampleWeight_cloud_gap_four l h)
    (fun _ _ l h => exampleWeight_middle_entries l h) (locAdj (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some))


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
def exampleRecordOfData
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
    (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
    (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
    (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
    (G : LocalGap H) : D7 :=
  letI : StarRing H.E := H.cmStar
  { R := R0
    host := H
    sp := spH H T pz hpz
    what₂ := rowsH H T
    eTau := Equiv.refl _
    hc := fun _ => hc0
    wordFin := inferInstanceAs (Fintype Unit)
    u₀ := ()
    hcW := fun _ _ => hc0
    hcW_base := rfl
    hcW_v := fun _ _ => rfl
    hcW_b := fun _ _ => rfl
    hcW_e := fun _ _ => rfl
    hcW_first := fun _ _ _ => rfl
    hcW_last := fun _ _ _ => rfl
    mem := fun _ => memT T
    nfLL := inferInstanceAs (NumberField H.E)
    starLL := H.cmStar
    tcLL := instTotallyComplex H
    galLL := instIsGalois H
    starLL_cx := fun x => emb_star H H.φ₀ x
    div := toyZeroLatticeDatum H.E
    div_good := ⟨(zeroHLat_good H.E).1, fun _ => (zeroHLat_good H.E).1⟩
    embE := RingHom.id _
    embE_φ₀ := rfl
    conjF := conjF H
    conjF_eq := conjF_apply H
    embE_conj := fun x => (star_eq_conj H x).symm
    LL0 := ⊤
    hostField_le_fixedField := fun _ => IntermediateField.mem_top
    O_contains := fun x => ⟨x, rfl⟩
    plEq := Equiv.refl _
    val_eq := placesOf_val_eq H.E
    ram_eq := placesOf_ram_eq H.E
    conj_val := placesOf_conj_val H.E
    T_level := fun _ => hlev
    T_norm := fun _ => ⟨pz, hK, hpz, hcong⟩
    sp_T := rfl
    cOf := fun _ => 1
    cOf_ne := fun _ => one_ne_zero
    cOf_eq := fun _ => by rw [map_one, one_mul, one_mul]
    T_win := fun _ => exampleLevel_near_lower Tau0 T
    GamP_eq := fun _ => rfl
    T_ne_pde := fun _ => hpde
    Dstar_eq := fun _ => rfl
    clsLat := fun _ _ c => Empty.elim c
    clsLat_lat := fun _ _ c => Empty.elim c
    eMu := fun _ => toyZeroSpaceEquiv Tau0 T (dstarOf T) (dstarOf_pos T)
    eMt := fun _ => toyZeroSpaceRefl
    perCol_base_eq_PtilCol := fun _ _ _ => rfl
    Bu_linL := fun _ _ => zero_isLinear
    Bu_linR := fun _ _ => zero_isLinear
    chTw := fun _ _ => (memT T).C
    memberColumns_twistedChain_base := fun _ => rfl
    e0Tw := fun _ _ => LinearEquiv.refl ℂ _
    PTw := fun _ _ => (memT T).P
    eMtTw := fun _ _ => toyZeroSpaceRefl
    perCol_tie := fun _ _ h => absurd rfl h
    vol := fun _ => 1
    vol_pos := fun _ => one_pos
    O_int := fun y => RingOfIntegers.isIntegral_coe y
    jEE := jZero H.E H.φ₀
    jEE_basis := jZero_basis H.E H.φ₀
    jN := fun _ => jZero H.E H.φ₀
    jN_basis := fun _ => jZero_basis H.E H.φ₀
    Dall_eq := rfl
    delP_eq := rfl
    Dt := ℂˣ
    detCls := fun _ _ _ => 1
    muTil := fun _ => 1
    chiD := MonoidHom.id _
    UO := ⊥
    chiD_UO := fun _ hx => Subgroup.mem_bot.mp hx
    e1Dt := exampleInverseEmbeddingProduct H (Equiv.refl Tau0)
    rest_detCharacter_on_unitary_eq := exampleCharacter_unitary_product H (Equiv.refl Tau0)
    relDet := fun N L L' => QuotientGroup.mk (relDetExample H (Equiv.refl Tau0) N L L')
    relDet_self := fun N L => by rw [relDetExample_self]; rfl
    relDet_mul := fun N L L' L'' => by rw [← QuotientGroup.mk_mul, relDetExample_mul]
    relDet_smul := fun N L L' γ h => congrArg _ (relDetExample_smul H (Equiv.refl Tau0) N L L' γ h)
    rhoDet_eq_inv_muTilde_chiD_pow := fun _ _ c => Empty.elim c
    rhoDetPrime_eq_muTilde_mul_chi_pow := fun _ i c => Empty.elim c
    dsig := toyConstantOne _
    dsig_pos := toyConstantOne_pos _
    s := sDataH H hg ht
    s_split := locAdj_split (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some)
    s_HH := toySData_HH _ _ _ _ _
    s_Cu := fun u => toySData_Cu _ _ _ _ _ u _ rfl
    s_PlF := toySData_PlF _ _ _ _ _
    loc := G.nloc
    locA := G.nlocA
    locT := G.nlocT
    nd := ndToy H (rowsH H T) (nHypH H T hg)
    ntw := ntwToy H ⊤ (nHypH H T hg)
    naut := nautToy H (rowsH H T) (nHypH H T hg)
    nbc := nbcToy H (rowsH H T) (nHypH H T hg)
    nexp := nexpToy H ⊤ (nHypH H T hg)
    ntypes := ntypesT H (rowsH H T) (nHypH H T hg) ht G.tame
    nStage_trivialCharacter_compat := @ntypesT_E0Tie _ H (rowsH H T) (nHypH H T hg)
      (fun _ => inferInstanceAs (Subsingleton Z0)) (fun _ _ => inferInstanceAs (Subsingleton Z0)) ht G.tame
    nth := nthToy H ⊤ (nHypH H T hg)
    nbr := fun i => Empty.elim i
    self_good := fun i => Empty.elim i
    ntwbr := fun i => Empty.elim i
    nbr_ind := fun i => Empty.elim i
    ntwbr_ind := fun i => Empty.elim i
    loc_tie := fun i => Empty.elim i
    bc_tie := fun i => Empty.elim i
    rbar_tie := fun i => Empty.elim i
    mtpar_tie := fun i => Empty.elim i
    jetW := fun i => Empty.elim i
    jetW_l := fun i => Empty.elim i
    jetTau := fun i => Empty.elim i
    jetW1 := fun i => Empty.elim i
    resChar_thetaJetPlaceDegOne := fun i => Empty.elim i
    jetTau1 := fun i => Empty.elim i
    nStage_trivialCharacter_coeff_eq := fun g => (map_zero H.φ₀).trans (newtypes_idempotent_zero H _ _ ht G.tame g).symm
    Z_tie := example_Z_compatibility H _ _
    Zgood_tie := example_goodZ_compatibility H _ _
    etaJ_tie := example_etaJ_compatibility H _ _ (fun _ _ => rfl)
    fm := fun _ => formsToy H.φ₀ (placesOf H.E) card_examplePsi_eq (memT T).C (memT T).A (memT T).P
    eMu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim φ 0, inner_zero_left]
      exact (Finset.sum_of_isEmpty _).symm
    nuIn := fun _ => 0
    nuIn_inj := fun _ x y _ => Subsingleton.elim (α := Fin 0 → H.E) x y
    nuIn_range := fun _ => Subsingleton.elim (α := Submodule H.E (Fin 0 → H.E)) _ _
    nuIn_jN := fun _ _ => funext fun c => Empty.elim c
    nuIn_norm := fun _ v x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (normAt_empty (ι := Fin 0) _ _ _ _).symm
    jEE_norm := fun x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (norm_zero (E := Z0)).symm
    sEE := ⟨0, fun x => (norm_zero (E := Z0)).trans
      ((norm_zero (E := Z0)).symm.trans (congrArg norm (Subsingleton.elim (α := Z0) 0 x)))⟩
    s_Cu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim (α := Z0) φ 0]
      exact (inner_zero_left (𝕜 := ℂ) (E := Z0) ψ).trans (Finset.sum_of_isEmpty _).symm
    cd := G.cd
    jet := jetToy R0 H
    jetU := fun i => Empty.elim i
    jetL := fun i => Empty.elim i
    jetL' := fun i => Empty.elim i
    jetU1 := fun i => Empty.elim i
    jetL1 := fun i => Empty.elim i
    jetL1' := fun i => Empty.elim i
    gx := gxExample _ _
    gat := fun _ _ _ => gAtPExample _
    gat_d := fun _ _ _ => (gAtPExample_d _).trans (finrank_bot ℂ _).symm
    Y_sigval := spacesExample_Ysig _ _ _ _ _ _ _ }

end Formalism.BasicNotions.Examples₂
end
end

section -- merged from Formalism.LocalRingCardinality.SpanPowerMembership.NZRowC
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions

abbrev En (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

section Rows

variable {R : Ranks} (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)
  (kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ)
  (tw : P.Pl → Bool) (htw : ∀ w, tw (P.conj w) = tw w)
  (Word : Type) (cI : Word → Type) [∀ u, Fintype (cI u)] (d Dall d0 : ℕ) (hd : d ≤ Dall)
  (FT : Type) [Fintype FT] [DecidableEq FT] (ft : Fin d → FT) (ft0 : Fin d0 → FT)
  (per : ∀ u : Word, Bool → EuclideanSpace ℂ (cI u) → En d → ℂ)
  (eta : ℕ → P.Pl → ℚ) (heta : ∀ j w, 0 ≤ eta j w)

end Rows

section RowsLemmas

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] {embLL : LL →+* ℂ} {P : Rows.Places LL}
  {Tau : Type} [Fintype Tau] {hTau : Fintype.card Tau = R.f} {Dst : ℝ}
  {sha : ℕ → ℕ → ℚ} {hsha : ∀ l e, 0 ≤ sha l e} {cg : ℕ} {hcg : 0 < cg}
  {kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ} {ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ}
  {tw : P.Pl → Bool} {htw : ∀ w, tw (P.conj w) = tw w}
  {Word : Type} {cI : Word → Type} [∀ u, Fintype (cI u)] {d Dall d0 : ℕ} {hd : d ≤ Dall}
  {FT : Type} [Fintype FT] [DecidableEq FT] {ft : Fin d → FT} {ft0 : Fin d0 → FT}
  {per : ∀ u : Word, Bool → EuclideanSpace ℂ (cI u) → En d → ℂ}
  {eta : ℕ → P.Pl → ℚ} {heta : ∀ j w, 0 ≤ eta j w}

end RowsLemmas

section Gen

variable {R : Ranks} (D : Rows.Data R)

end Gen

end Formalism.BasicNotions.Examples₂.NZ
end
end

section -- merged from Formalism.LocalRingCardinality.SpanPowerMembership.GatTies
noncomputable section

namespace Formalism.BasicNotions.Examples₂.LevelValuationRings

open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField QuadraticAlgebra

section Orbit

variable {G : Type} [Group G] [Finite G] (g : G)

abbrev Quo : Type := G ⧸ Subgroup.zpowers g

def eQuo : Fin (Nat.card (Quo g)) ≃ Quo g := (Finite.equivFin (Quo g)).symm


open Classical in
def secOf (T : Set G) (q : Quo g) : G :=
  if h : ∃ x ∈ T, (QuotientGroup.mk x : Quo g) = q then h.choose else q.out

theorem mk_secOf (T : Set G) (q : Quo g) : (QuotientGroup.mk (secOf g T q) : Quo g) = q := by
  unfold secOf
  split_ifs with h
  · exact h.choose_spec.2
  · exact QuotientGroup.out_eq' q

def orbFun (T : Set G) (x : Σ _ : Fin (Nat.card (Quo g)), Fin (orderOf g)) : G :=
  secOf g T (eQuo g x.1) * g ^ (x.2 : ℕ)

theorem orbFun_bij (T : Set G) : Function.Bijective (orbFun g T) := by
  have key : ∀ (q : Quo g) (n : ℕ), (QuotientGroup.mk (secOf g T q * g ^ n) : Quo g) = q := by
    intro q n
    have h1 : (QuotientGroup.mk (secOf g T q) : Quo g) = QuotientGroup.mk (secOf g T q * g ^ n) := by
      rw [QuotientGroup.eq, inv_mul_cancel_left]
      exact Subgroup.npow_mem_zpowers g n
    rw [← h1, mk_secOf]
  have hinj : Function.Injective (orbFun g T) := by
    rintro ⟨v1, s1⟩ ⟨v2, s2⟩ h
    simp only [orbFun] at h
    have hv : v1 = v2 := by
      have h3 := congrArg (fun y => (QuotientGroup.mk y : Quo g)) h
      simp only [key] at h3
      exact (eQuo g).injective h3
    subst hv
    have hs : g ^ (s1 : ℕ) = g ^ (s2 : ℕ) := mul_left_cancel h
    have h4 : (s1 : ℕ) = s2 := pow_injOn_Iio_orderOf s1.2 s2.2 hs
    rw [Fin.ext h4]
  refine hinj.bijective_of_nat_card_le ?_
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers g), Nat.card_zpowers,
    Nat.card_eq_fintype_card (α := Σ _ : Fin (Nat.card (Quo g)), Fin (orderOf g)), Fintype.card_sigma]
  simp

def orbEquiv (T : Set G) : (Σ _ : Fin (Nat.card (Quo g)), Fin (orderOf g)) ≃ G :=
  Equiv.ofBijective (orbFun g T) (orbFun_bij g T)

theorem orbEquiv_step (T : Set G) (v : Fin (Nat.card (Quo g))) (s : Fin (orderOf g)) :
    orbEquiv g T ⟨v, posAdd s 1⟩ = orbEquiv g T ⟨v, s⟩ * g := by
  show orbFun g T ⟨v, posAdd s 1⟩ = orbFun g T ⟨v, s⟩ * g
  simp only [orbFun, posAdd, pow_mod_orderOf, pow_succ, mul_assoc]

end Orbit

variable {R : Ranks} (H : Host R) (p : ℕ)

theorem of_cls (h : H.cls p = .inertClass) : p ∉ H.small ∧ p ≠ H.q ∧ p ≠ H.d ∧
    jacobiSym (-(H.d : ℤ)) p ≠ 1 ∧ H.psAt p ≠ 1 := by
  unfold Host.cls primeClass at h
  by_cases h1 : p ∈ H.small
  · rw [if_pos h1] at h
    cases h
  rw [if_neg h1] at h
  by_cases h2 : p = H.q
  · rw [if_pos h2] at h
    cases h
  rw [if_neg h2] at h
  by_cases h3 : p = H.d
  · rw [if_pos h3] at h
    cases h
  rw [if_neg h3] at h
  by_cases h4 : jacobiSym (-(H.d : ℤ)) p = 1
  · rw [if_pos h4] at h
    cases h
  rw [if_neg h4] at h
  by_cases h5 : H.psAt p = 1
  · rw [if_pos h5] at h
    cases h
  exact ⟨h1, h2, h3, h4, h5⟩

private theorem coprime_of_cls (hp : p.Prime) (hc : H.cls p = .inertClass) : p.Coprime H.condN := by
  obtain ⟨h2, hq, hd, -, -⟩ := of_cls H p hc
  have h1 : ¬ p ∣ H.QS := fun h => h2 (Nat.mem_primeFactors.2 ⟨hp, h, H.QS_pos.ne'⟩)
  exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.2 h1)
    ((Nat.coprime_primes hp H.hyp.1).2 hq)) ((Nat.coprime_primes hp H.hyp.2.1).2 hd)

def hOf : R.MA :=
  if h : p.Coprime H.condN then (H.art (ZMod.unitOfCoprime p h)).2 else 1

theorem hOf_of_coprime (h : p.Coprime H.condN) : hOf H p = (H.art (ZMod.unitOfCoprime p h)).2 := by
  rw [hOf, dite_eq_left h]

theorem unit_eq_neg_one (x : ℤˣ) (h : (x : ℤ) ≠ 1) : x = -1 := by
  rcases Int.units_eq_one_or x with hx | hx
  · rw [hx] at h
    exact absurd rfl h
  · exact hx

theorem frob_val (hp : p.Prime) (hc : H.cls p = .inertClass) (P : Ideal (𝓞 H.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    H.galE σ = (c0, hOf H p) := by
  have : Fact p.Prime := ⟨hp⟩
  have hco := coprime_of_cls H p hp hc
  obtain ⟨h2, hq, hd, hjd, hjq⟩ := of_cls H p hc
  obtain ⟨-, hiff, hval, -⟩ := H.der.frob p (hp.coprime_iff_not_dvd.1 hco) P
  obtain ⟨h1, h3, -⟩ := hval σ hσ
  have h4 := (hiff σ (ZMod.unitOfCoprime p hco) (ZMod.coe_unitOfCoprime p hco)).1 hσ
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · exact unit_eq_neg_one _ (by rw [h1]; exact hjq)
  · exact unit_eq_neg_one _ (by rw [h3]; exact hjd)
  · show (H.gal σ).2 = hOf H p
    rw [hOf_of_coprime H p hco, h4]

open Ideal in
theorem exists_frob (hp : p.Prime) (hc : H.cls p = .inertClass) :
    ∃ (P : Ideal (𝓞 H.E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P := by
  have : Fact p.Prime := ⟨hp⟩
  have hco := coprime_of_cls H p hp hc
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (span {(p : ℤ)}).IsPrime := (span_singleton_prime hpZ.ne_zero).2 hpZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((span {(p : ℤ)}).primesOver (𝓞 H.E)) := inferInstance
  obtain ⟨⟨σ, hσ⟩, -, -⟩ := H.der.frob p (hp.coprime_iff_not_dvd.1 hco) P
  exact ⟨P, hPp, hPl, σ, hσ⟩

theorem hOf_even (hp : p.Prime) (hc : H.cls p = .inertClass) (hn : HNeZero H p) :
    Even (orderOf (hOf H p)) := by
  obtain ⟨P, hP, hL, σ, hσ⟩ := exists_frob H p hp hc
  have h1 := @hn P hP hL σ hσ
  rwa [@frob_val R H p hp hc P hP hL σ hσ] at h1

def inPsi (φ : Formalism.HC.Frame) : φ.MA →* ↥φ.Psi :=
  (MonoidHom.inr G0 φ.MA).codRestrict φ.Psi (fun _ => rfl)

theorem inPsi_inj (φ : Formalism.HC.Frame) : Function.Injective (inPsi φ) := by
  intro a b h
  have h' := congrArg (fun x : ↥φ.Psi => (Subtype.val x).2) h
  exact h'

theorem order_spec (φ : Formalism.HC.Frame) (h : φ.MA) (h1 : Even (orderOf h)) :
    orderOf (inPsi φ h) = orderOf h ∧ 2 ≤ orderOf (inPsi φ h) ∧ Even (orderOf (inPsi φ h)) := by
  rw [orderOf_injective (inPsi φ) (inPsi_inj φ) h]
  refine ⟨rfl, ?_, h1⟩
  have hpos : 0 < orderOf h := orderOf_pos h
  obtain ⟨r, hr⟩ := h1
  omega

instance (φ : Formalism.HC.Frame) : Finite ↥φ.Psi := inferInstance

structure Served {R : Ranks} (H : Host R) (p : ℕ) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  cls : H.cls p = .inertClass
  hne : HNeZero H p

variable {H p}

def gPsi (S : Served H p) : ↥(R.Psi) := inPsi R.toFrame (hOf H p)

abbrev nOrb (S : Served H p) : ℕ := Nat.card (Quo (gPsi S))

def posPsi (S : Served H p) (T : Set ↥(R.Psi)) :
    (Σ _ : Fin (nOrb S), Fin (orderOf (gPsi S))) ≃ ↥(R.Psi) := orbEquiv (gPsi S) T

theorem posPsi_step (S : Served H p) (T : Set ↥(R.Psi)) (v : Fin (nOrb S))
    (s : Fin (orderOf (gPsi S))) : posPsi S T ⟨v, posAdd s 1⟩ = posPsi S T ⟨v, s⟩ * gPsi S :=
  orbEquiv_step (gPsi S) T v s

theorem ord_spec (S : Served H p) :
    orderOf (gPsi S) = orderOf (hOf H p) ∧
      2 ≤ orderOf (gPsi S) ∧ Even (orderOf (gPsi S)) :=
  order_spec R.toFrame (hOf H p) (hOf_even H p S.prime S.cls S.hne)

theorem k_pos (R : Ranks) : R.k - 1 + 1 = R.k := by
  have := R.m_add_three_le_k
  omega

def placesOf (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0)) :
    haveI : Fact p.Prime := ⟨S.prime⟩
    Places p (On p (orderOf (gPsi S))) (Kn p (orderOf (gPsi S))) :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  { w := ω
    nV := nOrb S
    n' := fun _ => orderOf (gPsi S)
    W := fun _ => Wn p (orderOf (gPsi S))
    Qq := fun _ => Qn p (orderOf (gPsi S))
    ι := fun _ => iotaN p _
    σ := fun _ => sigN p _
    j := fun _ => algebraMap _ _
    setting := fun _ => hidaSettingOfEven p _ S.five_le (ord_spec S).2.1 (ord_spec S).2.2
    m := R.k - 1
    r := r
    lam0 := fun v s i => (lam (posPsi S T ⟨v, s⟩)).w
      ⟨i.1, by have h1 := k_pos R; have h2 := i.2; simp only [Ranks.N]; omega⟩
    dom := fun v s a b hab => (lam (posPsi S T ⟨v, s⟩)).anti (show (_ : Fin _) ≤ _ from hab) }

theorem orderOf_frobenius_image_eq (S : Served H p) (P : Ideal (𝓞 H.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    orderOf (gPsi S) = orderOf (H.galE σ).2 := by
  rw [(ord_spec S).1, @frob_val R H p S.prime S.cls P _ _ σ hσ]

theorem position_succ_eq_mul_frobenius (S : Served H p) (T : Set ↥(R.Psi)) {Tau : Type} (eTau : Tau ≃ ↥(R.Psi))
    (v : Fin (nOrb S)) (s : Fin (orderOf (gPsi S))) (P : Ideal (𝓞 H.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E) (hσ : IsArithFrobAt ℤ σ P) :
    ((eTau (((posPsi S T).trans eTau.symm) ⟨v, posAdd s 1⟩) : R.Psi) : R.GG) =
      ((eTau (((posPsi S T).trans eTau.symm) ⟨v, s⟩) : R.Psi) : R.GG) *
        H.galE σ * R.cc := by
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    posPsi_step, Subgroup.coe_mul, mul_assoc, @frob_val R H p S.prime S.cls P _ _ σ hσ]
  congr 1
  simp [gPsi, inPsi, Formalism.HC.Frame.cc, Prod.ext_iff]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem served_of {T : ℕ} (h : GIdx H T p) : Served H p := by
  obtain ⟨h1, h2, h3, h4, _⟩ := h
  exact ⟨h1, h2, h3, h4⟩

end Formalism.BasicNotions.Examples₂.LevelValuationRings

namespace Formalism.BasicNotions.Examples₂

open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField LevelValuationRings

variable (D : D7) (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0)
  (rOf : D.what₂.Word → ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))

end Formalism.BasicNotions.Examples₂
end
end
