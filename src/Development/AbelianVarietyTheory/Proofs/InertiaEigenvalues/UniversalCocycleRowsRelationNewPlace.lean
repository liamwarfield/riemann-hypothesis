module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobenius

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCocycleRowsRelationNewPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCocycleRowsRelationNewPlace
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrimeRel

theorem one_add_pow_of_sq {B : Type} [CommRing B] {x : B} (hx : x * x = 0) (n : ℕ) : (1 + x) ^ n = 1 + (n : B) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    linear_combination (n : B) * hx

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}

theorem tame_rel (hT : TameQuotient) (_hl : 0 < nu X i) {M : ℕ} {L : Subgroup (GE N)} {p : PlE D.host}
    {d : GE N →* Multiplicative (ZMod (X.l i ^ M))} {σ γ : GE N} (hM : nu X i + 2 ≤ M) (hp : NewPl i M L p d σ γ)
    {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W]
    (ρ : Representation R (GE N) W) (a b : R) (h4 : ∀ m : W, (X.l i ^ (nu X i + 1)) • m = 0) (hb : b * b = 0)
    (hI : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), ∀ m, ρ τ m = m + (((Multiplicative.toAdd (d τ)).val : R) * b) • m)
    (hσ : ∀ m, ρ σ m = m + a • m) (z : Z1 ρ) : a • z.1 γ = b • z.1 σ := by
  have := X.lPrime i
  obtain ⟨h0, -, hn, -, hd, hσ', hγ, hdγ⟩ := hp
  have h8 : normV p % (2 * X.l i ^ (nu X i + 1)) = 1 :=
    KStar.Tree.mod_two_mul_pow_of_le (X.lPrime i).out (by omega) hn
  exact (GlobalTheory.T.tame_relation_cocycle_squareZero_inertia hT D.host.E N.Om (X.l i) (N.plOm.1 p) p (N.plOm.2 p)
    (fun h => h0 p (Or.inl rfl) (X.twistExcludedPlaces_contains_residueChar i h)) (nu X i + 1) h8 M d γ σ (by omega) hd hγ hdγ hσ' R W ρ a b h4 hb hI hσ z).1

theorem rel : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N), nu X i + 2 ≤ M → Small2 i s M L z → NewPl i M L p d σ γ → ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (κ : GE N →* Bˣ) (x y : B), Kills i B → AntiHom X.cc κ → x * x = 0 → (∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), ((κ τ : Bˣ) : B) * (1 + x) ^ (Multiplicative.toAdd (d τ)).val = 1) → ((κ σ : Bˣ) : B) * (1 + y) = 1 → ∀ (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) B) Z, Univ bkP i s κ Q Φ Z → ∀ j : Bool × Fin D.R.r, x • Z (two X σ j.1) j.2 - (y * (if j.1 then 1 else ((κ σ : Bˣ) : B))) • Z (two X γ j.1) j.2 ∈ what₂ Φ := by
  intro hT D N X bkP i s hl M L z₀ p d σ γ hM hL hp B _ _ κ x y hK hκ hx hI hσ Q a Φ Z hU j

  let Y := (Fin a → B) ⧸ what₂ Φ
  letI : TopologicalSpace Y := ⊥
  haveI : DiscreteTopology Y := ⟨rfl⟩
  let mk : (Fin a → B) →ₗ[B] Y := (what₂ Φ).mkQ
  have hmk : ∀ v ∈ what₂ Φ, mk v = 0 := fun v hv => (Submodule.Quotient.mk_eq_zero _).2 hv

  let x0 : Fin a → Y := fun j => mk (Pi.single j 1)
  have hrow : ∀ (r : ℕ) (A : Matrix (Fin r) (Fin a) B) (c : Fin r), ∑ j, A c j • x0 j = mk (A c) := by
    intro r A c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [x0, ← map_smul, ← map_sum]
    congr 1
    ext j
    simp [Pi.single_apply]
  have hx0 : matAct Φ x0 = 0 := by
    ext c
    change ∑ j, Φ c j • x0 j = 0
    rw [hrow]
    exact hmk _ (Submodule.subset_span ⟨c, rfl⟩)
  have hrect : ∀ g c, rect (Z g) x0 c = mk (Z g c) := fun g c => hrow _ _ _

  obtain ⟨z, hz, -⟩ := (hU Y).1 x0 hx0

  have h4 : ∀ m : Fin D.R.r → Y, (X.l i ^ (nu X i + 1)) • m = 0 := fun m => by
    have h1 := hK _ (GlobalTheory.Growth.sq_mem_idl (X := X) (i := i))
    rw [map_natCast] at h1
    rw [← Nat.cast_smul_eq_nsmul B]
    exact (congrArg (· • m) h1).trans (zero_smul _ _)
  have htr : ∀ g ∈ L, ∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Bˣ) : B) • m := fun g hg =>
    (GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z₀ (by omega) hL B κ _ hK (isDual_dualRep i s) Y g hg).1
  have hdec : DecV N p ≤ L := hp.2.2.2.1
  have hIL : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), τ ∈ L := fun τ hτ => hdec (Ine_le_Dec _ hτ)
  have hσL : σ ∈ L := hdec hp.2.2.2.2.2.1.1
  have hcL : ∀ g, g ∈ L → cConj X g ∈ L := fun g hg => (hL.1.2.2.1 g _ (cConj_apply X g)).1 hg

  have hIv : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p),
      ((κ τ : Bˣ) : B) * (1 + ((Multiplicative.toAdd (d τ)).val : B) * x) = 1 := fun τ hτ => by
    rw [← one_add_pow_of_sq hx]
    exact hI τ hτ

  have r1 := tame_rel hT.1 hl hM hp (repOn (Tgl i s) κ Y) (-(y * ((κ σ : Bˣ) : B))) (-x) h4 (by rw [neg_mul_neg, hx])
    (fun τ hτ m => by
      have h := hIv τ hτ
      have hκτ : ((κ τ : Bˣ) : B) = 1 + ((Multiplicative.toAdd (d τ)).val : B) * -x := by
        linear_combination (1 - ((Multiplicative.toAdd (d τ)).val : B) * x) * h +
          ((Multiplicative.toAdd (d τ)).val : B) * ((Multiplicative.toAdd (d τ)).val : B) * ((κ τ : Bˣ) : B) * hx
      rw [htr τ (hIL τ hτ), hκτ, add_smul, one_smul])
    (fun m => by
      have hκσ : ((κ σ : Bˣ) : B) = 1 + -(y * ((κ σ : Bˣ) : B)) := by linear_combination hσ
      rw [htr σ hσL]
      nth_rw 1 [hκσ]
      rw [add_smul, one_smul]) z

  have hcont : Continuous (cConj X) := GlobalTheory.ResConjTriv.continuous_cConj X
  let z' : Z1 ((repOn (Tgl i s) κ Y).comp (cConj X)) :=
    ⟨fun g => z.1 (cConj X g), z.2.1.comp hcont, fun g h => by
      change z.1 (cConj X (g * h)) = _
      rw [map_mul]
      exact z.2.2 _ _⟩
  have r2 := tame_rel hT.1 hl hM hp ((repOn (Tgl i s) κ Y).comp (cConj X)) y x h4 hx
    (fun τ hτ m => by
      change repOn (Tgl i s) κ Y (cConj X τ) m = _
      rw [htr _ (hcL τ (hIL τ hτ)), antiHom_cConj X hκ, Units.inv_eq_of_mul_eq_one_right (hIv τ hτ), add_smul, one_smul])
    (fun m => by
      change repOn (Tgl i s) κ Y (cConj X σ) m = _
      rw [htr _ (hcL σ hσL), antiHom_cConj X hκ, Units.inv_eq_of_mul_eq_one_right hσ, add_smul, one_smul]) z'

  obtain ⟨b, c⟩ := j
  have key : ∀ (u v : B) (g h : GE N), u • z.1 g = v • z.1 h → u • Z g c - v • Z h c ∈ what₂ Φ := by
    intro u v g h e
    have e' := congrFun e c
    simp only [Pi.smul_apply, hz, hrect] at e'
    rw [← Submodule.Quotient.mk_eq_zero (what₂ Φ)]
    change mk (u • Z g c - v • Z h c) = 0
    rw [map_sub, map_smul, map_smul, e', sub_self]
  cases b
  · simp only [two, Bool.false_eq_true, ↓reduceIte, mul_one]
    apply key
    have := r1
    rw [neg_smul, neg_smul, neg_inj] at this
    exact this.symm
  · simp only [two, ↓reduceIte, mul_one]
    apply key
    exact r2.symm

end GlobalTheory.NewPrimeRel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCocycleRowsRelationNewPlaceStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_cocycle_rows_relation_newPlace : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N), nu X i + 2 ≤ M → Small2 i s M L z → NewPl i M L p d σ γ → ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (κ : GE N →* Bˣ) (x y : B), Kills i B → AntiHom X.cc κ → x * x = 0 → (∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), ((κ τ : Bˣ) : B) * (1 + x) ^ (Multiplicative.toAdd (d τ)).val = 1) → ((κ σ : Bˣ) : B) * (1 + y) = 1 → ∀ (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) B) Z, Univ bkP i s κ Q Φ Z → ∀ j : Bool × Fin D.R.r, x • Z (two X σ j.1) j.2 - (y * (if j.1 then 1 else ((κ σ : Bˣ) : B))) • Z (two X γ j.1) j.2 ∈ what₂ Φ := by
  first | exact @GlobalTheory.NewPrimeRel.rel | exact GlobalTheory.NewPrimeRel.rel | (intros; apply GlobalTheory.NewPrimeRel.rel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNewPlaceFrobeniusConjugateModOpenNormalSub
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNewPlaceFrobeniusConjugateModOpenNormalSub
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
open GlobalTheory.ChosenPrimes

namespace GlobalTheory.NewPrimePick

theorem exists_newPlace : Cheb → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → n < R → ∀ (H : Subgroup (GE N)) (S : Finset (PlE D.host)), AdmFam X i M H S d → L ≤ H → ∀ (U : Subgroup (GE N)) (h : GE N), IsOpen (U : Set (GE N)) → U.Normal → U ≤ L → h ∈ L → (∀ b : Fin R, b.val < n → d (P (.inl b)) h = 1) → (∀ b : Fin R, n ≤ b.val → Ine (F := D.host.E) (N.plOm.1 (P (.inl b))) ≤ U) → ∃ P' : Fin R ⊕ Fin (n + 1) → PlE D.host, Ext P P' ∧ PiLocalization₂ i M d A₀ L z P' ∧ ∃ σ γ g : GE N, NewPl i M L (P' (.inr (Fin.last n))) (d (P' (.inr (Fin.last n)))) σ γ ∧ d (P' (.inr (Fin.last n))) σ = 1 ∧ g * σ * g⁻¹ * h⁻¹ ∈ U := by
  intro hC D N X i s M R n d A L z P _ _ hsm hst _ H S hA hLH U h hU hUn hUL hh hh1 hIU
  classical
  obtain ⟨-, -, -, hd⟩ := hA
  obtain ⟨⟨hL, hLn, -⟩, hLr, -⟩ := hsm
  obtain ⟨⟨ha1, ha2, ha3⟩, hs1, hs2⟩ := hst
  have hl := (X.lPrime i).out
  set m := 2 * X.l i ^ M with hm
  have hn1 : 1 < m := by have := Nat.pow_pos (n := M) hl.pos; omega
  have hn0 : m ≠ 0 := by omega
  have hval := exists_values (U ⊓ ⨅ b : {b : Fin R // b.val < n}, (d (P (.inl b.1))).ker)
    (fun b : {b : Fin R // n ≤ b.val} => d (P (.inl b.1))) (fun b c => by
      obtain ⟨γ, hγ, e⟩ := (ha3 (.inl b.1)).2.2.2.2 _ (over_refl _) _ (N.plOm.2 (P (.inl b.1))) c
      have key : ∀ b' : Fin R, b' ≠ b.1 → d (P (.inl b')) γ = 1 := fun b' hb' =>
        (ha3 (.inl b')).2.2.2.1 _ (fun h => hb' (Sum.inl_injective (ha2 _ _ h))) _ (N.plOm.2 (P (.inl b.1))) γ hγ
      refine ⟨γ, ⟨hIU b.1 b.2 hγ, Subgroup.mem_iInf.2 fun b' => key b'.1 fun h => ?_⟩, e,
        fun b' hb' => key b'.1 fun h => hb' (Subtype.ext h)⟩
      have h1 := b'.2
      have h2 := b.2
      rw [h] at h1
      omega)
  obtain ⟨γ₀, hγ₀, hγd⟩ := hval fun b =>
    Multiplicative.ofAdd (if n = b.1.val then 1 else 0) * (d (P (.inl b.1)) h)⁻¹
  have hγh : ∀ b : Fin R, d (P (.inl b)) (γ₀ * h) = Multiplicative.ofAdd (if n = b.val then 1 else 0) := by
    intro b
    rw [map_mul]
    rcases lt_or_ge b.val n with hb | hb
    · have h1 : d (P (.inl b)) γ₀ = 1 := Subgroup.mem_iInf.1 hγ₀.2 ⟨b, hb⟩
      rw [h1, hh1 b hb, if_neg (by omega), mul_one]
      rfl
    · rw [hγd ⟨b, hb⟩, inv_mul_cancel_right]
  let V : Subgroup (GE N) := U ⊓ ⨅ b, (d (P (.inl b))).ker
  have hV : IsOpen (V : Set (GE N)) := by
    refine hU.inter ?_
    show IsOpen ((⨅ b, (d (P (.inl b))).ker : Subgroup (GE N)) : Set (GE N))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun b => (ha3 (.inl b)).1
  have hVn : V.Normal := by
    have : (⨅ b, (d (P (.inl b))).ker).Normal := Subgroup.normal_iInf_normal fun b => inferInstance
    infer_instance
  obtain ⟨T₀, hT₀, hsp⟩ := GlobalTheory.FrobDense.exists_finite_split D.host
  let T : Set (PlE D.host) := ((↑A ∪ ↑S ∪ ↑(X.S0 i)) ∪ (T₀ ∪ {P | P.asIdeal.ramificationIdx ℤ ≠ 1}) ∪
    ({v | ((m : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal} ∪
      {v | ∃ B : ValuationSubring N.Om, IsPlaceOver B v ∧ ¬ Ine (F := D.host.E) B ≤ U})) ∪ Set.range P
  have hT : T.Finite :=
    ((((A.finite_toSet.union S.finite_toSet).union (X.S0 i).finite_toSet).union
      (hT₀.union (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified D.host.E).2)).union
      ((finite_mem hn0).union (finite_ram hU))).union (Set.finite_range P)
  obtain ⟨p, hp⟩ := exists_pick hC hV hVn (γ₀ * h) hT
  have h1 : ∀ v, Over p v → ((((v ∉ A ∧ v ∉ S) ∧ v ∉ X.S0 i) ∧ v ∉ T₀ ∧ v.asIdeal.ramificationIdx ℤ = 1) ∧
      ((m : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ∧
      ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ U) ∧ v ∉ Set.range P := fun v hv => by
    have : v ∉ T := (hp.1 v hv).1
    simpa only [T, Set.mem_union, not_or, Finset.mem_coe, Set.mem_ofPred_eq, not_exists, not_and, not_not] using this
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 p)
  obtain ⟨k, hk⟩ := hp.2 σ hσ
  have hσL : σ ∈ L := by
    have h2 := hLn.conj_mem _ (L.mul_mem (hUL hk.1) (L.mul_mem (hUL hγ₀.1) hh)) k⁻¹
    have e : k⁻¹ * (k * σ * k⁻¹ * (γ₀ * h)⁻¹ * (γ₀ * h)) * k⁻¹⁻¹ = σ := by group
    rwa [e] at h2
  have hP0 := h1 p (over_refl p)
  have hq := norm_mod (N.plOm.2 p) hn1 hP0.1.2.1 hσ (hLr σ hσL)
  have hIp : Ine (F := D.host.E) (N.plOm.1 p) ≤ U := hP0.1.2.2 _ (N.plOm.2 p)
  have hdec : DecV N p ≤ L := dec_le (N.plOm.2 p) hL (hIp.trans hUL) hσ hσL
  have hspl : IsSplitPl D.host p := hsp p hP0.1.1.2.1 (hp.1 p (over_refl p)).2
  have hgood : GoodChar X i M p (d p) := hd p hP0.1.1.1.1.2 hspl (hdec.trans hLH)
  have haux : ∀ v, Over p v → IsSplitPl D.host v ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ Formalism.BasicNotions.eWL D.host.E v = 1 ∧
      v ∉ X.S0 i ∧ v ∉ A ∧ normV v % m = 1 := by
    refine fun v hv => ⟨hsp v (h1 v hv).1.1.2.1 (hp.1 v hv).2, (hp.1 v hv).2, (h1 v hv).1.1.2.2, (h1 v hv).1.1.1.2,
      (h1 v hv).1.1.1.1.1, ?_⟩
    rcases hv with rfl | hv
    · exact hq
    · rwa [normV_conj hv]
  let P' : Fin R ⊕ Fin (n + 1) → PlE D.host :=
    Sum.elim (fun a => P (.inl a)) (Fin.snoc (α := fun _ => PlE D.host) (fun a => P (.inr a)) p)
  have e1 : P' (.inr (Fin.last n)) = p := by simp [P']
  have e2 : ∀ q, P' (Sum.map id Fin.castSucc q) = P q := by
    rintro (a | a) <;> simp [P']
  have cases : ∀ q : Fin R ⊕ Fin (n + 1), q = .inr (Fin.last n) ∨ ∃ q₀, q = Sum.map id Fin.castSucc q₀ := by
    rintro (a | a)
    · exact Or.inr ⟨.inl a, rfl⟩
    · refine Fin.lastCases (Or.inl rfl) (fun a => Or.inr ⟨.inr a, rfl⟩) a
  refine ⟨P', e2, ⟨⟨fun q => ?_, fun q q' => ?_, fun q => ?_⟩, hs1, fun a => ?_⟩, ?_⟩
  · rcases cases q with rfl | ⟨q, rfl⟩
    · rw [e1]; exact haux
    · rw [e2]; exact ha1 q
  · rcases cases q with rfl | ⟨q, rfl⟩ <;> rcases cases q' with rfl | ⟨q', rfl⟩
    · exact fun _ => rfl
    · rw [e1, e2]; exact fun h => ((h1 _ h).2 ⟨q', rfl⟩).elim
    · rw [e1, e2]; exact fun h => ((h1 _ (over_symm h)).2 ⟨q, rfl⟩).elim
    · rw [e2, e2]; exact fun h => by rw [ha2 _ _ h]
  · show GoodChar X i M (P' q) (d (P' q))
    rcases cases q with rfl | ⟨q, rfl⟩
    · rw [e1]; exact hgood
    · rw [e2]; exact ha3 q
  · refine Fin.lastCases ?_ (fun a => ?_) a
    · rw [e1]
      refine ⟨hdec, fun b τ hτ => ?_⟩
      obtain ⟨k', hk'⟩ := hp.2 τ hτ
      have h2 : d (P (.inl b)) _ = 1 := Subgroup.mem_iInf.1 hk'.2 b
      rw [map_mul, map_inv, hγh] at h2
      simp only [map_mul, map_inv, mul_inv_cancel_comm, mul_inv_eq_one] at h2
      exact h2
    · have e3 : P' (.inr a.castSucc) = P (.inr a) := e2 (.inr a)
      rw [e3]
      exact hs2 a
  · rw [e1]
    obtain ⟨γ, hγ, hγ1⟩ := hgood.2.2.2.2 p (over_refl p) _ (N.plOm.2 p) (Multiplicative.ofAdd 1)
    obtain ⟨τ, hτ, hτ1⟩ := hgood.2.2.2.2 p (over_refl p) _ (N.plOm.2 p) (d p σ)⁻¹
    refine ⟨σ * τ, γ, k, ⟨fun v hv => (haux v hv).2.2.2.1, hspl, hq, hdec, hgood.1, ?_, hγ, hγ1⟩, ?_, ?_⟩
    · first | exact isFrob_mul_of_mem_Ine hσ hτ | exact isFrob_mul_of_mem_Ine hτ hσ
    · rw [map_mul, hτ1, mul_inv_cancel]
    · have h2 := U.mul_mem (U.mul_mem (hUn.conj_mem _ (hIp hτ) (k * σ)) hk.1) hγ₀.1
      have e : k * σ * τ * (k * σ)⁻¹ * (k * σ * k⁻¹ * (γ₀ * h)⁻¹) * γ₀ = k * (σ * τ) * k⁻¹ * h⁻¹ := by group
      rwa [e] at h2

end GlobalTheory.NewPrimePick
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNewPlaceFrobeniusConjugateModOpenNormalSubStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_newPlace_frobeniusConjugate_modOpenNormalSubgroup : Cheb → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → n < R → ∀ (H : Subgroup (GE N)) (S : Finset (PlE D.host)), AdmFam X i M H S d → L ≤ H → ∀ (U : Subgroup (GE N)) (h : GE N), IsOpen (U : Set (GE N)) → U.Normal → U ≤ L → h ∈ L → (∀ b : Fin R, b.val < n → d (P (.inl b)) h = 1) → (∀ b : Fin R, n ≤ b.val → Ine (F := D.host.E) (N.plOm.1 (P (.inl b))) ≤ U) → ∃ P' : Fin R ⊕ Fin (n + 1) → PlE D.host, Ext P P' ∧ PiLocalization₂ i M d A₀ L z P' ∧ ∃ σ γ g : GE N, NewPl i M L (P' (.inr (Fin.last n))) (d (P' (.inr (Fin.last n)))) σ γ ∧ d (P' (.inr (Fin.last n))) σ = 1 ∧ g * σ * g⁻¹ * h⁻¹ ∈ U := by
  first | exact @GlobalTheory.NewPrimePick.exists_newPlace | exact GlobalTheory.NewPrimePick.exists_newPlace | (intros; apply GlobalTheory.NewPrimePick.exists_newPlace <;> assumption)
end
end
