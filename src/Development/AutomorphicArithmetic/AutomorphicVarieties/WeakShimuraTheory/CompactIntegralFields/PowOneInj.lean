module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PowOneInj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

private theorem charP_res (c : Coef l) : CharP (ResidueField c.O) l := by
  haveI := c.dvr
  haveI := c.fin
  obtain ⟨-, -, hloc, -, -, he, -, hval, -⟩ := dvrFacts l c.O
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
  have hmem : ((l : ℕ) : c.O) ∈ maximalIdeal c.O := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h0 : IsDiscreteValuationRing.addVal c.O (l : c.O) = 0 :=
      (IsDiscreteValuationRing.addVal_eq_zero_iff).2 hu
    exact he (hval.trans h0)
  have := (residue_eq_zero_iff ((l : ℕ) : c.O)).2 hmem
  simpa using this

private theorem pow_inj {x y : ResidueField c.O} (j : ℕ) (h : x ^ l ^ j = y ^ l ^ j) : x = y := by
  haveI := charP_res c
  haveI : ExpChar (ResidueField c.O) l := ExpChar.prime Fact.out
  induction j with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply frobenius_inj (ResidueField c.O) l
    simpa [frobenius_def, pow_succ, pow_mul] using h

private theorem pow_one_inj {x : ResidueField c.O} (j : ℕ) (h : x ^ l ^ j = 1) : x = 1 := by
  exact pow_inj j (by simpa using h)

private theorem resQ_mem (F : IntermediateField ℚ Ω) (g : G F Ω) : resQ F g ∈ F.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  exact fun x hx => g.commutes ⟨x, hx⟩

private theorem dec_resLe {F F' : IntermediateField ℚ Ω} (h : F ≤ F') (A : ValuationSubring Ω) (g : G F' Ω) :
    resLe h g ∈ Dec (F := F) A ↔ g ∈ Dec (F := F') A := Iff.rfl

private theorem ine_resLe {F F' : IntermediateField ℚ Ω} [NumberField F] [NumberField F'] (h : F ≤ F')
    (A : ValuationSubring Ω) (g : G F' Ω) :
    resLe h g ∈ Ine (F := F) A ↔ g ∈ Ine (F := F') A := Iff.rfl

variable {T T' : Tower D}

private theorem up (h : T.Le T') : ∃ j : ℕ, ∀ g : G T.F Ω, ∃ g' : G T'.F Ω, resLe h.le g' = g ^ l ^ j := by
  obtain ⟨j, hj⟩ := h.pow
  refine ⟨j, fun g => ?_⟩
  have hm := hj _ (resQ_mem T.F g)
  refine ⟨IntermediateField.fixingSubgroupEquiv T'.F ⟨_, hm⟩, ?_⟩
  ext x
  simp [resLe, IntermediateField.fixingSubgroupEquiv, map_pow]

private theorem rb_resLe (h : T.Le T') (w : ℤ × ℤ) (g : G T'.F Ω) : T'.rb w g = T.rb w (resLe h.le g) := by
  simp only [Tower.rb, Tower.fr, Fr.rt, h.pr]
  rfl

private theorem rb_pow (w : ℤ × ℤ) (g : G T.F Ω) (n : ℕ) : T.rb w (g ^ n) = T.rb w g ^ n := by
  simp only [Tower.rb, map_pow, Units.val_pow_eq_pow_val]

private theorem bar_pow (γ : G ℚ Ω →* c.Oˣ) (g : G ℚ Ω) (n : ℕ) : Raw.bar γ (g ^ n) = Raw.bar γ g ^ n := by
  simp only [Raw.bar, map_pow, Units.val_pow_eq_pow_val]

private theorem galL_resLe (h : T.Le T') (g : G T'.F Ω) : resLe h.le g ∈ T.GalL ↔ g ∈ T'.GalL := by
  simp only [Tower.GalL, Subgroup.mem_comap, h.K]
  rfl

private theorem g3'_up (hl : l ≠ 2) (h : T.Le T') (ho : T.Ok) (η : T'.GalL →* (ResidueField c.O)ˣ) (h2 : η ^ 2 = 1)
    (hom : ∀ g : T'.GalL, D.om (resQ T'.F g) = 1 → η g = 1)
    (hperm : ∀ i, ∃ j, ∀ g : T'.GalL, η g * Raw.bar (chi D T'.pr i) (resQ T'.F g) =
      Raw.bar (chi D T'.pr j) (resQ T'.F g)) : η = 1 := by
  obtain ⟨k, hk⟩ := up h
  have L : ∀ u : (ResidueField c.O)ˣ, u ^ l ^ k = 1 → u = 1 := fun u hu =>
    Units.ext (pow_one_inj k (by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]))
  let φ : Fin 4 → T.GalL →* (ResidueField c.O)ˣ := fun m =>
    (Units.map (residue c.O).toMonoidHom).comp ((chi D T.pr m).comp ((resQ T.F).comp T.GalL.subtype))
  let φ' : Fin 4 → T'.GalL →* (ResidueField c.O)ˣ := fun m =>
    (Units.map (residue c.O).toMonoidHom).comp ((chi D T.pr m).comp ((resQ T'.F).comp T'.GalL.subtype))
  have hφ : ∀ m (g : T'.GalL), φ m ⟨resLe h.le g, (galL_resLe h g).2 g.2⟩ = φ' m g := fun _ _ => rfl
  have hperm' : ∀ i, ∃ j, ∀ g : T'.GalL, η g * φ' i g = φ' j g := by
    intro i
    obtain ⟨j, hj⟩ := hperm i
    refine ⟨j, fun g => Units.ext ?_⟩
    have hj' := hj g
    rw [h.pr] at hj'
    simpa [φ', Raw.bar] using hj'
  have lift : ∀ g : T.GalL, ∃ g' : T'.GalL, ∀ m, φ m g ^ l ^ k = φ' m g' ∧
      (D.om (resQ T.F g) = 1 → D.om (resQ T'.F g') = 1) := by
    intro g
    obtain ⟨g', hg'⟩ := hk g
    have hm : g' ∈ T'.GalL := (galL_resLe h g').1 (by rw [hg']; exact pow_mem g.2 _)
    refine ⟨⟨g', hm⟩, fun m => ⟨?_, fun h1 => ?_⟩⟩
    · rw [← map_pow, ← hφ]
      congr 1
      exact Subtype.ext (by simp [hg'])
    · show D.om (resQ T.F (resLe h.le g')) = 1
      rw [hg', map_pow, map_pow, h1, one_pow]
  obtain ⟨j, hj⟩ := hperm' 0
  have hη : ∀ g : T'.GalL, η g = φ' j g / φ' 0 g := fun g => eq_div_iff_mul_eq'.2 (hj g)
  let η₀ : T.GalL →* (ResidueField c.O)ˣ := φ j / φ 0
  have hη₀ : ∀ g, η₀ g = φ j g / φ 0 g := fun _ => rfl
  have C : ∀ (g : T.GalL) (g' : T'.GalL), (∀ m, φ m g ^ l ^ k = φ' m g') → η₀ g ^ l ^ k = η g' := by
    intro g g' hm
    rw [hη g', ← hm j, ← hm 0, hη₀, div_pow]
  have h0 : η₀ = 1 := by
    refine ho.g3' η₀ ?_ ?_ ?_
    · refine MonoidHom.ext fun g => ?_
      obtain ⟨g', hg'⟩ := lift g
      rw [MonoidHom.one_apply, MonoidHom.pow_apply]
      apply L
      rw [← pow_mul, mul_comm, pow_mul, C g g' (fun m => (hg' m).1), ← MonoidHom.pow_apply, h2,
        MonoidHom.one_apply]
    · intro g hg
      obtain ⟨g', hg'⟩ := lift g
      apply L
      rw [C g g' (fun m => (hg' m).1)]
      exact hom g' ((hg' 0).2 hg)
    · intro i
      obtain ⟨i', hi'⟩ := hperm' i
      refine ⟨i', fun g => ?_⟩
      have key : η₀ g * φ i g = φ i' g := by
        obtain ⟨g', hg'⟩ := lift g
        have hu : η₀ g * φ i g / φ i' g = 1 := by
          apply L
          rw [div_pow, mul_pow, C g g' (fun m => (hg' m).1), (hg' i).1, (hg' i').1, hi' g', div_self']
        exact div_eq_one.1 hu
      have := congrArg Units.val key
      simpa [φ, Raw.bar] using this
  refine MonoidHom.ext fun g => ?_
  rw [hη g, MonoidHom.one_apply, div_eq_one, ← hφ, ← hφ]
  have := congrArg (fun f : T.GalL →* (ResidueField c.O)ˣ => f ⟨resLe h.le g, (galL_resLe h g).2 g.2⟩) h0
  simp only [hη₀, MonoidHom.one_apply, div_eq_one] at this
  exact this

private theorem ok_up (hl : l ≠ 2) (h : T.Le T') (ho : T.Ok) : T'.Ok := by
  obtain ⟨k, hk⟩ := up h
  have L1 : ∀ x : ResidueField c.O, x ^ l ^ k = 1 → x = 1 := fun x hx => pow_one_inj k hx
  have liftL : ∀ g ∈ T.GalL, ∃ g' ∈ T'.GalL, resLe h.le g' = g ^ l ^ k := fun g hg => by
    obtain ⟨g', hg'⟩ := hk g
    exact ⟨g', (galL_resLe h g').1 (by rw [hg']; exact pow_mem hg _), hg'⟩
  refine
    { lab := ?_, even := ?_, unr := ?_, split := ?_, g2 := ?_, g3 := ?_, g3' := ?_, ord := ?_,
      kb := ?_, kc := ?_, ineL := ?_, dist := ?_, locL := ?_ }
  · rw [h.pr]
    exact ho.lab
  · obtain ⟨n, hn⟩ := IntermediateField.finrank_dvd_of_le_right h.le
    show Even (Module.finrank ℚ T'.F)
    rw [hn]
    exact (show Even (Module.finrank ℚ T.F) from ho.even).mul_right n
  · intro A g hg
    exact (galL_resLe h g).1 (ho.unr A ((ine_resLe h.le A g).2 hg))
  · intro p hp A hA
    rw [h.K]
    exact ho.split p hp A hA
  · intro w
    obtain ⟨g, hg, hne⟩ := ho.g2 w
    obtain ⟨g', hm, hg'⟩ := liftL g hg
    refine ⟨g', hm, fun heq => hne (pow_inj k ?_)⟩
    rw [← rb_pow, ← bar_pow, ← map_pow (resQ T.F), ← hg', ← rb_resLe h]
    exact heq
  · intro w hw
    obtain ⟨g, hg, hne⟩ := ho.g3 w hw
    obtain ⟨g', hm, hg'⟩ := liftL g hg
    exact ⟨g', hm, fun heq => hne (L1 _ (by rw [← rb_pow, ← hg', ← rb_resLe h]; exact heq))⟩
  · exact fun η h2 hom hperm => g3'_up hl h ho η h2 hom hperm
  · obtain ⟨w, hw, hord⟩ := ho.ord
    refine ⟨w, hw, fun n hn0 hn4 => ?_⟩
    obtain ⟨g, hg, hne⟩ := hord n hn0 hn4
    obtain ⟨g', hm, hg'⟩ := liftL g hg
    refine ⟨g', hm, fun heq => hne (L1 _ ?_)⟩
    rw [← pow_mul, mul_comm, pow_mul, ← rb_pow, ← hg', ← rb_resLe h]
    exact heq
  · intro A hA g hg h1
    exact ho.kb A hA (resLe h.le g) ((ine_resLe h.le A g).2 hg) h1
  · obtain ⟨m, hm, hψ⟩ := ho.kc
    exact ⟨m, hm, fun g hg => hψ (resLe h.le g) hg⟩
  · intro A hA g hg
    exact ho.ineL A hA (resLe h.le g) ((ine_resLe h.le A g).2 hg)
  · intro i j hij heq
    apply ho.dist i j hij
    obtain ⟨k', hk'⟩ := h.g0
    apply pow_inj k'
    rw [← bar_pow, ← bar_pow, ← hk']
    rw [h.pr] at heq
    exact heq
  · intro A hA
    rcases ho.locL A hA with ⟨g, hg, hne⟩ | ⟨g, hg, h1, h2, h3⟩
    · obtain ⟨g', hg'⟩ := hk g
      left
      refine ⟨g', (ine_resLe h.le A g').1 (by rw [hg']; exact pow_mem hg _), fun heq => hne (L1 _ ?_)⟩
      rw [← bar_pow, ← map_pow (resQ T.F), ← hg']
      exact heq
    · obtain ⟨g', hg'⟩ := hk g
      right
      refine ⟨g', (dec_resLe h.le A g').1 (by rw [hg']; exact pow_mem hg _), ?_, ?_, ?_⟩
      · rw [show resQ T'.F g' = resQ T.F (resLe h.le g') from rfl, hg', map_pow, bar_pow, h1, one_pow]
      · rw [rb_resLe h, hg', rb_pow, h2, one_pow]
      · exact fun heq => h3 (L1 _ (by rw [← rb_pow, ← hg', ← rb_resLe h]; exact heq))

private theorem two_up (h : T.Le T') (ht : T.Two) : T'.Two := by
  obtain ⟨j, hj⟩ := up h
  refine ⟨fun g => ?_, fun A g hg => ?_, fun A hA g hg => ?_, ?_, ht.ord, ht.xi, fun A hA => ?_, fun A hA => ?_⟩
  · rw [rb_resLe h]
    exact ht.sq _
  · rw [rb_resLe h]
    exact ht.unr A _ hg
  · rw [rb_resLe h]
    exact ht.atL A hA _ hg
  · obtain ⟨k₀, h1, h2, h3, h4⟩ := ht.quad
    refine ⟨k₀, h1, h2, h3, fun g => ?_⟩
    rw [rb_resLe h]
    exact h4 _
  · obtain ⟨g, hg, hne⟩ := ht.bigL A hA
    obtain ⟨g', hg'⟩ := hj g
    refine ⟨g', (dec_resLe h.le A g').1 (hg' ▸ pow_mem hg _), fun he => hne (pow_one_inj j ?_)⟩
    rwa [rb_resLe h, hg', rb_pow, pow_right_comm] at he
  · obtain ⟨g, hg, hne⟩ := ht.big2 A hA
    obtain ⟨g', hg'⟩ := hj g
    refine ⟨g', (ine_resLe h.le A g').1 (hg' ▸ pow_mem hg _), fun he => hne (pow_one_inj j ?_)⟩
    rwa [rb_resLe h, hg', rb_pow, pow_right_comm] at he

private theorem three_up (h : T.Le T') (ht : T.Three) : T'.Three :=
  ⟨ht.five, ht.sb, ht.psi, fun g => by rw [rb_resLe h, rb_resLe h]; exact ht.sq _⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.leFit :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T T' : Tower D, T.Le T' → (T.Ok → T'.Ok) ∧ (T.Two → T'.Two) ∧ (T.Three → T'.Three) ∧ (T.Deep → T'.Deep) ∧ (T.Fit → T'.Fit) ∧
      T.Le T ∧ ∀ T'' : Tower D, T'.Le T'' → T.Le T'' := by
  intro Ω _ _ _ l _ c D hD T T' h
  refine ⟨ok_up hD.l_odd h, two_up h, three_up h, ?_, ?_, ⟨rfl, rfl, le_rfl, ⟨0, fun g hg => by simpa using hg⟩, ⟨0, by simp⟩⟩,
    fun T'' h' => ⟨h'.pr.trans h.pr, h'.K.trans h.K, h.le.trans h'.le, ?_, ?_⟩⟩
  · rintro ⟨m, hm, hk⟩
    exact ⟨m, hm, fun g => hk (resLe h.le g)⟩
  · rintro ⟨ho, hc⟩
    exact ⟨ok_up hD.l_odd h ho, hc.imp (fun a => ⟨a.1, two_up h a.2⟩) fun a => ⟨a.1, a.2.five, a.2.sb, a.2.psi⟩⟩
  · obtain ⟨j, hj⟩ := h.pow
    obtain ⟨k, hk⟩ := h'.pow
    exact ⟨j + k, fun g hg => by rw [pow_add, pow_mul]; exact hk _ (hj g hg)⟩
  · obtain ⟨j, hj⟩ := h.g0
    obtain ⟨k, hk⟩ := h'.g0
    exact ⟨j + k, by rw [hk, hj, pow_add, pow_mul]⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AmbZero
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem az_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

open Cardinal in
private theorem az_card (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) = 𝔠 := by
  have h1 : #ℚ_[l] ≤ #(CauSeq ℚ (padicNorm l)) :=
    mk_le_of_surjective (f := (Quotient.mk'' : CauSeq ℚ (padicNorm l) → ℚ_[l])) Quotient.mk''_surjective
  have h2 : #(CauSeq ℚ (padicNorm l)) ≤ #(ℕ → ℚ) := mk_subtype_le _
  have h3 : #(ℕ → ℚ) = 𝔠 := by simp
  apply le_antisymm
  · refine (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans ?_
    exact max_le (h1.trans (h2.trans h3.le)) aleph0_le_continuum
  · have h : 𝔠 ≤ #ℚ_[l] := continuum_le_cardinal_of_nontriviallyNormedField ℚ_[l]
    exact h.trans (mk_le_of_injective (algebraMap ℚ_[l] (PadicAlgCl l)).injective)

private noncomputable def azV (l : ℕ) [Fact l.Prime] : ValuationSubring (PadicAlgCl l) :=
  (NormedField.valuation : Valuation (PadicAlgCl l) NNReal).valuationSubring

private theorem mem_azV {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : x ∈ azV l ↔ ‖x‖ ≤ 1 := by
  show ‖x‖₊ ≤ 1 ↔ _
  exact_mod_cast Iff.rfl

private noncomputable def azA {l : ℕ} [Fact l.Prime] (c : Coef l) : c.O →+* azV l :=
  (c.O.val : c.O →+* PadicAlgCl l).codRestrict (azV l) fun x =>
    (mem_azV _).2 ((az_intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map c.O.val))

private theorem azA_loc {l : ℕ} [Fact l.Prime] (c : Coef l) : IsLocalHom (azA c) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hx.exists_left_inv
  have hy' : (y : PadicAlgCl l) * (x : PadicAlgCl l) = 1 := congrArg Subtype.val hy
  have h0 : (x : PadicAlgCl l) ≠ 0 := right_ne_zero_of_mul_eq_one hy'
  have hm : (y : PadicAlgCl l) ∈ c.O :=
    (coefSup l).2.2.2 c y ((az_intIff _).2 ((mem_azV _).1 y.2)) ⟨1, x, h0, hy'⟩
  exact IsUnit.of_mul_eq_one_right (⟨y, hm⟩ : c.O) (Subtype.ext hy')

theorem UpperTheory.V.Ws.ambZero :
    ∀ (l : ℕ) [Fact l.Prime], (∃ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e) ∧ Nonempty (PadicAlgCl l ≃+* ℂ) := by
  intro l hl
  refine ⟨⟨{ K := PadicAlgCl l, V := azV l, a := azA, compat := fun _ _ _ _ => rfl, loc := azA_loc, alg := fun x => ?_ },
    RingEquiv.refl _, fun _ _ => rfl, mem_azV⟩, ?_⟩
  · obtain ⟨c, -⟩ := (coefSup l).2.1 1 (by rw [Nat.dvd_one]; exact hl.out.ne_one)
    obtain ⟨c', -, hx⟩ := (coefSup l).2.2.1 c x ((az_intIff _).2 ((mem_azV _).1 x.2))
    refine ⟨c', ⟨x, hx⟩, ?_⟩
    have : azA c' ⟨x, hx⟩ = x := rfl
    rw [this, sub_self]
    exact Ideal.zero_mem _
  · apply IsAlgClosed.ringEquiv_of_equiv_of_charZero
    · rw [az_card]; exact Cardinal.aleph0_lt_continuum
    · exact Cardinal.eq.1 (by rw [az_card, Cardinal.mk_complex])
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.MkTower
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

private theorem mem_asIdeal_iff_mem_span_of_above (l : ℕ) [hl : Fact l.Prime] (u : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))
    (hu : u ∈ Formalism.GaloisCohomology.Above ℚ l) (x : 𝓞 ℚ) :
    x ∈ u.asIdeal ↔ Rat.ringOfIntegersEquiv x ∈ Ideal.span {(l : ℤ)} := by
  have hmax : (Ideal.span {(l : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl.out).irreducible
  have hP : Ideal.span {(l : ℤ)} = Ideal.comap (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) u.asIdeal := by
    refine hmax.eq_of_le (Ideal.comap_ne_top _ u.isPrime.ne_top) ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    have : (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (l : ℤ) = (l : 𝓞 ℚ) := map_natCast _ l
    rw [this]
    exact hu
  rw [hP, Ideal.mem_comap]
  have hx : (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) (Rat.ringOfIntegersEquiv x) = x :=
    RingEquiv.symm_apply_apply _ x
  rw [hx]

private theorem mt_conj {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [hl : Fact l.Prime]
    (A B : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (hB : B.valuation (l : Ω) < 1) :
    ∃ g : G ℚ Ω, ∀ x, g x ∈ A ↔ x ∈ B := by
  have hA0 : A ≠ ⊤ := fun h => ((UpperTheory.V.Base.places ℚ Ω l A).2.1 h).2 hA
  have hB0 : B ≠ ⊤ := fun h => ((UpperTheory.V.Base.places ℚ Ω l B).2.1 h).2 hB
  obtain ⟨v, hv⟩ := (UpperTheory.V.Base.places ℚ Ω l A).1 hA0
  obtain ⟨w, hw⟩ := (UpperTheory.V.Base.places ℚ Ω l B).1 hB0
  have hvl : v ∈ Formalism.GaloisCohomology.Above ℚ l := ((UpperTheory.V.Base.places ℚ Ω l A).2.2.1 v hv).1 hA
  have hwl : w ∈ Formalism.GaloisCohomology.Above ℚ l := ((UpperTheory.V.Base.places ℚ Ω l B).2.2.1 w hw).1 hB
  have hvw : v = w := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    ext x
    rw [mem_asIdeal_iff_mem_span_of_above l v hvl x, mem_asIdeal_iff_mem_span_of_above l w hwl x]
  subst hvw
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hv hw
  refine ⟨σ.symm, fun x => ?_⟩
  rw [← hσ]
  show _ ↔ x ∈ Subring.map (MulSemiringAction.toRingHom (G ℚ Ω) Ω σ) A.toSubring
  rw [Subring.mem_map]
  constructor
  · intro hx
    exact ⟨σ.symm x, hx, by simp [MulSemiringAction.toRingHom_apply, AlgEquiv.smul_def]⟩
  · rintro ⟨a, ha, rfl⟩
    simpa [MulSemiringAction.toRingHom_apply, AlgEquiv.smul_def] using ha

private theorem mt_not_both (L : Type) [Field L] [NumberField L] [IsTotallyReal L] [_root_.NumberField.IsTotallyComplex L] : False := by
  obtain w : NumberField.InfinitePlace L := Classical.choice inferInstance
  exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)) (IsTotallyReal.isReal w)

private theorem mt_cm {Ω : Type} [Field Ω] [CharZero Ω] (K F : IntermediateField ℚ Ω) [NumberField K] [NumberField F]
    [NumberField ↥(F ⊔ K)] [IsCMField K] [IsTotallyReal F] (hK : Module.finrank ℚ K = 2) : IsCMField ↥(F ⊔ K) := by
  letI : Algebra K ↥(F ⊔ K) := (IntermediateField.inclusion (le_sup_right : K ≤ F ⊔ K)).toRingHom.toAlgebra
  haveI : IsTotallyComplex ↥(F ⊔ K) := NumberField.isTotallyComplex_of_algebra K _
  letI : Algebra F ↥(F ⊔ K) := (IntermediateField.inclusion (le_sup_left : F ≤ F ⊔ K)).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ F ↥(F ⊔ K) := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : Module.Free F ↥(F ⊔ K) := Module.Free.of_divisionRing F _
  haveI : Module.Finite F ↥(F ⊔ K) := Module.Finite.of_restrictScalars_finite ℚ F _
  have hle := IntermediateField.finrank_sup_le F K
  have hmul := Module.finrank_mul_finrank ℚ F ↥(F ⊔ K)
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hne : Module.finrank F ↥(F ⊔ K) ≠ 1 := by
    intro h1
    have hb := Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h1
    haveI : IsTotallyReal ↥(F ⊔ K) := IsTotallyReal.ofRingEquiv (RingEquiv.ofBijective (algebraMap F ↥(F ⊔ K)) hb)
    exact mt_not_both ↥(F ⊔ K)
  have hpos' : 0 < Module.finrank F ↥(F ⊔ K) := Module.finrank_pos
  haveI : Algebra.IsQuadraticExtension F ↥(F ⊔ K) := ⟨by
    rw [hK] at hle
    have : Module.finrank F ↥(F ⊔ K) ≤ 2 := by
      by_contra hc
      push_neg at hc
      have := Nat.mul_lt_mul_of_pos_left hc hpos
      omega
    omega⟩
  exact NumberField.IsCMField.ofCMExtension F ↥(F ⊔ K)

private theorem mt_out {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K F : IntermediateField ℚ Ω) [NumberField K]
    [NumberField F] [IsCMField K] [IsTotallyReal F] : ∃ h ∈ F.fixingSubgroup, h ∉ K.fixingSubgroup := by
  by_contra hcon
  push_neg at hcon
  have hle : F.fixingSubgroup ≤ K.fixingSubgroup := hcon
  have hKF : K ≤ F := by
    have h := IntermediateField.fixedField_le hle
    rwa [InfiniteGalois.fixedField_fixingSubgroup, InfiniteGalois.fixedField_fixingSubgroup] at h
  letI : Algebra K F := (IntermediateField.inclusion hKF).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K F := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsTotallyReal K := IsTotallyReal.of_algebra K F
  exact mt_not_both K

private theorem mem_or_mul_mem_fixing_of_quadratic {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : IntermediateField ℚ Ω)
    [NumberField K] (hK : Module.finrank ℚ K = 2) (h τ : G ℚ Ω) (hh : h ∉ K.fixingSubgroup) :
    τ ∈ K.fixingSubgroup ∨ h * τ ∈ K.fixingSubgroup := by
  have hN : Normal ℚ K := by
    haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
    exact inferInstance
  have hG : IsGalois ℚ K := by
    haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
    exact inferInstance
  have hk := @IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ K hN
  rw [← hk] at hh ⊢
  rw [MonoidHom.mem_ker] at hh
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, map_mul]
  by_cases ht : (@AlgEquiv.restrictNormalHom ℚ _ Ω _ _ K _ _ _ _ hN) τ = 1
  · exact Or.inl ht
  · right
    have hc0 : Nat.card (K ≃ₐ[ℚ] K) = 2 := by
      haveI : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
      rw [IsGalois.card_aut_eq_finrank ℚ K, hK]
    have hc : Nat.card (@AlgEquiv ℚ K K _ _ _ K.algebra' K.algebra') = 2 := by
      rw [← hc0]
    obtain ⟨y, hy, hu⟩ := (Nat.card_eq_two_iff' (1 : @AlgEquiv ℚ K K _ _ _ K.algebra' K.algebra')).mp hc
    by_contra hm
    have e1 := hu _ hh
    have e2 := hu _ ht
    have e3 := hu _ hm
    exact ht (mul_eq_left.mp (e3.trans e1.symm))

private theorem exists_conj_between_valuationSubrings_of_common {Ω : Type} [Field Ω] [CharZero Ω] (F : IntermediateField ℚ Ω) (A B C : ValuationSubring Ω)
    (g g' : G F Ω) (h1 : ∀ x, g x ∈ A ↔ x ∈ B) (h2 : ∀ x, g' x ∈ C ↔ x ∈ B) :
    ∃ k : G F Ω, ∀ x, k x ∈ A ↔ x ∈ C := by
  refine ⟨g * g'⁻¹, fun x => ?_⟩
  rw [AlgEquiv.mul_apply, h1, ← h2, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

private theorem inv_apply_mem_iff_of_apply_mem_iff {Ω : Type} [Field Ω] [CharZero Ω] (F : IntermediateField ℚ Ω) (A B : ValuationSubring Ω)
    (g : G F Ω) (h1 : ∀ x, g x ∈ A ↔ x ∈ B) : ∀ x, g⁻¹ x ∈ B ↔ x ∈ A := by
  intro x
  rw [← h1, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

private theorem exists_conj_valuationSubrings_trans {Ω : Type} [Field Ω] [CharZero Ω] (F : IntermediateField ℚ Ω) (A B C : ValuationSubring Ω)
    (g g' : G F Ω) (h1 : ∀ x, g x ∈ A ↔ x ∈ B) (h2 : ∀ x, g' x ∈ B ↔ x ∈ C) :
    ∃ k : G F Ω, ∀ x, k x ∈ A ↔ x ∈ C := by
  refine ⟨g * g', fun x => ?_⟩
  rw [AlgEquiv.mul_apply, h1, h2]

private theorem exists_over_l_place_conj_agreeing_on_field {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (K F : IntermediateField ℚ Ω) [NumberField K] (hK : Module.finrank ℚ K = 2)
    (h : G ℚ Ω) (hhF : h ∈ F.fixingSubgroup) (hhK : h ∉ K.fixingSubgroup)
    (P A : ValuationSubring Ω) (hP : P.valuation (l : Ω) < 1) (hA : A.valuation (l : Ω) < 1) :
    ∃ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 ∧ (∀ x ∈ K, x ∈ B ↔ x ∈ P) ∧
      ∃ g : G F Ω, ∀ x, g x ∈ A ↔ x ∈ B := by
  obtain ⟨σ, hσ⟩ := mt_conj l A P hA hP
  obtain ⟨m, hmF, hmK⟩ : ∃ m ∈ F.fixingSubgroup, ∀ x ∈ K, m x = σ x := by
    have hh' : h⁻¹ ∉ K.fixingSubgroup := fun hc => hhK (by simpa using K.fixingSubgroup.inv_mem hc)
    rcases mem_or_mul_mem_fixing_of_quadratic K hK h⁻¹ σ hh' with hs | hs
    · refine ⟨1, F.fixingSubgroup.one_mem, fun x hx => ?_⟩
      rw [IntermediateField.mem_fixingSubgroup_iff] at hs
      rw [hs x hx]
      rfl
    · refine ⟨h, hhF, fun x hx => ?_⟩
      rw [IntermediateField.mem_fixingSubgroup_iff] at hs
      have e := hs x hx
      rw [AlgEquiv.mul_apply] at e
      calc h x = h (h⁻¹ (σ x)) := by rw [e]
        _ = σ x := by rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  let gm : G F Ω := IntermediateField.fixingSubgroupEquiv F ⟨m, hmF⟩
  refine ⟨A.comap (gm : Ω →+* Ω), ?_, ?_, gm, fun x => ?_⟩
  · have key := UpperTheory.V.val_lt_one (σ := gm.toRingEquiv) (A := A.comap (gm : Ω →+* Ω)) (A' := A)
      (fun x => by rw [ValuationSubring.mem_comap]; rfl) (l : Ω)
    rw [← key, map_natCast]
    exact hA
  · intro x hx
    rw [ValuationSubring.mem_comap, ← hσ, ← hmK x hx]
    rfl
  · rw [ValuationSubring.mem_comap]
    rfl

theorem UpperTheory.V.Ws.mkTower :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (pr : Bool) (K F : IntermediateField ℚ Ω) [NumberField K] [NumberField F] [IsCMField K] [IsTotallyReal F] [IsAbelianGalois ℚ F],
      Module.finrank ℚ K = 2 → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K.fixingSubgroup) → ∀ g0 : G F Ω,
      ∃ T : Tower D, T.pr = pr ∧ T.K = K ∧ T.F = F ∧ resQ T.F T.g0 = resQ F g0 := by
  intro Ω _ _ _ l _ c D hD pr K F _ _ _ _ _ hK hdec g0
  haveI : NumberField ↥(F ⊔ K) := NumberField.mk
  haveI : IsCMField ↥(F ⊔ K) := mt_cm K F hK
  obtain ⟨h, hhF, hhK⟩ := mt_out K F
  have hP : (D.pl l).valuation (l : Ω) < 1 := hD.pl_over l Fact.out
  let s : Setoid {B : ValuationSubring Ω // B.valuation (l : Ω) < 1 ∧ ∀ x ∈ K, x ∈ B ↔ x ∈ D.pl l} :=
    { r := fun B B' => ∃ g : G F Ω, ∀ x, g x ∈ B.1 ↔ x ∈ B'.1
      iseqv := ⟨fun _ => ⟨1, fun _ => Iff.rfl⟩,
        fun ⟨g, hg⟩ => ⟨g⁻¹, inv_apply_mem_iff_of_apply_mem_iff F _ _ g hg⟩,
        fun ⟨g, hg⟩ ⟨g', hg'⟩ => exists_conj_valuationSubrings_trans F _ _ _ g g' hg hg'⟩ }
  have hex : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
      ∃ q : Quotient s, ∃ g : G F Ω, ∀ x, g x ∈ A ↔ x ∈ q.out.1 := by
    intro A hA
    obtain ⟨B, hBl, hBK, g, hg⟩ := exists_over_l_place_conj_agreeing_on_field l K F hK h hhF hhK (D.pl l) A hP hA
    obtain ⟨g', hg'⟩ := Quotient.mk_out (s := s) ⟨B, hBl, hBK⟩
    exact ⟨⟦⟨B, hBl, hBK⟩⟧, exists_conj_between_valuationSubrings_of_common F A B _ g g' hg hg'⟩
  have huniq : ∀ (A : ValuationSubring Ω) (q q' : Quotient s) (g g' : G F Ω),
      (∀ x, g x ∈ A ↔ x ∈ q.out.1) → (∀ x, g' x ∈ A ↔ x ∈ q'.out.1) → q = q' := by
    intro A q q' g g' hg hg'
    apply Quotient.out_equiv_out.mp
    exact exists_conj_between_valuationSubrings_of_common F q.out.1 A q'.out.1 g⁻¹ g'⁻¹ (inv_apply_mem_iff_of_apply_mem_iff F A _ g hg) (inv_apply_mem_iff_of_apply_mem_iff F A _ g' hg')
  haveI : Finite (Quotient s) := by
    have hsurj := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := ↥F) Ω
    have hA : ∀ τ : G ℚ Ω, ((D.pl l).comap (τ : Ω →+* Ω)).valuation (l : Ω) < 1 := by
      intro τ
      have key := UpperTheory.V.val_lt_one (σ := τ.toRingEquiv) (A := (D.pl l).comap (τ : Ω →+* Ω)) (A' := D.pl l)
        (fun x => by rw [ValuationSubring.mem_comap]; rfl) (l : Ω)
      rw [← key, map_natCast]
      exact hP
    choose f hf using fun ρ : F ≃ₐ[ℚ] F => hex _ (hA (hsurj ρ).choose)
    refine Finite.of_surjective f (fun q => ?_)
    obtain ⟨τ, hτ⟩ := mt_conj l (D.pl l) q.out.1 hP q.out.2.1
    refine ⟨AlgEquiv.restrictNormalHom F τ, ?_⟩
    obtain ⟨g, hg⟩ := hf (AlgEquiv.restrictNormalHom F τ)
    have hσ := (hsurj (AlgEquiv.restrictNormalHom F τ)).choose_spec
    set σc := (hsurj (AlgEquiv.restrictNormalHom F τ)).choose with hσc
    have hn : τ⁻¹ * σc ∈ F.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have e1 := AlgEquiv.restrictNormal_commutes σc F ⟨x, hx⟩
      have e2 := AlgEquiv.restrictNormal_commutes τ F ⟨x, hx⟩
      have e3 : σc.restrictNormal F = τ.restrictNormal F := hσ
      rw [e3, e2] at e1
      rw [AlgEquiv.mul_apply]
      have e4 : σc x = τ x := e1.symm
      rw [e4, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    let gn : G F Ω := IntermediateField.fixingSubgroupEquiv F ⟨_, hn⟩
    have h1 : ∀ x, gn x ∈ q.out.1 ↔ x ∈ (D.pl l).comap (σc : Ω →+* Ω) := by
      intro x
      rw [ValuationSubring.mem_comap, ← hτ]
      show τ ((τ⁻¹ * σc) x) ∈ D.pl l ↔ _
      rw [← AlgEquiv.mul_apply, ← mul_assoc, mul_inv_cancel, one_mul]
      rfl
    obtain ⟨k, hk⟩ := exists_conj_valuationSubrings_trans F _ _ _ gn g h1 hg
    have hr : q.out ≈ (f (AlgEquiv.restrictNormalHom F τ)).out := ⟨k, hk⟩
    exact (Quotient.out_equiv_out.mp hr).symm
  refine ⟨⟨pr, K, F, F ⊔ K, hK, rfl, g0, Quotient s, fun q => q.out.1, fun q => q.out.2.1, ?_,
    fun q => q.out.2.2⟩, rfl, rfl, rfl, rfl⟩
  intro A hA
  obtain ⟨q, g, hg⟩ := hex A hA
  exact ⟨q, ⟨g, hg⟩, fun q' ⟨g', hg'⟩ => huniq A q' q g' g hg' hg⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallExt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem fin_quot (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] (n : ℕ) (h : Module.rank A B ≤ n) :
    Module.Finite A (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) := by
  classical
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have hnzd : ∀ (c : A) (x : B), c ≠ 0 → c • x = 0 → x = 0 := by
    intro c x hc hx
    rw [Algebra.smul_def] at hx
    rcases mul_eq_zero.mp hx with h | h
    · exact absurd ((map_eq_zero_iff _ hinj).mp h) hc
    · exact h
  have hbound : ∀ s : Finset (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)),
      LinearIndependent (A ⧸ maximalIdeal A) (fun i : s => (i : B ⧸ (maximalIdeal A • ⊤ : Submodule A B))) →
      s.card ≤ n := by
    intro s hs
    have hlift : ∀ i : s, ∃ b : B,
        Submodule.Quotient.mk (p := (maximalIdeal A • ⊤ : Submodule A B)) b = (i : B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) :=
      fun i => Submodule.Quotient.mk_surjective _ _
    choose b hb using hlift
    have hli : LinearIndependent A b := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      by_contra hne
      push_neg at hne
      obtain ⟨i0, hi0⟩ := hne
      obtain ⟨j, hj, hjmin⟩ := (Finset.univ.filter (fun i => c i ≠ 0)).exists_min_image
        (fun i => IsDiscreteValuationRing.addVal A (c i)) ⟨i0, by simpa using hi0⟩
      have hcj : c j ≠ 0 := by simpa using hj
      have hdvd : ∀ i, c j ∣ c i := by
        intro i
        by_cases hci : c i = 0
        · rw [hci]; exact dvd_zero _
        · exact IsDiscreteValuationRing.addVal_le_iff_dvd.mp (hjmin i (by simpa using hci))
      choose d hd using hdvd
      have hsum : c j • ∑ i, d i • b i = 0 := by
        rw [Finset.smul_sum]
        simp_rw [smul_smul, ← hd]
        exact hc
      have hsum' : ∑ i, d i • b i = 0 := hnzd _ _ hcj hsum
      have hdj : d j = 1 := by
        have h1 : c j * d j = c j * 1 := by rw [mul_one, ← hd j]
        exact mul_left_cancel₀ hcj h1
      have hk : ∑ i, Ideal.Quotient.mk (maximalIdeal A) (d i) •
          (i : B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) = 0 := by
        have h2 := congrArg (Submodule.mkQ (maximalIdeal A • ⊤ : Submodule A B)) hsum'
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_zero, map_smul, Submodule.mkQ_apply] at h2
        rw [← h2]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hb i]
        rfl
      have h3 := Fintype.linearIndependent_iff.mp hs _ hk j
      rw [hdj, map_one] at h3
      exact one_ne_zero h3
    have h4 := hli.cardinal_le_rank
    rw [Cardinal.mk_coe_finset] at h4
    exact_mod_cast h4.trans h
  have hrank : Module.rank (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) ≤ n :=
    rank_le hbound
  haveI : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) :=
    Module.rank_lt_aleph0_iff.mp (hrank.trans_lt (Cardinal.natCast_lt_aleph0))
  exact Module.Finite.trans (A ⧸ maximalIdeal A) _

private theorem haus (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)] [Algebra.IsAlgebraic A B] :
    IsHausdorff (maximalIdeal A) B := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  refine ⟨fun x hx => ?_⟩
  by_contra hx0
  have hmem : ∀ n : ℕ, ∃ b : B, algebraMap A B (ϖ ^ n) * b = x := by
    intro n
    have h1 := (SModEq.zero).mp (hx n)
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨b, _, hb⟩ := h1
    exact ⟨b, by rw [← hb, Algebra.smul_def]⟩
  have hne := Ideal.comap_ne_bot_of_algebraic_mem hx0 (Ideal.mem_span_singleton_self x)
    (Algebra.IsAlgebraic.isAlgebraic (R := A) x)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, hc⟩ := ha
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨b, hb⟩ := hmem (k + 1)
  have e : algebraMap A B (ϖ ^ k) * algebraMap A B (u : A)
      = algebraMap A B (ϖ ^ k) * (algebraMap A B ϖ * (b * c)) := by
    rw [← map_mul, mul_comm (ϖ ^ k), ← hu, ← hc, ← hb, pow_succ, map_mul]
    ring
  have hpk : algebraMap A B (ϖ ^ k) ≠ 0 := by
    rw [← map_zero (algebraMap A B)]
    exact fun h => pow_ne_zero k hϖ.ne_zero (hinj h)
  have e2 := mul_left_cancel₀ hpk e
  have hunit : IsUnit (algebraMap A B ϖ) :=
    isUnit_of_mul_isUnit_left (e2 ▸ (u.isUnit.map (algebraMap A B)))
  exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap A B) ϖ).mp hunit)

private theorem key (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [CommRing B] [IsDomain B] [ValuationRing B]
    [Algebra A B] [FaithfulSMul A B] [IsLocalHom (algebraMap A B)] [Algebra.IsAlgebraic A B]
    (n : ℕ) (h : Module.rank A B ≤ n) (hf : Finite (ResidueField A)) :
    ∃ _ : IsDiscreteValuationRing B, IsAdicComplete (maximalIdeal B) B ∧ Finite (ResidueField B) := by
  haveI : IsHausdorff (maximalIdeal A) B := haus A B
  haveI : Module.Finite A (B ⧸ (maximalIdeal A • ⊤ : Submodule A B)) := fin_quot A B n h
  haveI : Module.Finite A B := GlobalTheory.finite_of_isHausdorff_of_finite_quotient (maximalIdeal A) B
  haveI : IsNoetherianRing B := isNoetherian_of_tower A inferInstance
  have hnf : ¬ IsField B := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
    intro hF
    have h0 : algebraMap A B ϖ ≠ 0 := by
      rw [← map_zero (algebraMap A B)]
      exact fun e => hϖ.ne_zero (FaithfulSMul.algebraMap_injective A B e)
    obtain ⟨y, hy⟩ := hF.mul_inv_cancel h0
    have hu : IsUnit (algebraMap A B ϖ) := ⟨⟨_, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
    exact hϖ.not_isUnit ((isUnit_map_iff (algebraMap A B) ϖ).mp hu)
  haveI hd : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hnf).out 2 1).mp (inferInstance : ValuationRing B)
  exact ⟨hd, GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite A B,
    IsLocalRing.ResidueField.finite_of_finite hf⟩

theorem UpperTheory.V.Ws.smallExt :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (f : A →+* 𝔞.V), 𝔞.IsDvr f →
      ∀ s : Finset 𝔞.K, ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (f' : A' →+* 𝔞.V) (g : A →+* A'),
        𝔞.IsDvr f' ∧ f'.comp g = f ∧ ∀ x : 𝔞.V, (x : 𝔞.K) ∈ Subfield.closure (Set.range (𝔞.toK.comp f) ∪ s) → x ∈ f'.range := by
  intro l _ 𝔞 A _ _ _ f hf s
  classical
  have hinjK : Function.Injective (𝔞.toK.comp f) := fun a b h => hf.inj (Subtype.val_injective h)
  let E := FractionRing A
  let φ : E →+* 𝔞.K := IsFractionRing.lift hinjK
  letI : Algebra E 𝔞.K := φ.toAlgebra
  letI : Algebra A 𝔞.K := (𝔞.toK.comp f).toAlgebra
  haveI : IsScalarTower A E 𝔞.K :=
    IsScalarTower.of_algebraMap_eq (fun a => (IsFractionRing.lift_algebraMap hinjK a).symm)
  have hint : ∀ x ∈ (s : Set 𝔞.K), IsIntegral E x := by
    intro x _
    obtain ⟨p, hp0, hp⟩ := hf.alg x
    refine IsAlgebraic.isIntegral ⟨p.map (algebraMap A E), ?_, ?_⟩
    · exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective A E)).mpr hp0
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]
      exact hp
  let L' : IntermediateField E 𝔞.K := IntermediateField.adjoin E (s : Set 𝔞.K)
  haveI : FiniteDimensional E L' := IntermediateField.finiteDimensional_adjoin hint
  have hcl : ∀ y ∈ Subfield.closure (Set.range (𝔞.toK.comp f) ∪ ↑s), y ∈ L' := by
    intro y hy
    have hle : Subfield.closure (Set.range (𝔞.toK.comp f) ∪ ↑s) ≤ L'.toSubfield := by
      rw [Subfield.closure_le]
      rintro z (⟨a, rfl⟩ | hz)
      · show (𝔞.toK.comp f) a ∈ L'
        have e : (𝔞.toK.comp f) a = algebraMap E 𝔞.K (algebraMap A E a) :=
          (IsFractionRing.lift_algebraMap hinjK a).symm
        rw [e]
        exact L'.algebraMap_mem _
      · exact IntermediateField.subset_adjoin E _ hz
    exact hle hy
  let B : Subring 𝔞.V := Subring.comap 𝔞.toK L'.toSubfield.toSubring
  have hBext : ∀ x y : B, ((x : 𝔞.V) : 𝔞.K) = ((y : 𝔞.V) : 𝔞.K) → x = y :=
    fun x y h => Subtype.ext (Subtype.ext h)
  have hBmem : ∀ x : B, ((x : 𝔞.V) : 𝔞.K) ∈ L' := fun x => x.2
  let g : A →+* B := f.codRestrict B (fun a => by
    have := hcl ((𝔞.toK.comp f) a) (Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
    exact this)
  have hgi : Function.Injective g := fun a b h => hf.inj (congrArg Subtype.val h)
  letI : Algebra A B := g.toAlgebra
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hgi
  haveI : IsLocalHom (algebraMap A B) := ⟨fun a ha => by
    haveI := hf.loc
    exact (isUnit_map_iff f a).mp (ha.map B.subtype)⟩
  have hdvd : ∀ a b : B, a ∣ b ∨ b ∣ a := by
    intro a b
    by_cases ha : ((a : 𝔞.V) : 𝔞.K) = 0
    · right
      exact ⟨0, hBext _ _ (by simp [ha])⟩
    by_cases hb : ((b : 𝔞.V) : 𝔞.K) = 0
    · left
      exact ⟨0, hBext _ _ (by simp [hb])⟩
    have hq : ((b : 𝔞.V) : 𝔞.K) / ((a : 𝔞.V) : 𝔞.K) ∈ L' := L'.div_mem (hBmem b) (hBmem a)
    rcases 𝔞.V.mem_or_inv_mem (((b : 𝔞.V) : 𝔞.K) / ((a : 𝔞.V) : 𝔞.K)) with hv | hv
    · left
      refine ⟨⟨⟨_, hv⟩, hq⟩, hBext _ _ ?_⟩
      show ((b : 𝔞.V) : 𝔞.K) = ((a : 𝔞.V) : 𝔞.K) * (((b : 𝔞.V) : 𝔞.K) / ((a : 𝔞.V) : 𝔞.K))
      field_simp
    · right
      refine ⟨⟨⟨_, hv⟩, L'.inv_mem hq⟩, hBext _ _ ?_⟩
      show ((a : 𝔞.V) : 𝔞.K) = ((b : 𝔞.V) : 𝔞.K) * (((b : 𝔞.V) : 𝔞.K) / ((a : 𝔞.V) : 𝔞.K))⁻¹
      field_simp
  haveI : ValuationRing B := ValuationRing.iff_dvd_total.mpr ⟨hdvd⟩
  haveI : Algebra.IsAlgebraic A B := ⟨fun x => by
    obtain ⟨p, hp0, hp⟩ := hf.alg ((x : 𝔞.V) : 𝔞.K)
    refine ⟨p, hp0, ?_⟩
    have e : (𝔞.toK.comp B.subtype) (Polynomial.aeval x p) = 0 := by
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
      exact hp
    exact hBext _ _ e⟩
  haveI : IsAdicComplete (maximalIdeal A) A := hf.complete
  let ψ : B →ₗ[A] L' :=
    { toFun := fun x => ⟨((x : 𝔞.V) : 𝔞.K), hBmem x⟩
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hψ : Function.Injective ψ := fun x y h => hBext x y (by
    have h' := congrArg (fun z : L' => (z : 𝔞.K)) h
    exact h')
  have hrank : Module.rank A B ≤ (Module.finrank E L' : ℕ) := by
    calc Module.rank A B ≤ Module.rank A L' := LinearMap.rank_le_of_injective ψ hψ
      _ = Module.rank E L' := (IsFractionRing.rank_right_eq A E L').symm
      _ = Module.finrank E L' := (Module.finrank_eq_rank E L').symm
  obtain ⟨hd, hc, hfin⟩ := key A B (Module.finrank E L') hrank hf.fin
  refine ⟨B, inferInstance, inferInstance, hd, B.subtype, g, ?_, RingHom.ext fun a => rfl, ?_⟩
  · refine ⟨Subtype.val_injective, ⟨fun x hx => ?_⟩, hc, hfin, fun x => ?_⟩
    · obtain ⟨u, hu⟩ := hx
      have hu' : (u : 𝔞.V) = x := hu
      have hxy : ((x : 𝔞.V) : 𝔞.K) * (((u⁻¹ : 𝔞.Vˣ) : 𝔞.V) : 𝔞.K) = 1 := by
        rw [← hu']
        exact congrArg Subtype.val u.mul_inv
      have hmem : (((u⁻¹ : 𝔞.Vˣ) : 𝔞.V) : 𝔞.K) ∈ L' := by
        rw [eq_inv_of_mul_eq_one_right hxy]
        exact L'.inv_mem (hBmem x)
      exact ⟨⟨x, ⟨_, hmem⟩, hBext _ _ hxy, hBext _ _ (by rw [mul_comm]; exact hxy)⟩, rfl⟩
    · obtain ⟨p, hp0, hp⟩ := hf.alg x
      refine ⟨p.map g, (Polynomial.map_ne_zero_iff hgi).mpr hp0, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hp
  · intro x hx
    exact RingHom.mem_range.mpr ⟨⟨x, hcl _ hx⟩, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.IsDvrCoef
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem isDvr_coef {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l) (h : 𝔞.IsZero e) (c : Coef l) :
    𝔞.IsDvr (𝔞.a c) := by
  haveI : CharZero c.O := charZero_of_injective_algebraMap (dvrFacts l c.O).1
  refine ⟨fun x y hxy => Subtype.ext ?_, 𝔞.loc c, inferInstance, (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1, fun x => ?_⟩
  · rw [← h.1 c x, ← h.1 c y, hxy]
  · have h1 : IsAlgebraic ℚ_[l] (e x) := Algebra.IsAlgebraic.isAlgebraic _
    have h2 : IsAlgebraic ℤ_[l] (e x) := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] _).2 h1
    have h3 : IsAlgebraic c.O (e x) := h2.extendScalars (dvrFacts l c.O).1
    obtain ⟨p, hp, hx⟩ := h3
    refine ⟨p, hp, e.injective ?_⟩
    have h4 : (e : 𝔞.K →+* PadicAlgCl l).comp (𝔞.toK.comp (𝔞.a c)) = algebraMap c.O (PadicAlgCl l) :=
      RingHom.ext fun z => h.1 c z
    have h5 := hom_eval₂ p (𝔞.toK.comp (𝔞.a c)) (e : 𝔞.K →+* PadicAlgCl l) x
    rw [h4] at h5
    rw [map_zero]
    exact h5.trans hx

theorem UpperTheory.V.Ws.eptV :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r, D.EPt r → ∃ r', VPt D 𝔞 r' ∧ mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) r' = r := by
  intro Ω _ _ _ l _ c D _ 𝔞 e h r hr
  obtain ⟨R, _, _, _, ρ, y, hρ, rfl⟩ := hr
  obtain ⟨⟨c', hc', hy'⟩, a, ha1, -, hy⟩ := (coPt c R).1 y
  let y' : R →+* c'.O := (y : R →+* PadicAlgCl l).codRestrict c'.O hy'
  have hn : ∀ z : c'.O, ‖(z : PadicAlgCl l)‖ ≤ 1 := fun z => by
    rw [← h.1 c' z]
    exact (h.2 _).1 (𝔞.a c' z).2
  have hm : ∀ x ∈ maximalIdeal R, y' x ∈ maximalIdeal c'.O := by
    intro x hx hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have h1 : y x * (w : PadicAlgCl l) = 1 := congrArg Subtype.val hw
    have h2 : ‖y x‖ ≤ a := by simpa using hy 1 x (by rwa [pow_one])
    have h3 := congrArg norm h1
    rw [norm_mul, norm_one] at h3
    have h4 := mul_le_of_le_one_right (norm_nonneg (y x)) (hn w)
    linarith
  refine ⟨mapRep ((𝔞.a c').comp y') ρ.hom, ⟨⟨c'.O, inferInstance, inferInstance, inferInstance, 𝔞.a c',
    ⟨mapRep y' ρ.hom, fun _ => 1⟩, isDvr_coef 𝔞 e h c', fun i j N => ?_, ?_⟩,
    R, _, _, _, ρ, (𝔞.a c').comp y', hρ, RingHom.ext fun x => ?_, fun x hx => ?_, rfl⟩, ?_⟩
  · have hle : maximalIdeal R ^ N ≤ (maximalIdeal c'.O ^ N).comap y' :=
      le_trans (Ideal.pow_right_mono hm N) (Ideal.le_comap_pow _ N)
    exact (ρ.cont i j N).comp (Ideal.quotientMap _ y' hle)
  · refine PD.ext rfl (funext fun _ => ?_)
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · rw [← 𝔞.compat c c' hc' x]
    exact congrArg (𝔞.a c') (Subtype.ext (y.commutes x))
  · exact map_nonunit (𝔞.a c') _ (hm x hx)
  · ext g i j
    exact h.1 c' (y' (ρ.hom g i j))
end
