module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsEps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaCyc
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecompose

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrLift
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem map_ofGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (h : GL (Fin 3) R) :
    GG.map f (GG.ofGL h) = GG.ofGL (Matrix.GeneralLinearGroup.map f h) := rfl

private theorem map_conjBy {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (h : GL (Fin 3) R)
    (r : G →* GG (m := 3) (R := R)) :
    (GG.map f).comp (conjBy h r) = conjBy (Matrix.GeneralLinearGroup.map f h) ((GG.map f).comp r) := by
  refine MonoidHom.ext fun g => ?_
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
    map_ofGL]

private theorem lift_lower {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (n' : GL (Fin 3) S) (hn : ∀ a b, 0 ≤ wt a b → ((n' : Matrix (Fin 3) (Fin 3) S) - 1) a b = 0) :
    ∃ n : GL (Fin 3) R, (∀ a b, 0 ≤ wt a b → ((n : Matrix (Fin 3) (Fin 3) R) - 1) a b = 0) ∧
      Matrix.GeneralLinearGroup.map f n = n' := by
  have hX : ∀ a b, ∃ x : R, (0 ≤ wt a b → x = 0) ∧ f x = ((n' : Matrix (Fin 3) (Fin 3) S) - 1) a b := by
    intro a b
    by_cases h : 0 ≤ wt a b
    · exact ⟨0, fun _ => rfl, by rw [map_zero, hn a b h]⟩
    · obtain ⟨x, hx⟩ := hf (((n' : Matrix (Fin 3) (Fin 3) S) - 1) a b)
      exact ⟨x, fun h' => absurd h' h, hx⟩
  choose X h0 hX using hX
  have hd : (Matrix.of X + 1).det = 1 := by
    have h00 := h0 0 0 (by decide)
    have h01 := h0 0 1 (by decide)
    have h02 := h0 0 2 (by decide)
    have h11 := h0 1 1 (by decide)
    have h12 := h0 1 2 (by decide)
    have h22 := h0 2 2 (by decide)
    simp [Matrix.det_fin_three, h00, h01, h02, h11, h12, h22]
  refine ⟨Matrix.GeneralLinearGroup.mk'' (Matrix.of X + 1) (by rw [hd]; exact isUnit_one), fun a b h => ?_, ?_⟩
  · change (Matrix.of X + 1 - 1) a b = 0
    rw [add_sub_cancel_right]
    exact h0 a b h
  · refine Units.ext (Matrix.ext fun a b => ?_)
    change f ((Matrix.of X + 1) a b) = _
    rw [Matrix.add_apply, map_add (f := _), Matrix.of_apply, hX, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Loc.crLift :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ r' : GQ l →* GG (m := 3) (R := B'), D.InDcr (π' : B' →+* E) r' → ∃ r : GQ l →* GG (m := 3) (R := B), D.InDcr (π : B →+* E) r ∧ (GG.map (p : B →+* B')).comp r = r' := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hc r' hr'
  obtain ⟨u', n', hu', hn1, hn2, rfl⟩ := (ordEq hP D E B' π' hπ' r').1 hr'
  obtain ⟨u, hu, rfl⟩ := triLift hP D E B π hπ B' π' hπ' p hp hc u' hu'
  obtain ⟨n, hn, rfl⟩ := lift_lower (p : B →+* B') hp n' hn2
  refine ⟨conjBy n u, (ordEq hP D E B π hπ _).2 ⟨u, n, hu, fun a b => ?_, hn, rfl⟩, map_conjBy _ n u⟩
  have h := hn1 a b
  rw [RingHom.mem_ker] at h ⊢
  rw [← h, ← hc, Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
  change π' (p _) = π' (p _ - _)
  congr 1
  split_ifs <;> simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArith
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterFirst
@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycBar :
    (E Ω : Type) →
      [inst : Field E] →
        [inst_1 : Field Ω] →
          [inst_2 : Algebra E Ω] →
            (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G E Ω →* (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)ˣ :=
    fun (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (Units.map
            (↑((Algebra.algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)).comp PadicInt.Coe.ringHom) :
              ℤ_[l] →* UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)).comp
        (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycZ E Ω l)

theorem UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cyc_continuous :
    ∀ (F Ω : Type) [inst : Field F] [NumberField F] [inst_2 : Field Ω] [inst_3 : Algebra F Ω] (l : ℕ)
      [inst_4 : Fact (Nat.Prime l)],
      Continuous (⇑(UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycBar F Ω l) : UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.G F Ω → (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)ˣ) := by
  intro F Ω _ _ _ _ l _
  have h1 : Continuous (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cycZ F Ω l) := cyclotomicCharacter.continuous l F Ω
  have h2 : Continuous ((algebraMap ℚ_[l] (UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.Qbar l)).comp PadicInt.Coe.ringHom) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp continuous_subtype_val
  exact (Continuous.units_map _ h2).comp h1
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem cyc_continuous (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.ContinuousCyclotomicCharacter₂.cyc_continuous F Ω l

theorem UpperTheory.V.Loc.laArith :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous κ → ∀ (m : ℤ) (k : ℕ), 0 < k → (∀ g : ↥(Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → (κ g * cycBar F Ω l g ^ (-m)) ^ k = 1) → IsLocAlg h κ fun _ => -m := by
  intro H F Ω _ _ _ _ _ l _ A w h hl κ hκ m k hk hpow
  set c : ↥(Dec (F := F) A) →* (Qbar l)ˣ := (cycBar F Ω l).comp (Dec (F := F) A).subtype with hc
  have hcc : Continuous c := (cyc_continuous F Ω l).comp continuous_subtype_val
  let i : ↥(Ine (F := F) A) →* ↥(Dec (F := F) A) := (Subgroup.inclusion (Weil_le_Dec h)).comp (ineIncl h)
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  let χ : ↥(Dec (F := F) A) →* (Qbar l)ˣ := κ * c ^ (-m)
  have hχ : Continuous χ := hκ.mul ((continuous_zpow (-m)).comp hcc)
  have ho : IsOpen ((χ.comp i)⁻¹.ker : Set ↥(Ine (F := F) A)) := by
    refine isOpen_ker_of_pow _ (hχ.comp hi).inv hk fun σ => ?_
    have h1 : χ (i σ) ^ k = 1 := hpow (i σ) σ.2
    rw [MonoidHom.inv_apply, MonoidHom.comp_apply, inv_pow, h1, inv_one]
  obtain ⟨hmul, hz, h0⟩ := UpperTheory.V.Loc.laMul (l := l) h
  have H0 : IsWtPart h χ 0 (χ.comp i)⁻¹ := h0 χ _ ho fun σ => mul_inv_cancel _
  have H1 := (hmul _ _ _ _ _ _ H0 (hz _ _ _ m (UpperTheory.V.Loc.laCyc H h hl))).1
  have e : χ * c ^ m = κ := by
    simp only [χ, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have e' : (0 + m • fun _ : Emb l w => (-1 : ℤ)) = fun _ => -m := by
    funext τ
    simp
  rw [← hc, e, e'] at H1
  exact ⟨_, H1⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AinfActionTiltFixedOfFrobeniusRelation
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

namespace UpperTheory.V.Loc

variable {l : ℕ} [hl : Fact l.Prime]

open Polynomial in
open scoped Formalism.Per in
private theorem tfab_lift (y : OCb l) {m : ℕ} (hm : 0 < m) (hy : y ^ l ^ m = y) :
    ∃ (z : OC l) (x : Om l), (z : ℂ_[l]) = (x : ℂ_[l]) ∧ x ^ l ^ m = x ∧
      PreTilt.coeff 0 y = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) z := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  have hz : y.untilt ^ l ^ m = y.untilt := by rw [← map_pow, hy]
  have hz' : ((y.untilt : OC l) : ℂ_[l]) ^ l ^ m = (y.untilt : OC l) := by
    have := congrArg (fun t : OC l => (t : ℂ_[l])) hz
    simpa using this
  have hint : IsIntegral (Om l) ((y.untilt : OC l) : ℂ_[l]) := by
    refine ⟨X ^ l ^ m - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1), ?_⟩
    simp [hz']
  obtain ⟨x, hx⟩ := minpoly.mem_range_of_degree_eq_one (Om l) _
    (IsAlgClosed.degree_eq_one_of_irreducible (Om l) (minpoly.irreducible hint))
  refine ⟨y.untilt, x, hx.symm, ?_, (PreTilt.mk_untilt_eq_coeff_zero y).symm⟩
  apply (algebraMap (Om l) ℂ_[l]).injective
  have hx' : algebraMap (Om l) ℂ_[l] x = (y.untilt : OC l) := hx
  rw [map_pow, hx', hz']

private theorem tfab_root {x : Om l} {m : ℕ} (hm : 0 < m) (hx : x ^ l ^ m = x) (h0 : x ≠ 0) :
    ∃ n, 0 < n ∧ ¬ l ∣ n ∧ x ^ n = 1 := by
  have h1 : 1 < l ^ m := Nat.one_lt_pow hm.ne' hl.out.one_lt
  refine ⟨l ^ m - 1, by omega, fun h => ?_, ?_⟩
  · have h2 := (Nat.dvd_sub_iff_right h1.le (dvd_pow_self l hm.ne')).mp h
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h2)
  · apply mul_right_cancel₀ h0
    rw [← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]

end UpperTheory.V.Loc

theorem UpperTheory.Ainf_action_tilt_fixed_of_frobenius_relation :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (a b : ℕ), (∀ c : ↥(MaximalUnramifiedExtension l), g (((GlobalTheory.Pst.frobUr l ^ b) c : ↥(MaximalUnramifiedExtension l)) : Om l) = (((GlobalTheory.Pst.frobUr l ^ a) c : ↥(MaximalUnramifiedExtension l)) : Om l)) → ∀ (y : OCb l) (m : ℕ), 0 < m → y ^ l ^ m = y → AI.actT g (y ^ l ^ b) = y ^ l ^ a := by
  intro l hl P AI g a b hg y m hm hy
  obtain ⟨z, x, hzx, hx, h0⟩ := UpperTheory.V.Loc.tfab_lift y hm hy
  have hgx : g (x ^ l ^ b) = x ^ l ^ a := by
    by_cases hx0 : x = 0
    · rw [hx0, zero_pow (pow_ne_zero _ hl.out.ne_zero), zero_pow (pow_ne_zero _ hl.out.ne_zero), map_zero]
    obtain ⟨n, hn0, hn, hxn⟩ := UpperTheory.V.Loc.tfab_root hm hx hx0
    have hmem : x ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨n, hn0, hn, hxn⟩
    have h1 := hg ⟨x, hmem⟩
    rw [GlobalTheory.Pst.frobUr_pow_root b ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn),
      GlobalTheory.Pst.frobUr_pow_root a ⟨x, hmem⟩ n hn0 hn (Subtype.ext hxn)] at h1
    exact h1
  have hc : ∀ k : ℕ, PreTilt.coeff 0 (y ^ k) = Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (z ^ k) := fun k => by
    rw [map_pow, h0]
    exact (map_pow _ _ _).symm
  have hz : ∀ k : ℕ, ((z ^ k : OC l) : ℂ_[l]) = ((x ^ k : Om l) : ℂ_[l]) := fun k => by
    rw [PadicComplex.coe_eq, map_pow, ← PadicComplex.coe_eq, ← hzx]
    simp
  have hp : ∀ k : ℕ, (y ^ k) ^ l ^ m = y ^ k := fun k => by rw [← pow_mul, mul_comm, pow_mul, hy]
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g (y ^ l ^ b) 0 _ (hc _)
  rw [hz, AI.actC_ext, hgx, ← hz] at h1
  refine GlobalTheory.UnramifiedCrys.eq_of_coeff_zero hm (by rw [← map_pow, hp]) (hp _) ?_
  rw [h2, hc, Subtype.ext h1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsAlgebraicVectorSpanningSubspace
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RestrictAutomorphism
noncomputable def UpperTheory.Reformulated.B.RestrictAutomorphism.zlW :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → (R : Type) → [inst_1 : CommRing R] → [CharP R l] → ℤ_[l] →+* WittVector l R :=
    fun (l : ℕ) [Fact (Nat.Prime l)] (R : Type) [CommRing R] [CharP R l] ↦
      (WittVector.map (ZMod.castHom (dvd_refl l) R)).comp (WittVector.equiv l).symm.toRingHom

namespace UpperTheory.Reformulated.B.RestrictAutomorphism

private theorem hom_unique {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (φ ψ : ℤ_[p] →+* WittVector p R) : φ = ψ := by
  ext1 x
  rw [← sub_eq_zero]
  ext i
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (i + 1) x)
  have hx : x = y * (p : ℤ_[p]) ^ (i + 1) + (x.appr (i + 1) : ℤ_[p]) := by
    rw [hy]; ring
  have h : φ x - ψ x = (φ y - ψ y) * (p : WittVector p R) ^ (i + 1) := by
    conv_lhs => rw [hx]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [h, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self i), WittVector.zero_coeff]

private theorem pow_pow_mul {p : ℕ} {R : Type} [CommRing R] {y : R} {m : ℕ}
    (h : y ^ p ^ m = y) (n : ℕ) : y ^ p ^ (m * n) = y := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

private def algPart (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p] : Subring R where
  carrier := {y | ∃ m : ℕ, 0 < m ∧ y ^ p ^ m = y}
  one_mem' := ⟨1, one_pos, one_pow _⟩
  zero_mem' := ⟨1, one_pos, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)⟩
  mul_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [mul_pow, pow_pow_mul ha, mul_comm m n, pow_pow_mul hb]
  add_mem' := by
    rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [add_pow_char_pow, pow_pow_mul ha, mul_comm m n, pow_pow_mul hb]
  neg_mem' := by
    rintro a ⟨m, hm, ha⟩
    refine ⟨m, hm, ?_⟩
    have h := map_neg (iterateFrobenius R p m) a
    rwa [iterateFrobenius_def, iterateFrobenius_def, ha] at h

private theorem map_mem_algPart {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (σ : R ≃+* R) {y : R} (hy : y ∈ algPart p R) : σ y ∈ algPart p R := by
  obtain ⟨m, hm, h⟩ := hy
  exact ⟨m, hm, by rw [← map_pow, h]⟩

private def restrictAut (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    (σ : R ≃+* R) : algPart p R ≃+* algPart p R where
  toFun y := ⟨σ y, map_mem_algPart σ y.2⟩
  invFun y := ⟨σ.symm y, map_mem_algPart σ.symm y.2⟩
  left_inv y := Subtype.ext (σ.symm_apply_apply _)
  right_inv y := Subtype.ext (σ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul σ (a : R) b)
  map_add' a b := Subtype.ext (map_add σ (a : R) b)

private def restrictHom (p : ℕ) [Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    [CharP R p] (ρ : G →* R ≃+* R) : G →* algPart p R ≃+* algPart p R where
  toFun g := restrictAut p (ρ g)
  map_one' := by
    ext y
    show ρ 1 (y : R) = y
    rw [map_one]; rfl
  map_mul' g h := by
    ext y
    show ρ (g * h) (y : R) = ρ g (ρ h y)
    rw [map_mul]; rfl

end UpperTheory.Reformulated.B.RestrictAutomorphism

theorem UpperTheory.Reformulated.B.RestrictAutomorphism.exists_alg :
    ∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {G : Type} [inst : Group G] {R : Type} [inst_1 : CommRing R] (ρ : G →* R ≃+* R)
      [inst_2 : TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [inst_6 : CharP R p],
      (∀ (y : R) (m : ℕ), (0 : ℕ) < m → y ^ p ^ m = y → ∀ᶠ (g : G) in nhds (1 : G), ((ρ : G → R ≃+* R) g : R → R) y = y) →
        ∀ {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]),
          Continuous (⇑M : G → Matrix (Fin r) (Fin r) ℤ_[p]) →
            (∀ (g : G),
                (∀ (m : ℕ), (0 : ℕ) < m → ∀ (y : R), y ^ p ^ m = y → ((ρ : G → R ≃+* R) g : R → R) y = y) →
                  (M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g = (1 : Matrix (Fin r) (Fin r) ℤ_[p])) →
              ∃ (W : Matrix (Fin r) (Fin r) (WittVector p R)),
                IsUnit W.det ∧
                  (∀ (g : G),
                      ((M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g).map (⇑(UpperTheory.Reformulated.B.RestrictAutomorphism.zlW p R) : ℤ_[p] → WittVector p R) *
                          W.map (⇑(WittVector.map ((ρ : G → R ≃+* R) g).toRingHom) : WittVector p R → WittVector p R) =
                        W) ∧
                    ∀ (i j : Fin r) (n : ℕ), ∃ (m : ℕ), (0 : ℕ) < m ∧ (W i j).coeff n ^ p ^ m = (W i j).coeff n := by
  intro p hp G _ R _ ρ _ _ _ _ _ hopen r M hM hker
  haveI : CharP (algPart p R) p := inferInstance
  obtain ⟨V, hV, hVeq⟩ := UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg (p := p) (restrictHom p ρ)
    (fun y m hm hy => (hopen y m hm (by simpa using congrArg Subtype.val hy)).mono
      fun g hg => Subtype.ext hg)
    M hM
    (fun g hg => hker g fun m hm y hy =>
      congrArg Subtype.val (hg m hm ⟨y, m, hm, hy⟩ (Subtype.ext (by simpa using hy))))
  let ι : WittVector p (algPart p R) →+* WittVector p R := WittVector.map (algPart p R).subtype
  refine ⟨V.map ι, ?_, fun g => ?_, fun i j n => ?_⟩
  · have h := hV.map ι
    rwa [RingHom.map_det] at h
  · have h := congrArg (fun A => A.map ι) (hVeq g (restrictHom p ρ g).toRingHom fun _ _ _ _ => rfl)
    have h1 : (M g).map (zlW p R) =
        ((M g).map (UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.zlW p (algPart p R))).map ι := by
      rw [hom_unique (zlW p R) (ι.comp (UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.zlW p (algPart p R))),
        RingHom.coe_comp, Matrix.map_map]
    have h2 : (V.map ι).map (WittVector.map (ρ g).toRingHom) =
        (V.map (WittVector.map (restrictHom p ρ g).toRingHom)).map ι := by
      ext i j n
      simp only [Matrix.map_apply, ι, WittVector.map_coeff]
      rfl
    rw [h1, h2, ← Matrix.map_mul]
    exact h
  · simp only [Matrix.map_apply, ι, WittVector.map_coeff]
    exact ((V i j).coeff n).2
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section
open GlobalTheory.UnramifiedCrys GlobalTheory.Cyc
open scoped Topology

private theorem exists_alg {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    (ρ : G →* (R ≃+* R)) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      (∀ g, (M g).map (zlW p R) * W.map (WittVector.map (ρ g).toRingHom) = W) ∧
      ∀ i j n, ∃ m, 0 < m ∧ (W i j).coeff n ^ p ^ m = (W i j).coeff n :=
  _root_.UpperTheory.Reformulated.B.RestrictAutomorphism.exists_alg ρ hopen M hM hJ

end

theorem UpperTheory.exists_algebraic_vector_spanning_subspace :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) {r : ℕ} (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ℤ_[l]), Continuous M → (∀ g ∈ IK K, M g = 1) → ∃ W : Matrix (Fin r) (Fin r) (Ainf l), IsUnit W.det ∧ (∀ g, (M g).map (zlW l (OCb l)) * W.map (AI.actW (g : GQ l)) = W) ∧ ∀ i j n, ∃ m, 0 < m ∧ (W i j).coeff n ^ l ^ m = (W i j).coeff n := by
  intro l _ P AI K r M hM hI
  have := GlobalTheory.UnramifiedCrys.compactSpace_GK K
  exact exists_alg (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (GlobalTheory.UnramifiedCrys.eventually_actT_eq AI y m hm hy)) M hM
    (fun g hg => hI g (Subgroup.subset_closure fun x hx =>
      GlobalTheory.UnramifiedCrys.norm_sub_lt_one_of_fix AI g hg x hx))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DeRhamRationalOfExtensionByCharacter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem charpoly_of_exact {K M₀ M M₂ : Type} [Field K] [AddCommGroup M₀] [Module K M₀] [FiniteDimensional K M₀]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M] [AddCommGroup M₂] [Module K M₂] [FiniteDimensional K M₂]
    (f : M₀ →ₗ[K] M) (p : M →ₗ[K] M₂) (hf : Function.Injective f) (hp : Function.Surjective p)
    (he : Function.Exact f p) (T₀ : End K M₀) (T : End K M) (T₂ : End K M₂) (h₀ : ∀ x, f (T₀ x) = T (f x))
    (h₂ : ∀ x, p (T x) = T₂ (p x)) : T.charpoly = T₀.charpoly * T₂.charpoly := by
  have hA : ∀ x ∈ LinearMap.ker p, T x ∈ LinearMap.ker p := fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢; rw [h₂, hx, map_zero]
  rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ (LinearMap.ker p) T hA]
  congr 1
  · let e : M₀ ≃ₗ[K] ↥(LinearMap.ker p) :=
      (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.1 he).symm)
    have he' : T.restrict hA = e.conj T₀ := by
      refine LinearMap.ext fun y => ?_
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      exact Subtype.ext (h₀ x).symm
    rw [he', LinearEquiv.charpoly_conj]
  · let e := p.quotKerEquivOfSurjective hp
    have he' : (LinearMap.ker p).mapQ (LinearMap.ker p) T (fun x hx => hA x hx) = e.symm.conj T₂ := by
      refine LinearMap.ext fun y => ?_
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.symm_symm]
      apply e.injective
      rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, Submodule.mapQ_apply]
      simp only [e, LinearMap.quotKerEquivOfSurjective_apply_mk, h₂]
      rfl
    rw [he', LinearEquiv.charpoly_conj]

private theorem wdAt_of_model {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces B) {a : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (L₂ : FinExt l) (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₂.1)
    (hm₂ : IsModel B r L₂ r₂) (hV₂ : IsPst P (B.repE L₂ r₂)) :
    wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L₂ r₂) := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj (r := r) ⟨L₂, r₂, hm₂, hV₂⟩
  have h₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have h₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e := IsModel.unique B r (hm₁.enlarge h₁) (hm₂.enlarge h₂)
  have a₁ := GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι B h hj h₁ r₁ hV₁
  have a₂ := GlobalTheory.T.potSemistableParameter_coefficientField_enlarge P ι B h hj h₂ r₂ hV₂
  rw [e] at a₁
  exact e₁.trans (a₁.symm.trans a₂)

section Blocks

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : LocBridge l E Ω Gw O)

private theorem exists_model {m : ℕ} (r : ↥Gw →* GL (Fin m) (Om l)) (L : FinExt l) (hL : B.LL.1 ≤ L.1)
    (hr : ∀ g i j, (r g : Matrix (Fin m) (Fin m) (Om l)) i j ∈ L.1) : ∃ r₂, IsModel B r L r₂ := by
  let M : ↥Gw →* Matrix (Fin m) (Fin m) ↥L.1 :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, hr g i j⟩
      map_one' := by
        ext i j
        simp [Matrix.one_apply, apply_ite]
      map_mul' := fun g g' => by
        ext i j
        simp [Matrix.mul_apply] }
  exact ⟨M.toHomUnits, hL, by ext g i j; rfl⟩

private theorem blocks {n : ℕ} (r : ↥Gw →* GL (Fin (n + 1)) (Om l)) (r' : ↥Gw →* GL (Fin n) (Om l))
    (ψ : ↥Gw →* (Om l)ˣ)
    (h0 : ∀ g (i : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) i.succ 0 = 0)
    (h1 : ∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) 0 0 = (ψ g : Om l))
    (h2 : ∀ g (i j : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) i.succ j.succ =
      (r' g : Matrix (Fin n) (Fin n) (Om l)) i j)
    (L : FinExt l) (r₁ : ↥Gw →* GL (Fin (n + 1)) ↥L.1) (hm : IsModel B r L r₁) :
    ∃ (r₀ : ↥Gw →* GL (Fin 1) ↥L.1) (r₂ : ↥Gw →* GL (Fin n) ↥L.1)
      (f : (Fin 1 → ↥L.1) →ₗ[↥L.1] (Fin (n + 1) → ↥L.1)) (p : (Fin (n + 1) → ↥L.1) →ₗ[↥L.1] (Fin n → ↥L.1)),
      IsModel B (GlobalTheory.TripleGal.rk1 ψ) L r₀ ∧ IsModel B r' L r₂ ∧
      (∀ g v, f (B.repE L r₀ g v) = B.repE L r₁ g (f v)) ∧ (∀ g v, p (B.repE L r₁ g v) = B.repE L r₂ g (p v)) ∧
      Function.Injective f ∧ Function.Surjective p ∧ Function.Exact f p := by
  have e₁ : ∀ g i j, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Om l)) i j =
      (((r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) i j : ↥L.1) : Om l) := fun g i j => by rw [← hm.2]; rfl
  have eψ : ∀ g i j, (GlobalTheory.TripleGal.rk1 ψ g : Matrix (Fin 1) (Fin 1) (Om l)) i j = ψ g := fun g i j => by
    rw [Subsingleton.elim j i]
    exact Matrix.diagonal_apply_eq (fun _ : Fin 1 => (ψ g : Om l)) i
  obtain ⟨r₀, m₀⟩ := exists_model B (GlobalTheory.TripleGal.rk1 ψ) L hm.1 fun g i j => by
    rw [eψ, ← h1, e₁]; exact SetLike.coe_mem _
  obtain ⟨r₂, m₂⟩ := exists_model B r' L hm.1 fun g i j => by
    rw [← h2, e₁]; exact SetLike.coe_mem _
  have k0 : ∀ g (i : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) i.succ 0 = 0 :=
    fun g i => Subtype.ext ((e₁ g _ _).symm.trans (h0 g i))
  have k1 : ∀ g, (r₀ g : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 = (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) 0 0 :=
    fun g => Subtype.ext (by rw [← e₁, h1, ← eψ g 0 0, ← m₀.2]; rfl)
  have k2 : ∀ g i j, (r₂ g : Matrix (Fin n) (Fin n) ↥L.1) i j =
      (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ↥L.1) i.succ j.succ :=
    fun g i j => Subtype.ext (by rw [← e₁, h2, ← m₂.2]; rfl)
  have ap : ∀ {m : ℕ} (s : ↥Gw →* GL (Fin m) ↥L.1) g v i,
      B.repE L s g v i = ∑ j, (s (B.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) i j * v j := fun s g v i => rfl
  refine ⟨r₀, r₂, LinearMap.single ↥L.1 (fun _ => ↥L.1) 0 ∘ₗ LinearMap.proj 0, LinearMap.funLeft ↥L.1 ↥L.1 Fin.succ,
    m₀, m₂, fun g v => funext fun i => ?_, fun g v => funext fun i => ?_, fun x y hxy => funext fun i => ?_,
    LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n), fun x => ⟨fun hx => ?_, ?_⟩⟩
  · rw [ap]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [ap, k1, Fin.sum_univ_succ]
    · simp [k0, Fin.sum_univ_succ]
  · rw [ap, LinearMap.funLeft_apply, ap, Fin.sum_univ_succ, k0]
    simp [k2]
  · rw [Subsingleton.elim i 0]
    simpa using congrFun hxy 0
  · refine ⟨fun _ => x 0, funext fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simpa using (congrFun hx i).symm
  · rintro ⟨y, rfl⟩
    funext i
    simp

end Blocks

set_option maxHeartbeats 1000000 in
theorem UpperTheory.deRham_rational_of_extension_by_character :
    GlobalTheory.Published.DeRhamPotSemistable → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {n : ℕ} (r : ↥(Dec (F := F) A) →* GL (Fin (n + 1)) (Qbar l)) (r' : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)) (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous r → (∀ g (i : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) i.succ 0 = 0) → (∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) 0 0 = (ψ g : Qbar l)) → (∀ g (i j : Fin n), (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) i.succ j.succ = (r' g : Matrix (Fin n) (Fin n) (Qbar l)) i j) → ∀ (c : (F →+* Qbar l) → ℤ) (HT : (F →+* Qbar l) → Multiset ℤ) (β : ↥(Weil h) → ℂ) (Q : ↥(Weil h) → ℂ[X]), DRat ι h r (fun τ => c τ ::ₘ HT τ) (fun s => (X - C (β s)) * Q s) → DRat ι h (GlobalTheory.TripleGal.rk1 ψ) (fun τ => {c τ}) (fun s => X - C (β s)) → DRat ι h r' HT Q := by
  intro hB F Ω _ _ _ _ _ l _ ι A w h n r r' ψ hc h0 h1 h2 c HT β Q hr hψ O _ _ _ Bw hj
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨d₁, j₁, p₁⟩ := hr O Bw hj
  obtain ⟨-, j₀, p₀⟩ := hψ O Bw hj
  have dr : ∀ {m : ℕ} (L : FinExt l) (s : ↥(Dec (F := F) A) →* GL (Fin m) ↥L.1),
      IsDR ((UpperTheory.V.Loc.PP l).PD Bw.Kw) (Bw.repE L s) ↔ Bw.IsdRE (UpperTheory.V.Loc.PP l) L s := fun L s => by
    rw [IsDR, finrank_fin_fun]; rfl
  refine ⟨?_, fun τ LL' τ' hτ => ?_, fun s => ?_⟩
  · obtain ⟨L, r₁, hm, hd⟩ := d₁
    obtain ⟨r₀, r₂, f, p, -, m₂, hf, hp, fi, ps, ex⟩ := blocks Bw r r' ψ h0 h1 h2 L r₁ hm
    exact ⟨L, r₂, m₂, (dr L r₂).1 (GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T Bw.Kw L _ _ _ _ _ _ f p hf hp
      fi ps (LinearMap.exact_iff.1 ex).symm ((dr L r₁).2 hd)).2.1⟩
  · obtain ⟨L, r₁, hm, hd, τ₁, t₁, hcount⟩ := j₁ τ LL' τ' hτ
    obtain ⟨r₀, r₂, f, p, m₀, m₂, hf, hp, fi, ps, ex⟩ := blocks Bw r r' ψ h0 h1 h2 L r₁ hm
    obtain ⟨-, d₂, hadd⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l _ _ T Bw.Kw L _ _ _ _ _ _ f p hf hp
      fi ps (LinearMap.exact_iff.1 ex).symm ((dr L r₁).2 hd)
    refine ⟨L, r₂, m₂, (dr L r₂).1 d₂, τ₁, t₁, fun a => ?_⟩
    have a₀ := IsJumpsAt.count_eq (UpperTheory.V.Loc.PP l) m₀ t₁ (j₀ τ LL' τ' hτ) a
    have a₁ := hcount a
    have a₂ : Bw.multE (UpperTheory.V.Loc.PP l) L r₁ τ₁ a = Bw.multE (UpperTheory.V.Loc.PP l) L r₀ τ₁ a + Bw.multE (UpperTheory.V.Loc.PP l) L r₂ τ₁ a :=
      (hadd τ₁ a).2.1
    beta_reduce at a₀ a₁
    rw [← Multiset.singleton_add, Multiset.count_add, Nat.cast_add, a₀, a₂] at a₁
    exact add_left_cancel a₁
  · obtain ⟨L, r₁, hm, hV⟩ := hB.isPstAt T Bw r (Units.continuous_val.comp hc) d₁
    obtain ⟨r₀, r₂, f, p, m₀, m₂, hf, hp, fi, ps, ex⟩ := blocks Bw r r' ψ h0 h1 h2 L r₁ hm
    obtain ⟨V₀, V₂, wi, ws, wex⟩ := UpperTheory.weil_deligne_functor_exactness l ι Bw.Kw L _ _ _ _ _ _ f p hf hp fi ps ex hV
    haveI := hV.finite
    haveI := V₀.finite
    haveI := V₂.finite
    have a₀ := p₀ s
    have a₁ := p₁ s
    beta_reduce at a₀ a₁
    rw [wdAt_of_model _ ι Bw h hj _ L r₀ m₀ V₀, DpstMap.charPol_wdPst _ ι Bw h hj _ V₀] at a₀
    rw [wdAt_of_model _ ι Bw h hj _ L r₁ hm hV, DpstMap.charPol_wdPst _ ι Bw h hj _ hV,
      charpoly_of_exact _ _ wi ws wex _ _ _ (DpstMap.wdLin_wdRho _ ι Bw h hj hf s)
        (DpstMap.wdLin_wdRho _ ι Bw h hj hp s), a₀] at a₁
    rw [wdAt_of_model _ ι Bw h hj _ L r₂ m₂ V₂, DpstMap.charPol_wdPst _ ι Bw h hj _ V₂]
    exact mul_left_cancel₀ (X_sub_C_ne_zero _) a₁
end
