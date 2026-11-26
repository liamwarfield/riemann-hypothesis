module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiGenOnInteriorOfPsiUnitOn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodLatticeInGenus
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodLatticeInGenus
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionGenus

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_eq_iff (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ ∃ y, a = b + n • y := by
  rw [tateIso_ev_eq_iff I hn]
  unfold Datum.ModN
  exact exists_congr fun y => sub_eq_iff_eq_add'

theorem exists_lift (I' : TateIso D' k Q act e) (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D'.La, ∀ a, I.ev n a = I'.ev n (f a) := by
  have hs : ∀ a, ∃ b, I'.ev n b = I.ev n a := fun a => (I'.onto n hn _).1 (tateIso_ev_pow I hn a)
  choose s hs using hs
  let N : Submodule (𝓞 E) D'.La := LinearMap.range (n • (LinearMap.id : D'.La →ₗ[𝓞 E] D'.La))
  have hN : ∀ a b : D'.La, N.mkQ a = N.mkQ b ↔ I'.ev n a = I'.ev n b := by
    intro a b
    rw [tateIso_ev_eq_iff I' hn, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, hc.symm⟩
  let φ : D.La →ₗ[𝓞 E] D'.La ⧸ N :=
    { toFun := fun a => N.mkQ (s a)
      map_add' := fun a b => by
        rw [← map_add (f := _), hN, I'.add, hs, hs, hs, I.add]
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← map_smul, hN, I'.lin, hs, hs, I.lin] }
  have := D.proj
  obtain ⟨f, hf⟩ := Module.projective_lifting_property N.mkQ φ N.mkQ_surjective
  refine ⟨f, fun a => ?_⟩
  have h : N.mkQ (f a) = N.mkQ (s a) := LinearMap.congr_fun hf a
  rw [(hN _ _).1 h, hs]

theorem genus_of_tateIso
    (he : ∀ n x y c c', 0 < n → x ^ n = 1 → y ^ n = 1 → e n x y c → e n x y c' → c = c')
    (I' : TateIso D' k Q act e) (I : TateIso D k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      ((∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧
      (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧
      ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧
      ∀ n, 0 < n → I.ζ n = I'.ζ n ^ ν n ∧ ∀ a, I.ev n a = I'.ev n (f n a) := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := exists_lift I' I h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℤ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · have : NeZero n := ⟨h.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n h).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n h).pow_eq_one)
      exact ⟨i, fun _ => by rw [zpow_natCast, hi]⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, ν, ⟨?_, ?_, ?_⟩, fun n hn => ⟨hν n hn, hf n hn⟩⟩
  · intro n m hn hm a
    rw [← ev_eq_iff I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun x => ?_, fun x' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨x, hx⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn x')
      refine ⟨x, (ev_eq_iff I' hn _ _).1 ?_⟩
      rw [← hf n hn, hx]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ hn (tateIso_ev_pow I' hn _) (tateIso_ev_pow I' hn _) e1 e2
    rw [hν n hn, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]

end

theorem unitOn_injective {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := fun a b h => by
  have h1 := congrArg (fun x : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x.val) h
  apply Units.ext
  simpa [unitOn] using h1

noncomputable def expRoot (n : ℕ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) / n)) (Complex.exp_ne_zero _)

theorem expRoot_zpow (n : ℕ) (m : ℤ) :
    ((expRoot n ^ m : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n) := by
  rw [Units.val_zpow_eq_zpow_val, expRoot, Units.val_mk0, ← Complex.exp_int_mul]
  congr 1
  ring

theorem expRoot_prim {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (expRoot n) n := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  have h := (Complex.isPrimitiveRoot_exp n hn.ne').inv
  rw [← Complex.exp_neg] at h
  rw [expRoot, Units.val_mk0, neg_div]
  exact h

theorem expRoot_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : expRoot (n * m) ^ m = expRoot n := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, expRoot, expRoot, Units.val_mk0, Units.val_mk0, ← Complex.exp_nat_mul]
  congr 1
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

section

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

end

noncomputable def periodTateIso {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D' : Datum H)
    {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (act : OAct (𝓞 E) A)
    (Q : D'.La →+ (Fin g → ℂ)) (hQ : Function.Injective Q) (hΛ : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range)
    (hact : ∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a)
    (hW : ∀ (n : ℕ) (a b : D'.La) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / n) →
      Out.WeilIs A L n (u.ex ((n : ℂ)⁻¹ • Q a)) (u.ex ((n : ℂ)⁻¹ • Q b)) (unitOn c)) :
    TateIso D' ℂ (𝟙_ (Over (Sp ℂ)) ⟶ A) (fun c y => y ≫ act.act c)
      (fun n y y' c => Out.WeilIs A L n y y' (unitOn c)) where
  ζ := expRoot
  ζ_prim _ hn := expRoot_prim hn
  ζ_pow _ _ hn hm := expRoot_pow hn hm
  ev n x := u.ex ((n : ℂ)⁻¹ • Q x)
  add n a b := by rw [map_add (f := _), smul_add, u.ex_add]
  lin n c a := hact c n a
  ker n hn a := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [u.ker, hΛ]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, hQ ?_⟩
      rw [map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hn', one_smul]
    · rintro ⟨b, rfl⟩
      refine ⟨b, ?_⟩
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn', one_smul]
  onto n hn x := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := u.ex_onto x
      rw [← ex_nsmul, u.ker, hΛ] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [ha, smul_smul, inv_mul_cancel₀ hn', one_smul]⟩
    · rintro ⟨a, rfl⟩
      rw [← ex_nsmul, u.ker, hΛ, smul_smul, mul_inv_cancel₀ hn', one_smul]
      exact ⟨a, rfl⟩
  tower n m hn hm a := by
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [← ex_nsmul, smul_smul]
    congr 2
    push_cast
    field_simp
  isom n hn a b := hW n a b _ hn (expRoot_zpow n _)

theorem period_lattice_in_genus :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (D' : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (Q : D'.La →+ (Fin P.g → ℂ)), D'.p = D.p → D'.q = D.q → u.IsAH Hm χ → Function.Injective Q → (∀ z, z ∈ u.Λ ↔ z ∈ Q.range) → (∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a) → ∀ I : TateIso D ℂ (Over.mk (𝟙 (Sp ℂ)) ⟶ P.A) (fun c y => y ≫ act.act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧ ∀ n : ℕ, 0 < n → (I.ζ n : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n) ∧ ∀ x, (I.ev n x).left = (u.ex ((n : ℂ)⁻¹ • Q (f n x))).left := by
  intro hL hL2 hT hU E _ _ _ H D D' P u Hm χ act Q hp hq hAH hQ hΛ hE hact I
  obtain ⟨Ef, hEf, -, -, -, -, -, -, hW⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm hL hL2 hT hU P u Hm χ hAH
  have hW' : ∀ (n : ℕ) (a b : D'.La) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • Q a)) (u.ex ((n : ℂ)⁻¹ • Q b)) (unitOn c) := by
    intro n a b c hn hc
    refine hW n ⟨Q a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hΛ _).2 ⟨b, rfl⟩⟩ c hn ?_
    have h := hEf ⟨Q a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨Q b, (hΛ _).2 ⟨b, rfl⟩⟩
    rw [hE] at h
    rw [Int.cast_injective h]
    exact hc
  obtain ⟨f, ν, ⟨h1, h2, h3⟩, h4⟩ := genus_of_tateIso (D := D) (D' := D')
    (fun n x y c c' _ hx hy ha hb =>
      unitOn_injective (((hL.weil _ P n (Over.mk (𝟙 (Sp ℂ)))).1 x y hx hy).unique ha hb))
    (periodTateIso D' u act Q hQ hΛ hact hW') I
  refine ⟨f, ν, ⟨hp, hq, h1, h2, h3⟩, fun n hn => ⟨?_, fun x => ?_⟩⟩
  · rw [(h4 n hn).1]
    exact expRoot_zpow n _
  · rw [(h4 n hn).2]
    rfl

end GlobalTheory.TorsionGenus
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PeriodLatticeInGenusStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_lattice_in_genus_alt : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (D' : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (Q : D'.La →+ (Fin P.g → ℂ)), D'.p = D.p → D'.q = D.q → u.IsAH Hm χ → Function.Injective Q → (∀ z, z ∈ u.Λ ↔ z ∈ Q.range) → (∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a) → ∀ I : TateIso D ℂ (Over.mk (𝟙 (Sp ℂ)) ⟶ P.A) (fun c y => y ≫ act.act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧ ∀ n : ℕ, 0 < n → (I.ζ n : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n) ∧ ∀ x, (I.ev n x).left = (u.ex ((n : ℂ)⁻¹ • Q (f n x))).left := by
  first | exact @GlobalTheory.TorsionGenus.period_lattice_in_genus | exact GlobalTheory.TorsionGenus.period_lattice_in_genus | (intros; apply GlobalTheory.TorsionGenus.period_lattice_in_genus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodsComplexPELObject
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.PELPeriod

theorem linear_eq_zero_of_mem_discrete {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, F z ∈ Λ) (z : Fin g → ℂ) : F z = 0 := by
  have hc : Continuous fun w => (⟨F w, h w⟩ : Λ) := F.continuous_of_finiteDimensional.subtype_mk _
  have := PreconnectedSpace.constant inferInstance hc (x := z) (y := 0)
  simpa using congrArg Subtype.val this

theorem sub_mem_of_ex_eq {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {z w : Fin g → ℂ} (h : u.ex z = u.ex w) : z - w ∈ u.Λ := by
  rw [← u.ker]
  have := u.ex_add (z - w) w
  rw [sub_add_cancel, h] at this
  exact mul_eq_right.1 this.symm


open Matrix in
theorem exists_coord {g : ℕ} {La La' : Type} [AddCommGroup La] [AddCommGroup La'] (Q : La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : La' ≃+ La) (Q' : La' →+ (Fin g → ℂ))
    (hQ : ∀ x, h (Q' x) = Q (e x)) (inj : Function.Injective Q) (disc : DiscreteTopology Q.range)
    (span : Submodule.span ℝ (Set.range Q) = ⊤) (herm : Hm.IsHermitian)
    (pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) :
    ∃ Hm' : Matrix (Fin g) (Fin g) ℂ, Function.Injective Q' ∧ DiscreteTopology Q'.range ∧
      Submodule.span ℝ (Set.range Q') = ⊤ ∧ Hm'.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re) ∧
      ∀ x y, hermForm Hm' (Q' x) (Q' y) = hermForm Hm (Q (e x)) (Q (e y)) := by
  let L := h.toLinearMap
  let M := LinearMap.toMatrix' L
  have key : ∀ z w, hermForm (Mᵀ * Hm * Mᵀᴴ) z w = hermForm Hm (L z) (L w) := fun z w => by
    rw [← LinearMap.toMatrix'_mulVec L z, ← LinearMap.toMatrix'_mulVec L w, hermForm, hermForm, ← mulVec_mulVec,
      ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, star_mulVec, ← mulVec_transpose]
    rfl
  refine ⟨Mᵀ * Hm * Mᵀᴴ, fun x y hxy => e.injective (inj (by rw [← hQ, ← hQ, hxy])), ?_, ?_,
    isHermitian_mul_mul_conjTranspose _ herm, fun z hz => ?_, fun x y => ?_⟩
  · let m : Q'.range → Q.range := fun z => ⟨h z, by
      obtain ⟨_, x, rfl⟩ := z
      exact ⟨e x, (hQ x).symm⟩⟩
    have hm : Continuous m :=
      (L.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hm fun z w hzw =>
      Subtype.ext (h.injective (congrArg Subtype.val hzw))
  · have r : Set.range Q' = (h.symm.toLinearMap.restrictScalars ℝ) '' Set.range Q := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨_, ⟨e x, rfl⟩, by simp [← hQ]⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨e.symm x, h.injective (by simp [hQ])⟩
    rw [r, Submodule.span_image, span, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  · rw [key]
    exact pos _ fun h0 => hz (h.injective (h0.trans (map_zero h).symm))
  · rw [key, ← hQ, ← hQ]
    rfl

theorem exists_module {O : Type} [CommRing O] {g : ℕ} {La : Type} [AddCommGroup La] (ty : Fin g → (O →+* ℂ))
    (Q : La →+ (Fin g → ℂ)) (inj : Function.Injective Q) (st : ∀ c x, ∃ y, ∀ i, Q y i = ty i c * Q x i) :
    ∃ _ : Module O La, ∀ (c : O) x i, Q (c • x) i = ty i c * Q x i := by
  choose sm hsm using st
  letI : SMul O La := ⟨sm⟩
  have hs : ∀ (c : O) x i, Q (c • x) i = ty i c * Q x i := hsm
  refine ⟨{ one_smul := fun x => inj (funext fun i => by simp [hs])
            mul_smul := fun c d x => inj (funext fun i => by simp [hs, _root_.mul_assoc])
            smul_zero := fun c => inj (funext fun i => by simp [hs])
            smul_add := fun c x y => inj (funext fun i => by simp [hs, mul_add])
            add_smul := fun c d x => inj (funext fun i => by simp [hs, add_mul])
            zero_smul := fun x => inj (funext fun i => by simp [hs]) }, hs⟩

theorem exists_period : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)), a w = H.w0 → a w' = H.bar H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → PELClass D a bas ρ em t → ∃ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧ em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) ∧ IsPeriod D' ty Q ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro l1 l2 l3 l4 E _ _ _ H D o _ g k J b em w w' a bas ρ ty t hw hw' hρ hty hP
  obtain ⟨La, _, EF, lam, ac, Q₀, Hm₀, hbij, hpol, -, u, χ, hAH, hΛ, hχ, hpt, hac⟩ :=
    GlobalTheory.T.exists_lattice_uniformisation_of_prim_theta l1 l2 l3 l4 o g k J b em w w' t ((GlobalTheory.T.pelObjectClass_prim_and_iso_closed E H D o g k J b em w w' a bas ρ t hP).1 hw hw')
  obtain ⟨act, haj, hdet, hadj, I, hζ, hev⟩ := exists_act hP
  change OAct (𝓞 E) t.A at act
  rw [hρ] at hdet
  obtain ⟨h, hh⟩ : ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ (c : 𝓞 E) z,
      u.ex (h (fun i => ty i (c : E) * z i)) = u.ex (h z) ≫ act.act c :=
    GlobalTheory.T.exists_diagonal_coordinates_of_determinantCondition l1 l2 l3 l4 E H D t.pol u Hm₀ χ act ty hAH hty hdet
  obtain ⟨inj, disc, span, herm, pos, him⟩ := id hpol
  let F : 𝓞 E → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) := fun c =>
    h.toLinearMap ∘ₗ (LinearMap.pi fun i => ty i (c : E) • LinearMap.proj i) ∘ₗ h.symm.toLinearMap
  have hF₀ : ∀ c z, F c z = h fun i => ty i (c : E) * h.symm z i := fun c z => rfl
  have hF : ∀ c z, u.ex (F c z) = u.ex z ≫ act.act c := fun c z => by
    have := hh c (h.symm z)
    rw [h.apply_symm_apply] at this
    exact this
  let Q₁ : La →+ (Fin g → ℂ) := h.symm.toLinearMap.toAddMonoidHom.comp Q₀
  have hQ₁ : ∀ x, h (Q₁ x) = Q₀ x := fun x => h.apply_symm_apply _
  obtain ⟨Hm₁, inj₁, disc₁, span₁, herm₁, pos₁, him₁⟩ :=
    exists_coord Q₀ Hm₀ h (AddEquiv.refl _) Q₁ hQ₁ inj disc span herm pos
  obtain ⟨_, hs⟩ := exists_module (fun i => (ty i).comp (algebraMap (𝓞 E) E)) Q₁ inj₁ (fun c x => by
    haveI := act.hom c
    have h1 : u.ex (Q₀ x) = 1 := (u.ker _).2 ((hΛ _).2 ⟨x, rfl⟩)
    have h2 : u.ex (F c (Q₀ x)) = 1 := by
      rw [hF, h1]
      exact MonObj.one_comp _
    obtain ⟨y, hy⟩ := (hΛ _).1 ((u.ker _).1 h2)
    refine ⟨y, fun i => ?_⟩
    show h.symm (Q₀ y) i = _
    rw [hy, hF₀, h.symm_apply_apply]
    rfl)
  have hs₀ : ∀ c x, Q₀ (c • x) = F c (Q₀ x) := fun c x => by
    rw [← hQ₁, hF₀]
    exact congrArg h (funext fun i => hs c x i)
  have adj : ∀ (c : 𝓞 E) x y, EF (c • x) y = EF x (H.bar c • y) := fun c x y => by
    have := (GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint l1 l2 l3 l4 t.pol u Hm₀ χ _ _ (F c) (F (H.bar c)) hAH (act.hom _) (act.hom _)
      (hF c) (hF _)).1 (hadj c) (Q₀ x) (Q₀ y)
    have h2 : ((EF (c • x) y : ℤ) : ℝ) = EF x (H.bar c • y) := by
      rw [← him, ← him, hs₀, hs₀]
      exact congrArg Complex.im this
    exact_mod_cast h2
  obtain ⟨D', e, hp, hq, hEF⟩ := GlobalTheory.PeriodDatum.exists_datum E H La EF D.p D.q g ty Q₁ Hm₁ hty hbij adj hs inj₁
    disc₁ span₁ herm₁ pos₁ (fun x y => by rw [him₁]; exact him x y)
  let Q₂ : D'.La →+ (Fin g → ℂ) := Q₀.comp e.toLinearMap.toAddMonoidHom
  have hQ₂ : ∀ x, Q₂ x = Q₀ (e x) := fun x => rfl
  obtain ⟨f, ν, hgen, hf⟩ := GlobalTheory.T.period_lattice_in_genus_alt l1 l2 l3 l4 E H D D' t.pol u Hm₀ χ act Q₂ hp hq hAH
    (inj.comp e.injective)
    (fun z => (hΛ z).trans ⟨fun ⟨x, hx⟩ => ⟨e.symm x, (congrArg Q₀ (e.apply_symm_apply x)).trans hx⟩,
      fun ⟨x, hx⟩ => ⟨e x, hx⟩⟩)
    (fun x y => by rw [hEF]; exact him _ _)
    (fun c n x => by
      have := hF c ((n : ℂ)⁻¹ • Q₀ (e x))
      rw [map_smul, ← hs₀, ← map_smul e] at this
      exact this) I
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  obtain ⟨hζ', hev'⟩ := hf k (Nat.pos_of_ne_zero (Nat.cast_ne_zero.1 hk))
  let Q : D'.La →+ (Fin g → ℂ) := Q₁.comp e.toLinearMap.toAddMonoidHom
  obtain ⟨Hm, inj', disc', span', herm', pos', him'⟩ :=
    exists_coord Q₀ Hm₀ h e.toAddEquiv Q (fun x => hQ₁ _) inj disc span herm pos
  have him'' : ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y := fun x y => by
    rw [him', hEF]; exact him _ _
  refine ⟨D', f, ν, Q, Hm, hgen, hζ.symm.trans hζ', ⟨fun c x i => ?_, inj', disc', span', Hm, herm', pos', him''⟩,
    ⟨inj', disc', span', herm', pos', him''⟩, ?_⟩
  · show Q₁ (e (c • x)) i = _ * Q₁ (e x) i
    rw [map_smul]
    exact hs _ _ _
  · refine GlobalTheory.T.transport_thetaLevel_uniformisation_coordinates o g k J b em w w' t La EF lam ac Q₀ Hm₀ D'.La D'.EF
      (fun i => f k (bas (Pi.single i 1))) (fun j x => a j • x) Q Hm e.symm.toAddEquiv h.symm hpol
      ⟨inj', disc', span', herm', pos', him''⟩ (fun x => ?_) (fun x y => ?_) (fun j x => ?_) (fun i => ?_)
      ⟨u, χ, hAH, hΛ, hχ, hpt, hac⟩
    · show Q₁ (e (e.symm x)) = _
      rw [e.apply_symm_apply]
      rfl
    · show D'.EF (e.symm x) (e.symm y) = _
      rw [hEF, e.apply_symm_apply, e.apply_symm_apply]
    · show e.symm (ac j x) = a j • e.symm x
      rw [← map_smul]
      congr 1
      obtain ⟨G, hG, hG'⟩ := hac j
      haveI := u.discrete
      have h0 := linear_eq_zero_of_mem_discrete u.Λ (G - F (a j))
        (fun z => sub_mem_of_ex_eq u (by rw [hG', hF, haj])) (Q₀ x)
      apply inj
      rw [hs₀, ← hG]
      exact sub_eq_zero.1 h0
    · have h1 : u.ex ((k : ℂ)⁻¹ • Q₀ (lam i)) = u.ex ((k : ℂ)⁻¹ • Q₂ (f k (bas (Pi.single i 1)))) :=
        Over.OverMorphism.ext ((hpt i).symm.trans ((hev i).symm.trans (hev' _)))
      obtain ⟨y, hy⟩ := (hΛ _).1 (sub_mem_of_ex_eq u h1)
      refine ⟨e.symm y, e.injective (inj ?_)⟩
      show Q₀ (e (e.symm (lam i))) = Q₀ (e (f k (bas (Pi.single i 1)) + k • e.symm y))
      rw [e.apply_symm_apply, map_add (f := _), map_nsmul, e.apply_symm_apply, map_add (f := _), map_nsmul, hy, hQ₂, ← smul_sub,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk, one_smul]
      abel

end GlobalTheory.PELPeriod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPeriodsComplexPELObjectStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periods_complexPELObject : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (ty : Fin g → (E →+* ℂ)) (t : TObj g k J b (spMap em)), a w = H.w0 → a w' = H.bar H.w0 → em ρ = H.rt0 → IsTypeFn H D.p D.q ty → PELClass D a bas ρ em t → ∃ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (Q : D'.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') ∧ em (b.ζ : o) = Complex.exp (-(2 * Real.pi * Complex.I) * (ν k : ℂ) / k) ∧ IsPeriod D' ty Q ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ D'.EF x ((fun j x => a j • x) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i => f k (bas (Pi.single i 1))) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j x => a j • x) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  first | exact @GlobalTheory.PELPeriod.exists_period | exact GlobalTheory.PELPeriod.exists_period | (intros; apply GlobalTheory.PELPeriod.exists_period <;> assumption)
end
