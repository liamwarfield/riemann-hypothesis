module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.OneLeLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.ZetaClassCohomologyCompat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTameRelationProjected
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SmoothedZetaClassHodgeTateLawStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubMulAddLeOfUltrametricReplace

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.STop0
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sTop0 :
    UpperTheory.V.Z.Kato.Nb.STop0 := by
  intro Ω _ _ _ ε X l _ N _ x c d w g hH hLw hLift n r
  obtain ⟨ws, hws⟩ := hLw
  have api := sApi Ω ε X l
  have inv := sInvApi Ω ε X l N w
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨fun σ _ => (inv 0).2.2.2.2.2.2.1 _, fun σ _ τ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _,
      ⟨∅, fun σ _ τ _ _ => (api 0).2.2.2.2.2.2.2.2.1 _ _⟩⟩
  · have hlp : l.Prime := Fact.out
    have hL0 : r + n ≠ 0 := by omega
    have hM0 : N * l ^ (r + n) ≠ 0 := mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hlp.ne_zero)
    haveI : NeZero (N * l ^ (r + n)) := ⟨hM0⟩
    have hMeq : topM l n r (N * N) = N * (N * l ^ (r + n)) := by
      unfold topM
      ring
    haveI : NeZero (topM l n r (N * N)) := ⟨by rw [hMeq]; exact mul_ne_zero (NeZero.ne N) hM0⟩
    have hLev : Lev l n N (N * l ^ (r + n)) (topM l n r (N * N)) g :=
      ⟨hMeq, ⟨l ^ (r + n), by ring⟩, ⟨N * l ^ r, by ring⟩, hn, hH.cop, hH.g0⟩
    have hLv : Lv c d (N * l ^ (r + n)) := hH.lv hlp.ne_zero (NeZero.ne N) rfl
    have hdvdl : l ∣ N * l ^ (r + n) := Dvd.dvd.mul_left (dvd_pow_self l hL0) N
    have hOk := ok_UV (M := N * l ^ (r + n)) (L := r + n) hlp hH.odd hH.cop (by omega) hdvdl x
    obtain ⟨β, hβ, hcg⟩ := sTopRel Ω ε X l n N (N * l ^ (r + n)) (topM l n r (N * N)) w g hLev hLift c d ws hws hLv
      _ _ hOk _ _ (ixU_toQ rfl x) (ixV_toQ rfl)
    exact sTopCocG Ω ε X l n N _ _ w g hLev hLift _ _ hOk (ws n _) (hws.coc n _ hLv) _ β hβ hcg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormEqOneOfIsUnitToZModPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

noncomputable section

namespace GlobalTheory.K4.TwistClauses

variable {l : ℕ} [hl : Fact l.Prime]

theorem mem_O_of_pow_eq_one (c : Coef l) (z : Qbar l) (hz : z ^ (l - 1) = 1) : z ∈ c.O := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have ho : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  haveI : NeZero (l - 1) := ⟨by have := hl.out.two_le; omega⟩
  have h1 : IsPrimitiveRoot g (l - 1) := ho ▸ IsPrimitiveRoot.orderOf g
  have h2 : IsPrimitiveRoot (g : ZMod l) (l - 1) :=
    h1.map_of_injective (f := Units.coeHom (ZMod l)) Units.val_injective
  have hinj : Function.Injective (WittVector.teichmuller l (R := ZMod l)) := fun a b h => by
    simpa [WittVector.teichmuller_coeff_zero] using congrArg (fun x => x.coeff 0) h
  obtain ⟨ω, hω⟩ : ∃ ω : ℤ_[l], IsPrimitiveRoot ω (l - 1) :=
    ⟨_, (h2.map_of_injective hinj).map_of_injective (f := WittVector.equiv l) (WittVector.equiv l).injective⟩
  have hf : Function.Injective (algebraMap ℤ_[l] (Qbar l)) := fun a b h =>
    PadicInt.ext ((algebraMap ℚ_[l] (Qbar l)).injective h)
  obtain ⟨i, -, hi⟩ := (hω.map_of_injective hf).eq_pow_of_pow_eq_one hz
  rw [← hi]
  exact pow_mem (c.O.algebraMap_mem ω) i

theorem norm_algebraMap_padicInt (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) z‖ = ‖z‖ :=
  norm_algebraMap' (Qbar l) (z : ℚ_[l])

theorem norm_eq_one_of_pow {z : Qbar l} (hz : z ^ (l - 1) = 1) : ‖z‖ = 1 := by
  have h : ‖z‖ ^ (l - 1) = 1 := by rw [← norm_pow, hz, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by have := hl.out.two_le; omega)).1 h

theorem norm_eq_one_of_isUnit_toZModPow {r : ℕ} (hr : r ≠ 0) {a : ℤ_[l]} (ha : IsUnit (PadicInt.toZModPow r a)) : ‖a‖ = 1 := by
  by_contra h
  obtain ⟨k, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd a).1 (lt_of_le_of_ne a.norm_le_one h)
  rw [map_mul, map_natCast] at ha
  have h2 := (ZMod.isUnit_iff_coprime l (l ^ r)).1 (isUnit_of_mul_isUnit_left ha)
  exact hl.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h2 (dvd_pow_self l hr))

theorem norm_inv_pow_sub_le {r : ℕ} (hr : r ≠ 0) (e : ℕ) {a b : ℤ_[l]} (ha : IsUnit (PadicInt.toZModPow r a))
    (hab : PadicInt.toZModPow r a = PadicInt.toZModPow r b) :
    ‖(algebraMap ℤ_[l] (Qbar l) a ^ e)⁻¹ - (algebraMap ℤ_[l] (Qbar l) b ^ e)⁻¹‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have na : ‖algebraMap ℤ_[l] (Qbar l) a ^ e‖ = 1 := by
    rw [norm_pow, norm_algebraMap_padicInt, norm_eq_one_of_isUnit_toZModPow hr ha, one_pow]
  have nb : ‖algebraMap ℤ_[l] (Qbar l) b ^ e‖ = 1 := by
    rw [norm_pow, norm_algebraMap_padicInt, norm_eq_one_of_isUnit_toZModPow hr (hab ▸ ha), one_pow]
  have hk : b ^ e - a ^ e ∈ RingHom.ker (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)) := by
    rw [RingHom.mem_ker, map_sub, map_pow, map_pow, hab, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
  obtain ⟨k, hk⟩ := hk
  have hk' := congrArg (algebraMap ℤ_[l] (Qbar l)) hk
  rw [RingHom.map_sub, map_pow, map_pow, map_mul, map_pow, map_natCast] at hk'
  rw [inv_sub_inv (norm_ne_zero_iff.1 (by rw [na]; exact one_ne_zero)) (norm_ne_zero_iff.1 (by rw [nb]; exact one_ne_zero)),
    norm_div, norm_mul, na, nb, mul_one, div_one, hk', norm_mul, norm_algebraMap_padicInt]
  exact mul_le_of_le_one_right (norm_nonneg _) k.norm_le_one

theorem val_cast_eq {r : ℕ} (hr : r ≠ 0) (z : ZMod (l ^ r)) :
    ((z.val : ℕ) : ZMod l) = ZMod.castHom (dvd_pow_self l hr) (ZMod l) z := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  rw [ZMod.natCast_val]; rfl

theorem val_cast_ne_zero {r : ℕ} (hr : r ≠ 0) (x : (ZMod (l ^ r))ˣ) : (((x : ZMod (l ^ r)).val : ℕ) : ZMod l) ≠ 0 := by
  rw [val_cast_eq hr]
  exact (x.isUnit.map _).ne_zero

theorem val_level_zero (z : ZMod (l ^ 0)) : z.val = 0 := by
  haveI : NeZero (l ^ 0) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have := ZMod.val_lt z
  simp only [pow_zero] at this
  omega

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]


variable (Ω l) in
def cycRes : G ℚ Ω →* ZMod l :=
  (ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l)).toMonoidHom.comp ((Units.coeHom (ZMod (l ^ 1))).comp (cycMod ℚ Ω l 1))

theorem cycRes_eq_val (s : G ℚ Ω) : (((cycMod ℚ Ω l 1 s : ZMod (l ^ 1)).val : ℕ) : ZMod l) = cycRes l Ω s :=
  val_cast_eq one_ne_zero _

theorem cycRes_eq_cast {r : ℕ} (hr : r ≠ 0) (s : G ℚ Ω) :
    ZMod.castHom (dvd_pow_self l hr) (ZMod l) (cycMod ℚ Ω l r s : ZMod (l ^ r)) = cycRes l Ω s := by
  have h1r : 1 ≤ r := Nat.one_le_iff_ne_zero.2 hr
  show ZMod.castHom (dvd_pow_self l hr) (ZMod l) (PadicInt.toZModPow r (cycZ ℚ Ω l s : ℤ_[l])) =
    ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l) (PadicInt.toZModPow 1 (cycZ ℚ Ω l s : ℤ_[l]))
  rw [← PadicInt.zmod_cast_comp_toZModPow 1 r h1r, RingHom.comp_apply, ← RingHom.comp_apply _ (ZMod.castHom _ (ZMod (l ^ 1))),
    RingHom.ext_zmod (RingHom.comp _ _) (ZMod.castHom (dvd_pow_self l hr) (ZMod l))]

theorem cycRes_ne_zero (s : G ℚ Ω) : cycRes l Ω s ≠ 0 := by
  rw [← cycRes_eq_val]; exact val_cast_ne_zero one_ne_zero _

theorem exists_cycRes_eq [IsAlgClosure ℚ Ω] {r : ℕ} (hr : r ≠ 0) (x : (ZMod (l ^ r))ˣ) :
    ∃ t : G ℚ Ω, cycRes l Ω t = (((x : ZMod (l ^ r)).val : ℕ) : ZMod l) := by
  obtain ⟨t, rfl⟩ := cycMod_surjective Ω l r x
  exact ⟨t, by rw [val_cast_eq hr, cycRes_eq_cast hr]⟩

theorem continuous_cycBar' : Continuous (cycBar ℚ Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ ℚ Ω l)

theorem cycBar_val (s : G ℚ Ω) : (cycBar ℚ Ω l s : Qbar l) = algebraMap ℤ_[l] (Qbar l) (cycZ ℚ Ω l s : ℤ_[l]) := rfl

theorem cycZ_inertia [IsAlgClosure ℚ Ω] {q : Pl} (hq : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal) {B : ValuationSubring Ω}
    (hB : IsPlaceOver B q) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) B) : cycZ ℚ Ω l s = 1 :=
  Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
    rw [ReciprocityTheory.Gal.cycZ_toZModPow_eq hq hB (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
    simp)

theorem chiK_update {r : ℕ} (hr : r ≠ 0) (ψ : ZMod l → Qbar l) (x : (ZMod (l ^ r))ˣ) :
    chiK l (Function.update ψ 0 0) r x = chiK l ψ r x :=
  Function.update_of_ne (val_cast_ne_zero hr x) _ _

theorem chiK_update_zero (ψ : ZMod l → Qbar l) (x : (ZMod (l ^ 0))ˣ) : chiK l (Function.update ψ 0 0) 0 x = 0 := by
  rw [chiK, val_level_zero, Nat.cast_zero, Function.update_self]

section Chi

variable {ψ : ZMod l → Qbar l} {χ : G ℚ Ω →* (Qbar l)ˣ}

theorem chi_eq_one (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) {s : G ℚ Ω} (hs : cycRes l Ω s = 1) : χ s = 1 := by
  apply Units.ext
  rw [hχ, hs, ← map_one (cycRes l Ω), ← hχ, map_one]

theorem chi_pow (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) (s : G ℚ Ω) : (χ s : Qbar l) ^ (l - 1) = 1 := by
  rw [← Units.val_pow_eq_pow_val, ← map_pow,
    chi_eq_one hχ (by rw [map_pow]; exact ZMod.pow_card_sub_one_eq_one (cycRes_ne_zero s)), Units.val_one]

theorem chiK_pow [IsAlgClosure ℚ Ω] (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) {r : ℕ} (hr : r ≠ 0)
    (x : (ZMod (l ^ r))ˣ) : chiK l ψ r x ^ (l - 1) = 1 := by
  obtain ⟨t, ht⟩ := exists_cycRes_eq (Ω := Ω) hr x
  rw [chiK, ← ht, ← hχ]
  exact chi_pow hχ t

theorem chiK_mul_cycMod [IsAlgClosure ℚ Ω] (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) {r : ℕ} (hr : r ≠ 0)
    (x : (ZMod (l ^ r))ˣ) (s : G ℚ Ω) : chiK l ψ r (x * cycMod ℚ Ω l r s) = chiK l ψ r x * χ s := by
  obtain ⟨t, ht⟩ := exists_cycRes_eq (Ω := Ω) hr x
  rw [chiK, chiK, val_cast_eq hr, Units.val_mul, map_mul, ← val_cast_eq hr, ← ht, cycRes_eq_cast hr, ← map_mul, ← hχ, ← hχ,
    map_mul, Units.val_mul]

omit hl in
theorem chiK_succ [Fact l.Prime] (ψ : ZMod l → Qbar l) {r : ℕ} (hr : r ≠ 0) (x : (ZMod (l ^ (r + 1)))ˣ) :
    chiK l ψ (r + 1) x =
      chiK l ψ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x) := by
  rw [chiK, chiK, val_cast_eq hr, val_cast_eq (Nat.succ_ne_zero r)]
  congr 1
  exact (RingHom.congr_fun (RingHom.ext_zmod ((ZMod.castHom (dvd_pow_self l hr) (ZMod l)).comp
    (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)))) (ZMod.castHom (dvd_pow_self l (Nat.succ_ne_zero r)) (ZMod l)))
    (x : ZMod (l ^ (r + 1)))).symm

theorem eta_shift [IsAlgClosure ℚ Ω] (hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s)) (e : ℕ) {r : ℕ} (hr : r ≠ 0)
    (s : G ℚ Ω) (x : (ZMod (l ^ r))ˣ) :
    ‖(((((x * cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r (x * cycMod ℚ Ω l r s) -
      ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x * ((eps l s ^ e)⁻¹ * (χ s : Qbar l))‖ ≤
      ‖((l : ℕ) : Qbar l) ^ r‖ := by
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have h := norm_inv_pow_sub_le (l := l) hr e
    (a := ((((x * cycMod ℚ Ω l r s : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val : ℕ) : ℤ_[l]))
    (b := (((x : ZMod (l ^ r)).val : ℕ) : ℤ_[l]) * (cycZ ℚ Ω l s : ℤ_[l]))
    (by rw [map_natCast, ZMod.natCast_zmod_val]; exact Units.isUnit _)
    (by rw [map_mul, map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; rfl)
  rw [map_mul, map_natCast, map_natCast, ← cycBar_val, mul_pow, mul_inv] at h
  rw [chiK_mul_cycMod hχ hr, show ∀ a b c u v : Qbar l, a * (u * v) - b * u * (c * v) = u * v * (a - b * c) from
    fun _ _ _ _ _ => by ring, norm_mul, norm_mul, norm_eq_one_of_pow (chiK_pow hχ hr x), norm_eq_one_of_pow (chi_pow hχ s),
    one_mul, one_mul]
  exact h

end Chi

end GlobalTheory.K4.TwistClauses

namespace GlobalTheory.K4


open TwistClauses in
theorem twist_clauses : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
  (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
  (ψ : ZMod l → Qbar l) (cf : Coef l) (S : Finset Pl),
  Nf e S A W → l ≠ 2 → (∃ x, cw x ≠ 0) → AdmWn ι e gN A W X pr N cw c d gm ψ cf →
  ∃ θ : G ℚ Ω →* (Qbar l)ˣ, Continuous θ ∧ (∀ s, mat W s = (θ s : Qbar l) • rhoK W e ψ s) ∧
    (∀ c' : Coef l, (∀ s i j, mat W s i j ∈ c'.O) → ∀ s i j, rhoK W e ψ s i j ∈ c'.O) ∧
    (∀ c' : Coef l, ∀ r x, chiK l (Function.update ψ 0 0) r x ∈ c'.O) ∧
    (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖chiK l (Function.update ψ 0 0) (r + 1) x - chiK l (Function.update ψ 0 0) r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
    (∀ r s x, ‖(fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l (Function.update ψ 0 0) r x) (x * cycMod ℚ Ω l r s) - (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l (Function.update ψ 0 0) r x) x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) ∧
    (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∀ s ∈ Ine (F := ℚ) B, θ s = 1) ∧
    (∀ s ∈ Dec (F := ℚ) A, rhoK W e ψ s 1 0 = 0 ∧ rhoK W e ψ s 1 1 = (nuD W e ψ s : Qbar l)) ∧
    (∀ r, (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l (Function.update ψ 0 0) r x) = (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r x)) := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ cw c d gm ψ cf S hNf _ hx hadm
  obtain ⟨x₀, hx₀⟩ := hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, χ, hkill, -, hχ'⟩ := hadm.1 x₀ hx₀
  have hχ : ∀ s, (χ s : Qbar l) = ψ (cycRes l Ω s) := fun s => by rw [hχ', cycRes_eq_val]
  set θ : G ℚ Ω →* (Qbar l)ˣ := cycBar ℚ Ω l ^ (-(e : ℤ)) * χ with hθdef
  have hθu : ∀ s, θ s = cycBar ℚ Ω l s ^ (-(e : ℤ)) * χ s := fun s => rfl
  have hθ : ∀ s, (θ s : Qbar l) = (eps l s ^ e)⁻¹ * χ s := fun s => by
    rw [hθu, Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_neg, zpow_natCast]
  have hth : ∀ s, thK l e ψ s = θ s := fun s => by rw [hθ, hχ', thK]
  have hρ : ∀ s i j, rhoK W e ψ s i j = (θ s : Qbar l)⁻¹ * mat W s i j := fun s i j => by
    rw [rhoK, hth, Matrix.smul_apply, smul_eq_mul]
  refine ⟨θ, ?_, fun s => ?_, fun c' hW s i j => ?_, fun c' r x => ?_, fun r x => ?_, fun r s x => ?_,
    fun q hq B hB s hs => ?_, fun s hs => ?_, fun r => funext fun x => ?_⟩
  · exact (continuous_cycBar'.zpow (-(e : ℤ))).mul (GlobalTheory.Ord2.VanishKato.cont_kills l hl.out.one_le χ hkill)
  · rw [rhoK, hth, smul_smul, mul_inv_cancel₀ (θ s).ne_zero, one_smul]
  · rw [hρ, hθ, mul_inv, inv_inv]
    refine mul_mem (mul_mem (pow_mem (c'.O.algebraMap_mem (cycZ ℚ Ω l s : ℤ_[l])) e) ?_) (hW s i j)
    exact mem_O_of_pow_eq_one c' _ (by rw [inv_pow, chi_pow hχ, inv_one])
  · rcases eq_or_ne r 0 with rfl | hr
    · rw [chiK_update_zero]; exact zero_mem _
    · rw [chiK_update hr]; exact mem_O_of_pow_eq_one c' _ (chiK_pow hχ hr x)
  · rcases eq_or_ne r 0 with rfl | hr
    · rw [chiK_update_zero, chiK_update (Nat.succ_ne_zero 0), sub_zero,
        norm_eq_one_of_pow (chiK_pow hχ (Nat.succ_ne_zero 0) x), pow_zero, norm_one]
    · rw [← chiK_succ _ hr, sub_self, norm_zero]; exact norm_nonneg _
  · rcases eq_or_ne r 0 with rfl | hr
    · simp only [chiK_update_zero, mul_zero, zero_mul, sub_self, norm_zero]; exact norm_nonneg _
    · simp only [chiK_update hr, hθ]
      exact eta_shift hχ e hr s x
  · have hz := cycZ_inertia hq hB hs
    have h1 : cycBar ℚ Ω l s = 1 := by rw [cycBar, MonoidHom.comp_apply, hz, map_one]
    have h2 : cycRes l Ω s = 1 := by
      rw [cycRes, MonoidHom.comp_apply, MonoidHom.comp_apply, cycMod, MonoidHom.comp_apply, hz, map_one, map_one, map_one]
    rw [hθu, h1, chi_eq_one hχ h2, one_zpow, one_mul]
  · have h10 := hNf.upper s hs
    have hdet : (mat W s).det ≠ 0 := (Matrix.GeneralLinearGroup.det (W s)).ne_zero
    rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
    have h11 : rhoK W e ψ s 1 1 ≠ 0 := by
      rw [hρ]; exact mul_ne_zero (inv_ne_zero (θ s).ne_zero) (right_ne_zero_of_mul hdet)
    refine ⟨by rw [hρ, h10, mul_zero], ?_⟩
    rw [nuD, dite_eq_left h11, Units.val_mk0]
  · rcases eq_or_ne r 0 with rfl | hr
    · rw [val_level_zero, Nat.cast_zero, zero_pow (Nat.one_le_iff_ne_zero.1 hNf.e_pos), inv_zero, zero_mul, zero_mul]
    · rw [chiK_update hr]

end GlobalTheory.K4

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaSystemExponentRaiseOfPrimePowSmul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

namespace GlobalTheory.K4

theorem zetaSystem_exponent_raise_of_prime_pow_smul : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (W : R2 Ω l) (e : ℕ) (ψ : ZMod l → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N)
  (c d k : ℕ) (g : (ZMod l)ˣ → SL(2, ℤ)) (cf : Coef l) (c₀ m : ℕ)
  (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  (∀ b b', pr (b + b') = pr b + pr b') →
  (∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b) →
  IsZetaSystemFixedExponent X l pr W e ψ N x c d k g cf c₀ Y →
  IsZetaSystemFixedExponent X l pr W e ψ N x c d k g cf (c₀ + m) (fun r s y => ((l : Qbar l) ^ m) • Y r s y) := by
  intro l _ Ω _ _ ε X pr W e ψ N _ x c d k g cf c₀ m Y hadd hsmul hZ r n
  obtain ⟨bB, hB, b, hb, hY⟩ := hZ r n
  have hl : ‖((l : ℕ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ l
  have hlm : ‖((l : ℕ) : Qbar l) ^ m‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hl
  have hpr : ∀ v : X.Fn l, pr (((l : ℤ_[l]) ^ m) • v) = ((l : ℕ) : Qbar l) ^ m • pr v := by
    intro v
    rw [hsmul]
    congr 1
    simp
  refine ⟨fun σ => ((l : ℤ_[l]) ^ m) • bB σ, ?_, fun y => ((l : ℕ) : Qbar l) ^ m • b y, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨h1, h2⟩ := hB σ hσ
    refine ⟨Submodule.smul_mem _ _ h1, fun u => ?_⟩
    have : (((l : ℤ_[l]) ^ m) • bB σ) u - ((l : ℤ_[l]) ^ (c₀ + m)) • clsBmu X l n r N x c d k g σ u
        = ((l : ℤ_[l]) ^ m) • (bB σ u - ((l : ℤ_[l]) ^ c₀) • clsBmu X l n r N x c d k g σ u) := by
      rw [smul_sub, smul_smul, ← pow_add, add_comm m c₀]
      rfl
    rw [this, LinearMap.map_smul, h2 u, smul_zero]
  · intro y i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact cf.O.mul_mem (cf.O.pow_mem (cf.O.natCast_mem l) m) (hb y i)
  · intro s y
    have hYf : YfB X l pr W e ψ n r N (fun σ => ((l : ℤ_[l]) ^ m) • bB σ) s y
        = ((l : ℕ) : Qbar l) ^ m • YfB X l pr W e ψ n r N bB s y := by
      unfold YfB GlobalTheory.KA.push
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [hpr, Matrix.mulVec_smul]
    rw [hYf]
    intro i
    have h := hY s y i
    unfold Cg at h ⊢
    have hrw : ((l : ℕ) : Qbar l) ^ m • Y r s y i -
        (((l : ℕ) : Qbar l) ^ m • YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ (((l : ℕ) : Qbar l) ^ m • b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)) -
            ((l : ℕ) : Qbar l) ^ m • b y)) i
        = ((l : ℕ) : Qbar l) ^ m * (Y r s y i - (YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i) := by
      simp only [Matrix.mulVec_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    show ‖_‖ ≤ _
    simp only [Pi.smul_apply, smul_eq_mul] at hrw ⊢
    rw [hrw, norm_mul]
    calc _ ≤ 1 * ‖Y r s y i - (YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹) - b y)) i‖ :=
          mul_le_mul_of_nonneg_right hlm (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h

end GlobalTheory.K4
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShCocWsumProps
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

namespace GlobalTheory.K4

theorem shCoc_wsum_props : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
  (ρ : (Ω ≃ₐ[ℚ] Ω) → Matrix (Fin 2) (Fin 2) (Qbar l)) (cf : Coef l) (ι : Type) [Fintype ι] (cw : ι → Qbar l)
  (Yx : ι → ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  (∀ i r, ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Yx i r)) →
  (∀ i r, Yx i r = push (redL l r) (Yx i (r + 1))) →
  (∀ i r y j, Continuous fun s => Yx i r s y j) →
  (∀ i r s u j, Yx i r s u j ∈ cf.O) → (∀ i, cw i ∈ cf.O) →
  (∀ r, ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (fun s y => ∑ i, cw i • Yx i r s y)) ∧
  (∀ r, (fun s y => ∑ i, cw i • Yx i r s y) = push (redL l r) (fun s y => ∑ i, cw i • Yx i (r + 1) s y)) ∧
  (∀ r y j, Continuous fun s => (∑ i, cw i • Yx i r s y) j) ∧
  (∀ r s u j, (∑ i, cw i • Yx i r s u) j ∈ cf.O) := by
  intro l _ Ω _ _ ρ cf ι _ cw Yx hC hP hCont hO hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r s t x
    have := fun i => hC i r s t x
    simp only [this, Finset.sum_add_distrib, smul_add, Matrix.mulVec_sum, Matrix.mulVec_smul]
  · intro r
    funext s y
    simp only [push]
    conv_lhs => rw [show (∑ i, cw i • Yx i r s y) = ∑ i, cw i • push (redL l r) (Yx i (r + 1)) s y from by
      simp only [← hP]]
    simp only [push, Finset.smul_sum]
    exact Finset.sum_comm
  · intro r y j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (hCont i r y j)
  · intro r s u j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hw i) (hO i r s u j)

end GlobalTheory.K4
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.Ml
section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.IsCompactIntegralCoefficients
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Topology

private theorem UpperTheory.Kd.K4.isCompact_integralCoefficients {l : ℕ} [Fact l.Prime] (c : Coef l) : IsCompact (c.O : Set (Qbar l)) := by
  haveI : ContinuousSMul ℤ_[l] (PadicAlgCl l) := by
    refine ⟨?_⟩
    have : (fun q : ℤ_[l] × PadicAlgCl l => q.1 • q.2) = fun q => (q.1 : ℚ_[l]) • q.2 := by
      funext q; rfl
    rw [this]
    exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd
  have hfg : (Subalgebra.toSubmodule c.O).FG := Module.Finite.iff_fg.1 c.fin
  exact Submodule.isCompact_of_fg hfg

private theorem UpperTheory.Kd.K4.norm_le_one_of_mem_coefficient_ring {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨M, hM⟩ := (UpperTheory.Kd.K4.isCompact_integralCoefficients c).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
  have := hM _ (c.O.pow_mem ha n)
  rw [norm_pow] at this
  linarith

private theorem UpperTheory.Kd.K4.norm_nat_cast_prime_lt_one_padic_closure (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem UpperTheory.Kd.K4.topCocycle_finsetSum (hA : SApi) (hI : SInvApi) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n M : ℕ) {ι : Type} (S : Finset ι)
    (z : ι → (Ω ≃ₐ[ℚ] Ω) → X.Fn l) (h : ∀ i ∈ S, TopCoc X l N w n M (z i)) :
    TopCoc X l N w n M (fun σ => ∑ i ∈ S, z i σ) := by
  classical
  have hsum := (hA Ω ε X l n).2.2.2.1
  refine ⟨fun σ hσ => ?_, fun σ hσ τ hτ => ?_, ?_⟩
  · exact (hI Ω ε X l N w n).2.2.2.2.1 ι S _ fun i hi => (h i hi).inv σ hσ
  · have e : (∑ i ∈ S, z i σ) + X.galB l σ (∑ i ∈ S, z i τ) = ∑ i ∈ S, (z i σ + X.galB l σ (z i τ)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_add_distrib]
    rw [e]
    exact hsum ι S _ _ fun i hi => (h i hi).coc σ hσ τ hτ
  · choose! T hT using fun i hi => (h i hi).loc
    refine ⟨S.biUnion T, fun σ hσ τ hτ hst => ?_⟩
    exact hsum ι S _ _ fun i hi => hT i hi σ hσ τ hτ fun a ha => hst a (Finset.mem_biUnion.2 ⟨i, hi, ha⟩)

private theorem UpperTheory.Kd.K4.cocycleBound_finsetSum (hC : SCohApi) {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N w n : ℕ) (hN : 0 < N) {A : Type} [CommGroup A]
    (κ : (Ω ≃ₐ[ℚ] Ω) → A) {ι : Type} (S : Finset ι) (z z' : ι → (Ω ≃ₐ[ℚ] Ω) → A → X.Fn l)
    (h : ∀ i ∈ S, CohB X l N w n κ (z i) (z' i)) : CohB X l N w n κ (∑ i ∈ S, z i) (∑ i ∈ S, z' i) := by
  classical
  have hc := hC Ω ε X l N w n hN A κ
  induction S using Finset.induction_on with
  | empty => simpa using hc.1.refl 0
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (hc.2.2.1 _ _ _ _ (h a (by simp)) (ih fun i hi => h i (by simp [hi]))).1

private theorem UpperTheory.Kd.K4.shiftedBound_finsetSum {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (M : ℕ) {ι : Type} (S : Finset ι) (z : ι → (Ω ≃ₐ[ℚ] Ω) → X.Fn l) :
    shB X l M (fun σ => ∑ i ∈ S, z i σ) = ∑ i ∈ S, shB X l M (z i) := by
  funext s y
  set_option synthInstance.maxHeartbeats 100000 in
    simp [shB, Finset.sum_apply, map_sum]

private theorem UpperTheory.Kd.K4.pushforward_finsetSum {Γ : Type} [Group Γ] {B A M ι : Type} [Fintype B] [DecidableEq A] [AddCommMonoid M]
    (π : B → A) (S : Finset ι) (f : ι → Γ → B → M) :
    GlobalTheory.KA.push π (∑ i ∈ S, f i) = ∑ i ∈ S, GlobalTheory.KA.push π (f i) := by
  funext s y
  simp only [GlobalTheory.KA.push, Finset.sum_apply]
  exact Finset.sum_comm

private def UpperTheory.Kd.K4.unitsPowPrimeReduction (l r : ℕ) : (ZMod (l ^ (r + 1)))ˣ →* (ZMod (l ^ r))ˣ :=
  Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom

private theorem UpperTheory.Kd.K4.unitsReduction_coe (l r : ℕ) : (⇑(unitsPowPrimeReduction l r)) = redL l r := rfl

private theorem UpperTheory.Kd.K4.unitsReduction_surjective (l r : ℕ) [Fact l.Prime] : Function.Surjective (unitsPowPrimeReduction l r) :=
  ZMod.unitsMap_surjective (pow_dvd_pow l (Nat.le_succ r))

private def UpperTheory.Kd.K4.unitsLevelToPrimePowReduction (l n r N : ℕ) : (ZMod (topM l n r N))ˣ →* (ZMod (l ^ r))ˣ :=
  Units.map (ZMod.castHom (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) N) (ZMod (l ^ r))).toMonoidHom

attribute [-instance] GlobalTheory.KZ.ClsMod.neZero_pow

theorem UpperTheory.Kd.K4.mlOf2 :
    SymEx → SApi → SInvApi → SBStab → SSlD → SCohApi → SCycZ → STop0 → KatoClassNormCompatibleCyclotomic → KatoClassCompatibleModPowers → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N : ℕ) [NeZero N] (e : ℕ),
      Nat.Coprime l N → l ≠ 2 → 1 ≤ e → ∃ c₁ : ℕ, ∀ c₀ : ℕ, c₁ ≤ c₀ → ∀ (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l)
      (pr : X.Fn l → Fin 2 → Qbar l) (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
      AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf → ∃ Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
        IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y ∧ (∀ r, ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
        (∀ r, Y r = GlobalTheory.KA.push (redL l r) (Y (r + 1))) ∧ (∀ r y i, Continuous fun s => Y r s y i) ∧ (∀ r s u i, Y r s u i ∈ cf.O) := by
  intro hSym hA hI hBS hS hC hZc hT hNr hNn l _ Ω _ _ _ ε X N _ e hlN hl2 he
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨c₁, hc₁⟩ := UpperTheory.Kd.K4.mlB hA hI hBS hS ε X l N (2 * e - 1) hN
  refine ⟨c₁, fun c₀ hc₀ ι gN A W pr x c d gm ψ cf hAd => ?_⟩
  obtain ⟨hc1, hd1, hcc, hdc, hadd, hsm, hint, heq, -, -, hg0, -⟩ := hAd
  have hk : 2 * e + 1 - 2 = 2 * e - 1 := by omega
  have hcy := (hS Ω ε X N hN).2.2.2.2.2.2.2
  have hHyp : ∀ r₀, Hyp l N c d (gm r₀) := fun r₀ => ⟨hl2, hlN, hc1, hd1, hcc, hdc, hg0 r₀⟩
  have hLaws : ∃ ws, UpperTheory.V.Z.Kato.Sym.Laws X l c d ws :=
    hSym Ω ε X l c d Fact.out hc1 hd1 (Nat.Coprime.coprime_dvd_right ⟨l * N, by ring⟩ hcc)
      (Nat.Coprime.coprime_dvd_right ⟨l * N, by ring⟩ hdc)
  have hL : LiftsWith X l N (2 * e - 1) (cL X l N (2 * e - 1)) :=
    Classical.epsilon_spec (UpperTheory.Kd.K4.liftH ε X l N (2 * e - 1) hl2 hN hlN ⟨e - 1, by omega⟩)
  let κ : ∀ r, (Ω ≃ₐ[ℚ] Ω) →* (ZMod (l ^ r))ˣ := fun r => (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹
  have hκ : ∀ r s, κ r s = (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹ := fun _ _ => rfl
  let zz : ℕ → ℕ → (Ω ≃ₐ[ℚ] Ω) → X.Fn l := fun n r σ => ∑ r₀, cls0 X l n r N x c d (2 * e - 1) (gm r₀) σ
  let Z : ∀ (_ r : ℕ), (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → X.Fn l := fun n r s y =>
    GlobalTheory.KA.push (unitsLevelToPrimePowReduction l n r (N * N)) (shB X l (topM l n r (N * N)) (zz n r)) s (y * 1)
  have hZeq : ∀ n r, Z n r = ∑ r₀, Y0 X l n r N x c d (2 * e - 1) (gm r₀) := by
    intro n r
    funext s y
    have e1 : shB X l (topM l n r (N * N)) (zz n r) =
        ∑ r₀, shB X l (topM l n r (N * N)) (cls0 X l n r N x c d (2 * e - 1) (gm r₀)) :=
      shiftedBound_finsetSum X l _ _ _
    simp only [Z, e1, pushforward_finsetSum, Finset.sum_apply, mul_one]
    rfl
  have hπκ : ∀ r s, unitsPowPrimeReduction l r (κ (r + 1) s) = κ r s := by
    intro r s
    rw [hκ, hκ, map_inv, (hZc Ω l (r + 1) s).1, (hZc Ω l r s).1]
    exact congrArg (·⁻¹) ((hcy (l ^ (r + 1)) s).2.2.2.2 (l ^ r) (pow_dvd_pow l (Nat.le_succ r)))
  have hred : ∀ n r s, unitsLevelToPrimePowReduction l n r (N * N) (cycM (topM l n r (N * N)) s)⁻¹ = κ r s := by
    intro n r s
    rw [map_inv, hκ, (hZc Ω l r s).1]
    exact congrArg (·⁻¹) ((hcy (topM l n r (N * N)) s).2.2.2.2 (l ^ r)
      (Dvd.dvd.mul_right (pow_dvd_pow l (Nat.le_add_right r n)) (N * N)))
  have htop : ∀ n r, TopCoc X l N (2 * e - 1) n (topM l n r (N * N)) (zz n r) := fun n r =>
    topCocycle_finsetSum hA hI X l N _ n _ Finset.univ _ fun r₀ _ => hT Ω ε X l N x c d _ (gm r₀) (hHyp r₀) hLaws hL n r
  have hcr : ∀ n r, CohB X l N (2 * e - 1) n (κ r) (GlobalTheory.KA.push (unitsPowPrimeReduction l r) (Z n (r + 1))) (Z n r) := by
    intro n r
    rw [hZeq, hZeq, unitsReduction_coe, pushforward_finsetSum]
    exact cocycleBound_finsetSum hC X l N _ n hN _ Finset.univ _ _ fun r₀ _ => hNr Ω ε X l N x c d _ (gm r₀) (hHyp r₀) hLaws hL n r
  have hcn : ∀ n r, CohB X l N (2 * e - 1) n (κ r) (Z (n + 1) r) (Z n r) := by
    intro n r
    rw [hZeq, hZeq]
    exact cocycleBound_finsetSum hC X l N _ n hN _ Finset.univ _ _ fun r₀ _ => hNn Ω ε X l N x c d _ (gm r₀) (hHyp r₀) hLaws hL n r
  obtain ⟨YB, hYB, hcoc, hcont, hcomp, hlast⟩ := hc₁ c₀ hc₀ (fun r => (ZMod (l ^ r))ˣ) (fun r => unitsPowPrimeReduction l r) κ
    (fun n r => topM l n r (N * N)) (fun n r => unitsLevelToPrimePowReduction l n r (N * N)) (fun _ _ => 1) zz Z (fun r => unitsReduction_surjective l r) hπκ hred
    (fun _ _ _ _ => rfl) htop hcr hcn
  let prA : X.Fn l →+ (Fin 2 → Qbar l) := AddMonoidHom.mk' pr hadd
  have hprA : ∀ b, prA b = pr b := fun _ => rfl
  have hpush : ∀ {B A' : Type} [Fintype B] [DecidableEq A'] (π : B → A') (f : (Ω ≃ₐ[ℚ] Ω) → B → X.Fn l) s y,
      pr (GlobalTheory.KA.push π f s y) = GlobalTheory.KA.push π (fun s y => pr (f s y)) s y := by
    intro B A' _ _ π f s y
    exact map_sum prA _ _
  have hln : ∀ n d, d ∈ X.B N l (2 * e - 1) → ∀ i, ‖pr ((l : ℤ_[l]) ^ n • d) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    intro n d hd i
    have e1 : algebraMap ℚ_[l] (Qbar l) (((l : ℤ_[l]) ^ n : ℤ_[l]) : ℚ_[l]) = ((l : ℕ) : Qbar l) ^ n := by simp
    rw [hsm, e1, Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem_coefficient_ring cf (hint d hd i))
  have hfix : ∀ (M : ℕ) [NeZero M] (s : Ω ≃ₐ[ℚ] Ω) (y : (ZMod M)ˣ),
      (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ * s * repM M (y * (cycM M s)⁻¹) ∈ fixMu Ω M := by
    intro M _ s y
    have h1 : cycM M (1 : Ω ≃ₐ[ℚ] Ω) = 1 := ((hcy M 1).2.2.2.1).1 (one_mem _)
    have h2 : cycM M (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ * y = 1 := by
      have := (hcy M (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹).2.1 (repM M y)
      rwa [inv_mul_cancel, h1, (hcy M s).2.2.1 y, eq_comm] at this
    rw [(hcy M _).2.2.2.1, (hcy M _).2.1, (hcy M _).2.1, (hcy M s).2.2.1]
    calc cycM M (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ * cycM M s * (y * (cycM M s)⁻¹)
        = (cycM M (repM M y : Ω ≃ₐ[ℚ] Ω)⁻¹ * y) * (cycM M s * (cycM M s)⁻¹) := by ac_rfl
      _ = 1 := by rw [h2, mul_inv_cancel, one_mul]
  refine ⟨fun r s y => pr (YB r s y), fun r n => ?_, fun r s s' y => ?_, fun r => ?_, fun r y i => ?_,
    fun r s u i => hint _ (hYB r s u) i⟩
  · obtain ⟨bB, hbB, b, hb, h⟩ := hlast r n
    refine ⟨bB, fun σ hσ => ?_, fun y => pr (b y), fun y i => hint _ (hb y) i, fun s y i => ?_⟩
    · rw [clsBmu_eq, hk]
      exact hbB σ hσ
    · obtain ⟨dd, hdd, hde⟩ := h s y
      rw [mul_one] at hde
      have hf : (fun s y => pr (shB X l (topM l n r (N * N)) bB s y)) = fun s y =>
          rhoK W e ψ (repM (topM l n r (N * N)) y) *ᵥ pr (bB ((repM (topM l n r (N * N)) y)⁻¹ * s *
            repM (topM l n r (N * N)) (y * (cycM (topM l n r (N * N)) s)⁻¹))) := by
        funext s y
        exact heq _ _ (hbB _ (hfix _ s y)).1
      have hsh : pr (GlobalTheory.KA.push (unitsLevelToPrimePowReduction l n r (N * N)) (shB X l (topM l n r (N * N)) bB) s y) =
          YfB X l pr W e ψ n r N bB s y := by
        rw [hpush, hf]
        rfl
      have hdec : YB r s y = GlobalTheory.KA.push (unitsLevelToPrimePowReduction l n r (N * N)) (shB X l (topM l n r (N * N)) bB) s y +
          (X.galB l s (b (y * κ r s)) - b y) + (l : ℤ_[l]) ^ n • dd := by
        rw [← hde]; abel
      have hprY : pr (YB r s y) = YfB X l pr W e ψ n r N bB s y +
          (rhoK W e ψ s *ᵥ pr (b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)) - pr (b y)) + pr ((l : ℤ_[l]) ^ n • dd) := by
        rw [hdec, hadd, hadd, ← hprA (_ - _), map_sub, hprA, hprA, heq _ _ (hb _), hsh]
        rfl
      change ‖pr (YB r s y) i - (YfB X l pr W e ψ n r N bB s y +
        (rhoK W e ψ s *ᵥ pr (b (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)) - pr (b y))) i‖ ≤ _
      have e3 : ∀ a b : Fin 2 → Qbar l, (a + b) i - a i = b i := fun a b => by simp
      rw [hprY, e3]
      exact hln n dd hdd i
  · change pr (YB r (s * s') y) = pr (YB r s y) + rhoK W e ψ s *ᵥ pr (YB r s' (y * κ r s))
    rw [hcoc, hadd, heq _ _ (hYB _ _ _)]
  · funext s y
    change pr (YB r s y) = GlobalTheory.KA.push (redL l r) (fun s y => pr (YB (r + 1) s y)) s y
    rw [hcomp r]
    exact hpush _ _ s y
  · rw [continuous_iff_continuousAt]
    intro s
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε' hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (norm_nat_cast_prime_lt_one_padic_closure l)
    rw [← norm_pow] at hn
    filter_upwards [hcont r n s y] with t ht
    obtain ⟨dd, hdd, hde⟩ := ht
    rw [dist_eq_norm]
    have e1 : pr (YB r t y) i - pr (YB r s y) i = pr ((l : ℤ_[l]) ^ n • dd) i := by
      rw [← hde, ← hprA (_ - _), map_sub, hprA, hprA]
      rfl
    rw [e1]
    exact lt_of_le_of_lt (hln n dd hdd i) hn
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

theorem UpperTheory.Kd.K4.ml :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
      (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
      (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (x : ZMod N) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
      (ψ : ZMod l → Qbar l) (cf : Coef l),
      (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf →
      ∃ c₁ : ℕ, ∀ c₀ : ℕ, c₁ ≤ c₀ →
      ∃ Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l,
        IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y ∧
        (∀ r, ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
        (∀ r, Y r = push (redL l r) (Y (r + 1))) ∧ (∀ r y i, Continuous fun s => Y r s y i) ∧ (∀ r s u i, Y r s u i ∈ cf.O) := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf _ hc hl he _ hA
  obtain ⟨c₁, h⟩ := UpperTheory.Kd.K4.mlOf2 UpperTheory.V.Z.Kato.Sym.symEx UpperTheory.V.Z.Kato.Nb.sApi UpperTheory.V.Z.Kato.Nb.sInvApi UpperTheory.V.Z.Kato.Nb.sBStab
    UpperTheory.V.Z.Kato.Nb.sSlD UpperTheory.V.Z.Kato.Nb.sCohApi UpperTheory.V.Z.Kato.Nb.sCycZ UpperTheory.V.Z.Kato.Nb.sTop0 UpperTheory.V.Z.Kato.Nb.kato_norm_compatible_cyclotomic_tower
    UpperTheory.V.Z.Kato.Nb.katoZetaElement_normCompatible_in_lTower l Ω ε X N e hc hl he
  exact ⟨c₁, fun c₀ h₀ => h c₀ h₀ ι gN A W pr x c d gm ψ cf hA⟩
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA
open scoped Matrix MatrixGroups

namespace UpperTheory.Kd.K4

theorem g3 : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
  (gN : Newform (2 * e + 1)) (A : ValuationSubring Ω) (W : R2 Ω l) (ε : Ω →+* ℂ) (X : Tower Ω ε)
  (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ))
  (ψ : ZMod l → Qbar l) (cf : Coef l),
  (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e → (∃ x, cw x ≠ 0) →
  AdmWn ι e gN A W X pr N cw c d gm ψ cf → Continuous W → (∀ s i j, mat W s i j ∈ cf.O) →
  ∃ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
    IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y ∧
    (∀ r, ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
    (∀ r, Y r = push (redL l r) (Y (r + 1))) ∧ (∀ r y i, Continuous fun s => Y r s y i) ∧ (∀ r s u i, Y r s u i ∈ cf.O) := by
  intro l _ Ω _ _ _ ι e gN A W ε X pr N _ cw c d gm ψ cf hφ hgm hcop hl2 he hcw hadm _hWc _hWO
  obtain ⟨x₀, hx₀⟩ := hcw
  have h3 : ∀ x : ZMod N, AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf := fun x => hadm.1 x₀ hx₀
  have hml := fun x : ZMod N => UpperTheory.Kd.K4.ml l Ω ι e gN A W ε X pr N x c d gm ψ cf hgm hcop hl2 he hφ (h3 x)
  choose c₁ hc₁ using hml
  let C : ℕ := Finset.univ.sup c₁
  have hC : ∀ x, c₁ x ≤ C := fun x => Finset.le_sup (f := c₁) (Finset.mem_univ x)
  have hY := fun x : ZMod N => hc₁ x C (hC x)
  choose Yx hZ hS hP hCt hO using hY
  obtain ⟨k1, k2, k3, k4⟩ := GlobalTheory.K4.shCoc_wsum_props l Ω (rhoK W e ψ) cf (ZMod N) cw Yx hS hP hCt hO hadm.2
  refine ⟨C, fun r s y => ∑ x, cw x • Yx x r s y, ⟨Yx, hZ, fun r s y => rfl⟩, k1, k2, k3, k4⟩

end UpperTheory.Kd.K4

namespace UpperTheory.Kd.K4.ZetaTop

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} {l : ℕ} [Fact l.Prime]

theorem isZWc_raise {X : Tower Ω ε} {pr : X.Fn l → Fin 2 → Qbar l} {W : R2 Ω l} {e : ℕ} {ψ : ZMod l → Qbar l}
    {N : ℕ} [NeZero N] {cw : ZMod N → Qbar l} {c d k : ℕ} {gm : (ZMod l)ˣ → SL(2, ℤ)} {cf : Coef l} {c₀ : ℕ}
    {Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l} (m : ℕ)
    (hadd : ∀ b b', pr (b + b') = pr b + pr b')
    (hsm : ∀ (a : ℤ_[l]) b, pr (a • b) = algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) • pr b)
    (h : IsZWc X l pr W e ψ N cw c d k gm cf c₀ Y) :
    IsZWc X l pr W e ψ N cw c d k gm cf (c₀ + m) (fun r s y => ((l : Qbar l) ^ m) • Y r s y) := by
  obtain ⟨Yx, hY, hsum⟩ := h
  refine ⟨fun x r s y => ((l : Qbar l) ^ m) • Yx x r s y,
    fun x => GlobalTheory.K4.zetaSystem_exponent_raise_of_prime_pow_smul l Ω ε X pr W e ψ N x c d k gm cf c₀ m (Yx x) hadd hsm (hY x), ?_⟩
  intro r s y
  simp only
  rw [hsum r s y, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_comm]

theorem shCoc_smul {Γ X R : Type*} [Group Γ] [Monoid X] [CommRing R] {ρ : Γ → Matrix (Fin 2) (Fin 2) R} {κ : Γ →* X}
    {Y : Γ → X → Fin 2 → R} (a : R) (h : ShCoc ρ κ Y) : ShCoc ρ κ (fun s y => a • Y s y) := by
  intro s t x
  simp only [h s t x, smul_add, Matrix.mulVec_smul]

theorem push_smul {Γ X X' R : Type*} [Fintype X'] [DecidableEq X] [CommRing R] (π : X' → X)
    (Y : Γ → X' → Fin 2 → R) (a : R) :
    GlobalTheory.KA.push π (fun s y => a • Y s y) = fun s y => a • GlobalTheory.KA.push π Y s y := by
  funext s y
  simp only [GlobalTheory.KA.push, Finset.smul_sum]

theorem spec_smul {Γ X R : Type*} [Fintype X] [CommRing R] (η : X → R) (Y : Γ → X → Fin 2 → R) (a : R) (s : Γ) :
    GlobalTheory.KA.spec η (fun s y => a • Y s y) s = a • GlobalTheory.KA.spec η Y s := by
  simp only [GlobalTheory.KA.spec, Finset.smul_sum, smul_comm a]

theorem exists_finset_unif [IsAlgClosure ℚ Ω] {T Q : Type} [Finite T] [SeminormedAddCommGroup Q]
    (f : (Ω ≃ₐ[ℚ] Ω) → T → Q) (hf : ∀ x, Continuous fun s => f s x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (x : T), (∀ z ∈ E0, s' z = z) → ‖f (s * s') x - f s x‖ ≤ δ := by
  classical
  haveI := Fintype.ofFinite T
  have hU : ∀ x, ∀ᶠ s' in nhds (1 : Ω ≃ₐ[ℚ] Ω), ∀ s ∈ (Set.univ : Set (Ω ≃ₐ[ℚ] Ω)),
      ‖f (s * s') x - f s x‖ < δ := by
    intro x
    refine isCompact_univ.eventually_forall_of_forall_eventually fun s _ => ?_
    have hc : Continuous fun z : (Ω ≃ₐ[ℚ] Ω) × (Ω ≃ₐ[ℚ] Ω) => ‖f (z.2 * z.1) x - f z.2 x‖ :=
      (((hf x).comp (continuous_snd.mul continuous_fst)).sub ((hf x).comp continuous_snd)).norm
    have h0 : ‖f (s * 1) x - f s x‖ < δ := by simpa using hδ
    exact hc.continuousAt.eventually (gt_mem_nhds h0)
  have hV : {s' : Ω ≃ₐ[ℚ] Ω | ∀ x, ∀ s, ‖f (s * s') x - f s x‖ < δ} ∈ nhds (1 : Ω ≃ₐ[ℚ] Ω) := by
    have := Filter.eventually_all.2 hU
    filter_upwards [this] with s' hs' x s using hs' x s (Set.mem_univ _)
  obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 hV
  have hfg : (Subalgebra.toSubmodule E.toSubalgebra).FG :=
    (Submodule.fg_iff_finiteDimensional _).2 hEfin
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t, fun s s' x hfix => ?_⟩
  have hmem : s' ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hy' : y ∈ Subalgebra.toSubmodule E.toSubalgebra := hy
    rw [← ht] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz => exact hfix z hz
    | zero => exact map_zero s'
    | add u v _ _ hu hv => rw [map_add (f := _), hu, hv]
    | smul a u _ hu => rw [map_smul, hu]
  exact (hEsub hmem x s).le

end UpperTheory.Kd.K4.ZetaTop

namespace UpperTheory.Kd.K4

open UpperTheory.Kd.K4.ZetaTop

theorem top : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
  ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ : ZMod l → Qbar l) (cf : Coef l),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    (∀ r₀, gm r₀ ∈ CongruenceSubgroup.Gamma1 N) → Nat.Coprime l N → l ≠ 2 → 1 ≤ e →
    (∃ x, cw x ≠ 0) → AdmWn ι e g A W X pr N cw c d gm ψ cf → Continuous W → (∀ s i j, mat W s i j ∈ cf.O) →
    ∃ (c₀ m : ℕ) (cf' : Coef l) (S' : Finset Pl) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l)
      (y : G ℚ Ω → Fin 2 → Qbar l),
      IsZWc X l pr W e ψ N cw c d (2 * e + 1) gm cf c₀ Y ∧
      (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) ∧
      (∀ r, Y r = GlobalTheory.KA.push (redL l r) (Y (r + 1))) ∧
      (∀ r y i, Continuous fun s => Y r s y i) ∧
      (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) ∧ (∀ r s y i, Y r s y i ∈ cf.O) ∧ (∀ z, z ∈ cf.O → z ∈ cf'.O) ∧
      (∀ r s, Cv r (y s) (GlobalTheory.KA.spec (fun u : (ZMod (l ^ r))ˣ => ((((u : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * chiK l ψ r u) (Y r) s)) ∧
      Sys W cf' (fun s => ((l : Qbar l) ^ m) • y s) S' ∧
      IwSys2 cf' A (nuD W e ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) ∧
      SpLink A e (chiK l ψ) (fun r s u => (l : Qbar l) ^ m * Y r s u 1) (fun s => ((l : Qbar l) ^ m) • y s) := by
  intro l _ Ω _ _ _ ι e S A W g hNf hSrc ε X pr N _ cw c d gm ψ cf hφ hgm hlN hl2 he hcw hAdm hWc hmat
  classical
  obtain ⟨c₀, Y, hZ, hSh, hPush, hCont, hO⟩ :=
    g3 l Ω ι e g A W ε X pr N cw c d gm ψ cf hφ hgm hlN hl2 he hcw hAdm hWc hmat
  obtain ⟨x₀, hx₀⟩ := hcw
  obtain ⟨-, -, -, -, hadd, hsm, -⟩ := hAdm.1 x₀ hx₀
  obtain ⟨θ, hθc, hmatθ, hρO, hχO, hχcong, hηtw, hθIne, hDec, hη⟩ :=
    GlobalTheory.K4.twist_clauses l Ω ι e g A W ε X pr N cw c d gm ψ cf S hNf hl2 ⟨x₀, hx₀⟩ hAdm
  obtain ⟨k, S', hIne, hfam⟩ := UpperTheory.V.Z.Kato.Nb.kato_tame_relation_projected l Ω ι e g A W ε X pr N cw c d gm ψ cf S hNf hmat hgm hlN
    hl2 he ⟨x₀, hx₀⟩ hφ hAdm c₀ Y hZ
  set Y' : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l :=
    fun r s y => ((l : Qbar l) ^ k) • Y r s y with hY'
  have hlk : ((l : Qbar l) ^ k) ∈ cf.O := pow_mem (natCast_mem _ _) _
  have hSh' : ∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y' r) :=
    fun r => shCoc_smul _ (hSh r)
  have hCont' : ∀ r y i, Continuous fun s => Y' r s y i := by
    intro r y i
    simp only [hY', Pi.smul_apply, smul_eq_mul]
    exact continuous_const.mul (hCont r y i)
  have hO' : ∀ r s u i, Y' r s u i ∈ cf.O := by
    intro r s u i
    simp only [hY', Pi.smul_apply, smul_eq_mul]
    exact mul_mem hlk (hO r s u i)
  have hPush' : ∀ r, Y' r = GlobalTheory.KA.push (redL l r) (Y' (r + 1)) := by
    intro r
    simp only [hY']
    rw [push_smul, ← hPush r]
  obtain ⟨m, y, S'', hy, hSys, hIw, hSp⟩ :=
    GlobalTheory.KZ.middle_glue2 l Ω W cf A e S' (chiK l (Function.update ψ 0 0)) θ (rhoK W e ψ) (nuD W e ψ) Y'
      hWc hθc hmat hmatθ (hρO cf hmat) (hχO cf) hχcong hηtw hSh' hCont' hO'
      (fun r s => congrFun (hPush' r) s) hDec hIne hθIne (by
        intro n hn w hw hdvd ψw hk hs
        obtain ⟨Yw, P, u, b, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hfam n hn w hw hdvd ψw hk hs
        refine ⟨Yw, P, u, b, h1, h2, h3, h4, h5, h6, h7, ?_, h9⟩
        intro r s i
        rw [hη r]
        simp only [hY', spec_smul]
        exact h8 r s i)
  refine ⟨c₀ + k, m, cf, S'', Y', y, isZWc_raise k hadd hsm hZ, hSh', hPush', hCont', ?_, hO',
    fun z hz => hz, ?_, hSys, hIw, ?_⟩
  · intro r n
    have hpos : (0 : ℝ) < ‖((l : Qbar l) ^ n)‖ := by
      rw [norm_pos_iff]
      exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
    obtain ⟨E0, hE0⟩ := exists_finset_unif (fun s y => Y' r s y 1) (fun y => hCont' r y 1) hpos
    exact ⟨E0, fun s s' y hfix => hE0 s s' y hfix⟩
  · intro r s i
    have := hy r s i
    rw [hη r] at this
    exact this
  · intro n
    obtain ⟨r₀, hr⟩ := hSp n
    refine ⟨r₀, fun r hr' s hs hc => ?_⟩
    have := hr r hr' s hs hc
    rwa [hη r] at this

end UpperTheory.Kd.K4

theorem UpperTheory.Kd.K4.kato_eulerSystem_integrality : UpperTheory.V.Z.Kato.Joint.KatoEulerSystemIwasawaClassStatement := UpperTheory.Kd.K4.top
