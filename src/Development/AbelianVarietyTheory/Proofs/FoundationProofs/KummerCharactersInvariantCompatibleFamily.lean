module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterAtLevelOfMemKummerModule
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTrace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharacterAdditiveOnCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharacterAdditiveOnCongruence
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3.KumHom

theorem germ_zero_of_vanish {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (h : ∀ z ∈ Hs, b z = 0) :
    (b : Mero) = 0 :=
  (GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 b (fun _ => 0) hb (differentiableOn_const 0)).2 h

theorem vanish_of_comp {b : ℂ → ℂ} (g : GQ) (h : ∀ z ∈ Hs, b (mob g z) = 0) : ∀ z ∈ Hs, b z = 0 := by
  intro w hw
  have h1 := GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.1 g g⁻¹ w hw
  rw [mul_inv_cancel, GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.2.1] at h1
  rw [h1]
  exact h _ (GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 _ w hw)

theorem diff_comp {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (g : GQ) :
    DifferentiableOn ℂ (fun z => b (mob g z)) Hs :=
  hb.comp (GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.2.2.1 g) (fun z hz => GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 g z hz)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem num_not_vanish {X : Tower Ω ε} {m : ℕ} (hm : 0 < m) {f : X.Kˣ} {a b : ℂ → ℂ} (h : IsRoot X m f a b) :
    ¬ ∀ z ∈ Hs, a z = 0 := by
  intro ha
  obtain ⟨hda, hdb, hb0, he⟩ := h
  rw [germ_zero_of_vanish hda ha, zero_pow hm.ne'] at he
  have hbm : (b : Mero) ^ m = 0 := by
    have := congrArg (X.an ((f⁻¹ : X.Kˣ) : X.K) * ·) he
    simp only [mul_zero, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at this
    exact this
  have hdbm : DifferentiableOn ℂ (fun z => b z ^ m) Hs := hdb.pow m
  have h0 : ((fun z => b z ^ m : ℂ → ℂ) : Mero) = ((fun _ => 0 : ℂ → ℂ) : Mero) := hbm
  have hz := (GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.1 _ (fun _ => 0) hdbm (differentiableOn_const 0)).1 h0
  exact hb0 (germ_zero_of_vanish hdb fun z hz' => (pow_eq_zero_iff hm.ne').1 (hz z hz'))

end GlobalTheory.KZ.H3.KumHom

namespace GlobalTheory.KZ.H3.KumHom

theorem zmod_eq_of_exp {m : ℕ} [NeZero m] (u v w : ZMod m)
    (h : Complex.exp (2 * Real.pi * Complex.I * (u.val : ℂ) / (m : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (v.val : ℂ) / (m : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (w.val : ℂ) / (m : ℂ))) : u = v + w := by
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨k, hk⟩ := h
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hc : ((u.val : ℤ) : ℂ) = ((v.val + w.val + k * m : ℤ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ h2
    field_simp at hk
    linear_combination (2 * (Real.pi : ℂ) * Complex.I) * hk
  have hi : (u.val : ℤ) = v.val + w.val + k * m := Int.cast_injective hc
  have := congrArg (Int.cast : ℤ → ZMod m) hi
  push_cast at this
  simpa [ZMod.natCast_val, ZMod.cast_id', ZMod.natCast_self] using this

theorem kum_hom : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ,
    ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → ∃ M : ℕ, 0 < M ∧
      ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M, χ (δ * δ') = χ δ + χ δ' := by
  intro Ω _ _ ε X l _ n x χ hK
  obtain ⟨f, a, b, M, hM, -, hr, hrel⟩ := hK
  refine ⟨M, hM, fun δ hδ δ' hδ' => ?_⟩
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  set E : ZMod (l ^ n) → ℂ := fun v => Complex.exp (2 * Real.pi * Complex.I * (v.val : ℂ) / ((l : ℂ) ^ n)) with hE
  obtain ⟨hda, hdb, hb0, -⟩ := id hr
  set g := ofSL δ
  set g' := ofSL δ'
  have key : ∀ z ∈ Hs, ((E (χ (δ * δ')) - E (χ δ) * E (χ δ')) * a z) * (b (mob g (mob g' z)) * b (mob g' z)) = 0 := by
    intro z hz
    have h1 := hrel (δ * δ') (Subgroup.mul_mem _ hδ hδ') z hz
    rw [map_mul, GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.1 _ _ z hz] at h1
    have h2 := hrel δ hδ (mob g' z) (GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 _ z hz)
    have h3 := hrel δ' hδ' z hz
    simp only [hE]
    linear_combination (-b (mob g' z)) * h1 + b z * h2 +
      Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) * b (mob g (mob g' z)) * h3
  have hA : DifferentiableOn ℂ (fun z => (E (χ (δ * δ')) - E (χ δ) * E (χ δ')) * a z) Hs :=
    (differentiableOn_const _).mul hda
  have hB : DifferentiableOn ℂ (fun z => b (mob g (mob g' z)) * b (mob g' z)) Hs := by
    refine DifferentiableOn.mul ?_ (diff_comp hdb g')
    have := diff_comp hdb (g * g')
    refine this.congr fun z hz => ?_
    simp only [GlobalTheory.T.glTwoPosRatMobius_basic_laws.2.1 g g' z hz]
  have hc : E (χ (δ * δ')) - E (χ δ) * E (χ δ') = 0 := by
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.2.1 _ _ hA hB key with h | h
    · by_contra hne
      exact num_not_vanish hpos hr fun z hz => (mul_eq_zero.1 (h z hz)).resolve_left hne
    · exfalso
      rcases GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties.2.1 _ _ (diff_comp (diff_comp hdb g) g') (diff_comp hdb g') h with h' | h'
      · exact hb0 (germ_zero_of_vanish hdb (vanish_of_comp g (vanish_of_comp g' h')))
      · exact hb0 (germ_zero_of_vanish hdb (vanish_of_comp g' h'))
  have := sub_eq_zero.1 hc
  simp only [hE] at this
  exact zmod_eq_of_exp _ _ _ (by exact_mod_cast this)

end GlobalTheory.KZ.H3.KumHom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharacterAdditiveOnCongruenceStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCharacter_additive_on_congruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → ∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M, χ (δ * δ') = χ δ + χ δ' := by
  first | exact @GlobalTheory.KZ.H3.KumHom.kum_hom | exact GlobalTheory.KZ.H3.KumHom.kum_hom | (intros; apply GlobalTheory.KZ.H3.KumHom.kum_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersEqOnPrincipalCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersEqOnPrincipalCongruence
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

namespace KumUniq

theorem gamma_mem_of_dvd {M N : ℕ} (h : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, h1, map_one]
  · rw [← e, h2, map_zero]
  · rw [← e, h3, map_zero]
  · rw [← e, h4, map_one]

end KumUniq

open KumUniq

theorem kum_near : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (x : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n x χ' → Near χ χ' := by
  intro Ω _ _ ε X l _ n x χ χ' hK hK'
  obtain ⟨hH, hmul, hone, hdiff, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  obtain ⟨G1, G2, G3, -, G5⟩ := GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hχ⟩ := hK
  obtain ⟨f', a', b', M', hM', hx', ⟨ha', hb', hb0', hab'⟩, hχ'⟩ := hK'
  have hl : l.Prime := Fact.out
  have hm : 0 < l ^ n := pow_pos hl.pos n
  obtain ⟨g, hfg⟩ := ((GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n).2.1 f f').1 (hx.symm.trans hx')
  obtain ⟨p, q, hp, hq, hq0, hpq⟩ := X.an_mero (g : X.K)
  obtain ⟨M'', hM'', hlev⟩ := X.level (g : X.K)

  have nz : ∀ u : ℂ → ℂ, DifferentiableOn ℂ u Hs → (u : Mero) ≠ 0 → ∃ z ∈ Hs, u z ≠ 0 := by
    intro u hu hu0
    by_contra hc
    push_neg at hc
    exact hu0 (((G1 u (fun _ => 0) hu (differentiableOn_const 0)).2 hc).trans Filter.Germ.coe_zero)

  have unz : ∀ (h : X.Kˣ) (u : ℂ → ℂ) (v : Mero) (k : ℕ), k ≠ 0 → X.an (h : X.K) * (u : Mero) ^ k = v →
      DifferentiableOn ℂ u Hs → (u : Mero) ≠ 0 → v ≠ 0 := by
    intro h u v k hk heq hu hu0 hv0
    have h0 : ((fun z => u z ^ k : ℂ → ℂ) : Mero) = ((fun _ => 0 : ℂ → ℂ) : Mero) := by
      have e : ((fun z => u z ^ k : ℂ → ℂ) : Mero) = (u : Mero) ^ k := Filter.Germ.coe_pow u k
      rw [e]
      calc (u : Mero) ^ k = X.an (((h⁻¹ : X.Kˣ) : X.K) * (h : X.K)) * (u : Mero) ^ k := by simp
        _ = X.an ((h⁻¹ : X.Kˣ) : X.K) * (X.an (h : X.K) * (u : Mero) ^ k) := by rw [map_mul, mul_assoc]
        _ = 0 := by rw [heq, hv0, mul_zero]
        _ = _ := Filter.Germ.coe_zero.symm
    have h1 := (G1 _ _ (hu.pow k) (differentiableOn_const 0)).1 h0
    apply hu0
    refine ((G1 u (fun _ => 0) hu (differentiableOn_const 0)).2 fun z hz => ?_).trans Filter.Germ.coe_zero
    exact pow_eq_zero_iff hk |>.1 (h1 z hz)

  have nzmul : ∀ u v : ℂ → ℂ, DifferentiableOn ℂ u Hs → DifferentiableOn ℂ v Hs → (∃ z ∈ Hs, u z ≠ 0) →
      (∃ z ∈ Hs, v z ≠ 0) → ∃ z ∈ Hs, u z * v z ≠ 0 := by
    rintro u v hu hv ⟨z1, hz1, h1⟩ ⟨z2, hz2, h2⟩
    by_contra hc
    push_neg at hc
    rcases G2 u v hu hv hc with h | h
    · exact h1 (h z1 hz1)
    · exact h2 (h z2 hz2)

  have hf : X.an (f : X.K) = X.an (f' : X.K) * X.an (g : X.K) ^ (l ^ n) := by
    rw [hfg, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  have key : ((fun z => (a z * b' z * q z) ^ (l ^ n) : ℂ → ℂ) : Mero) =
      ((fun z => (a' z * b z * p z) ^ (l ^ n) : ℂ → ℂ) : Mero) := by
    have e1 : ((fun z => (a z * b' z * q z) ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a : Mero) * b' * q) ^ (l ^ n) := by
      rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_pow]; rfl
    have e2 : ((fun z => (a' z * b z * p z) ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a' : Mero) * b * p) ^ (l ^ n) := by
      rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_pow]; rfl
    rw [e1, e2, ← hpq]
    linear_combination (-((b' : Mero) ^ (l ^ n) * (q : Mero) ^ (l ^ n))) * hab +
      ((b : Mero) ^ (l ^ n) * (b' : Mero) ^ (l ^ n) * (q : Mero) ^ (l ^ n)) * hf +
      ((b : Mero) ^ (l ^ n) * (X.an (g : X.K)) ^ (l ^ n) * (q : Mero) ^ (l ^ n)) * hab'
  have key' := (G1 _ _ (((ha.mul hb').mul hq).pow (l ^ n)) (((ha'.mul hb).mul hp).pow (l ^ n))).1 key
  obtain ⟨k, hk⟩ := G5 (l ^ n) (fun z => a z * b' z * q z) (fun z => a' z * b z * p z) hm
    ((ha.mul hb').mul hq) ((ha'.mul hb).mul hp) key'

  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (g : X.K) = (φ : Mero) :=
    Filter.Germ.inductionOn (X.an (g : X.K)) (p := fun F => ∃ φ : ℂ → ℂ, F = (φ : Mero)) fun φ => ⟨φ, rfl⟩
  have hmap : ∀ γ : SL(2, ℤ), Set.MapsTo (mob (ofSL γ)) Hs Hs := fun γ z hz => hH _ z hz
  have hpqδ : ∀ δ ∈ CongruenceSubgroup.Gamma M'', ∀ z ∈ Hs,
      p (mob (ofSL δ) z) * q z = p z * q (mob (ofSL δ) z) := by
    intro δ hδ
    have h1 : (φ : Mero) = ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) := by
      rw [← hφ, ← X.an_sl (ofSL δ) _ φ hφ, hlev δ hδ]
    have h2 : ((fun z => φ z * q z : ℂ → ℂ) : Mero) = (p : Mero) := by
      rw [← hpq, hφ]; exact Filter.Germ.coe_mul φ q
    have h3 := G3 (ofSL δ) _ _ h2
    have e3 : ((fun z => φ (mob (ofSL δ) z) * q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) =
        ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) :=
      Filter.Germ.coe_mul _ _
    have h2' : (φ : Mero) * (q : Mero) = (p : Mero) := by rw [← h2]; exact (Filter.Germ.coe_mul φ q).symm
    have h3' : ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) =
        ((fun z => p (mob (ofSL δ) z) : ℂ → ℂ) : Mero) := by rw [← e3]; exact h3
    have hpδ : DifferentiableOn ℂ (fun z => p (mob (ofSL δ) z)) Hs := hp.comp (hdiff _) (hmap δ)
    have hqδ : DifferentiableOn ℂ (fun z => q (mob (ofSL δ) z)) Hs := hq.comp (hdiff _) (hmap δ)
    refine (G1 (fun z => p (mob (ofSL δ) z) * q z) (fun z => p z * q (mob (ofSL δ) z))
      (hpδ.mul hq) (hp.mul hqδ)).1 ?_
    have e4 : ((fun z => p (mob (ofSL δ) z) * q z : ℂ → ℂ) : Mero) =
        ((fun z => p (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * (q : Mero) := Filter.Germ.coe_mul _ _
    have e5 : ((fun z => p z * q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) =
        (p : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) := Filter.Germ.coe_mul _ _
    rw [e4, e5]
    linear_combination (-((q : Mero) * ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero))) * h1 +
      ((fun z => q (mob (ofSL δ) z) : ℂ → ℂ) : Mero) * h2' + (-(q : Mero)) * h3'

  refine ⟨M * M' * M'', by positivity, fun δ hδ => ?_⟩
  have hδ1 : δ ∈ CongruenceSubgroup.Gamma M :=
    gamma_mem_of_dvd (Dvd.intro (M' * M'') (by ring)) hδ
  have hδ2 : δ ∈ CongruenceSubgroup.Gamma M' :=
    gamma_mem_of_dvd (Dvd.intro (M * M'') (by ring)) hδ
  have hδ3 : δ ∈ CongruenceSubgroup.Gamma M'' := gamma_mem_of_dvd (Dvd.intro_left (M * M') rfl) hδ
  set e1 := Complex.exp (2 * Real.pi * Complex.I * ((χ δ).val : ℂ) / ((l : ℂ) ^ n)) with he1
  set e2 := Complex.exp (2 * Real.pi * Complex.I * ((χ' δ).val : ℂ) / ((l : ℂ) ^ n)) with he2
  set ζ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / ((l ^ n : ℕ) : ℂ)) with hζ
  have hP : ∀ z ∈ Hs, (e1 - e2) * (a z * a' z * b (mob (ofSL δ) z) * b' (mob (ofSL δ) z) *
      p (mob (ofSL δ) z) * q z) = 0 := by
    intro z hz
    have hw := hH (ofSL δ) z hz
    have K1 := hχ δ hδ1 z hz
    have K2 := hχ' δ hδ2 z hz
    have K3 := hpqδ δ hδ3 z hz
    have Dz : a z * b' z * q z = ζ * (a' z * b z * p z) := hk z hz
    have Dw : a (mob (ofSL δ) z) * b' (mob (ofSL δ) z) * q (mob (ofSL δ) z) =
        ζ * (a' (mob (ofSL δ) z) * b (mob (ofSL δ) z) * p (mob (ofSL δ) z)) := hk _ hw
    linear_combination (a' z * b z * p z) * Dw
      - (a' (mob (ofSL δ) z) * b (mob (ofSL δ) z) * p (mob (ofSL δ) z)) * Dz
      - (b' (mob (ofSL δ) z) * q (mob (ofSL δ) z) * a' z * p z) * K1
      + e1 * (a z * b (mob (ofSL δ) z) * b' (mob (ofSL δ) z) * a' z) * K3
      + (a z * q z * b (mob (ofSL δ) z) * p (mob (ofSL δ) z)) * K2

  have nzδ : ∀ u : ℂ → ℂ, (∃ z ∈ Hs, u z ≠ 0) → ∃ z ∈ Hs, u (mob (ofSL δ) z) ≠ 0 := by
    rintro u ⟨z, hz, hu⟩
    refine ⟨mob (ofSL δ⁻¹) z, hH _ z hz, ?_⟩
    rwa [← hmul _ _ z hz, ← map_mul, mul_inv_cancel, map_one, hone]
  have dδ : ∀ u : ℂ → ℂ, DifferentiableOn ℂ u Hs → DifferentiableOn ℂ (fun z => u (mob (ofSL δ) z)) Hs :=
    fun u hu => hu.comp (hdiff _) (hmap δ)
  have na : ∃ z ∈ Hs, a z ≠ 0 := nz a ha fun h0 => unz f b _ (l ^ n) hm.ne' hab hb hb0 (by rw [h0, zero_pow hm.ne'])
  have na' : ∃ z ∈ Hs, a' z ≠ 0 := nz a' ha' fun h0 => unz f' b' _ (l ^ n) hm.ne' hab' hb' hb0' (by rw [h0, zero_pow hm.ne'])
  have np : ∃ z ∈ Hs, p z ≠ 0 := nz p hp (unz g q _ 1 one_ne_zero (by rw [pow_one]; exact hpq) hq hq0)
  obtain ⟨z0, hz0, hne⟩ := nzmul _ _ ((((ha.mul ha').mul (dδ b hb)).mul (dδ b' hb')).mul (dδ p hp)) hq
    (nzmul _ _ (((ha.mul ha').mul (dδ b hb)).mul (dδ b' hb')) (dδ p hp)
      (nzmul _ _ ((ha.mul ha').mul (dδ b hb)) (dδ b' hb')
        (nzmul _ _ (ha.mul ha') (dδ b hb) (nzmul _ _ ha ha' na na') (nzδ b (nz b hb hb0)))
        (nzδ b' (nz b' hb' hb0'))) (nzδ p np)) (nz q hq hq0)
  have he : e1 = e2 := by
    rcases mul_eq_zero.1 (hP z0 hz0) with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hne

  haveI : NeZero (l ^ n) := ⟨hm.ne'⟩
  have hprim := Complex.isPrimitiveRoot_exp (l ^ n) hm.ne'
  have ex : ∀ v : ℕ, Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ n)) =
      (Complex.exp (2 * Real.pi * Complex.I / ((l ^ n : ℕ) : ℂ))) ^ v := by
    intro v
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  apply ZMod.val_injective (l ^ n)
  exact hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (by rw [← ex, ← ex]; exact he)

end GlobalTheory.KZ.H3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersEqOnPrincipalCongruenceStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCharacters_eqOn_principalCongruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n x χ' → Near χ χ' := by
  first | exact @GlobalTheory.KZ.H3.kum_near | exact GlobalTheory.KZ.H3.kum_near | (intros; apply GlobalTheory.KZ.H3.kum_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelSuccReduce
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelSuccReduce
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem exp_pow_reduce (l n v : ℕ) (hl : l ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ (n + 1))) ^ l =
      Complex.exp (2 * Real.pi * Complex.I * ((v % l ^ n : ℕ) : ℂ) / ((l : ℂ) ^ n)) := by
  rw [← Complex.exp_nat_mul]
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  have hv : (v : ℂ) = ((v % l ^ n : ℕ) : ℂ) + (l : ℂ) ^ n * ((v / l ^ n : ℕ) : ℂ) := by
    exact_mod_cast (Nat.mod_add_div v (l ^ n)).symm
  have e : (l : ℂ) * (2 * Real.pi * Complex.I * (v : ℂ) / ((l : ℂ) ^ (n + 1))) =
      2 * Real.pi * Complex.I * ((v % l ^ n : ℕ) : ℂ) / ((l : ℂ) ^ n) +
        ((v / l ^ n : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hv]; field_simp; ring
  rw [e, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem kum_succ_reduce : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ (n + 1))), Kum X l (n + 1) x χ →
      Kum X l n x (fun δ => ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)) := by
  intro Ω _ _ ε X l _ n x χ ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hrel⟩
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hl0⟩
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl0⟩
  refine ⟨f, fun z => a z ^ l, fun z => b z ^ l, M, hM, ?_, ⟨ha.pow l, hb.pow l, ?_, ?_⟩, ?_⟩
  · have h := AdicCompletion.transitionMap_comp_eval_apply (idl l) (X.Kl l) (Nat.le_succ n) x
    change x.val n = _
    rw [← h]
    change AdicCompletion.transitionMap (idl l) (X.Kl l) (Nat.le_succ n) (AdicCompletion.eval (idl l) (X.Kl l) (n + 1) x) = _
    rw [hx]
    rfl
  · intro h
    apply hb0
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at h ⊢
    exact h.mono fun z hz => (pow_eq_zero_iff hl0).1 hz
  · have e1 : ((fun z => b z ^ l : ℂ → ℂ) : Mero) = (b : Mero) ^ l := Filter.Germ.coe_pow b l
    have e2 : ((fun z => a z ^ l : ℂ → ℂ) : Mero) = (a : Mero) ^ l := Filter.Germ.coe_pow a l
    rw [e1, e2, ← pow_mul, ← pow_mul, ← pow_succ', hab]
  · intro δ hδ z hz
    have h1 := congrArg (fun t : ℂ => t ^ l) (hrel δ hδ z hz)
    simp only [mul_pow] at h1
    rw [exp_pow_reduce l n _ hl0] at h1
    have hv : (ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)).val = (χ δ).val % l ^ n := by
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    rw [hv]
    simpa only [mul_pow, mul_assoc] using h1

end GlobalTheory.KZ.H3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelSuccReduceStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKummerCharacterAtLevel_succ_reduce : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ (n + 1))), Kum X l (n + 1) x χ → Kum X l n x (fun δ => ZMod.castHom (pow_dvd_pow l (Nat.le_succ n)) (ZMod (l ^ n)) (χ δ)) := by
  first | exact @GlobalTheory.KZ.H3.kum_succ_reduce | exact GlobalTheory.KZ.H3.kum_succ_reduce | (intros; apply GlobalTheory.KZ.H3.kum_succ_reduce <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersInvariantCompatibleFamily
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.KumFam

theorem gamma_dvd {M N : ℕ} (h : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, h1, map_one]
  · rw [← e, h2, map_zero]
  · rw [← e, h3, map_zero]
  · rw [← e, h4, map_one]

theorem common_level {k : ℕ} (Q : Fin k → ℕ → Prop) (hmono : ∀ i M M', M ∣ M' → Q i M → Q i M')
    (h : ∀ i, ∃ M, 0 < M ∧ Q i M) : ∃ M, 0 < M ∧ ∀ i, Q i M := by
  choose M hM hQ using h
  exact ⟨∏ i, M i, Finset.prod_pos fun i _ => hM i,
    fun i => hmono i _ _ (Finset.dvd_prod_of_mem M (Finset.mem_univ i)) (hQ i)⟩

theorem near_fin {V : Type} {k : ℕ} (φ ψ : Fin k → SL(2, ℤ) → V) (h : ∀ i, Near (φ i) (ψ i)) :
    ∃ M, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ i, φ i δ = ψ i δ := by
  obtain ⟨M, hM, hQ⟩ := common_level (fun i M => ∀ δ ∈ CongruenceSubgroup.Gamma M, φ i δ = ψ i δ)
    (fun _ _ _ hd hq δ hδ => hq δ (gamma_dvd hd hδ)) h
  exact ⟨M, hM, fun δ hδ i => hQ i δ hδ⟩

theorem kum_sum {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    {ι : Type} [DecidableEq ι] (s : Finset ι) (x : ι → X.Khat l) (χ : ι → SL(2, ℤ) → ZMod (l ^ n))
    (h : ∀ k ∈ s, Kum X l n (x k) (χ k)) : Kum X l n (∑ k ∈ s, x k) (∑ k ∈ s, χ k) := by
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).1 _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem map_mon {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (w : ℕ) (i : Fin (w + 1)) :
    MvPolynomial.map f (mon R w i) = mon S w i := by
  simp [mon]

end GlobalTheory.KZ.H3.KumFam


open GlobalTheory.KZ.H3.KumFam in
theorem GlobalTheory.KZ.H3.kum_family : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ) (c : Fin (w + 1) → X.Khat l), (∀ i, c i ∈ X.A l) → (∀ γ ∈ Gam N l, ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k)) → ∃ Φ, IsFam l w (Gam N l) Φ ∧ ∀ n i, Kum X l n (c i) (fun δ => AddMonoidAlgebra.coeff (Φ n δ) (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ)))) := by
  intro Ω _ _ ε X l _ _ hj N w c hA hinv
  choose χ hχ using fun n i => GlobalTheory.T.exists_kummerCharacterAtLevel_of_mem_kummerModule Ω ε X l hj n (c i) (hA i)
  refine ⟨fun n δ => ∑ i, MvPolynomial.C (χ n i δ) * mon (ZMod (l ^ n)) w i, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n δ
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
    have h := (MvPolynomial.isHomogeneous_C (Fin 2) (χ n i δ)).mul ((mon_expand (ZMod (l ^ n)) w).2.2.1 i)
    rwa [zero_add] at h
  · intro n
    obtain ⟨M, hM, hQ⟩ := GlobalTheory.KZ.H3.KumFam.common_level (k := w + 1)
      (fun i M => ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M,
        χ n i (δ * δ') = χ n i δ + χ n i δ')
      (fun _ _ _ hd hq δ hδ δ' hδ' => hq δ (GlobalTheory.KZ.H3.KumFam.gamma_dvd hd hδ) δ' (GlobalTheory.KZ.H3.KumFam.gamma_dvd hd hδ'))
      (fun i => GlobalTheory.T.kummerCharacter_additive_on_congruence Ω ε X l n (c i) (χ n i) (hχ n i))
    refine ⟨M, hM, fun δ hδ δ' hδ' => ?_⟩
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hQ i δ hδ δ' hδ', map_add (f := _), add_mul]
  · intro n γ hγ
    have hdet : (0 : ℤ) < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [γ.det_coe]; exact one_pos
    have hK : ∀ i, Kum X l n (c i)
        (fun δ => ∑ k, ((cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ) : ZMod (l ^ n)) * χ n k (γ * δ * γ⁻¹)) := by
      intro i
      have hk : ∀ k, Kum X l n ((cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) •
          X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k))
          (fun δ => PadicInt.toZModPow n (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) *
            χ n k (cj (γ : Matrix (Fin 2) (Fin 2) ℤ) δ)) := by
        intro k
        have h1 := GlobalTheory.T.isKummerCharacterAtLevel_integral_matrix_conj Ω ε X l n γ (c k) (χ n k) hdet (hχ n k)
        rw [Betti.toGQ_sl] at h1
        exact GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n _ _ _ h1
      have hs := GlobalTheory.KZ.H3.KumFam.kum_sum X l n Finset.univ _ _ (fun k _ => hk k)
      rw [← hinv γ hγ i] at hs
      refine (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.2 _ _ _ hs ⟨1, one_pos, fun δ _ => ?_⟩
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [GlobalTheory.T.integralConjugateSL2Int_laws.2.1, map_intCast]
    obtain ⟨M, hM, hQ⟩ := GlobalTheory.KZ.H3.KumFam.near_fin (k := w + 1) _ _ fun i => GlobalTheory.T.kummerCharacters_eqOn_principalCongruence Ω ε X l n (c i) _ _ (hK i) (hχ n i)
    refine ⟨M, hM, fun δ hδ => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MvPolynomial.algHom_C, (mon_expand (ZMod (l ^ n)) w).1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hQ δ hδ i, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, MvPolynomial.algebraMap_eq]; ring
  · intro n
    obtain ⟨M, hM, hQ⟩ := GlobalTheory.KZ.H3.KumFam.near_fin (k := w + 1) _ _ fun i => GlobalTheory.T.kummerCharacters_eqOn_principalCongruence Ω ε X l n (c i) _ _
      (GlobalTheory.T.isKummerCharacterAtLevel_succ_reduce Ω ε X l n (c i) (χ (n + 1) i) (hχ (n + 1) i)) (hχ n i)
    refine ⟨M, hM, fun δ hδ => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MvPolynomial.map_C, GlobalTheory.KZ.H3.KumFam.map_mon]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hQ δ hδ i]
  · intro n i
    convert hχ n i using 1
    funext δ
    exact MonExp.coeff_sum_mon _ w (fun j => χ n j δ) i
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersInvariantCompatibleFamilyStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCharacters_invariant_compatible_family : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ) (c : Fin (w + 1) → X.Khat l), (∀ i, c i ∈ X.A l) → (∀ γ ∈ Gam N l, ∀ i, c i = ∑ k, (cf w (γ : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ_[l]) • X.kmap l (X.sl (ofSL γ)).toRingEquiv (c k)) → ∃ Φ, IsFam l w (Gam N l) Φ ∧ ∀ n i, Kum X l n (c i) (fun δ => AddMonoidAlgebra.coeff (Φ n δ) (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ)))) := by
  first | exact @GlobalTheory.KZ.H3.kum_family | exact GlobalTheory.KZ.H3.kum_family | (intros; apply GlobalTheory.KZ.H3.kum_family <;> assumption)
end
