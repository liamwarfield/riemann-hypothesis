module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryFormCoeffOfGamma1CapGamma0Invariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersInvariantCompatibleFamily
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPadicCocycleOfCompatiblePolyFamily
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerPotentialRelationPadic
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfHomogeneousPolyCo
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CapGamma0LevelActsFreelyUpperHalfPlane
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CapGamma0LevelActsFreelyUpperHalfPlane
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.FreeAct

theorem ent_ofSL (γ : SL(2, ℤ)) (i j : Fin 2) :
    ent (ofSL γ) i j = ((γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
  simp [ent, ofSL]

theorem key (a b c d x y : ℝ) (h1 : a - d = 2 * c * x) (h2 : c * (x ^ 2 - y ^ 2) + (d - a) * x - b = 0)
    (hdet : a * d - b * c = 1) : 4 * c ^ 2 * y ^ 2 = 4 - (a + d) ^ 2 := by
  linear_combination (-4 * c) * h2 + 4 * hdet + (a - d - 2 * c * x) * h1

theorem no_small (N : ℕ) (hN : 4 ≤ N) (t k : ℤ) (hk : t - 2 = (N : ℤ) * k) (ht : t ^ 2 < 4) : False := by
  have h1 : -1 ≤ t := by nlinarith
  have h2 : t ≤ 1 := by nlinarith
  have hN' : (4 : ℤ) ≤ N := by exact_mod_cast hN
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · nlinarith
  · subst hk0; omega
  · nlinarith

end GlobalTheory.KZ.FreeAct

namespace GlobalTheory.KZ


open FreeAct in
theorem gam_free : ∀ (N l : ℕ), 4 ≤ N → ∀ γ ∈ Gam N l, ∀ z ∈ Hs, mob (ofSL γ) z = z → γ = 1 := by
  intro N l hN γ hγ z hz hfix
  have hγ1 : γ ∈ CongruenceSubgroup.Gamma1 N := hγ.1
  rw [CongruenceSubgroup.Gamma1_mem] at hγ1
  obtain ⟨ha1, hd1, -⟩ := hγ1
  set A := (γ : Matrix (Fin 2) (Fin 2) ℤ) with hA
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have := γ.2; rw [Matrix.det_fin_two] at this; exact this
  have hden := GlobalTheory.KZ.MobLaws.den_ne (ofSL γ) hz
  simp only [ent_ofSL] at hden
  unfold mob at hfix
  simp only [ent_ofSL] at hfix
  rw [div_eq_iff hden] at hfix
  have hy : 0 < z.im := hz
  have hre := congrArg Complex.re hfix
  have him := congrArg Complex.im hfix
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
    Complex.intCast_im, Complex.ratCast_re, Complex.ratCast_im] at hre him
  push_cast at hre him
  simp at hre him
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (A 0 0) N).1 (by simpa using ha1.symm)
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (A 1 1) N).1 (by simpa using hd1.symm)
  have hN' : (4 : ℤ) ≤ N := by exact_mod_cast hN
  simp only [← hA] at hre him
  generalize e00 : A 0 0 = a at *
  generalize e01 : A 0 1 = b at *
  generalize e10 : A 1 0 = c at *
  generalize e11 : A 1 1 = d at *
  have h1 : (a : ℝ) - d = 2 * c * z.re := by
    have : ((a : ℝ) - d - 2 * c * z.re) * z.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have h2 : (c : ℝ) * (z.re ^ 2 - z.im ^ 2) + (d - a) * z.re - b = 0 := by linarith
  have hdetR : (a : ℝ) * d - b * c = 1 := by exact_mod_cast hdet
  have hk4 := key a b c d z.re z.im h1 h2 hdetR
  by_cases hc : c = 0
  · subst hc
    have had : a = d := by
      have : (a : ℝ) = d := by simp at h1; linarith
      exact_mod_cast this
    subst had
    have hb : b = 0 := by
      have : (b : ℝ) = 0 := by simpa using h2
      exact_mod_cast this
    subst hb
    have haa : a * a = 1 := by simpa using hdet
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' haa with ⟨ha, -⟩ | ⟨ha, -⟩
    · subst ha
      ext i j
      fin_cases i <;> fin_cases j <;> simp [← hA, e00, e01, e10, e11]
    · exfalso
      subst ha
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · nlinarith
      · subst hk0; omega
      · nlinarith
  · exfalso
    have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
    have hpos : 0 < 4 * (c : ℝ) ^ 2 * z.im ^ 2 := by positivity
    have ht : (a + d) ^ 2 < 4 := by
      have : ((a : ℝ) + d) ^ 2 < 4 := by linarith
      exact_mod_cast this
    exact no_small N hN (a + d) (k + m) (by linear_combination hk + hm) ht

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CapGamma0LevelActsFreelyUpperHalfPlaneStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma1CapGamma0Level_acts_freely_upperHalfPlane : ∀ (N l : ℕ), 4 ≤ N → ∀ γ ∈ Gam N l, ∀ z ∈ Hs, mob (ofSL γ) z = z → γ = 1 := by
  first | exact @GlobalTheory.KZ.gam_free | exact GlobalTheory.KZ.gam_free | (intros; apply GlobalTheory.KZ.gam_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfHomogeneousPolyCo
noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3.PotCoc

def orbSetoid (Γ : Subgroup SL(2, ℤ)) : Setoid Hs where
  r a b := ∃ γ ∈ Γ, mob (ofSL γ) a.1 = b.1
  iseqv := by
    obtain ⟨-, hmul, hone, -⟩ := GlobalTheory.KZ.mob_laws
    refine ⟨fun a => ⟨1, Γ.one_mem, by simp [hone]⟩, ?_, ?_⟩
    · rintro a b ⟨γ, hγ, h⟩
      refine ⟨γ⁻¹, Γ.inv_mem hγ, ?_⟩
      rw [← h, ← hmul _ _ _ a.2, ← map_mul, inv_mul_cancel, map_one, hone]
    · rintro a b c ⟨γ, hγ, h⟩ ⟨δ, hδ, h'⟩
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, ?_⟩
      rw [map_mul, hmul _ _ _ a.2, h, h']

def rep (Γ : Subgroup SL(2, ℤ)) (a : Hs) : Hs := (Quotient.mk (orbSetoid Γ) a).out

theorem rep_rel (Γ : Subgroup SL(2, ℤ)) (a : Hs) : ∃ γ ∈ Γ, mob (ofSL γ) (rep Γ a).1 = a.1 :=
  Quotient.mk_out (s := orbSetoid Γ) a


open Classical in
def gel (Γ : Subgroup SL(2, ℤ)) (τ : ℂ) : SL(2, ℤ) :=
  if h : τ ∈ Hs then (rep_rel Γ ⟨τ, h⟩).choose else 1

theorem gel_spec (Γ : Subgroup SL(2, ℤ)) {τ : ℂ} (h : τ ∈ Hs) :
    gel Γ τ ∈ Γ ∧ mob (ofSL (gel Γ τ)) (rep Γ ⟨τ, h⟩).1 = τ := by
  simp only [gel, dif_pos h]
  exact (rep_rel Γ ⟨τ, h⟩).choose_spec

theorem rep_eq (Γ : Subgroup SL(2, ℤ)) {δ : SL(2, ℤ)} (hδ : δ ∈ Γ) {τ : ℂ} (h : τ ∈ Hs)
    (h' : mob (ofSL δ) τ ∈ Hs) : rep Γ ⟨mob (ofSL δ) τ, h'⟩ = rep Γ ⟨τ, h⟩ := by
  unfold rep
  congr 1
  exact Quotient.sound (s := orbSetoid Γ) ⟨δ⁻¹, Γ.inv_mem hδ, by
    obtain ⟨-, hmul, hone, -⟩ := GlobalTheory.KZ.mob_laws
    show mob (ofSL δ⁻¹) (mob (ofSL δ) τ) = τ
    rw [← hmul _ _ _ h, ← map_mul, inv_mul_cancel, map_one, hone]⟩

theorem slPS {R : Type} [CommRing R] (a c : SL(2, ℤ)) (p : MvPolynomial (Fin 2) R) :
    slP (c : Matrix (Fin 2) (Fin 2) ℤ) (slP (a : Matrix (Fin 2) (Fin 2) ℤ) p) =
      slP ((a * c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) p := by
  rw [GlobalTheory.KZ.Betti.polySlash_polySlash, Matrix.SpecialLinearGroup.coe_mul]

def potOf {R : Type} [CommRing R] (Γ : Subgroup SL(2, ℤ)) (z : SL(2, ℤ) → MvPolynomial (Fin 2) R) (τ : ℂ) :
    MvPolynomial (Fin 2) R :=
  slP (((gel Γ τ)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (z (gel Γ τ))

end GlobalTheory.KZ.H3.PotCoc


open GlobalTheory.KZ.H3.PotCoc GlobalTheory.KZ.Betti in
theorem GlobalTheory.KZ.H3.exists_pot_of_isCoc : ∀ (R : Type) [CommRing R] (w N l : ℕ), 4 ≤ N →
    ∀ z : SL(2, ℤ) → MvPolynomial (Fin 2) R, IsCoc w (Gam N l) z → ∃ F ∈ Pot R w (Gam N l),
      ∀ γ ∈ Gam N l, ∀ τ ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ = z γ := by
  intro R _ w N l hN z hz
  obtain ⟨hmem, hmul, hone, -⟩ := GlobalTheory.KZ.mob_laws
  set Γ := Gam N l
  have key : ∀ γ ∈ Γ, ∀ τ ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (potOf Γ z (mob (ofSL γ) τ)) - potOf Γ z τ = z γ := by
    intro δ hδ τ hτ
    have hτ' : mob (ofSL δ) τ ∈ Hs := hmem _ _ hτ
    obtain ⟨hg1, hg2⟩ := gel_spec Γ hτ
    obtain ⟨hg1', hg2'⟩ := gel_spec Γ hτ'
    rw [rep_eq Γ hδ hτ hτ'] at hg2'
    set g := gel Γ τ
    set g' := gel Γ (mob (ofSL δ) τ)
    have hg : g' = δ * g := by
      have hfree := GlobalTheory.T.gamma1CapGamma0Level_acts_freely_upperHalfPlane N l hN (g'⁻¹ * (δ * g)) (Γ.mul_mem (Γ.inv_mem hg1') (Γ.mul_mem hδ hg1))
        _ (rep Γ ⟨τ, hτ⟩).2 (by
          rw [map_mul, hmul _ _ _ (rep Γ ⟨τ, hτ⟩).2, map_mul, hmul _ _ _ (rep Γ ⟨τ, hτ⟩).2, hg2, ← hg2',
            ← hmul _ _ _ (rep Γ ⟨τ, hτ⟩).2, ← map_mul, inv_mul_cancel, map_one, hone])
      exact (inv_mul_eq_one.mp hfree)
    show slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (slP ((g'⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (z g')) -
      slP ((g⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (z g) = z δ
    rw [hg, (hz.2 δ hδ g hg1)]
    have e1 : (δ * g)⁻¹ * δ = g⁻¹ := by group
    have e2 : g * (δ * g)⁻¹ * δ = 1 := by rw [mul_assoc, e1]; group
    simp only [map_add (f := _), slPS, e1, e2, Matrix.SpecialLinearGroup.coe_one, polySlash_one]
    abel
  refine ⟨potOf Γ z, ⟨fun τ => ?_, fun γ hγ => ⟨z γ, key γ hγ⟩⟩, key⟩
  by_cases hτ : τ ∈ Hs
  · exact polySlash_isHomogeneous _ (hz.1 _ (gel_spec Γ hτ).1)
  · have : gel Γ τ = 1 := by simp [gel, dif_neg hτ]
    unfold potOf
    rw [this]
    exact polySlash_isHomogeneous _ (hz.1 _ Γ.one_mem)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfHomogeneousPolyCoStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eichlerShimuraPotential_of_homogeneousPolyCocycle : ∀ (R : Type) [CommRing R] (w N l : ℕ), 4 ≤ N → ∀ z : SL(2, ℤ) → MvPolynomial (Fin 2) R, IsCoc w (Gam N l) z → ∃ F ∈ Pot R w (Gam N l), ∀ γ ∈ Gam N l, ∀ τ ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ = z γ := by
  first | exact @GlobalTheory.KZ.H3.exists_pot_of_isCoc | exact GlobalTheory.KZ.H3.exists_pot_of_isCoc | (intros; apply GlobalTheory.KZ.H3.exists_pot_of_isCoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraPotentialSubmoduleAndBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraPotentialSubmoduleAndBaseChange
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ

theorem pot_triv_lin : ∀ (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)), (∀ F G, F ∈ Pot R w Γ → G ∈ Pot R w Γ → F + G ∈ Pot R w Γ) ∧ (0 ∈ Pot R w Γ) ∧ (∀ (c : R) F, F ∈ Pot R w Γ → c • F ∈ Pot R w Γ) ∧ (∀ F G, F ∈ Triv R w Γ → G ∈ Triv R w Γ → F + G ∈ Triv R w Γ) ∧ (∀ (c : R) F, F ∈ Triv R w Γ → c • F ∈ Triv R w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Pot R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Pot S w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Triv R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Triv S w Γ) := by
  intro R _ w Γ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    refine ⟨fun z => (hF z).add (hG z), fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    obtain ⟨q, hq⟩ := hG' γ hγ
    refine ⟨p + q, fun z hz => ?_⟩
    simp only [Pi.add_apply, map_add (f := _)]
    rw [← hp z hz, ← hq z hz]; abel
  · refine ⟨fun z => MvPolynomial.isHomogeneous_zero _ _ _, fun γ _ => ⟨0, fun z _ => ?_⟩⟩
    simp
  · rintro c F ⟨hF, hF'⟩
    refine ⟨fun z => ?_, fun γ hγ => ?_⟩
    · simp only [Pi.smul_apply, MvPolynomial.smul_eq_C_mul]
      simpa using (MvPolynomial.isHomogeneous_C (Fin 2) c).mul (hF z)
    · obtain ⟨p, hp⟩ := hF' γ hγ
      refine ⟨c • p, fun z hz => ?_⟩
      simp only [Pi.smul_apply, map_smul]
      rw [← hp z hz, smul_sub]
  · rintro F G ⟨ψ, p, hψ, hp⟩ ⟨ψ', p', hψ', hp'⟩
    refine ⟨ψ + ψ', p + p', fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp only [Pi.add_apply, map_add (f := _), hψ γ hγ z hz, hψ' γ hγ z hz]
    · simp only [Pi.add_apply, hp z hz, hp' z hz]; abel
  · rintro c F ⟨ψ, p, hψ, hp⟩
    refine ⟨c • ψ, c • p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp only [Pi.smul_apply, map_smul, hψ γ hγ z hz]
    · simp only [Pi.smul_apply, hp z hz, smul_add]
  · rintro S _ f F ⟨hF, hF'⟩
    refine ⟨fun z => (hF z).map f, fun γ hγ => ?_⟩
    obtain ⟨p, hp⟩ := hF' γ hγ
    refine ⟨MvPolynomial.map f p, fun z hz => ?_⟩
    rw [← (polySlash_laws R).2.2.2.2.1 S f, ← map_sub, hp z hz]
  · rintro S _ f F ⟨ψ, p, hψ, hp⟩
    refine ⟨fun z => MvPolynomial.map f (ψ z), MvPolynomial.map f p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
    · simp only
      rw [← (polySlash_laws R).2.2.2.2.1 S f, hψ γ hγ z hz]
    · simp only [hp z hz, map_add (f := _)]

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraPotentialSubmoduleAndBaseChangeStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerShimuraPotential_submodule_and_base_change : ∀ (R : Type) [CommRing R] (w : ℕ) (Γ : Subgroup SL(2, ℤ)), (∀ F G, F ∈ Pot R w Γ → G ∈ Pot R w Γ → F + G ∈ Pot R w Γ) ∧ (0 ∈ Pot R w Γ) ∧ (∀ (c : R) F, F ∈ Pot R w Γ → c • F ∈ Pot R w Γ) ∧ (∀ F G, F ∈ Triv R w Γ → G ∈ Triv R w Γ → F + G ∈ Triv R w Γ) ∧ (∀ (c : R) F, F ∈ Triv R w Γ → c • F ∈ Triv R w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Pot R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Pot S w Γ) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) F, F ∈ Triv R w Γ → (fun z => MvPolynomial.map f (F z)) ∈ Triv S w Γ) := by
  first | exact @GlobalTheory.KZ.pot_triv_lin | exact GlobalTheory.KZ.pot_triv_lin | (intros; apply GlobalTheory.KZ.pot_triv_lin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerPotentialRelationPadic
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.KumPot

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cast_of_dvd {d M : ℕ} (h : d ∣ M) {x y : ℤ} (hxy : (x : ZMod M) = y) : (x : ZMod d) = y :=
  (ZMod.intCast_eq_intCast_iff _ _ _).2
    (Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 h) ((ZMod.intCast_eq_intCast_iff _ _ _).1 hxy))

theorem gamma_le {d M : ℕ} (h : d ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma d := by
  intro γ hγ
  obtain ⟨a, b, c, e⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
  refine CongruenceSubgroup.Gamma_mem.2 ⟨?_, ?_, ?_, ?_⟩
  · simpa using cast_of_dvd h (x := γ 0 0) (y := 1) (by simpa using a)
  · simpa using cast_of_dvd h (x := γ 0 1) (y := 0) (by simpa using b)
  · simpa using cast_of_dvd h (x := γ 1 0) (y := 0) (by simpa using c)
  · simpa using cast_of_dvd h (x := γ 1 1) (y := 1) (by simpa using e)

theorem gamma_le_gam {N l M : ℕ} (hN : N ∣ M) (hl : l ∣ M) : CongruenceSubgroup.Gamma M ≤ Gam N l := by
  intro γ hγ
  obtain ⟨a, -, c, e⟩ := CongruenceSubgroup.Gamma_mem.1 (gamma_le hN hγ)
  obtain ⟨-, -, c', -⟩ := CongruenceSubgroup.Gamma_mem.1 (gamma_le hl hγ)
  exact ⟨(CongruenceSubgroup.Gamma1_mem N γ).2 ⟨a, e, c⟩, CongruenceSubgroup.Gamma0_mem.2 c'⟩

theorem polySlash_eq_self_of_mem_Gamma (l n : ℕ) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma (l ^ n))
    (p : MvPolynomial (Fin 2) (ZMod (l ^ n))) : slP (δ : Matrix (Fin 2) (Fin 2) ℤ) p = p := by
  obtain ⟨a, b, c, e⟩ := CongruenceSubgroup.Gamma_mem.1 hδ
  rw [GlobalTheory.KZ.SlPLaws.polySlash_congr _ 1 p, GlobalTheory.KZ.SlPLaws.polySlash_one']
  intro i j
  fin_cases i <;> fin_cases j <;> simp [a, b, c, e]

theorem toZModPow_eval (l : ℕ) [Fact l.Prime] (n : ℕ) (u : Fin 2 → ℤ_[l]) (p : MvPolynomial (Fin 2) ℤ_[l]) :
    PadicInt.toZModPow n (MvPolynomial.eval u p) =
      MvPolynomial.eval (fun i => PadicInt.toZModPow n (u i)) (MvPolynomial.map (PadicInt.toZModPow n) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem kum_sum (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {ι : Type} (s : Finset ι) (x : ι → X.Khat l)
    (χ : ι → SL(2, ℤ) → ZMod (l ^ n)) (h : ∀ i ∈ s, Kum X l n (x i) (χ i)) :
    Kum X l n (∑ i ∈ s, x i) (∑ i ∈ s, χ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).1 _ _ _ _ (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end GlobalTheory.KZ.H3.KumPot

namespace GlobalTheory.KZ.H3.KumPot

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem bset_rel (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] [IsAlgClosed Ω] (hJ : JHol X) (N w : ℕ) (hN : 4 ≤ N)
    (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (hw : Odd w) (b : X.Fn l) (hb : b ∈ X.BSet N l w) :
    ∃ F ∈ Pot ℤ_[l] w (Gam N l), Rel X l b F := by
  obtain ⟨⟨c, hcA, hbc⟩, hinv⟩ := hb
  have hcoef := fun γ hγ i => GlobalTheory.T.binaryForm_coeff_of_gamma1CapGamma0_invariant Ω ε X l N w b c hbc γ hγ (hinv γ hγ) i
  obtain ⟨Φ, hΦ, hK⟩ := GlobalTheory.T.kummerCharacters_invariant_compatible_family Ω ε X l hJ N w c hcA hcoef
  obtain ⟨z, hz, hzΦ⟩ := GlobalTheory.T.exists_padic_cocycle_of_compatible_poly_family N l w (by omega) hl2 hlN hw Φ hΦ
  obtain ⟨F, hF, hFz⟩ := GlobalTheory.T.exists_eichlerShimuraPotential_of_homogeneousPolyCocycle ℤ_[l] w N l hN z hz
  refine ⟨F, hF, fun u n => ⟨fun δ => MvPolynomial.eval (fun i => PadicInt.toZModPow n (u i)) (Φ n δ), ?_, ?_⟩⟩
  · have hsum := kum_sum X l n (Finset.univ : Finset (Fin (w + 1))) (fun (i : Fin (w + 1)) => (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) • c i)
      (fun (i : Fin (w + 1)) δ => PadicInt.toZModPow n (u 0 ^ (i : ℕ) * u 1 ^ (w - (i : ℕ))) *
        AddMonoidAlgebra.coeff (Φ n δ) (Finsupp.single 0 (i : ℕ) + Finsupp.single 1 (w - (i : ℕ))))
      (fun i _ => GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n _ _ _ (hK n i))
    rw [← hbc u] at hsum
    convert hsum using 1
    funext δ
    rw [Finset.sum_apply]
    have MX := GlobalTheory.T.binaryMonomialDegree_subst_expansion (ZMod (l ^ n)) w
    conv_lhs => rw [MX.2.1 (Φ n δ) (hΦ.1 n δ)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MvPolynomial.eval_C, MX.2.2.2.1, map_pow]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · obtain ⟨M1, hM1, hM1'⟩ := hzΦ n
    have hl : 0 < l := (Fact.out : l.Prime).pos
    refine ⟨N * l ^ (n + 1) * M1, by positivity, fun δ hδ τ hτ => ?_⟩
    have hδG : δ ∈ Gam N l := gamma_le_gam (l := l) ⟨l ^ (n + 1) * M1, by ring⟩
      ⟨N * l ^ n * M1, by ring⟩ hδ
    have hδn : δ ∈ CongruenceSubgroup.Gamma (l ^ n) := gamma_le ⟨N * l * M1, by ring⟩ hδ
    have hδ1 : δ ∈ CongruenceSubgroup.Gamma M1 := gamma_le ⟨N * l ^ (n + 1), by ring⟩ hδ
    have e1 := hFz δ hδG τ hτ
    have e2 : MvPolynomial.map (PadicInt.toZModPow n) (z δ) = Φ n δ := hM1' δ hδ1
    have e3 : MvPolynomial.map (PadicInt.toZModPow n) (F (mob (ofSL δ) τ)) =
        MvPolynomial.map (PadicInt.toZModPow n) (slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL δ) τ))) := by
      rw [GlobalTheory.KZ.SlPLaws.map_slP, polySlash_eq_self_of_mem_Gamma l n hδn]
    rw [map_sub, toZModPow_eval, toZModPow_eval, e3, ← map_sub, ← map_sub, e1, e2]

end GlobalTheory.KZ.H3.KumPot

theorem GlobalTheory.KZ.H3.exists_pot_rel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ), 4 ≤ N → l ≠ 2 → ¬ l ∣ N → Odd w →
    ∀ b ∈ X.B N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), Rel X l b F := by
  intro Ω _ _ ε X l _ _ hJ N w hN hl2 hlN hw b hb
  have RO := GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable Ω ε X l
  have PL := GlobalTheory.T.eichlerShimuraPotential_submodule_and_base_change ℤ_[l] w (Gam N l)
  induction hb using Submodule.span_induction with
  | mem b hb => exact KumPot.bset_rel X l hJ N w hN hl2 hlN hw b hb
  | zero => exact ⟨0, PL.2.1, RO.2.1⟩
  | add b b' _ _ ih ih' =>
    obtain ⟨F, hF, hR⟩ := ih
    obtain ⟨F', hF', hR'⟩ := ih'
    exact ⟨F + F', PL.1 _ _ hF hF', RO.1 _ _ _ _ hR hR'⟩
  | smul a b _ ih =>
    obtain ⟨F, hF, hR⟩ := ih
    exact ⟨a • F, PL.2.2.1 a F hF, RO.2.2.1 a b F hR⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerPotentialRelationPadicStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerPotentialRelation_padic : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ), 4 ≤ N → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ b ∈ X.B N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), Rel X l b F := by
  first | exact @GlobalTheory.KZ.H3.exists_pot_rel | exact GlobalTheory.KZ.H3.exists_pot_rel | (intros; apply GlobalTheory.KZ.H3.exists_pot_rel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemKummer
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem GlobalTheory.KZ.exists_pot_rel_of_mem_bSet : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F := by
  intro Ω _ _ _ ε X _ hj N l w hl h2 hN hc hw b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨φ, hφ, hφ'⟩ := hj
  exact GlobalTheory.T.exists_kummerPotentialRelation_padic Ω ε X l ⟨φ, hφ', hφ⟩ N w (by omega) h2
    ((Nat.Prime.coprime_iff_not_dvd hl.out).1 hc.symm) hw b (Submodule.subset_span hb)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemKummerStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_kummer : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F := by
  first | exact @GlobalTheory.KZ.exists_pot_rel_of_mem_bSet | exact GlobalTheory.KZ.exists_pot_rel_of_mem_bSet | (intros; apply GlobalTheory.KZ.exists_pot_rel_of_mem_bSet <;> assumption)
end
