module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.AmplePlusNefInduction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNonzeroPairSectionOfAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNonzeroPairSectionOfAmple
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem exists_pos_nonzero_mem_H : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ),
      ∃ (c : ℕ) (h : X.functionField), 0 < c ∧ h ≠ 0 ∧ h ∈ P.H a c := by
  intro k _ X _ p D hX P hA a
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a 0
  obtain ⟨b, hb, u, hu⟩ := exists_sec_finite_subset_nonzeroLocus k X p D hX M P.A hA {genericPoint X}
    (Set.finite_singleton _)
  have hA1 := (Pair.rep_base k X p P).2.1
  have hAb := Pair.rep_pow k X p P 0 1 P.A b hA1
  have hN := Pair.rep_tens k X p P a 0 _ _ M (P.A.pow b) hM hAb
  have e1 : a + (b : ℤ) * 0 = a := by ring
  have e2 : (0 : ℤ) + (b : ℤ) * 1 = b := by ring
  rw [e1, e2] at hN
  obtain ⟨e, -, hrange, -, hloc⟩ := RepDict.rep_dict k X p P a b _ hN
  have hmem : e u ∈ P.H a b := by
    have : e u ∈ Set.range e := Set.mem_range_self u
    rw [hrange] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i, genericPoint X ∈ P.L.B.U i :=
    Opens.mem_iSup.1 (P.L.isLB.cover.ge (Opens.mem_top _))
  obtain ⟨j, hj⟩ : ∃ j, genericPoint X ∈ P.A.B.U j :=
    Opens.mem_iSup.1 (P.A.isLB.cover.ge (Opens.mem_top _))
  have hU := (hloc u (genericPoint X) i j hi hj).1 (hu rfl)
  refine ⟨b, e u, hb, fun h0 => ?_, hmem⟩
  have hz : ∀ x : X, ¬ UnitAt x (0 : X.functionField) := by
    rintro x ⟨w, hw, h⟩
    exact (hw.map (algebraMap _ X.functionField)).ne_zero h
  rw [h0] at hU
  have z : P.loc a b 0 i j = 0 := by simp [Pair.loc]
  rw [z] at hU
  exact hz _ hU

end GlobalTheory.HSNef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNonzeroPairSectionOfAmpleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_nonzero_pairSection_of_ample : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ), ∃ (c : ℕ) (h : X.functionField), 0 < c ∧ h ≠ 0 ∧ h ∈ P.H a c := by
  first | exact @GlobalTheory.HSNef.exists_pos_nonzero_mem_H | exact GlobalTheory.HSNef.exists_pos_nonzero_mem_H | (intros; apply GlobalTheory.HSNef.exists_pos_nonzero_mem_H <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionClearingRationalFunctionDenomi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionClearingRationalFunctionDenomi
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSNef.DenOne

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.LBGerm

variable {X : Scheme.{0}} [IsIntegral X]

theorem isRatSec_lbPow {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) (τ : ℕ) :
    IsRatSec (lbPow L τ) fun c => r (c PUnit.unit) ^ τ := fun c c' h => by
  have l : (lbPow L τ).U c ⊓ (lbPow L τ).U c' ≤ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have e : (lbPow L τ).g c c' = res l (L.g (c PUnit.unit) (c' PUnit.unit)) ^ τ := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    ← mul_pow, hr _ _ (l h)]
  exact congrArg (fun a => (a * _) ^ τ) (fnOf_resG l h _).symm

theorem res_mem_secOn (L : LB X) (V : X.Opens) (a : Γ(X, V)) :
    (fun J : PUnit → L.ι => resG X (inf_le_left : V ⊓ powChart L J ≤ V) a) ∈ secOn (lbPow L 0) V :=
  mem_secOn_of_germ _ fun y i j hV hi hj => by
    rw [gm_lbPow_g 0 (𝟙 X) y i j hi hj, pow_zero, Units.val_one, one_mul]
    exact (gs_res (𝟙 X) y _ (⟨hV, hi⟩ : y ∈ V ⊓ (lbPow L 0).U i) a).trans
      (gs_res (𝟙 X) y _ (⟨hV, hj⟩ : y ∈ V ⊓ (lbPow L 0).U j) a).symm

theorem unitAt_ne_zero {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : UnitAt x f) : f ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  exact (hc.map (algebraMap _ X.functionField)).ne_zero

theorem exists_den_one : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (f : X.functionField),
    ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H 0 c ∧ g * f ∈ P.H 0 c := by
  intro k _ X _ p D _ P hA f
  haveI := hA.compactSpace
  haveI := hA.quasiSeparatedSpace
  have hL := hA.isLB
  obtain ⟨n, hn, s, hgs, haff⟩ := hA.exists_affine (genericPoint X)
  haveI : Nonempty (nonzeroLocus s) := ⟨⟨_, hgs⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X (nonzeroLocus s) haff
  obtain ⟨a, b, hb, hf⟩ := IsFractionRing.div_surjective (A := Γ(X, nonzeroLocus s)) f
  change fnOf _ hgs a / fnOf _ hgs b = f at hf
  have hβ : fnOf _ hgs b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  obtain ⟨Na, ha⟩ := exists_sec_eq_pow_mul hL s _ (res_mem_secOn P.A.B (nonzeroLocus s) a)
  obtain ⟨Nb, hb'⟩ := exists_sec_eq_pow_mul hL s _ (res_mem_secOn P.A.B (nonzeroLocus s) b)
  obtain ⟨u, hu⟩ := ha (max Na Nb + 1) (by omega)
  obtain ⟨v, hv⟩ := hb' (max Na Nb + 1) (by omega)
  have hρ := isRatSec_lbPow P.hr' (0 + n * (max Na Nb + 1))
  obtain ⟨e, he⟩ := RepDict.exists_quot (isLB_lbPow hL (0 + n * (max Na Nb + 1))) hρ
  have hmem : ∀ w : (lbPow P.A.B (0 + n * (max Na Nb + 1))).Sec,
      e w ∈ P.H 0 ((0 + n * (max Na Nb + 1) : ℕ) : ℤ) := by
    intro w x i j _ hj
    have hJ : x ∈ (lbPow P.A.B (0 + n * (max Na Nb + 1))).U (fun _ => j) := mem_powChart.2 hj
    have h1 := he w (fun _ => j) (gen_mem hJ)
    simp only [Pair.loc, zpow_zero, mul_one, zpow_natCast]
    rw [← Units.val_pow_eq_pow_val, h1]
    exact regAt_fnOf hJ _ _
  obtain ⟨j₀, hj₀⟩ := exists_chart hL (genericPoint X)
  have hJ₀ : genericPoint X ∈ powChart P.A.B (fun _ => j₀) := mem_powChart.2 hj₀
  have hVJ : genericPoint X ∈ nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) := ⟨hgs, hJ₀⟩
  have key : ∀ (w : (lbPow P.A.B (0 + n * (max Na Nb + 1))).Sec) (a' : Γ(X, nonzeroLocus s)),
      resG X (inf_le_right : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ powChart P.A.B (fun _ => j₀))
          (powFn w (fun _ => j₀)) =
        resG X (inf_le_right : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ powChart P.A.B (fun _ => j₀))
          (powFn s (fun _ => j₀)) ^ (max Na Nb + 1) *
        resG X (inf_le_left : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ nonzeroLocus s) a' →
      e w * (P.r' j₀ : X.functionField) ^ (0 + n * (max Na Nb + 1)) =
        fnOf _ hJ₀ (powFn s (fun _ => j₀)) ^ (max Na Nb + 1) * fnOf _ hgs a' := by
    intro w a' h
    have h' := congrArg (fnOf _ hVJ) h
    rw [map_mul, map_pow, fnOf_resG, fnOf_resG, fnOf_resG] at h'
    rw [← Units.val_pow_eq_pow_val]
    exact (he w _ hJ₀).trans h'
  have eu := key u a (hu _)
  have ev := key v b (hv _)
  have hS : fnOf _ hJ₀ (powFn s (fun _ => j₀)) ≠ 0 := by
    exact unitAt_ne_zero ((unitAt_fnOf_iff hJ₀ hJ₀ _).2 ((mem_nonzeroLocus_iff_basicOpen s hJ₀).1 hgs))
  have hR : (P.r' j₀ : X.functionField) ^ (0 + n * (max Na Nb + 1)) ≠ 0 := pow_ne_zero _ (P.r' j₀).ne_zero
  refine ⟨0 + n * (max Na Nb + 1), e v, by positivity, fun h0 => ?_, hmem v, ?_⟩
  · rw [h0, zero_mul] at ev
    exact mul_ne_zero (pow_ne_zero _ hS) hβ ev.symm
  · have e1 : e u = _ := eq_div_of_mul_eq hR eu
    have e2 : e v = _ := eq_div_of_mul_eq hR ev
    have : e v * f = e u := by
      rw [e1, e2, ← hf]
      field_simp
    rw [this]
    exact hmem u

end GlobalTheory.HSNef.DenOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionClearingRationalFunctionDenomiStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ampleSection_clearing_rationalFunction_denominator : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (f : X.functionField), ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H 0 c ∧ g * f ∈ P.H 0 c := by
  first | exact @GlobalTheory.HSNef.DenOne.exists_den_one | exact GlobalTheory.HSNef.DenOne.exists_den_one | (intros; apply GlobalTheory.HSNef.DenOne.exists_den_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundle
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef.Den

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem one_mem_H (P : Pair p) : (1 : X.functionField) ∈ P.H 0 0 := by
  intro x i j _ _
  exact ⟨1, by simp [Pair.loc]⟩

theorem mul_mem_H {P : Pair p} {a b a' b' : ℤ} {f g : X.functionField} (hf : f ∈ P.H a b) (hg : g ∈ P.H a' b') :
    f * g ∈ P.H (a + a') (b + b') :=
  (NuMul.mul_mem_H_and_nu_mul k X p P a b a' b' f g hf hg).1

theorem prod_mem_H {P : Pair p} {J : Type} (s : Finset J) (c : J → ℕ) (g : J → X.functionField)
    (hg : ∀ j ∈ s, g j ∈ P.H 0 (c j)) : (∏ j ∈ s, g j) ∈ P.H 0 ((∑ j ∈ s, c j : ℕ) : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_mem_H P
  | insert l s hl ih =>
    rw [Finset.prod_insert hl, Finset.sum_insert hl]
    have := mul_mem_H (hg l (Finset.mem_insert_self l s)) (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))
    simpa using this

theorem exists_clear_denominators : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ) (J : Type) [Finite J] (f : J → X.functionField), ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H a c ∧ ∀ j, g * f j ∈ P.H a c := by
  intro k _ X _ p D hX P hA a J _ f
  classical
  have := Fintype.ofFinite J
  choose c g hc hg0 hg hgf using fun j => GlobalTheory.T.exists_ampleSection_clearing_rationalFunction_denominator k X p D hX P hA (f j)
  obtain ⟨c', h, hc', h0, hh⟩ := GlobalTheory.T.exists_pos_nonzero_pairSection_of_ample k X p D hX P hA a
  refine ⟨c' + ∑ j, c j, h * ∏ j, g j, by omega, mul_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun j _ => hg0 j), ?_, fun j => ?_⟩
  · have := mul_mem_H hh (prod_mem_H Finset.univ c g fun j _ => hg j)
    simpa using this
  · have e : h * (∏ l, g l) * f j = h * ((g j * f j) * ∏ l ∈ Finset.univ.erase j, g l) := by
      rw [← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ j)]; ring
    have es : ∑ l, c l = c j + ∑ l ∈ Finset.univ.erase j, c l := (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
    rw [e, es]
    have := mul_mem_H hh (mul_mem_H (hgf j) (prod_mem_H (Finset.univ.erase j) c g fun l _ => hg l))
    simpa using this

end GlobalTheory.HSNef.Den
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClearDenominatorsAmpleHermLineBundleStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clear_denominators_ampleHermLineBundle : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (a : ℤ) (J : Type) [Finite J] (f : J → X.functionField), ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H a c ∧ ∀ j, g * f j ∈ P.H a c := by
  first | exact @GlobalTheory.HSNef.Den.exists_clear_denominators | exact GlobalTheory.HSNef.Den.exists_clear_denominators | (intros; apply GlobalTheory.HSNef.Den.exists_clear_denominators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystallineFormLiftDifferenceEqSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystallineFormLiftDifferenceEqSum
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS.FormLocal

open KaehlerDifferential
attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

section Alg

variable {R B C : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  {J : Ideal C}

theorem mul_eq_zero_of_sq (hJ : J ^ 2 = 0) {a b : C} (ha : a ∈ J) (hb : b ∈ J) : a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rwa [← pow_two, hJ, Ideal.zero_eq_bot, Ideal.mem_bot] at this

def diffDer (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J) :
    letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
    Derivation R B C :=
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  { toFun := fun b ↦ ρ₁ b - ρ₂ b
    map_add' := fun a b ↦ by simp only [map_add (f := _)]; ring
    map_smul' := fun r b ↦ by
      simp only [map_smul, RingHom.id_apply, smul_sub]
    map_one_eq_zero' := by simp
    leibniz' := fun a b ↦ by
      change ρ₁ (a * b) - ρ₂ (a * b) = ρ₂ a * (ρ₁ b - ρ₂ b) + ρ₂ b * (ρ₁ a - ρ₂ a)
      have h0 := mul_eq_zero_of_sq hJ (hd a) (hd b)
      simp only [map_mul]
      linear_combination h0 }

def diffLam (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J) : Ω[B⁄R] →+ C :=
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₂.commutes r).symm
  ((diffDer hJ ρ₁ ρ₂ hd).liftKaehlerDifferential).toAddMonoidHom

variable (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J)

theorem diffLam_smul (b : B) (m : Ω[B⁄R]) :
    diffLam hJ ρ₁ ρ₂ hd (b • m) = ρ₂ b * diffLam hJ ρ₁ ρ₂ hd m := by
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₂.commutes r).symm
  exact ((diffDer hJ ρ₁ ρ₂ hd).liftKaehlerDifferential).map_smul b m

theorem diffLam_D (t : B) : diffLam hJ ρ₁ ρ₂ hd (D R B t) = ρ₁ t - ρ₂ t := by
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₂.commutes r).symm
  exact (diffDer hJ ρ₁ ρ₂ hd).liftKaehlerDifferential_comp_D t

theorem diffLam_mem (m : Ω[B⁄R]) : diffLam hJ ρ₁ ρ₂ hd m ∈ J := by
  induction m using GlobalTheory.CechDR.ind1 with
  | h b c => rw [diffLam_smul, diffLam_D]; exact J.mul_mem_left _ (hd c)
  | h0 => rw [map_zero]; exact J.zero_mem
  | ha x y hx hy => rw [map_add (f := _)]; exact J.add_mem hx hy

end Alg

section Alg2

variable {R B C : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  {J : Ideal C} (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J)

def diagLift : TrivSqZeroExt B Ω[B⁄R] →ₐ[R] C where
  toFun c := ρ₂ c.fst + diffLam hJ ρ₁ ρ₂ hd c.snd
  map_one' := by simp
  map_zero' := by simp
  map_add' a b := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add (f := _)]; ring
  map_mul' a b := by
    have h0 := mul_eq_zero_of_sq hJ (diffLam_mem hJ ρ₁ ρ₂ hd a.snd) (diffLam_mem hJ ρ₁ ρ₂ hd b.snd)
    have e : (MulOpposite.op b.fst • a.snd : Ω[B⁄R]) = b.fst • a.snd := rfl
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, map_mul, map_add (f := _), e, diffLam_smul]
    linear_combination -h0
  commutes' r := by
    simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem diagLift_apply (c : TrivSqZeroExt B Ω[B⁄R]) :
    diagLift hJ ρ₁ ρ₂ hd c = ρ₂ c.fst + diffLam hJ ρ₁ ρ₂ hd c.snd := rfl

theorem diagLift_inl (b : B) : diagLift hJ ρ₁ ρ₂ hd (TrivSqZeroExt.inl b) = ρ₂ b := by
  simp [diagLift_apply]

theorem diagLift_diagSec (b : B) : diagLift hJ ρ₁ ρ₂ hd (diagSec R B b) = ρ₁ b := by
  rw [diagLift_apply, fst_derSec, snd_derSec, diffLam_D]; ring

theorem diagLift_sub_mem (c : TrivSqZeroExt B Ω[B⁄R]) : diagLift hJ ρ₁ ρ₂ hd c - ρ₂ c.fst ∈ J := by
  rw [diagLift_apply, add_sub_cancel_left]; exact diffLam_mem hJ ρ₁ ρ₂ hd _

end Alg2

section Repr

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem exists_sum_smul_D (m : Ω[B⁄R]) : ∃ (n : ℕ) (r t : Fin n → B), m = ∑ k, r k • D R B (t k) := by
  induction m using GlobalTheory.CechDR.ind1 with
  | h b c => exact ⟨1, fun _ ↦ b, fun _ ↦ c, by simp⟩
  | h0 => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | ha x y hx hy =>
    obtain ⟨n, r, t, rfl⟩ := hx
    obtain ⟨n', r', t', rfl⟩ := hy
    refine ⟨n + n', Fin.append r r', Fin.append t t', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

end Repr

section Geo

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {U : X.Opens}

def valHom {C : Type} [CommRing C] [Algebra R C] (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U)
    (hs : y ≫ s = spMap (algebraMap R C)) : CechDR.Sec s U →ₐ[R] C :=
  { (GlobalTheory.Points.valMap y U hy).hom with
    commutes' := fun r ↦ by
      have e1 := GlobalTheory.Points.valR_appLE y s (U := ⊤) (V := U) le_top hy
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
      rw [hs, GlobalTheory.Points.valR_specMap, GlobalTheory.Points.valR_eq y U hy] at e1
      exact e1 }

theorem valR_eq_valHom {C : Type} [CommRing C] [Algebra R C] (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U)
    (hs : y ≫ s = spMap (algebraMap R C)) (f : Γ(X, U)) : valR y U f = valHom y hy hs f :=
  GlobalTheory.Points.valR_eq y U hy f

theorem valHom_pt {C : Type} [CommRing C] [Algebra R C] (hU : IsAffineOpen U) (y : Sp C ⟶ X)
    (hy : ⊤ ≤ y ⁻¹ᵁ U) (hs : y ≫ s = spMap (algebraMap R C)) :
    spMap (valHom y hy hs : CechDR.Sec s U →+* C) ≫ CechDR.affPt s ⟨U, hU⟩ = y :=
  GlobalTheory.Points.specMap_valMap_fromSpec hU y hy

theorem ringHom_ext_affPt {C : Type} [CommRing C] (hU : IsAffineOpen U) {a b : CechDR.Sec s U →+* C}
    (h : spMap a ≫ CechDR.affPt s ⟨U, hU⟩ = spMap b ≫ CechDR.affPt s ⟨U, hU⟩) : a = b := by
  have h1 : spMap a = spMap b := (cancel_mono hU.fromSpec).1 h
  have h2 := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

def diagPr (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) :
    (diagExt R B).thick x hx ⟶ Thick.triv B x hx where
  φ := (diagExt R B).π
  φ₀ := RingHom.id B
  comm _ := rfl
  dp := (DividedPowers.isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ ha,
    fun n hn a ha ↦ by
      have ha' : ((diagExt R B).π : TrivSqZeroExt B Ω[B⁄R] →+* B) a = 0 := ha
      have hm := (divided₂ (diagExt R B).sq).dpow_mem hn ha
      have hm' : ((diagExt R B).π : TrivSqZeroExt B Ω[B⁄R] →+* B) ((divided₂ (diagExt R B).sq).dpow n a) = 0 := hm
      rw [hm', ha', DividedPowers.dpow_eval_zero _ hn]⟩
  pt := by rw [spMap_id, Category.id_comp]

theorem fst_ev_secHom (ω : Form s) (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)) (j : B →ₐ[R] TrivSqZeroExt B Ω[B⁄R])
    (hj : ∀ b, (j b).fst = b) :
    (ev ω.1 ((diagExt R B).secHom hx j hj)).fst = - ev ω.1 (diagPr B x hx) := by
  have h0 : ev ω.1 ((diagExt R B).secHom hx j hj ≫ diagPr B x hx) = 0 := ω.2 _ rfl rfl
  rw [ev_comp] at h0
  exact eq_neg_of_add_eq_zero_left h0

end Geo

theorem ev_idLift_sub_eq_sum : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (ω : Form s) (U : X.Opens), IsAffineOpen U → ∃ (n : ℕ) (r t : Fin n → Γ(X, U)), ∀ (T : Thick (dp0 R) s) (hJ : T.J ^ 2 = 0), T.δ = divided₂ hJ → ∀ (y₁ y₂ : Sp T.B ⟶ X) (h₁ : y₁ ≫ s = spMap (algebraMap R T.B)) (h₂ : y₂ ≫ s = spMap (algebraMap R T.B)) (e₁ : spMap T.π ≫ y₁ = T.x) (e₂ : spMap T.π ≫ y₂ = T.x), ⊤ ≤ y₁ ⁻¹ᵁ U → ⊤ ≤ y₂ ⁻¹ᵁ U → ev ω.1 (idLift T y₂ h₂ e₂) - ev ω.1 (idLift T y₁ h₁ e₁) = ∑ k, valR y₂ U (r k) * (valR y₁ U (t k) - valR y₂ U (t k)) := by
  intro R _ X s ω U hU
  have hx := CechDR.affPt_w s ⟨U, hU⟩
  obtain ⟨n, r, t, hΩ⟩ := exists_sum_smul_D (connForm ω.1 (CechDR.affPt s ⟨U, hU⟩) hx)
  refine ⟨n, r, t, ?_⟩
  intro T hJ hδ y₁ y₂ h₁ h₂ e₁ e₂ hy₁ hy₂
  have p₁ := valHom_pt hU y₁ hy₁ h₁
  have p₂ := valHom_pt hU y₂ hy₂ h₂
  have hπ : T.π.comp (valHom y₁ hy₁ h₁ : CechDR.Sec s U →+* T.B) = T.π.comp (valHom y₂ hy₂ h₂ : CechDR.Sec s U →+* T.B) :=
    ringHom_ext_affPt hU (by rw [Cris.spMap_comp, Cris.spMap_comp, Category.assoc, Category.assoc, p₁, p₂, e₁, e₂])
  have hd : ∀ b, valHom y₁ hy₁ h₁ b - valHom y₂ hy₂ h₂ b ∈ T.J := fun b ↦
    (T.ker _).1 (by rw [map_sub, sub_eq_zero]; exact RingHom.congr_fun hπ b)
  let Φ : (diagExt R (CechDR.Sec s U)).thick (CechDR.affPt s ⟨U, hU⟩) hx ⟶ T :=
    { φ := diagLift hJ _ _ hd
      φ₀ := T.π.comp (valHom y₂ hy₂ h₂ : CechDR.Sec s U →+* T.B)
      comm := fun c ↦ by
        have h0 := (T.ker _).2 (diagLift_sub_mem hJ _ _ hd c)
        rw [map_sub, sub_eq_zero] at h0
        exact h0.symm
      dp := by
        have key : DividedPowers.IsDPMorphism (divided₂ (diagExt R (CechDR.Sec s U)).sq) (divided₂ hJ)
            (diagLift hJ _ _ hd : TrivSqZeroExt (CechDR.Sec s U) Ω[(CechDR.Sec s U)⁄R] →+* T.B) :=
          isDPMorphism_sqDP _ hJ _ fun (a : TrivSqZeroExt (CechDR.Sec s U) Ω[(CechDR.Sec s U)⁄R]) ha ↦ by
            have ha' : a.fst = 0 := ha
            have h0 := diagLift_sub_mem hJ _ _ hd a
            rwa [ha', map_zero, sub_zero] at h0
        rw [hδ]
        exact key
      pt := by rw [Cris.spMap_comp, Category.assoc, p₂, e₂] }
  let a₁ : Thick.triv (CechDR.Sec s U) (CechDR.affPt s ⟨U, hU⟩) hx ⟶ Thick.triv T.B y₁ h₁ :=
    Thick.trivHom (valHom y₁ hy₁ h₁) p₁
  let a₂ : Thick.triv (CechDR.Sec s U) (CechDR.affPt s ⟨U, hU⟩) hx ⟶ Thick.triv T.B y₂ h₂ :=
    Thick.trivHom (valHom y₂ hy₂ h₂) p₂
  have k₂ := Form.ev_sq ω a₂ (idLift T y₂ h₂ e₂)
    ((diagExt R (CechDR.Sec s U)).secHom hx (diagExt R (CechDR.Sec s U)).i fun _ ↦ rfl) Φ rfl rfl
    fun c ↦ (diagLift_inl hJ _ _ hd c).symm
  have k₁ := Form.ev_sq ω a₁ (idLift T y₁ h₁ e₁)
    ((diagExt R (CechDR.Sec s U)).secHom hx (diagSec R (CechDR.Sec s U)) (fst_derSec _)) Φ rfl rfl
    fun c ↦ (diagLift_diagSec hJ _ _ hd c).symm
  have f₁ := fst_ev_secHom ω (CechDR.Sec s U) _ hx (diagExt R (CechDR.Sec s U)).i fun _ ↦ rfl
  have f₂ := fst_ev_secHom ω (CechDR.Sec s U) _ hx (diagSec R (CechDR.Sec s U)) (fst_derSec _)
  rw [k₁, k₂, add_sub_add_right_eq_sub, ← map_sub]
  change diagLift hJ _ _ hd _ = _
  rw [diagLift_apply, TrivSqZeroExt.fst_sub, f₁, f₂, sub_self, map_zero, zero_add]
  have hc : (ev ω.1 ((diagExt R (CechDR.Sec s U)).secHom hx (diagExt R (CechDR.Sec s U)).i fun _ ↦ rfl) -
      ev ω.1 ((diagExt R (CechDR.Sec s U)).secHom hx (diagSec R (CechDR.Sec s U)) (fst_derSec _))).snd =
      connForm ω.1 (CechDR.affPt s ⟨U, hU⟩) hx := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc, hΩ, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [diffLam_smul, diffLam_D]
  exact (congrArg₂ (fun a b ↦ a * b) (valR_eq_valHom y₂ hy₂ h₂ (r k))
    (congrArg₂ (fun a b ↦ a - b) (valR_eq_valHom y₁ hy₁ h₁ (t k)) (valR_eq_valHom y₂ hy₂ h₂ (t k)))).symm

end GlobalTheory.CechKS.FormLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystallineFormLiftDifferenceEqSumStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystallineForm_lift_difference_eq_sum : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (ω : Form s) (U : X.Opens), IsAffineOpen U → ∃ (n : ℕ) (r t : Fin n → Γ(X, U)), ∀ (T : Thick (dp0 R) s) (hJ : T.J ^ 2 = 0), T.δ = divided₂ hJ → ∀ (y₁ y₂ : Sp T.B ⟶ X) (h₁ : y₁ ≫ s = spMap (algebraMap R T.B)) (h₂ : y₂ ≫ s = spMap (algebraMap R T.B)) (e₁ : spMap T.π ≫ y₁ = T.x) (e₂ : spMap T.π ≫ y₂ = T.x), ⊤ ≤ y₁ ⁻¹ᵁ U → ⊤ ≤ y₂ ⁻¹ᵁ U → ev ω.1 (idLift T y₂ h₂ e₂) - ev ω.1 (idLift T y₁ h₁ e₁) = ∑ k, valR y₂ U (r k) * (valR y₁ U (t k) - valR y₂ U (t k)) := by
  first | exact @GlobalTheory.CechKS.FormLocal.ev_idLift_sub_eq_sum | exact GlobalTheory.CechKS.FormLocal.ev_idLift_sub_eq_sum | (intros; apply GlobalTheory.CechKS.FormLocal.ev_idLift_sub_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.RetractGeneric

theorem isProper_of_retract {S : Scheme.{0}} {X Y : Over S} (i : X ⟶ Y) (r : Y ⟶ X)
    (h : i ≫ r = 𝟙 X) (hY : IsProper Y.hom) : IsProper X.hom := by
  have hl : i.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, h, Over.id_left]
  have h1 : IsSeparated (r.left ≫ X.hom) := by rw [Over.w r]; infer_instance
  have h2 : IsSeparated r.left := IsSeparated.of_comp r.left X.hom
  have h3 : IsClosedImmersion (i.left ≫ r.left) := by rw [hl]; infer_instance
  have h4 : IsClosedImmersion i.left := IsClosedImmersion.of_comp i.left r.left
  rw [← Over.w i]
  infer_instance

theorem isAbelianScheme_generic : ∀ (R : Type) [CommRing R] [IsDomain R] (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ((Over.pullback (jK R)).obj G' ≅ A'.A) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → IsAbelianScheme ((Over.pullback (jK R)).obj G) := by
  intro R _ _ A' G' _ _ _ e G _ _ hG inc pr _ _ h
  have hK := IsSemiAbelian.pullback (jK R) G hG
  have hp : IsProper ((Over.pullback (jK R)).obj G).hom :=
    isProper_of_retract ((Over.pullback (jK R)).map inc ≫ e.hom)
      (e.inv ≫ (Over.pullback (jK R)).map pr)
      (by rw [Category.assoc, e.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp, h,
        CategoryTheory.Functor.map_id]) A'.isAb.proper
  exact ⟨hK.comm, hK.smooth, hp, hK.geomConnected⟩

end GlobalTheory.Mum.RetractGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomTrivIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PoincarePull

theorem exists_hom_triv_iff : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (D : Over (Sp R)) [GrpObj D] (Q : LB (A ⊗ D).left), GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsDual D A (GlobalTheory.AbDual.swap Q) →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∀ P : LB (A ⊗ A).left, P.IsLB →
    HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
    ∃ x : A ⟶ D, IsMonHom x ∧ ∀ (T : Over (Sp R)) (y : T ⟶ A),
      (HasGen (P.pull (lift (fst A T) (snd A T ≫ y)).left) ↔ y ≫ x = 1) := by
  intro R _ A _ hA D _ Q q q' L hL aL P hP h₁ h₂
  obtain ⟨H, hH, aH⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod hA hA hL aL hL aL
  obtain ⟨a₁, a₂⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH aH hP h₁ h₂
  obtain ⟨x, hx, e⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hP a₁ a₂
  refine ⟨x, hx, fun T y ↦ ?_⟩
  have k := GlobalTheory.AbDual.triv_ev_iff hP (fst A T) (snd A T ≫ y)
  rw [GlobalTheory.BirigidLift.evc_of_cls q.isLB hP e, Category.assoc, ← GlobalTheory.AbDual.triv_ev_iff q.isLB] at k
  refine k.trans ⟨fun h ↦ q.eq_one (y ≫ x) h, fun h ↦ ?_⟩
  rw [h, GlobalTheory.AbDual.triv_ev_iff q.isLB, MonObj.comp_one]
  exact GlobalTheory.AbDual.evc_one_right q.isLB q.zero _

end GlobalTheory.PoincarePull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfForallField
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)

namespace GlobalTheory.FibreDim

theorem smoothOfRelativeDimension_of_forall_field : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (g : ℕ), Smooth X.hom → (∀ (k : Type) [Field k] [Algebra R k], SmoothOfRelativeDimension g (Limits.pullback.snd X.hom (spMap (algebraMap R k)))) → SmoothOfRelativeDimension g X.hom := by
  intro R _ X g hs h
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom
  have hn : ∀ x, n x = g := fun x => by
    let p : PrimeSpectrum R := X.hom x
    have hk := h p.asIdeal.ResidueField
    let t := spMap (algebraMap R p.asIdeal.ResidueField)
    obtain ⟨y, hy⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R p.asIdeal.ResidueField)) := by
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
      exact Ideal.ker_algebraMap_residueField p.asIdeal
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} (n x)
    have h1 : SmoothOfRelativeDimension (n x) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) :=
      this.of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t) (hd x)
    have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) := by
      rw [← Limits.pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance
    obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t)
      ⟨x, hW x⟩ y hy.symm
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← hn x]; exact hd x

end GlobalTheory.FibreDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleAddNefIsAmple
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory

theorem isAmpleLB_tens_of_isNef_of_dim_le (k : Type) [Field k] [Infinite k] : ∀ d : ℕ,
    ∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) →
      ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N) := by
  intro d
  induction d with
  | zero => exact isAmpleLB_tens_of_isNef_of_dim_le_zero k
  | succ d ih => exact GlobalTheory.T.ample_plus_nef_induction k d ih

theorem isAmpleLB_of_cls_eq_ample_add_nef : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (A N P : LB X) (hA : IsAmpleLB A) (hN : letI := algebraΓOfHom p; IsNef k N) (hP : P.IsLB), cls P hP = cls A hA.isLB + cls N (letI := algebraΓOfHom p; hN.isLB) → IsAmpleLB P := by
  intro k _ _ X p hp A N P hA hN hP hcls
  letI := algebraΓOfHom p
  have hs : strHom k X = p := strHom_eq fun _ => rfl
  have hp' : IsProjOver (strHom k (X := X)) := hs ▸ hp
  obtain ⟨n, i, hi, -⟩ := hp
  have hd : topologicalKrullDim X ≤ (n : ℕ) :=
    i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans
      (ProjSpace.topologicalKrullDim_eq k n).le
  have hT : IsAmpleLB (tens A N) := isAmpleLB_tens_of_isNef_of_dim_le k n X hp' hd A N hA hN
  refine IsAmpleLB.of_lbIso hT hP ((cls_eq_iff hP hT.isLB).1 ?_)
  rw [hcls, cls_tens hA.isLB hN.isLB hT.isLB]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceEquivOfRingEquivOverConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceEquivOfRingEquivOverConstants
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem placeEquiv_ringEquiv : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∃ Φ : Place c ≃ Place c', ∀ E : Place c, (∀ a, e a ∈ (Φ E).ring ↔ a ∈ E.ring) ∧ (∀ a, (Φ E).ord (e a) = E.ord a) ∧ (∀ φ : K →₀ ℚ, (Φ E).ordQ (Finsupp.mapDomain e φ) = E.ordQ φ) ∧ ∀ (n : ℕ) (x : Fin n → K), TrBasis c x → (Φ E).formOrd (dForm c' (e ∘ x)) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm c x) := by
  intro k K K' _ _ _ _ c c' e he
  refine ⟨⟨RingEquivTransport.place e he,
    RingEquivTransport.place e.symm (RingEquivTransport.symm_apply e he),
    RingEquivTransport.place_symm_place e he, RingEquivTransport.place_place_symm e he⟩,
    fun E => ⟨RingEquivTransport.apply_mem_place e he E, RingEquivTransport.ord_place e he E,
      RingEquivTransport.ordQ_place e he E, fun n x _ => ?_⟩⟩
  have hd : dForm c' (e ∘ x) = TopForm.formMap n e.toRingHom (RingHom.ext he) (dForm c x) :=
    (TopForm.formMap_dForm e.toRingHom (RingHom.ext he) x).symm
  change (RingEquivTransport.place e he E).formOrd _ = _
  rw [hd]
  exact RingEquivTransport.formOrd_place e he E _

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPlaceEquivOfRingEquivOverConstantsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvrPlace_equiv_of_ringEquiv_over_constants : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'), (∀ a, e (c a) = c' a) → ∃ Φ : Place c ≃ Place c', ∀ E : Place c, (∀ a, e a ∈ (Φ E).ring ↔ a ∈ E.ring) ∧ (∀ a, (Φ E).ord (e a) = E.ord a) ∧ (∀ φ : K →₀ ℚ, (Φ E).ordQ (Finsupp.mapDomain e φ) = E.ordQ φ) ∧ ∀ (n : ℕ) (x : Fin n → K), TrBasis c x → (Φ E).formOrd (dForm c' (e ∘ x)) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm c x) := by
  first | exact @GlobalTheory.FieldPair.placeEquiv_ringEquiv | exact GlobalTheory.FieldPair.placeEquiv_ringEquiv | (intros; apply GlobalTheory.FieldPair.placeEquiv_ringEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismUniqueOfThickeningAc
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismUniqueOfThickeningAc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

theorem actsAs_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre b h g → ActsAs U.toUnifPre b h g' → g = g' := by
  intro R _ _ _ hR D A G _ _ hG U b h g g' hg hg' H H'
  have : IsNoetherianRing R := hR.1.1
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have : IsSeparated G.hom := hG.separated
  refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq (IsLocalRing.maximalIdeal_le_jacobson _) G g g' fun e => ?_
  obtain ⟨q1, t, ht, i1⟩ := H e
  obtain ⟨q2, t', ht', i2⟩ := H' e
  have htt : t = t' := GlobalTheory.LinearUnifCheck.torusEndOf_unique ht ht'
  have := (U.gt e).i_hom
  exact GlobalTheory.LinearUnifIso.hom_ext_torus (U.gt e) (U.gt e) GlobalTheory.globalFns_holds _ _
    (q1.trans q2.symm) (i1.trans (htt ▸ i2.symm))

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismUniqueOfThickeningAcStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_endomorphism_unique_of_thickening_action : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre b h g → ActsAs U.toUnifPre b h g' → g = g' := by
  first | exact @GlobalTheory.Mum.actsAs_unique | exact GlobalTheory.Mum.actsAs_unique | (intros; apply GlobalTheory.Mum.actsAs_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumMaximalIdealUniqueNoetherianLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumMaximalIdealUniqueNoetherianLocal
open IsLocalRing GlobalTheory.UT

namespace GlobalTheory.Poinc

theorem sumI_maximalIdeal_unique :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (Ix : Type) (x : Ix → R) (s s' : R),
      SumI (maximalIdeal R) x s → SumI (maximalIdeal R) x s' → s = s' := by
  classical
  intro R _ _ _ Ix x s s' ⟨N, _, _, _, h⟩ ⟨N', _, _, _, h'⟩
  have key : ∀ n : ℕ, s - s' ∈ maximalIdeal R ^ n := by
    intro n
    obtain ⟨S, hS⟩ := h n
    obtain ⟨S', hS'⟩ := h' n
    have le : ∀ M : Submodule R R, maximalIdeal R ^ n • M ≤ maximalIdeal R ^ n := fun M =>
      Submodule.smul_le.2 fun a ha b _ => Ideal.mul_mem_right b _ ha
    have h1 := le _ (hS (S ∪ S') Finset.subset_union_left)
    have h2 := le _ (hS' (S ∪ S') Finset.subset_union_right)
    have h3 := Ideal.sub_mem _ h1 h2
    rwa [sub_sub_sub_cancel_right] at h3
  have hb : ⨅ n : ℕ, maximalIdeal R ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  have : s - s' ∈ ⨅ n : ℕ, maximalIdeal R ^ n := Ideal.mem_iInf.2 key
  rw [hb, Ideal.mem_bot] at this
  exact sub_eq_zero.1 this

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicSumMaximalIdealUniqueNoetherianLocalStatement
open IsLocalRing GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicSum_maximalIdeal_unique_noetherian_local : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (Ix : Type) (x : Ix → R) (s s' : R), SumI (maximalIdeal R) x s → SumI (maximalIdeal R) x s' → s = s' := by
  first | exact @GlobalTheory.Poinc.sumI_maximalIdeal_unique | exact GlobalTheory.Poinc.sumI_maximalIdeal_unique | (intros; apply GlobalTheory.Poinc.sumI_maximalIdeal_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelOKOfIsPullDeg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open GlobalTheory.ArcPull ReciprocityTheory.ChartRestriction.G.DVR

theorem pelOK_of_isPullDeg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), PelOK Dm D.toPre o → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (φ : R →+* R'), Function.Injective φ → ∀ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg φ D.toPre D'.toPre) → ∃ (_ : Module (𝓞 E) D'.toPre.X) (o' : letI := H.starRing; D'.toPre.OAct (𝓞 E)), PelOK Dm D'.toPre o' := by
  intro R _ _ _ hR E _ _ _ H Dm D _ o hP R' _ _ _ φ hφ D' ⟨hD⟩
  letI := H.starRing
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  letI inst : Module (𝓞 E) D'.toPre.X := hD.xe.module (𝓞 E)
  have hx : ∀ (a : 𝓞 E) y, hD.xe (a • y) = a • hD.xe y := fun a y => hD.xe.apply_symm_apply _
  obtain ⟨o', ho⟩ := ArcPull.exists_oAct hD hG hφ o hx
  obtain ⟨hpq, hp1, hw, hF⟩ := hP
  refine ⟨inst, o', hpq, hp1, ArcPull.traceFormTwistIso_of_pullback hD hφ hx ho hw, fun F _ _ _ => ?_⟩
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing R') F).comp (ArcPull.fracMap hφ)).toAlgebra
  have hc : ArcPull.Compat φ F := fun x =>
    congrArg (algebraMap (FractionRing R') F) (ArcPull.fracMap_algebraMap hφ x)
  obtain ⟨hL, hT⟩ := hF F
  refine ⟨fun τ => ?_, fun ζ hζ hζ' => ?_⟩
  · obtain ⟨n, hn, hn'⟩ := hL τ
    refine ⟨n, (LiePull.lieMult_pull _ _ _ _ _ _ _ (ofRingAct o.onB.toRingAct) _ (pull_grp hD) ho F _ τ n).2 ?_, ?_⟩
    · rw [← spMap_comp, show ((algebraMap (FractionRing R') F).comp (algebraMap R' _)).comp φ =
        (algebraMap (FractionRing R) F).comp (algebraMap R _) from RingHom.ext fun r => (hc r).symm]
      exact hn
    · rw [(({ hD.xe with map_smul' := hx } : D'.toPre.X ≃ₗ[𝓞 E] D.toPre.X)).finrank_eq]
      exact hn'
  · obtain ⟨I, hI⟩ := hT ζ hζ hζ'
    exact ⟨ArcPull.pullTate hG hD hx ho D.tau_bimult D'.tau_bimult hc I, hI⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatPowEq
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtCover

theorem exists_faithfullyFlat_pow_eq :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ n : ℕ, 0 < n → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D') (ψ : D →ₐ[R] D') (z : Pt A D'),
        (ψ : D →+* D').FaithfullyFlat ∧ (z ^ n : Pt A D') = spOver ψ ≫ x := by
  intro R _ A _ hA n hn D _ _ x
  obtain ⟨hf, hfl⟩ := AbTorsionAnyBase.isFinite_and_flat_mulA _ A hA n hn
  have hs := AbelianLimit.surjective_pow A hA n hn
  let m : A.left ⟶ A.left := ((𝟙 A) ^ n : A ⟶ A).left
  have : IsFinite m := hf
  have : Flat m := hfl
  have : Surjective m := hs
  let x₀ : Spec (CommRingCat.of D) ⟶ A.left := x.left
  let Y := Limits.pullback x₀ m
  have : IsAffine Y := isAffine_of_isAffineHom (Limits.pullback.fst x₀ m)
  let q : Spec Γ(Y, ⊤) ⟶ Spec (CommRingCat.of D) := Y.isoSpec.inv ≫ Limits.pullback.fst x₀ m
  let φ : CommRingCat.of D ⟶ Γ(Y, ⊤) := Spec.preimage q
  have hφ : Spec.map φ = q := Spec.map_preimage q
  have hff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 (by
    rw [hφ]; exact ⟨inferInstance, inferInstance⟩)
  letI : Algebra R Γ(Y, ⊤) := (φ.hom.comp (algebraMap R D)).toAlgebra
  let ψ : D →ₐ[R] Γ(Y, ⊤) := { φ.hom with commutes' := fun _ ↦ rfl }
  have hψ : (spOver ψ).left = q := hφ
  have hc : (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) ≫ m = (spOver ψ ≫ x).left := by
    rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc, Over.comp_left, hψ]
  let z : Pt A Γ(Y, ⊤) := Over.homMk (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) (by
    rw [← Over.w (spOver ψ ≫ x), ← hc]
    simp only [Category.assoc]
    rw [Over.w ((𝟙 A) ^ n : A ⟶ A)])
  refine ⟨Γ(Y, ⊤), inferInstance, inferInstance, ψ, z, hff, ?_⟩
  rw [← Category.comp_id z, ← MonObj.comp_pow]
  exact Over.OverMorphism.ext hc

end GlobalTheory.PtCover
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingAndIsDomainOfIsComplAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem isRegularLocalRing_and_isDomain_of_isComplAt :
    ∀ (W : Type) [CommRing W] [IsRegularLocalRing W] (I : Type) [Fintype I] (R : Type) [CommRing R]
      [IsLocalRing R] (ψ : MvPolynomial I W →+* R), IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) →
      IsRegularLocalRing R ∧ IsDomain R := by
  intro W _ _ I _ R _ _ ψ hψ _
  obtain ⟨hnoeth, -, hflat, hmap, -⟩ := hψ
  haveI : IsRegularRing W := GlobalTheory.isRegularRing_of_isRegularLocalRing W
  set q : Ideal (MvPolynomial I W) := (maximalIdeal R).comap ψ with hq
  haveI : q.IsPrime := Ideal.comap_isPrime ψ (maximalIdeal R)
  let L := Localization.AtPrime q
  haveI : IsRegularLocalRing L := IsRegularRing.isRegularLocalRing_localization q
  have hu : ∀ y : q.primeCompl, IsUnit (ψ y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).2 h)
  let φ : L →+* R := IsLocalization.lift (M := q.primeCompl) hu
  letI : Algebra (MvPolynomial I W) R := ψ.toAlgebra
  letI : Algebra L R := φ.toAlgebra
  haveI : IsScalarTower (MvPolynomial I W) L R := IsScalarTower.of_algebraMap_eq (fun a => by
    change ψ a = φ (algebraMap _ L a)
    exact (IsLocalization.lift_eq (M := q.primeCompl) hu a).symm)
  haveI : Module.Flat (MvPolynomial I W) R := hflat
  haveI : IsLocalizedModule q.primeCompl (LinearMap.id : R →ₗ[MvPolynomial I W] R) :=
    isLocalizedModule_id q.primeCompl R L
  haveI : Module.Flat L R :=
    Module.Flat.of_isLocalizedModule L q.primeCompl (LinearMap.id : R →ₗ[MvPolynomial I W] R)
  haveI : IsNoetherianRing R := hnoeth
  have hm : maximalIdeal R = (maximalIdeal L).map (algebraMap L R) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact hmap.symm
  haveI hreg : IsRegularLocalRing R :=
    GlobalTheory.isRegularLocalRing_of_flat_of_map_eq_maximalIdeal L R (maximalIdeal L) hm
  exact ⟨hreg, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).1⟩

end GlobalTheory.TChart
end
