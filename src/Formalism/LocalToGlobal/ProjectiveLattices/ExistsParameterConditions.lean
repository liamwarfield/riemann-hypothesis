module

public import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
public import Formalism.LocalToGlobal.ProjectiveLattices.AvMono
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem g_mod (D : D7) (k : Fin 2) : D.host.g k % 4 = 1 ∧ D.host.g k % D.host.d = 1 := by
  have hc := D.ntypes.g_cond k
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  refine ⟨?_, ?_⟩
  · rw [← Nat.mod_mod_of_dvd (D.host.g k)
      (show 4 ∣ D.host.QS * D.host.q * D.host.d from
        ((show 4 ∣ 2 ^ (D.R.e + 2) from ⟨2 ^ D.R.e, by ring⟩).trans D.host.tower_dvd).mul_right _ |>.mul_right _), hc]
  · rw [← Nat.mod_mod_of_dvd (D.host.g k)
      (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from Dvd.intro_left _ rfl), hc]
    exact Nat.mod_eq_of_lt (by omega)

theorem g_ne_two (D : D7) (k : Fin 2) : D.host.g k ≠ 2 := by
  intro h
  have h4 := (g_mod D k).1
  rw [h] at h4
  norm_num at h4

theorem g_jacobi (D : D7) (k : Fin 2) : jacobiSym (-(D.host.d : ℤ)) (D.host.g k) = 1 := by
  obtain ⟨h4, hd1⟩ := g_mod D k
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hgo : Odd (D.host.g k) := Nat.odd_iff.mpr (by omega)
  have hdo : Odd D.host.d := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hgo, ZMod.χ₄_nat_one_mod_four h4, one_mul,
    jacobiSym.quadratic_reciprocity_one_mod_four' hdo h4, jacobiSym.mod_left]
  have h1 : ((D.host.g k : ℤ) % (D.host.d : ℤ)) = 1 := by
    rw [← Int.natCast_mod, hd1]
    rfl
  rw [h1, jacobiSym.one_left]

theorem splitG (D : D7) : ∀ p ∈ [D.host.g 0, D.host.g 1], SplitOK D p := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨D.host.g_prime 0, g_ne_two D 0, g_jacobi D 0⟩
  · exact ⟨D.host.g_prime 1, g_ne_two D 1, g_jacobi D 1⟩

def levelG (D : D7) {hU} : Level (hostOf D hU) :=
  levelOfPs D [D.host.g 0, D.host.g 1] (fun p hp => ⟨(splitG D p hp).1, (splitG D p hp).2.1⟩) (by simp)
    (MbProd_of D _ (splitG D)) (MbCop_of D _ (splitG D))

theorem levelG_M (D : D7) (hU) :
    (levelG D (hU := hU)).M = D.host.g 0 * D.host.g 1 ∧ (levelG D (hU := hU)).A = 1 := by
  constructor <;> simp [levelG, levelOfPs]

theorem tauEmb_sqrt (D : D7) (t : D.what₂.Tau) :
    DV.tauEmb D t D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
  have h1 : D.host.galE
      (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG)) =
      ((D.eTau t : D.R.Psi) : D.R.GG) :=
    MulEquiv.apply_symm_apply _ _
  have hmem := (D.eTau t).2
  rw [← h1] at hmem
  exact congrArg D.host.φ₀ ((D.host.galE_mem_Psi_iff _).1 hmem)

def FO (D : D7) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range D.what₂.phiO)

theorem phiO_mem_FO (D : D7) (y : D.what₂.O) : D.what₂.phiO y ∈ FO D :=
  IntermediateField.subset_adjoin ℚ _ ⟨y, rfl⟩

theorem FO_le (D : D7) : FO D ≤ (D.what₂.embLL.toRatAlgHom).fieldRange := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨y, rfl⟩
  exact AlgHom.mem_fieldRange.mpr ⟨D.what₂.OtoLL y, rfl⟩

instance FO_fin (D : D7) : FiniteDimensional ℚ (FO D) := by
  have : FiniteDimensional ℚ (D.what₂.embLL.toRatAlgHom).fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField D.what₂.embLL.toRatAlgHom).toLinearEquiv
  exact FiniteDimensional.of_injective (IntermediateField.inclusion (FO_le D)).toLinearMap
    (IntermediateField.inclusion_injective (FO_le D))

theorem phi0_mem_coeff_field (D : D7) (a : D.host.E) : D.host.φ₀ a ∈ FO D := by
  have hO : ∀ x : 𝓞 D.host.E, D.host.φ₀ (x : D.host.E) ∈ FO D := by
    intro x
    obtain ⟨y, hy⟩ := D.O_contains x
    have h1 : D.host.φ₀ (x : D.host.E) = D.what₂.phiO y := by
      rw [← D.embE_φ₀, RingHom.comp_apply, ← hy]
      rfl
    rw [h1]
    exact phiO_mem_FO D y
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) a
  rw [map_div₀]
  exact div_mem (hO x) (hO y)

theorem conj_mem_FO (D : D7) (τ : D.host.E →+* ℂ) (a : D.host.E) : τ a ∈ FO D := by
  have hG : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have key : ∀ (E' : IntermediateField ℚ ℂ) (_ : Normal ℚ E') (f : E' →ₐ[ℚ] ℂ), f.fieldRange = E' :=
    fun E' hN f => @AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ E' hN f
  let φ : D.host.E →ₐ[ℚ] ℂ := D.host.φ₀.toRatAlgHom
  let e : D.host.E ≃ₐ[ℚ] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  let f : φ.fieldRange →ₐ[ℚ] ℂ := τ.toRatAlgHom.comp e.symm.toAlgHom
  have hf : f.fieldRange = φ.fieldRange := key φ.fieldRange (by have := hG; exact Normal.of_algEquiv e) f
  have hmem : τ a ∈ φ.fieldRange := by
    rw [← hf]
    exact ⟨e a, by simp [f]⟩
  obtain ⟨b, hb⟩ := hmem
  rw [← hb]
  exact phi0_mem_coeff_field D b

theorem zeta_one : zeta 1 = 1 := by
  unfold zeta
  simp

def OZeta (D : D7) : Prop := ∃ y : D.what₂.O, D.what₂.phiO y = zeta (D.host.g 0 * D.host.g 1)

def coeffFieldOfRecord (D : D7) {hU} (hz : OZeta D) : Coeff (levelG D (hU := hU)) where
  F := FO D
  fin := inferInstance
  conj τ a := conj_mem_FO D τ a
  zeta_mem := by
    obtain ⟨y, hy⟩ := hz
    have : (levelG D (hU := hU)).M' = D.host.g 0 * D.host.g 1 := by
      simp [Level.M', levelG, levelOfPs]
    rw [this, ← hy]
    exact phiO_mem_FO D y
  le := by
    rw [KA, IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨phi0_mem_coeff_field D D.host.sqrtMinusD, ?_⟩
    have : (levelG D (hU := hU)).A = 1 := (levelG_M D hU).2
    rw [this, zeta_one]
    exact one_mem _

def OFull (D : D7) : Prop :=
  Function.Injective D.what₂.OtoLL ∧ ∀ z ∈ FO D, IsIntegral ℤ z → z ∈ Set.range D.what₂.phiO

theorem phiO_isIntegral (D : D7) (y : D.what₂.O) : IsIntegral ℤ (D.what₂.phiO y) :=
  (D.O_int y).map D.what₂.embLL.toIntAlgHom

theorem isIntegral_FO (D : D7) {x : FO D} : IsIntegral ℤ (x : ℂ) ↔ IsIntegral ℤ x :=
  isIntegral_algHom_iff (FO D).val.toRingHom.toIntAlgHom Subtype.val_injective

def toOF (D : D7) : D.what₂.O →+* 𝓞 (FO D) where
  toFun y := ⟨⟨D.what₂.phiO y, phiO_mem_FO D y⟩, (isIntegral_FO D).1 (phiO_isIntegral D y)⟩
  map_one' := RingOfIntegers.ext (Subtype.ext (map_one D.what₂.phiO))
  map_mul' x y := RingOfIntegers.ext (Subtype.ext (map_mul D.what₂.phiO x y))
  map_zero' := RingOfIntegers.ext (Subtype.ext (map_zero D.what₂.phiO))
  map_add' x y := RingOfIntegers.ext (Subtype.ext (map_add D.what₂.phiO x y))

theorem toOF_coe (D : D7) (y : D.what₂.O) : (((toOF D y : 𝓞 (FO D)) : FO D) : ℂ) = D.what₂.phiO y := rfl

theorem toOF_bij (D : D7) (hF : OFull D) : Function.Bijective (toOF D) := by
  refine ⟨fun x y hxy => hF.1 (D.what₂.embLL.injective ?_), fun z => ?_⟩
  · have hc := congrArg (fun w : 𝓞 (FO D) => ((w : FO D) : ℂ)) hxy
    exact hc
  · obtain ⟨y, hy⟩ := hF.2 ((z : FO D) : ℂ) (z : FO D).2 ((isIntegral_FO D).2 (RingOfIntegers.isIntegral_coe z))
    exact ⟨y, RingOfIntegers.ext (Subtype.ext hy)⟩

def eOf (D : D7) (hF : OFull D) : 𝓞 (FO D) ≃+* D.what₂.O :=
  (RingEquiv.ofBijective (toOF D) (toOF_bij D hF)).symm

theorem eOf_spec (D : D7) (hF : OFull D) (x : 𝓞 (FO D)) :
    D.what₂.embLL (D.what₂.OtoLL (eOf D hF x)) = ((x : FO D) : ℂ) := by
  have h1 : toOF D (eOf D hF x) = x := (RingEquiv.ofBijective (toOF D) (toOF_bij D hF)).apply_symm_apply x
  have h2 := toOF_coe D (eOf D hF x)
  rw [h1] at h2
  exact h2.symm


open Classical in
def epsW (D : D7) (j : ℕ) : ℤˣ := if ∃ hI : DatInt D j, DomFor D j (intForm (efQ D j) hI) then 1 else -1

theorem epsW_coe (D : D7) (j : ℕ) : ((epsW D j : ℤˣ) : ℤ) = sgnW D j := by
  unfold epsW sgnW
  split_ifs <;> simp

theorem isDatW_datumOf (D : D7) (hU) (j : ℕ) (hI : DatInt D j) (hL : DatLaws D j hI) :
    IsDatW D j (datumOf D (hU := hU) j hI hL) := by
  refine ⟨rfl, rfl, (latW D j).subtype, epsW D j, Submodule.injective_subtype _, Submodule.range_subtype _,
    fun x y => ?_⟩
  show ((sgnW D j * intForm (efQ D j) hI x y : ℤ) : ℚ) = _
  rw [Int.cast_mul, epsW_coe]
  congr 1
  exact intForm_cast (efQ D j) hI x y

theorem inR_one (D : D7) : InR D 1 := by
  unfold InR
  exact ⟨le_refl 1, le_trans (by norm_num) D.R.two_le_m⟩


open Classical in
def datumAtLift (D : D7) (hU) (hDat : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI) (j : ℕ) :
    Datum (hostOf D hU) :=
  if h : InR D j then datumOf D j (hDat j h).choose (hDat j h).choose_spec
  else datumOf D 1 (hDat 1 (inR_one D)).choose (hDat 1 (inR_one D)).choose_spec

theorem datumAtLift_pq_pos (D : D7) (hU) (hDat : ∀ j, InR D j → ∃ hI : DatInt D j, DatLaws D j hI) (j : ℕ) :
    1 ≤ (datumAtLift D hU hDat j).p + (datumAtLift D hU hDat j).q := by
  have := D.R.m_add_three_le_k
  unfold datumAtLift
  split_ifs with h
  · show 1 ≤ (D.R.sigW j).1 + (D.R.sigW j).2
    simp only [Ranks.sigW]
    have := h.1
    omega
  · show 1 ≤ (D.R.sigW 1).1 + (D.R.sigW 1).2
    simp only [Ranks.sigW]
    omega

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Submodule c.F (Rul Xo c) :=
  sec Xo c a n ⊓ ⨅ (σ : c.F →+* ℂ) (_ : GoodEmb c σ), (holSub (U σ).X (laU (U σ) a n)).comap (rdU (U σ))

theorem cusp_le_sec (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : cusp Xo c U a n ≤ sec Xo c a n := inf_le_left

theorem mem_cusp (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) :
    f ∈ cusp Xo c U a n ↔ f ∈ sec Xo c a n ∧ ∀ σ : c.F →+* ℂ, GoodEmb c σ → rdU (U σ) f ∈ holSub (U σ).X (laU (U σ) a n) := by
  unfold cusp
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]

def mulC (f g : Rul Xo c) : Rul Xo c := f * g

theorem mulC_mem_sec (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) {f g : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (hg : g ∈ sec Xo c a' n') : mulC Xo c f g ∈ sec Xo c (a + a') (n + n') := by
  unfold mulC
  exact sec_mul Xo c a a' n n' hf hg

def CuspMul : Prop :=
  ∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), Dom a n → Dom a' n' → f ∈ cusp Xo c U a n →
    g ∈ cusp Xo c U a' n' → mulC Xo c f g ∈ cusp Xo c U (a + a') (n + n')

set_option maxSynthPendingDepth 1 in
def CuspFD : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cusp Xo c U a n)

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure LatB (E : Type) [Field E] [NumberField E] where
  Y : Type
  [add : AddCommGroup Y]
  [free : Module.Free ℤ Y]
  [fin : Module.Finite ℤ Y]
  [md : Module (𝓞 E) Y]
  beta : Y → Y → ℝ

attribute [instance] LatB.add LatB.free LatB.fin LatB.md

section
variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O]
  {β : O →+* c.F} {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

def DatAt.toLatB (A : DatAt Y P) : LatB E := ⟨A.Ylat, A.beta⟩

end

open PointsOfFlagModel

variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ}

def N3Tower (T : Tower p Xo c) : Prop := (∀ v, N3AtPoints (T.Y v) p) ∧ ∀ n w, N3AtPoints (T.YN n w) p

variable {T : Tower p Xo c}

def lattice₂ (hN : N3Tower T) : ∀ {Z : MdlC}, Pt T Z → LatB E
  | .xm, y => (Classical.choice (hN.1 y.1 y.2.1 y.2.2)).toLatB
  | .yy, y => (Classical.choice (hN.1 y.1 y.2.1 y.2.2.1)).toLatB
  | .xn n, y => (Classical.choice (hN.2 n y.1 y.2.1 y.2.2)).toLatB

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

section Ext

variable {K L : Type} [Field K] [Field L] [Algebra K L] {M : Type} [AddCommGroup M] [Module K M]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def incl : M →ₗ[K] L ⊗[K] M := TensorProduct.mk K L M 1

end Ext

section Forms

variable {K : Type} [Field K] {LL : Type} [Field LL] [NumberField LL] [Algebra K LL]
variable {C : Type} [AddCommGroup C] [Module K C] {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {D : D7}

def rhoOf (LL : Type) [Field LL] [Algebra K LL] {G0 : Type} [Group G0] (ρC : G0 →* (C →ₗ[K] C)) :
    G0 →* (LL ⊗[K] C →ₗ[LL] LL ⊗[K] C) where
  toFun g := (ρC g).baseChange LL
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g g' := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

end Forms

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfB
noncomputable section

namespace Formalism.L2.Pj.CompSplitPfB

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem cspB_over {S : Type} [CommRing S] [Algebra c.F S] {x : Sp S ⟶ Xo.X} (hx : x ≫ Xo.s = sOf c S) :
    x ≫ Xo.s = spMap (algebraMap c.F S) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
  rw [hx, sOf, ← Spec.map_comp]
  rfl

def cspB_lift {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    Sp S ⟶ Xo.XF c :=
  pullback.lift x (spMap (algebraMap c.F S)) (cspB_over hx)

theorem cspB_lift_fst {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    cspB_lift x hx ≫ pullback.fst _ _ = x := by
  unfold cspB_lift
  exact pullback.lift_fst _ _ _

theorem cspB_lift_snd {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    cspB_lift x hx ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
  unfold cspB_lift
  exact pullback.lift_snd _ _ _

theorem cspB_lift_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (hx : x ≫ Xo.s = sOf c S) {z : Sp T ⟶ Xo.X} (hz : z ≫ Xo.s = sOf c T)
    (hzx : z = spMap φ.toRingHom ≫ x) : cspB_lift z hz = spMap φ.toRingHom ≫ cspB_lift x hx := by
  apply pullback.hom_ext
  · rw [cspB_lift_fst, Category.assoc, cspB_lift_fst, hzx]
  · rw [cspB_lift_snd, Category.assoc, cspB_lift_snd, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (AlgHom.comp_algebraMap φ).symm

theorem cspB_idem_eq_of {S : Type} [CommRing S] {a b : S} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : ∀ q : PrimeSpectrum S, a ∉ q.asIdeal ↔ b ∉ q.asIdeal) : a = b := by
  have key : ∀ x y : S, IsIdempotentElem x → IsIdempotentElem y →
      (∀ q : PrimeSpectrum S, x ∉ q.asIdeal → y ∉ q.asIdeal) → x = x * y := by
    intro x y hx hy hxy
    have hid : x * (1 - y) * (x * (1 - y)) = x * (1 - y) := by
      linear_combination (1 - y) ^ 2 * hx.eq + x * hy.eq
    have hmem : x * (1 - y) ∈ nilradical S := by
      rw [nilradical_eq_sInf, Ideal.mem_sInf]
      intro J hJ
      by_cases hxJ : x ∈ J
      · exact J.mul_mem_right _ hxJ
      · have hyJ : y ∉ J := hxy ⟨J, hJ⟩ hxJ
        apply J.mul_mem_left
        have h0 : y * (1 - y) = 0 := by linear_combination -hy.eq
        have h1 : y * (1 - y) ∈ J := by rw [h0]; exact J.zero_mem
        exact (hJ.mem_or_mem h1).resolve_left hyJ
    obtain ⟨n, hn⟩ := mem_nilradical.mp hmem
    have hpow : ∀ k : ℕ, (x * (1 - y)) ^ (k + 1) = x * (1 - y) := by
      intro k
      induction k with
      | zero => rw [zero_add, pow_one]
      | succ k ih => rw [pow_succ, ih, hid]
    have h0 : x * (1 - y) = 0 := by rw [← hpow n, pow_succ, hn, zero_mul]
    linear_combination h0
  calc a = a * b := key a b ha hb (fun q h => (hab q).mp h)
    _ = b * a := mul_comm a b
    _ = b := (key b a hb ha (fun q h => (hab q).mpr h)).symm

variable (C : Set (Xo.XF c)) (hC : IsClopen C)

def cspB_idem {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) : S :=
  ((PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).symm
    ⟨(cspB_lift x hx) ⁻¹' C, hC.preimage (cspB_lift x hx).continuous⟩).1

theorem cspB_idem_idem {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    IsIdempotentElem (cspB_idem C hC x hx) := by
  unfold cspB_idem
  exact ((PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).symm _).2

theorem cspB_idem_spec {S : Type} [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S)
    (q : PrimeSpectrum S) : cspB_idem C hC x hx ∉ q.asIdeal ↔ cspB_lift x hx q ∈ C := by
  have h1 := (PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).apply_symm_apply
    ⟨(cspB_lift x hx) ⁻¹' C, hC.preimage (cspB_lift x hx).continuous⟩
  have h2 : q ∈ ((((PrimeSpectrum.isIdempotentElemEquivClopens (R := S))
      ((PrimeSpectrum.isIdempotentElemEquivClopens (R := S)).symm
        ⟨(cspB_lift x hx) ⁻¹' C, hC.preimage (cspB_lift x hx).continuous⟩)) :
          TopologicalSpace.Clopens (PrimeSpectrum S)) : Set (PrimeSpectrum S)) ↔
      q ∈ (cspB_lift x hx) ⁻¹' C := by
    rw [h1]
    rfl
  exact h2

theorem cspB_idem_congr {S : Type} [CommRing S] [Algebra c.F S] {x x' : Sp S ⟶ Xo.X}
    (hx : x ≫ Xo.s = sOf c S) (hx' : x' ≫ Xo.s = sOf c S) (h : x' = x) :
    cspB_idem C hC x' hx' = cspB_idem C hC x hx := by
  subst h
  rfl

theorem cspB_idem_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (hx : x ≫ Xo.s = sOf c S) {z : Sp T ⟶ Xo.X} (hz : z ≫ Xo.s = sOf c T)
    (hzx : z = spMap φ.toRingHom ≫ x) : φ (cspB_idem C hC x hx) = cspB_idem C hC z hz := by
  apply cspB_idem_eq_of ((cspB_idem_idem C hC x hx).map φ) (cspB_idem_idem C hC z hz)
  intro q
  rw [cspB_idem_spec C hC z hz q, cspB_lift_map φ hx hz hzx]
  exact cspB_idem_spec C hC x hx (PrimeSpectrum.comap φ.toRingHom q)


variable (Xo c) in
def cspB_rule : Rul Xo c := fun _ y => cspB_idem C hC y.x y.x_over

theorem cspB_rule_natural : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
    (cspB_rule Xo c C hC) := by
  intro p q φ y z hyz
  first
  | exact cspB_idem_map C hC φ y.x_over z.x_over hyz.1
  | exact (cspB_idem_map C hC φ y.x_over z.x_over hyz.1).symm

theorem cspB_rule_bor (p : TRing c.F) (t : Ix Dw → (p.R)ˣ) (y y' : FrPt Xo c p.R) (hb : FrBor t y y') :
    cspB_rule Xo c C hC p y' = cspB_rule Xo c C hC p y := by
  exact cspB_idem_congr C hC y.x_over y'.x_over hb.1

theorem cspB_evR {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (hy : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    evR Xo c (cspB_rule Xo c C hC) y = cspB_idem C hC y.x y.x_over := by
  unfold evR evalAt
  rw [dite_eq_left hy]
  first
  | exact cspB_idem_map C hC _ _ _ hy.choose_spec.choose_spec.choose_spec.1
  | exact cspB_idem_map C hC _ _ _ hy.choose_spec.choose_spec.choose_spec.1.1

theorem cspB_evR_zero {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (hy : ¬ FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) (f : Rul Xo c) :
    evR Xo c f y = 0 := by
  unfold evR evalAt
  rw [dite_eq_right hy]

theorem cspB_evR_mul {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (f g : Rul Xo c) :
    evR Xo c (f * g) y = evR Xo c f y * evR Xo c g y := by
  exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g y

theorem cspB_genPt_mem (Z : Comp Xo c) : genPt Z ∈ (Z : Set (Xo.XF c)) := by
  unfold genPt
  have hcl : IsClosed (Z : Set (Xo.XF c)) := isClosed_of_mem_irreducibleComponents _ Z.2
  have hS : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
  have hg : IsGenericPoint hS.genericPoint (closure (Z : Set (Xo.XF c))) := by
    first
    | exact hS.isGenericPoint_genericPoint_closure
    | exact hS.genericPoint_spec
  rw [hcl.closure_eq] at hg
  exact hg.mem

theorem cspB_isClopen (hdisj : ∀ Z Z' : Comp Xo c, Z ≠ Z' → Disjoint (Z : Set (Xo.XF c)) Z')
    (Z : Comp Xo c) : IsClopen (Z : Set (Xo.XF c)) := by
  have := CompFin.finite_comp Xo c
  refine ⟨isClosed_of_mem_irreducibleComponents _ Z.2, ?_⟩
  have hU : (Z : Set (Xo.XF c)) = (⋃ Z' : {Z' : Comp Xo c // Z' ≠ Z}, (Z'.1 : Set (Xo.XF c)))ᶜ := by
    ext p
    constructor
    · intro hp hp'
      obtain ⟨⟨Z', hne⟩, hZ'⟩ := Set.mem_iUnion.1 hp'
      exact Set.disjoint_left.1 (hdisj Z Z' (Ne.symm hne)) hp hZ'
    · intro hp
      have hall : p ∈ ⋃₀ irreducibleComponents (Xo.XF c) := by
        rw [sUnion_irreducibleComponents]; trivial
      obtain ⟨W, hW, hpW⟩ := Set.mem_sUnion.1 hall
      by_contra hpZ
      refine hp (Set.mem_iUnion.2 ⟨⟨⟨W, hW⟩, fun hWZ => hpZ ?_⟩, hpW⟩)
      rw [← hWZ]
      exact hpW
  rw [hU]
  exact (isClosed_iUnion_of_finite fun Z' : {Z' : Comp Xo c // Z' ≠ Z} =>
    isClosed_of_mem_irreducibleComponents _ Z'.1.2).isOpen_compl



end Formalism.L2.Pj.CompSplitPfB
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.VAddIntNonneg
noncomputable section

namespace Formalism.L2.Pj

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

section One

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]

structure IsVal (la : HeightOneSpectrum (𝓞 K)) (v : R → EReal) : Prop where
  zero : v 0 = ⊤
  ne_bot : ∀ r, v r ≠ ⊥
  add : ∀ r s, min (v r) (v s) ≤ v (r + s)
  smul : ∀ (a : K) r, a ≠ 0 → v (a • r) = (((vAdd la a : ℤ) : ℝ) : EReal) + v r
  mul : ∀ r s, v (r * s) = v r + v s

structure IsNormOn (C : Submodule K R) (σ : K →+* ℂ) (N : R → ℝ) : Prop where
  nonneg : ∀ f ∈ C, 0 ≤ N f
  defin : ∀ f ∈ C, N f = 0 → f = 0
  smul : ∀ (a : K), ∀ f ∈ C, N (a • f) = ‖σ a‖ * N f
  add : ∀ f ∈ C, ∀ g ∈ C, N (f + g) ≤ N f + N g

theorem vAdd_int_nonneg (la : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : (a : K) ≠ 0) : 0 ≤ vAdd la (a : K) := by
  unfold vAdd
  have h1 := la.valuation_le_one (K := K) a
  have h2 : (la.valuation K) (a : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr ha
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  omega

variable [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R]

def latOf (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
    (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v) : Submodule (𝓞 K) C where
  carrier := {F | ∀ la, ∀ v ∈ Vs la, 0 ≤ v F}
  zero_mem' := fun la v hv => by
    change 0 ≤ v 0
    rw [(hV la v hv).zero]; exact le_top
  add_mem' := fun {F F'} hF hF' la v hv => (le_min (hF la v hv) (hF' la v hv)).trans ((hV la v hv).add _ _)
  smul_mem' := fun a F hF la v hv => by
    have h1 : ((a • F : C) : R) = (a : K) • (F : R) := (algebraMap_smul K a (F : R)).symm
    rw [h1]
    by_cases ha : (a : K) = 0
    · rw [ha, zero_smul, (hV la v hv).zero]; exact le_top
    · rw [(hV la v hv).smul _ _ ha]
      refine add_nonneg ?_ (hF la v hv)
      exact_mod_cast vAdd_int_nonneg la ha

end One

variable {D : D7}

abbrev Deg (D : D7) (j : ℕ) : Type :=
  (D.what₂.Tau → Fin (D.R.sigW j).1 → ℕ) × (D.what₂.Tau → Fin (D.R.sigW j).2 → ℕ) × ℕ

def deg {j : ℕ} (w : WeightFamilies.Wt D j) : Deg D j := (w.aP, w.aM, w.n)

theorem deg_inj {j : ℕ} : Function.Injective (deg (D := D) (j := j)) := by
  rintro ⟨a1, b1, _, _, n1, _⟩ ⟨a2, b2, _, _, n2, _⟩ h
  simp only [deg, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem deg_wadd {j : ℕ} (w w' : WeightFamilies.Wt D j) : deg (WeightAlgebra.wadd w w') = deg w + deg w' := rfl

section Rec

variable {K : Type} [Field K] [NumberField K] (eO : 𝓞 K ≃+* D.what₂.O)
  {R : ℕ → Type} [∀ j, CommRing (R j)] [∀ j, Algebra K (R j)] [∀ j, Algebra (𝓞 K) (R j)]
  [∀ j, IsScalarTower (𝓞 K) K (R j)] (C : ∀ j, WeightFamilies.Wt D j → Submodule K (R j))

def cutR (j : ℕ) (w : WeightFamilies.Wt D j) : Submodule K (R j) := C j w ⊓ ⨅ _ : ¬ InR D j, ⊥

omit [NumberField K] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)] in
theorem cutR_le (j : ℕ) (w : WeightFamilies.Wt D j) : cutR C j w ≤ C j w := inf_le_left

omit [NumberField K] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)] in
theorem cutR_eq {j : ℕ} (h : InR D j) (w : WeightFamilies.Wt D j) : cutR C j w = C j w := by simp [cutR, h]

omit [NumberField K] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)] in
theorem cutR_out {j : ℕ} (h : ¬ InR D j) (w : WeightFamilies.Wt D j) : cutR C j w = ⊥ := by simp [cutR, h]

omit [NumberField K] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)] in
theorem cutR_zero {j : ℕ} (h : ¬ InR D j) {w : WeightFamilies.Wt D j} (F : cutR C j w) : F = 0 := by
  apply Subtype.ext
  have := F.2
  simpa [cutR_out C h w] using this


open Classical in
def cutN (N : ∀ j, WeightFamilies.Wt D j → (K →+* ℂ) → R j → ℝ) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : K →+* ℂ)
    (F : cutR C j w) : ℝ := if InR D j then N j w σ F else 0

section Norm

variable {C} {N : ∀ j, WeightFamilies.Wt D j → (K →+* ℂ) → R j → ℝ}
  (hN : ∀ j, InR D j → ∀ w σ, IsNormOn (C j w) σ (N j w σ))
include hN

omit [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)]

theorem cutN_nonneg (j w σ) (F : cutR C j w) : 0 ≤ cutN C N j w σ F := by
  unfold cutN; split_ifs with h
  · exact (hN j h w σ).nonneg _ (cutR_le C j w F.2)
  · exact le_rfl

theorem cutN_smul (j w σ) (a : K) (F : cutR C j w) : cutN C N j w σ (a • F) = ‖σ a‖ * cutN C N j w σ F := by
  unfold cutN; split_ifs with h
  · exact (hN j h w σ).smul a _ (cutR_le C j w F.2)
  · simp

theorem cutN_eq_zero (j w σ) (F : cutR C j w) : cutN C N j w σ F = 0 ↔ F = 0 := by
  constructor
  · intro h0
    by_cases h : InR D j
    · unfold cutN at h0; rw [if_pos h] at h0
      exact Subtype.ext ((hN j h w σ).defin _ (cutR_le C j w F.2) h0)
    · exact cutR_zero C h F
  · rintro rfl
    have := cutN_smul hN j w σ 0 0
    simpa using this

theorem cutN_add (j w σ) (F G : cutR C j w) : cutN C N j w σ (F + G) ≤ cutN C N j w σ F + cutN C N j w σ G := by
  unfold cutN; split_ifs with h
  · exact (hN j h w σ).add _ (cutR_le C j w F.2) _ (cutR_le C j w G.2)
  · simp

end Norm

variable (hfd : ∀ j, InR D j → ∀ w, FiniteDimensional K (C j w))
  (Vs : ∀ j, HeightOneSpectrum (𝓞 K) → Set (R j → EReal)) (hV : ∀ j la, ∀ v ∈ Vs j la, IsVal la v)
  (Ns Nl : ∀ j, WeightFamilies.Wt D j → (K →+* ℂ) → R j → ℝ)
  (hNs : ∀ j, InR D j → ∀ w σ, IsNormOn (C j w) σ (Ns j w σ))
  (hNl : ∀ j, InR D j → ∀ w σ, IsNormOn (C j w) σ (Nl j w σ))
  (hle : ∀ j, InR D j → ∀ w σ, ∀ f ∈ C j w, Nl j w σ f ≤ Ns j w σ f)
  (Cu : ℕ → Type) (Xc : ∀ j, Cu j → Submodule (𝓞 D.host.E) (Fin (WeightFamilies.rho D j) → D.host.E))
  (hXc : ∀ j c, Submodule.IsLattice D.host.E (Xc j c))
  (FJ : ∀ j (c : Cu j), WeightFamilies.ExpoSet D (Xc j c) → WeightFamilies.Wt D j → Type)
  [∀ j c χ w, AddCommGroup (FJ j c χ w)] [∀ j c χ w, Module K (FJ j c χ w)]
  (sg : ∀ j (c : Cu j) (χ : WeightFamilies.ExpoSet D (Xc j c)) (w : WeightFamilies.Wt D j), C j w →ₗ[K] FJ j c χ w)

@[reducible] def mkB : WeightFamilies.Prov D where
  KO := K
  eO := eO
  Cusp j w := cutR C j w
  fdC j w := by
    by_cases h : InR D j
    · rw [cutR_eq C h]; exact hfd j h w
    · rw [cutR_out C h]; infer_instance
  Mlat j w := latOf (cutR C j w) (Vs j) (hV j)
  supN := cutN C Ns
  supN_nonneg := cutN_nonneg hNs
  supN_eq_zero := cutN_eq_zero hNs
  supN_smul := cutN_smul hNs
  supN_add := cutN_add hNs
  l2NormAlt := cutN C Nl
  l2Norm_nonneg_bis := cutN_nonneg hNl
  l2Norm_eq_zero_iff := cutN_eq_zero hNl
  l2Norm_smul_alt := cutN_smul hNl
  l2Norm_add_le' := cutN_add hNl
  l2Norm_le_supNorm_alt j w σ F := by
    unfold cutN; split_ifs with h
    · exact hle j h w σ _ (cutR_le C j w F.2)
    · exact le_rfl
  Cu := Cu
  Xc := Xc
  Xc_lat := hXc
  FJt := FJ
  sg j c χ w := (sg j c χ w).comp (Submodule.inclusion (cutR_le C j w))

def spanIn (j : ℕ) (w : WeightFamilies.Wt D j) (s : Set (R j)) : Submodule (𝓞 K) (cutR C j w) :=
  (Submodule.span (𝓞 K) s).comap ((cutR C j w).subtype.restrictScalars (𝓞 K))

def mkX (P : ModuliIntegralCharts.Prov D) (j : ℕ) (hj : InR D j)
    (hmul : ∀ w w', ∀ f ∈ C j w, ∀ g ∈ C j w', f * g ∈ C j (WeightAlgebra.wadd w w'))
    (dat : P.Dat) (hrk : j < D.R.m → P.rk dat = D.R.r) (hjj : j < D.R.m → P.jj dat = (D.R.sigW j).1)
    (Pt : HeightOneSpectrum (𝓞 K) → Type)
    (p66 : ∀ la, Pt la → (P.loc dat (WeightAlgebra.resCh la)).Pt (P.loc dat (WeightAlgebra.resCh la)).YY)
    (pv : ∀ la, Pt la → R j → EReal) (hpv : ∀ la y, IsVal la (pv la y))
    (hlat : ∀ w, ∀ f ∈ C j w, (∀ la, ∀ v ∈ Vs j la, 0 ≤ v f) ↔ ∀ la y, 0 ≤ pv la y f)
    (th sh : WeightFamilies.Wt D j → Set (R j)) :
    WeightAlgebra.PJ D (mkB eO C hfd Vs hV Ns Nl hNs hNl hle Cu Xc hXc FJ sg) P j where
  Forms := AddMonoidAlgebra (R j) (Deg D j)
  inc w := incG deg (cutR C j) w
  inc_inj w := incG_inj deg (cutR C j) w
  inc_indep := incG_indep deg (cutR C j) deg_inj
  inc_mul w w' F G :=
    ⟨⟨_, by rw [cutR_eq C hj]; exact hmul w w' _ (cutR_le C j w F.2) _ (cutR_le C j w' G.2)⟩,
      incG_mul deg (cutR C j) (deg_wadd w w') F G _⟩
  dat := dat
  dat_rk := hrk
  dat_jj := hjj
  Pt := Pt
  pt66 := p66
  vAt la y := vG (pv la y)
  vAt_zero la y := vG_zero (hpv la y).zero
  vAt_ne_bot la y := vG_ne_bot (hpv la y).zero (hpv la y).ne_bot
  vAt_add la y := vG_add (hpv la y).add
  vAt_smul la y a F ha := vG_smul (fun r => (hpv la y).smul a r ha) F
  vAt_mul la y := vG_mul deg (cutR C j) (hpv la y).zero (hpv la y).mul
  Mlat_eq w F := by
    refine (hlat w _ (cutR_le C j w F.2)).trans (forall_congr' fun la => forall_congr' fun y => ?_)
    rw [vG_incG deg (cutR C j) (hpv la y).zero]
  thAll w := spanIn C j w (th w)
  shortTh w := spanIn C j w (sh w)

end Rec

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.IntFrExtM
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section ValCrit

theorem valCrit_proj {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (hf : IsProjOver f)
    (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (b : R →+* V) (y : Sp K ⟶ X) (hy : y ≫ f = spMap (algebraMap V K) ≫ spMap b) :
    ∃ y' : Sp V ⟶ X, y' ≫ f = spMap b ∧ spMap (algebraMap V K) ≫ y' = y := by
  obtain ⟨N, i, hi, hif⟩ := hf
  haveI : IsClosedImmersion i := hi
  haveI : IsProper (PSpace.str R N) := isProper_str R N
  have hU : UniversallyClosed (i ≫ PSpace.str R N) := inferInstance
  rw [hif] at hU
  have h2 : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f := by
    rw [← UniversallyClosed.eq_valuativeCriterion]
    exact hU
  have hE : ValuativeCriterion.Existence f := h2.1
  haveI : ValuationRing V := by
    first
      | exact inferInstance
      | exact ValuationRing.of_isDiscreteValuationRing V
  let S : ValuativeCommSq f := ⟨V, K, y, spMap b, ⟨hy⟩⟩
  obtain ⟨l⟩ := (hE S).exists_lift
  exact ⟨l.l, l.fac_right, l.fac_left⟩

end ValCrit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Open

variable {D : Datum H} {l : Level H}

end Open

section Proofs

variable {D : Datum H} {l : Level H}

theorem exists_family {D : Datum H} {l : Level H} (X0 : Moduli D l) (hN : ∀ l' : Level H, Nonempty (Moduli D l')) :
    ∃ XoF : ∀ l' : Level H, Moduli D l', XoF l = X0 := by
  classical
  refine ⟨fun l' => if h : l' = l then cast (congrArg (Moduli D) h.symm) X0 else (hN l').some, ?_⟩
  first
    | (beta_reduce
       rw [dite_eq_left rfl]
       rfl)
    | simp

end Proofs

section Place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Place

section Level

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Level

section Definite

open Formalism.BasicNotions Formalism.MainNotions

end Definite

end Formalism.L2.Pj
end
end
