module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireTheta
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentKillsInvariantsNoJumpZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2TwistSetup
public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.InertPlacesGoodSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarBoundOfMultiplicity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW
open scoped ComplexConjugate

namespace GlobalTheory.RSnmUnf

def padNat {m n : ℕ} (l : Fin m → ℕ) : Fin n → ℕ := fun i => if h : (i : ℕ) < m then l ⟨i, h⟩ else 0

theorem padNat_zero {m n : ℕ} : padNat (m := m) (n := n) 0 = 0 := by
  funext i; simp only [padNat, Pi.zero_apply]; split_ifs <;> rfl

open Classical in
def rsTermNM (q : ℕ) {n m : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (x : ℝ) (v : Fin m → ℤ) : ℂ :=
  if (∀ i, 0 ≤ v i) ∧ Antitone v then
    schurAt (padNat fun i => (v i).toNat) α * conj (schurAt (fun i => (v i).toNat) β) *
      ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, (v i).toNat)
  else 0

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def uIntNM {m n : ℕ} (hmn : m + 1 ≤ n) (F : (Fin (m + 1) → Ad E) → ℂ) (φ : GA E n → ℂ) (φ' : GA E (m + 1) → ℂ)
    (x : ℝ) (h : GA E (m + 1)) : ℂ :=
  whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL hmn h) * conj (whit φ' h) * GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h) *
    ((GlobalTheory.RSnm.detAbs h : ℝ) : ℂ) ^ ((x : ℂ) - ((n : ℂ) - ((m + 1 : ℕ) : ℂ)) / 2)

end GlobalTheory.RSnmUnf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmH0Setup
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.PowerSmulVanishing

theorem pow_smul_eq_zero_of_le {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (p : O) {a b : ℕ}
    (h : a ≤ b) {x : M} (hx : p ^ a • x = 0) : p ^ b • x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, mul_comm, ← smul_smul, hx, smul_zero]

end GlobalTheory.NLink.PowerSmulVanishing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientSubContinuitySetup
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section
namespace GlobalTheory.NLink.AmbSub

variable {D : D7}

theorem WpO_cont (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hρ : Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :
    Continuous fun g => WpO D.nd i ρ π g := by
  have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [map_inv]
      rfl
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  exact h1.smul hρ

end GlobalTheory.NLink.AmbSub
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftColumnRowSetup
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.LiftExpSplit

open Module

variable {D : D7}

theorem lift_of_window (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Formalism.MainNotions.TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hC : C.IsGood)
    (hur : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i)) (hl : D.nd.l i ≠ 2) {ι : Type} {k : ℕ}
    (Ms : ι → Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥C.LL.1)
    (hc : ∀ x v, Continuous fun g => (Ms x g).mulVec v)
    (hF : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL)) (M h : ℕ)
    (hcr : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Ms x)))
    (hS : ∀ x τ, JumpsInV (Br.PD D.loc D.nbr i w hw) (matRep (Ms x)) τ (Set.Icc (-(M : ℤ)) h))
    (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {CA CB CK : ℝ} (hCA : 0 ≤ CA)
    (h54 : Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK) (e' : ℕ)
    (he : CA * (1 + ((M + h : ℕ) : ℝ) / (D.nd.l i : ℝ) +
      (1 + Real.logb (D.nd.l i) (((M + h : ℕ) : ℝ) + 1))) ≤ (e' : ℝ)) :
    LiftAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) (fun x : ι => ⇑(Ms x)) e' := by
  have hg : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl (le_trans (le_inf le_rfl hur) le_sup_left)
  have hA := caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hg hur hl
  intro V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 L1 hc1 hs1 V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 L2 hc2 hs2 F hF'
  let T₁ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := V1, ρ := ρ1, cont := hc1, L := L1 }
  let T₂ : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
    { V := V2, ρ := ρ2, cont := hc2, L := L2 }
  obtain ⟨hcr1, hj1⟩ := subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF
    (S := fun _ => Set.Icc (-(M : ℤ)) h) hcr hS T₁ hs1
  obtain ⟨hcr2, -⟩ := subquot_crys (PD := Br.PD D.loc D.nbr i w hw) Ms hc hF
    (S := fun _ => Set.Icc (-(M : ℤ)) h) hcr hS T₂ hs2
  have hJ : Formalism.MainNotions.LiftingTheory.JumpsLet ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hg) T₁
      (fun _ => M) (fun _ => h) := fun _ τ _ => hj1 τ
  have h1 := h54.1 (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg hA T₁ T₂ F (fun _ => M) (fun _ => h)
    ⟨hcr1, hcr2, hF'⟩ hJ
  have h2 := (h54.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hg T₁ (fun _ => M) (fun _ => h) hcr1 hJ).1 hA
  refine LiftF_mono _ F ?_ h1
  have hp : (((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p : ℝ) = (D.nd.l i : ℝ) := by
    rw [(D.loc (D.nd.l i)).PD_p]
  have hl1 : (1 : ℝ) < (D.nd.l i : ℝ) := by exact_mod_cast (D.nd.lPrime i).out.one_lt
  have hH : ((Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M)
      (fun _ => h) : ℕ) : ℝ) ≤ ((M + h : ℕ) : ℝ) := by exact_mod_cast Hmax_const_le _ M h
  rw [hp] at h2
  have h3 : CA * (1 + ((Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M)
      (fun _ => h) : ℕ) : ℝ) / (D.nd.l i : ℝ) + (1 + Real.logb (D.nd.l i)
        (((Formalism.MainNotions.LiftingTheory.Hmax (Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) (fun _ => M)
      (fun _ => h) : ℕ) : ℝ) + 1))) ≤ CA * (1 + ((M + h : ℕ) : ℝ) / (D.nd.l i : ℝ) +
      (1 + Real.logb (D.nd.l i) (((M + h : ℕ) : ℝ) + 1))) := by
    apply mul_le_mul_of_nonneg_left _ hCA
    have ha := div_le_div_of_nonneg_right hH (le_of_lt (lt_trans zero_lt_one hl1))
    have hb := Real.logb_le_logb_of_le hl1 (by positivity) (add_le_add_left hH 1)
    linarith
  exact_mod_cast (h2.trans (h3.trans he))

theorem shape_le_eA (L : SizeData₂ D) (CA : ℝ) (l : ℕ) :
    CA * (1 + ((Formalism.MainNotions.N.hN L + Formalism.MainNotions.N.hN L : ℕ) : ℝ) / (l : ℝ) +
      (1 + Real.logb l (((Formalism.MainNotions.N.hN L + Formalism.MainNotions.N.hN L : ℕ) : ℝ) + 1))) ≤ (eA L CA l : ℝ) := by
  unfold eA
  exact Nat.le_ceil _

theorem mem_window (L : SizeData₂ D) (a : ℤ) (ha : |(a : ℝ)| ≤ Formalism.MainNotions.TwistedPlaces.hB L) :
    a ∈ Set.Icc (-(Formalism.MainNotions.N.hN L : ℤ)) (Formalism.MainNotions.N.hN L) := by
  have h1 : a.natAbs ≤ Formalism.MainNotions.N.hN L := by
    unfold Formalism.MainNotions.N.hN
    apply Nat.le_floor
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact ha
  constructor <;> omega

end GlobalTheory.LiftExpSplit

end

namespace GlobalTheory.LiftExpSplit

end GlobalTheory.LiftExpSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass
  GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct

namespace GlobalTheory.UseLoc.Cases

section Gen

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def intO : Submodule O LL := LinearMap.range (Algebra.linearMap O LL)

def Xq (lam : O) (a : ℕ) : Submodule O (LL ⧸ intO (O := O) LL) :=
  LinearMap.ker (lam ^ a • (LinearMap.id : (LL ⧸ intO (O := O) LL) →ₗ[O] (LL ⧸ intO (O := O) LL)))

variable {LL}
variable {V V' : Type} [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module LL V'] [Module O V']
  [IsScalarTower O LL V']

def scalQ (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') (t : ↥T) :
    (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' :=
  (intO (O := O) LL).liftQ (T'.mkQ ∘ₗ (LinearMap.id : LL →ₗ[O] LL).smulRight (j t)) (by
    rintro _ ⟨c, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Algebra.linearMap_apply, algebraMap_smul]
    exact T'.smul_mem c (hj t t.2))

def scalB (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') :
    ↥T →ₗ[O] (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' where
  toFun := scalQ T T' j hj
  map_add' t u := by
    apply Submodule.linearMap_qext
    ext s
    simp [scalQ, smul_add]
  map_smul' c t := by
    apply Submodule.linearMap_qext
    ext s
    simp [scalQ, smul_comm s c]

def iotaG (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T') :
    ↥T ⊗[O] (LL ⧸ intO (O := O) LL) →ₗ[O] V' ⧸ T' :=
  TensorProduct.lift (scalB T T' j hj)

theorem iotaG_tmul (T : Submodule O V) (T' : Submodule O V') (j : V →ₗ[O] V') (hj : ∀ v ∈ T, j v ∈ T')
    (t : ↥T) (s : LL) :
    iotaG T T' j hj (t ⊗ₜ Submodule.Quotient.mk s) = Submodule.Quotient.mk (s • j t) := rfl

end Gen

section Conc

variable {O : Type} (LL : Type) [CommRing O] [Field LL] [Algebra O LL]

def iotaW (lam : O) (a k : ℕ) :
    ↥(stdG O LL k) ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin k → LL) ⧸ stdG O LL k :=
  iotaG (stdG O LL k) (stdG O LL k) LinearMap.id (fun _ h => h) ∘ₗ LinearMap.lTensor _ (Xq LL lam a).subtype

def constOne : LL →ₗ[O] (Fin 1 → LL) := LinearMap.pi fun _ => LinearMap.id

theorem constOne_mem : ∀ v ∈ intO (O := O) LL, constOne (O := O) LL v ∈ stdG O LL 1 := by
  rintro _ ⟨c, rfl⟩
  simp only [constOne, stdG]
  refine ⟨fun _ => c, ?_⟩
  ext i
  simp

def iotaC (lam : O) (a : ℕ) :
    ↥(intO (O := O) LL) ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin 1 → LL) ⧸ stdG O LL 1 :=
  iotaG (intO LL) (stdG O LL 1) (constOne LL) (constOne_mem LL) ∘ₗ LinearMap.lTensor _ (Xq LL lam a).subtype

variable {LL}

def latOne (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) :
    Lattice (O := O) (Formalism.WeaklyAdmissibleFiltrations.charRep (tableLineDegreeTwo.charL (LL := LL) ψ)) where
  T := intO LL
  stable g x hx := by
    obtain ⟨c, rfl⟩ := hx
    refine ⟨((ψ g : Oˣ) : O) * c, ?_⟩
    simp [Formalism.WeaklyAdmissibleFiltrations.charRep, tableLineDegreeTwo.charL, Algebra.linearMap_apply, Algebra.smul_def]
  fg := by
    rw [intO, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hinj)
  span := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL ((intO (O := O) LL : Set LL)) :=
      Submodule.subset_span ⟨1, map_one (algebraMap O LL)⟩
    simpa using Submodule.smul_mem _ x h1

end Conc

end GlobalTheory.UseLoc.Cases

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LongOrbitsRowColengthInertLocalisation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LongOrbitsRowColengthInertLocalisation
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.RowBLong

theorem logb_le_self {l : ℕ} (hl : 11 ≤ l) {y : ℝ} (hy : 0 < y) : Real.logb l y ≤ y := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hlog : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have h1 := Real.log_le_sub_one_of_pos hy
  unfold Real.logb
  rcases le_or_gt 0 (Real.log y) with h | h
  · calc Real.log y / Real.log l ≤ Real.log y := div_le_self h hlog
      _ ≤ y := by linarith
  · have : Real.log y / Real.log l < 0 := div_neg_of_neg_of_pos h (by linarith)
    linarith

theorem logb_le_split {l : ℕ} (hl : 11 ≤ l) (j : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    Real.logb l H ≤ H / ((l : ℝ) - 1) ^ (j + 1) + ((j : ℝ) + 1) := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hm : 0 < ((l : ℝ) - 1) ^ (j + 1) := pow_pos (by linarith) _
  have hl1 : (1 : ℝ) < l := by linarith
  rcases hH.eq_or_lt with h0 | hpos
  · rw [← h0]; simp; positivity
  have hsplit : Real.logb l H = Real.logb l (H / ((l : ℝ) - 1) ^ (j + 1)) + Real.logb l (((l : ℝ) - 1) ^ (j + 1)) := by
    rw [Real.logb_div hpos.ne' hm.ne']; ring
  have h2 : Real.logb l (((l : ℝ) - 1) ^ (j + 1)) ≤ (j : ℝ) + 1 := by
    rw [Real.logb_pow]
    have h3 : Real.logb l ((l : ℝ) - 1) ≤ 1 := by
      have := Real.logb_le_logb_of_le hl1 (by linarith : (0:ℝ) < l - 1) (by linarith : (l:ℝ) - 1 ≤ l)
      rwa [Real.logb_self_eq_one hl1] at this
    push_cast
    have : (0:ℝ) ≤ (j:ℝ) + 1 := by positivity
    nlinarith
  rw [hsplit]
  have := logb_le_self hl (div_pos hpos hm)
  linarith

theorem bracket_le {l : ℕ} (hl : 11 ≤ l) (j : ℕ) {H G0 hB GP large₂ : ℝ} (hH0 : 0 ≤ H) (hG0 : 0 ≤ G0)
    (hGP : G0 ≤ GP) (hB0 : 0 ≤ hB) (hLg : 0 ≤ large₂) (hH : H ≤ hB ∨ H ≤ G0) :
    H / ((l : ℝ) - 1) ^ (j + 1) + (G0 + 1) * ((j : ℝ) + 1) + Real.logb l H ≤
      3 * (hB / ((l : ℝ) - 1) ^ (j + 1) + (GP + 1) * ((j : ℝ) + 1) + large₂) := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hm1 : 1 ≤ ((l : ℝ) - 1) ^ (j + 1) := one_le_pow₀ (by linarith)
  have hm : 0 < ((l : ℝ) - 1) ^ (j + 1) := by linarith
  have hlog := logb_le_split hl j hH0
  have hj : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  have hBm : 0 ≤ hB / ((l : ℝ) - 1) ^ (j + 1) := div_nonneg hB0 hm.le
  have hGj : (G0 + 1) * ((j : ℝ) + 1) ≤ (GP + 1) * ((j : ℝ) + 1) := by nlinarith
  have hj1 : (j : ℝ) + 1 ≤ (GP + 1) * ((j : ℝ) + 1) := by nlinarith
  rcases hH with h | h
  · have : H / ((l : ℝ) - 1) ^ (j + 1) ≤ hB / ((l : ℝ) - 1) ^ (j + 1) := div_le_div_of_nonneg_right h hm.le
    nlinarith
  · have h1 : H / ((l : ℝ) - 1) ^ (j + 1) ≤ H := div_le_self hH0 hm1
    have h2 : 2 * G0 + (j : ℝ) + 1 ≤ 2 * (G0 + 1) * ((j : ℝ) + 1) := by nlinarith
    nlinarith

end GlobalTheory.RowBLong

namespace GlobalTheory.RowBLong

theorem nLet_eq_nLam {D : D7} {L : SizeData₂ D} {HW : HWOf D.loc} {i : D.nd.Loc}
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
    {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    {Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw} {hG : Good (D.nbr i w hw).Kw 1 Cx.LL} {Wd : WordDat (nLet i w hw)}
    (hb : WordBase L HW i r ρ π w hw Cx hG Wd) : nLet i w hw = Formalism.MainNotions.TwistedPlaces.nLam D w := by
  have hK : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.mpr hb.unram
  have h1 : nLet i w hw = Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 :=
    (IntermediateField.equivOfEq hK).toLinearEquiv.finrank_eq
  rw [h1]
  exact hb.deg

end GlobalTheory.RowBLong

namespace GlobalTheory.RowBLong

attribute [local instance] Formalism.MainNotions.N.nLet_neZero

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), WachCoordinates.Conclusion2 D C₂ → 1 ≤ C₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → LocalRepresentationBoundCondition L HW C₂ i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowB L C₂ (D.nd.l i)) := by
  intro D L P HW C₂ i r ρ π dc hA hC _ h11 hJ
  intro w hw _ C hCg
  obtain ⟨hur, hWd⟩ := hJ w hw
  have hg : Good (D.nbr i w hw).Kw 1 C.LL := hCg.good_one (by omega) (le_trans (le_inf le_rfl hur) le_sup_left)
  obtain ⟨Wd, hb, hB⟩ := hWd C hg
  have hrow := GlobalTheory.Survey.InertPlacesGoodSet.rowL_of_wordsB hA h11 hb hB
  refine GlobalTheory.T.rowBound_at_place_of_latticeColengthBound D i r ρ π w hw C _ _ hrow ?_
  have hn : ((nLet i w hw : ℕ) : ℝ) = (Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) := by
    exact_mod_cast nLet_eq_nLam hb
  have hl' : (11 : ℝ) ≤ D.nd.l i := by exact_mod_cast h11
  have hbr := bracket_le h11 (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i))
    (H := (WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) (G0 := ((Wd.w + Wd.S + Wd.η : ℕ) : ℝ))
    (hB := Formalism.MainNotions.TwistedPlaces.hB L) (GP := Formalism.MainNotions.TwistedPlaces.GP L) (large₂ := Formalism.MainNotions.TwistedPlaces.large₂ L)
    (by positivity) (by positivity)
    (by
      unfold Formalism.MainNotions.TwistedPlaces.GP
      have := hb.w_le; have := hb.S_le; have := hb.η_le
      push_cast; linarith)
    (by linarith [Formalism.MainNotions.TwistedPlaces.one_le_hB L]) (Formalism.MainNotions.TwistedPlaces.Lg_nonneg L)
    (by
      unfold WachCoordinates.hCor
      split_ifs
      · left; have := hb.h_le; push_cast; linarith
      · right; exact le_rfl)
  have key : C₂ * (((nLet i w hw : ℕ) : ℝ) + 1) * D.R.r *
      ((WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ) / ((D.nd.l i : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) + 1) +
        (((Wd.w + Wd.S + Wd.η : ℕ) : ℝ) + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) +
        Real.logb (D.nd.l i) (WachCoordinates.hCor Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) ≤
      3 * C₂ * coreB L (D.nd.l i) w := by
    unfold coreB
    rw [hn]
    have h0 : 0 ≤ C₂ * ((Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) + 1) * D.R.r := by
      have : (0:ℝ) ≤ C₂ := by linarith
      positivity
    calc _ ≤ C₂ * ((Formalism.MainNotions.TwistedPlaces.nLam D w : ℝ) + 1) * D.R.r *
          (3 * (Formalism.MainNotions.TwistedPlaces.hB L / ((D.nd.l i : ℝ) - 1) ^ (Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) + 1) +
            (Formalism.MainNotions.TwistedPlaces.GP L + 1) * ((Formalism.MainNotions.TwistedPlaces.jA L (D.nd.l i) : ℝ) + 1) + Formalism.MainNotions.TwistedPlaces.large₂ L)) :=
          mul_le_mul_of_nonneg_left hbr h0
      _ = _ := by ring
  unfold lenRowB ratIn
  split_ifs with hlt
  · have := (exists_rat_btwn hlt).choose_spec
    linarith [this.1]
  · push_neg at hlt
    have hc0 : coreB L (D.nd.l i) w ≤ 0 := by linarith
    have : 3 * C₂ * coreB L (D.nd.l i) w ≤ 0 := by
      have : (0:ℝ) ≤ 3 * C₂ := by linarith
      nlinarith
    simp only [Rat.cast_zero]
    linarith

end GlobalTheory.RowBLong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LongOrbitsRowColengthInertLocalisationStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.longOrbits_rowColength_inertLocalisation : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), WachCoordinates.Conclusion2 D C₂ → 1 ≤ C₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → LocalRepresentationBoundCondition L HW C₂ i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowB L C₂ (D.nd.l i)) := by
  first | exact @GlobalTheory.RowBLong.main | exact GlobalTheory.RowBLong.main | (intros; apply GlobalTheory.RowBLong.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelDatumReferenceTupleSmallField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelDatumReferenceTupleSmallField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.RefDatumLev

variable {D : D7}

theorem q_base_empty {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) :
    R.Q A.μ0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h := (hL.Q_ram A.μ0 PP).2 (Or.inl hPP)
  rw [hL.xi_base] at h
  exact h fun x _ => rfl

open Classical in
theorem isIdemSum_conjPl {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) :
    IsIdemSum (cA D e) (P.image Formalism.L2.DIV.conjPl) := by
  classical
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  refine ⟨⟨fun Q => cA D (es (Formalism.L2.DIV.conjPl Q)), ?_, ?_⟩, ?_⟩
  · intro Q hQ
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ
    show Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.DIV.conjPl (Formalism.L2.DIV.conjPl PP)))) (Formalism.L2.DIV.conjPl PP)
    rw [Formalism.L2.DIV.conjPl_conjPl]
    exact GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun x => Iff.rfl
  · rw [Finset.sum_image (fun a _ b _ (hab : Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b) => by
      rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b])]
    simp only [Formalism.L2.DIV.conjPl_conjPl]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he, map_sum]
  · rw [GlobalTheory.MovedIdem.cA_cA, mul_comm]; exact hc

theorem frMapAdj_add' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
  unfold frMapAdj
  rw [Matrix.map_add (cA D) (fun a b => (cA D).map_add a b), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.map_add (toEAf D) (fun a b => (toEAf D).map_add a b), Matrix.mul_add, Matrix.add_mul]

theorem frMapAdj_nsmul' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (k : ℕ) (x : WO S T) :
    frMapAdj S T βS βT (k • x) = k • frMapAdj S T βS βT x := by
  induction k with
  | zero =>
    rw [zero_smul, zero_smul]
    unfold frMapAdj
    rw [Matrix.map_zero (cA D) (cA D).map_zero, Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.map_zero (toEAf D) (toEAf D).map_zero, Matrix.mul_zero, Matrix.zero_mul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, frMapAdj_add', ih]

theorem natM_mem_Mb (T : CoreJ D) : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb := by
  have hle : T.Q.l.Mb * T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ T.Q.l.Mb := Ideal.mul_le_left
  rw [T.Q.l.prod] at hle
  exact hle (Ideal.mem_span_singleton_self _)

theorem isIntM_add_nsmul_iff {b a : ℕ} {N N' : Matrix (Fin b) (Fin a) (EAf D)} (hN' : IsIntM N') (k : ℕ) :
    IsIntM (N + k • N') ↔ IsIntM N := by
  constructor
  · intro h i j
    have := sub_mem (h i j) (nsmul_mem (hN' i j) k)
    rwa [Matrix.add_apply, Matrix.smul_apply, add_sub_cancel_right] at this
  · intro h i j
    rw [Matrix.add_apply, Matrix.smul_apply]
    exact add_mem (h i j) (nsmul_mem (hN' i j) k)

theorem redM_add_nsmul (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} {N N' : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N)
    (hN' : IsIntM N') (k : ℕ) (hk : ((k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : redM PP (N + k • N') = redM PP N := by
  have hk0 : ((k : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hk
  ext i j
  have h1 : (N + k • N') i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (isIntM_add_nsmul_iff hN' _).2 hN i j
  unfold redM
  rw [dite_eq_left h1, dite_eq_left (hN i j)]
  have h2 : (⟨(N + k • N') i j, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ⟨N i j, hN i j⟩ + ((k : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨N' i j, hN' i j⟩ := by
    apply Subtype.ext
    simp [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_add (f := _), map_mul, map_natCast, hk0, zero_mul, add_zero]

theorem omegaK_congr {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    {y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)}
    (h : ∀ PP ∈ Pg, y PP = y' PP) : omegaK Pg y = omegaK Pg y' := by
  unfold omegaK
  have : (∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1) ↔ (∀ PP ∈ Pg, LowZero a (y' PP) ∧ topL a (y' PP) = 1) :=
    ⟨fun hy PP hPP => h PP hPP ▸ hy PP hPP, fun hy PP hPP => (h PP hPP).symm ▸ hy PP hPP⟩
  by_cases hc : ∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1
  · rw [if_pos hc, if_pos (this.1 hc)]
  · rw [if_neg hc, if_neg (fun h' => hc (this.2 h'))]

theorem omegaK_mem {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) (k : Subfield ℂ) :
    omegaK Pg y ∈ k := by
  unfold omegaK
  split_ifs
  exacts [k.one_mem, k.zero_mem]

theorem omegaQ_empty {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dite_eq_left (fun PP h => absurd h (Finset.notMem_empty PP))]
  simp

theorem isLevDatum_ref : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsLevDatum Rl.toRealDat.ψ (Vc D j) (Wc D j) (Rl.toRealDat.ΛV j) (Rl.toRealDat.ΛW j) T.Q.l.M (embLL0 D).fieldRange (Rl.toRealDat.vacP j) (Rl.toRealDat.vP j A3.A.μ0) := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
  classical
  have hQ0 : Rl.toRealDat.Q A3.A.μ0 = ∅ := q_base_empty Rl.toRealDat hcore.lev
  obtain ⟨-, e, he, hth⟩ := hcore.thP.vP j A3.A.μ0
  rw [hQ0, Finset.union_empty] at he
  simp only [hQ0, omegaQ_empty, mul_one] at hth
  obtain ⟨cV, hbV⟩ := hcore.lev.βV j
  obtain ⟨cW, hbW⟩ := hcore.lev.βW j
  have hsV := GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hbV
  have hsW := GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hbW
  have hfV := hbV.1
  have hfW := hbW.1
  have hhalf := (hpins.2.tuple ()).half
  have hP2 : ∀ PP ∈ Rl.toRealDat.Pg,
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
    fun PP hPP => hhalf.2.2 PP (Or.inl hPP)
  have hMPg : ∀ PP ∈ Rl.toRealDat.Pg, ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    have h1 : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb := natM_mem_Mb T
    have h2 : T.Q.l.Mb ≤ PP.asIdeal := by
      rw [hhalf.1]
      exact Ideal.prod_le_inf.trans (Finset.inf_le hPP)
    exact h2 h1
  refine ⟨Rl.toRealDat.Pg.image Formalism.L2.DIV.conjPl, cA D e, _, isIdemSum_conjPl he, ?_, ?_, ?_, ?_, hth⟩
  · intro PP hPP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hPP
    show Formalism.L2.DIV.starOHom ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ P0.asIdeal
    rw [map_natCast]
    exact hMPg P0 hP0
  · intro t ht
    by_cases hc : IsHalf (cA D e) t ∧ IsIntM (frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t)
    · exact ⟨GlobalTheory.T.idempotent_sum_self_dual_frames_bound D _ _ _ _ _ _ hsV hsW hfV hfW _ e he hP2 t hc.1 hc.2, hc.1⟩
    · exact absurd (if_neg hc) ht
  · intro u hu hue t
    have hN' := GlobalTheory.T.adjointFrameMatrix_integral_of_conjugate_half D _ _ _ _ _ _ hsV hsW hfV hfW _ e he hP2 u hu hue
    have hfr : frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) (t + T.Q.l.M • u) =
        frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t +
          T.Q.l.M • frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) u := by
      rw [frMapAdj_add', frMapAdj_nsmul']
    have hKu : IsHalf (cA D e) (T.Q.l.M • u) := fun a b => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hue a b]
    have hhalf' : IsHalf (cA D e) (t + T.Q.l.M • u) ↔ IsHalf (cA D e) t := by
      constructor
      · intro h a b
        have := h a b
        rw [Matrix.add_apply, mul_add, hKu a b] at this
        exact add_right_cancel this
      · intro h a b
        rw [Matrix.add_apply, mul_add, h a b, hKu a b]
    show (if _ then _ else _) = (if _ then _ else _)
    rw [hfr]
    by_cases hc : IsHalf (cA D e) t ∧ IsIntM (frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t)
    · rw [if_pos ⟨hhalf'.2 hc.1, (isIntM_add_nsmul_iff hN' _).2 hc.2⟩, if_pos hc]
      exact omegaK_congr _ fun PP hPP => redM_add_nsmul PP hc.2 hN' _ (hMPg PP hPP)
    · rw [if_neg, if_neg hc]
      intro h'
      exact hc ⟨hhalf'.1 h'.1, (isIntM_add_nsmul_iff hN' _).1 h'.2⟩
  · intro t
    show (if _ then _ else _) ∈ _
    split_ifs
    · exact omegaK_mem _ _ _
    · exact Subfield.zero_mem _

end GlobalTheory.RefDatumLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelDatumReferenceTupleSmallFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLevelDatum_referenceTuple_smallField : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsLevDatum Rl.toRealDat.ψ (Vc D j) (Wc D j) (Rl.toRealDat.ΛV j) (Rl.toRealDat.ΛW j) T.Q.l.M (embLL0 D).fieldRange (Rl.toRealDat.vacP j) (Rl.toRealDat.vP j A3.A.μ0) := by
  first | exact @GlobalTheory.RefDatumLev.isLevDatum_ref | exact GlobalTheory.RefDatumLev.isLevDatum_ref | (intros; apply GlobalTheory.RefDatumLev.isLevDatum_ref <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegral
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.HalfOInt

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

theorem idem_mem_at (D : D7) (e : AE D) (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  set n : ℕ := Ideal.absNorm D.host.𝔟 with hn
  have hnP : (n : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro h
    obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under PP
    exact hP ((hpP _).2 (((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 ((hpP _).1 h)).mul_right _))
  have hn0 : (n : 𝓞 D.host.E) ≠ 0 := fun h => hnP (h ▸ zero_mem _)
  have hn0' : (n : D.host.E) ≠ 0 := by
    intro h
    apply hn0
    have : n = 0 := by exact_mod_cast h
    rw [this, Nat.cast_zero]
  have h1 : finPart D (e * incA D (((n : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hnP ((he.2 _ hn0).2 h)
  have h2 := GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1
  obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem D.host.𝔟) ha
  have h3 := mul_mem h2 (GlobalTheory.IdemIntegral.eToEAf_int D c)
  rw [map_mul, GlobalTheory.IdemIntegral.toEAf_incA, mul_assoc, ← map_mul] at h3
  convert h3 using 3
  have hc' : (c : D.host.E) = a * n := hc
  have hcast : ((n : 𝓞 D.host.E) : D.host.E) = n := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n
  rw [hc', hcast]
  field_simp

theorem idem_mem_intAf (D : D7) (e : AE D) (P : Finset (Pl D.host.E)) (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul]
  exact sum_mem fun PP hPP => idem_mem_at D _ PP (hes PP hPP) (hP PP hPP) a ha

theorem smul_genE {D : D7} {S T : HSp D} (e : AE D) (c : EAf D) (τ : Fin T.rank → EAf D)
    (σ : Fin S.rank → EAf D) :
    e • genE (S := S) (T := T) c τ σ = genE (toEAf D e * c) τ σ := by
  ext i j
  simp only [genE, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_liftE, mul_assoc]

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

set_option maxHeartbeats 4000000 in
theorem frMapO_int_of_half {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {u : WO S T} (hu : u ∈ latO S T ΛS ΛT (fun _ => True)) (hh : IsHalf e u) :
    IsIntM (frMapO S T βS βT u) := by
  have hx : e • u = u := Matrix.ext fun i j => hh i j
  rw [← hx]
  clear hx hh
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, _, a, ha, s, hs, t, ht, rfl⟩ := hw
    show IsIntM (frMapO S T βS βT (e • genL S T α a s t))
    rw [genL_eq_genE, smul_genE, genE, frMapO_mapLiftE, mul_vecMulVec_mul]
    intro i j
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    refine mul_mem ?_ (mul_mem ?_ ?_)
    · rw [← mul_assoc]
      exact mul_mem (idem_mem_intAf D e P he hP a ha)
        (Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩))
    · exact (fT _).1 (mem_hatL_of_mem ht) i
    · rw [Matrix.vecMul_vecMul]
      have e : (fun l => (S.gram.map (eToEAf D) * (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D))) l j) =
          S.gram.map (eToEAf D) *ᵥ (fun i => (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) i j) := by
        funext l; rw [Matrix.mul_apply]; rfl
      show (fun k => sR D (eToEAf D (s k))) ⬝ᵥ
        (fun l => (S.gram.map (eToEAf D) * (βS : Matrix (Fin S.rank) (Fin S.rank) (EAf D))) l j) ∈ _
      rw [e]
      exact hform_int hS hs (col_mem_hatL fS j)
  | zero =>
    rw [smul_zero, frMapO_zero]
    exact fun _ _ => zero_mem _
  | add x y _ _ hx hy =>
    rw [smul_add, frMapO_add]
    exact isIntM_add hx hy
  | neg x _ hx =>
    rw [smul_neg, frMapO_neg]
    exact fun i j => neg_mem (hx i j)

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat Matrix

theorem sum_decomp {R : Type} [CommRing R] {m n N : ℕ} (M : Matrix (Fin m) (Fin n) R) (g Y : Fin N → Fin n → R)
    (hb : ∑ k, vecMulVec (g k) (Y k) = 1) (c z : R) (hM : (c * z) • M = M) :
    ∑ k, c • vecMulVec (z • (M *ᵥ g k)) (Y k) = M := by
  have h : ∀ k, c • vecMulVec (z • (M *ᵥ g k)) (Y k) = (c * z) • (M * vecMulVec (g k) (Y k)) := by
    intro k
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.smul_sum, ← Matrix.mul_sum, hb, Matrix.mul_one, hM]

set_option maxHeartbeats 4000000 in
theorem mem_latO_of_int {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hS : IsSelfDualC S ΛS) (fS : Formalism.L2.DIV.IsFrame βS ΛS) (fT : Formalism.L2.DIV.IsFrame βT ΛT)
    {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P)
    (hP : ∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {t : WO S T} (ht : IsHalf e t) (hN : IsIntM (frMapO S T βS βT t)) :
    t ∈ latO S T ΛS ΛT (fun _ => True) := by
  have ha := GlobalTheory.HalfAdjLattice.natCast_mem_AA (D := D) (D.host.QS * D.host.q)
  generalize D.host.QS * D.host.q * Ideal.absNorm D.host.ccK = n at hP ha
  obtain ⟨N, g, s, hg, hs, hb⟩ := GlobalTheory.HalfAdjLattice.exists_dual_families S hS
  have hz := GlobalTheory.HalfAdjLattice.toEAf_int (GlobalTheory.HalfAdjLattice.idem_div_int he hP)
  have hze := GlobalTheory.HalfAdjLattice.natCast_mul_idem_div he hP
  generalize e * incA D (n : D.host.E)⁻¹ = z at hz hze
  set M : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.map t (toEAf D) with hMdef
  have hN' : IsIntM ((βT⁻¹).val * M * βS.val) := hN
  have hb' : ∑ k, vecMulVec (fun i => eToEAf D (g k i))
      (vecMul (fun a => sR D (eToEAf D (s k a))) (S.gram.map (eToEAf D))) = 1 := by
    ext i j
    have h1 := congrArg (eToEAf D) (congrFun (hb (Pi.single j 1)) i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_apply, map_sum] at h1
    rw [Matrix.sum_apply]
    have h2 : eToEAf D ((Pi.single j 1 : Fin S.rank → D.host.E) i) = (1 : Matrix (Fin S.rank) (Fin S.rank) (EAf D)) i j := by
      rw [Pi.single_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [← h2, ← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulVec_single_one]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [vecMulVec_apply, vecMul, dotProduct, map_apply, sR_eTo, Pi.smul_apply, smul_eq_mul, map_mul, map_sum,
      Matrix.col, transpose_apply]
    exact mul_comm _ _
  have hM : ((eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) * toEAf D z) • M = M := by
    have h1 : (eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F))) * toEAf D z = toEAf D e := by
      rw [← hze, map_mul, toEAf_incA, ← Algebra.TensorProduct.one_def, mul_one]
    rw [h1]
    ext i j
    simp only [hMdef, Matrix.smul_apply, map_apply, smul_eq_mul]
    rw [← map_mul, ht i j]
  have key := sum_decomp M (fun k i => eToEAf D (g k i))
    (fun k => vecMul (fun a => sR D (eToEAf D (s k a))) (S.gram.map (eToEAf D))) hb' _ _ hM
  have hdec : t = ∑ k, genE (S := S) (T := T)
      (eToEAf D (n : D.host.E) * ((1 : D.host.E) ⊗ₜ[D.host.F] (1 : Af D.host.F)))
      (toEAf D z • (M *ᵥ fun i => eToEAf D (g k i))) (fun a => eToEAf D (s k a)) := by
    ext i j
    have h1 := congrFun (congrFun key i) j
    rw [Matrix.sum_apply] at h1
    rw [Matrix.sum_apply]
    unfold genE
    simp only [map_apply]
    rw [← liftE_sum, h1]
    have h0 : infPart D (t i j) = 0 := by rw [← ht i j, map_mul, infPart_of_idemSum he, zero_mul]
    exact (liftE_toEAf _ h0).symm
  rw [hdec]
  refine AddSubgroup.sum_mem _ fun k _ => genE_mem ?_ ha ?_ (mem_hatL_of_mem (hs k))
  · intro v; rw [map_one]; exact one_mem _
  · exact Submodule.smul_mem _ (⟨_, hz⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)
      (GlobalTheory.HalfAdjLattice.mulVec_mem_hatL fT fS hN' (mem_hatL_of_mem (hg k)))

end GlobalTheory.HalfOInt

namespace GlobalTheory.HalfOInt

theorem mem_latO_iff_frMapO_int : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ w : WO S T, IsHalf e w → (w ∈ latO S T ΛS ΛT (fun _ => True) ↔ IsIntM (frMapO S T βS βT w)) := by
  intro D S T ΛS ΛT βS βT hS _ fS fT P e he hP w hw
  exact ⟨fun hu => frMapO_int_of_half hS fS fT he hP hu hw, fun hN => mem_latO_of_int hS fS fT he hP hw hN⟩

end GlobalTheory.HalfOInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegralStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedLattice_half_iff_frameMatrix_integral : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ w : WO S T, IsHalf e w → (w ∈ latO S T ΛS ΛT (fun _ => True) ↔ IsIntM (frMapO S T βS βT w)) := by
  first | exact @GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int | exact GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int | (intros; apply GlobalTheory.HalfOInt.mem_latO_iff_frMapO_int <;> assumption)
end
end
