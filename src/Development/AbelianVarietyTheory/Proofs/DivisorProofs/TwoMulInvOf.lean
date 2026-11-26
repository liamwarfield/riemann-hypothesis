module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFifth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
public import Formalism.PolynomialDimension.WeylDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealWeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftFrLifts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ
open scoped Matrix

namespace GlobalTheory.ThetaTransform

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

abbrev VA (F : Type) [Field F] [NumberField F] (N : ℕ) : Type := (Fin N → AF F) × (Fin N → AF F)

def symV (w w' : VA F N) : AF F := w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2

def embR {κ : Type} (t : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i)) 0

def IsRealLine (M : ℝ →+ VA F N) : Prop := Continuous M ∧ ∀ t, fin (M t).1 = 0 ∧ fin (M t).2 = 0

def half (F : Type) [Field F] (N : ℕ) : Fin N → F := fun _ => 1 / 2

variable [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ)

def heisV (u : VA F N) (f : VA F N → ℂ) : VA F N → ℂ := fun w => ψ (⅟(2 : AF F) * symV w u) * f (w + u)

def thV (Φ : (Fin N → AF F) → ℂ) : VA F N → ℂ := fun w => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ w Φ)

def invV (ν : Measure (AF F)) (𝓓 : Set (Fin N → AF F)) (f : VA F N → ℂ) : (Fin N → AF F) → ℂ :=
  fun x => ∫ y in 𝓓, f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) ∂(muV N ν)

def QuasiV (f : VA F N → ℂ) : Prop :=
  ∀ (a b : Fin N → F) (w : VA F N), f ((rat a, rat b) + w) = ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w)) * f w

def LevelV (f : VA F N → ℂ) : Prop :=
  ∃ U : AddSubgroup (VA F N), IsOpen (U : Set (VA F N)) ∧ ∀ u ∈ U, inf u.1 = 0 → inf u.2 = 0 → heisV ψ u f = f

abbrev ratSub (F : Type) [Field F] [NumberField F] (N : ℕ) : AddSubgroup (Fin N → AF F) :=
  AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))

theorem invOf_two_eq : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  simp

omit [Invertible (2 : AF F)] in
theorem Bd_half (u u' : Fin N → AF F) : Bd (AF F) (half F N) u u' = u ⬝ᵥ u' := by
  simp [Bd, half, dotProduct]

omit [NumberField F] [Invertible (2 : AF F)] in
theorem half_ne_zero [CharZero F] (l : Fin N) : half F N l ≠ 0 := by
  simp [half]

theorem schr_eq_rho (w : VA F N) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w Φ = rho ψ (half F N) w.1 w.2 Φ := by
  funext x
  rw [GlobalTheory.WeilM.schr, rho, Bd_half, Bd_half, invOf_two_eq]

theorem thV_eq_th (Φ : (Fin N → AF F) → ℂ) (w : VA F N) : thV ψ Φ w = th (rho ψ (half F N) w.1 w.2 Φ) := by
  rw [thV, schr_eq_rho]
  rfl

theorem two_mul_invOf (a : AF F) : ⅟(2 : AF F) * a + ⅟(2 : AF F) * a = a := by
  rw [← add_mul, invOf_two_add_invOf_two, one_mul]

theorem schr_schr (w u : VA F N) (Φ : (Fin N → AF F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ u Φ) = ψ (⅟(2 : AF F) * symV w u) • GlobalTheory.WeilM.schr ψ (w + u) Φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_assoc]
  congr 2
  simp only [symV, add_dotProduct, dotProduct_add]
  linear_combination (-1 : AF F) * two_mul_invOf (w.1 ⬝ᵥ u.2)

theorem thV_schr (u : VA F N) (Φ : (Fin N → AF F) → ℂ) : thV ψ (GlobalTheory.WeilM.schr ψ u Φ) = heisV ψ u (thV ψ Φ) := by
  funext w
  rw [thV, schr_schr, heisV, thV]
  exact tsum_mul_left

theorem quasiV_thV (hψ : ∀ a : F, ψ (algebraMap F (AF F) a) = 1) (Φ : (Fin N → AF F) → ℂ) : QuasiV ψ (thV ψ Φ) := by
  intro a b w
  simp only [thV, GlobalTheory.WeilM.thetaSum]
  rw [← tsum_mul_left, ← (Equiv.addRight a).tsum_eq (fun ξ : Fin N → F => ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w)) *
    GlobalTheory.WeilM.schr ψ w Φ fun i => algebraMap F (AF F) (ξ i))]
  refine tsum_congr fun ξ => ?_
  have e1 : (fun i => algebraMap F (AF F) ((Equiv.addRight a ξ) i)) = rat ξ + rat a := by
    funext i; simp [rat]
  have e2 : (fun i => algebraMap F (AF F) (ξ i)) = rat ξ := rfl
  have e3 : ∀ c d : Fin N → F, rat c ⬝ᵥ rat d = algebraMap F (AF F) (c ⬝ᵥ d) := fun c d => by
    simp [rat, dotProduct]
  rw [e1, e2]
  simp only [GlobalTheory.WeilM.schr, Prod.fst_add, Prod.snd_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc]
  congr 1
  have h1 := hψ (ξ ⬝ᵥ b + 1 / 2 * (a ⬝ᵥ b))
  rw [← mul_one (ψ (-(⅟(2 : AF F) * symV (rat a, rat b) w) + _)), ← h1, ← AddChar.map_add_eq_mul]
  congr 1
  rw [map_add (f := _), map_mul, ← invOf_two_eq, ← e3, ← e3]
  simp only [symV, add_dotProduct, dotProduct_add]
  linear_combination two_mul_invOf (rat a ⬝ᵥ w.2)

end GlobalTheory.ThetaTransform

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMemLocSpan
noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW.MirSemi

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def locSpan (S : Finset (HeightOneSpectrum (𝓞 E))) (F₀ : GA E a → ℂ) : Submodule ℂ (GA E a → ℂ) :=
  sInf {V | F₀ ∈ V ∧ (∀ F ∈ V, ∀ h ∈ supS (E := E) (a := a) S, (fun g => F (g * h)) ∈ V) ∧
    ∀ F ∈ V, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ V}

variable {S : Finset (HeightOneSpectrum (𝓞 E))} {F₀ : GA E a → ℂ}

theorem self_mem_locSpan : F₀ ∈ locSpan S F₀ :=
  Submodule.mem_sInf.2 fun _ hV => hV.1

theorem rt_mem_locSpan {F : GA E a → ℂ} (hF : F ∈ locSpan S F₀) {h : GA E a} (hh : h ∈ supS (E := E) (a := a) S) :
    (fun g => F (g * h)) ∈ locSpan S F₀ :=
  Submodule.mem_sInf.2 fun V hV => hV.2.1 F (Submodule.mem_sInf.1 hF V hV) h hh

theorem kerInf_mem_locSpan {F : GA E a → ℂ} (hF : F ∈ locSpan S F₀) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) :
    kerInf ν k γ F ∈ locSpan S F₀ :=
  Submodule.mem_sInf.2 fun V hV => hV.2.2 F (Submodule.mem_sInf.1 hF V hV) X ν k γ hk

theorem locSpan_le {V : Submodule ℂ (GA E a → ℂ)} (h₁ : F₀ ∈ V)
    (h₂ : ∀ F ∈ V, ∀ h ∈ supS (E := E) (a := a) S, (fun g => F (g * h)) ∈ V)
    (h₃ : ∀ F ∈ V, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
      (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → kerInf ν k γ F ∈ V) : locSpan S F₀ ≤ V :=
  sInf_le ⟨h₁, h₂, h₃⟩

theorem locSpan_le_rspan {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) : locSpan S φ.1 ≤ rspan π :=
  locSpan_le (mem_rspan hφ) (fun _ hF h _ => rt_mem_rspan hF h) fun _ hF _ _ ν _ _ _ hk => kerInf_mem_rspan hF ν hk

theorem locSpan_le_mspanR {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V) : locSpan S φ.1 ≤ mspanR π := by
  rw [← rspan_eq_mspanR]; exact locSpan_le_rspan hφ

end GlobalTheory.JSW.MirSemi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalHomLatticeOfKeepsCompletedLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalHomLatticeOfKeepsCompletedLattices
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.LocalLatStab

open GlobalTheory.AdelicLatMove

variable {D : D7}

def swp (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) →+* EAf D :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E : _ →+* _)

theorem map_toEAf (V : HSp D) (g : GA D V) :
    (mt V g).map (toEAf D) = (finMat D.sp.cm.sig V.gram g).map (swp D) := rfl

def swpVec (D : D7) (n : ℕ) (α : Af D.host.F) :
    (Fin n → Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin n → EAf D) :=
  AddMonoidHom.mk' (fun y i => ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * swp D (y i))
    (fun y z => by funext i; simp only [Pi.add_apply, map_add (f := _), mul_add])

theorem swpVec_pure {n : ℕ} (α β : Af D.host.F) (x : Fin n → D.host.E) :
    swpVec D n α (fun i => β ⊗ₜ[D.host.F] x i) = fun i => x i ⊗ₜ[D.host.F] (α * β) := by
  funext i
  change ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * (x i ⊗ₜ[D.host.F] β) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem mulVec_swpVec (V : HSp D) (g : GA D V) (α : Af D.host.F)
    (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (mt V g).map (toEAf D) *ᵥ swpVec D _ α y = swpVec D _ α (finMat D.sp.cm.sig V.gram g *ᵥ y) := by
  rw [map_toEAf]
  funext i
  change ∑ j, swp D (finMat D.sp.cm.sig V.gram g i j) * (((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * swp D (y j)) =
    ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) * swp D (∑ j, finMat D.sp.cm.sig V.gram g i j * y j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_left_comm]

theorem rankOne_mem (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (a : D.host.E) (ha : a ∈ D.host.AA)
    (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (hP : ∀ v, ¬ P v → evalV D.host.F v α = 0)
    (s : Fin S.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hs : s ∈ latHat D.host.F D.host.E LS)
    (t : Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E) (ht : t ∈ latHat D.host.F D.host.E LT) :
    rankOne S T a (swpVec D _ 1 s) (swpVec D _ α t) ∈ latO S T LS LT P := by
  change rankOneHom S T a _ _ ∈ _
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    induction ht using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨β, hβ, x, hx, rfl⟩ := hs
      obtain ⟨γ, hγ, y, hy, rfl⟩ := ht
      rw [swpVec_pure, swpVec_pure, one_mul]
      apply AddSubgroup.subset_closure
      refine ⟨α * γ * β, (mul_mem (mul_mem hα hγ : α * γ ∈ Formalism.UG.intAd D.host.F) hβ :
        α * γ * β ∈ Formalism.UG.intAd D.host.F), fun v hv => ?_, a, ha, x, hx, y, hy,
        rankOne_pure S T a x y β (α * γ)⟩
      rw [map_mul, map_mul, hP v hv, zero_mul, zero_mul]
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _)]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg, map_neg]; exact neg_mem hy
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _)]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg, map_neg]; exact neg_mem hy

theorem actO_mem (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (g : GA D S) (h : GA D T)
    (hg : ∀ y ∈ latHat D.host.F D.host.E LS, finMat D.sp.cm.sig S.gram g *ᵥ y ∈ latHat D.host.F D.host.E LS)
    (hh : ∀ y ∈ latHat D.host.F D.host.E LT, finMat D.sp.cm.sig T.gram h *ᵥ y ∈ latHat D.host.F D.host.E LT)
    (u : WO S T) (hu : u ∈ latO S T LS LT P) : actO S T g h u ∈ latO S T LS LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hu
    have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := (one_mem _ : (1 : Af D.host.F) ∈ Formalism.UG.intAd D.host.F)
    have e := rankOne_pure S T a s t (1 * 1) (α * 1)
    rw [← swpVec_pure, ← swpVec_pure, mul_one, mul_one, mul_one] at e
    rw [← e, actO_rankOne, mulVec_swpVec, mulVec_swpVec]
    exact rankOne_mem S T LS LT P a ha α hα hP _
      (hg _ (AddSubgroup.subset_closure ⟨1, h1, s, hs, rfl⟩)) _
      (hh _ (AddSubgroup.subset_closure ⟨1, h1, t, ht, rfl⟩))
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem finMat_mul_inv (V : HSp D) (g : GA D V) :
    finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram g⁻¹ = 1 := by
  let f := Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
  change (mt V g).map f * (mt V g⁻¹).map f = 1
  rw [← Matrix.map_mul (f := f), ← mt_mul, mul_inv_cancel, mt_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem inv_keeps (V : HSp D) (L : Set (Fin V.rank → D.host.E)) (g : GA D V)
    (hg : ∀ y, y ∈ latHat D.host.F D.host.E L ↔
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E L) :
    ∀ y ∈ latHat D.host.F D.host.E L, finMat D.sp.cm.sig V.gram g⁻¹ *ᵥ y ∈ latHat D.host.F D.host.E L := by
  intro y hy
  rw [hg, Matrix.mulVec_mulVec, finMat_mul_inv, Matrix.one_mulVec]
  exact hy

theorem mem_latO_place_iff_actO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ v ε, IsPlaceIdem D v ε → ∀ (g : GA D S) (h : GA D T), (∀ y, y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) ↔ (finMat D.sp.cm.sig S.gram g).mulVec y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E))) → (∀ y, y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) ↔ (finMat D.sp.cm.sig T.gram h).mulVec y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) → ∀ u, u ∈ (latO S T ΛS ΛT fun w => w = v) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun w => w = v) := by
  intro D S T ΛS ΛT _ _ v _ _ g h hg hh u
  refine ⟨actO_mem S T _ _ _ g h (fun y hy => (hg y).1 hy) (fun y hy => (hh y).1 hy) u, fun hu => ?_⟩
  have h1 := actO_mem S T _ _ _ g⁻¹ h⁻¹ (inv_keeps S _ g hg) (inv_keeps T _ h hh) _ hu
  have h2 := actO_actO_inv S T g⁻¹ h⁻¹ u
  rw [inv_inv, inv_inv] at h2
  rwa [h2] at h1

end GlobalTheory.LocalLatStab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalHomLatticeOfKeepsCompletedLatticesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_localHomLattice_of_keeps_completedLattices : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ v ε, IsPlaceIdem D v ε → ∀ (g : GA D S) (h : GA D T), (∀ y, y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) ↔ (finMat D.sp.cm.sig S.gram g).mulVec y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E))) → (∀ y, y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) ↔ (finMat D.sp.cm.sig T.gram h).mulVec y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) → ∀ u, u ∈ (latO S T ΛS ΛT fun w => w = v) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun w => w = v) := by
  first | exact @GlobalTheory.LocalLatStab.mem_latO_place_iff_actO | exact GlobalTheory.LocalLatStab.mem_latO_place_iff_actO | (intros; apply GlobalTheory.LocalLatStab.mem_latO_place_iff_actO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

open GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

abbrev compGL (w : InfinitePlace E) : GL (Fin n) (Cinf E) →* GL (Fin n) ℂ :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)

theorem compGL_apply (w : InfinitePlace E) (g : GL (Fin n) (Cinf E)) (i j : Fin n) :
    ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = (g : Matrix (Fin n) (Fin n) (Cinf E)) i j w := rfl

abbrev matInf (g : GL (Fin n) (Cinf E)) : Fin n → Fin n → Cinf E :=
  fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j

def IsWhitInf (W : GL (Fin n) (Cinf E) → ℂ) : Prop :=
  ∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), ∀ g,
    W (u * g) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * W g

def IsModGrowthInf (W : GL (Fin n) (Cinf E) → ℂ) : Prop :=
  Continuous W ∧ ∃ (C : ℝ) (N : ℕ), ∀ g, ‖W g‖ ≤ C * htInf g ^ N

def IsRapidFInf {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (ν : Measure X) (k : X → ℂ)
    (γ : X → GL (Fin n) (Cinf E)) (η : X → Z →L[ℝ] ℝ) : Prop :=
  Measurable k ∧ (∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) ∧
    (∀ z, Measurable fun x => η x z) ∧
    ∀ N : ℕ, Integrable (fun x => ‖k x‖ * (htInf (γ x) * (1 + ‖η x‖)) ^ N) ν

def IsKerOpInf {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ) : Prop :=
  ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin n) (Cinf E))
    (η : X → Z →L[ℝ] ℝ), IsRapidFInf ν k γ η ∧
      ∀ W, IsModGrowthInf W → ∀ z g, T W z g = ∫ x, k x * (𝐞 (η x z) : ℂ) * W (g * γ x) ∂ν


variable (E) in
def levSetInf (n r : ℕ) : Set (GL (Fin n) (Cinf E)) := {g | ∀ w, compGL w g ∈ levSet n r}

def rowCutInf (ρ : Fin n) (x : Matrix (Fin n) (Fin n) (Cinf E)) : Fin n → Cinf E := fun j => if j ≤ ρ then x ρ j else 0

def secMatInf (ρ : Fin n) (j : InfinitePlace E → Fin n) (v : Fin n → Cinf E) : Fin n → Fin n → Cinf E :=
  fun i l w => secMat ρ (j w) (fun l => v l w) i l


open Classical in
def onMatInf (W : GL (Fin n) (Cinf E) → ℂ) (x : Matrix (Fin n) (Fin n) (Cinf E)) : ℂ :=
  if h : IsUnit x then W h.unit else 0

def smoothMatInf (α : (Fin n → Fin n → Cinf E) → ℂ) (W : GL (Fin n) (Cinf E) → ℂ) (g : GL (Fin n) (Cinf E)) : ℂ :=
  ∫ a : Fin n → Fin n → Cinf E, α a * onMatInf W ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a)


open Classical in
def toGLInf (x : Matrix (Fin n) (Fin n) (Cinf E)) : GL (Fin n) (Cinf E) := if h : IsUnit x then h.unit else 1

theorem val_toGLInf {x : Matrix (Fin n) (Fin n) (Cinf E)} (h : IsUnit x) :
    (toGLInf x : Matrix (Fin n) (Fin n) (Cinf E)) = x := by
  simp [toGLInf, h]

theorem onMatInf_val (W : GL (Fin n) (Cinf E) → ℂ) (g : GL (Fin n) (Cinf E)) :
    onMatInf W (g : Matrix (Fin n) (Fin n) (Cinf E)) = W g := by
  simp [onMatInf]

theorem onMatInf_of_isUnit (W : GL (Fin n) (Cinf E) → ℂ) {x : Matrix (Fin n) (Fin n) (Cinf E)} (h : IsUnit x) :
    onMatInf W x = W (toGLInf x) := by
  simp [onMatInf, toGLInf, h]

theorem mem_levSetInf {r : ℕ} {g : GL (Fin n) (Cinf E)} : g ∈ levSetInf E n r ↔
    ∀ i : Fin n, r ≤ (i : ℕ) → (∀ j, j < i → (g : Matrix (Fin n) (Fin n) (Cinf E)) i j = 0) ∧
      (g : Matrix (Fin n) (Fin n) (Cinf E)) i i = 1 := by
  constructor
  · intro h i hi
    refine ⟨fun j hj => funext fun w => ?_, funext fun w => ?_⟩
    · exact (h w i hi).1 j hj
    · exact (h w i hi).2
  · intro h w i hi
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [compGL_apply, (h i hi).1 j hj]; rfl
    · rw [compGL_apply, (h i hi).2]; rfl

theorem isKerOpInf_dirac (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (h : GL (Fin n) (Cinf E)) :
    IsKerOpInf (fun W (_ : Z) g => W (g * h)) := by
  refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance, fun _ => 1, fun _ => h, fun _ => 0,
    ⟨measurable_const, fun _ _ => measurable_const, fun _ => measurable_const, fun _ => integrable_const _⟩,
    fun W _ z g => ?_⟩
  simp

def LevRepInf (E : Type) [Field E] [NumberField E] (n r : ℕ) (lam : (GL (Fin n) (Cinf E) → ℂ) → ℂ) : Prop :=
  ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (B : Y × (Fin n → Fin n → Cinf E) → ℂ),
    ContDiffOn ℝ ∞ B {p | IsUnit (Matrix.of p.2)} → (∀ y, IsWhitInf fun g => B (y, matInf g)) →
    (∃ (D : Set Y) (C : Set (GL (Fin n) (Cinf E))), IsCompact D ∧ IsCompact C ∧ ∀ y, ∀ g ∈ levSetInf E n r,
      B (y, matInf g) ≠ 0 → y ∈ D ∧ ∃ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u⁻¹ * g ∈ C) →
    ∃ T : (GL (Fin n) (Cinf E) → ℂ) → Y → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T ∧
      ∀ W, IsModGrowthInf W → IsWhitInf W → ∀ y, ∀ g ∈ levSetInf E n r, T W y g = B (y, matInf g) * lam W

end GlobalTheory.JSW.MirCinf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSixth
noncomputable section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace EntryDatum

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}

theorem phiT_add {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG') (hd' : d'.Ok)
    (c : 𝓞 E) (hc : ∀ P ∈ ST, c ∈ P.asIdeal) (x z : HomE E a b)
    (hz : ∀ P ∈ ST, ∀ y ∈ d.at P, z y ∈ d'.at P) : phiT K d d' (x + c • z) = phiT K d d' x := by
  have key : ∀ (x z : HomE E a b), (∀ P ∈ ST, ∀ y ∈ d.at P, z y ∈ d'.at P) →
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) →
      ∀ P : ST, ∀ y ∈ d.at P.1, (x + c • z) y ∈ d'.at P.1 ∧ d'.f P ((x + c • z) y) = d.f P y := by
    intro x z hz h P y hy
    obtain ⟨h1, h2⟩ := h P y hy
    have h3 := hz P.1 P.2 y hy
    have h4 : c • z y ∈ d'.at P.1 := Submodule.smul_mem _ c h3
    have e : (x + c • z) y = x y + c • z y := rfl
    rw [e]
    refine ⟨add_mem h1 h4, ?_⟩
    rw [hd'.f_add P _ h1 _ h4, hd'.f_smul P c _ h3, Ideal.Quotient.eq_zero_iff_mem.2 (hc P.1 P.2), zero_mul, add_zero, h2]
  have hiff : (∀ P : ST, ∀ y ∈ d.at P.1, (x + c • z) y ∈ d'.at P.1 ∧ d'.f P ((x + c • z) y) = d.f P y) ↔
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) := by
    refine ⟨fun h => ?_, key x z hz⟩
    have h' := key (x + c • z) (-z) (fun P hP y hy => neg_mem (hz P hP y hy)) h
    have e : x + c • z + c • (-z) = x := by rw [smul_neg, add_neg_cancel_right]
    rwa [e] at h'
  unfold phiT
  by_cases h : ∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y
  · rw [if_pos h, if_pos (hiff.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.1 h'))]

theorem phiT_support {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (x : HomE E a b) (hx : phiT K d d' x ≠ 0) : ∀ P ∈ ST, ∀ y ∈ d.at P, x y ∈ d'.at P := by
  intro P hP y hy
  unfold phiT at hx
  split_ifs at hx with h
  · exact (h ⟨P, hP⟩ y hy).1
  · exact absurd rfl hx

theorem norm_phiT_le {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (σ : K →+* ℂ) (x : HomE E a b) : ‖σ (phiT K d d' x)‖ ≤ 1 := by
  unfold phiT
  split_ifs <;> simp

theorem inFr_maps_iff (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    {M M₀ : Submodule (𝓞 E) (Sp E a)} {M' M₀' : Submodule (𝓞 E) (Sp E b)}
    (hf : ∀ x, f x ∈ M ↔ x ∈ M₀) (hf' : ∀ x, f' x ∈ M' ↔ x ∈ M₀') (x : HomE E a b) :
    (∀ y ∈ M₀, inFr f f' x y ∈ M₀') ↔ ∀ y ∈ M, x y ∈ M' := by
  have e : ∀ y, f' (inFr f f' x y) = x (f y) := fun y => by simp [inFr]
  constructor
  · intro h y hy
    have h1 : f.symm y ∈ M₀ := (hf _).1 (by simpa using hy)
    have h2 := (hf' _).2 (h _ h1)
    rw [e] at h2
    simpa using h2
  · intro h y hy
    rw [← hf', e]
    exact h _ ((hf y).2 hy)

theorem inFr_add_smul (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x z : HomE E a b) (q k : ℕ) :
    inFr f f' (x + ((q * k : ℕ) : 𝓞 E) • z) = inFr f f' x + (q : E) • inFr f f' ((k : 𝓞 E) • z) := by
  have e : ∀ n : ℕ, ((n : ℕ) : 𝓞 E) • z = (n : E) • z := fun n => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [e, e]
  refine LinearMap.ext fun y => ?_
  simp [inFr, mul_smul]

theorem smallDatum_prod {ST SG SG' SB S : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (hd' : d'.Ok) (fr : Frs E a SB) (fr' : Frs E b SB)
    (hfr : ∀ (P : SB) x, fr P x ∈ d.at P.1 ↔ x ∈ stdAt E a P.1) (hfr' : ∀ (P : SB) x, fr' P x ∈ d'.at P.1 ↔ x ∈ stdAt E b P.1)
    (hS : ∀ P, P ∈ S ↔ P ∈ ST ∨ P ∈ SB) (c : ℕ) (hc : ∀ P ∈ ST, (c : 𝓞 E) ∈ P.asIdeal) (q : SB → ℕ) (hq : ∀ P, q P ∣ c)
    (Φ : SB → HomE E a b → K) (β : SB → ℝ) (hΦ : ∀ P : SB, LocSmall (q P) (stdAt E a P.1) (stdAt E b P.1) (Φ P) (β P)) :
    SmallDatum S d.N d'.N c (fun x => phiT K d d' x * ∏ P : SB, Φ P (inFr (fr P) (fr' P) x)) (∏ P : SB, β P) := by
  refine ⟨fun x hx P hP => ?_, fun x y hy => ?_, fun σ x => ?_⟩
  · rcases (hS P).1 hP with h | h
    · exact phiT_support d d' x (left_ne_zero_of_mul hx) P h
    · have h1 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) ⟨P, h⟩ (Finset.mem_univ _)
      exact (inFr_maps_iff _ _ (hfr ⟨P, h⟩) (hfr' ⟨P, h⟩) x).1 ((hΦ ⟨P, h⟩).1 _ h1)
  · obtain ⟨z, hz, rfl⟩ := hy
    have e : ((c : 𝓞 E) • (LinearMap.id : HomE E a b →ₗ[𝓞 E] HomE E a b)) z = (c : 𝓞 E) • z := rfl
    rw [e]
    show phiT K d d' _ * _ = phiT K d d' _ * _
    rw [phiT_add d d' hd' _ hc x z (fun P hP => hz P ((hS P).2 (Or.inl hP)))]
    congr 1
    refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨k, hk⟩ := hq P
    rw [hk, inFr_add_smul]
    refine (hΦ P).2.1 _ _ ?_
    refine (inFr_maps_iff _ _ (hfr P) (hfr' P) _).2 fun y hy => ?_
    exact Submodule.smul_mem _ (k : 𝓞 E) (hz P.1 ((hS P.1).2 (Or.inr P.2)) y hy)
  · show ‖σ (phiT K d d' x * _)‖ ≤ _
    rw [map_mul, norm_mul, map_prod, norm_prod]
    have h1 : ∏ P : SB, ‖σ (Φ P (inFr (fr P) (fr' P) x))‖ ≤ ∏ P : SB, β P :=
      Finset.prod_le_prod₀ (fun P _ => norm_nonneg _) fun P _ => (hΦ P).2.2 σ _
    have h0 : 0 ≤ ∏ P : SB, ‖σ (Φ P (inFr (fr P) (fr' P) x))‖ := Finset.prod_nonneg fun P _ => norm_nonneg _
    exact (mul_le_of_le_one_left h0 (norm_phiT_le d d' σ x)).trans h1

end EntryDatum

end GlobalTheory.ColNorms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingListCharacterProduct
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare.Shift

variable {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n}

theorem natW_top (lam : DomWeight (n + 1)) (a : Fin (n + 1)) :
    (lam.natW a : ℤ) = lam.w a - lam.w (Fin.last n) := by
  have h1 : lam.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dite_eq_left (Nat.succ_pos n)]
    rfl
  have h2 := lam.anti (Fin.le_last a)
  unfold DomWeight.natW
  rw [h1]
  omega

theorem lamZ_lamN (lam : DomWeight (n + 1)) (a : Fin (n + 1)) :
    lamZ (lamN lam) a = lam.w a - lam.w (Fin.last n) := by
  unfold lamZ
  split_ifs with h
  · exact natW_top lam a
  · have : a = Fin.last n := Fin.ext (by have := a.2; simp; omega)
    simp [this]

theorem lamN_cast (lam : DomWeight (n + 1)) (i : Fin n) :
    (lamN lam i : ℤ) = lam.w i.castSucc - lam.w (Fin.last n) := natW_top lam _

theorem nuNext_cast (lam : DomWeight (n + 1)) (i : Fin n) :
    (nuNext (lamN lam) i : ℤ) = lam.w i.succ - lam.w (Fin.last n) := by
  rw [← lamZ_lamN]
  unfold nuNext lamZ
  simp only [Fin.val_succ]
  split_ifs <;> rfl

theorem natW_low (hE : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg) (i : Fin n) :
    (sg.natW i : ℤ) = sg.w i - lam.w (Fin.last n) := by
  have hi := i.2
  have h0 : 0 < n := by omega
  have h1 : sg.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dite_eq_left h0]
    exact hE _ (by simp only; omega)
  have h2 : sg.w ⟨n - 1, by omega⟩ ≤ sg.w i := sg.anti (by rw [Fin.le_def]; simp only; omega)
  rw [hE ⟨n - 1, by omega⟩ (by simp only; omega)] at h2
  unfold DomWeight.natW
  rw [h1]
  omega

theorem d0_eq (hE : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg) :
    Formalism.BranchingDeterminantCap.d0 (lamZ (lamN lam)) (fun i => (sg.natW i : ℤ)) = GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.dZero lam sg := by
  unfold Formalism.BranchingDeterminantCap.d0 GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.dZero
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [lamZ_lamN, natW_low hE]
  ring

theorem rename_initMinor (K : Type) [Field K] {s : ℕ} (I : Fin s → Fin (n + 1)) (hs : s ≤ n) :
    incl K n (initMinor K I hs) = initMinor K I (hs.trans (Nat.le_succ n)) := by
  unfold initMinor incl
  rw [AlgHom.map_det]
  congr 1
  ext p q
  simp

end GlobalTheory.BrCompare.Shift


open GlobalTheory.BrCompare.Shift in
theorem GlobalTheory.BrCompare.shifted_branching_list_character : ∀ (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n), GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg → GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg → Formalism.BranchingDeterminantCap.Interlace (lamZ (lamN lam)) (fun i => (sg.natW i : ℤ)) ∧ (∀ u ∈ bmList (lamN lam) sg.natW, u ∈ zList lam sg) ∧ ((zList lam sg).map (bmChi (lamN lam) fun s => ((lamN lam s - sg.natW s : ℕ) : ℤ))).prod = Formalism.L2.Col.Br.cBr rfl lam sg ∧ (∀ s, (Formalism.L2.Col.Br.bBr rfl lam sg s).toNat = lamN lam s - sg.natW s) ∧ ∀ (K : Type) [Field K], Formalism.L2.Col.Br.xiBr K rfl lam sg = incl K n (xiB K (lamN lam) sg.natW) := by
  intro n lam sg hI hE
  have hb : ∀ s, (Formalism.L2.Col.Br.bBr rfl lam sg s).toNat = lamN lam s - sg.natW s := by
    intro s
    have h1 := lamN_cast lam s
    have h2 := natW_low hE s
    have h3 : Formalism.L2.Col.Br.bBr rfl lam sg s = lam.w s.castSucc - sg.w s := rfl
    rw [h3]
    omega
  have ha : ∀ s, (Formalism.L2.Col.Br.aBr rfl lam sg s).toNat = sg.natW s - nuNext (lamN lam) s := by
    intro s
    have h1 := nuNext_cast lam s
    have h2 := natW_low hE s
    have h3 : Formalism.L2.Col.Br.aBr rfl lam sg s = sg.w s - lam.w s.succ := rfl
    rw [h3]
    omega
  refine ⟨?_, ?_, ?_, hb, ?_⟩
  · intro i
    have := hI i
    simp only [lamZ_lamN, natW_low hE]
    omega
  · intro u hu
    simp only [bmList, List.mem_flatMap, List.mem_map, Finset.mem_toList, Finset.mem_erase, rset, d0_eq hE,
      Finset.mem_Icc] at hu
    simp only [lamZ_lamN, natW_low hE] at hu
    obtain ⟨i, -, v, ⟨h1, h2, h3⟩, rfl⟩ := hu
    simp only [zList, List.mem_flatten, List.mem_ofFn]
    refine ⟨_, ⟨i, rfl⟩, ?_⟩
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_erase, GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.rangeSet, Finset.mem_Icc]
    exact ⟨v + lam.w (Fin.last n), ⟨by omega, by omega, by omega⟩, by ring⟩
  · unfold zList Formalism.L2.Col.Br.cBr
    rw [List.map_flatten, List.prod_flatten, List.map_map, List.map_ofFn, List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Function.comp_def, List.map_map, Finset.prod_map_toList]
    refine Finset.prod_congr rfl fun v _ => ?_
    unfold bmChi
    refine Finset.prod_congr rfl fun j _ => ?_
    have h1 := lamN_cast lam j
    have h2 := natW_low hE j
    have h3 := hI j
    simp only
    omega
  · intro K _
    unfold Formalism.L2.Col.Br.xiBr xiB
    rw [map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, map_pow, rename_initMinor, rename_initMinor, ha, hb]
    congr 2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramFrameEmbeddingMatrixNormOfVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramFrameEmbeddingMatrixNormOfVector
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.DefPt

theorem isGram_matNorm : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → IsGram (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) (matNorm Y) ∧ HasGram (matNorm Y) := by
  intro K _ _ ι _ _ Y hY
  have h : IsGram (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) (matNorm Y) := by
    intro v
    have hu : IsUnit (Y v.embedding).det := (hY _).isUnit
    refine ⟨Matrix.isUnit_nonsing_inv_det _ hu, fun x => ?_⟩
    have hv : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K ι) v x = fun j => v.embedding (x j) := by
      funext j
      simp [Formalism.HermitianLatticesTheory.vecAt]
    simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord, matNorm, Matrix.nonsing_inv_nonsing_inv _ hu, hv]
  exact ⟨h, h.hasGram⟩

end GlobalTheory.DefPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramFrameEmbeddingMatrixNormOfVectorStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGramFrame_embeddingMatrixNormOfVector : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : (K →+* ℂ) → Matrix ι ι ℂ), (∀ σ, (Y σ).det ≠ 0) → IsGram (Pi.basisFun K ι) (fun v => (Y v.embedding)⁻¹) (matNorm Y) ∧ HasGram (matNorm Y) := by
  first | exact @GlobalTheory.DefPt.isGram_matNorm | exact GlobalTheory.DefPt.isGram_matNorm | (intros; apply GlobalTheory.DefPt.isGram_matNorm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLastZeroInclusion
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare


open GlobalTheory.Branching.AddColumn in
theorem exists_eq_incl_of_last_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin (n + 1) → ℕ), ν (Fin.last n) = 0 → ∀ x ∈ dualWeyl K (n + 1) (n + 1) ν, ∃ x' ∈ dualWeyl K (n + 1) n (fun i => ν i.castSucc), x = incl K n x' := by
  intro K _ _ n ν hν x hx
  have hinj : Function.Injective
      (Prod.map id Fin.castSucc : Fin (n + 1) × Fin n → Fin (n + 1) × Fin (n + 1)) :=
    Function.injective_id.prodMap (Fin.castSucc_injective n)
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hx ⊢
  obtain ⟨x', rfl⟩ := exists_rename_eq_of_vars_subset_range x _ hinj (by
    rintro ⟨a, s⟩ hv
    induction s using Fin.lastCases with
    | cast s => exact ⟨(a, s), rfl⟩
    | last =>
      exfalso
      obtain ⟨d, hd, hvd⟩ := (mem_vars_iff_mem_support _).1 (Finset.mem_coe.1 hv)
      have h := congrFun (hx.1 (mem_support_iff.1 hd)) (Fin.last n)
      rw [hν, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero_iff] at h
      have h2 := h _ hvd
      simp [colW] at h2
      exact Finsupp.mem_support_iff.1 hvd h2)
  refine ⟨x', ⟨fun u hu => ?_, fun l j hlj => ?_⟩, rfl⟩
  · rw [← coeff_rename_mapDomain _ hinj] at hu
    funext i
    rw [← (weight_mapDomain (n + 1) n u).1, hx.1 hu]
  · have h := hx.2 l.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.2 hlj)
    rw [colAddGen_rename_castSucc] at h
    apply rename_injective _ (Option.map_injective hinj)
    rw [h, rename_rename, rename_rename]
    rfl

end GlobalTheory.BrCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCompactSecondCountable
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG Matrix GlobalTheory.BorelUMod
open scoped NNReal Pointwise

noncomputable section
namespace GlobalTheory.LineUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem locCompact_secondCountable [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) :
    LocallyCompactSpace L ∧ SecondCountableTopology L := by
  obtain ⟨-, hv, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := L)).2 ⟨inferInstance, (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (by
        refine ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  constructor
  · open scoped Valued in exact inferInstance
  · open scoped Valued in exact inferInstance


open UpLatIndex in
theorem distribHaarChar_eq [CompleteSpace L] [LocallyCompactSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ}
    (h : IsUnramInv ϖ σ q) (u : Lˣ) : (distribHaarChar L u : ℝ) = (q : ℝ) ^ (-2 * ordL (u : L)) := by
  have hq : q ≠ 0 := by have := h.2.2.2.2.2.1; omega
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  haveI := (locCompact_secondCountable h).2
  borelize L
  let μ : Measure L := Measure.addHaar
  have key : ∀ k K : ℤ, k ≤ K → μ.real (ordBall L k) = (q : ℝ) ^ (2 * (K - k)) * μ.real (ordBall L K) := by
    intro k K hk
    have e := relIndex_ordBall h hk
    haveI : ((ordBall L K).addSubgroupOf (ordBall L k)).FiniteIndex :=
      ⟨ne_of_eq_of_ne e (pow_ne_zero _ (pow_ne_zero _ hq))⟩
    have := GlobalTheory.BaseModule.addRelIndex_mul_measure (ordBall L K) (ordBall L k) (ordBall_mono hk)
      (isOpen_vball h.2.2.2.1 K).measurableSet μ
    rw [Measure.real, ← this, e, ENNReal.toReal_mul, ENNReal.toReal_natCast, ← pow_mul, Nat.cast_pow, ← zpow_natCast,
      Measure.real]
    congr 2
    omega
  have hs : u • (ordBall L 0 : Set L) = ordBall L (ordL (u : L)) := by
    ext x
    obtain ⟨y, rfl⟩ := MulAction.surjective u x
    beta_reduce
    rw [Set.smul_mem_smul_set_iff, SetLike.mem_coe, SetLike.mem_coe, mem_ordBall, mem_ordBall, Units.smul_def,
      smul_eq_mul, map_mul, v_eq_exp u.ne_zero, neg_zero, WithZero.exp_zero]
    exact (mul_le_iff_le_one_right WithZero.exp_pos).symm
  have h1 := congrArg ENNReal.toReal (distribHaarChar_mul μ u (ordBall L 0 : Set L))
  rw [hs, ENNReal.toReal_mul, ENNReal.coe_toReal, ← Measure.real, ← Measure.real,
    key 0 |ordL (u : L)| (abs_nonneg _), key (ordL (u : L)) _ (le_abs_self _), ← mul_assoc] at h1
  have hpos : μ.real (ordBall L |ordL (u : L)|) ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨(isOpen_vball h.2.2.2.1 _).measure_ne_zero μ ⟨0, zero_mem (ordBall L _)⟩,
      (isCompact_vball h _).measure_ne_top⟩
  have h2 := mul_right_cancel₀ hpos h1
  rw [eq_comm, ← mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hq'), ← _root_.zpow_neg, ← zpow_add₀ hq'] at h2
  rw [← h2]
  congr 1
  ring

section Mat
omit [Valued L (WithZero (Multiplicative ℤ))]

variable (x y : Fin n → L) (z : L)

end Mat

variable {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) (hc : Continuous σ)



variable {θ d : L} (hθ : θ + σ θ = 1) (hd : σ d = -d) (hd0 : d ≠ 0)



end GlobalTheory.LineUMod
end
end
