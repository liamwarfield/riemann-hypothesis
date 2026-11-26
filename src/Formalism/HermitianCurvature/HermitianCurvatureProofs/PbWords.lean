module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointCornerScaledSingleComm

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section defs

variable {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def Proper (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n) (Cs : Set (B.Mat k n))
    (U : Set (B.Mat k n)) : Prop :=
  ∀ y ∈ U, ∃ V ∈ 𝓝 y, ∃ K : Set (PBQ.XP k p ρ), IsCompact K ∧ ∀ g ∈ V, g ∈ B.GV k n → ∀ x, PBQ.GoodP Bj x → x ∉ K →
    ∀ ξ, PBG.InR B0 ξ → D.castM e (PBQ.sP Bj x) * g * Matrix.of ξ.2 * Matrix.of ξ.1 ∉ Cs

end defs

def PbWords : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n),
    B0.z = D.castV e (liftVec k p ρ Bj.z) →
    ∀ (i : ℕ) (hi : i ≤ n) (H : B.Mat k n → (Wq →L[ℂ] Wp)) (Cs : Set (B.Mat k n)),
    (∀ g ∈ B.GV k n, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g) →
    IsCompact Cs → (∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) →
    ∀ U : Set (B.Mat k n), IsOpen U → (∀ g ∈ U, Dmin k n B0.z B0.z' g ⟨i, by omega⟩ ≠ 0) →
    Proper Bj B0 e Cs U →
    ∀ (w : List C.Letter) (ew : Wd.Ix (Fin w.length)), ∀ y ∈ U, y ∈ B.GV k n →
      D.uwG k n B0.z B0.z' (PBQ.pbF Bj B0 e H) i hi w ew y =
        PBQ.pbF Bj B0 e (D.uwG k n B0.z B0.z' H i hi w ew) y

def PbLoc : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq) (e : p + ρ = n),
    B0.z = D.castV e (liftVec k p ρ Bj.z) →
    ∀ (H : B.Mat k n → (Wq →L[ℂ] Wp)) (Cs : Set (B.Mat k n)),
    B.CkOn ⊤ (B.GV k n) H → IsCompact Cs → (∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) →
    ∀ U : Set (B.Mat k n), IsOpen U → Proper Bj B0 e Cs U →
    ∀ y ∈ U, y ∈ B.GV k n → CapelliWordSumExpansion.Loc ⊤ (PBQ.pbF Bj B0 e H) y

end Formalism.FourierDecayAlt.P.PartialBesselProperness
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX_UwTop
noncomputable section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXUw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gloc

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def LocOpG (T : (B.Mat k r → E) → (B.Mat k r → E)) : Prop :=
  ∀ O : Set (B.Mat k r), IsOpen O → ∀ f₁ f₂ : B.Mat k r → E, (∀ x ∈ O, x ∈ B.GV k r → f₁ x = f₂ x) →
    ∀ x ∈ O, x ∈ B.GV k r → T f₁ x = T f₂ x

theorem locOpG_top (u : ℂ) (a b : Fin (2 * r + k + 1)) :
    LocOpG (k := k) (r := r) (E := E) (Formalism.QuantumDeterminants.Top (EabH (Hpk k r)) u a b) := by
  intro O hO f₁ f₂ h x hx hxG
  exact PBG.top_congr' O hO u a b h x hx hxG

theorem locOpG_foldr : ∀ (L : List ((B.Mat k r → E) → (B.Mat k r → E))), (∀ T ∈ L, LocOpG T) →
    LocOpG (fun f => L.foldr (fun T h => T h) f)
  | [], _ => fun _ _ _ _ h => h
  | T :: L, hL => by
    intro O hO f₁ f₂ h x hx hxG
    simp only [List.foldr_cons]
    exact hL T List.mem_cons_self O hO _ _
      (locOpG_foldr L (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) O hO f₁ f₂ h) x hx hxG

theorem locOpG_qminorOp {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    LocOpG (k := k) (r := r) (E := E) (qminorOp (EabH (Hpk k r)) a b u) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine locOpG_foldr _ (fun T hT => ?_) O hO f₁ f₂ h x hx hxG
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT
  exact locOpG_top _ _ _

theorem locOpG_AAop (m : ℕ) (hm : m ≤ r) (u : ℂ) : LocOpG (k := k) (r := r) (E := E) (C3.AAop k r m hm u) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [C3.AAop]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [locOpG_qminorOp _ _ _ O hO f₁ f₂ h x hx hxG]
  · rfl

theorem locOpG_AAvop (m : ℕ) (hm : m ≤ r) (ell : ℂ) :
    LocOpG (k := k) (r := r) (E := E) (C3.AAvop k r m hm ell) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [C3.AAvop]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [locOpG_qminorOp _ _ _ O hO f₁ f₂ h x hx hxG]
  · rfl

theorem locOpG_vLet (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) :
    LocOpG (k := k) (r := r) (E := E) (D.vLet k r z z' j hj l e) := by
  intro O hO f₁ f₂ h x hx hxG
  simp only [D.vLet]
  split_ifs
  · rfl
  · rw [locOpG_AAop _ _ _ O hO f₁ f₂ h x hx hxG]
  · rw [locOpG_AAvop _ _ _ O hO f₁ f₂ h x hx hxG]

theorem uwG_congrG (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) {O : Set (B.Mat k r)} (hO : IsOpen O)
    {f₁ f₂ : B.Mat k r → E} (h : ∀ x ∈ O, x ∈ B.GV k r → f₁ x = f₂ x) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ x ∈ O, x ∈ B.GV k r →
      D.uwG k r z z' f₁ j hj w e x = D.uwG k r z z' f₂ j hj w e x
  | [], _ => h
  | l :: w, e => by
    intro x hx hxG
    simp only [D.uwG]
    exact locOpG_vLet z z' j hj l _ O hO _ _ (uwG_congrG z z' j hj hO h w _) x hx hxG

theorem top_zero (u : ℂ) (a b : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Top (EabH (Hpk k r)) u a b (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [Formalism.QuantumDeterminants.Top, smul_zero, ite_self, zero_add]
  exact PBG.eabH_zero a b g

theorem foldr_zero : ∀ (L : List ((B.Mat k r → E) → (B.Mat k r → E))),
    (∀ T ∈ L, T (fun _ => 0) = fun _ => 0) → L.foldr (fun T h => T h) (fun _ => (0 : E)) = fun _ => 0
  | [], _ => rfl
  | T :: L, hL => by
    simp only [List.foldr_cons]
    rw [foldr_zero L (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))]
    exact hL T List.mem_cons_self

theorem qminorOp_zero {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    qminorOp (EabH (Hpk k r)) a b u (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  unfold qminorOp
  apply Finset.sum_eq_zero
  intro σ _
  rw [foldr_zero _ (fun T hT => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT; exact top_zero _ _ _)]
  funext g
  simp

theorem AAop_zero (m : ℕ) (hm : m ≤ r) (u : ℂ) : C3.AAop k r m hm u (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [C3.AAop]
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem AAvop_zero (m : ℕ) (hm : m ≤ r) (ell : ℂ) :
    C3.AAvop k r m hm ell (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [C3.AAvop]
  apply Finset.sum_eq_zero
  intro c _
  split_ifs
  · rw [qminorOp_zero]; simp
  · rfl

theorem vLet_zero (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) (l : C.Letter) (e : Fin 2) :
    D.vLet k r z z' j hj l e (fun _ : B.Mat k r => (0 : E)) = fun _ => 0 := by
  funext g
  simp only [D.vLet]
  split_ifs
  · rfl
  · rw [AAop_zero]; simp
  · rw [AAvop_zero]; simp

theorem uwG_zero (z z' : Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)),
      D.uwG k r z z' (fun _ : B.Mat k r => (0 : E)) j hj w e = fun _ => 0
  | [], _ => rfl
  | l :: w, e => by
    simp only [D.uwG]
    rw [uwG_zero z z' j hj w _]
    exact vLet_zero z z' j hj l _

end gloc

theorem continuous_gN {k r : ℕ} : Continuous (fun g : B.Mat k r => B.gN g) := by
  unfold B.gN
  fun_prop

theorem topCls_uwG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : CutEX.TopCls Bs F) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) :
    CutEX.TopCls Bs (D.uwG k r Bs.z Bs.z' F r le_rfl w e) := by
  obtain ⟨⟨hsm, ⟨R, hR⟩, ⟨ε, hε, hεG⟩⟩, ⟨K, hK, h0K, hDK⟩⟩ := hF
  let S : Set (B.Mat k r) := {x | x ∈ B.GV k r ∧ F x ≠ 0}
  have hDc : Continuous (fun x : B.Mat k r => Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _).continuous
  have hvan : ∀ x ∈ (closure S)ᶜ, x ∈ B.GV k r → D.uwG k r Bs.z Bs.z' F r le_rfl w e x = 0 := by
    intro x hx hxG
    have hz : ∀ y ∈ (closure S)ᶜ, y ∈ B.GV k r → F y = (fun _ => (0 : Wq →L[ℂ] Wp)) y := by
      intro y hy hyG
      by_contra hne
      exact hy (subset_closure ⟨hyG, hne⟩)
    rw [uwG_congrG Bs.z Bs.z' r le_rfl isClosed_closure.isOpen_compl hz w e x hx hxG, uwG_zero]
  have hcl : ∀ x, x ∈ B.GV k r → D.uwG k r Bs.z Bs.z' F r le_rfl w e x ≠ 0 → x ∈ closure S := by
    intro x hxG hne
    by_contra hx
    exact hne (hvan x hx hxG)
  have hDcl : ∀ x ∈ closure S, Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩ ∈ K := by
    have hsub : S ⊆ (fun x => Dmin k r Bs.z Bs.z' x ⟨r, by omega⟩) ⁻¹' K := fun x hx => hDK x hx.1 hx.2
    exact fun x hx => closure_minimal hsub (hK.isClosed.preimage hDc) hx
  refine ⟨⟨?_, ⟨R, ?_⟩, ⟨ε, hε, ?_⟩⟩, ⟨K, hK, h0K, ?_⟩⟩
  · intro g₀ hg₀
    by_cases hD : Dmin k r Bs.z Bs.z' g₀ ⟨r, by omega⟩ = 0
    · have hg₀S : g₀ ∈ (closure S)ᶜ := fun h => h0K (hD ▸ hDcl g₀ h)
      exact ⟨(closure S)ᶜ, fun _ => 0, isClosed_closure.isOpen_compl, hg₀S, contDiffOn_const,
        fun x hx hxG => hvan x hx hxG⟩
    · exact PBG.uwG_mem Bs.z Bs.z' r le_rfl hsm w e g₀ hD hg₀
  · intro g hg hne
    have hsub : S ⊆ {x | B.gN x ≤ R} := fun x hx => hR x hx.1 hx.2
    exact closure_minimal hsub (isClosed_le continuous_gN continuous_const) (hcl g hg hne)
  · intro g hg hne
    have hsub : S ⊆ {x | ε ≤ Gf k r Bs.z Bs.z' x} := fun x hx => hεG x hx.1 hx.2
    exact closure_minimal hsub (isClosed_le continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _)) (hcl g hg hne)
  · intro g hg hne
    exact hDcl g (hcl g hg hne)

end Formalism.FourierDecayAlt.P.CutEXUw

namespace Formalism.FourierDecayAlt.P

theorem unipotent_weight_top : CutEX.UwTop := by
  intro Wp Wq _ _ _ _ _ _ P p F hF w e
  exact CutEXUw.topCls_uwG p.T.base F hF w e

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLNf
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem zfull_zb {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (a b : Fin (j + 1)) :
    zfull Z τ a b = C3.Zb j 1 Z τ a.val b.val := by
  rw [zfull_apply]
  unfold C3.Zb
  have := a.isLt; have := b.isLt
  by_cases h1 : a.val < j ∧ b.val < j
  · rw [dite_eq_left h1, dite_eq_left h1.1, dite_eq_left h1.2]
  · rw [dite_eq_right h1]
    by_cases ha : a.val < j
    · have hb : ¬ b.val < j := fun hb => h1 ⟨ha, hb⟩
      rw [dite_eq_left ha, dite_eq_right hb, if_neg (fun h => by omega)]
    · rw [dite_eq_right ha]
      by_cases h2 : a.val = j ∧ b.val = j
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem normal_form_x0 : NormalFormsAtBasePoint := by
  intro k r j hj Z τ γ hZ hτ hγ
  refine ⟨fun a p ha => ?_, fun a p ha => ?_⟩
  · rw [upper_minor_of_level_point hj Z τ γ a p ha]
    by_cases hp : p.val < j + 1
    · rw [dite_eq_left hp, if_pos hp]
      exact zfull_zb Z τ _ _
    · rw [dite_eq_right hp, if_neg hp]
  · rw [lower_minor_of_level_point hj hZ hτ hγ a p ha]
    by_cases hp : r + k < p.val ∧ 2 * r + k - p.val < j + 1
    · rw [dite_eq_left hp, if_pos hp]
      exact congrArg star (zfull_zb Z τ _ _)
    · rw [dite_eq_right hp, if_neg hp]

theorem leading_minors_at_base_point : LeadingMinorsAtBasePoint := by
  intro k r j hj z z' Z τ γ hZ hτ hγ
  have hnf := (normal_form_x0 k r j hj Z τ γ hZ hτ hγ).1
  have hd := Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb j 1 Z τ
  refine ⟨?_, ?_⟩
  · rw [PBG.dmin_nf z z' _ j 1 Z τ hj hnf j (by omega), hd.1]
  · rw [PBG.dmin_nf z z' _ j 1 Z τ hj hnf (j + 1) le_rfl, hd.2]
    simp [C3.sgnW]

theorem first_component_of_parts : Comp1OfParts := by
  intro hNf k r j hj z z' E _ _ Dm Φ Z γ τ hH Y
  obtain ⟨hz, hz', hD, hDs, hR, hZ, hτ, hγ, hx⟩ := hH
  obtain ⟨hnf, hnfy⟩ := hNf k r j hj Z τ γ hZ hτ hγ
  have hxG : x0 k r j hj Z τ γ ∈ B.GV k r := x0_GV hj hZ hτ hγ
  have hx1 : x0 k r j hj Z τ γ ∈ Q.Glev k r 0 ∩ Dm := ⟨⟨hxG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hx⟩
  have hK : Q.SmoothLev k r 0 Dm Φ := hR.1
  have hRule : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ p q, C3.InNp k r p q → Q.EH k r p q Φ g = C3.dpsiP k r z' p q • Φ g :=
    fun g hg p q hpq => Formalism.FourierDecayAlt.P.rule_of_eq E k r z' Φ g hz' (fun n hn => (hR.2.1 g hg n hn).2) p q hpq
  refine ⟨?_, ?_⟩
  · have h := PBG.letter_plus_component_one_eq_smul_component_zero hD z z' j 1 le_rfl hj Z τ hZ hτ _ hx1 hnf Φ hK hRule Y
    rw [show ((-1 : ℂ) ^ (1 - 1) * τ⁻¹) = τ⁻¹ by simp] at h
    exact h
  · have h := PBG.letter_minus_component_one_eq_smul_component_zero hD z z' j 1 le_rfl hj Z τ hZ hτ _ hx1 hxG hnf hnfy Φ hK hRule Y
    rw [show ((-1 : ℂ) ^ (1 - 1) * (conj τ)⁻¹) = (conj τ)⁻¹ by simp] at h
    exact h

theorem headLetter_of_open (hL : LeftActionRuleAtBasePoint) (hT : TorusDirectionAtBasePoint) (hSL : ConjugateActionRuleAtBasePoint) (hST : ConjugateTorusDirectionAtBasePoint)
    (hFX : FrozenX) (hFV : FrozenV) (hPP : PlusPosOfParts) (hPZ : PlusZeroOfParts) (hMP : MinusPosOfParts)
    (hMZ : MinusZeroOfParts) : LevelPointCoordinates.HeadLetter :=
  headLetter_of_leaves normal_form_x0 leading_minors_at_base_point hL hT hSL hST hFX hFV first_component_of_parts hPP hPZ hMP hMZ

end Formalism.FourierDecayAlt.P.CutHL
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkCpt
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX.MkCptPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section casts

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def castBS {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) : B.RealPlaceData k b Wp Wq := e ▸ Bs

theorem castBS_z_eq_castV {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) : (castBS e Bs).z = D.castV e Bs.z := by
  subst e
  rfl

theorem castBS_z'_eq_castV {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) : (castBS e Bs).z' = D.castV e Bs.z' := by
  subst e
  rfl

theorem cptCoef_castF {k a b : ℕ} (e : a = b) (Bs : B.RealPlaceData k a Wp Wq) (G : B.Mat k b → (Wq →L[ℂ] Wp))
    (h : KB.CptCoef (castBS e Bs) G) : KB.CptCoef Bs (D.castF e G) := by
  subst e
  exact h

end casts

theorem glev_last_iff {k ρ : ℕ} (hρ : ρ = 0) (g : B.Mat k ρ) :
    g ∈ Q.Glev k ρ (Fin.last ρ) ↔ g ∈ B.GV k ρ := by
  subst hρ
  exact Formalism.FourierDecayAlt.P.JCx2.sq_glev0 g

theorem gf_eq_ggl {k ρ : ℕ} (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (g : B.Mat k ρ) :
    Gf k ρ z z' g = Q.GGl k ρ z z' g := by
  subst hρ
  have h0 : Dmin k 0 z z' g ⟨0, by omega⟩ = 1 := by
    unfold Dmin
    exact Matrix.det_isEmpty
  have h1 : Dmin k 0 z z' g (Fin.last 1) = Zhat k 0 z z' g (Fin.last 0) (Fin.last 0) := by
    unfold Dmin
    exact Matrix.det_fin_one _
  unfold Gf Q.GGl
  rw [Formalism.FourierDecayAlt.P.PBI.zetaL_eq_zhat, h0, h1]
  simp

end Formalism.FourierDecayAlt.P.CutEX.MkCptPf

namespace Formalism.FourierDecayAlt.P.CutEX.MkCptPf

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem lowV_top {k r : ℕ} (T : D.LevTower k r Wp Wq) (e : r = r + (r - r)) :
    U.lowV k r (r - r) (D.castV e T.base.z) = (T.bs r).z := by
  have hzl := (T.z_lev r le_rfl).symm
  change T.base.z = _ at hzl
  rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
  exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _

theorem lowV_top' {k r : ℕ} (T : D.LevTower k r Wp Wq) (e : r = r + (r - r)) :
    U.lowV k r (r - r) (D.castV e T.base.z') = (T.bs r).z' := by
  have hzl := (T.z'_lev r le_rfl).symm
  change T.base.z' = _ at hzl
  rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
  exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec rfl _ _

end top

theorem mkCpt : MkCpt := by
  intro Wp Wq _ _ _ _ _ _ P p b b' hb hbc hb' hb'c Φ hΦ K hK hKU hsupp
  have hρ : P.r - P.r = 0 := Nat.sub_self _
  have e : P.r = P.r + (P.r - P.r) := by omega
  have hz : U.lowV P.k P.r (P.r - P.r) (castBS e p.T.base).z = (p.T.bs P.r).z := by
    rw [castBS_z_eq_castV]; exact lowV_top p.T e
  have hz' : U.lowV P.k P.r (P.r - P.r) (castBS e p.T.base).z' = (p.T.bs P.r).z' := by
    rw [castBS_z'_eq_castV]; exact lowV_top' p.T e
  have hUTo : IsOpen (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') := by
    have c1 : Continuous (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) :=
      Continuous.matrix_det continuous_fst
    have c2 : Continuous (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) =>
        Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of q.2)) :=
      (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous _ _ _ _).comp continuous_snd
    exact (isOpen_ne_fun c1 continuous_const).inter (isOpen_lt continuous_const c2)
  have hCpt : KB.CptCoef (castBS e p.T.base) (PBI.chartCoefficient b b' Φ) := by
    refine PBI.chartCoefficient_hasCompactSupport (castBS e p.T.base) b b' hb hbc hb' hb'c Φ (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z')
      hUTo ?_ K hK hKU ?_ ?_
    · intro q₀ hq₀ hG
      obtain ⟨U', F, hU', hq, hF, hEq⟩ := hΦ q₀ hq₀ ((glev_last_iff hρ _).2 hG)
      exact ⟨U', F, hU', hq, hF, fun q hqU hqG => hEq q hqU ((glev_last_iff hρ _).2 hqG)⟩
    · intro q hq
      obtain ⟨h1, h2⟩ := hKU hq
      refine ⟨h1, ?_⟩
      rw [hz, hz', gf_eq_ggl hρ]
      exact h2
    · intro q hG hq
      exact hsupp q ((glev_last_iff hρ _).2 hG) hq
  refine ⟨cptCoef_castF e p.T.base _ hCpt,
    (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) '' K,
    hK.image (Continuous.matrix_det continuous_fst), ?_, ?_⟩
  · rintro ⟨q, hq, h0⟩
    exact (hKU hq).1 h0
  · intro g hg hne
    have hg' : D.castM e g ∈ B.GV P.k (P.r + (P.r - P.r)) := Formalism.FourierDecayAlt.P.PBE.castM_GV e hg
    have hne' : PBI.chartCoefficient b b' Φ (D.castM e g) ≠ 0 := hne
    have hD : U.DjU P.k P.r (P.r - P.r) (D.castM e g) ≠ 0 := by
      intro h0; apply hne'; unfold PBI.chartCoefficient; rw [if_neg (not_not.2 h0)]
    obtain ⟨-, hμ, heq⟩ := PBI.chart_spec (D.castM e g) hg' hD
    have hmk := hne'
    unfold PBI.chartCoefficient at hmk
    rw [if_pos hD] at hmk
    obtain ⟨-, hΦne⟩ := smul_ne_zero_iff.1 hmk
    have hμ' : Matrix.of (PBI.chart (Matrix.of.symm (D.castM e g))).2.2 ∈ B.GV P.k (P.r - P.r) := by
      simpa only [PBI.chart, Equiv.apply_symm_apply] using hμ
    have hK' : (PBI.chart (Matrix.of.symm (D.castM e g))).2 ∈ K := by
      by_contra hn
      exact hΦne (hsupp _ ((glev_last_iff hρ _).2 hμ') hn)
    refine ⟨_, hK', ?_⟩
    have hpsi : PBI.psiC (PBI.chart (Matrix.of.symm (D.castM e g))) = D.castM e g := by
      unfold PBI.psiC PBI.chart
      simp only [Equiv.apply_symm_apply]
      exact heq.symm
    have e1 := PBI.djU_psiC (PBI.chart (Matrix.of.symm (D.castM e g)))
    rw [hpsi] at e1
    show (Matrix.of (PBI.chart (Matrix.of.symm (D.castM e g))).2.1).det = _
    rw [← e1, ← Formalism.FourierDecayAlt.P.hat_z_minimum_degree P.k P.r (P.r - P.r) (D.castV e p.T.base.z) (D.castV e p.T.base.z'),
      Formalism.FourierDecayAlt.P.PBG.Dmin_castM e _ _ g P.r, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV,
      Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self, Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self]

end Formalism.FourierDecayAlt.P.CutEX.MkCptPf

namespace Formalism.FourierDecayAlt.P

theorem compact_truncation_construction : CutEX.MkCpt := CutEX.MkCptPf.mkCpt

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftRuleLevelPoint
open Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section hpart

variable {k r j : ℕ}

theorem hpk_row_eI (l : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r (eI k r c) l = if l = esI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem single_mul_hpk_eI (p : Fin (2 * r + k + 1)) (c : Fin r) (x : ℂ) :
    Matrix.single p (eI k r c) x * Hpk k r = Matrix.single p (esI k r c) x := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r c)]
  · rw [hpk_row_eI]
    by_cases hi : i = p <;> by_cases hl : l = esI k r c <;> simp [Matrix.single_apply, hi, hl, eq_comm]
  · intro m _ hm; simp [Matrix.single_apply, Ne.symm hm]
  · simp

theorem hpart1_single (hj : j + 1 ≤ r) (b : Fin j) :
    hpart1 (Hpk k r) (Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) b.castSucc (1 / 2) := by
  unfold hpart1 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, single_mul_hpk_eI,
    smul_sub]
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h2]
  rfl

theorem hpart2_single (hj : j + 1 ≤ r) (b : Fin j) :
    hpart2 (Hpk k r) (Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) b.castSucc (1 / (2 * Complex.I)) := by
  unfold hpart2 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_eI, single_mul_hpk_eI,
    smul_add]
  have h2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp [Complex.conj_I]
  rw [h2, neg_smul, sub_neg_eq_add]
  rfl

theorem nN_smul_real (hj : j + 1 ≤ r) (a : Fin j → ℂ) (t : ℝ) :
    nN k r j hj (fun c => (t : ℂ) * a c) = (t : ℂ) • nN k r j hj a := by
  unfold nN
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_sub, smul_smul, smul_smul, map_mul, Complex.conj_ofReal]

theorem ell_nL (hj : j + 1 ≤ r) (hj1 : 1 ≤ j) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (a : Fin j → ℂ) :
    ell k r z (nL k r j hj a) = -conj (a ⟨j - 1, by omega⟩) := by
  unfold ell
  rw [Finset.sum_eq_single (⟨j - 1, by omega⟩ : Fin r)]
  · rw [dite_eq_left (show j - 1 + 1 < r by omega), SingleEntryHermitianProducts.nL_apply, Matrix.one_apply_ne (by simp [eI, Fin.ext_iff]),
      zero_add, Finset.sum_eq_single (⟨j - 1, by omega⟩ : Fin j)]
    · have e2 : eI k r ⟨j - 1 + 1, by omega⟩ = eI k r ⟨j, by omega⟩ := by ext; simp [eI]; omega
      rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub, e2]
      rw [show (eI k r ⟨((⟨j - 1, by omega⟩ : Fin j) : ℕ), by omega⟩ : Fin (2 * r + k + 1)) = eI k r ⟨j - 1, by omega⟩
        from rfl, Matrix.single_apply_same, mul_one]
    · intro b _ hb
      rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub,
        Matrix.single_apply_of_row_ne, mul_zero, neg_zero]
      intro h
      apply hb
      have := congrArg Fin.val h
      simp only [eI] at this
      exact Fin.ext this
    · simp
  · intro a' _ ha'
    have hne : a'.val ≠ j - 1 := fun h => ha' (Fin.ext h)
    split_ifs with h
    · rw [SingleEntryHermitianProducts.nL_apply, Matrix.one_apply_ne (by simp [eI, Fin.ext_iff]), zero_add]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub, Matrix.single_apply]
      rw [if_neg, mul_zero, neg_zero]
      rintro ⟨h1, h2⟩
      have e1 := congrArg Fin.val h1; have e2 := congrArg Fin.val h2
      simp only [eI] at e1 e2
      omega
    · have hrow : ∀ q, nL k r j hj a (eI k r a') q = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a') q := by
        intro q
        rw [SingleEntryHermitianProducts.nL_apply, Finset.sum_eq_zero, add_zero]
        intro b _
        rw [Matrix.single_apply_of_row_ne (SingleEntryHermitianProducts.eI_ne_esI _ _).symm, mul_zero, zero_sub, Matrix.single_apply]
        rw [if_neg, mul_zero, neg_zero]
        rintro ⟨h1, _⟩
        have e1 := congrArg Fin.val h1
        simp only [eI] at e1
        have := b.isLt
        omega
      rw [Matrix.mulVec, dotProduct]
      simp_rw [hrow]
      rw [← dotProduct, ← Matrix.mulVec, Matrix.one_mulVec, hz _ (Or.inl (by simp [eI]))]
  · simp

end hpart

section deriv

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r j : ℕ}

theorem hpk_row_esI (l : Fin (2 * r + k + 1)) (c : Fin r) :
    Hpk k r (esI k r c) l = if l = eI k r c then 1 else 0 := by
  have hc := c.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem single_mul_hpk_esI (p : Fin (2 * r + k + 1)) (c : Fin r) (x : ℂ) :
    Matrix.single p (esI k r c) x * Hpk k r = Matrix.single p (eI k r c) x := by
  ext i l
  rw [Matrix.mul_apply, Finset.sum_eq_single (esI k r c)]
  · rw [hpk_row_esI]
    by_cases hi : i = p <;> by_cases hl : l = eI k r c <;> simp [Matrix.single_apply, hi, hl, eq_comm]
  · intro m _ hm; simp [Matrix.single_apply, Ne.symm hm]
  · simp

theorem hM_lie (hj : j + 1 ≤ r) (x y : Fin (j + 1)) (s : ℂ) :
    (hM k r j hj x y s)ᴴ * Hpk k r + Hpk k r * hM k r j hj x y s = 0 := by
  unfold hM
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul, SingleEntryHermitianProducts.single_conjT,
    SingleEntryHermitianProducts.single_conjT, star_one, star_star, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, single_mul_hpk_eI,
    single_mul_hpk_esI, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, SingleEntryHermitianProducts.hpk_mul_single_eI,
    SingleEntryHermitianProducts.hpk_mul_single_esI]
  abel

theorem psi_nL_hasDeriv (hj : j + 1 ≤ r) (hj1 : 1 ≤ j) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z)
    (a : Fin j → ℂ) :
    HasDerivAt (fun t : ℝ => psi k r z cStd (nL k r j hj (fun c => (t : ℂ) * a c)))
      (a ⟨j - 1, by omega⟩ - conj (a ⟨j - 1, by omega⟩)) 0 := by
  set R : ℝ := (cStd * -conj (a ⟨j - 1, by omega⟩)).re with hR
  have hfun : (fun t : ℝ => psi k r z cStd (nL k r j hj (fun c => (t : ℂ) * a c))) =
      fun t : ℝ => Complex.exp (Complex.I * (((t * R : ℝ)) : ℂ)) := by
    funext t
    unfold psi
    rw [ell_nL hj hj1 z hz]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, hR]
    rw [show cStd * -((t : ℂ) * conj (a ⟨j - 1, by omega⟩)) = (t : ℂ) * (cStd * -conj (a ⟨j - 1, by omega⟩)) by ring,
      Complex.re_ofReal_mul]
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => ((t * R : ℝ) : ℂ)) ((R : ℝ) : ℂ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const R).ofReal_comp
    simpa using this
  have h2 := (h1.const_mul Complex.I).cexp
  have hval : Complex.I * ((R : ℝ) : ℂ) = a ⟨j - 1, by omega⟩ - conj (a ⟨j - 1, by omega⟩) := by
    apply Complex.ext <;> simp [hR, cStd, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im] <;> ring
  rw [← hval]
  simpa using h2

theorem rdV_hM (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) (Dm : Set (Q.Mx k r)) (Ψ : Q.Mx k r → E) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))) (hj1 : 1 ≤ j) (hz : inWb k r z) (hS : Q.SmoothLev k r 0 Dm Ψ) (hZ : Z.det ≠ 0)
    (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) (hx : x0 k r j hj Z τ γ ∈ Dm)
    (hEq : ∀ a : Fin j → ℂ,
      Ψ (nL k r j hj a * x0 k r j hj Z τ γ) = psi k r z cStd (nL k r j hj a) • Ψ (x0 k r j hj Z τ γ))
    (b : Fin j) (s : ℂ) :
    RdV (hM k r j hj (Fin.last j) b.castSucc s) Ψ (x0 k r j hj Z τ γ) =
      (s * τ * Z⁻¹ b ⟨j - 1, by omega⟩ - conj (s * τ * Z⁻¹ b ⟨j - 1, by omega⟩)) • Ψ (x0 k r j hj Z τ γ) := by
  set x₁ := x0 k r j hj Z τ γ with hx₁
  have hxG : x₁ ∈ Q.Glev k r 0 := SingleEntryHermitianProducts.glev0 (x0_GV hj hZ hτ hγ)
  obtain ⟨U, F, hU, hxU, hF, hFU⟩ := hS x₁ ⟨hxG, hx⟩
  have hd : DifferentiableAt ℝ F x₁ := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
  set a : Fin j → ℂ := fun c => s * τ * Z⁻¹ b c with ha
  have hrd : RdV (hM k r j hj (Fin.last j) b.castSucc s) Ψ x₁ =
      fderiv ℝ F x₁ (x₁ * hM k r j hj (Fin.last j) b.castSucc s) :=
    (Formalism.FourierDecayAlt.P.Qx2.hasDeriv_ext hU hxU hxG ⟨hM_lie hj _ _ s, fun a ha => absurd ha (Nat.not_lt_zero _)⟩ hd
      hFU).deriv
  rw [hrd, hx₁, level_point_conj_unipotent hj hZ hτ γ b s, ← hx₁]
  have hc : HasDerivAt (fun t : ℝ => x₁ + (t : ℂ) • (nN k r j hj a * x₁)) (nN k r j hj a * x₁) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := by simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
    have := (h0.smul_const (nN k r j hj a * x₁)).const_add x₁
    rw [one_smul] at this
    exact this
  have hcF := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have hcurve : ∀ t : ℝ, x₁ + (t : ℂ) • (nN k r j hj a * x₁) = nL k r j hj (fun c => (t : ℂ) * a c) * x₁ := by
    intro t
    rw [nL_eq, nN_smul_real, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  have hev : (F ∘ fun t : ℝ => x₁ + (t : ℂ) • (nN k r j hj a * x₁)) =ᶠ[𝓝 0]
      fun t : ℝ => psi k r z cStd (nL k r j hj (fun c => (t : ℂ) * a c)) • Ψ x₁ := by
    have hUn : U ∈ 𝓝 (x₁ + ((0 : ℝ) : ℂ) • (nN k r j hj a * x₁)) := by
      rw [Complex.ofReal_zero, zero_smul, add_zero]; exact hU.mem_nhds hxU
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, x₁ + (t : ℂ) • (nN k r j hj a * x₁) ∈ U :=
      hc.continuousAt.preimage_mem_nhds hUn
    filter_upwards [hmem] with t ht
    have hG : x₁ + (t : ℂ) • (nN k r j hj a * x₁) ∈ Q.Glev k r 0 := by
      rw [hcurve t]; exact Formalism.FourierDecayAlt.P.Qx3.glev_mul (HeadLetterLemmas.nL_glev0 hj _) hxG
    simp only [Function.comp]
    rw [← hFU _ ht hG, hcurve t, hEq]
  have h2 := (psi_nL_hasDeriv hj hj1 z hz a).smul_const (Ψ x₁)
  exact (hcF.congr_of_eventuallyEq hev.symm).unique h2

theorem left_rule_level_point : CutHL.LeftActionRuleAtBasePoint := by
  intro E _ _ k r j hj z Dm Ψ Z τ γ hj1 hz hD hS hZ hτ hγ hx hEq b
  show EabH (Hpk k r) _ _ Ψ _ = _
  unfold EabH
  rw [hpart1_single hj b, hpart2_single hj b, rdV_hM E hj z Dm Ψ Z τ γ hj1 hz hS hZ hτ hγ hx hEq b,
    rdV_hM E hj z Dm Ψ Z τ γ hj1 hz hS hZ hτ hγ hx hEq b, smul_smul, ← add_smul]
  congr 1
  set w := τ * Z⁻¹ b ⟨j - 1, by omega⟩
  have e1 : (1 / 2 : ℂ) * τ * Z⁻¹ b ⟨j - 1, by omega⟩ = w / 2 := by simp only [w]; ring
  have e2 : 1 / (2 * Complex.I) * τ * Z⁻¹ b ⟨j - 1, by omega⟩ = -(Complex.I * w) / 2 := by
    simp only [w]; field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [e1, e2]
  simp only [map_div₀, map_neg, map_mul, Complex.conj_I, map_ofNat]
  ring_nf
  rw [Complex.I_sq]
  ring

end deriv

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMK2
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMK

def HB {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ)
    (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)) : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp) :=
  PBI.chartCoefficient b b' (fun Z' y' => ((β Z' : ℝ) : ℂ) • Φ Z' y')

def kapL {k p ρ : ℕ} (z : Fin (2 * ρ + k + 1) → ℂ) (b : U.RC k p ρ → ℝ) : ℂ :=
  ∫ x, (b x : ℂ) * psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x) ∂(U.muRC k p ρ)

def kapR {k p ρ : ℕ} (z' : Fin (2 * ρ + k + 1) → ℂ) (b' : U.RC k p ρ → ℝ) : ℂ :=
  ∫ x, (b' x : ℂ) * star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)) ∂(U.muRC k p ρ)

def RightAvg : Prop :=
  ∀ (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq], ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq),
    B0.z' = liftVec k p ρ Bj.z' → (∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) →
    Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl) →
    Bj.μN = D.muN k ρ → B0.μN = D.muN k (p + ρ) →
    ∀ (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)),
    Continuous b' → HasCompactSupport b' →
    ∀ Z : Fin p → Fin p → ℂ, (Matrix.of Z).det ≠ 0 →
    Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) →
    ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1 →
    ∀ y : Mt k ρ, (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ →
    (∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2))) →
    (∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') →
    ∀ h ∈ UWset k ρ Bj.z, ∀ a : U.RC k p ρ,
      PBG.Kr B0 (HB b b' β Φ) (U.Rn k p ρ (-a) * U.embG k p ρ h⁻¹ * U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) =
        (((b a : ℝ) : ℂ) * kapR Bj.z' b') • (Bj.π h⁻¹).comp (Φ Z y)

def LeftAvg : Prop :=
  ∀ (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq], ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq),
    Bj.μW Set.univ = 1 → Bj.μN = D.muN k ρ →
    ∀ (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k (p + ρ)) (b : U.RC k p ρ → ℝ) (c : ℂ)
      (A : Wq →L[ℂ] Wp), Continuous b → HasCompactSupport b →
    (∀ h ∈ UWset k ρ Bj.z, ∀ a : U.RC k p ρ,
      PBG.Kr B0 H (U.Rn k p ρ (-a) * U.embG k p ρ h⁻¹ * g) = (((b a : ℝ) : ℂ) * c) • (Bj.π h⁻¹).comp A) →
    PBQ.pbF Bj B0 rfl H g = (kapL Bj.z b * c) • A

def CoreN : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (e : p + ρ = n), ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq),
    D.castV e (liftVec k p ρ Bj.z') = B0.z' → (∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y))) →
    Bj.μW Set.univ = 1 → Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e) →
    Bj.μN = D.muN k ρ → B0.μN = D.muN k n →
    ∀ (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)),
    Continuous b → HasCompactSupport b → Continuous b' → HasCompactSupport b' →
    ∀ Z : Fin p → Fin p → ℂ, (Matrix.of Z).det ≠ 0 →
    Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) →
    ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1 →
    ∀ y : Mt k ρ, (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ →
    (∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2))) →
    (∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') →
    PBQ.pbF Bj B0 e (D.castF e.symm (HB b b' β Φ)) (D.castM e (U.mMap k p ρ (Matrix.of Z) (Matrix.of y))) =
      (kapL Bj.z b * kapR Bj.z' b') • Φ Z y

def TopMk : Prop := CoreN → CutEX.MkTop

section assembly

theorem coreRfl (hR : RightAvg) (hL : LeftAvg) (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (hρ : ρ = 0) (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq)
    (hz' : B0.z' = liftVec k p ρ Bj.z') (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y))
    (hW : Bj.μW Set.univ = 1) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k (p + ρ))
    (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp))
    (hb : Continuous b) (hbc : HasCompactSupport b) (hb' : Continuous b') (hbc' : HasCompactSupport b')
    (Z : Fin p → Fin p → ℂ) (hZ : (Matrix.of Z).det ≠ 0)
    (hβi : Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))))
    (hβ1 : ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1)
    (y : Mt k ρ) (hy : (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ)
    (hΦL : ∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2)))
    (hΦU : ∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') :
    PBQ.pbF Bj B0 rfl (HB b b' β Φ) (U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) =
      (kapL Bj.z b * kapR Bj.z' b') • Φ Z y := hL k p ρ Wp Wq hρ Bj B0 hW hNj (HB b b' β Φ) (U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) b
    (kapR Bj.z' b') (Φ Z y) hb hbc
    (fun h hh a => hR k p ρ Wp Wq hρ Bj B0 hz' hπ' hW' hW0' hNj hN0 b b' β Φ hb' hbc' Z hZ hβi hβ1 y hy
      hΦL hΦU h hh a)

theorem coreN_of (hR : RightAvg) (hL : LeftAvg) : CoreN := by
  intro k p ρ n Wp Wq _ _ _ _ _ _ e hρ Bj B0 hz' hπ' hW hW' hW0' hNj hN0 b b' β Φ hb hbc hb' hbc' Z hZ hβi hβ1 y hy
    hΦL hΦU
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl] at hz'
  have hπ'' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
  have hF : D.castF (rfl : p + ρ = p + ρ).symm (HB b b' β Φ) = HB b b' β Φ := funext fun x => by
    simp only [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rw [hF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact coreRfl hR hL k p ρ Wp Wq hρ Bj B0 hz'.symm hπ'' hW hW' hW0' hNj hN0 b b' β Φ hb hbc hb' hbc' Z hZ hβi hβ1
    y hy hΦL hΦU

theorem mkTop_of_leaves (hR : RightAvg) (hL : LeftAvg) (hT : TopMk) : CutEX.MkTop := hT (coreN_of hR hL)

end assembly

end Formalism.FourierDecayAlt.P.CutMK
end
end
