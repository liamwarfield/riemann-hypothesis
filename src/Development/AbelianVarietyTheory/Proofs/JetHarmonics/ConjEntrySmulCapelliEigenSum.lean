module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliLeftComatrix
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CkOnInCCCongrOnGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InverseEntrySmulCapelliEigenfunctionSum
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliModuleModel
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OperatorEabPreservesSmoothClassCC
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OperatorEabPreservesSmoothClassCC
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory.EabClass

theorem rdV_class {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {X : B.Mat k r}
    (hX : B.inLie k r X) {f : B.Mat k r → E} (hf : B.CkOn ⊤ (B.GV k r) f ∧ ∀ m : ℕ, B.InCC A m f) :
    B.CkOn ⊤ (B.GV k r) (RdV X f) ∧ ∀ m : ℕ, B.InCC A m (RdV X f) := by
  refine ⟨Formalism.FourierDecayAlt.P.B5.ckOn_RdV hX (by simpa using hf.1), fun m => ?_⟩
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_Rw (v := [X]) (by simpa using hX) (hf.2 _)

theorem eh_class : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (A : ℝ) (a b : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (B.CkOn ⊤ (B.GV k r) (Q.EH k r a b f) ∧ ∀ m : ℕ, B.InCC (A) m (Q.EH k r a b f)) := by
  intro k r Wp Wq _ _ _ _ _ _ A a b f hf
  have h1 := rdV_class (X := hpart1 (Hpk k r) (Matrix.single a b 1)) (Formalism.FourierDecayAlt.P.Qx2.hpart1_lie _) hf
  have h2 := rdV_class (X := hpart2 (Hpk k r) (Matrix.single a b 1)) (Formalism.FourierDecayAlt.P.Qx2.hpart2_lie _) hf
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add h1.1 (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul Complex.I h2.1), fun m => ?_⟩
  obtain ⟨c₁, hc₁⟩ := h1.2 m
  obtain ⟨c₂, hc₂⟩ := h2.2 m
  exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc₁ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul Complex.I hc₂)⟩

end GlobalTheory.EabClass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OperatorEabPreservesSmoothClassCCStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operatorEab_preserves_smooth_classCC : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (A : ℝ) (a b : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (B.CkOn ⊤ (B.GV k r) (Q.EH k r a b f) ∧ ∀ m : ℕ, B.InCC (A) m (Q.EH k r a b f)) := by
  first | exact @GlobalTheory.EabClass.eh_class | exact GlobalTheory.EabClass.eh_class | (intros; apply GlobalTheory.EabClass.eh_class <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenRealToComplex
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem entire_eq_of_eq_on_reals {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (p q : ℂ → E) (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (h : ∀ y : ℝ, p y = q y) : p = q := by
  have hp' : AnalyticOnNhd ℂ p Set.univ := fun z _ => hp.analyticAt z
  have hq' : AnalyticOnNhd ℂ q Set.univ := fun z _ => hq.analyticAt z
  refine AnalyticOnNhd.eq_of_frequently_eq (z₀ := ((0 : ℝ) : ℂ)) hp' hq' ?_
  have ht : Filter.Tendsto (fun y : ℝ => (y : ℂ)) (nhdsWithin 0 {0}ᶜ)
      (nhdsWithin ((0 : ℝ) : ℂ) {((0 : ℝ) : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      intro h0
      exact hy (Complex.ofReal_injective h0)
  exact ht.frequently (Filter.Frequently.of_forall h)

theorem capelli_eigen_real_to_complex :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) f → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∀ Y : ℂ, ∀ g ∈ B.GV k r, Q.CV k r Y f g = (∏ s, (Y + (lam s : ℂ))) • f g := by
  intro k r Wp Wq _ _ _ _ _ _ lam f hf hR Y g hg
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hs : Q.SmoothLev k r 0 Set.univ f := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀.1.1
    exact ⟨U, f', hU, hgU, hf', fun g hg hgl => hff g hg hgl.1⟩
  have hg0 : g ∈ Q.Glev k r 0 := ⟨hg, fun a ha => absurd ha (Nat.not_lt_zero _)⟩
  have h0 : Formalism.QuantumDeterminants.inWb k r 0 := by
    unfold Formalism.QuantumDeterminants.inWb
    simp
  obtain ⟨A, hA⟩ := Formalism.FourierDecayAlt.P.leading_term_alt (Wq →L[ℂ] Wp) k r 0 0 0 h0 h0
  have hpoly : (fun Y : ℂ => Q.CV k r Y f g) = fun Y : ℂ => Y ^ Q.mdim k r 0 • f g +
      ∑ j ∈ Finset.range (Q.mdim k r 0), Y ^ j • A 0 0 j f g := by
    funext Y
    exact (hA Set.univ f isOpen_univ hs g ⟨hg0, trivial⟩ Y).1
  have key := entire_eq_of_eq_on_reals (fun Y : ℂ => Q.CV k r Y f g)
    (fun Y : ℂ => (∏ s, (Y + (lam s : ℂ))) • f g) (by rw [hpoly]; fun_prop)
    (by
      refine Differentiable.smul_const ?_ _
      exact Differentiable.fun_finsetProd fun s _ => by fun_prop)
    (fun y => by
      show Q.CV k r (y : ℂ) f g = _
      rw [hR y g hg]; push_cast; rfl)
  exact congrFun key Y

end GlobalTheory
end

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

noncomputable section
namespace GlobalTheory
namespace CapelliModel

open Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.PBG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem mem_lev {g : B.Mat k r} : g ∈ Q.Glev k r 0 ∩ Set.univ ↔ g ∈ B.GV k r :=
  ⟨fun h => h.1.1, fun h => ⟨⟨h, fun a ha => absurd ha (by simp)⟩, trivial⟩⟩

theorem smooth_iff {f : B.Mat k r → F} :
    Q.SmoothLev k r 0 Set.univ f ↔ B.CkOn ⊤ (B.GV k r) f := by
  constructor
  · intro h g₀ hg₀
    obtain ⟨U, f', hU, hg, hf, he⟩ := h g₀ (mem_lev.2 hg₀)
    exact ⟨U, f', hU, hg, hf, fun g hgU hgG => he g hgU (mem_lev.2 hgG).1⟩
  · intro h g₀ hg₀
    obtain ⟨U, f', hU, hg, hf, he⟩ := h g₀ (mem_lev.1 hg₀)
    exact ⟨U, f', hU, hg, hf, fun g hgU hgG => he g hgU hgG.1⟩

theorem dLR_zero (u v : List (B.Mat k r)) : B.dLR u v (0 : B.Mat k r → F) = 0 := by
  have h1 : B.Rw v (0 : B.Mat k r → F) = 0 := by
    unfold B.Rw
    induction v with
    | nil => rfl
    | cons X v ih =>
      rw [List.foldr_cons, ih]
      funext g
      simp [RdV]
  unfold B.dLR
  rw [h1]
  induction u with
  | nil => rfl
  | cons X u ih =>
    rw [List.foldr_cons, ih]
    funext g
    simp [B.LdV]

theorem inCC_zero (A : ℝ) (m : ℕ) : B.InCC A m (0 : B.Mat k r → F) := by
  refine ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ?_⟩
  intro u v _ _ _ g _
  simp [dLR_zero]

abbrev Sm (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] := VS k r 0 Set.univ F

abbrev Eu (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (a b : Fin (2 * r + k + 1)) :
    Module.End ℂ (Sm k r F) := E0 isOpen_univ a b

theorem sm_ext (v v' : Sm k r F) (h : ∀ g ∈ B.GV k r, (v : B.Mat k r → F) g = (v' : B.Mat k r → F) g) :
    v = v' := by
  refine Subtype.ext (funext fun g => ?_)
  by_cases hg : g ∈ Q.Glev k r 0 ∩ Set.univ
  · exact h g (mem_lev.1 hg)
  · rw [v.2.2 g hg, v'.2.2 g hg]

theorem ev_Eu (a b : Fin (2 * r + k + 1)) (v : Sm k r F) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    (Eu k r F a b v : B.Mat k r → F) g = Q.EH k r a b (v : B.Mat k r → F) g := by
  have := ev_E (i := 0) isOpen_univ (c0 a) (c0 b) v (mem_lev.2 hg)
  rwa [position_level_zero_coord, position_level_zero_coord] at this

theorem qminorOp_cast {n t t' : ℕ} (h : t = t')
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → F) → (Matrix (Fin n) (Fin n) ℂ → F))
    (a : Fin t' → Fin n) (a' : Fin t → Fin n) (ha : ∀ j, a' j = a (Fin.cast h j)) (u : ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → F) : qminorOp Eop a' a' u f = qminorOp Eop a a u f := by
  subst h
  have : a' = a := funext ha
  rw [this]

theorem CV_eq (Y : ℂ) (f : B.Mat k r → F) :
    Q.CV k r Y f = qminorOp (Q.EH k r) id id (Y + (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) f := by
  have hm : Q.mdim k r 0 = 2 * r + k + 1 := by simp [Q.mdim]
  unfold Q.CV Q.capL Q.uC
  rw [qminorOp_cast hm _ id _ (fun j => by ext; simp [Q.posL]), hm]

theorem ev_qdet (Y : ℂ) (v : Sm k r F) (g : B.Mat k r) (hg : g ∈ B.GV k r) :
    (qdet (Eu k r F) (Y + (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) v : B.Mat k r → F) g =
      Q.CV k r Y (v : B.Mat k r → F) g := by
  rw [CV_eq]
  exact quantum_minor_level_eq_hat isOpen_univ id id _ v g (mem_lev.2 hg)

def eig (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (χ : ℂ → ℂ) (A : ℝ) :
    Submodule ℂ (Sm k r F) where
  carrier := {v | (∀ m : ℕ, B.InCC A m (v : B.Mat k r → F)) ∧ ∀ u : ℂ, qdet (Eu k r F) u v = χ u • v}
  zero_mem' := ⟨fun m => inCC_zero A m, fun u => by simp⟩
  add_mem' := by
    rintro v w ⟨hv, hv'⟩ ⟨hw, hw'⟩
    refine ⟨fun m => ?_, fun u => by rw [map_add (f := _), hv', hw', smul_add]⟩
    obtain ⟨c, hc⟩ := hv m
    obtain ⟨c', hc'⟩ := hw m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r F A m _ _ c c' 1 hc hc').1⟩
  smul_mem' := by
    rintro a v ⟨hv, hv'⟩
    refine ⟨fun m => ?_, fun u => by rw [map_smul, hv', smul_comm]⟩
    obtain ⟨c, hc⟩ := hv m
    exact ⟨_, (Formalism.FourierDecayAlt.P.matrix_coefficient_linear k r F A m _ _ c c a hc hc).2⟩

open Classical in
def mulOp (k r : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] (c : B.Mat k r → ℂ) :
    Module.End ℂ (Sm k r F) :=
  if h : B.CkOn ⊤ (B.GV k r) c then Mh isOpen_univ c (smooth_iff.2 h) else 0

theorem glRel_of_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V)
    (hι : Function.Injective ι) (h : ∀ a b w, ι (E' a b w) = E a b (ι w)) (hE : GlRel E) : GlRel E' := by
  intro a b c d
  refine LinearMap.ext fun w => hι ?_
  have := LinearMap.congr_fun (hE a b c d) (ι w)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, h] at this ⊢
  rw [this]
  congr 1 <;> split_ifs <;> simp [h]

end CapelliModel

open CapelliModel Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.PBG in
theorem capelli_module_model : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (A : ℝ), ∃ (V W : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : AddCommGroup W) (_ : Module ℂ W) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ V) (E' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ W) (ι : W →ₗ[ℂ] V) (ev : V →ₗ[ℂ] (B.Mat k r → (Wq →L[ℂ] Wp))) (mul : (B.Mat k r → ℂ) → Module.End ℂ V), GlRel E ∧ GlRel E' ∧ (∀ a b w, ι (E' a b w) = E a b (ι w)) ∧ (∀ (u : ℂ) (w : W), qdet E' u w = (∏ s, (u + ((lam s : ℂ) - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2))) • w) ∧ (∀ v, B.CkOn ⊤ (B.GV k r) (ev v)) ∧ (∀ v v', (∀ g ∈ B.GV k r, ev v g = ev v' g) → v = v') ∧ (∀ w, ∀ m : ℕ, B.InCC A m (ev (ι w))) ∧ (∀ f : B.Mat k r → (Wq →L[ℂ] Wp), (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∃ w, ∀ g ∈ B.GV k r, ev (ι w) g = f g) ∧ (∀ a b v, ∀ g ∈ B.GV k r, ev (E a b v) g = Q.EH k r a b (ev v) g) ∧ (∀ (Y : ℂ) v, ∀ g ∈ B.GV k r, ev (qdet E (Y + (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) v) g = Q.CV k r Y (ev v) g) ∧ (∀ c : B.Mat k r → ℂ, B.CkOn ⊤ (B.GV k r) c → (∀ v, ∀ g ∈ B.GV k r, ev (mul c v) g = c g • ev v g) ∧ ∀ a b v, ∀ g ∈ B.GV k r, ev (E a b (mul c v)) g = c g • ev (E a b v) g + Q.EH k r a b c g • ev v g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam A
  let χ : ℂ → ℂ := fun u => ∏ s, (u + ((lam s : ℂ) - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2))
  have hgl : GlRel (Eu k r (Wq →L[ℂ] Wp)) := level_zero_derivation_relation isOpen_univ
  have hst : ∀ a b, ∀ v ∈ eig k r (Wq →L[ℂ] Wp) χ A, Eu k r (Wq →L[ℂ] Wp) a b v ∈ eig k r (Wq →L[ℂ] Wp) χ A := by
    rintro a b v ⟨hv, hv'⟩
    refine ⟨fun m => ?_, fun u => ?_⟩
    · exact (GlobalTheory.ckOn_inCC_congr_on_group k r _ A _ _ (fun g hg => (ev_Eu a b v g hg).symm)).2 m
        ((GlobalTheory.T.operatorEab_preserves_smooth_classCC k r Wp Wq A a b _ ⟨smooth_iff.1 v.2.1, hv⟩).2 m)
    · have := LinearMap.congr_fun (qDetCentral _ _ _ hgl u a b) v
      rw [Module.End.mul_apply, Module.End.mul_apply, hv', map_smul] at this
      exact this
  have hint : ∀ a b (w : eig k r (Wq →L[ℂ] Wp) χ A),
      (eig k r (Wq →L[ℂ] Wp) χ A).subtype ((Eu k r (Wq →L[ℂ] Wp) a b).restrict (hst a b) w) =
        Eu k r (Wq →L[ℂ] Wp) a b ((eig k r (Wq →L[ℂ] Wp) χ A).subtype w) := fun _ _ _ => rfl
  refine ⟨Sm k r (Wq →L[ℂ] Wp), eig k r (Wq →L[ℂ] Wp) χ A, inferInstance, inferInstance, inferInstance,
    inferInstance, Eu k r (Wq →L[ℂ] Wp), fun a b => (Eu k r (Wq →L[ℂ] Wp) a b).restrict (hst a b),
    (eig k r (Wq →L[ℂ] Wp) χ A).subtype, (Sm k r (Wq →L[ℂ] Wp)).subtype, mulOp k r _, hgl,
    glRel_of_intertwine _ _ _ (Submodule.subtype_injective _) hint hgl, hint, ?_,
    fun v => smooth_iff.1 v.2.1, sm_ext, fun w => w.2.1, ?_, ev_Eu, ev_qdet, ?_⟩
  · intro u w
    apply Submodule.subtype_injective
    unfold qdet
    rw [qminor_intertwine _ _ _ _ _ _ _ hint, map_smul]
    exact w.2.2 u
  · rintro f ⟨hf, hfc⟩ hY
    have hcut : ∀ g ∈ B.GV k r, f g = (vK isOpen_univ f (smooth_iff.2 hf) : B.Mat k r → (Wq →L[ℂ] Wp)) g :=
      fun g hg => (cut_of_mem f (mem_lev.2 hg)).symm
    refine ⟨⟨vK isOpen_univ f (smooth_iff.2 hf), fun m => (GlobalTheory.ckOn_inCC_congr_on_group k r _ A _ _ hcut).2 m (hfc m),
      fun u => ?_⟩, fun g hg => (hcut g hg).symm⟩
    refine sm_ext _ _ fun g hg => ?_
    have h1 := ev_qdet (u - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) (vK isOpen_univ f (smooth_iff.2 hf)) g hg
    rw [sub_add_cancel] at h1
    have h2 := GlobalTheory.capelli_eigen_real_to_complex k r Wp Wq lam f hf hY (u - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2) g hg
    rw [CV_eq] at h1 h2
    rw [h1, ← qminorOp_loc isOpen_univ id id _ f _ (fun x hx => hcut x (mem_lev.1 hx)) g (mem_lev.2 hg), h2,
      Submodule.coe_smul, Pi.smul_apply, ← hcut g hg]
    congr 1
    exact Finset.prod_congr rfl fun s _ => by ring
  · intro c hc
    simp only [mulOp, dif_pos hc]
    refine ⟨fun v g hg => ev_M isOpen_univ (smooth_iff.2 hc) v (mem_lev.2 hg), fun a b v g hg => ?_⟩
    have := ev_EM (i := 0) isOpen_univ (c0 a) (c0 b) (smooth_iff.2 hc) v (mem_lev.2 hg)
    rw [position_level_zero_coord, position_level_zero_coord, ← ev_Eu a b v g hg] at this
    exact this

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EhInvEntry
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

open Matrix in
theorem eh_inv_entry : ∀ (k r : ℕ) (a b c i : Fin (2 * r + k + 1)), ∀ g ∈ B.GV k r, Q.EH k r a b (fun y : B.Mat k r => y⁻¹ c i) g = -(if a = c then g⁻¹ b i else 0) := by
  intro k r a b c i g _
  have h := Formalism.FourierDecayAlt.P.Qx5.eh_inv (k := k) (r := r) (LinearMap.proj c) (Pi.single i 1) g a b
  have e : (fun y : B.Mat k r => y⁻¹ c i) = fun y : B.Mat k r => (LinearMap.proj c : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (y⁻¹ *ᵥ Pi.single i 1) := by
    funext y
    simp [Matrix.mulVec_single_one]
  rw [e]
  refine h.trans ?_
  by_cases hac : a = c
  · subst hac
    simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single, hac]
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CovectorMultiplierShift
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumDetVectorMultiplierShiftPlus
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetMulVectorType
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorCommOfCommColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorCommOfCommColumns
open Formalism.REAL Finset

namespace GlobalTheory

theorem qminor_comm_of_comm_columns (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ)
    (E : Fin n → Fin n → A) (x : A) (a b : Fin t → Fin n) (u : ℂ)
    (h : ∀ (c : Fin n) (i : Fin t), E c (b i) * x = x * E c (b i)) :
    qminor E a b u * x = x * qminor E a b u := by
  have hT : ∀ (v : ℂ) (c : Fin n) (i : Fin t), Commute (Tm E v c (b i)) x := by
    intro v c i
    have h1 : Commute (E c (b i)) x := h c i
    unfold Tm
    refine Commute.add_left ?_ h1
    split_ifs
    · exact Algebra.commutes v x
    · exact Commute.zero_left x
  change Commute (qminor E a b u) x
  unfold qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  have hp : ∀ f : Fin t → A, (∀ i, Commute (f i) x) → Commute (List.ofFn f).prod x := by
    intro f hf
    refine Commute.list_prod_left _ _ fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact hf i
  exact (Int.cast_commute _ x).mul_left (hp _ fun i => hT _ _ i)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorCommOfCommColumnsStatement
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qminor_commute_of_commute_columns : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (x : A) (a b : Fin t → Fin n) (u : ℂ), (∀ (c : Fin n) (i : Fin t), E c (b i) * x = x * E c (b i)) → qminor E a b u * x = x * qminor E a b u := by
  first | exact @GlobalTheory.qminor_comm_of_comm_columns | exact GlobalTheory.qminor_comm_of_comm_columns | (intros; apply GlobalTheory.qminor_comm_of_comm_columns <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetMulVectorType
open Formalism.REAL Finset

namespace GlobalTheory

theorem qdet_mul_vector (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ)
    (E : Fin (m + 1) → Fin (m + 1) → A) (x : Fin (m + 1) → A) (hE : GlRel E)
    (hx : ∀ a b j, E a b * x j = x j * E a b + if b = j then x a else 0)
    (u : ℂ) (j : Fin (m + 1)) :
    qdet E u * x j = x j * qdet E u + ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) •
      (x a * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) := by
  have h1 := GlobalTheory.T.capelli_left_comatrix_qminor_eq A m E hE u j j
  rw [if_pos rfl] at h1
  have h2 : ∀ a : Fin (m + 1), qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1) * x j
      = x j * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1) := by
    intro a
    refine GlobalTheory.T.qminor_commute_of_commute_columns A (m + 1) m E (x j) _ _ _ ?_
    intro c i
    rw [hx, if_neg (Fin.succAbove_ne j i), add_zero]
  have h3 : ∀ a : Fin (m + 1), Tm E u a j * x j = x j * Tm E u a j + x a := by
    intro a
    have h := hx a j j
    rw [if_pos rfl] at h
    unfold Tm
    by_cases haj : a = j
    · simp only [if_pos haj, add_mul, mul_add, h, Algebra.commutes]
      abel
    · simp only [if_neg haj, zero_add, h]
  rw [← h1, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, ← smul_add, mul_assoc, h2, ← mul_assoc, h3, add_mul,
    mul_assoc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliDetMulVectorTypeStatement
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliDet_mul_vectorType : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (x : Fin (m + 1) → A), GlRel E → (∀ a b j, E a b * x j = x j * E a b + if b = j then x a else 0) → ∀ (u : ℂ) (j : Fin (m + 1)), qdet E u * x j = x j * qdet E u + ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) • (x a * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) := by
  first | exact @GlobalTheory.qdet_mul_vector | exact GlobalTheory.qdet_mul_vector | (intros; apply GlobalTheory.qdet_mul_vector <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEigenSplitOfResolventIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumEigenvectorsOfAevalProdLinearEqZeroStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumEigenvectorsOfAevalProdLinearEqZero
open Finset

namespace GlobalTheory

theorem sum_eigenvectors_of_aeval_prod_linear_eq_zero :
    ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (ν : Fin n → ℂ),
      Function.Injective ν →
      Polynomial.aeval (-Ω) (∏ s, (Polynomial.X + Polynomial.C (ν s))) = 0 →
      ∀ w : N, ∃ v : Fin n → N, (∀ s, Ω (v s) = ν s • v s) ∧ w = ∑ s, v s := by
  intro N _ _ n Ω ν hν h w
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨fun s => s.elim0, fun s => s.elim0, ?_⟩
    have h1 : (1 : Module.End ℂ N) = 0 := by simpa using h
    have h2 : w = 0 := by
      have := congrArg (fun f : Module.End ℂ N => f w) h1
      simpa using this
    simp [h2]
  · have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have hinj : Set.InjOn (fun s => -ν s) (↑(Finset.univ : Finset (Fin n))) := by
      intro a _ b _ hab
      exact hν (neg_injective hab)
    have hsum := Lagrange.sum_basis hinj hne
    refine ⟨fun s => Polynomial.aeval (-Ω) (Lagrange.basis Finset.univ (fun s => -ν s) s) w, ?_, ?_⟩
    · intro s
      have key : (Polynomial.X + Polynomial.C (ν s)) * Lagrange.basis Finset.univ (fun s => -ν s) s
          = (∏ j ∈ Finset.univ.erase s, Polynomial.C ((-ν s - -ν j)⁻¹)) *
            ∏ s, (Polynomial.X + Polynomial.C (ν s)) := by
        rw [← Finset.mul_prod_erase Finset.univ (fun s => Polynomial.X + Polynomial.C (ν s))
          (Finset.mem_univ s), Lagrange.basis]
        simp only [Lagrange.basisDivisor, Finset.prod_mul_distrib, map_neg, sub_neg_eq_add]
        ring
      have h2 := congrArg (Polynomial.aeval (-Ω)) key
      rw [map_mul, map_mul, h, mul_zero] at h2
      have h3 := congrArg (fun f : Module.End ℂ N => f w) h2
      simp only [map_add (f := _), Polynomial.aeval_X, Polynomial.aeval_C, Module.End.mul_apply,
        LinearMap.add_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
        LinearMap.zero_apply] at h3
      exact (neg_add_eq_zero.mp h3)
    · have h2 := congrArg (fun p => Polynomial.aeval (-Ω) p w) hsum
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_one, LinearMap.sum_apply, Module.End.one_apply] at h2
      exact h2.symm

end GlobalTheory
end

open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigen_decomp_of_aeval_prod_eq_zero : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → Polynomial.aeval (-Ω) (∏ s, (Polynomial.X + Polynomial.C (ν s))) = 0 → ∀ w : N, ∃ v : Fin n → N, (∀ s, Ω (v s) = ν s • v s) ∧ w = ∑ s, v s := by
  first | exact @GlobalTheory.sum_eigenvectors_of_aeval_prod_linear_eq_zero | exact GlobalTheory.sum_eigenvectors_of_aeval_prod_linear_eq_zero | (intros; apply GlobalTheory.sum_eigenvectors_of_aeval_prod_linear_eq_zero <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AevalNegEqZeroOfResolventIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AevalNegEqZeroOfResolventIdentity
open Formalism.REAL Finset

namespace GlobalTheory

theorem shift_coeff_of_eval_identity {N : Type} [AddCommGroup N] [Module ℂ N]
    (Ω : Module.End ℂ N) (M : ℕ) (a : ℕ → N) (ha : ∀ i, M ≤ i → a i = 0) (p : Polynomial ℂ)
    (w : N) (h : ∀ u : ℂ, u • (∑ i ∈ Finset.range M, u ^ i • a i)
      + Ω (∑ i ∈ Finset.range M, u ^ i • a i) = p.eval u • w) :
    Ω (a 0) = p.coeff 0 • w ∧ ∀ k, a k + Ω (a (k + 1)) = p.coeff (k + 1) • w := by
  have hc : ∀ (f : N →ₗ[ℂ] ℂ) (k : ℕ),
      (∑ i ∈ Finset.range M, Polynomial.monomial i (f (a i))).coeff k = f (a k) := by
    intro f k
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial_apply]
    rw [Finset.sum_ite_eq']
    split_ifs with hk
    · rfl
    · rw [ha k (by simpa using hk), map_zero]
  have key : ∀ f : N →ₗ[ℂ] ℂ,
      Polynomial.X * (∑ i ∈ Finset.range M, Polynomial.monomial i (f (a i)))
        + (∑ i ∈ Finset.range M, Polynomial.monomial i ((f ∘ₗ Ω) (a i)))
        = p * Polynomial.C (f w) := by
    intro f
    apply Polynomial.funext
    intro u
    have h1 := congrArg f (h u)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_smul, map_sum, smul_eq_mul] at h1
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_C,
      LinearMap.comp_apply]
    rw [← h1]
    simp only [mul_comm]
  refine ⟨?_, fun k => ?_⟩
  · rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro f
    have h1 := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P 0) (key f)
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul_zero, hc, Polynomial.coeff_mul_C,
      zero_add] at h1
    rw [LinearMap.comp_apply] at h1
    rw [map_sub, map_smul, smul_eq_mul, h1, sub_self]
  · rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro f
    have h1 := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P (k + 1)) (key f)
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_mul, hc, Polynomial.coeff_mul_C] at h1
    rw [LinearMap.comp_apply] at h1
    rw [map_sub, map_add (f := _), map_smul, smul_eq_mul, h1, sub_self]

theorem aeval_neg_eq_zero_and_eigen_of_resolvent_identity :
    ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (p : Polynomial ℂ), (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = p.eval u • w) → Polynomial.aeval (-Ω) p = 0 ∧ ∀ (α : ℂ) (w : N), Ω w = α • w → ∀ (q : Polynomial ℂ), p = (Polynomial.X + Polynomial.C α) * q → ∀ u : ℂ, X u w = q.eval u • w := by
  intro N _ _ Ω X d c p hX h
  let a : N → ℕ → N := fun w i => if i < d then c i w else 0
  have ha : ∀ w i, d ≤ i → a w i = 0 := fun w i hi => if_neg (by omega)
  have hXa : ∀ (M : ℕ), d ≤ M → ∀ (u : ℂ) (w : N),
      X u w = ∑ i ∈ Finset.range M, u ^ i • a w i := by
    intro M hM u w
    rw [hX u, LinearMap.sum_apply]
    rw [← Finset.sum_subset (Finset.range_subset_range.2 hM)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      simp only [a, if_pos (Finset.mem_range.1 hi), LinearMap.smul_apply]
    · intro i _ hi
      rw [ha w i (by simpa using hi), smul_zero]
  have hco : ∀ w, Ω (a w 0) = p.coeff 0 • w ∧
      ∀ k, a w k + Ω (a w (k + 1)) = p.coeff (k + 1) • w := by
    intro w
    refine shift_coeff_of_eval_identity Ω d (a w) (ha w) p w fun u => ?_
    rw [← hXa d le_rfl u w]
    exact h u w
  refine ⟨?_, ?_⟩
  · ext w
    have tel : ∀ n, ∑ i ∈ Finset.range (n + 1), p.coeff i • ((-Ω) ^ i) w
        = ((-Ω) ^ n) (Ω (a w n)) := by
      intro n
      induction n with
      | zero => simp [(hco w).1]
      | succ n ih =>
        rw [Finset.sum_range_succ, ih, ← map_smul, ← (hco w).2 n, map_add (f := _), ← add_assoc]
        have : ((-Ω) ^ (n + 1)) (a w n) = - ((-Ω) ^ n) (Ω (a w n)) := by
          rw [pow_succ, Module.End.mul_apply, LinearMap.neg_apply, map_neg]
        rw [this, add_neg_cancel, zero_add]
    rw [Polynomial.aeval_eq_sum_range' (n := d + p.natDegree + 1) (by omega), LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
    rw [tel, ha w _ (by omega), map_zero, map_zero, LinearMap.zero_apply]
  · intro α w hw q hq u
    have step : ∀ k, a w (k + 1) = q.coeff (k + 1) • w → a w k = q.coeff k • w := by
      intro k hk
      have h1 := (hco w).2 k
      rw [hk, map_smul, hw, hq, add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul,
        Polynomial.coeff_C_mul, add_smul, smul_smul, mul_comm] at h1
      exact add_right_cancel h1
    have all : ∀ k, a w k = q.coeff k • w := by
      intro k
      have hk : k ≤ k + d + q.natDegree + 1 := by omega
      refine Nat.decreasingInduction (motive := fun k _ => a w k = q.coeff k • w)
        (fun j _ hj => step j hj) ?_ hk
      rw [ha w _ (by omega), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]
    rw [hXa (d + q.natDegree + 1) (by omega), Polynomial.eval_eq_sum_range' (n := d + q.natDegree + 1) (by omega), Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [all, smul_smul, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AevalNegEqZeroOfResolventIdentityStatement
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_neg_eq_zero_of_resolvent_identity : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (p : Polynomial ℂ), (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = p.eval u • w) → Polynomial.aeval (-Ω) p = 0 ∧ ∀ (α : ℂ) (w : N), Ω w = α • w → ∀ (q : Polynomial ℂ), p = (Polynomial.X + Polynomial.C α) * q → ∀ u : ℂ, X u w = q.eval u • w := by
  first | exact @GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity | exact GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity | (intros; apply GlobalTheory.aeval_neg_eq_zero_and_eigen_of_resolvent_identity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEigenSplitOfResolventIdentity
open Formalism.REAL Finset

namespace GlobalTheory

theorem exists_sum_eigen_split_of_resolvent : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = (∏ s, (u + ν s)) • w) → ∀ w : N, ∃ v : Fin n → N, w = ∑ s, v s ∧ ∀ s (u : ℂ), X u (v s) = (∏ t ∈ Finset.univ.erase s, (u + ν t)) • v s := by
  intro N _ _ n Ω X d c ν hν hX hres w
  have key := GlobalTheory.T.aeval_neg_eq_zero_of_resolvent_identity N Ω X d c (∏ s, (Polynomial.X + Polynomial.C (ν s))) hX (by
    intro u w
    rw [hres u w, Polynomial.eval_prod]
    simp)
  obtain ⟨v, hv, hw⟩ := GlobalTheory.T.exists_eigen_decomp_of_aeval_prod_eq_zero N n Ω ν hν key.1 w
  refine ⟨v, hw, fun s u => ?_⟩
  have h := key.2 (ν s) (v s) (hv s)
    (∏ t ∈ Finset.univ.erase s, (Polynomial.X + Polynomial.C (ν t)))
    (Finset.mul_prod_erase Finset.univ (fun t => Polynomial.X + Polynomial.C (ν t))
      (Finset.mem_univ s)).symm u
  rw [h, Polynomial.eval_prod]
  simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsEigenSplitOfResolventIdentityStatement
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenSplit_of_resolventIdentity : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = (∏ s, (u + ν s)) • w) → ∀ w : N, ∃ v : Fin n → N, w = ∑ s, v s ∧ ∀ s (u : ℂ), X u (v s) = (∏ t ∈ Finset.univ.erase s, (u + ν t)) • v s := by
  first | exact @GlobalTheory.exists_sum_eigen_split_of_resolvent | exact GlobalTheory.exists_sum_eigen_split_of_resolvent | (intros; apply GlobalTheory.exists_sum_eigen_split_of_resolvent <;> assumption)
end
end

open Formalism.REAL Finset

namespace GlobalTheory

theorem prod_add_ite_shift {n : ℕ} (ν : Fin n → ℂ) (s : Fin n) (u : ℂ) :
    (∏ t, (u + ν t + if t = s then 1 else 0)) =
      (∏ t, (u + ν t)) + ∏ t ∈ Finset.univ.erase s, (u + ν t) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ s),
    ← Finset.mul_prod_erase Finset.univ (fun t => u + ν t) (Finset.mem_univ s)]
  have : ∏ t ∈ Finset.univ.erase s, (u + ν t + if t = s then 1 else 0) =
      ∏ t ∈ Finset.univ.erase s, (u + ν t) :=
    Finset.prod_congr rfl fun t ht => by simp [Finset.ne_of_mem_erase ht]
  rw [this]; simp only [if_true]; ring

theorem qdet_vector_multiplier_shift_plus : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V) (x : Fin n → Module.End ℂ V) (ν : Fin n → ℂ), GlRel E → GlRel E' → (∀ a b w, ι (E' a b w) = E a b (ι w)) → Function.Injective ν → (∀ (u : ℂ) (w : W), qdet E' u w = (∏ s, (u + ν s)) • w) → (∀ a b j, E a b * x j = x j * E a b + if b = j then x a else 0) → ∀ (j : Fin n) (w : W), ∃ v : Fin n → Fin n → W, x j (ι w) = ∑ s, ∑ a, x a (ι (v s a)) ∧ ∀ (s : Fin n) (u : ℂ), qdet E u (∑ a, x a (ι (v s a))) = (∏ t, (u + ν t + if t = s then 1 else 0)) • ∑ a, x a (ι (v s a)) := by
  intro V W _ _ _ _ n E E' ι x ν hE hE' hι hν hq hx j w
  cases n with
  | zero => exact j.elim0
  | succ m =>
  let M : (Fin (m + 1) → Fin (m + 1) → Module.End ℂ W) → Module.End ℂ (Fin (m + 1) → W) :=
    fun B => LinearMap.pi fun a => ∑ k, (B a k).comp (LinearMap.proj k)
  have hM : ∀ B y a, M B y a = ∑ k, B a k (y k) := by
    intro B y a
    simp [M, LinearMap.sum_apply]
  let Ω := M (fun l a => E' a l)
  let X : ℂ → Module.End ℂ (Fin (m + 1) → W) := fun u => M (fun a k =>
    ((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1))
  choose c hc using fun a k : Fin (m + 1) =>
    GlobalTheory.T.exists_qminor_sub_eq_polynomial (Module.End ℂ W) (m + 1) m E' (Fin.succAbove a) (Fin.succAbove k) 1
  have hXc : ∀ u, X u = ∑ i ∈ Finset.range (m + 1), u ^ i •
      M (fun a k => ((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • c a k i) := by
    intro u
    refine LinearMap.ext fun y => funext fun a => ?_
    simp only [X, hM, hc, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
      Pi.smul_apply, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  have hΩ : ∀ (u : ℂ) (y : Fin (m + 1) → W),
      u • X u y + Ω (X u y) = (∏ s, (u + ν s)) • y := by
    intro u y
    funext l
    have h1 : (u • X u y + Ω (X u y)) l = ∑ a, Tm E' u a l (X u y a) := by
      simp only [Pi.add_apply, Pi.smul_apply, Ω, hM, Tm, LinearMap.add_apply,
        Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single l]
      · simp [Finset.smul_sum]
      · intro b _ hb; simp [hb]
      · simp
    have h2 : ∀ k : Fin (m + 1), ∑ a : Fin (m + 1), Tm E' u a l ((((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1)) (y k)) = if l = k then qdet E' u (y k) else 0 := by
      intro k
      have := LinearMap.congr_fun (GlobalTheory.T.capelli_left_comatrix_qminor_eq (Module.End ℂ W) m E' hE' u k l) (y k)
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
      simp only [LinearMap.smul_apply, map_smul]
      rw [this]
      split_ifs <;> simp
    rw [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [X, hM, map_sum]
    rw [Finset.sum_comm]
    simp only [h2]
    simp [hq]
  obtain ⟨v, hv, hXv⟩ := GlobalTheory.T.exists_eigenSplit_of_resolventIdentity (Fin (m + 1) → W) (m + 1) Ω X (m + 1) _ ν hν hXc hΩ
    (Pi.single j w)
  have hqι : ∀ u y, qdet E u (ι y) = (∏ s, (u + ν s)) • ι y := by
    intro u y
    rw [← map_smul, ← hq]
    exact (GlobalTheory.T.qminor_intertwining_apply V W (m + 1) (m + 1) E E' ι hι id id u y).symm
  have hmu : ∀ (u : ℂ) (y : Fin (m + 1) → W), qdet E u (∑ a, x a (ι (y a))) =
      (∏ s, (u + ν s)) • (∑ a, x a (ι (y a))) + ∑ a, x a (ι (X u y a)) := by
    intro u y
    have h3 : ∀ k : Fin (m + 1), qdet E u (x k (ι (y k))) = (∏ s, (u + ν s)) • x k (ι (y k)) +
        ∑ a : Fin (m + 1), x a (ι ((((-1 : ℂ) ^ ((a : ℕ) + (k : ℕ))) • qminor E' (Fin.succAbove a) (Fin.succAbove k) (u - 1)) (y k))) := by
      intro k
      have := LinearMap.congr_fun (GlobalTheory.T.capelliDet_mul_vectorType (Module.End ℂ V) m E x hE hx u k) (ι (y k))
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
        LinearMap.add_apply, hqι, map_smul] at this
      rw [this]
      simp only [LinearMap.smul_apply, map_smul, GlobalTheory.T.qminor_intertwining_apply V W (m + 1) m E E' ι hι]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, h3, Finset.sum_add_distrib, Finset.smul_sum, X, hM]
    rw [Finset.sum_comm]
  refine ⟨v, ?_, fun s u => ?_⟩
  · rw [Finset.sum_comm]
    have : ∀ a, ∑ s, x a (ι (v s a)) = x a (ι ((Pi.single j w : Fin (m + 1) → W) a)) := by
      intro a
      rw [hv]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    simp only [this]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · simp
  · rw [hmu, hXv, prod_add_ite_shift, add_smul]
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum]

end GlobalTheory
end

open Formalism.REAL Finset

namespace GlobalTheory

theorem _root_.GlobalTheory.covector_multiplier_shift : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V) (x : Fin n → Module.End ℂ V) (ν : Fin n → ℂ), _root_.Formalism.REAL.GlRel E → _root_.Formalism.REAL.GlRel E' → (∀ a b w, ι (E' a b w) = E a b (ι w)) → Function.Injective ν → (∀ (u : ℂ) (w : W), _root_.Formalism.REAL.qdet E' u w = (∏ s, (u + ν s)) • w) → (∀ a b j, E a b * x j = x j * E a b - if a = j then x b else 0) → ∀ (j : Fin n) (w : W), ∃ v : Fin n → Fin n → W, x j (ι w) = ∑ s, ∑ a, x a (ι (v s a)) ∧ ∀ (s : Fin n) (u : ℂ), _root_.Formalism.REAL.qdet E u (∑ a, x a (ι (v s a))) = (∏ t, (u + ν t - if t = s then 1 else 0)) • ∑ a, x a (ι (v s a)) := by
  intro V W _ _ _ _ n E E' ι x ν hE hE' hι hν hq hx j w
  obtain ⟨hF, hqF⟩ := _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ V) n E hE
  obtain ⟨hF', hqF'⟩ := _root_.GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ W) n E' hE'
  have hιF : ∀ (a b : Fin n) (w : W), ι ((-E' b a) w) = (-E b a) (ι w) := by
    intro a b w
    simp only [LinearMap.neg_apply, map_neg, hι]
  have hνF : Function.Injective (fun s : Fin n => (1 : ℂ) - n - ν s) := by
    intro s t h
    apply hν
    have h' : (1 - n - ν s : ℂ) = 1 - n - ν t := h
    linear_combination -h'
  have hqE' : ∀ (u : ℂ) (w : W), (_root_.Formalism.REAL.qdet (fun a b => -E' b a) u) w
      = (∏ s, (u + (1 - n - ν s))) • w := by
    intro u w
    rw [hqF', LinearMap.smul_apply, hq, smul_smul]
    congr 1
    rw [← Fin.prod_const n (-1 : ℂ), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    ring
  have hxF : ∀ (a b k : Fin n), (-E b a) * x k = x k * (-E b a) + if b = k then x a else 0 := by
    intro a b k
    rw [neg_mul, mul_neg, hx b a k]
    abel
  obtain ⟨v, hv1, hv2⟩ := _root_.GlobalTheory.qdet_vector_multiplier_shift_plus V W n (fun a b => -E b a)
    (fun a b => -E' b a) ι x (fun s => 1 - n - ν s) hF hF' hιF hνF hqE' hxF j w
  · refine ⟨v, hv1, fun s u => ?_⟩
    have h := hv2 s ((n : ℂ) - 1 - u)
    rw [hqF, show (n : ℂ) - 1 - ((n : ℂ) - 1 - u) = u by ring, LinearMap.smul_apply] at h
    have h2 := congrArg (((-1 : ℂ) ^ n) • ·) h
    simp only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul] at h2
    rw [h2]
    congr 1
    rw [← Fin.prod_const n (-1 : ℂ), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    split_ifs <;> ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InverseEntrySmulCapelliEigenfunctionSum
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckOn_inv_entry (k r : ℕ) (c j : Fin (2 * r + k + 1)) :
    B.CkOn ⊤ (B.GV k r) (fun y : B.Mat k r => y⁻¹ c j) := by
  intro g₀ _
  refine ⟨Set.univ, fun g => Formalism.FourierDecayAlt.P.JCx2.mnLinInv (Pi.single j 1) c g, isOpen_univ, trivial,
    (Formalism.FourierDecayAlt.P.JCx2.mnLinInv (Pi.single j 1) c).contDiff.contDiffOn, fun g _ hg => ?_⟩
  show g⁻¹ c j = Matrix.mulVec (Hpk k r * g.conjTranspose * Hpk k r) (Pi.single j 1) c
  rw [← Formalism.FourierDecayAlt.P.JCx2.mn_inv_gv hg]
  simp

theorem inCC_inv_entry_smul {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (c j : Fin (2 * r + k + 1)) {A : ℝ} {m : ℕ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.InCC A m F) :
    B.InCC (A - 1) m (fun g : B.Mat k r => g⁻¹ c j • F g) := by
  have hg : Formalism.FourierDecayAlt.P.JCx2.pdGood Wp Wq 1 (fun g : B.Mat k r => g⁻¹ c j) :=
    Formalism.FourierDecayAlt.P.JCx2.pd_good_congr (fun g _ => by simp)
      (Formalism.FourierDecayAlt.P.JCx2.pd_good_inv (Wp := Wp) (Wq := Wq) (Pi.single j 1) c)
  obtain ⟨K, -, hK⟩ := hg.2 (A - 1) m
  obtain ⟨b, hb⟩ := hF
  exact ⟨K * b, hK F b (by rw [Nat.cast_one, sub_add_cancel]; exact hb)⟩

theorem inv_entry_smul_eigen_split : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (A : ℝ) (i j : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), Function.Injective lam → (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∃ Fi : Fin (2 * r + k + 1) → B.Mat k r → (Wq →L[ℂ] Wp), (∀ t, (B.CkOn ⊤ (B.GV k r) (Fi t) ∧ ∀ m : ℕ, B.InCC (A - 1) m (Fi t))) ∧ (∀ t, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi t) g = ((∏ s, (Y + (lam s - if s = t then 1 else 0)) : ℝ) : ℂ) • (Fi t) g)) ∧ ∀ g ∈ B.GV k r, g⁻¹ i j • f g = ∑ t, Fi t g := by
  intro k r Wp Wq _ _ _ _ _ _ lam A i j f hlam hf heig
  obtain ⟨V, W, _, _, _, _, E, E', ι, ev, mul, hE, hE', hι, hq, hsm, hext, hcc, hex, -, hqC, hmul⟩ :=
    GlobalTheory.capelli_module_model k r Wp Wq lam A
  obtain ⟨w, hw⟩ := hex f hf heig
  let x : Fin (2 * r + k + 1) → Module.End ℂ V := fun c => mul (fun y : B.Mat k r => y⁻¹ c j)
  have hx : ∀ c v, ∀ g ∈ B.GV k r, ev (x c v) g = g⁻¹ c j • ev v g :=
    fun c => (hmul _ (ckOn_inv_entry k r c j)).1
  have hcomm : ∀ a b c, E a b * x c = x c * E a b - if a = c then x b else 0 := by
    intro a b c
    ext v
    refine hext _ _ fun g hg => ?_
    have h1 := (hmul _ (ckOn_inv_entry k r c j)).2 a b v g hg
    rw [GlobalTheory.eh_inv_entry k r a b c j g hg] at h1
    rw [Module.End.mul_apply, LinearMap.sub_apply, map_sub, Pi.sub_apply, Module.End.mul_apply, hx _ _ g hg]
    refine h1.trans ?_
    split_ifs with h
    · rw [hx _ _ g hg, neg_smul, sub_eq_add_neg]
    · simp
  have hinj : Function.Injective
      (fun s => ((lam s : ℂ) - (((2 * r + k + 1) : ℕ) - 1 : ℂ) / 2)) := by
    intro s t h
    apply hlam
    have h' : (lam s : ℂ) = lam t := sub_left_inj.1 h
    exact_mod_cast h'
  obtain ⟨v, hv1, hv2⟩ := GlobalTheory.covector_multiplier_shift V W _ E E' ι x _ hE hE' hι hinj hq hcomm i w
  refine ⟨fun t => ev (∑ a, x a (ι (v t a))), fun t => ⟨hsm _, fun m => ?_⟩, fun t Y g hg => ?_, fun g hg => ?_⟩
  · obtain ⟨b, hb⟩ := Formalism.FourierDecayAlt.P.JCx2.sq_inCC_sum (A := A - 1) (m := m) Finset.univ
      (fun a (g : B.Mat k r) => g⁻¹ a j • ev (ι (v t a)) g)
      (fun a _ => inCC_inv_entry_smul a j (hcc (v t a) m))
    refine ⟨b, Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr (fun g hg => ?_) hb⟩
    beta_reduce
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => (hx _ _ g hg).symm
  · rw [← hqC _ _ g hg, hv2, map_smul, Pi.smul_apply]
    congr 1
    push_cast
    refine Finset.prod_congr rfl fun s _ => ?_
    split_ifs <;> push_cast <;> ring
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← hw g hg, ← hx i _ g hg, hv1, map_sum, Finset.sum_apply]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InverseEntrySmulCapelliEigenfunctionSumStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseEntry_smul_capelliEigenfunction_sum : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (A : ℝ) (i j : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), Function.Injective lam → (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∃ Fi : Fin (2 * r + k + 1) → B.Mat k r → (Wq →L[ℂ] Wp), (∀ t, (B.CkOn ⊤ (B.GV k r) (Fi t) ∧ ∀ m : ℕ, B.InCC (A - 1) m (Fi t))) ∧ (∀ t, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi t) g = ((∏ s, (Y + (lam s - if s = t then 1 else 0)) : ℝ) : ℂ) • (Fi t) g)) ∧ ∀ g ∈ B.GV k r, g⁻¹ i j • f g = ∑ t, Fi t g := by
  first | exact @GlobalTheory.inv_entry_smul_eigen_split | exact GlobalTheory.inv_entry_smul_eigen_split | (intros; apply GlobalTheory.inv_entry_smul_eigen_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryConjEntryAndInvEntryLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryConjEntryAndInvEntryLinear
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset Matrix

namespace GlobalTheory

theorem sandwich_entry_sum {n : Type*} [Fintype n] (A M B : Matrix n n ℂ) (i j : n) :
    (A * M * B) i j = ∑ a, ∑ b, A i a * B b j * M a b := by
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem unitary_inv_eq_gram_conj {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  refine Matrix.inv_eq_left_inv ?_
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [mul_assoc, mul_assoc, ← mul_assoc gᴴ, h, BesselUnitary.gram_sq]

theorem unitary_conj_entry_and_inv_entry : ∀ (k r : ℕ) (i j : Fin (2 * r + k + 1)), (∃ co : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ, ∀ g ∈ B.GV k r, star (g i j) = ∑ a, ∑ b, co a b * g⁻¹ a b) ∧ ∃ q : B.Mat k r → ℂ, U.IsPolyDeg 1 q ∧ ∀ g ∈ B.GV k r, g⁻¹ i j = q g := by
  intro k r i j
  refine ⟨⟨fun a b => Hpk k r j a * Hpk k r b i, fun g hg => ?_⟩,
    fun g => (Hpk k r * gᴴ * Hpk k r) i j, ?_, fun g hg => by rw [unitary_inv_eq_gram_conj hg]⟩
  · have h : gᴴ = Hpk k r * g⁻¹ * Hpk k r := by
      rw [unitary_inv_eq_gram_conj hg]
      simp only [← mul_assoc]
      rw [BesselUnitary.gram_sq, one_mul, mul_assoc, BesselUnitary.gram_sq, mul_one]
    rw [← sandwich_entry_sum, ← h, Matrix.conjTranspose_apply]
  · refine ⟨∑ a, ∑ b, MvPolynomial.C (Hpk k r i a * Hpk k r b j) * MvPolynomial.X (Sum.inr (b, a)), ?_, fun g => ?_⟩
    · refine MvPolynomial.totalDegree_finsetSum_le fun a _ =>
        MvPolynomial.totalDegree_finsetSum_le fun b _ => ?_
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    · show (Hpk k r * gᴴ * Hpk k r) i j = _
      rw [sandwich_entry_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inr,
        Matrix.conjTranspose_apply]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryConjEntryAndInvEntryLinearStatement
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_conj_entry_and_inv_entry_linear : ∀ (k r : ℕ) (i j : Fin (2 * r + k + 1)), (∃ co : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ, ∀ g ∈ B.GV k r, star (g i j) = ∑ a, ∑ b, co a b * g⁻¹ a b) ∧ ∃ q : B.Mat k r → ℂ, U.IsPolyDeg 1 q ∧ ∀ g ∈ B.GV k r, g⁻¹ i j = q g := by
  first | exact @GlobalTheory.unitary_conj_entry_and_inv_entry | exact GlobalTheory.unitary_conj_entry_and_inv_entry | (intros; apply GlobalTheory.unitary_conj_entry_and_inv_entry <;> assumption)
end
end

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem conj_entry_smul_eigenSum : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (i j : Fin (2 * r + k + 1)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ s t, s ≠ t → 2 * ((d : ℕ) : ℝ) < |lam s - lam t|) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d + 1 : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A - 1) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (fun g => star (g i j) • F g) g = ∑ i, Fi i g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam d A i j F hsep hF
  obtain ⟨N₀, Fi, ν, hν, hcl, heig, hsum⟩ := hF
  obtain ⟨⟨co, hco⟩, -⟩ := GlobalTheory.T.unitary_conj_entry_and_inv_entry_linear k r i j
  refine GlobalTheory.T.capelliEigenSum_linearCombination k r Wp Wq lam (d + 1) (A - 1)
    (Fin N₀ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) Finset.univ
    (fun x => co x.2.1 x.2.2) (fun x g => g⁻¹ x.2.1 x.2.2 • Fi x.1 g)
    (fun g => star (g i j) • F g) ?_ ?_
  · rintro ⟨x, a, b⟩ -
    refine ⟨d + 1, A - 1, le_rfl, le_rfl, ?_⟩
    have hinj : Function.Injective (fun s => lam s + (ν x s : ℝ)) := by
      intro s t hst
      by_contra hne
      have h1 := hsep s t hne
      have h2 : |(ν x s : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν x s
      have h3 : |(ν x t : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν x t
      have h4 : lam s - lam t = (ν x t : ℝ) - (ν x s : ℝ) := by
        simp only at hst
        linarith
      rw [h4] at h1
      have h5 := abs_sub (ν x t : ℝ) (ν x s : ℝ)
      linarith
    obtain ⟨G, hG1, hG2, hG3⟩ := GlobalTheory.T.inverseEntry_smul_capelliEigenfunction_sum k r Wp Wq (fun s => lam s + (ν x s : ℝ)) A a b
      (Fi x) hinj (hcl x) (by
        intro Y g hg
        rw [heig x Y g hg]
        simp only [add_assoc])
    refine ⟨2 * r + k + 1, G, fun t s => ν x s - if s = t then 1 else 0, ?_, hG1, ?_, hG3⟩
    · intro t s
      have h := abs_le.mp (hν x s)
      rw [abs_le]
      push_cast
      split_ifs <;> constructor <;> omega
    · intro t Y g hg
      rw [hG2 t Y g hg]
      congr 2
      refine Finset.prod_congr rfl fun s _ => ?_
      push_cast
      split_ifs <;> ring
  · intro g hg
    beta_reduce
    rw [hco g hg, hsum g hg, Fintype.sum_prod_type, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul]

end GlobalTheory
