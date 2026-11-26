module

public import Formalism.HermitianCurvature.StatementQ
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusInvariance.Development
open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def blk {k r : ℕ} (i : Fin (r + 1)) (g : Mx k r) : Matrix (Fin (mdim k r i)) (Fin (mdim k r i)) ℂ :=
  fun a b => g (posL k r i a) (posL k r i b)

def StepS : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)), inWb k r z →
    (1 : Mx k r) ∈ Slev k r z i ∧ ∀ s ∈ Slev k r z i, s ∈ Glev k r i ∧ s *ᵥ fvec k r z i = fvec k r z i

def StepGrp : Prop :=
  ∀ (k r : ℕ) (i : Fin (r + 1)), ∀ g ∈ Glev k r i, ∀ h ∈ Glev k r i, g * h ∈ Glev k r i

def StepVec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)), inWb k r z → inWb k r z' →
    (∀ s ∈ Slev k r z i, ∀ g : Mx k r, yv k r z i (s * g) = yv k r z i g ∧ ybv k r z i (s * g) = ybv k r z i g) ∧
    ∀ s' ∈ Slev k r z' i,
      blk i s' * blk i s'⁻¹ = 1 ∧ blk i s'⁻¹ * blk i s' = 1 ∧
      blk i s' *ᵥ xv k r z' i = xv k r z' i ∧ xbv k r z' i ᵥ* blk i s'⁻¹ = xbv k r z' i ∧
      ∀ g ∈ Glev k r i, yv k r z i g = blk i s' *ᵥ yv k r z i (g * s') ∧
        ybv k r z i g = ybv k r z i (g * s') ᵥ* blk i s'⁻¹

def StepCongr : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (a b : Fin (mdim k r i)) (f f' : Mx k r → E) (g : Mx k r), IsOpen D → g ∈ Glev k r i ∩ D →
    (∀ x ∈ Glev k r i ∩ D, f x = f' x) →
    EH k r (posL k r i a) (posL k r i b) f g = EH k r (posL k r i a) (posL k r i b) f' g

def StepRight : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (a b : Fin (mdim k r i)) (f : Mx k r → E) (s' g : Mx k r), IsOpen D → SmoothLev k r i D f →
    s' ∈ Glev k r i → g ∈ Glev k r i → g * s' ∈ D →
    EH k r (posL k r i a) (posL k r i b) (fun x => f (x * s')) g =
      ∑ c, ∑ d, (blk i s'⁻¹ c a * blk i s' b d) • EH k r (posL k r i c) (posL k r i d) f (g * s')

def StepRSm : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (f : Mx k r → E) (s' : Mx k r), s' ∈ Glev k r i → (∀ g ∈ Glev k r i ∩ D, g * s' ∈ D) →
    SmoothLev k r i D f → SmoothLev k r i D (fun x => f (x * s'))

section Alg

variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}

lemma tm_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ)
    (a b : Fin n) : Tm E u a b * R = R * Tm E' u a b := by
  unfold Tm
  rw [add_mul, mul_add, h]
  congr 1
  split_ifs
  · exact Algebra.commutes u R
  · simp

lemma prod_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b)
    (l : List (ℂ × Fin n × Fin n)) :
    (l.map fun p => Tm E p.1 p.2.1 p.2.2).prod * R = R * (l.map fun p => Tm E' p.1 p.2.1 p.2.2).prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, ih, ← mul_assoc, tm_inter E E' R h, mul_assoc]

lemma qminor_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b)
    {t : ℕ} (α β : Fin t → Fin n) (u : ℂ) : qminor E α β u * R = R * qminor E' α β u := by
  have key : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α (σ k)) (β k)).prod * R =
        R * (List.ofFn fun k : Fin t => Tm E' (u - (k : ℂ)) (α (σ k)) (β k)).prod := by
    intro σ
    have hl := prod_inter E E' R h (List.ofFn fun k : Fin t => (u - (k : ℂ), α (σ k), β k))
    simpa [List.map_ofFn, Function.comp_def] using hl
  unfold qminor
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_assoc, key σ, ← mul_assoc, ← mul_assoc, (Int.cast_commute _ R).eq]

lemma chatA_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ)
    (a β : Fin n → ℂ) : chatA E u a β * R = R * chatA E' u a β := by
  unfold chatA
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, qminor_inter E E' R h]

lemma second_capelli_minor_intertwines (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ)
    (a a' β β' : Fin n → ℂ) : chat2A E u a a' β β' * R = R * chat2A E' u a a' β β' := by
  unfold chat2A
  simp only [Finset.sum_mul, Finset.mul_sum, ite_mul, mul_ite, zero_mul, mul_zero, smul_mul_assoc,
    mul_smul_comm, qminor_inter E E' R h]

lemma qdet_inter (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b) (u : ℂ) :
    qdet E u * R = R * qdet E' u := qminor_inter E E' R h id id u

end Alg

section Model

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}

abbrev Pt (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) : Type := {g : Mx k r // g ∈ Glev k r i ∩ D}


open Classical in
def ext (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (φ : Pt k r i D → E) : Mx k r → E :=
  fun g => if h : g ∈ Glev k r i ∩ D then φ ⟨g, h⟩ else 0

lemma ext_at {φ : Pt k r i D → E} {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : ext k r i D φ g = φ ⟨g, hg⟩ := by
  unfold ext
  rw [dite_eq_left hg]

lemma lev_congr (hD : IsOpen D) {f f' : Mx k r → E} (h : ∀ g ∈ Glev k r i ∩ D, f g = f' g)
    (hf : SmoothLev k r i D f) : SmoothLev k r i D f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left, fun g hg hgG => ?_⟩
  rw [← h g ⟨hgG, hg.2⟩, hfF g hg.1 hgG]

lemma lev_zero : SmoothLev k r i D (fun _ : Mx k r => (0 : E)) := fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩

lemma lev_add {f f' : Mx k r → E} (hf : SmoothLev k r i D f) (hf' : SmoothLev k r i D f') :
    SmoothLev k r i D (fun g => f g + f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hgG => ?_⟩
  show f g + f' g = F g + F' g
  rw [hfF g hg.1 hgG, hfF' g hg.2 hgG]

lemma lev_smul {f : Mx k r → E} (c : ℂ) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (fun g => c • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, hgU, hF.const_smul c, fun g hg hgG => ?_⟩
  show c • f g = c • F g
  rw [hfF g hg hgG]


variable (E k r i D) in
def Sm : Submodule ℂ (Pt k r i D → E) where
  carrier := {φ | SmoothLev k r i D (ext k r i D φ)}
  add_mem' {φ ψ} hφ hψ := by
    have e : ext k r i D (φ + ψ) = fun g => ext k r i D φ g + ext k r i D ψ g := by
      funext g; unfold ext; split_ifs <;> simp
    show SmoothLev k r i D (ext k r i D (φ + ψ))
    rw [e]; exact lev_add hφ hψ
  zero_mem' := by
    have e : ext k r i D (0 : Pt k r i D → E) = fun _ => 0 := by
      funext g; unfold ext; split_ifs <;> simp
    show SmoothLev k r i D (ext k r i D (0 : Pt k r i D → E))
    rw [e]; exact lev_zero
  smul_mem' c φ hφ := by
    have e : ext k r i D (c • φ) = fun g => c • ext k r i D φ g := by
      funext g; unfold ext; split_ifs <;> simp
    show SmoothLev k r i D (ext k r i D (c • φ))
    rw [e]; exact lev_smul c hφ

def Rep (F : Mx k r → E) (φ : Pt k r i D → E) : Prop :=
  ∀ g (hg : g ∈ Glev k r i ∩ D), F g = φ ⟨g, hg⟩

lemma rep_ext (φ : Pt k r i D → E) : Rep (ext k r i D φ) φ := fun _ hg => ext_at hg

lemma posL_inj {a b : Fin (mdim k r i)} (h : posL k r i a = posL k r i b) : a = b := by
  unfold posL at h
  have h2 := congrArg Fin.val h
  simp only at h2
  exact Fin.ext (by omega)

def Tf (a b : Fin (mdim k r i)) (φ : Pt k r i D → E) : Pt k r i D → E :=
  fun p => EH k r (posL k r i a) (posL k r i b) (ext k r i D φ) p.1

lemma eh_zero (a b : Fin (2 * r + k + 1)) (g : Mx k r) :
    EH k r a b (fun _ : Mx k r => (0 : E)) g = 0 := by
  simp [EabH, RdV]

section Ops

variable (hP : EabPres) (hC : StepCongr) (hD : IsOpen D)
include hP hC hD

lemma Tf_mem {φ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) (a b : Fin (mdim k r i)) :
    Tf a b φ ∈ Sm E k r i D := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  have h1 := (hP E k r (fun _ => 0) i D a b (ext k r i D φ) (ext k r i D φ) 0 hD hφ' hφ').1
  show SmoothLev k r i D (ext k r i D (Tf a b φ))
  exact lev_congr hD (fun g hg => (ext_at (φ := Tf a b φ) hg).symm) h1

lemma Tf_add {φ ψ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) (hψ : ψ ∈ Sm E k r i D)
    (a b : Fin (mdim k r i)) : Tf a b (φ + ψ) = Tf a b φ + Tf a b ψ := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  have hψ' : SmoothLev k r i D (ext k r i D ψ) := hψ
  funext p
  have e : ext k r i D (φ + ψ) = fun x => ext k r i D φ x + (1 : ℂ) • ext k r i D ψ x := by
    funext g; unfold ext; split_ifs <;> simp
  have h3 := (hP E k r (fun _ => 0) i D a b (ext k r i D φ) (ext k r i D ψ) 1 hD hφ' hψ').2.2 p.1 p.2
  show EH k r (posL k r i a) (posL k r i b) (ext k r i D (φ + ψ)) p.1 =
    EH k r (posL k r i a) (posL k r i b) (ext k r i D φ) p.1 + EH k r (posL k r i a) (posL k r i b) (ext k r i D ψ) p.1
  rw [e, h3, one_smul]

lemma Tf_smul {φ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) (c : ℂ)
    (a b : Fin (mdim k r i)) : Tf a b (c • φ) = c • Tf a b φ := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  funext p
  have e : ext k r i D (c • φ) = fun x => (0 : E) + c • ext k r i D φ x := by
    funext g; unfold ext; split_ifs <;> simp
  have h3 := (hP E k r (fun _ => 0) i D a b (fun _ => (0 : E)) (ext k r i D φ) c hD lev_zero hφ').2.2 p.1 p.2
  show EH k r (posL k r i a) (posL k r i b) (ext k r i D (c • φ)) p.1 =
    c • EH k r (posL k r i a) (posL k r i b) (ext k r i D φ) p.1
  rw [e, h3, eh_zero, zero_add]

def Ealg (a b : Fin (mdim k r i)) : Module.End ℂ (Sm E k r i D) where
  toFun x := ⟨Tf a b x.1, Tf_mem hP hC hD x.2 a b⟩
  map_add' x y := Subtype.ext (Tf_add hP hC hD x.2 y.2 a b)
  map_smul' c x := Subtype.ext (Tf_smul hP hC hD x.2 c a b)

lemma E_rep {F : Mx k r → E} {x : Sm E k r i D} (h : Rep F x.1) (a b : Fin (mdim k r i)) :
    Rep (EH k r (posL k r i a) (posL k r i b) F) (Ealg hP hC hD a b x).1 := by
  intro g hg
  show EH k r (posL k r i a) (posL k r i b) F g = EH k r (posL k r i a) (posL k r i b) (ext k r i D x.1) g
  exact hC E k r i D a b F (ext k r i D x.1) g hD hg (fun y hy => by rw [h y hy, ext_at hy])

lemma Top_rep {F : Mx k r → E} {x : Sm E k r i D} (h : Rep F x.1) (u : ℂ)
    (a b : Fin (mdim k r i)) :
    Rep (Formalism.QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) F) (Tm (Ealg hP hC hD) u a b x).1 := by
  intro g hg
  have h2 := E_rep hP hC hD h a b g hg
  by_cases hab : a = b
  · subst hab
    simp [Formalism.QuantumDeterminants.Top, Tm, h g hg, h2]
  · have hne : posL k r i a ≠ posL k r i b := fun e => hab (posL_inj e)
    simp [Formalism.QuantumDeterminants.Top, Tm, hab, hne, h2]

lemma foldr_rep (l : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i))) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) :
    Rep ((l.map fun p => Formalism.QuantumDeterminants.Top (EH k r) p.1 (posL k r i p.2.1) (posL k r i p.2.2)).foldr (fun T f => T f) F)
      ((l.map fun p => Tm (Ealg hP hC hD) p.1 p.2.1 p.2.2).prod x).1 := by
  induction l with
  | nil => simpa using h
  | cons p l ih =>
    simp only [List.map_cons, List.foldr_cons, List.prod_cons]
    exact Top_rep hP hC hD ih p.1 p.2.1 p.2.2

lemma qminor_apply {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) (x : Sm E k r i D) :
    qminor (Ealg hP hC hD) a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm (Ealg hP hC hD) p.1 p.2.1 p.2.2).prod x := by
  unfold qminor
  simp [LinearMap.sum_apply, List.map_ofFn, Function.comp_def, Int.cast_smul_eq_zsmul]

lemma qminor_rep {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) :
    Rep (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u F) (qminor (Ealg hP hC hD) a b u x).1 := by
  intro g hg
  rw [qminor_apply hP hC hD a b u x]
  unfold qminorOp
  simp only [Finset.sum_apply, Pi.smul_apply, Submodule.coe_sum, Submodule.coe_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hf := foldr_rep hP hC hD (List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)) h g hg
  simpa [List.map_ofFn, Function.comp_def] using hf

lemma chat_rep (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chatL (EH k r) (posL k r i) u a β F g = (chatA (Ealg hP hC hD) u (a g) (β g) x).1 ⟨g, hg⟩ := by
  unfold chatL chatA
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [qminor_rep hP hC hD (skip1 i) (skip1 j) u h g hg]

lemma second_capelli_minor_represents (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ) {F : Mx k r → E}
    {x : Sm E k r i D} (h : Rep F x.1) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    chat2L (EH k r) (posL k r i) u a a' β β' F g =
      (chat2A (Ealg hP hC hD) u (a g) (a' g) (β g) (β' g) x).1 ⟨g, hg⟩ := by
  unfold chat2L chat2A
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
  split_ifs
  · simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [qminor_rep hP hC hD (skip2 i i') (skip2 j j') u h g hg]
  · simp

lemma qdet_rep (u : ℂ) {F : Mx k r → E} {x : Sm E k r i D} (h : Rep F x.1) (g : Mx k r)
    (hg : g ∈ Glev k r i ∩ D) :
    capL k r i u F g = (qdet (Ealg hP hC hD) u x).1 ⟨g, hg⟩ := qminor_rep hP hC hD id id u h g hg

variable (hG : EabGlLev) in
include hG in
lemma Ealg_gl : GlRel (Ealg (E := E) (i := i) hP hC hD) := by
  intro a b c d
  apply LinearMap.ext; intro x
  apply Subtype.ext; funext p
  obtain ⟨g, hg⟩ := p
  have r0 : Rep (ext k r i D x.1) x.1 := rep_ext x.1
  have hab := E_rep hP hC hD (E_rep hP hC hD r0 c d) a b g hg
  have hcd := E_rep hP hC hD (E_rep hP hC hD r0 a b) c d g hg
  have had := E_rep hP hC hD r0 a d g hg
  have hcb := E_rep hP hC hD r0 c b g hg
  have key := hG E k r i D a b c d (ext k r i D x.1) hD x.2 g hg
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply]
  rw [← hab, ← hcd, key]
  split_ifs <;> simp [had, hcb]

variable {s' : Mx k r} (hs' : ∀ g ∈ Glev k r i ∩ D, g * s' ∈ Glev k r i ∩ D)

def Rf (φ : Pt k r i D → E) : Pt k r i D → E := fun p => φ ⟨p.1 * s', hs' p.1 p.2⟩

variable (hRS : StepRSm) (hs'G : s' ∈ Glev k r i)
include hRS hs'G

lemma Rf_mem {φ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) : Rf hs' φ ∈ Sm E k r i D := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  have h1 := hRS E k r i D (ext k r i D φ) s' hs'G (fun g hg => (hs' g hg).2) hφ'
  show SmoothLev k r i D (ext k r i D (Rf hs' φ))
  refine lev_congr hD (fun g hg => ?_) h1
  show ext k r i D φ (g * s') = ext k r i D (Rf hs' φ) g
  rw [ext_at hg, ext_at (hs' g hg)]
  rfl

def RL : Module.End ℂ (Sm E k r i D) where
  toFun x := ⟨Rf hs' x.1, Rf_mem hP hC hD hs' hRS hs'G x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (hRt : StepRight) in
include hRt in
lemma RL_inter (a b : Fin (mdim k r i)) :
    Ealg (E := E) hP hC hD a b * RL (E := E) hP hC hD hs' hRS hs'G =
      RL (E := E) hP hC hD hs' hRS hs'G * Econj (Ealg (E := E) hP hC hD) (blk i s'⁻¹) (blk i s') a b := by
  apply LinearMap.ext; intro x
  apply Subtype.ext; funext p
  obtain ⟨g, hg⟩ := p
  have hcon := hC E k r i D a b (ext k r i D (Rf hs' x.1)) (fun y => ext k r i D x.1 (y * s')) g hD hg
    (fun y hy => by
      show ext k r i D (Rf hs' x.1) y = ext k r i D x.1 (y * s')
      rw [ext_at hy, ext_at (hs' y hy)]
      rfl)
  have hR := hRt E k r i D a b (ext k r i D x.1) s' g hD x.2 hs'G hg.1 (hs' g hg).2
  show EH k r (posL k r i a) (posL k r i b) (ext k r i D (Rf hs' x.1)) g =
    (Econj (Ealg (E := E) hP hC hD) (blk i s'⁻¹) (blk i s') a b x).1 ⟨g * s', hs' g hg⟩
  rw [hcon, hR]
  simp only [Econj, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  rfl

lemma RL_apply (M M' : Module.End ℂ (Sm E k r i D)) (hM : M * RL (E := E) hP hC hD hs' hRS hs'G = RL (E := E) hP hC hD hs' hRS hs'G * M')
    (x : Sm E k r i D) (g : Mx k r) (hg : g ∈ Glev k r i ∩ D) :
    (M (RL hP hC hD hs' hRS hs'G x)).1 ⟨g, hg⟩ = (M' x).1 ⟨g * s', hs' g hg⟩ := congrArg (fun T : Module.End ℂ (Sm E k r i D) => (T x).1 ⟨g, hg⟩) hM

end Ops

end Model

lemma tl00 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 0 0 f = capL k r i (uC k r i Y) f := rfl

lemma tl01 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 0 1 f =
      -(chatL (EH k r) (posL k r i) (uC k r i Y - 1) (fun _ => xv k r z' i) (ybv k r z i) f) := rfl

lemma tl10 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 1 0 f =
      -(chatL (EH k r) (posL k r i) (uC k r i Y) (yv k r z i) (fun _ => xbv k r z' i) f) := rfl

lemma tl11 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (r + 1)) (Y : ℂ) (f : Mx k r → E) :
    tL k r z z' i Y 1 1 f =
      -(chat2L (EH k r) (posL k r i) (uC k r i Y - 1) (yv k r z i) (fun _ => xv k r z' i)
        (ybv k r z i) (fun _ => xbv k r z' i) f) := rfl

lemma left_step (hL : QMinorLeftH) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Y : ℂ) (p q : Fin 2) (F : Mx k r → E) (s g : Mx k r)
    (hy : yv k r z i (s * g) = yv k r z i g) (hyb : ybv k r z i (s * g) = ybv k r z i g) :
    tL k r z z' i Y p q (fun x => F (s * x)) g = tL k r z z' i Y p q F (s * g) := by
  have hq : ∀ {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ),
      qminorOp (EH k r) a b u (fun x => F (s * x)) g = qminorOp (EH k r) a b u F (s * g) := by
    intro t a b u
    exact congrFun (hL E (2 * r + k + 1) t (Hpk k r) F a b u s) g
  match p, q with
  | 0, 0 =>
    rw [tl00, tl00]
    exact hq _ _ _
  | 0, 1 =>
    rw [tl01, tl01]
    simp only [Pi.neg_apply, chatL, hq, hyb]
  | 1, 0 =>
    rw [tl10, tl10]
    simp only [Pi.neg_apply, chatL, hq, hy]
  | 1, 1 =>
    rw [tl11, tl11]
    simp only [Pi.neg_apply, chat2L, hq, hy, hyb]

theorem tInvariant_of_contractions (hCC : ContractionsCovariant) (hP : EabPres) (hG : EabGlLev) (hL : QMinorLeftH)
    (hS : StepS) (hGr : StepGrp) (hV : StepVec) (hC : StepCongr) (hRt : StepRight) (hRS : StepRSm) :
    TInvariant := by
  intro E _ _ k r z z' i D f Y p q hz hz' hDom hf s hs s' hs' g hg
  have hDo : IsOpen D := hDom.1
  obtain ⟨hVl, hVr⟩ := hV k r z z' i hz hz'
  have hsG : s ∈ Glev k r i := ((hS k r z i hz).2 s hs).1
  have hs'G : s' ∈ Glev k r i := ((hS k r z' i hz').2 s' hs').1
  have h1z : (1 : Mx k r) ∈ Slev k r z i := (hS k r z i hz).1
  have h1z' : (1 : Mx k r) ∈ Slev k r z' i := (hS k r z' i hz').1
  have hh : s * g ∈ Glev k r i ∩ D := by
    refine ⟨hGr k r i s hsG g hg.1, ?_⟩
    simpa using hDom.2 g hg s hs 1 h1z'
  have hR : ∀ y ∈ Glev k r i ∩ D, y * s' ∈ Glev k r i ∩ D := fun y hy =>
    ⟨hGr k r i y hy.1 s' hs'G, by simpa using hDom.2 y hy 1 h1z s' hs'⟩
  rw [left_step hL k r z z' i Y p q (fun y => f (y * s')) s g (hVl s hs g).1 (hVl s hs g).2]
  obtain ⟨hQP, hPQ, hxv, hxbv, hyv⟩ := hVr s' hs'
  have hf' : SmoothLev k r i D (ext k r i D (fun p : Pt k r i D => f p.1)) :=
    lev_congr hDo (fun y hy => (ext_at (φ := fun p : Pt k r i D => f p.1) hy).symm) hf
  let x0 : Sm E k r i D := ⟨fun p => f p.1, hf'⟩
  have hrep : Rep f x0.1 := fun _ _ => rfl
  have hrep' : Rep (fun x => f (x * s')) (RL (E := E) hP hC hDo hR hRS hs'G x0).1 := fun _ _ => rfl
  have hint : ∀ a b, Ealg (E := E) (i := i) hP hC hDo a b * RL (E := E) hP hC hDo hR hRS hs'G =
      RL (E := E) hP hC hDo hR hRS hs'G * Econj (Ealg (E := E) (i := i) hP hC hDo) (blk i s'⁻¹) (blk i s') a b :=
    fun a b => RL_inter hP hC hDo hR hRS hs'G hRt a b
  have hGl : GlRel (Ealg (E := E) (i := i) hP hC hDo) := Ealg_gl hP hC hDo hG
  have cov := hCC (Module.End ℂ (Sm E k r i D)) (mdim k r i) (Ealg (E := E) (i := i) hP hC hDo)
    (blk i s'⁻¹) (blk i s') hGl hQP hPQ
  obtain ⟨hyvy, hybvy⟩ := hyv (s * g) hh.1
  have hy' := hR (s * g) hh
  match p, q with
  | 0, 0 =>
    rw [tl00, tl00, qdet_rep hP hC hDo _ hrep' (s * g) hh, qdet_rep hP hC hDo _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (qdet_inter _ _ _ hint _) x0 (s * g) hh,
      (cov (uC k r i Y) 0 0 0 0).1]
  | 0, 1 =>
    have e := (cov (uC k r i Y - 1) (xv k r z' i) 0 (ybv k r z i (s * g * s')) 0).2.1
    rw [hxv, ← hybvy] at e
    rw [tl01, tl01, Pi.neg_apply, Pi.neg_apply, chat_rep hP hC hDo _ _ _ hrep' (s * g) hh,
      chat_rep hP hC hDo _ _ _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (chatA_inter _ _ _ hint _ _ _) x0 (s * g) hh, e]
  | 1, 0 =>
    have e := (cov (uC k r i Y) (yv k r z i (s * g * s')) 0 (xbv k r z' i) 0).2.1
    rw [← hyvy, hxbv] at e
    rw [tl10, tl10, Pi.neg_apply, Pi.neg_apply, chat_rep hP hC hDo _ _ _ hrep' (s * g) hh,
      chat_rep hP hC hDo _ _ _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (chatA_inter _ _ _ hint _ _ _) x0 (s * g) hh, e]
  | 1, 1 =>
    have e := (cov (uC k r i Y - 1) (yv k r z i (s * g * s')) (xv k r z' i) (ybv k r z i (s * g * s'))
      (xbv k r z' i)).2.2
    rw [← hyvy, hxv, ← hybvy, hxbv] at e
    rw [tl11, tl11, Pi.neg_apply, Pi.neg_apply, second_capelli_minor_represents hP hC hDo _ _ _ _ _ hrep' (s * g) hh,
      second_capelli_minor_represents hP hC hDo _ _ _ _ _ hrep (s * g * s') hy',
      RL_apply hP hC hDo hR hRS hs'G _ _ (second_capelli_minor_intertwines _ _ _ hint _ _ _ _ _) x0 (s * g) hh, e]

end Formalism.FourierDecayAlt.Q.TInvW
end
end

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.Q.TInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma glev_mul' {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  simp only [Glev, UH, Set.mem_setOf_eq] at hg hh ⊢
  obtain ⟨hgU, hgF⟩ := hg
  obtain ⟨hhU, hhF⟩ := hh
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [conjTranspose_mul, show hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h by
      simp only [mul_assoc], hgU, hhU]
  · rw [← Matrix.mulVec_mulVec, (hhF a ha).1, (hgF a ha).1]
  · rw [← Matrix.mulVec_mulVec, (hhF a ha).2, (hgF a ha).2]

theorem transfer_invariance_group_mul : StepGrp := fun _ _ _ _ hg _ hh => glev_mul' hg hh

lemma glev_unit {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := by
    simp only [Glev, UH, Set.mem_setOf_eq] at hg
    exact hg.1
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by simp only [mul_assoc], hU, hpk_sq]
  rw [Matrix.inv_eq_left_inv hl]
  exact ⟨mul_eq_one_comm.mp hl, hl⟩

lemma inv_fix {g : Mx k r} (hu : g⁻¹ * g = 1) {v : Fin (2 * r + k + 1) → ℂ} (h : g *ᵥ v = v) :
    g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]

lemma glev_inv {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ ∈ Glev k r i := by
  have hu := glev_unit hg
  simp only [Glev, UH, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, hF⟩ := hg
  refine ⟨?_, fun a ha => ⟨inv_fix hu.2 (hF a ha).1, inv_fix hu.2 (hF a ha).2⟩⟩
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hU]
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by rw [conjTranspose_mul]; simp only [mul_assoc]
    _ = Hpk k r := by rw [hu.1, conjTranspose_one, one_mul, mul_one]

lemma H_esI (a : Fin r) (w : Fin (2 * r + k + 1) → ℂ) : (Hpk k r *ᵥ w) (esI k r a) = w (eI k r a) := by
  have ha := a.isLt
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (eI k r a)]
  · have h1 : Hpk k r (esI k r a) (eI k r a) = 1 := by
      simp only [Hpk, eI, esI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ a.val := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have h0 : Hpk k r (esI k r a) j = 0 := by
      simp only [Hpk, esI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma H_eI (a : Fin r) (w : Fin (2 * r + k + 1) → ℂ) : (Hpk k r *ᵥ w) (eI k r a) = w (esI k r a) := by
  have ha := a.isLt
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (esI k r a)]
  · have h1 : Hpk k r (eI k r a) (esI k r a) = 1 := by
      simp only [Hpk, eI, esI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ 2 * r + k - a.val := fun h => hj (Fin.ext h)
    have hjl := j.isLt
    have h0 : Hpk k r (eI k r a) j = 0 := by
      simp only [Hpk, eI, Fin.ext_iff]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma coord {g : Mx k r} (hg : g ∈ UH (Hpk k r)) (c d : Fin (2 * r + k + 1))
    (hcd : ∀ w, (Hpk k r *ᵥ w) c = w d) (hfix : g *ᵥ bvec c = bvec c) (v : Fin (2 * r + k + 1) → ℂ) :
    (g *ᵥ v) d = v d := by
  have hU : gᴴ * Hpk k r * g = Hpk k r := hg
  have hcol : ∀ l, g l c = bvec c l := fun l => by
    rw [← congrFun hfix l]
    simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]
  have hrow : ∀ j, (Hpk k r * g) c j = Hpk k r c j := by
    intro j
    have h1 := congrFun (congrFun hU c) j
    rw [Matrix.mul_assoc, Matrix.mul_apply] at h1
    rw [← h1, Finset.sum_eq_single c]
    · rw [conjTranspose_apply, hcol]
      simp [bvec]
    · intro l _ hl
      rw [conjTranspose_apply, hcol]
      simp [bvec, Pi.single_apply, hl]
    · intro h
      exact absurd (Finset.mem_univ c) h
  have key : (Hpk k r *ᵥ (g *ᵥ v)) c = (Hpk k r *ᵥ v) c := by
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, hrow]
  calc (g *ᵥ v) d = (Hpk k r *ᵥ (g *ᵥ v)) c := (hcd _).symm
    _ = (Hpk k r *ᵥ v) c := key
    _ = v d := hcd v

lemma outer {i : Fin (r + 1)} (q : Fin (2 * r + k + 1)) (hq : ∀ c, q ≠ posL k r i c) :
    ∃ a : Fin r, a.val < i.val ∧ (q = eI k r a ∨ q = esI k r a) := by
  have hq' := q.isLt
  have hi := i.isLt
  by_cases h1 : q.val < i.val
  · exact ⟨⟨q.val, by omega⟩, h1, Or.inl (Fin.ext rfl)⟩
  · have h2 : 2 * r + k - i.val < q.val := by
      by_contra h3
      exact hq ⟨q.val - i.val, by unfold mdim; omega⟩ (Fin.ext (by simp only [posL]; omega))
    exact ⟨⟨2 * r + k - q.val, by omega⟩, by simp only; omega, Or.inr (Fin.ext (by simp only [esI]; omega))⟩

lemma glev_fix_outer {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g *ᵥ bvec q = bvec q := by
  obtain ⟨a, ha, hq'⟩ := outer q hq
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  rcases hq' with rfl | rfl
  · exact (hg'.2 a ha).1
  · exact (hg'.2 a ha).2

lemma glev_col {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (p q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g p q = bvec q p := by
  rw [← congrFun (glev_fix_outer hg q hq) p]
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

lemma glev_row {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) (v : Fin (2 * r + k + 1) → ℂ) : (g *ᵥ v) q = v q := by
  have hg' : g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := hg
  obtain ⟨a, ha, hq'⟩ := outer q hq
  rcases hq' with rfl | rfl
  · exact coord hg'.1 (esI k r a) (eI k r a) (H_esI a) (hg'.2 a ha).2 v
  · exact coord hg'.1 (eI k r a) (esI k r a) (H_eI a) (hg'.2 a ha).1 v

lemma glev_row' {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) (q p : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : g q p = bvec p q := by
  rw [← glev_row hg q hq (bvec p)]
  simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]

lemma sum_posL {M : Type*} [AddCommMonoid M] {i : Fin (r + 1)} (F : Fin (2 * r + k + 1) → M)
    (hF : ∀ q, (∀ c, q ≠ posL k r i c) → F q = 0) :
    ∑ q, F q = ∑ c : Fin (mdim k r i), F (posL k r i c) := (Fintype.sum_of_injective (posL k r i) (fun _ _ h => posL_inj h) _ F
    (fun q hq => hF q (fun c hc => hq ⟨c, hc.symm⟩)) (fun _ => rfl)).symm

lemma bvec_posL_outer {i : Fin (r + 1)} (a : Fin (mdim k r i)) (q : Fin (2 * r + k + 1))
    (hq : ∀ c, q ≠ posL k r i c) : bvec q (posL k r i a) = 0 ∧ bvec (posL k r i a) q = 0 := ⟨by simp [bvec, Pi.single_apply, hq a, (hq a).symm], by simp [bvec, Pi.single_apply, hq a, (hq a).symm]⟩

lemma n_fix {z : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} (hz : inWb k r z) {m : Mx k r}
    (hm : m ∈ Nlev k r i) : m *ᵥ fvec k r z i = fvec k r z i := by
  unfold Nlev at hm
  simp only [QuantumDeterminants.Nset, Set.mem_inter_iff, Set.mem_setOf_eq] at hm
  obtain ⟨⟨_, hcol, hmid⟩, hG⟩ := hm
  unfold inWb at hz
  unfold fvec
  split_ifs with hi
  · funext x
    rw [show (m *ᵥ bvec (eI k r ⟨i.val, hi⟩)) x = m x (eI k r ⟨i.val, hi⟩) by
      simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply]]
    by_cases hx : i.val ≤ x.val
    · rw [hcol ⟨i.val, hi⟩ x hx]
      simp [bvec, Pi.single_apply]
    · have hout : ∀ c, x ≠ posL k r i c := fun c h => hx (by
        have h2 := congrArg Fin.val h
        simp only [posL] at h2
        omega)
      rw [glev_row' hG x (eI k r ⟨i.val, hi⟩) hout]
  · funext x
    by_cases hx : r ≤ x.val
    · simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single x]
      · by_cases hxk : x.val ≤ r + k
        · rw [hmid x x hx hxk hx]
          simp
        · rw [hz x (Or.inr (by omega)), mul_zero]
      · intro j _ hj
        by_cases hjm : r ≤ j.val ∧ j.val ≤ r + k
        · rw [hmid x j hjm.1 hjm.2 hx, if_neg (Ne.symm hj), zero_mul]
        · rw [hz j (by omega), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have hout : ∀ c, x ≠ posL k r i c := fun c h => hx (by
        have h2 := congrArg Fin.val h
        simp only [posL] at h2
        omega)
      exact glev_row hG x hout z

lemma h_fix {z : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {h : Mx k r} (hh : h ∈ UWset k r z) :
    h *ᵥ fvec k r z i = fvec k r z i := by
  simp only [UWset, Set.mem_setOf_eq] at hh
  unfold fvec
  split_ifs with hi
  · exact (hh.2.1 _).1
  · exact hh.2.2

theorem transfer_invariance_smooth : StepS := by
  intro k r z i hz
  have hUW : ∀ h ∈ UWset k r z, h ∈ Glev k r i := by
    intro h hh
    simp only [UWset, Glev, Set.mem_setOf_eq] at hh ⊢
    exact ⟨hh.1, fun a _ => hh.2.1 a⟩
  simp only [Slev, Set.mem_setOf_eq]
  refine ⟨⟨1, ?_, 1, ?_, (mul_one 1).symm⟩, ?_⟩
  · simp [UWset, UH]
  · simp [Nlev, QuantumDeterminants.Nset, Glev, UH, Matrix.one_apply]
  · rintro s ⟨h, hh, m, hm, rfl⟩
    have hmG : m ∈ Glev k r i := by
      unfold Nlev at hm
      exact hm.2
    refine ⟨glev_mul' (hUW h hh) hmG, ?_⟩
    rw [← Matrix.mulVec_mulVec, n_fix hz hm, h_fix hh]

lemma herm_uh {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (s *ᵥ v) (s *ᵥ w) = herm (Hpk k r) v w := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [← Matrix.mul_assoc, hs']

lemma herm_col (M : Mx k r) (q : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (M *ᵥ bvec q) w = (star w ᵥ* Hpk k r ᵥ* M) q := by
  unfold herm
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
  simp [bvec]

lemma herm_bv (q : Fin (2 * r + k + 1)) (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec q) w = (star w ᵥ* Hpk k r) q := by
  unfold herm
  rw [Matrix.dotProduct_mulVec]
  simp [bvec]

lemma uh_H_inv {s : Mx k r} (hs : s ∈ UH (Hpk k r)) (hu : s * s⁻¹ = 1) :
    Hpk k r * s⁻¹ = sᴴ * Hpk k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  calc Hpk k r * s⁻¹ = sᴴ * Hpk k r * s * s⁻¹ := by rw [hs']
    _ = sᴴ * Hpk k r := by rw [mul_assoc (sᴴ * Hpk k r), hu, mul_one]

theorem transfer_invariance_vector : StepVec := by
  intro k r z z' i hz hz'
  have bo : ∀ (a : Fin (mdim k r i)) q, (∀ c, q ≠ posL k r i c) →
      bvec q (posL k r i a) = 0 ∧ bvec (posL k r i a) q = 0 :=
    fun a q hq => bvec_posL_outer a q hq
  have blk_mul : ∀ s t : Mx k r, s ∈ Glev k r i → blk i (s * t) = blk i s * blk i t := by
    intro s t hs
    ext a b
    simp only [blk, Matrix.mul_apply]
    exact sum_posL (fun q => s (posL k r i a) q * t q (posL k r i b)) (fun q hq => by
      show s (posL k r i a) q * t q (posL k r i b) = 0
      rw [glev_col hs (posL k r i a) q hq, (bo a q hq).1, zero_mul])
  have blk_one : blk i (1 : Mx k r) = 1 := by
    ext a b
    simp only [blk, Matrix.one_apply]
    by_cases h : a = b
    · simp [h]
    · rw [if_neg (fun e => h (posL_inj e)), if_neg h]
  have mv_blk : ∀ s ∈ Glev k r i, ∀ v : Fin (2 * r + k + 1) → ℂ,
      (blk i s *ᵥ fun j => v (posL k r i j)) = fun j => (s *ᵥ v) (posL k r i j) := by
    intro s hs v
    funext a
    simp only [blk, Matrix.mulVec, dotProduct]
    exact (sum_posL (fun q => s (posL k r i a) q * v q) (fun q hq => by
      show s (posL k r i a) q * v q = 0
      rw [glev_col hs (posL k r i a) q hq, (bo a q hq).1, zero_mul])).symm
  have vm_blk : ∀ t ∈ Glev k r i, ∀ x : Fin (2 * r + k + 1) → ℂ,
      ((fun j => x (posL k r i j)) ᵥ* blk i t) = fun j => (x ᵥ* t) (posL k r i j) := by
    intro t ht x
    funext b
    simp only [blk, Matrix.vecMul, dotProduct]
    exact (sum_posL (fun q => x q * t q (posL k r i b)) (fun q hq => by
      show x q * t q (posL k r i b) = 0
      rw [glev_row' ht q (posL k r i b) hq, (bo b q hq).2, mul_zero])).symm
  have hS := transfer_invariance_smooth k r z i hz
  have hS' := transfer_invariance_smooth k r z' i hz'
  refine ⟨fun s hs g => ?_, fun s' hs' => ?_⟩
  · obtain ⟨hsG, hsf⟩ := hS.2 s hs
    have hu := glev_unit hsG
    have hsU : s ∈ UH (Hpk k r) := by
      simp only [Glev, Set.mem_setOf_eq] at hsG
      exact hsG.1
    have hinv : s⁻¹ *ᵥ fvec k r z i = fvec k r z i := inv_fix hu.2 hsf
    constructor
    · funext j
      simp only [yv]
      rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, hinv]
    · funext j
      simp only [ybv]
      conv_lhs => rw [← hsf]
      rw [← Matrix.mulVec_mulVec, herm_uh hsU]
  · obtain ⟨hsG, hsf⟩ := hS'.2 s' hs'
    have hu := glev_unit hsG
    have hiG := glev_inv hsG
    have hsU : s' ∈ UH (Hpk k r) := by
      have h0 := hsG
      simp only [Glev, Set.mem_setOf_eq] at h0
      exact h0.1
    refine ⟨?_, ?_, ?_, ?_, fun g hg => ⟨?_, ?_⟩⟩
    · rw [← blk_mul _ _ hsG, hu.1, blk_one]
    · rw [← blk_mul _ _ hiG, hu.2, blk_one]
    · unfold xv
      rw [mv_blk _ hsG, hsf]
    · unfold xbv
      simp only [herm_bv]
      rw [vm_blk _ hiG, Matrix.vecMul_vecMul, uh_H_inv hsU hu.1, ← Matrix.vecMul_vecMul, ← Matrix.star_mulVec, hsf]
    · unfold yv
      rw [mv_blk _ hsG]
      funext j
      rw [Matrix.mulVec_mulVec, Matrix.mul_inv_rev, ← Matrix.mul_assoc, hu.1, Matrix.one_mul]
    · unfold ybv
      simp only [herm_col]
      rw [vm_blk _ hiG]
      simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc, hu.1, Matrix.mul_one]

theorem transfer_invariance_restriction : StepRSm := by
  intro E _ _ k r i D f s' hs' hD hf g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g₀ * s') ⟨glev_mul' hg₀.1 hs', hD g₀ hg₀⟩
  let L : Mx k r →L[ℝ] Mx k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ s')
  have hL : ∀ x, L x = x * s' := fun _ => rfl
  refine ⟨L ⁻¹' U, fun x => F (L x), hU.preimage L.continuous, by simpa [hL] using hgU,
    hF.comp L.contDiff.contDiffOn (fun _ hx => hx), fun x hx hxG => ?_⟩
  have hx' : x * s' ∈ U := by rw [← hL]; exact hx
  show f (x * s') = F (L x)
  rw [hL]
  exact hfF _ hx' (glev_mul' hxG hs')

end Formalism.FourierDecayAlt.Q.TInvW
