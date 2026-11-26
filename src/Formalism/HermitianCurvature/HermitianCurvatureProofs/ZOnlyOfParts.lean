module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenDomP

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ContDiffOnInvConjDet
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ContDiffOfSnd
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {j : ℕ}

theorem cont_ofSnd : Continuous fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of q.2 : MJ j) := continuous_snd

theorem contDiff_ofSnd : ContDiff ℝ ∞ fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of q.2 : MJ j) := contDiff_snd

theorem contDiff_pair (τ : ℂ) : ContDiff ℝ ∞ fun Z : MJ j => ((τ, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) :=
  contDiff_const.prodMk contDiff_id

theorem isOpen_inv : IsOpen {Z : MJ j | Z.det ≠ 0} :=
  isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const

theorem diffAt_fst {G : ℂ × (Fin j → Fin j → ℂ) → E} {U : Set (ℂ × (Fin j → Fin j → ℂ))} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {q : ℂ × (Fin j → Fin j → ℂ)} (hq : q ∈ U) :
    DifferentiableAt ℝ (fun τ : ℂ => G (τ, q.2)) q.1 := by
  have hd : DifferentiableAt ℝ G q := (hG.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq)
  exact hd.comp q.1 ((differentiableAt_id).prodMk (differentiableAt_const _))

theorem dz_add {F G : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (hG : DifferentiableAt ℝ G τ) :
    PBP.dz (fun s => F s + G s) τ = PBP.dz F τ + PBP.dz G τ := by
  unfold PBP.dz
  rw [show (fun s => F s + G s) = F + G from rfl, (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv]
  simp only [_root_.add_apply]
  module

theorem dzb_add {F G : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (hG : DifferentiableAt ℝ G τ) :
    PBP.dzb (fun s => F s + G s) τ = PBP.dzb F τ + PBP.dzb G τ := by
  unfold PBP.dzb
  rw [show (fun s => F s + G s) = F + G from rfl, (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv]
  simp only [_root_.add_apply]
  module

theorem dz_smul {F : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (c : ℂ) :
    PBP.dz (fun s => c • F s) τ = c • PBP.dz F τ := by
  unfold PBP.dz
  rw [show (fun s => c • F s) = c • F from rfl, (hF.hasFDerivAt.const_smul c).fderiv]
  simp only [_root_.smul_apply]
  module

theorem dzb_smul {F : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (c : ℂ) :
    PBP.dzb (fun s => c • F s) τ = c • PBP.dzb F τ := by
  unfold PBP.dzb
  rw [show (fun s => c • F s) = c • F from rfl, (hF.hasFDerivAt.const_smul c).fderiv]
  simp only [_root_.smul_apply]
  module

theorem dz_const (v : E) (τ : ℂ) : PBP.dz (fun _ : ℂ => v) τ = 0 := by simp [PBP.dz]

theorem dzb_const (v : E) (τ : ℂ) : PBP.dzb (fun _ : ℂ => v) τ = 0 := by simp [PBP.dzb]

theorem zop_id : ZOp (E := E) (j := j) (fun h => h) := by
  refine ⟨fun h₁ h₂ Z h => h.eq_of_nhds, fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl, ?_⟩
  intro U κ _ _ hκ
  exact ⟨hκ, fun q _ => ⟨rfl, rfl⟩⟩

theorem zop_zero : ZOp (E := E) (j := j) (fun _ _ => 0) := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ _ => by simp, ?_⟩
  intro U κ _ _ _
  exact ⟨contDiffOn_const, fun q _ => ⟨dz_const _ _, dzb_const _ _⟩⟩

theorem ZOp.smooth {T : (MJ j → E) → MJ j → E} (hT : ZOp T) {V : Set (MJ j)} (hV : IsOpen V)
    (hVi : V ⊆ {Z | Z.det ≠ 0}) {h : MJ j → E} (hh : ContDiffOn ℝ ∞ h V) : ContDiffOn ℝ ∞ (T h) V := by
  let U : Set (ℂ × (Fin j → Fin j → ℂ)) := {q | (Matrix.of q.2 : MJ j) ∈ V}
  have hU : IsOpen U := hV.preimage cont_ofSnd
  have hUi : U ⊆ {q | (Matrix.of q.2).det ≠ 0} := fun q hq => hVi hq
  have hκ : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => (fun _ : ℂ => h) q.1 (Matrix.of q.2)) U :=
    hh.comp contDiff_ofSnd.contDiffOn (fun q hq => hq)
  have h1 := (hT.par U (fun _ => h) hU hUi hκ).1
  exact h1.comp (contDiff_pair 0).contDiffOn (fun Z hZ => hZ)

theorem ZOp.add' {T S : (MJ j → E) → MJ j → E} (hT : ZOp T) (hS : ZOp S) :
    ZOp (fun h Z => T h Z + S h Z) := by
  refine ⟨fun h₁ h₂ Z h => by rw [hT.loc _ _ Z h, hS.loc _ _ Z h], ?_, ?_, ?_⟩
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    rw [hT.add V h₁ h₂ hV hVi s₁ s₂ Z hZ, hS.add V h₁ h₂ hV hVi s₁ s₂ Z hZ]; abel
  · intro V c h hV hVi s Z hZ
    rw [hT.smul V c h hV hVi s Z hZ, hS.smul V c h hV hVi s Z hZ, smul_add]
  · intro U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U κ hU hUi hκ
    obtain ⟨s1, s2⟩ := hS.par U κ hU hUi hκ
    refine ⟨t1.add s1, fun q hq => ?_⟩
    have d1 := diffAt_fst hU t1 hq
    have d2 := diffAt_fst hU s1 hq
    refine ⟨?_, ?_⟩
    · rw [dz_add d1 d2, (t2 q hq).1, (s2 q hq).1]
    · rw [dzb_add d1 d2, (t2 q hq).2, (s2 q hq).2]

theorem ZOp.cmul {T : (MJ j → E) → MJ j → E} (hT : ZOp T) {c : MJ j → ℂ}
    (hc : ContDiffOn ℝ ∞ c {Z | Z.det ≠ 0}) : ZOp (fun h Z => c Z • T h Z) := by
  refine ⟨fun h₁ h₂ Z h => by rw [hT.loc _ _ Z h], ?_, ?_, ?_⟩
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    rw [hT.add V h₁ h₂ hV hVi s₁ s₂ Z hZ, smul_add]
  · intro V c' h hV hVi s Z hZ
    rw [hT.smul V c' h hV hVi s Z hZ, smul_comm]
  · intro U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U κ hU hUi hκ
    have hc' : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => c (Matrix.of q.2)) U :=
      hc.comp contDiff_ofSnd.contDiffOn (fun q hq => hUi hq)
    refine ⟨hc'.smul t1, fun q hq => ?_⟩
    have d1 := diffAt_fst hU t1 hq
    exact ⟨by rw [dz_smul d1, (t2 q hq).1], by rw [dzb_smul d1, (t2 q hq).2]⟩

theorem ZOp.csmul {T : (MJ j → E) → MJ j → E} (hT : ZOp T) (c : ℂ) : ZOp (fun h Z => c • T h Z) :=
  hT.cmul (c := fun _ => c) contDiffOn_const

theorem ZOp.comp {T S : (MJ j → E) → MJ j → E} (hT : ZOp T) (hS : ZOp S) : ZOp (fun h => T (S h)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h₁ h₂ Z h
    apply hT.loc
    filter_upwards [h.eventually_nhds] with Z' hZ'
    exact hS.loc _ _ Z' hZ'
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    have e : S (h₁ + h₂) =ᶠ[𝓝 Z] S h₁ + S h₂ := by
      filter_upwards [hV.mem_nhds hZ] with Z' hZ'
      exact hS.add V h₁ h₂ hV hVi s₁ s₂ Z' hZ'
    rw [hT.loc _ _ Z e]
    exact hT.add V (S h₁) (S h₂) hV hVi (hS.smooth hV hVi s₁) (hS.smooth hV hVi s₂) Z hZ
  · intro V c h hV hVi s Z hZ
    have e : S (c • h) =ᶠ[𝓝 Z] c • S h := by
      filter_upwards [hV.mem_nhds hZ] with Z' hZ'
      exact hS.smul V c h hV hVi s Z' hZ'
    rw [hT.loc _ _ Z e]
    exact hT.smul V c (S h) hV hVi (hS.smooth hV hVi s) Z hZ
  · intro U κ hU hUi hκ
    obtain ⟨s1, s2⟩ := hS.par U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U (fun τ => S (κ τ)) hU hUi s1
    refine ⟨t1, fun q hq => ?_⟩
    have hsl : IsOpen {Z : MJ j | ((q.1, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) ∈ U} :=
      hU.preimage (contDiff_pair q.1).continuous
    have e1 : (fun Z => PBP.dz (fun τ => S (κ τ) Z) q.1) =ᶠ[𝓝 (Matrix.of q.2)]
        S (fun Z => PBP.dz (fun τ => κ τ Z) q.1) := by
      filter_upwards [hsl.mem_nhds (show (q.1, q.2) ∈ U from hq)] with Z hZ
      exact (s2 (q.1, (Z : Fin j → Fin j → ℂ)) hZ).1
    have e2 : (fun Z => PBP.dzb (fun τ => S (κ τ) Z) q.1) =ᶠ[𝓝 (Matrix.of q.2)]
        S (fun Z => PBP.dzb (fun τ => κ τ Z) q.1) := by
      filter_upwards [hsl.mem_nhds (show (q.1, q.2) ∈ U from hq)] with Z hZ
      exact (s2 (q.1, (Z : Fin j → Fin j → ℂ)) hZ).2
    exact ⟨by rw [(t2 q hq).1, hT.loc _ _ _ e1], by rw [(t2 q hq).2, hT.loc _ _ _ e2]⟩

theorem zop_sum {ι : Type*} (s : Finset ι) {T : ι → (MJ j → E) → MJ j → E} (hT : ∀ i ∈ s, ZOp (T i)) :
    ZOp (fun h Z => ∑ i ∈ s, T i h Z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zop_zero (E := E) (j := j))
  | insert a s ha ih =>
    have h1 := (hT a (by simp)).add' (ih (fun i hi => hT i (by simp [hi])))
    simpa [Finset.sum_insert ha] using h1

theorem zop_foldr : ∀ L : List ((MJ j → E) → MJ j → E), (∀ T ∈ L, ZOp T) →
    ZOp (fun f => L.foldr (fun T h => T h) f)
  | [], _ => zop_id
  | T :: L, h => by
    simp only [List.foldr_cons]
    exact (h T (by simp)).comp (zop_foldr L (fun T' hT' => h T' (by simp [hT'])))

end Formalism.FourierDecayAlt.P.WirtingerOperators
end
end

open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def TopG {ι X : Type} [DecidableEq ι] (Eop : ι → ι → (X → E) → (X → E)) (u : ℂ) (a b : ι) (f : X → E) : X → E :=
  fun g => (if a = b then u • f g else 0) + Eop a b f g

def qminG {ι X : Type} [DecidableEq ι] {t : ℕ} (Eop : ι → ι → (X → E) → (X → E)) (a b : Fin t → ι) (u : ℂ)
    (f : X → E) : X → E :=
  ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun k : Fin t => TopG Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).foldr (fun T h => T h) f)

def EopZ (k r j : ℕ) (p q : Fin (2 * r + k + 1)) : (MJ j → E) → MJ j → E :=
  if hp : p.val < j then (if hq : q.val < j then EZ ⟨p.val, hp⟩ ⟨q.val, hq⟩ else fun _ _ => 0)
  else if hp' : 2 * r + k < p.val + j then
    (if hq' : 2 * r + k < q.val + j then
      EZs ⟨2 * r + k - p.val, by omega⟩ ⟨2 * r + k - q.val, by omega⟩ else fun _ _ => 0)
  else fun _ _ => 0

def cZ {j N : ℕ} (Z : MJ j) (p : Fin N) (a : Fin j) : ℂ := if hp : p.val < j then Z a ⟨p.val, hp⟩ else 0

def cvZ (k r : ℕ) {j : ℕ} (Z : MJ j) (p : Fin (2 * r + k + 1)) (a : Fin j) : ℂ :=
  if hp : 2 * r + k < p.val + j then conj (Z a ⟨2 * r + k - p.val, by omega⟩) else 0


open scoped Classical in
def AZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (u : ℂ) (h : MJ j → E) : MJ j → E := fun Z =>
  ∑ c : Fin m → Fin (2 * r + k + 1),
    if StrictMono c then
      (Matrix.of fun a l : Fin m => cZ Z (c l) (Fin.castLE hmj a)).det •
        qminG (EopZ (E := E) k r j) (C3.xR k r m hm) c u h Z
    else 0


open scoped Classical in
def AvZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (ell : ℂ) (h : MJ j → E) : MJ j → E := fun Z =>
  ∑ B : Fin m → Fin (2 * r + k + 1),
    if StrictMono (fun l => C3.keyS k r (B l)) then
      (Matrix.of fun a l : Fin m => cvZ k r Z (B l) (Fin.castLE hmj a)).det •
        qminG (EopZ (E := E) k r j) B (C3.sR k r m hm) (ell + (m : ℂ) - 1) h Z
    else 0

def Aform (k r j : ℕ) (hj : j + 1 ≤ r) (l : C.Letter) (e : Fin 2) (h : MJ j → E) : MJ j → E := fun Z =>
  if e = 1 ∧ j = 0 then 0 else
  if l.1 then
    (Z.det)⁻¹ • AZ k r j (j - e) (by omega) (by omega) ((l.2 : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) h Z
  else
    (conj Z.det)⁻¹ • AvZ k r j (j - e) (by omega) (by omega) ((l.2 : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) h Z

section zop

variable (hR : ZOpRd)
include hR

theorem zop_EZ {j : ℕ} (a b : Fin j) : ZOp (E := E) (EZ a b) :=
  (hR j E _).add' ((hR j E _).csmul Complex.I)

theorem zop_EZs {j : ℕ} (a b : Fin j) : ZOp (E := E) (EZs a b) :=
  (hR j E _).add' ((hR j E _).csmul Complex.I)

theorem zop_EopZ (k r j : ℕ) (p q : Fin (2 * r + k + 1)) : ZOp (E := E) (EopZ k r j p q) := by
  unfold EopZ
  split_ifs
  · exact zop_EZ hR _ _
  · exact zop_zero
  · exact zop_EZs hR _ _
  · exact zop_zero
  · exact zop_zero

theorem zop_TopG (k r j : ℕ) (u : ℂ) (p q : Fin (2 * r + k + 1)) :
    ZOp (E := E) (TopG (EopZ k r j) u p q) := by
  have h1 : ZOp (E := E) (j := j) (fun f g => if p = q then u • f g else 0) := by
    split_ifs
    · exact zop_id.csmul u
    · exact zop_zero
  exact h1.add' (zop_EopZ hR k r j p q)

theorem zop_qminG (k r j : ℕ) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    ZOp (E := E) (qminG (EopZ k r j) a b u) := by
  have e : (qminG (E := E) (EopZ k r j) a b u) = fun h Z => ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin t))),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun k' : Fin t =>
        TopG (EopZ (E := E) k r j) (u - ((k' : ℕ) : ℂ)) (a (σ k')) (b k')).foldr (fun T h => T h) h Z) := by
    funext h Z
    simp [qminG, Finset.sum_apply]
  rw [e]
  refine zop_sum _ (fun σ _ => ?_)
  refine ZOp.csmul ?_ _
  refine zop_foldr _ (fun T hT => ?_)
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
  exact zop_TopG hR k r j _ _ _

end zop

theorem contDiff_entry {j : ℕ} (a b : Fin j) : ContDiff ℝ ∞ fun Z : MJ j => Z a b :=
  (contDiff_apply ℝ (fun _ => ℂ) b).comp (contDiff_apply ℝ (fun _ => (Fin j → ℂ)) a)

theorem contDiff_det_of {j m : ℕ} (M : MJ j → Matrix (Fin m) (Fin m) ℂ) (hM : ∀ a b, ContDiff ℝ ∞ fun Z => M Z a b) :
    ContDiff ℝ ∞ fun Z => (M Z).det := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum (fun σ _ => ?_)
  simp only [Units.smul_def, zsmul_eq_mul]
  exact contDiff_const.mul (contDiff_prod (fun i _ => hM _ _))

theorem contDiff_cZ {j N : ℕ} (p : Fin N) (a : Fin j) : ContDiff ℝ ∞ fun Z : MJ j => cZ Z p a := by
  unfold cZ
  split_ifs
  · exact contDiff_entry _ _
  · exact contDiff_const

theorem contDiff_cvZ (k r : ℕ) {j : ℕ} (p : Fin (2 * r + k + 1)) (a : Fin j) :
    ContDiff ℝ ∞ fun Z : MJ j => cvZ k r Z p a := by
  unfold cvZ
  split_ifs
  · exact Complex.conjCLE.contDiff.comp (contDiff_entry _ _)
  · exact contDiff_const

theorem contDiffOn_invDet {j : ℕ} : ContDiffOn ℝ ∞ (fun Z : MJ j => (Z.det)⁻¹) {Z | Z.det ≠ 0} :=
  (contDiff_det_of (fun Z => Z) (fun a b => contDiff_entry a b)).contDiffOn.inv (fun Z hZ => hZ)

theorem contDiffOn_invConjDet {j : ℕ} :
    ContDiffOn ℝ ∞ (fun Z : MJ j => (conj Z.det)⁻¹) {Z | Z.det ≠ 0} :=
  (Complex.conjCLE.contDiff.comp (contDiff_det_of (fun Z => Z) (fun a b => contDiff_entry a b))).contDiffOn.inv
    (fun Z hZ => by simpa using hZ)

section zop2

variable (hR : ZOpRd)
include hR

theorem zop_AZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (u : ℂ) : ZOp (E := E) (AZ k r j m hm hmj u) := by
  classical
  unfold AZ
  refine zop_sum _ (fun c _ => ?_)
  split_ifs
  · exact (zop_qminG hR k r j _ _ u).cmul
      (contDiff_det_of _ (fun a l => contDiff_cZ _ _)).contDiffOn
  · exact zop_zero

theorem zop_AvZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (ell : ℂ) : ZOp (E := E) (AvZ k r j m hm hmj ell) := by
  classical
  unfold AvZ
  refine zop_sum _ (fun c _ => ?_)
  split_ifs
  · exact (zop_qminG hR k r j _ _ _).cmul
      (contDiff_det_of _ (fun a l => contDiff_cvZ k r _ _)).contDiffOn
  · exact zop_zero

theorem zop_Aform (k r j : ℕ) (hj : j + 1 ≤ r) (l : C.Letter) (e : Fin 2) :
    ZOp (E := E) (Aform k r j hj l e) := by
  unfold Aform
  split_ifs
  · exact zop_zero
  · exact (zop_AZ hR _ _ _ _ _ _ _).cmul contDiffOn_invDet
  · exact (zop_AvZ hR _ _ _ _ _ _ _).cmul contDiffOn_invConjDet

end zop2
end Formalism.FourierDecayAlt.P.WirtingerOperators
end
end

open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

section transfer

variable {k r j : ℕ} (hj : j + 1 ≤ r) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))

def Good (k r j : ℕ) (p q : Fin (2 * r + k + 1)) : Prop :=
  (p.val < j ∧ q.val < j) ∨ (2 * r + k < p.val + j ∧ 2 * r + k < q.val + j)

theorem rdV_levi (hC : CurveLevi) (x : MJ j) (f : Q.Mx k r → E) (Z : MJ j) :
    RdV (levi k r j x) f (x0 k r j hj Z τ γ) = RdV x (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  unfold RdV
  congr 1
  funext t
  rw [hC k r j hj Z τ γ x t]

theorem EopZ_e (a b : Fin j) :
    EopZ (E := E) k r j (eI k r (Fin.castLE (by omega) a)) (eI k r (Fin.castLE (by omega) b)) = EZ a b := by
  unfold EopZ
  simp [eI]

theorem EopZ_es (a b : Fin j) :
    EopZ (E := E) k r j (esI k r (Fin.castLE (by omega) a)) (esI k r (Fin.castLE (by omega) b)) = EZs a b := by
  unfold EopZ
  have ha := a.isLt
  have hb := b.isLt
  rw [dite_eq_right (by simp [esI]; omega), dif_pos (by simp [esI]; omega), dif_pos (by simp [esI]; omega)]
  congr 1 <;> ext <;> simp [esI] <;> omega

theorem eab_pull (hC : CurveLevi) (hH : HpartLevi) (p q : Fin (2 * r + k + 1)) (hpq : Good k r j p q)
    (f : Q.Mx k r → E) (Z : MJ j) :
    EabH (Hpk k r) p q f (x0 k r j hj Z τ γ) = EopZ k r j p q (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  have hjr : j ≤ r := by omega
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · obtain ⟨a, rfl⟩ : ∃ a : Fin j, p = eI k r (Fin.castLE hjr a) := ⟨⟨p.val, hp⟩, Fin.ext rfl⟩
    obtain ⟨b, rfl⟩ : ∃ b : Fin j, q = eI k r (Fin.castLE hjr b) := ⟨⟨q.val, hq⟩, Fin.ext rfl⟩
    rw [EopZ_e hj]
    unfold EabH EZ
    rw [(hH k r j hjr a b).1, (hH k r j hjr a b).2.1, rdV_levi hj τ γ hC, rdV_levi hj τ γ hC]
  · have hp2 := p.isLt
    have hq2 := q.isLt
    obtain ⟨a, rfl⟩ : ∃ a : Fin j, p = esI k r (Fin.castLE hjr a) :=
      ⟨⟨2 * r + k - p.val, by omega⟩, Fin.ext (by simp [esI]; omega)⟩
    obtain ⟨b, rfl⟩ : ∃ b : Fin j, q = esI k r (Fin.castLE hjr b) :=
      ⟨⟨2 * r + k - q.val, by omega⟩, Fin.ext (by simp [esI]; omega)⟩
    rw [EopZ_es hj]
    unfold EabH EZs
    rw [(hH k r j hjr a b).2.2.1, (hH k r j hjr a b).2.2.2, rdV_levi hj τ γ hC, rdV_levi hj τ γ hC]

theorem top_pull (hC : CurveLevi) (hH : HpartLevi) (u : ℂ) (p q : Fin (2 * r + k + 1)) (hpq : Good k r j p q)
    (f : Q.Mx k r → E) (Z : MJ j) :
    QuantumDeterminants.Top (EabH (Hpk k r)) u p q f (x0 k r j hj Z τ γ) =
      TopG (EopZ k r j) u p q (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  unfold QuantumDeterminants.Top TopG
  rw [eab_pull hj τ γ hC hH p q hpq]

def Rel (T : (Q.Mx k r → E) → Q.Mx k r → E) (S : (MJ j → E) → MJ j → E) : Prop :=
  ∀ (f : Q.Mx k r → E) (Z : MJ j), T f (x0 k r j hj Z τ γ) = S (fun Z' => f (x0 k r j hj Z' τ γ)) Z

theorem foldr_pull : ∀ (L₁ : List ((Q.Mx k r → E) → Q.Mx k r → E)) (L₂ : List ((MJ j → E) → MJ j → E)),
    List.Forall₂ (Rel (E := E) hj τ γ) L₁ L₂ →
    ∀ (f : Q.Mx k r → E) (Z : MJ j),
      (L₁.foldr (fun (T : (Q.Mx k r → E) → Q.Mx k r → E) (h : Q.Mx k r → E) => T h) f) (x0 k r j hj Z τ γ) =
      (L₂.foldr (fun (T : (MJ j → E) → MJ j → E) (h : MJ j → E) => T h) (fun Z' => f (x0 k r j hj Z' τ γ))) Z
  | [], [], _ => fun _ _ => rfl
  | T :: L₁, S :: L₂, List.Forall₂.cons h hL => by
    intro f Z
    simp only [List.foldr_cons]
    rw [h]
    congr 1
    funext Z'
    exact foldr_pull L₁ L₂ hL f Z'

theorem forall₂_ofFn {α β : Type*} (R : α → β → Prop) : ∀ (n : ℕ) (F : Fin n → α) (G : Fin n → β),
    (∀ i, R (F i) (G i)) → List.Forall₂ R (List.ofFn F) (List.ofFn G)
  | 0, _, _, _ => by simp
  | n + 1, F, G, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (forall₂_ofFn R n _ _ (fun i => h i.succ))

theorem qmin_pull (hC : CurveLevi) (hH : HpartLevi) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (hab : ∀ (σ : Equiv.Perm (Fin t)) (i : Fin t), Good k r j (a (σ i)) (b i)) (f : Q.Mx k r → E) (Z : MJ j) :
    qminorOp (EabH (Hpk k r)) a b u f (x0 k r j hj Z τ γ) =
      qminG (EopZ k r j) a b u (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  unfold qminorOp qminG
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  congr 1
  refine foldr_pull hj τ γ _ _ ?_ f Z
  exact forall₂_ofFn (Rel (E := E) hj τ γ) t _ _ (fun i f' Z' => top_pull hj τ γ hC hH _ _ _ (hab σ i) f' Z')

theorem AAop_pull (hC : CurveLevi) (hH : HpartLevi) (hXC : XiCoef) (m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (u : ℂ)
    (f : Q.Mx k r → E) (Z : MJ j) :
    C3.AAop k r m hm u f (x0 k r j hj Z τ γ) = AZ k r j m hm hmj u (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  classical
  unfold C3.AAop AZ
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hc
  · have hcoef : (Matrix.of fun a l : Fin m =>
        herm (Hpk k r) (x0 k r j hj Z τ γ *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))) =
        Matrix.of fun a l => cZ Z (c l) (Fin.castLE hmj a) := by
      ext a l
      exact hXC k r j hj Z τ γ (Fin.castLE hmj a) (c l)
    rw [hcoef]
    by_cases hall : ∀ l, (c l).val < j
    · rw [qmin_pull hj τ γ hC hH]
      intro σ i
      left
      exact ⟨by simp [C3.xR, eI]; omega, hall i⟩
    · push Not at hall
      obtain ⟨l, hl⟩ := hall
      rw [Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [cZ]; omega)]
      simp
  · rfl

theorem AAvop_pull (hC : CurveLevi) (hH : HpartLevi) (hXV : XiCoefV) (m : ℕ) (hm : m ≤ r) (hmj : m ≤ j)
    (ell : ℂ) (f : Q.Mx k r → E) (Z : MJ j) (hZ : Z.det ≠ 0) (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) :
    C3.AAvop k r m hm ell f (x0 k r j hj Z τ γ) = AvZ k r j m hm hmj ell (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  classical
  unfold C3.AAvop AvZ
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hc
  · have hcoef : (Matrix.of fun a l : Fin m =>
        ((x0 k r j hj Z τ γ)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (c l)) =
        Matrix.of fun a l => cvZ k r Z (c l) (Fin.castLE hmj a) := by
      ext a l
      exact hXV k r j hj Z τ γ hZ hτ hγ (Fin.castLE hmj a) (c l)
    rw [hcoef]
    by_cases hall : ∀ l, 2 * r + k < (c l).val + j
    · rw [qmin_pull hj τ γ hC hH]
      intro σ i
      right
      have := i.isLt
      exact ⟨hall (σ i), by simp [C3.sR, esI]; omega⟩
    · push Not at hall
      obtain ⟨l, hl⟩ := hall
      rw [Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [cvZ]; omega)]
      simp
  · rfl

theorem Dmin_pull (hXC : XiCoef) (z z' : Fin (2 * r + k + 1) → ℂ) (Z : MJ j) :
    Dmin k r z z' (x0 k r j hj Z τ γ) ⟨j, by omega⟩ = Z.det := by
  show ((Zhat k r z z' (x0 k r j hj Z τ γ)).submatrix (Fin.castLE (by omega : j ≤ r + 1))
    (Fin.castLE (by omega : j ≤ r + 1))).det = Z.det
  congr 1
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [Matrix.submatrix_apply, Zhat, fvec]
  rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
  have := hXC k r j hj Z τ γ a (eI k r ⟨b.val, by omega⟩)
  simp only [eI] at this ⊢
  simpa [hb] using this

theorem vLet_pull (hC : CurveLevi) (hH : HpartLevi) (hXC : XiCoef) (hXV : XiCoefV)
    (z z' : Fin (2 * r + k + 1) → ℂ) (l : C.Letter) (e : Fin 2) (Φ : Q.Mx k r → E) (Z : MJ j)
    (hZ : Z.det ≠ 0) (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) :
    D.vLet k r z z' j (by omega) l e Φ (x0 k r j hj Z τ γ) =
      Aform k r j hj l e (fun Z' => Φ (x0 k r j hj Z' τ γ)) Z := by
  unfold D.vLet Aform
  split_ifs
  · rfl
  · rw [Dmin_pull hj τ γ hXC, AAop_pull hj τ γ hC hH hXC]
  · rw [Dmin_pull hj τ γ hXC, AAvop_pull hj τ γ hC hH hXV _ _ _ _ _ Z hZ hτ hγ]

end transfer

section lin

variable {j : ℕ}

def W (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Z : MJ j) : Submodule ℂ (MJ j → E) where
  carrier := {h | ∃ V : Set (MJ j), IsOpen V ∧ Z ∈ V ∧ ContDiffOn ℝ ∞ h V}
  add_mem' := by
    rintro h₁ h₂ ⟨V₁, o₁, m₁, s₁⟩ ⟨V₂, o₂, m₂, s₂⟩
    exact ⟨V₁ ∩ V₂, o₁.inter o₂, ⟨m₁, m₂⟩, (s₁.mono Set.inter_subset_left).add (s₂.mono Set.inter_subset_right)⟩
  zero_mem' := ⟨Set.univ, isOpen_univ, trivial, contDiffOn_const⟩
  smul_mem' := by
    rintro c h ⟨V, o, m, s⟩
    exact ⟨V, o, m, s.const_smul c⟩

def fW {T : (MJ j → E) → MJ j → E} (hT : ZOp T) (Z : MJ j) (hZ : Z.det ≠ 0) : W E Z →ₗ[ℂ] E where
  toFun h := T h.1 Z
  map_add' := by
    rintro ⟨h₁, V₁, o₁, m₁, s₁⟩ ⟨h₂, V₂, o₂, m₂, s₂⟩
    exact hT.add (V₁ ∩ V₂ ∩ {Z | Z.det ≠ 0}) h₁ h₂ ((o₁.inter o₂).inter isOpen_inv)
      (fun _ h => h.2) (s₁.mono (fun _ h => h.1.1)) (s₂.mono (fun _ h => h.1.2)) Z ⟨⟨m₁, m₂⟩, hZ⟩
  map_smul' := by
    rintro c ⟨h, V, o, m, s⟩
    exact hT.smul (V ∩ {Z | Z.det ≠ 0}) c h (o.inter isOpen_inv) (fun _ h => h.2) (s.mono (fun _ h => h.1)) Z ⟨m, hZ⟩

def linOf {T : (MJ j → E) → MJ j → E} (hT : ZOp T) : (MJ j → E) →ₗ[ℂ] (MJ j → E) :=
  LinearMap.pi fun Z => if hZ : Z.det ≠ 0 then Classical.choose (LinearMap.exists_extend (fW hT Z hZ)) else 0

theorem linOf_eq {T : (MJ j → E) → MJ j → E} (hT : ZOp T) {Z : MJ j} (hZ : Z.det ≠ 0) {h : MJ j → E}
    (hh : h ∈ W E Z) : linOf hT h Z = T h Z := by
  simp only [linOf, LinearMap.pi_apply, dif_pos hZ]
  have := Classical.choose_spec (LinearMap.exists_extend (fW hT Z hZ))
  exact congrArg (fun L : W E Z →ₗ[ℂ] E => L ⟨h, hh⟩) this

theorem dz_congr {F G : ℂ → E} {τ : ℂ} (h : F =ᶠ[𝓝 τ] G) : PBP.dz F τ = PBP.dz G τ := by
  unfold PBP.dz; rw [h.fderiv_eq]

theorem dzb_congr {F G : ℂ → E} {τ : ℂ} (h : F =ᶠ[𝓝 τ] G) : PBP.dzb F τ = PBP.dzb G τ := by
  unfold PBP.dzb; rw [h.fderiv_eq]

theorem linOf_par (hD : DzSlice) {T : (MJ j → E) → MJ j → E} (hT : ZOp T) : ParamComm (linOf hT) := by
  intro U κ hU hUi hκ
  obtain ⟨t1, t2⟩ := hT.par U κ hU hUi hκ
  have hsl : ∀ τ : ℂ, IsOpen {Z : MJ j | ((τ, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) ∈ U} :=
    fun τ => hU.preimage (contDiff_pair τ).continuous
  have key : ∀ (τ : ℂ) (Z : MJ j), ((τ, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) ∈ U →
      linOf hT (κ τ) Z = T (κ τ) Z := by
    intro τ Z hτZ
    exact linOf_eq hT (hUi hτZ) ⟨_, hsl τ, hτZ, hκ.comp (contDiff_pair τ).contDiffOn (fun _ h => h)⟩
  refine ⟨t1.congr (fun q hq => key q.1 (Matrix.of q.2) hq), fun q hq => ?_⟩
  have hev : (fun τ => linOf hT (κ τ) (Matrix.of q.2)) =ᶠ[𝓝 q.1] (fun τ => T (κ τ) (Matrix.of q.2)) := by
    have hop : IsOpen {τ : ℂ | ((τ, q.2) : ℂ × (Fin j → Fin j → ℂ)) ∈ U} :=
      hU.preimage (continuous_id.prodMk continuous_const)
    filter_upwards [hop.mem_nhds (show (q.1, q.2) ∈ U from hq)] with τ hτ
    exact key τ _ hτ
  obtain ⟨d1, d2⟩ := hD j E U κ hU hκ q.1
  refine ⟨?_, ?_⟩
  · rw [dz_congr hev, (t2 q hq).1]
    exact (linOf_eq hT (hUi hq) ⟨_, hsl q.1, hq, d1⟩).symm
  · rw [dzb_congr hev, (t2 q hq).2]
    exact (linOf_eq hT (hUi hq) ⟨_, hsl q.1, hq, d2⟩).symm

end lin

theorem zOnly_of_parts (hC : CurveLevi) (hH : HpartLevi) (hXC : XiCoef) (hXV : XiCoefV) (hXM : XiMem)
    (hXS : XiSmooth) (hR : ZOpRd) (hD : DzSlice) : ZOnly := by
  intro k r j hj z z' E _ _ l e _ _
  refine ⟨linOf (zop_Aform (E := E) hR k r j hj l e), linOf_par hD _, ?_⟩
  intro Dm Φ _ _ hsm Z τ γ hZ hτ hγ hmem
  rw [vLet_pull hj τ γ hC hH hXC hXV z z' l e Φ Z hZ hτ hγ]
  refine (linOf_eq _ hZ ?_).symm
  obtain ⟨UF, F, hUF, hgUF, hF, hΦF⟩ := hsm _ ⟨hXM k r j hj Z τ γ hZ hτ hγ, hmem⟩
  have hcont := (hXS k r j hj τ γ).continuousOn
  refine ⟨{Z' | Z'.det ≠ 0} ∩ (fun Z' => x0 k r j hj Z' τ γ) ⁻¹' UF,
    hcont.isOpen_inter_preimage isOpen_inv hUF, ⟨hZ, hgUF⟩, ?_⟩
  refine (hF.comp ((hXS k r j hj τ γ).mono Set.inter_subset_left) (fun _ h => h.2)).congr ?_
  intro Z' hZ'
  exact hΦF _ hZ'.2 (hXM k r j hj Z' τ γ hZ'.1 hτ hγ)

end Formalism.FourierDecayAlt.P.WirtingerOperators
