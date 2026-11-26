module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RaisingCompactSupport

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothGConst
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ParFamIntegrable
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

section Fam

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Par : Type} [NormedAddCommGroup Par]
  [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}

theorem parFam_add {f g : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) (hg : PBI.ParFam k ρ U₀ g) :
    PBI.ParFam k ρ U₀ (fun q => f q + g q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  obtain ⟨U', F', hU', hqU', hF', hgF⟩ := hg q₀ hq hG
  exact ⟨U ∩ U', fun q => F q + F' q, hU.inter hU', ⟨hqU, hqU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right),
    fun q hq hG => by show f q + g q = F q + F' q; rw [hfF q hq.1 hG, hgF q hq.2 hG]⟩

theorem parFam_smul (a : ℂ) {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) :
    PBI.ParFam k ρ U₀ (fun q => a • f q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  exact ⟨U, fun q => a • F q, hU, hqU, hF.const_smul a, fun q hq hG => by show a • f q = a • F q; rw [hfF q hq hG]⟩

theorem parFam_zero : PBI.ParFam k ρ U₀ (fun _ => (0 : E)) := fun q₀ _ _ =>
  ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem parFam_sum {ι : Type} (s : Finset ι) {f : ι → Par × Mt k ρ → E}
    (hf : ∀ i ∈ s, PBI.ParFam k ρ U₀ (f i)) : PBI.ParFam k ρ U₀ (fun q => ∑ i ∈ s, f i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (parFam_zero (E := E) (U₀ := U₀))
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have := parFam_add h1 h2
    simpa [Finset.sum_insert ha] using this

theorem parFam_contAt {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) {Z : Par} {y : Mt k ρ} (hq : (Z, y) ∈ U₀)
    (hy : Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ)) : ContinuousAt (fun Z' => f (Z', y)) Z := by
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf (Z, y) hq hy
  have hci : Continuous fun Z' : Par => ((Z', y) : Par × Mt k ρ) := continuous_id.prodMk continuous_const
  have hm : {Z' | (Z', y) ∈ U} ∈ 𝓝 Z := hci.continuousAt.preimage_mem_nhds (hU.mem_nhds hqU)
  have hcF : ContinuousAt (fun Z' => F (Z', y)) Z :=
    ContinuousAt.comp (g := F) (f := fun Z' : Par => ((Z', y) : Par × Mt k ρ)) (x := Z)
      (hF.continuousOn.continuousAt (hU.mem_nhds hqU)) hci.continuousAt
  refine hcF.congr ?_
  filter_upwards [hm] with Z' hZ'
  exact (hfF (Z', y) hZ' hy).symm

theorem parFam_integrable [MeasurableSpace Par] [BorelSpace Par] {f : Par × Mt k ρ → E}
    (hf : PBI.ParFam k ρ U₀ f) {ν : Measure Par} [IsFiniteMeasure ν] {Kp : Set Par} (hK : IsCompact Kp)
    (hν : ν Kpᶜ = 0) {y : Mt k ρ} (hy : Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ)) (hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀) :
    Integrable (fun Z => f (Z, y)) ν := by
  have hc : ContinuousOn (fun Z => f (Z, y)) Kp := fun Z hZ =>
    (parFam_contAt hf (hKU Z hZ) hy).continuousWithinAt
  have hI : IntegrableOn (fun Z => f (Z, y)) Kp ν := hc.integrableOn_compact hK
  have hae : ∀ᵐ Z ∂ν, Z ∈ Kp := by
    rw [ae_iff]
    simpa [Set.compl_def] using hν
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at hI

end Fam

section Cls

variable {k ρ : ℕ} {z z' : Fin (2 * ρ + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Q.Mx k ρ → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)}

def Rep {Par : Type} (Ψ : Par → Q.RadSp k ρ z z' π π') (Ψf : Par → Mt k ρ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Z c y, Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → (Ψ Z : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = Ψf Z y

def GGpos (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) : Set (Mt k ρ) := {y | 0 < Q.GGl k ρ z z' (Matrix.of y)}


variable (z z' π π') in
def Good (A : Module.End ℂ (Q.RadSp k ρ z z' π π')) : Prop :=
  ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
    [BorelSpace Par] (U₀ : Set (Par × Mt k ρ)), IsOpen U₀ → U₀ ⊆ Set.univ ×ˢ GGpos k ρ z z' →
  ∀ (Ψ : Par → Q.RadSp k ρ z z' π π') (Ψf : Par → Mt k ρ → (Wq →L[ℂ] Wp)), Rep Ψ Ψf →
    PBI.ParFam k ρ U₀ (fun q => Ψf q.1 q.2) →
  ∃ Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp), Rep (fun Z => A (Ψ Z)) Φf ∧ PBI.ParFam k ρ U₀ (fun q => Φf q.1 q.2) ∧
    (∀ K : Set (Par × Mt k ρ), (∀ q, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → q ∉ K → Ψf q.1 q.2 = 0) →
      ∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → q ∉ closure K → Φf q.1 q.2 = 0) ∧
    ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
    ∀ (Ψi : Q.RadSp k ρ z z' π π') (y : Mt k ρ) (V : Set (Mt k ρ)), IsOpen V → y ∈ V →
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → Kp ×ˢ V ⊆ U₀ →
      (∀ c y', y' ∈ V → Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) →
        (Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y') = ∫ Z, Ψf Z y' ∂ν) →
      ∀ c, (A Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = ∫ Z, Φf Z y ∂ν

theorem good_id : Good z z' π π' (LinearMap.id : Module.End ℂ (Q.RadSp k ρ z z' π π')) := by
  intro Par _ _ _ _ _ U₀ _ _ Ψ Ψf hR hF
  refine ⟨Ψf, fun Z c y hy => hR Z c y hy, hF, fun K hK q _ hG hq => hK q hG (fun h => hq (subset_closure h)),
    fun ν _ Kp _ _ Ψi y V _ hyV hyG _ hi c => hi c y hyV hyG⟩

theorem good_comp {A B : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) (hB : Good z z' π π' B) :
    Good z z' π π' (A * B) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hB Par U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₂, hR₂, hF₂, hS₂, hW₂⟩ := hA Par U₀ hU₀ hUpos (fun Z => B (Ψ Z)) Φ₁ hR₁ hF₁
  refine ⟨Φ₂, fun Z c y hy => hR₂ Z c y hy, hF₂, fun K hK q hq hG hqK => ?_, ?_⟩
  · have hK' : ∀ q', Matrix.of q'.2 ∈ Q.Glev k ρ (Fin.last ρ) → q' ∉ closure K ∪ U₀ᶜ → Φ₁ q'.1 q'.2 = 0 := by
      intro q' hG' hq'
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hq'
      exact hS₁ K hK q' hq'.2 hG' hq'.1
    refine hS₂ _ hK' q hq hG ?_
    rw [closure_union, hU₀.isClosed_compl.closure_eq, closure_closure]
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not]
    exact ⟨hqK, hq⟩
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    have hi' : ∀ c y', y' ∈ V → Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) →
        (B Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y') = ∫ Z, Φ₁ Z y' ∂ν :=
      fun c y' hy' hG' => hW₁ ν Kp hKp hν Ψi y' V hV hy' hG' hKV hi c
    exact hW₂ ν Kp hKp hν (B Ψi) y V hV hyV hyG hKV hi' c

theorem good_add {A B : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) (hB : Good z z' π π' B) :
    Good z z' π π' (A + B) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hA Par U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₂, hR₂, hF₂, hS₂, hW₂⟩ := hB Par U₀ hU₀ hUpos Ψ Ψf hR hF
  refine ⟨fun Z y => Φ₁ Z y + Φ₂ Z y, fun Z c y hy => ?_, parFam_add hF₁ hF₂, fun K hK q hq hG hqK => ?_, ?_⟩
  · simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [hR₁ Z c y hy, hR₂ Z c y hy]
  · simp only [hS₁ K hK q hq hG hqK, hS₂ K hK q hq hG hqK, add_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    have hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀ := fun Z hZ => hKV ⟨hZ, hyV⟩
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [hW₁ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c, hW₂ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c,
      ← integral_add (parFam_integrable hF₁ hKp hν hyG hKU) (parFam_integrable hF₂ hKp hν hyG hKU)]

theorem good_smul (a : ℂ) {A : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) :
    Good z z' π π' (a • A) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hA Par U₀ hU₀ hUpos Ψ Ψf hR hF
  refine ⟨fun Z y => a • Φ₁ Z y, fun Z c y hy => ?_, parFam_smul a hF₁, fun K hK q hq hG hqK => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hR₁ Z c y hy]
  · simp only [hS₁ K hK q hq hG hqK, smul_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hW₁ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c, integral_smul]


variable (z z' π π') in
def PGood (x : Q.Pr (Q.RadSp k ρ z z' π π')) : Prop := Good z z' π π' x.1 ∧ Good z z' π π' x.2.unop


variable (z z' π π') in
def goodAlg : StarSubalgebra ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) where
  carrier := {x | PGood z z' π π' x}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨good_comp hx1 hy1, good_comp hy2 hx2⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨good_add hx1 hy1, good_add hx2 hy2⟩
  algebraMap_mem' := by
    intro a
    have e1 : (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).1 = a • LinearMap.id := by
      show algebraMap ℂ (Module.End ℂ (Q.RadSp k ρ z z' π π')) a = _
      exact Module.algebraMap_end_eq_smul_id _ _ _ a
    have e2 : (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).2.unop = (starRingEnd ℂ a) • LinearMap.id := by
      show algebraMap ℂ (Module.End ℂ (Q.RadSp k ρ z z' π π')) (starRingEnd ℂ a) = _
      exact Module.algebraMap_end_eq_smul_id _ _ _ _
    refine ⟨?_, ?_⟩
    · show Good z z' π π' (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).1
      rw [e1]; exact good_smul a good_id
    · show Good z z' π π' (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).2.unop
      rw [e2]; exact good_smul _ good_id
  star_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx2, hx1⟩

theorem good_mkP {X Xs : Module.End ℂ (Q.RadSp k ρ z z' π π')} (h1 : Good z z' π π' X) (h2 : Good z z' π π' Xs) :
    Q.mkP X Xs ∈ goodAlg z z' π π' := ⟨h1, h2⟩

end Cls

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

section Ops

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]


variable (k ρ) in
def ParOK (T : (Q.Mx k ρ → E) → Q.Mx k ρ → E) : Prop :=
  ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
    [BorelSpace Par] (U₀ : Set (Par × Mt k ρ)), IsOpen U₀ →
  ∀ f : Par → Q.Mx k ρ → E, PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2)) →
    PBI.ParFam k ρ U₀ (fun q => T (f q.1) (Matrix.of q.2)) ∧
    (∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → ∀ W : Set (Par × Mt k ρ), IsOpen W → q ∈ W →
      (∀ q' ∈ W, Matrix.of q'.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q'.1 (Matrix.of q'.2) = 0) →
      T (f q.1) (Matrix.of q.2) = 0) ∧
    ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
    ∀ (fi : Q.Mx k ρ → E) (y : Mt k ρ) (V : Set (Mt k ρ)), IsOpen V → y ∈ V →
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → Kp ×ˢ V ⊆ U₀ →
      (∀ y' ∈ V, Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) → fi (Matrix.of y') = ∫ Z, f Z (Matrix.of y') ∂ν) →
      T fi (Matrix.of y) = ∫ Z, T (f Z) (Matrix.of y) ∂ν


variable (k ρ) in
def SmoothG (a : Q.Mx k ρ → ℂ) : Prop :=
  ∀ y₀ : Mt k ρ, Matrix.of y₀ ∈ Q.Glev k ρ (Fin.last ρ) → ∃ (U : Set (Mt k ρ)) (F : Mt k ρ → ℂ),
    IsOpen U ∧ y₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ y ∈ U, Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → a (Matrix.of y) = F y

theorem smoothG_const (s : ℂ) : SmoothG k ρ (fun _ => s) := fun _ _ =>
  ⟨Set.univ, fun _ => s, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem smoothG_mul {a b : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) (hb : SmoothG k ρ b) :
    SmoothG k ρ (fun g => a g * b g) := by
  intro y₀ hy
  obtain ⟨U, F, hU, hyU, hF, haF⟩ := ha y₀ hy
  obtain ⟨U', F', hU', hyU', hF', hbF⟩ := hb y₀ hy
  exact ⟨U ∩ U', fun y => F y * F' y, hU.inter hU', ⟨hyU, hyU'⟩,
    (hF.mono Set.inter_subset_left).mul (hF'.mono Set.inter_subset_right),
    fun y hy hG => by show a (Matrix.of y) * b (Matrix.of y) = F y * F' y; rw [haF y hy.1 hG, hbF y hy.2 hG]⟩

theorem smoothG_sub {a b : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) (hb : SmoothG k ρ b) :
    SmoothG k ρ (fun g => a g - b g) := by
  intro y₀ hy
  obtain ⟨U, F, hU, hyU, hF, haF⟩ := ha y₀ hy
  obtain ⟨U', F', hU', hyU', hF', hbF⟩ := hb y₀ hy
  exact ⟨U ∩ U', fun y => F y - F' y, hU.inter hU', ⟨hyU, hyU'⟩,
    (hF.mono Set.inter_subset_left).sub (hF'.mono Set.inter_subset_right),
    fun y hy hG => by show a (Matrix.of y) - b (Matrix.of y) = F y - F' y; rw [haF y hy.1 hG, hbF y hy.2 hG]⟩

theorem parFam_congr {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}
    {f g : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f)
    (h : ∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q = g q) (hU₀ : IsOpen U₀) :
    PBI.ParFam k ρ U₀ g := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  exact ⟨U ∩ U₀, F, hU.inter hU₀, ⟨hqU, hq⟩, hF.mono Set.inter_subset_left,
    fun q hq' hG' => (h q hq'.2 hG').symm.trans (hfF q hq'.1 hG')⟩

theorem parFam_smulG {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}
    {a : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) :
    PBI.ParFam k ρ U₀ (fun q => a (Matrix.of q.2) • f q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  obtain ⟨U', A, hU', hqU', hA, haA⟩ := ha q₀.2 hG
  refine ⟨U ∩ Prod.snd ⁻¹' U', fun q => A q.2 • F q, hU.inter (hU'.preimage continuous_snd), ⟨hqU, hqU'⟩, ?_,
    fun q hq' hG' => ?_⟩
  · exact (hA.comp contDiff_snd.contDiffOn (fun q (hq : q ∈ U ∩ Prod.snd ⁻¹' U') => hq.2)).smul (hF.mono Set.inter_subset_left)
  · show a (Matrix.of q.2) • f q = A q.2 • F q
    rw [haA q.2 hq'.2 hG', hfF q hq'.1 hG']

theorem parOK_id : ParOK k ρ (E := E) (fun f => f) := by
  intro Par _ _ _ _ _ U₀ _ f hf
  refine ⟨hf, fun q _ hG W _ hqW hW => hW q hqW hG, fun ν _ Kp _ _ fi y V _ hyV hyG _ hi => hi y hyV hyG⟩

theorem parOK_zero : ParOK k ρ (E := E) (fun _ _ => 0) := by
  intro Par _ _ _ _ _ U₀ _ f hf
  refine ⟨parFam_zero, fun _ _ _ _ _ _ _ => rfl, fun ν _ Kp _ _ fi y V _ _ _ _ _ => by simp⟩

theorem parOK_congr {T T' : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) (h : ∀ f g, T f g = T' f g) :
    ParOK k ρ T' := by
  have e : T = T' := funext fun f => funext fun g => h f g
  rw [← e]; exact hT

theorem parOK_add {T₁ T₂ : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (h₁ : ParOK k ρ T₁) (h₂ : ParOK k ρ T₂) :
    ParOK k ρ (fun f g => T₁ f g + T₂ f g) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := h₁ Par U₀ hU₀ f hf
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Par U₀ hU₀ f hf
  refine ⟨parFam_add a₁ a₂, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show T₁ (f q.1) (Matrix.of q.2) + T₂ (f q.1) (Matrix.of q.2) = 0
    rw [b₁ q hq hG W hW hqW hz, b₂ q hq hG W hW hqW hz, add_zero]
  · have hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀ := fun Z hZ => hKV ⟨hZ, hyV⟩
    show T₁ fi (Matrix.of y) + T₂ fi (Matrix.of y) = ∫ Z, (T₁ (f Z) (Matrix.of y) + T₂ (f Z) (Matrix.of y)) ∂ν
    rw [c₁ ν Kp hKp hν fi y V hV hyV hyG hKV hi, c₂ ν Kp hKp hν fi y V hV hyV hyG hKV hi,
      integral_add (parFam_integrable a₁ hKp hν hyG hKU) (parFam_integrable a₂ hKp hν hyG hKU)]

theorem parOK_smulG {a : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E}
    (hT : ParOK k ρ T) : ParOK k ρ (fun f g => a g • T f g) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := hT Par U₀ hU₀ f hf
  refine ⟨parFam_smulG ha a₁, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show a (Matrix.of q.2) • T (f q.1) (Matrix.of q.2) = 0
    rw [b₁ q hq hG W hW hqW hz, smul_zero]
  · show a (Matrix.of y) • T fi (Matrix.of y) = ∫ Z, a (Matrix.of y) • T (f Z) (Matrix.of y) ∂ν
    rw [c₁ ν Kp hKp hν fi y V hV hyV hyG hKV hi, integral_smul]

theorem parOK_csmul (s : ℂ) {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) :
    ParOK k ρ (fun f g => s • T f g) := parOK_smulG (smoothG_const s) hT

theorem parOK_neg {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) : ParOK k ρ (fun f g => -T f g) :=
  parOK_congr (parOK_csmul (-1) hT) (fun f g => by simp)

theorem parOK_comp {T₁ T₂ : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (h₁ : ParOK k ρ T₁) (h₂ : ParOK k ρ T₂) :
    ParOK k ρ (fun f => T₁ (T₂ f)) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Par U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := h₁ Par U₀ hU₀ (fun Z => T₂ (f Z)) a₂
  refine ⟨a₁, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · refine b₁ q hq hG (W ∩ U₀) (hW.inter hU₀) ⟨hqW, hq⟩ (fun q' hq' hG' => ?_)
    exact b₂ q' hq'.2 hG' W hW hq'.1 hz
  · refine c₁ ν Kp hKp hν (T₂ fi) y V hV hyV hyG hKV (fun y' hy' hG' => ?_)
    exact c₂ ν Kp hKp hν fi y' V hV hy' hG' hKV hi

theorem parOK_sum {ι : Type} (s : Finset ι) {T : ι → (Q.Mx k ρ → E) → Q.Mx k ρ → E}
    (h : ∀ i ∈ s, ParOK k ρ (T i)) : ParOK k ρ (fun f g => ∑ i ∈ s, T i f g) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact parOK_congr parOK_zero (fun f g => by simp)
  | insert a s ha ih =>
    have := parOK_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact parOK_congr this (fun f g => by simp [Finset.sum_insert ha])

theorem parOK_foldr (L : List ((Q.Mx k ρ → E) → Q.Mx k ρ → E)) (hL : ∀ T ∈ L, ParOK k ρ T) :
    ParOK k ρ (fun f => L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact parOK_id
  | cons T L ih =>
    exact parOK_comp (hL T List.mem_cons_self) (ih fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))

end Ops

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GoodAlt
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothGOfSf
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtRightDerivativeCurve
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section RdV

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def cur (X : Q.Mx k ρ) (y : Mt k ρ) (t : ℝ) : Mt k ρ :=
  Matrix.of.symm (Matrix.of y * NormedSpace.exp ((t : ℂ) • X))

theorem cur_zero (X : Q.Mx k ρ) (y : Mt k ρ) : cur X y 0 = y := by
  simp [cur, NormedSpace.exp_zero]

theorem cur_add (X : Q.Mx k ρ) (y : Mt k ρ) (s t : ℝ) : cur X (cur X y s) t = cur X y (s + t) := by
  have hc : Commute ((s : ℂ) • X) ((t : ℂ) • X) := ((Commute.refl X).smul_left _).smul_right _
  have e : NormedSpace.exp (((s + t : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X) := by
    rw [← Matrix.exp_add_of_commute _ _ hc, Complex.ofReal_add, add_smul]
  unfold cur
  rw [Equiv.apply_symm_apply, e, Matrix.mul_assoc]

theorem cur_hasDerivAt0 (X : Q.Mx k ρ) (y : Mt k ρ) :
    HasDerivAt (cur X y) (Matrix.of.symm (Matrix.of y * X)) 0 :=
  Formalism.REAL.hasDerivAt_mul_exp_smul_zero (Matrix.of y) X

theorem cur_hasDerivAt (X : Q.Mx k ρ) (y : Mt k ρ) (s : ℝ) :
    HasDerivAt (cur X y) (Matrix.of.symm (Matrix.of (cur X y s) * X)) s := by
  have h0 := cur_hasDerivAt0 X (cur X y s)
  rw [← sub_self s] at h0
  have h1 := h0.comp_sub_const s s
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show cur X y t = cur X (cur X y s) (t - s)
  rw [cur_add, add_sub_cancel]

def mulX (X : Q.Mx k ρ) : Mt k ρ →ₗ[ℝ] Mt k ρ where
  toFun y := Matrix.of.symm (Matrix.of y * X)
  map_add' a b := by
    show Matrix.of.symm ((Matrix.of a + Matrix.of b) * X) = _
    rw [Matrix.add_mul]; rfl
  map_smul' c a := by
    show Matrix.of.symm ((c • Matrix.of a) * X) = _
    rw [Matrix.smul_mul]; rfl

variable {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par]

def dirL (X : Q.Mx k ρ) : Par × Mt k ρ →L[ℝ] Par × Mt k ρ :=
  (ContinuousLinearMap.inr ℝ Par (Mt k ρ)).comp
    ((LinearMap.toContinuousLinearMap (mulX X)).comp (ContinuousLinearMap.snd ℝ Par (Mt k ρ)))

theorem rdv_local {X : Q.Mx k ρ} (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) {f : Par → Q.Mx k ρ → E}
    {U : Set (Par × Mt k ρ)} {F : Par × Mt k ρ → E} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ q ∈ U, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q.1 (Matrix.of q.2) = F q)
    {q : Par × Mt k ρ} (hq : q ∈ U) (hqG : Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ)) :
    HasDerivAt (fun t : ℝ => f q.1 (Matrix.of (cur X q.2 t))) (fderiv ℝ F q (dirL X q)) 0 := by
  have hc := cur_hasDerivAt0 X q.2
  have hγ : HasDerivAt (fun t : ℝ => ((q.1, cur X q.2 t) : Par × Mt k ρ)) (dirL X q) 0 :=
    (hasDerivAt_const (0 : ℝ) q.1).prodMk hc
  have hγ0 : ((q.1, cur X q.2 0) : Par × Mt k ρ) = q := by rw [cur_zero]
  have hFd : DifferentiableAt ℝ F q := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq)
  have hcomp := hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((q.1, cur X q.2 t) : Par × Mt k ρ) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hq)
  filter_upwards [hmem] with t ht
  exact hfF _ ht (Formalism.FourierDecayAlt.P.Qx3.glev_mul hqG (hX t))

theorem parFam_contAt_comp {Y : Type} [TopologicalSpace Y] {U₀ : Set (Par × Mt k ρ)} {g : Par × Mt k ρ → E}
    (hg : PBI.ParFam k ρ U₀ g) {m : Y → Par × Mt k ρ} {y₀ : Y} (hm : ContinuousAt m y₀) (hU : m y₀ ∈ U₀)
    (hG : ∀ y, Matrix.of (m y).2 ∈ Q.Glev k ρ (Fin.last ρ)) : ContinuousAt (fun y => g (m y)) y₀ := by
  obtain ⟨U, F, hUo, hqU, hF, hgF⟩ := hg (m y₀) hU (hG y₀)
  have hcF : ContinuousAt F (m y₀) := hF.continuousOn.continuousAt (hUo.mem_nhds hqU)
  have h := ContinuousAt.comp (g := F) (f := m) (x := y₀) hcF hm
  refine h.congr ?_
  have hmem : ∀ᶠ y in 𝓝 y₀, m y ∈ U := hm.preimage_mem_nhds (hUo.mem_nhds hqU)
  filter_upwards [hmem] with y hy
  exact (hgF (m y) hy (hG y)).symm

theorem rdv_parFam {X : Q.Mx k ρ} (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) {U₀ : Set (Par × Mt k ρ)}
    {f : Par → Q.Mx k ρ → E} (hf : PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2))) :
    PBI.ParFam k ρ U₀ (fun q => RdV X (f q.1) (Matrix.of q.2)) := by
  intro q₀ hq₀ hG₀
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq₀ hG₀
  refine ⟨U, fun q => fderiv ℝ F q (dirL X q), hU, hqU, ?_, fun q hq hqG => ?_⟩
  · exact (hF.fderiv_of_isOpen (m := ∞) hU Formalism.REAL.withTop_enat_infty_add_one_le_infty).clm_apply
      (ContinuousLinearMap.contDiff (n := ∞) (dirL (Par := Par) (k := k) (ρ := ρ) X)).contDiffOn
  · exact (rdv_local hX hU hF hfF hq hqG).deriv

theorem hasDerivAt_right_derivative_curve {X : Q.Mx k ρ} (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) {U₀ : Set (Par × Mt k ρ)}
    {f : Par → Q.Mx k ρ → E} (hf : PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2))) (Z : Par) (y : Mt k ρ)
    (s : ℝ) (hq : (Z, cur X y s) ∈ U₀) (hG : Matrix.of (cur X y s) ∈ Q.Glev k ρ (Fin.last ρ)) :
    HasDerivAt (fun t : ℝ => f Z (Matrix.of (cur X y t))) (RdV X (f Z) (Matrix.of (cur X y s))) s := by
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf _ hq hG
  have h0 := rdv_local hX hU hF hfF hqU hG
  have h1 : HasDerivAt (fun t : ℝ => f Z (Matrix.of (cur X (cur X y s) t)))
      (RdV X (f Z) (Matrix.of (cur X y s))) 0 := h0.differentiableAt.hasDerivAt
  rw [← sub_self s] at h1
  have h2 := h1.comp_sub_const s s
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show f Z (Matrix.of (cur X y t)) = f Z (Matrix.of (cur X (cur X y s) (t - s)))
  rw [cur_add, add_sub_cancel]

end RdV

theorem parOK_rdV {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {X : Q.Mx k ρ}
    (hX : Formalism.FourierDecayAlt.P.Qx3.LieLev (Fin.last ρ) X) : ParOK k ρ (E := E) (RdV X) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  have hD := rdv_parFam hX hf
  refine ⟨hD, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show deriv (fun t : ℝ => f q.1 (Matrix.of (cur X q.2 t))) 0 = 0
    have hγ : ContinuousAt (fun t : ℝ => ((q.1, cur X q.2 t) : Par × Mt k ρ)) 0 :=
      continuousAt_const.prodMk (cur_hasDerivAt0 X q.2).continuousAt
    have hγ0 : ((q.1, cur X q.2 0) : Par × Mt k ρ) = q := by rw [cur_zero]
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((q.1, cur X q.2 t) : Par × Mt k ρ) ∈ W :=
      hγ.preimage_mem_nhds (by rw [hγ0]; exact hW.mem_nhds hqW)
    have hev : (fun t : ℝ => f q.1 (Matrix.of (cur X q.2 t))) =ᶠ[𝓝 0] (fun _ => (0 : E)) := by
      filter_upwards [hmem] with t ht
      exact hz _ ht (Formalism.FourierDecayAlt.P.Qx3.glev_mul hG (hX t))
    rw [hev.deriv_eq, deriv_const]
  · have hGt : ∀ t : ℝ, Matrix.of (cur X y t) ∈ Q.Glev k ρ (Fin.last ρ) := fun t =>
      Formalism.FourierDecayAlt.P.Qx3.glev_mul hyG (hX t)
    have hpre : cur X y ⁻¹' V ∈ 𝓝 (0 : ℝ) :=
      (cur_hasDerivAt0 X y).continuousAt.preimage_mem_nhds (by rw [cur_zero]; exact hV.mem_nhds hyV)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    have hδ : 0 < ε / 2 := half_pos hε
    have hcb : Metric.closedBall (0 : ℝ) (ε / 2) ⊆ cur X y ⁻¹' V := fun t ht =>
      hball (Metric.closedBall_subset_ball (half_lt_self hε) ht)
    have hUt : ∀ t ∈ Metric.closedBall (0 : ℝ) (ε / 2), ∀ Z ∈ Kp, (Z, cur X y t) ∈ U₀ :=
      fun t ht Z hZ => hKV ⟨hZ, hcb ht⟩
    have hcont : ContinuousOn (fun p : Par × ℝ => RdV X (f p.1) (Matrix.of (cur X y p.2)))
        (Kp ×ˢ Metric.closedBall (0 : ℝ) (ε / 2)) := by
      intro p hp
      have hm : ContinuousAt (fun p : Par × ℝ => ((p.1, cur X y p.2) : Par × Mt k ρ)) p :=
        continuous_fst.continuousAt.prodMk
          (ContinuousAt.comp (g := cur X y) (f := Prod.snd) (x := p) (cur_hasDerivAt X y p.2).continuousAt
            continuous_snd.continuousAt)
      exact (parFam_contAt_comp (g := fun q => RdV X (f q.1) (Matrix.of q.2)) hD hm (hUt p.2 hp.2 p.1 hp.1)
        (fun p => hGt p.2)).continuousWithinAt
    obtain ⟨C, hC⟩ := (hKp.prod (isCompact_closedBall (0 : ℝ) (ε / 2))).exists_bound_of_continuousOn hcont
    have hae : ∀ᵐ Z ∂ν, Z ∈ Kp := by
      rw [ae_iff]
      simpa [Set.compl_def] using hν
    have hb : Metric.ball (0 : ℝ) (ε / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hδ
    have hin : ∀ t ∈ Metric.ball (0 : ℝ) (ε / 2), t ∈ Metric.closedBall (0 : ℝ) (ε / 2) :=
      fun t ht => Metric.ball_subset_closedBall ht
    have hF_int : ∀ t ∈ Metric.closedBall (0 : ℝ) (ε / 2),
        Integrable (fun Z => f Z (Matrix.of (cur X y t))) ν := fun t ht =>
      parFam_integrable (f := fun q => f q.1 (Matrix.of q.2)) hf hKp hν (hGt t) (fun Z hZ => hUt t ht Z hZ)
    have h0c : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) (ε / 2) := Metric.mem_closedBall_self hδ.le
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
      (F := fun t Z => f Z (Matrix.of (cur X y t)))
      (F' := fun t Z => RdV X (f Z) (Matrix.of (cur X y t))) (x₀ := 0) (bound := fun _ => C) hb
      (by
        filter_upwards [hb] with t ht
        exact (hF_int t (hin t ht)).aestronglyMeasurable)
      (hF_int 0 h0c)
      ((parFam_integrable (f := fun q => RdV X (f q.1) (Matrix.of q.2)) hD hKp hν (hGt 0)
        (fun Z hZ => hUt 0 h0c Z hZ)).aestronglyMeasurable)
      (by
        filter_upwards [hae] with Z hZ
        intro t ht
        exact hC (Z, t) ⟨hZ, hin t ht⟩)
      (integrable_const C)
      (by
        filter_upwards [hae] with Z hZ
        intro t ht
        exact hasDerivAt_right_derivative_curve hX hf Z y t (hUt t (hin t ht) Z hZ) (hGt t))
    show deriv (fun t : ℝ => fi (Matrix.of (cur X y t))) 0 = ∫ Z, RdV X (f Z) (Matrix.of y) ∂ν
    have hev : (fun t : ℝ => fi (Matrix.of (cur X y t))) =ᶠ[𝓝 0]
        (fun t => ∫ Z, f Z (Matrix.of (cur X y t)) ∂ν) := by
      filter_upwards [hb] with t ht
      exact hi (cur X y t) (hcb (hin t ht)) (hGt t)
    rw [hev.deriv_eq, key.2.deriv, cur_zero]

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Ent

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smoothG_of_sf {a : Mx k ρ → ℂ}
    (h : SmoothFam k ρ (Fin.last ρ) (Set.univ : Set (Formalism.FourierDecayAlt.P.Qx3.XX k ρ)) (fun _ g => a g)) : SmoothG k ρ a := by
  intro y₀ hy₀
  obtain ⟨U, F, hU, hxU, hF, hfF⟩ := h ((0 : Fin ρ → ℂ), Matrix.of y₀) (Set.mem_univ _) hy₀
  have hm : Continuous fun y : Mt k ρ => (((0 : Fin ρ → ℂ), (Matrix.of y : Mx k ρ)) : Formalism.FourierDecayAlt.P.Qx3.XX k ρ) :=
    continuous_const.prodMk continuous_id
  have hmd : ContDiff ℝ ∞ fun y : Mt k ρ => (((0 : Fin ρ → ℂ), (Matrix.of y : Mx k ρ)) : Formalism.FourierDecayAlt.P.Qx3.XX k ρ) :=
    contDiff_const.prodMk contDiff_id
  refine ⟨(fun y : Mt k ρ => (((0 : Fin ρ → ℂ), (Matrix.of y : Mx k ρ)) : Formalism.FourierDecayAlt.P.Qx3.XX k ρ)) ⁻¹' U,
    fun y => F ((0 : Fin ρ → ℂ), Matrix.of y), hU.preimage hm, hxU, hF.comp hmd.contDiffOn (fun y hy => hy),
    fun y hy hG => hfF _ hy hG⟩

theorem smoothG_yv (z : Fin (2 * ρ + k + 1) → ℂ) (j : Fin (mdim k ρ (Fin.last ρ))) :
    SmoothG k ρ (fun g => yv k ρ z (Fin.last ρ) g j) :=
  smoothG_of_sf (Formalism.FourierDecayAlt.P.Qx3.sf_yv z j)

theorem smoothG_ybv (z : Fin (2 * ρ + k + 1) → ℂ) (j : Fin (mdim k ρ (Fin.last ρ))) :
    SmoothG k ρ (fun g => ybv k ρ z (Fin.last ρ) g j) :=
  smoothG_of_sf (Formalism.FourierDecayAlt.P.Qx3.sf_ybv z j)

theorem parOK_EH (a b : Fin (mdim k ρ (Fin.last ρ))) :
    ParOK k ρ (E := E) (EH k ρ (posL k ρ (Fin.last ρ) a) (posL k ρ (Fin.last ρ) b)) :=
  parOK_congr (parOK_add (parOK_rdV (Formalism.FourierDecayAlt.P.Qx3.lieLev_of (Formalism.FourierDecayAlt.P.Qx3.hpart_lie (Fin.last ρ) a b).1))
    (parOK_csmul Complex.I
      (parOK_rdV (Formalism.FourierDecayAlt.P.Qx3.lieLev_of (Formalism.FourierDecayAlt.P.Qx3.hpart_lie (Fin.last ρ) a b).2)))) (fun f g => rfl)

theorem parOK_Top (u : ℂ) (a b : Fin (mdim k ρ (Fin.last ρ))) :
    ParOK k ρ (E := E) (Top (EH k ρ) u (posL k ρ (Fin.last ρ) a) (posL k ρ (Fin.last ρ) b)) := by
  by_cases hab : posL k ρ (Fin.last ρ) a = posL k ρ (Fin.last ρ) b
  · exact parOK_congr (parOK_add (parOK_csmul u parOK_id) (parOK_EH a b)) (fun f g => by simp [Formalism.QuantumDeterminants.Top, hab])
  · exact parOK_congr (parOK_add parOK_zero (parOK_EH a b)) (fun f g => by simp [Formalism.QuantumDeterminants.Top, hab])

theorem parOK_qminor {t : ℕ} (a b : Fin t → Fin (mdim k ρ (Fin.last ρ))) (u : ℂ) :
    ParOK k ρ (E := E) (qminorOp (EH k ρ) (posL k ρ (Fin.last ρ) ∘ a) (posL k ρ (Fin.last ρ) ∘ b) u) := by
  have key : ∀ σ : Equiv.Perm (Fin t), ParOK k ρ (E := E) (fun f g =>
      (((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun j : Fin t =>
        Top (E := E) (EH k ρ) (u - ((j : ℕ) : ℂ)) ((posL k ρ (Fin.last ρ) ∘ a) (σ j))
          ((posL k ρ (Fin.last ρ) ∘ b) j)).foldr (fun T h => T h) f g)) := by
    intro σ
    refine parOK_csmul _ (parOK_foldr _ ?_)
    intro T hT
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact parOK_Top _ _ _
  refine parOK_congr (parOK_sum Finset.univ (fun σ _ => key σ)) (fun f g => ?_)
  simp [qminorOp, Finset.sum_apply]

theorem parOK_chatL (u : ℂ) (a β : Mx k ρ → Fin (mdim k ρ (Fin.last ρ)) → ℂ)
    (ha : ∀ j, SmoothG k ρ (fun g => a g j)) (hβ : ∀ j, SmoothG k ρ (fun g => β g j)) :
    ParOK k ρ (E := E) (chatL (EH k ρ) (posL k ρ (Fin.last ρ)) u a β) := by
  refine parOK_congr (parOK_sum Finset.univ fun i' _ => parOK_sum Finset.univ fun j' _ =>
    parOK_smulG (smoothG_mul (smoothG_mul (smoothG_const _) (hβ i')) (ha j')) (parOK_qminor _ _ _))
    (fun f g => rfl)

theorem parOK_chat2L (u : ℂ) (a a' β β' : Mx k ρ → Fin (mdim k ρ (Fin.last ρ)) → ℂ)
    (ha : ∀ j, SmoothG k ρ (fun g => a g j)) (ha' : ∀ j, SmoothG k ρ (fun g => a' g j))
    (hβ : ∀ j, SmoothG k ρ (fun g => β g j)) (hβ' : ∀ j, SmoothG k ρ (fun g => β' g j)) :
    ParOK k ρ (E := E) (chat2L (EH k ρ) (posL k ρ (Fin.last ρ)) u a a' β β') := by
  refine parOK_congr (parOK_sum Finset.univ fun i₁ _ => parOK_sum Finset.univ fun i₂ _ =>
    parOK_sum Finset.univ fun j₁ _ => parOK_sum Finset.univ fun j₂ _ => ?_) (fun f g => rfl)
  by_cases hc : i₁ < i₂ ∧ j₁ < j₂
  · refine parOK_congr (parOK_smulG (smoothG_mul (smoothG_mul
      (smoothG_const ((-1 : ℂ) ^ ((i₁ : ℕ) + (i₂ : ℕ) + (j₁ : ℕ) + (j₂ : ℕ))))
      (smoothG_sub (smoothG_mul (hβ i₁) (hβ' i₂)) (smoothG_mul (hβ i₂) (hβ' i₁))))
      (smoothG_sub (smoothG_mul (ha j₁) (ha' j₂)) (smoothG_mul (ha j₂) (ha' j₁)))) (parOK_qminor (skip2 i₁ i₂) (skip2 j₁ j₂) u))
      (fun f g => by simp only [if_pos hc])
  · exact parOK_congr parOK_zero (fun f g => by simp only [if_neg hc])

theorem parOK_tL (z z' : Fin (2 * ρ + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2) :
    ParOK k ρ (E := E) (tL k ρ z z' (Fin.last ρ) Y p q) := by
  fin_cases p <;> fin_cases q
  · show ParOK k ρ (capL k ρ (Fin.last ρ) (uC k ρ (Fin.last ρ) Y))
    exact parOK_qminor id id _
  · show ParOK k ρ (fun f g => -(chatL (EH k ρ) (posL k ρ (Fin.last ρ)) (uC k ρ (Fin.last ρ) Y - 1)
      (fun _ => xv k ρ z' (Fin.last ρ)) (ybv k ρ z (Fin.last ρ)) f g))
    exact parOK_neg (parOK_chatL _ _ _ (fun j => smoothG_const _) (fun j => smoothG_ybv z j))
  · show ParOK k ρ (fun f g => -(chatL (EH k ρ) (posL k ρ (Fin.last ρ)) (uC k ρ (Fin.last ρ) Y) (yv k ρ z (Fin.last ρ))
      (fun _ => xbv k ρ z' (Fin.last ρ)) f g))
    exact parOK_neg (parOK_chatL _ _ _ (fun j => smoothG_yv z j) (fun j => smoothG_const _))
  · show ParOK k ρ (fun f g => -(chat2L (EH k ρ) (posL k ρ (Fin.last ρ)) (uC k ρ (Fin.last ρ) Y - 1)
      (yv k ρ z (Fin.last ρ)) (fun _ => xv k ρ z' (Fin.last ρ)) (ybv k ρ z (Fin.last ρ))
      (fun _ => xbv k ρ z' (Fin.last ρ)) f g))
    exact parOK_neg (parOK_chat2L _ _ _ _ _ (fun j => smoothG_yv z j) (fun j => smoothG_const _)
      (fun j => smoothG_ybv z j) (fun j => smoothG_const _))

end Ent

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Act

variable {k ρ : ℕ} {z z' : Fin (2 * ρ + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Q.Mx k ρ → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)}

theorem rad_zero (Φ : Q.RadSp k ρ z z' π π') {x : (Fin ρ → ℂ) × Q.Mx k ρ} (hx : x ∉ Q.DomR k ρ z z') :
    (Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) x.1 x.2 = 0 := Φ.2.1 x hx

theorem one_mem_OmX : (fun _ => (1 : ℂ)) ∈ OmX ρ := fun _ => one_ne_zero

theorem good_fn (hT : 0 ≤ Tz k ρ z * Tz k ρ z') (X : Q.ActualOps k ρ z z' π π') (j : Fin 6) :
    Good z z' π π' (X.fn j) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  set Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp) := fun Z y =>
    if 0 < Q.GGl k ρ z z' (Matrix.of y) then Q.fnVal k ρ z z' j (Matrix.of y) • Ψf Z y else 0 with hΦf

  have key : ∀ (Φ : Q.RadSp k ρ z z' π π') (c : Fin ρ → ℂ) (y : Mt k ρ),
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' (Matrix.of y) →
      (X.fn j Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) =
        Q.fnVal k ρ z z' j (Matrix.of y) • (Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) := by
    intro Φ c y hG hpos
    by_cases hD : ((c, Matrix.of y) : (Fin ρ → ℂ) × Q.Mx k ρ) ∈ Q.DomR k ρ z z'
    · exact X.fn_apply j Φ (c, Matrix.of y) hD
    · rw [rad_zero (X.fn j Φ) hD, rad_zero Φ hD, smul_zero]
  have key0 : ∀ (Φ : Q.RadSp k ρ z z' π π') (c : Fin ρ → ℂ) (y : Mt k ρ),
      ¬ 0 < Q.GGl k ρ z z' (Matrix.of y) → (X.fn j Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = 0 := by
    intro Φ c y hpos
    exact rad_zero (X.fn j Φ) (x := (c, Matrix.of y)) (fun hD => hpos hD.2.2)
  refine ⟨Φf, fun Z c y hG => ?_, ?_, fun K hK q hq hG hqK => ?_, ?_⟩
  · by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key (Ψ Z) c y hG hpos, hR Z c y hG, hΦf]
      simp only [if_pos hpos]
    · rw [key0 (Ψ Z) c y hpos, hΦf]
      simp only [if_neg hpos]
  · intro q₀ hq hG
    obtain ⟨U, F, hU, hqU, hFs, hfF⟩ := hF q₀ hq hG
    have hfn := Formalism.FourierDecayAlt.P.Qx5.fnVal_contDiffOn (z := z) (z' := z') (k := k) (r := ρ) hT j
    have hm : ContDiff ℝ ∞ fun q : Par × Mt k ρ =>
        (((fun _ => (1 : ℂ)), (Matrix.of q.2 : Q.Mx k ρ)) : (Fin ρ → ℂ) × Q.Mx k ρ) :=
      contDiff_const.prodMk contDiff_snd
    refine ⟨U ∩ U₀, fun q => Q.fnVal k ρ z z' j (Matrix.of q.2) • F q, hU.inter hU₀, ⟨hqU, hq⟩, ?_, ?_⟩
    · refine ContDiffOn.smul (hfn.comp hm.contDiffOn (fun q hq' => ?_)) (hFs.mono Set.inter_subset_left)
      exact ⟨one_mem_OmX, (hUpos hq'.2).2⟩
    · intro q hq' hG'
      have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq'.2).2
      show Φf q.1 q.2 = _
      rw [hΦf]
      simp only [if_pos hpos]
      rw [show Ψf q.1 q.2 = F q from hfF q hq'.1 hG']
  · have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq).2
    rw [hΦf]
    simp only [if_pos hpos]
    rw [hK q hG (fun h => hqK (subset_closure h)), smul_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key Ψi c y hyG hpos, hi c y hyV hyG, ← integral_smul]
      refine integral_congr_ae (ae_of_all _ fun Z => ?_)
      rw [hΦf]
      simp only [if_pos hpos]
    · rw [key0 Ψi c y hpos]
      have : (fun Z => Φf Z y) = fun _ => 0 := by
        funext Z
        rw [hΦf]
        simp only [if_neg hpos]
      rw [this, integral_zero]

theorem good_alt_bis (hOm : ∀ c : Fin ρ → ℂ, c ∈ OmX ρ) (hS : ∀ c c' : Fin ρ → ℂ, c = c')
    (X : Q.ActualOps k ρ z z' π π') (Y : ℂ) (a b : Fin 2) : Good z z' π π' (X.t Y a b) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  set c₁ : Fin ρ → ℂ := fun _ => 1 with hc₁
  set f : Par → Q.Mx k ρ → (Wq →L[ℂ] Wp) := fun Z => (Ψ Z : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁ with hfdef
  have hf : PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2)) :=
    parFam_congr hF (fun q _ hG => (hR q.1 c₁ q.2 hG).symm) hU₀
  obtain ⟨a1, b1, c1⟩ := parOK_tL (E := Wq →L[ℂ] Wp) z z' Y a b Par U₀ hU₀ f hf
  set Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp) := fun Z y =>
    if 0 < Q.GGl k ρ z z' (Matrix.of y) then tL k ρ z z' (Fin.last ρ) Y a b (f Z) (Matrix.of y) else 0 with hΦf
  have key : ∀ (Φ : Q.RadSp k ρ z z' π π') (y : Mt k ρ),
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → 0 < Q.GGl k ρ z z' (Matrix.of y) →
      (X.t Y a b Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁ (Matrix.of y) =
        tL k ρ z z' (Fin.last ρ) Y a b ((Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁) (Matrix.of y) := by
    intro Φ y hG hpos
    exact X.t_apply Y a b Φ (c₁, Matrix.of y) ⟨hOm c₁, hG, hpos⟩
  have key0 : ∀ (Φ : Q.RadSp k ρ z z' π π') (c : Fin ρ → ℂ) (y : Mt k ρ),
      ¬ 0 < Q.GGl k ρ z z' (Matrix.of y) → (X.t Y a b Φ : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = 0 := by
    intro Φ c y hpos
    exact rad_zero (X.t Y a b Φ) (x := (c, Matrix.of y)) (fun hD => hpos hD.2.2)
  refine ⟨Φf, fun Z c y hG => ?_, ?_, fun K hK q hq hG hqK => ?_, ?_⟩
  · rw [hS c c₁]
    by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key (Ψ Z) y hG hpos, hΦf]
      simp only [if_pos hpos]
      rfl
    · rw [key0 (Ψ Z) c₁ y hpos, hΦf]
      simp only [if_neg hpos]
  · exact parFam_congr a1 (fun q hq _ => by
      have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq).2
      show _ = Φf q.1 q.2
      rw [hΦf]
      simp only [if_pos hpos]) hU₀
  · have hpos : 0 < Q.GGl k ρ z z' (Matrix.of q.2) := (hUpos hq).2
    rw [hΦf]
    simp only [if_pos hpos]
    refine b1 q hq hG (closure K)ᶜ isClosed_closure.isOpen_compl hqK (fun q' hq' hG' => ?_)
    show (Ψ q'.1 : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁ (Matrix.of q'.2) = 0
    rw [hR q'.1 c₁ q'.2 hG']
    exact hK q' hG' (fun h => hq' (subset_closure h))
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    rw [hS c c₁]
    by_cases hpos : 0 < Q.GGl k ρ z z' (Matrix.of y)
    · rw [key Ψi y hyG hpos]
      rw [c1 ν Kp hKp hν ((Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c₁) y V hV hyV hyG hKV (fun y' hy' hG' => by
        rw [hi c₁ y' hy' hG']
        refine integral_congr_ae (ae_of_all _ fun Z => ?_)
        exact (hR Z c₁ y' hG').symm)]
      refine integral_congr_ae (ae_of_all _ fun Z => ?_)
      show _ = Φf Z y
      rw [hΦf]
      simp only [if_pos hpos]
    · rw [key0 Ψi c₁ y hpos]
      have : (fun Z => Φf Z y) = fun _ => 0 := by
        funext Z
        rw [hΦf]
        simp only [if_neg hpos]
      rw [this, integral_zero]

end Act

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFP
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutFP

def GoodFnLeaf : Prop :=
  ∀ (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (π : Q.Mx k ρ → (Wp →L[ℂ] Wp)) (π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)),
    0 ≤ Tz k ρ z * Tz k ρ z' → ∀ (X : Q.ActualOps k ρ z z' π π') (j : Fin 6), ParameterFamilyAlgebra.Good z z' π π' (X.fn j)

def GoodTLeaf : Prop :=
  ∀ (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (π : Q.Mx k ρ → (Wp →L[ℂ] Wp)) (π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)),
    (∀ c : Fin ρ → ℂ, c ∈ OmX ρ) → (∀ c c' : Fin ρ → ℂ, c = c') →
    ∀ (X : Q.ActualOps k ρ z z' π π') (Y : ℂ) (a b : Fin 2), ParameterFamilyAlgebra.Good z z' π π' (X.t Y a b)

section Asm

open Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gens_good (hfn : GoodFnLeaf) (ht : GoodTLeaf) (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π')
    (μ : Measure (Mt P.k P.r)) (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ) (hD : IsData P z z' π π' X μ L st l0)
    (hOm : ∀ c : Fin P.r → ℂ, c ∈ OmX P.r) (hS : ∀ c c' : Fin P.r → ℂ, c = c') :
    HerA.Gens (ParameterFamilyAlgebra.goodAlg z z' π π') L st := by
  obtain ⟨κ, hx, hxi, -⟩ :=
    xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  have hT : 0 ≤ Tz P.k P.r z * Tz P.k P.r z' := Formalism.FourierDecayAlt.P.Qx5.place_alt_alt hD.1
  obtain ⟨-, -, hAL, hQQ, -, -, -, hst⟩ := hD
  have hF : ∀ i j, Q.mkP (X.fn i) (X.fn j) ∈ ParameterFamilyAlgebra.goodAlg z z' π π' := fun i j =>
    ParameterFamilyAlgebra.good_mkP (hfn P.k P.r z z' Wp Wq π π' hT X i) (hfn P.k P.r z z' Wp Wq π π' hT X j)
  have hz : ∀ g ∈ zfns L, g ∈ ParameterFamilyAlgebra.goodAlg z z' π π' := by
    obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4, h5, h6, -⟩ := hAL
    intro g hg
    simp only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h1]; exact hF _ _
    · rw [h2]; exact hF _ _
    · rw [h3]; exact hF _ _
    · rw [h4]; exact hF _ _
    · rw [h5]; exact hF _ _
    · rw [h6]; exact hF _ _
  have hQ : ∀ Y : ℂ, star Y = Y → ∀ i j, st.QQ Y i j ∈ ParameterFamilyAlgebra.goodAlg z z' π π' := by
    intro Y _ i j
    rw [hQQ Y, Matrix.smul_apply]
    refine (ParameterFamilyAlgebra.goodAlg z z' π π').smul_mem ?_ _
    exact ParameterFamilyAlgebra.good_mkP (ht P.k P.r z z' Wp Wq π π' hOm hS X Y i j) (ht P.k P.r z z' Wp Wq π π' hOm hS X _ j i)
  exact HerA.gens_of _ L st hst κ _ hx hxi hz hQ

theorem frameParam_of (hfn : GoodFnLeaf) (ht : GoodTLeaf) : PBI.FrameParam := by
  intro Wp Wq _ _ _ _ _ _ P p X μ L st hD w hA Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  have hr0 : ∀ l : Fin (JC.parLev P P.r).r, False := fun l => by
    have := l.isLt
    simp only [JC.parLev, Nat.sub_self] at this
    omega
  have hOm : ∀ c : Fin (JC.parLev P P.r).r → ℂ, c ∈ OmX (JC.parLev P P.r).r := fun c l => (hr0 l).elim
  have hS : ∀ c c' : Fin (JC.parLev P P.r).r → ℂ, c = c' := fun c c' => funext fun l => (hr0 l).elim
  have hg := gens_good hfn ht (JC.parLev P P.r) _ _ _ _ X μ L st p.l0 hD hOm hS
  have hent : ∀ e e', ParameterFamilyAlgebra.Good _ _ _ _ ((Fr.ofWord L st (D.positionted w)).F e e').1 := fun e e' =>
    ((HerA.frameAlg L st hD.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2 hg (D.positionted w) hA e e').1).1
  have key := fun e b => hent e b Par U₀ hU₀ hUpos (fun Z => Ψ Z b) (fun Z y => Ψf Z b y)
    (fun Z c y hy => hR Z b c y hy) (hF b)
  choose Φ hΦR hΦF hΦS hΦW using key
  refine ⟨fun Z e y => ∑ b, Φ e b Z y, ?_, ?_, ?_, ?_⟩
  · intro Z e c y hy
    simp only [P5.act, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun b _ => hΦR e b Z c y hy
  · intro e
    exact ParameterFamilyAlgebra.parFam_sum _ fun b _ => hΦF e b
  · intro K hK e q hq hG hqK
    exact Finset.sum_eq_zero fun b _ => hΦS e b K (fun q' hG' hq' => hK b q' hG' hq') q hq hG hqK
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi e c
    simp only [P5.act, Submodule.coe_sum, Finset.sum_apply]
    rw [integral_finsetSum _ (fun b _ => ParameterFamilyAlgebra.parFam_integrable (hΦF e b) hKp hν hyG
      (fun Z hZ => hKV ⟨hZ, hyV⟩))]
    exact Finset.sum_congr rfl fun b _ => hΦW e b ν Kp hKp hν (Ψi b) y V hV hyV hyG hKV
      (fun c' y' hy' hG' => hi b c' y' hy' hG') c

end Asm

end Formalism.FourierDecayAlt.P.CutFP
end
end

noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem good_function_leaf : CutFP.GoodFnLeaf :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hT X j => ParameterFamilyAlgebra.good_fn hT X j

theorem good_transfer_leaf : CutFP.GoodTLeaf :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hOm hS X Y a b => ParameterFamilyAlgebra.good_alt_bis hOm hS X Y a b

theorem frame_parameter_regularity : PBI.FrameParam :=
  CutFP.frameParam_of good_function_leaf good_transfer_leaf

end Formalism.FourierDecayAlt.P
