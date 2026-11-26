module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.LagLine
public import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.ExistsScaledIntegralLatticeSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.MixedModelPlanes.IndicatorCosetScaledIntegralEqRestrictedProductStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.EvAdm
theorem _root_.PositivityTheory.Mix.T.indicator_coset_scaledIntegral_eq_restrictedProduct : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F) (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    ∃ φ : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ y : κ → FiniteAdeleRing (𝓞 F) F, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) y =
        ∏ᶠ v, φ v fun i => evalV F v (y i) := by
  first | exact @GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod | exact fun _ => @GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod | exact GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod | exact @GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod trivial
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.GeoCore
section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.GeoAlg
noncomputable section

open Matrix GlobalTheory.WeilM Module

namespace PositivityTheory.ThKF0.Geo

section Form

variable {F : Type} [Field F] {κ : Type} [Fintype κ]

def om (F : Type) [Field F] (κ : Type) [Fintype κ] : LinearMap.BilinForm F ((κ → F) × (κ → F)) :=
  LinearMap.mk₂ F (fun w w' => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring)

theorem om_apply (w w' : (κ → F) × (κ → F)) : om F κ w w' = w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 := rfl

theorem eq_zero_of_om (w : (κ → F) × (κ → F)) (h : ∀ w', om F κ w' w = 0) : w = 0 := by
  classical
  have h1 : ∀ i, w.2 i = 0 := fun i => by
    have := h (Pi.single i 1, 0)
    simpa [om_apply, single_dotProduct] using this
  have h2 : ∀ i, w.1 i = 0 := fun i => by
    have := h (0, Pi.single i 1)
    simpa [om_apply, dotProduct_single] using this
  exact Prod.ext (funext h2) (funext h1)

theorem om_refl : (om F κ).IsRefl := fun x y h => by
  rw [om_apply] at h ⊢
  linear_combination -h

theorem lag_of_finrank (L : Submodule F ((κ → F) × (κ → F))) (h : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2)
    (hr : finrank F L = Fintype.card κ) (a) : a ∈ L ↔ ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
  have hiso : L ≤ (om F κ).orthogonal L := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [om_apply, h y hy x hx, sub_self]
  have hbot : (L ⊓ (om F κ).orthogonal ⊤ : Submodule F ((κ → F) × (κ → F))) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    apply eq_zero_of_om
    intro w'
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hx.2) w' Submodule.mem_top
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal (om_refl (F := F) (κ := κ)) L
  rw [hbot, finrank_bot, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hr] at hdim
  have heq : L = (om F κ).orthogonal L := Submodule.eq_of_le_of_finrank_eq hiso (by rw [hr]; omega)
  constructor
  · intro ha
    exact h a ha
  · intro ha
    rw [heq, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    rw [om_apply, ha y hy, sub_self]

end Form

section Abs

variable {F : Type} [Field F] {A : Type} [CommRing A] [Algebra F A]


variable (A) in
def emb (κ : Type) : ((κ → F) × (κ → F)) →ₗ[F] ((κ → A) × (κ → A)) :=
  ((Algebra.linearMap F A).compLeft κ).prodMap ((Algebra.linearMap F A).compLeft κ)

theorem emb_apply {κ : Type} (w : (κ → F) × (κ → F)) :
    emb (F := F) A κ w = (fun i => algebraMap F A (w.1 i), fun i => algebraMap F A (w.2 i)) := rfl

theorem emb_inj (hA : Function.Injective (algebraMap F A)) {κ : Type} : Function.Injective (emb (F := F) A κ) := by
  intro a b hab
  rw [emb_apply, emb_apply] at hab
  simp only [Prod.mk.injEq] at hab
  exact Prod.ext (funext fun i => hA (congrFun hab.1 i)) (funext fun i => hA (congrFun hab.2 i))

theorem emb_form {κ : Type} [Fintype κ] (a b : (κ → F) × (κ → F)) :
    (emb (F := F) A κ a).1 ⬝ᵥ (emb (F := F) A κ b).2 - (emb (F := F) A κ b).1 ⬝ᵥ (emb (F := F) A κ a).2 = algebraMap F A (om F κ a b) := by
  simp [emb_apply, om_apply, dotProduct]

variable {VA : Type} [AddCommGroup VA] [Module A VA] [Module F VA] [IsScalarTower F A VA] {BA : VA → VA → A}
  {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module F V]

theorem exists_coord (hA : Function.Injective (algebraMap F A)) (co : Darboux BA κ) (inc : V →ₗ[F] VA)
    (hr : ∀ x, ∃ w, co.e (inc x) = emb (F := F) A κ w) :
    ∃ r : V →ₗ[F] (κ → F) × (κ → F), ∀ x, co.e (inc x) = emb (F := F) A κ (r x) := by
  choose f hf using hr
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, hf⟩
  · intro x y
    apply emb_inj hA
    rw [map_add (f := _), ← hf, ← hf, ← hf, map_add (f := _), map_add (f := _)]
  · intro c x
    apply emb_inj hA
    rw [RingHom.id_apply, map_smul, ← hf, ← hf, map_smul]
    exact co.e.toLinearMap.map_smul_of_tower c (inc x)

theorem schr_add [Invertible (2 : A)] (ψ : AddChar A ℂ) (a b : (κ → A) × (κ → A))
    (h : a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 = 0) (φ : (κ → A) → ℂ) : schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by
  funext x
  have e1 : x ⬝ᵥ (a + b).2 + ⅟(2 : A) * ((a + b).1 ⬝ᵥ (a + b).2) =
      (x ⬝ᵥ a.2 + ⅟(2 : A) * (a.1 ⬝ᵥ a.2)) + ((x + a.1) ⬝ᵥ b.2 + ⅟(2 : A) * (b.1 ⬝ᵥ b.2)) := by
    have h2 : ⅟(2 : A) * 2 = 1 := invOf_mul_self 2
    simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    linear_combination (-⅟(2 : A)) * h + (a.1 ⬝ᵥ b.2) * h2
  have e2 : x + (a + b).1 = x + a.1 + b.1 := by rw [Prod.fst_add, add_assoc]
  simp only [schr]
  rw [e1, e2, AddChar.map_add_eq_mul, mul_assoc]

variable {VB : Type} [AddCommGroup VB] [Module A VB] [Module F VB] [IsScalarTower F A VB] {BB : VB → VB → A}
  {κ₁ : Type} [Fintype κ₁] {V₁ : Type} [AddCommGroup V₁] [Module F V₁] {U : Type} [AddCommGroup U] [Module F U]

theorem exists_lag [Invertible (2 : A)] [FiniteDimensional F V₁] [FiniteDimensional F U]
    (hA : Function.Injective (algebraMap F A)) (co : Darboux BA κ) (inc : V →ₗ[F] VA) (hinc : Function.Injective inc)
    (hr : ∀ x, ∃ w, co.e (inc x) = emb (F := F) A κ w)
    (co₁ : Darboux BB κ₁) (inc₁ : V₁ →ₗ[F] VB) (hinc₁ : Function.Injective inc₁)
    (hr₁ : ∀ x, ∃ w, co₁.e (inc₁ x) = emb (F := F) A κ₁ w) (hd₁ : finrank F V₁ = 2 * Fintype.card κ₁)
    (j : V₁ →ₗ[F] V) (jA : VB →ₗ[A] VA) (hj : ∀ z, inc (j z) = jA (inc₁ z)) (hB : ∀ z z', BA (jA z) (jA z') = BB z z')
    (s : U →ₗ[F] V) (hs : Function.Injective s) (hss : ∀ u u', BA (inc (s u)) (inc (s u')) = 0)
    (hjs : ∀ z u, BA (jA z) (inc (s u)) = 0) (hd : finrank F U + Fintype.card κ₁ = Fintype.card κ) :
    ∃ L : Submodule F ((κ → F) × (κ → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧ finrank F L = Fintype.card κ ∧
      ∀ (t : A), ∀ w ∈ L, ∃ (u : U) (z : VB), (co₁.e z).1 = 0 ∧ ∀ (ψ : AddChar A ℂ) (φ : (κ → A) → ℂ),
        schr ψ (t • emb (F := F) A κ w) φ = co.rho ψ (t • inc (s u)) (co.rho ψ (jA z) φ) := by
  classical
  obtain ⟨r, hr'⟩ := exists_coord hA co inc hr
  obtain ⟨r₁, hr₁'⟩ := exists_coord hA co₁ inc₁ hr₁
  have hBx : ∀ x y, BA (inc x) (inc y) = algebraMap F A (om F κ (r x) (r y)) := fun x y => by
    rw [co.form, hr', hr', emb_form]
  have hBz : ∀ z z', BB (inc₁ z) (inc₁ z') = algebraMap F A (om F κ₁ (r₁ z) (r₁ z')) := fun z z' => by
    rw [co₁.form, hr₁', hr₁', emb_form]
  have hBA0 : ∀ w, BA w 0 = 0 := fun w => by
    rw [co.form]
    simp
  have hrinj : Function.Injective r := by
    intro a b hab
    apply hinc
    apply co.e.injective
    rw [hr', hr', hab]
  have hr₁inj : Function.Injective r₁ := by
    intro a b hab
    apply hinc₁
    apply co₁.e.injective
    rw [hr₁', hr₁', hab]
  have hr₁surj : Function.Surjective r₁ := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := r₁) ?_).mp hr₁inj
    rw [hd₁, Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
    ring
  let L₁ : Submodule F V₁ := LinearMap.ker ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁)
  have hL₁ : ∀ z, z ∈ L₁ ↔ (r₁ z).1 = 0 := fun z => by
    simp [L₁]
  have hfinL₁ : finrank F L₁ = Fintype.card κ₁ := by
    have hsurj : Function.Surjective ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁) := fun v => by
      obtain ⟨x, hx⟩ := hr₁surj (v, 0)
      exact ⟨x, by simp [hx]⟩
    have hrn := LinearMap.finrank_range_add_finrank_ker ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, hd₁] at hrn
    have e : finrank F L₁ =
        finrank F (LinearMap.ker ((LinearMap.fst F (κ₁ → F) (κ₁ → F)).comp r₁)) := rfl
    omega
  have hjinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).mpr fun z hz => ?_
    apply hr₁inj
    rw [map_zero]
    apply eq_zero_of_om
    intro v
    obtain ⟨z', rfl⟩ := hr₁surj v
    apply hA
    rw [← hBz, ← hB, ← hj, ← hj, hz]
    simp [hBA0]
  have hdisj : LinearMap.range s ⊓ L₁.map j = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx1
    obtain ⟨z, hz, hzs⟩ := Submodule.mem_map.mp hx2
    rw [Submodule.mem_bot]
    have hz0 : z = 0 := by
      apply hr₁inj
      rw [map_zero]
      apply eq_zero_of_om
      intro v
      obtain ⟨z', rfl⟩ := hr₁surj v
      apply hA
      rw [← hBz, ← hB, ← hj z, hzs, hjs, map_zero]
    rw [← hzs, hz0, map_zero]
  let L' : Submodule F V := LinearMap.range s ⊔ L₁.map j
  have hfinL' : finrank F L' = Fintype.card κ := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range s) (L₁.map j)
    rw [hdisj, finrank_bot, add_zero, LinearMap.finrank_range_of_inj hs,
      ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective j hjinj L₁), hfinL₁] at h1
    rw [← hd]
    exact h1
  have T1 : ∀ u u', om F κ (r (s u)) (r (s u')) = 0 := fun u u' => hA (by
    rw [← hBx, hss, map_zero])
  have T2 : ∀ z u, om F κ (r (j z)) (r (s u)) = 0 := fun z u => hA (by
    rw [← hBx, hj, hjs, map_zero])
  have T3 : ∀ u z, om F κ (r (s u)) (r (j z)) = 0 := fun u z => om_refl _ _ (T2 z u)
  have T4 : ∀ z z', z ∈ L₁ → z' ∈ L₁ → om F κ (r (j z)) (r (j z')) = 0 := fun z z' hz hz' => hA (by
    rw [← hBx, hj, hj, hB, hBz, om_apply, (hL₁ z).mp hz, (hL₁ z').mp hz']
    simp)
  have hiso : ∀ x ∈ L', ∀ y ∈ L', om F κ (r x) (r y) = 0 := by
    intro x hx y hy
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨p', hp', q', hq', rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hp
    obtain ⟨u', rfl⟩ := LinearMap.mem_range.mp hp'
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hq
    obtain ⟨z', hz', rfl⟩ := Submodule.mem_map.mp hq'
    simp only [map_add (f := _), LinearMap.add_apply, T1, T2, T3, T4 z z' hz hz', add_zero]
  refine ⟨L'.map r, ?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hb
    have h0 := hiso x hx y hy
    rw [om_apply] at h0
    exact sub_eq_zero.mp h0
  · rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective r hrinj L'), hfinL']
  · intro t w hw
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hw
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hp
    obtain ⟨z₀, hz₀, rfl⟩ := Submodule.mem_map.mp hq
    refine ⟨u, t • inc₁ z₀, ?_, fun ψ φ => ?_⟩
    · rw [map_smul, hr₁' z₀, emb_apply]
      funext i
      simp [(hL₁ z₀).mp hz₀]
    · have hsum : t • emb (F := F) A κ (r (s u + j z₀)) = co.e (t • inc (s u)) + co.e (jA (t • inc₁ z₀)) := by
        rw [← hr', map_add (f := _), map_add (f := _), hj, smul_add, map_smul, map_smul, map_smul]
      have hω : (co.e (t • inc (s u))).1 ⬝ᵥ (co.e (jA (t • inc₁ z₀))).2 -
          (co.e (jA (t • inc₁ z₀))).1 ⬝ᵥ (co.e (t • inc (s u))).2 = 0 := by
        have hf := co.form (jA (inc₁ z₀)) (inc (s u))
        rw [hjs] at hf
        rw [map_smul, map_smul, map_smul]
        simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        linear_combination (t * t) * hf
      simp only [Darboux.rho]
      rw [hsum, schr_add ψ _ _ hω φ]

end Abs

section Mat

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β α' β' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype α'] [DecidableEq α']
  [Fintype β'] [DecidableEq β']

theorem hTens_eq (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = Matrix.trace (xᵀ * (JA * y.map c * JBᵀ)) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem hTens_mul (JA : Matrix α α E) (JB : Matrix β β E) (a : Matrix α α' E) (b : Matrix β β' E) (x y : Matrix α' β' E) :
    hTens c JA JB (a * x * bᵀ) (a * y * bᵀ) = hTens c (aᵀ * JA * a.map c) (bᵀ * JB * b.map c) x y := by
  rw [hTens_eq, hTens_eq]
  have hm : (a * y * bᵀ).map c = a.map c * y.map c * (b.map c)ᵀ := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, map_sum, map_mul]
  rw [hm]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm b]
  simp only [Matrix.mul_assoc]

theorem hTens_vec (JA : Matrix α α E) (JB : Matrix β β E) (w : Matrix α β E) (a : α → E) (b : β → E) :
    hTens c JA JB w (vecMulVec a b) = (JA *ᵥ fun i => c (a i)) ⬝ᵥ (w *ᵥ (JB *ᵥ fun i => c (b i))) := by
  simp only [hTens, vecMulVec_apply, map_mul, dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end Mat

end PositivityTheory.ThKF0.Geo
end
end

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace PositivityTheory.ThKF0.Geo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

def HasLag (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ψ : AddChar (AF F) ℂ) (ι : Matrix (Fin n) (Fin n₁) E)
    (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E))) : Prop :=
  ∃ L : Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)), (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) ∧
    Module.finrank F L = Fintype.card (Fin n × Fin d) ∧
    ∀ (t : AF F), ∀ w ∈ L, ∃ u ∈ I, ∃ z : Matrix (Fin n₁) (Fin d₁) (AE F E),
      (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
        schr ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
          M.co.rho ψ u (M.co.rho ψ (incM F ι * z * (incM F ι')ᵀ) φ)

theorem alg_inj : Function.Injective (algebraMap F (AF F)) := NumberField.AdeleRing.algebraMap_injective (𝓞 F) F


variable (F E) in
def incL (α β : Type) : Matrix α β E →ₗ[F] Matrix α β (AE F E) :=
  (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E).toLinearMap.mapMatrix

theorem incL_apply {α β : Type} (x : Matrix α β E) : incL F E α β x = incM F x := rfl

theorem incL_inj {α β : Type} : Function.Injective (incL F E α β) := fun _ _ h => Matrix.ext fun i j =>
  Algebra.TensorProduct.includeRight_injective alg_inj (congrFun (congrFun h i) j)

theorem incM_mul {α β γ : Type} [Fintype β] (a : Matrix α β E) (b : Matrix β γ E) :
    incM F (a * b) = incM F a * incM F b := Matrix.map_mul

theorem cA_incl (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := rfl

theorem incM_gram {m m₁ : ℕ} {J : Matrix (Fin m) (Fin m) E} {J₁ : Matrix (Fin m₁) (Fin m₁) E} {ι : Matrix (Fin m) (Fin m₁) E}
    (h : ιᵀ * J * ι.map σ = J₁) : (incM F ι)ᵀ * incM F J * (incM F ι).map (cA σ) = incM F J₁ := by
  rw [← h, incM_mul, incM_mul]
  rfl

theorem incM_vec {α β : Type} (a : α → E) (b : β → E) : incM F (Matrix.vecMulVec a b) =
    Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (a i)) (fun i => inclR (F := F) (AF F) (b i)) := by
  ext i j
  simp [incM, Matrix.vecMulVec_apply]

theorem incM_mulVec {α β : Type} [Fintype β] (a : Matrix α β E) (b : β → E) :
    incM F a *ᵥ (fun i => inclR (F := F) (AF F) (b i)) = fun i => inclR (F := F) (AF F) ((a *ᵥ b) i) := by
  funext i
  simp [incM, Matrix.mulVec, dotProduct]

theorem inc_dot {α : Type} [Fintype α] (a b : α → E) :
    (fun i => inclR (F := F) (AF F) (a i)) ⬝ᵥ (fun i => inclR (F := F) (AF F) (b i)) = inclR (F := F) (AF F) (a ⬝ᵥ b) := by
  simp [dotProduct]

theorem hasLag_of (h2 : Module.finrank F E = 2) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ψ : AddChar (AF F) ℂ)
    (hM : M.IsGood ψ) (hM₁ : M₁.IsGood ψ) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (hι : ιᵀ * X.J * ι.map σ = X₁.J) (hι' : ι'ᵀ * W.J * ι'.map σ = W₁.J) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    {m : ℕ} (s : (Fin m → E) →ₗ[F] Matrix (Fin n) (Fin d) E) (hs : Function.Injective s)
    (hI : ∀ (t : AF F) u, t • incM F (s u) ∈ I)
    (hss : ∀ u u', hTens (cA σ) (incM F X.J) (incM F W.J) (incM F (s u)) (incM F (s u')) = 0)
    (hjs : ∀ (z : Matrix (Fin n₁) (Fin d₁) (AE F E)) u, hTens (cA σ) (incM F X.J) (incM F W.J) (incM F ι * z * (incM F ι')ᵀ) (incM F (s u)) = 0)
    (hd : m * 2 + n₁ * d₁ = n * d) : HasLag M M₁ ψ ι ι' I := by
  let j : Matrix (Fin n₁) (Fin d₁) E →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun z => ι * z * ι'ᵀ
      map_add' := fun _ _ => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun _ _ => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  let jA : Matrix (Fin n₁) (Fin d₁) (AE F E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun z => incM F ι * z * (incM F ι')ᵀ
      map_add' := fun _ _ => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun _ _ => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  obtain ⟨L, h1, h3, h4⟩ := exists_lag alg_inj M.co (incL F E _ _) incL_inj
    (fun x => by obtain ⟨y, z, h⟩ := hM.rat x; exact ⟨(y, z), h⟩) M₁.co (incL F E _ _) incL_inj
    (fun x => by obtain ⟨y, z, h⟩ := hM₁.rat x; exact ⟨(y, z), h⟩)
    (by rw [Module.finrank_matrix, h2]; simp; ring) j jA
    (fun z => by
      show incM F (ι * z * ι'ᵀ) = incM F ι * incM F z * (incM F ι')ᵀ
      rw [incM_mul, incM_mul]; rfl)
    (fun z z' => by
      show symp _ _ _ _ (incM F ι * z * (incM F ι')ᵀ) (incM F ι * z' * (incM F ι')ᵀ) = _
      rw [symp, symp, hTens_mul, incM_gram hι, incM_gram hι'])
    s hs (fun u u' => by rw [symp, incL_apply, incL_apply, hss, mul_zero, map_zero])
    (fun z u => by
      show symp _ _ _ _ (incM F ι * z * (incM F ι')ᵀ) (incM F (s u)) = _
      rw [symp, hjs, mul_zero, map_zero])
    (by rw [Module.finrank_pi_fintype]; simp [h2, hd])
  refine ⟨L, h1, h3, fun t w hw => ?_⟩
  obtain ⟨u, z, hz, h⟩ := h4 t w hw
  exact ⟨_, hI t u, z, hz, h ψ⟩

theorem x_ne {B : Base F E} {m m₁ i₀ i₁ : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {H : Plane E m m₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) : ∃ i, H.x i ≠ 0 := by
  by_contra h
  push Not at h
  have := hH.xy
  rw [form, show H.x = 0 from funext h, zero_dotProduct] at this
  exact zero_ne_one this

theorem orth_alt {B : Base F E} {m m₁ i₀ i₁ : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {H : Plane E m m₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    (incM F H.ι)ᵀ *ᵥ (incM F Y.J *ᵥ fun i => cA σ (inclR (F := F) (AF F) (H.x i))) = 0 := by
  have h : H.ιᵀ *ᵥ (Y.J *ᵥ fun i => σ (H.x i)) = 0 := funext fun k => by
    have := (hH.orth (Pi.single k 1)).1
    rw [form, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_single, mul_one, ← Matrix.mulVec_transpose] at this
    exact this
  simp only [cA_incl]
  rw [incM_mulVec, show (incM F H.ι)ᵀ = incM F H.ιᵀ from rfl, incM_mulVec, h]
  exact funext fun _ => map_zero _

theorem adapted_plane_isotropic_vector {B : Base F E} {m m₁ i₀ i₁ : ℕ} {Y : Spc F E m} {Y₁ : Spc F E m₁} {H : Plane E m m₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    (fun i => inclR (F := F) (AF F) (H.x i)) ⬝ᵥ (incM F Y.J *ᵥ fun i => cA σ (inclR (F := F) (AF F) (H.x i))) = 0 := by
  simp only [cA_incl]
  rw [incM_mulVec, inc_dot]
  exact (congrArg _ hH.xx).trans (map_zero _)

theorem gram_one {m : ℕ} (J : Matrix (Fin m) (Fin m) E) : (1 : Matrix (Fin m) (Fin m) E)ᵀ * J * (1 : Matrix _ _ E).map σ = J := by
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem hasLagrangian_skew_adapted {B : Base F E} (hB : B.IsGood σ) (M : Model σ X W) (M₁ : Model σ X W₁) (hM : M.IsGood B.ψ)
    (hM₁ : M₁.IsGood B.ψ) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hH : H'.IsAdapted σ B W W₁ i₀ i₁) :
    HasLag M M₁ B.ψ 1 H'.ι (iso0 n H') := by
  let s : (Fin n → E) →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun y => Matrix.vecMulVec y H'.x
      map_add' := fun _ _ => by ext i j; simp [Matrix.vecMulVec_apply, add_mul]
      map_smul' := fun _ _ => by ext i j; simp [Matrix.vecMulVec_apply] }
  have hs : ∀ y, s y = Matrix.vecMulVec y H'.x := fun _ => rfl
  obtain ⟨k, hk⟩ := x_ne hH
  refine hasLag_of hB.cm.2.2.1 M M₁ B.ψ hM hM₁ 1 H'.ι (gram_one _) hH.gram _ s (fun y y' h => funext fun i => ?_)
    (fun t u => ⟨t • fun i => inclR (F := F) (AF F) (u i), ?_⟩) (fun u u' => ?_) (fun z u => ?_) ?_
  · exact mul_right_cancel₀ hk (congrFun (congrFun h i) k)
  · rw [hs, incM_vec]
    ext i j
    simp [Matrix.vecMulVec_apply, incV]
  · rw [hs, hs, incM_vec, incM_vec, hTens_vec, Matrix.vecMulVec_mulVec, adapted_plane_isotropic_vector hH]
    simp
  · rw [hs, incM_vec, hTens_vec, ← Matrix.mulVec_mulVec, orth_alt hH]
    simp
  · rw [hH.rank]; ring

theorem hasLag_X {B : Base F E} (hB : B.IsGood σ) (M : Model σ X W) (M₁ : Model σ X₁ W) (hM : M.IsGood B.ψ)
    (hM₁ : M₁.IsGood B.ψ) {H : Plane E n n₁} {i₀ i₁ : ℕ} (hH : H.IsAdapted σ B X X₁ i₀ i₁) :
    HasLag M M₁ B.ψ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} := by
  let s : (Fin d → E) →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun y => Matrix.vecMulVec H.x y
      map_add' := fun _ _ => by ext i j; simp [Matrix.vecMulVec_apply, mul_add]
      map_smul' := fun _ _ => by ext i j; simp [Matrix.vecMulVec_apply] }
  have hs : ∀ y, s y = Matrix.vecMulVec H.x y := fun _ => rfl
  obtain ⟨k, hk⟩ := x_ne hH
  refine hasLag_of hB.cm.2.2.1 M M₁ B.ψ hM hM₁ H.ι 1 hH.gram (gram_one _) _ s (fun y y' h => funext fun i => ?_)
    (fun t u => ⟨t • fun i => inclR (F := F) (AF F) (u i), ?_⟩) (fun u u' => ?_) (fun z u => ?_) ?_
  · exact mul_left_cancel₀ hk (congrFun (congrFun h k) i)
  · rw [hs, incM_vec]
    ext i j
    simp [Matrix.vecMulVec_apply, incV]
  · rw [hs, hs, incM_vec, incM_vec, hTens_vec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMulVec, dotProduct_comm _ (fun i => inclR (F := F) (AF F) (H.x i)),
      adapted_plane_isotropic_vector hH]
    simp
  · rw [hs, incM_vec, hTens_vec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, orth_alt hH]
    simp
  · rw [hH.rank]; ring


open scoped Classical in
theorem proj_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (y : κ → AF F) :
    (LinearMap.proj y : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (y i).2) • ((BoundedContinuousFunction.evalCLM ℂ (fun i => evI F (y i))).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp only [LinearMap.coe_proj, Function.eval, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul, pureA]
  rw [mul_comm]
  rfl

theorem form_line (h : LagLine) {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (AE F E))}
    (hL : HasLag M M₁ ψ ι ι' I) (l l' : Fn F n d →ₗ[ℂ] ℂ) (hl : l ∈ (adeleClass F).adm (Fin n × Fin d))
    (hl' : l' ∈ (adeleClass F).adm (Fin n × Fin d))
    (hI : ∀ u ∈ I, ∀ Φ ∈ schA F (Fin n × Fin d), l (M.co.rho ψ u Φ) = l Φ ∧ l' (M.co.rho ψ u Φ) = l' Φ)
    (hz : ∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), (M₁.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
      l (M.co.rho ψ (incM F ι * z * (incM F ι')ᵀ) Φ) = l Φ ∧ l' (M.co.rho ψ (incM F ι * z * (incM F ι')ᵀ) Φ) = l' Φ)
    (h0 : ∃ Φ ∈ schA F (Fin n × Fin d), l' Φ ≠ 0) : ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), l Φ = c * l' Φ := by
  obtain ⟨L, h1, h2, h3⟩ := hL
  refine h F ψ hψ _ L (lag_of_finrank L h1 h2) l hl l' hl' (fun t w hw Φ hΦ => ?_) (fun t w hw Φ hΦ => ?_) h0
  · obtain ⟨u, hu, z, hz0, e⟩ := h3 t w hw
    rw [e, (hI u hu _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Φ hΦ)).1, (hz z hz0 Φ hΦ).1]
  · obtain ⟨u, hu, z, hz0, e⟩ := h3 t w hw
    rw [e, (hI u hu _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Φ hΦ)).2, (hz z hz0 Φ hΦ).2]

theorem map_line (h : LagLine) {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (AE F E))}
    (hL : HasLag M M₁ ψ ι ι' I) (T e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (hT : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), T (M.co.rho ψ (incM F ι * z * (incM F ι')ᵀ) Φ) = M₁.co.rho ψ z (T Φ))
    (he : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho ψ (incM F ι * z * (incM F ι')ᵀ) Φ) = M₁.co.rho ψ z (e Φ))
    (hTI : ∀ u ∈ I, ∀ Φ ∈ schA F (Fin n × Fin d), T (M.co.rho ψ u Φ) = T Φ)
    (heI : ∀ u ∈ I, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho ψ u Φ) = e Φ)
    (aT : (LinearMap.proj 0 : Fn F n₁ d₁ →ₗ[ℂ] ℂ) ∘ₗ T ∈ (adeleClass F).adm (Fin n × Fin d))
    (ae : (LinearMap.proj 0 : Fn F n₁ d₁ →ₗ[ℂ] ℂ) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d))
    (h0 : ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0) : ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), T Φ = c • e Φ := by
  have r0 : ∀ z, (M₁.co.e z).1 = 0 → ∀ Ψ : Fn F n₁ d₁, M₁.co.rho ψ z Ψ 0 = Ψ 0 := fun z hz Ψ => by
    simp [Darboux.rho, schr, hz]
  have r1 : ∀ y (Ψ : Fn F n₁ d₁), M₁.co.rho ψ (M₁.co.e.symm (y, 0)) Ψ 0 = Ψ y := fun y Ψ => by
    simp [Darboux.rho, schr]
  obtain ⟨Φ₀, hΦ₀, hne⟩ := h0
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.1 hne
  obtain ⟨c, hc⟩ := form_line h hψ hL _ _ aT ae
    (fun u hu Φ hΦ => ⟨congrFun (hTI u hu Φ hΦ) 0, congrFun (heI u hu Φ hΦ) 0⟩)
    (fun z hz Φ hΦ => ⟨(congrFun (hT z Φ hΦ) 0).trans (r0 z hz _), (congrFun (he z Φ hΦ) 0).trans (r0 z hz _)⟩)
    ⟨_, GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ Φ₀ hΦ₀, fun h' =>
      hy₀ (((congrFun (he (M₁.co.e.symm (y₀, 0)) Φ₀ hΦ₀) 0).trans (r1 y₀ _)).symm.trans h')⟩
  refine ⟨c, fun Φ hΦ => funext fun y => ?_⟩
  have := hc _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ (incM F ι * M₁.co.e.symm (y, 0) * (incM F ι')ᵀ) Φ hΦ)
  rw [Pi.smul_apply, smul_eq_mul, ← r1 y (T Φ), ← r1 y (e Φ), ← hT _ Φ hΦ, ← he _ Φ hΦ]
  exact this

end PositivityTheory.ThKF0.Geo
end
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.GeoAdm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace PositivityTheory.ThKF0.GeoAdm
open GlobalTheory.EvAdm
open scoped Classical

theorem boxS : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F) (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    ∃ φ : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ y : κ → FiniteAdeleRing (𝓞 F) F, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) y =
        ∏ᶠ v, φ v fun i => evalV F v (y i) := by
  exact PositivityTheory.Mix.T.indicator_coset_scaledIntegral_eq_restrictedProduct

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_invariant {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∀ x, ∀ z ∈ scaledInt F κ a, g (x + z) = g x := by
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  obtain ⟨hlc, hcs⟩ := hg'
  have hK : IsCompact (tsupport g) := hcs
  have hW : ∀ x : κ → FiniteAdeleRing (𝓞 F) F, ∃ W ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F),
      ∀ u ∈ W, ∀ w ∈ W, g (x + u + w) = g x := by
    intro x
    have h1 : {y | g y = g x} ∈ 𝓝 x := (hlc.isOpen_fiber (g x)).mem_nhds rfl
    have h2 : (fun u => x + u) ⁻¹' {y | g y = g x} ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
      (continuous_const_add x).continuousAt.preimage_mem_nhds (by simpa using h1)
    obtain ⟨W, hW0, hWW⟩ := exists_nhds_zero_half h2
    exact ⟨W, hW0, fun u hu w hw => by simpa [add_assoc] using hWW u hu w hw⟩
  choose W hW0 hWg using hW
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {y | y - x ∈ W x}) (fun x _ =>
    (continuous_sub_right x).continuousAt.preimage_mem_nhds (by simpa using hW0 x))
  have hV : (⋂ x ∈ t, W x) ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
    (Filter.biInter_finset_mem t).2 fun x _ => hW0 x
  have hkey : ∀ y ∈ tsupport g, ∀ z ∈ ⋂ x ∈ t, W x, g (y + z) = g y := by
    intro y hy z hz
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy)
    have hzx : z ∈ W x := Set.mem_iInter₂.1 hz x hx
    have e1 := hWg x (y - x) hyx z hzx
    have e2 := hWg x (y - x) hyx 0 (mem_of_mem_nhds (hW0 x))
    simp only [add_sub_cancel, add_zero] at e1 e2
    rw [e1, e2]
  have hV' : (fun z : κ → FiniteAdeleRing (𝓞 F) F => -z) ⁻¹' (⋂ x ∈ t, W x) ∈
      𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
    continuous_neg.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨a, ha, hsub⟩ := PositivityTheory.Mix.exists_scaled_integral_lattice_subset F κ _ (Filter.inter_mem hV hV')
  refine ⟨a, ha, fun y z hz => ?_⟩
  have hz' := hsub hz
  by_cases hy : y ∈ tsupport g
  · exact hkey y hy z hz'.1
  · by_cases hyz : y + z ∈ tsupport g
    · have h3 := hkey (y + z) hyz (-z) hz'.2
      have h4 : g y = g (y + z) := by simpa using h3
      exact h4.symm
    · rw [image_eq_zero_of_notMem_tsupport hyz, image_eq_zero_of_notMem_tsupport hy]

theorem exists_sum_cosets {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ a : F, a ≠ 0 ∧ ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
      g = ∑ r ∈ R, g r • Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) := by
  obtain ⟨a, ha, hinv⟩ := exists_invariant hg
  have hg' : IsLocallyConstant g ∧ HasCompactSupport g := hg
  have hK : IsCompact (tsupport g) := hg'.2
  have hopen : IsOpen ((scaledInt F κ a : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) :
      Set (κ → FiniteAdeleRing (𝓞 F) F)) := GlobalTheory.EvAdm.isOpen_scaledInt a
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {y | y - x ∈ scaledInt F κ a}) (fun x _ =>
    (continuous_sub_right x).continuousAt.preimage_mem_nhds
      (hopen.mem_nhds (by simp)))
  refine ⟨a, ha, (t.image (fun x => (QuotientAddGroup.mk x :
    (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a))).image Quotient.out, ?_⟩
  funext y
  have hmem : ∀ q : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a,
      y - Quotient.out q ∈ scaledInt F κ a ↔
        (QuotientAddGroup.mk y : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a) = q := by
    intro q
    have hq : (QuotientAddGroup.mk (Quotient.out q) :
        (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a) = q := Quotient.out_eq' q
    calc y - Quotient.out q ∈ scaledInt F κ a ↔ -y + Quotient.out q ∈ scaledInt F κ a := by
          rw [← (scaledInt F κ a).neg_mem_iff, neg_sub, sub_eq_neg_add]
      _ ↔ (QuotientAddGroup.mk y : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a) =
          QuotientAddGroup.mk (Quotient.out q) := QuotientAddGroup.eq.symm
      _ ↔ _ := by rw [hq]
  rw [Finset.sum_apply, Finset.sum_image (by intro q _ q' _ h; exact Quotient.out_injective h)]
  simp only [Pi.smul_apply, smul_eq_mul, Set.indicator_apply, Set.mem_ofPred_eq, hmem, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hy
  · have h1 := hinv (Quotient.out (QuotientAddGroup.mk y :
        (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a)) (y - Quotient.out (QuotientAddGroup.mk y :
        (κ → FiniteAdeleRing (𝓞 F) F) ⧸ scaledInt F κ a)) ((hmem _).2 rfl)
    simpa using h1
  · by_contra hne
    have hyK : y ∈ tsupport g := subset_tsupport g hne
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hyK)
    apply hy
    refine Finset.mem_image.2 ⟨x, hx, ?_⟩
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
    exact hyx

theorem exists_sum_finprod {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (φ : Fin m → ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ),
      (∀ k v, φ k v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ k, ∀ᶠ v in cofinite, φ k v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      g = ∑ k, c k • fun y => ∏ᶠ v, φ k v fun i => evalV F v (y i) := by
  obtain ⟨a, ha, R, hR⟩ := exists_sum_cosets hg
  choose ψ hψSB hψcof hψeq using fun r => boxS F κ a r ha
  refine ⟨R.card, fun k => g (R.equivFin.symm k), fun k => ψ (R.equivFin.symm k),
    fun k v => hψSB _ v, fun k => hψcof _, ?_⟩
  have key : ∀ r, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) =
      fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, ψ r v fun i => evalV F v (y i) := fun r => funext (hψeq r)
  calc g = ∑ r ∈ R, g r • Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) := hR
    _ = ∑ r ∈ R, g r • fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, ψ r v fun i => evalV F v (y i) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [key r]
    _ = _ := by
        rw [← Finset.sum_coe_sort R]
        exact (Equiv.sum_comp R.equivFin.symm
          (fun r : R => g r • fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, ψ r v fun i => evalV F v (y i))).symm

theorem comp_mem_adm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hev l hl
  obtain ⟨-, -, hstd, -, -⟩ := hM
  obtain ⟨-, -, hstd₁, -, -⟩ := hM₁
  obtain ⟨ei, ev, -, hev_v, hpure⟩ := hev.loc
  simp only [GlobalTheory.WeilM.adeleClass, Set.mem_ofPred_eq] at hl ⊢
  intro g hg
  obtain ⟨m, c, φ, hφ, hcof, hgeq⟩ := exists_sum_finprod hg
  have hcofM : ∀ k, ∀ᶠ v in cofinite, φ k v = M.vac v := fun k =>
    (hcof k).mp (hstd.mono fun v h1 h2 => h2.trans h1.symm)
  set H : Fin m → (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    fun k y => ∏ᶠ v, ev v (φ k v) fun i => evalV F v (y i) with hHdef
  have hH : ∀ k, H k ∈ GlobalTheory.WeilM.SB (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F) := by
    intro k
    have hSB : ∀ v : HeightOneSpectrum (𝓞 F),
        ev v (φ k v) ∈ GlobalTheory.WeilM.SB (Fin n₁ × Fin d₁ → Fv F v) := fun v => by
      rw [← (hev_v v).2]
      exact Submodule.mem_map_of_mem (hφ k v)
    have hc : ∀ᶠ v in cofinite, ev v (φ k v) =
        Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      ((hcofM k).and hstd₁).mono fun v h => by rw [h.1, (hev_v v).1, h.2]
    show IsLocallyConstant (H k) ∧ HasCompactSupport (H k)
    exact ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV (fun v => ev v (φ k v)) hSB hc,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod (fun v => ev v (φ k v)) hSB hc⟩
  choose T hT using fun k => hl (H k) (hH k)
  have hsplit : ∀ f : SchwartzMap (Fin n × Fin d → NumberField.mixedEmbedding.mixedSpace F) ℂ,
      GlobalTheory.WeilM.pureA F (⇑f) g = ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    intro f
    funext x
    rw [hgeq]
    simp only [GlobalTheory.WeilM.pureA, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm]
    rfl
  refine ⟨∑ k, c k • (T k).comp ei, fun f => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.comp_apply, hsplit f, map_sum, map_sum, ContinuousLinearMap.sum_apply]
  simp only [map_smul, smul_eq_mul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hpure f (φ k) (hφ k) (hcofM k), ← hT k (ei f)]
  congr 2

end PositivityTheory.ThKF0.GeoAdm

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.ThKF0

open Geo

theorem evUniq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
    {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {M : Model σ X W}
    {M₁ : Model σ X₁ W₁} (hψ : IsStd B.ψ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))}
    (hL : HasLag M M₁ B.ψ ι ι' I) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (he : IsEv B M M₁ ι ι' I e) (T : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (hT : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), T (M.co.rho B.ψ (incM F ι * z * (incM F ι')ᵀ) Φ) = M₁.co.rho B.ψ z (T Φ))
    (hTI : ∀ u ∈ I, ∀ Φ ∈ schA F (Fin n × Fin d), T (M.co.rho B.ψ u Φ) = T Φ)
    (aT : (LinearMap.proj 0 : Fn F n₁ d₁ →ₗ[ℂ] ℂ) ∘ₗ T ∈ (adeleClass F).adm (Fin n × Fin d)) :
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), T Φ = c • e Φ :=
  map_line lagLine hψ hL T e hT he.Heisenberg₂ hTI he.inv aT
    (GeoAdm.comp_mem_adm F E σ B _ _ _ _ _ _ _ _ M M₁ _ _ _ e hM hM₁ he _ (proj_adm F _ 0))
    (GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero F E σ B _ _ _ _ _ _ _ _ M M₁ _ _ _ e hM hM₁ he)

theorem hermitian_plane_theta_restriction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ e' : Fn F n d →ₗ[ℂ] Fn F n₁ d,
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ) = M₁.co.rho B.ψ z (e' Φ)) →
      (∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ u Φ) = e' Φ) →
      (∀ y : Fin n₁ × Fin d → AF F, (LinearMap.proj y : Fn F n₁ d →ₗ[ℂ] ℂ) ∘ₗ e' ∈ (adeleClass F).adm (Fin n × Fin d)) →
      ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e' Φ = c • e Φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he T h1 h2 h3
  exact evUniq hP.base.std hP.good hP₁.good (hasLag_X hP.base M M₁ hP.good hP₁.good hH) e he T h1 h2 (h3 0)

theorem hermitian_plane_theta_cusp_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ y : Fin n₁ × Fin d → AF F, (LinearMap.proj y : Fn F n₁ d →ₗ[ℂ] ℂ) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H i₀ i₁ M₁ om₁ r₁ s₁ hH hP₁ e he y
  exact GeoAdm.comp_mem_adm F E σ B _ _ _ _ _ _ _ _ M M₁ _ _ _ e hP.good hP₁.good he _ (proj_adm F _ y)

theorem evaluation_intertwining_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  exact GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero

theorem evaluation_intertwining_of_models : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ)
    (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e →
      ∀ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := by
  exact GeoAdm.comp_mem_adm

end PositivityTheory.ThKF0
