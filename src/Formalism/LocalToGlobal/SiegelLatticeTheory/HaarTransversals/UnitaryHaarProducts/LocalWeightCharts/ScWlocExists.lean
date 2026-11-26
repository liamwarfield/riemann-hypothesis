module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.SchurOrthogonalityRelations
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2OfHypotheses
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.AKindR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilradicalUnimodularConjInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NChartP

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2OfNilpotentChart
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.DecayR
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.UnitMulStar
noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Matrix
open scoped InnerProductSpace

namespace WlocSk.OneP

section MatAlg

variable {n : ℕ}

lemma unit_star_mul {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    uᴴ * u = 1 := by
  have := (Matrix.mem_unitaryGroup_iff').mp hu
  rwa [Matrix.star_eq_conjTranspose] at this

lemma unit_mul_star {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    u * uᴴ = 1 := by
  have := (Matrix.mem_unitaryGroup_iff).mp hu
  rwa [Matrix.star_eq_conjTranspose] at this

lemma unit_inv {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    u⁻¹ = uᴴ := Matrix.inv_eq_left_inv (unit_star_mul hu)

private theorem conj_mem_lemma {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

private theorem mem_UJset_of_mem_Kset_local_weight_charts {ε : Fin n → Bool} {u : Matrix (Fin n) (Fin n) ℂ}
    (hu : u ∈ Formalism.REAL.Kset ε) : u ∈ UJset ε := by
  obtain ⟨hU, hc⟩ := hu
  show uᴴ * Formalism.REAL.Jm ε * u = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, unit_star_mul hU, Matrix.one_mul]

private theorem conjTranspose_mem_Kset' {ε : Fin n → Bool} {u : Matrix (Fin n) (Fin n) ℂ}
    (hu : u ∈ Formalism.REAL.Kset ε) : uᴴ ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hU, hc⟩ := hu
  refine ⟨?_, ?_⟩
  · refine Matrix.mem_unitaryGroup_iff.2 ?_
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact unit_star_mul hU
  · calc uᴴ * Formalism.REAL.Jm ε = uᴴ * (Formalism.REAL.Jm ε * u) * uᴴ := by
          simp only [Matrix.mul_assoc, unit_mul_star hU, Matrix.mul_one]
      _ = uᴴ * (u * Formalism.REAL.Jm ε) * uᴴ := by rw [hc]
      _ = Formalism.REAL.Jm ε * uᴴ := by
          simp only [← Matrix.mul_assoc, unit_star_mul hU, Matrix.one_mul]

lemma conj_mem {ε : Fin n → Bool} {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Formalism.REAL.Kset ε)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : uᴴ * g * u ∈ UJset ε := by
  exact conj_mem_lemma (conj_mem_lemma (mem_UJset_of_mem_Kset_local_weight_charts (conjTranspose_mem_Kset' hu)) hg) (mem_UJset_of_mem_Kset_local_weight_charts hu)

lemma star_mem_K {ε : Fin n → Bool} {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Formalism.REAL.Kset ε) :
    uᴴ ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hU, hc⟩ := hu
  refine ⟨?_, ?_⟩
  · refine Matrix.mem_unitaryGroup_iff.2 ?_
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact unit_star_mul hU
  · calc uᴴ * Formalism.REAL.Jm ε = uᴴ * (Formalism.REAL.Jm ε * u) * uᴴ := by
          simp only [Matrix.mul_assoc, unit_mul_star hU, Matrix.mul_one]
      _ = uᴴ * (u * Formalism.REAL.Jm ε) * uᴴ := by rw [hc]
      _ = Formalism.REAL.Jm ε * uᴴ := by
          simp only [← Matrix.mul_assoc, unit_star_mul hU, Matrix.one_mul]

lemma K_mem_UJ {ε : Fin n → Bool} {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Formalism.REAL.Kset ε) :
    u ∈ UJset ε := by
  obtain ⟨hU, hJ⟩ := hu
  show uᴴ * Formalism.REAL.Jm ε * u = Formalism.REAL.Jm ε
  rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, unit_star_mul hU, Matrix.one_mul]

lemma mul_mem_UJ {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) :
    a * b ∈ UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

end MatAlg

section KTypes

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} (σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (T : H ≃ₗ[ℂ] H)

def Inter : Prop := ∀ g ∈ Formalism.REAL.Kset ε, ∀ v : H, σ' g (T v) = T (σ g v)

variable {σ σ' T}

lemma inter_symm (hT : Inter (ε := ε) σ σ' T) : Inter (ε := ε) σ' σ T.symm := by
  intro g hg v
  have := hT g hg (T.symm v)
  rw [T.apply_symm_apply] at this
  rw [this, T.symm_apply_apply]

lemma wt_map (hT : Inter (ε := ε) σ σ' T) {μ : Fin n → ℝ} {v : H}
    (hv : IsWtOn (Formalism.REAL.Kset ε) σ μ v) : IsWtOn (Formalism.REAL.Kset ε) σ' μ (T v) := by
  intro θ hθ
  rw [hT _ hθ, hv θ hθ, map_smul]

lemma stab_map (hT : Inter (ε := ε) σ σ' T) {S : Submodule ℂ H} (hS : IsKStableOn ε σ S) :
    IsKStableOn ε σ' (S.map (T : H →ₗ[ℂ] H)) := by
  intro g hg w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
  exact Submodule.mem_map.2 ⟨σ g v, hS g hg v hv, by simp [hT g hg v]⟩

lemma map_symm_map (S : Submodule ℂ H) : (S.map (T.symm : H →ₗ[ℂ] H)).map (T : H →ₗ[ℂ] H) = S := by
  ext v
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    simpa using hx
  · intro hv
    exact ⟨T.symm v, ⟨v, hv, rfl⟩, by simp⟩

lemma ktype_map (hT : Inter (ε := ε) σ σ' T) {Λ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) : IsKTypeOf ε σ' Λ (S.map (T : H →ₗ[ℂ] H)) := by
  obtain ⟨hfin, hst, hirr, ⟨v, hvS, hv0, hvw⟩, hdom⟩ := hS
  refine ⟨?_, stab_map hT hst, ?_, ?_, ?_⟩
  · haveI := hfin
    infer_instance
  · intro S' hS' hst'
    have hle : S'.map (T.symm : H →ₗ[ℂ] H) ≤ S := by
      have h1 := Submodule.map_mono (f := (T.symm : H →ₗ[ℂ] H)) hS'
      have h2 : (S.map (T : H →ₗ[ℂ] H)).map (T.symm : H →ₗ[ℂ] H) = S := by
        simpa using map_symm_map (T := T.symm) S
      rwa [h2] at h1
    rcases hirr _ hle (stab_map (inter_symm hT) hst') with h | h
    · left
      rw [← map_symm_map (T := T) S', h, Submodule.map_bot]
    · right
      rw [← map_symm_map (T := T) S', h]
  · exact ⟨T v, Submodule.mem_map_of_mem hvS, (LinearEquiv.map_ne_zero_iff T).2 hv0, wt_map hT hvw⟩
  · intro μ w hw hw0 hww
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hw
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hw0 (by simp)
    have hxw := wt_map (inter_symm hT) hww
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hxw
    exact hdom μ x hx hx0 hxw

end KTypes

section Conj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem isDS_conj (hσ : IsDS ε lam σ) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ Formalism.REAL.Kset ε) :
    IsDS ε lam (fun g => σ (uᴴ * g * u)) := by
  obtain ⟨hc, hnt, ⟨⟨h1, hmul⟩, hnorm, hcont⟩, hirr, hsq, ⟨S0, hS0⟩, hmin⟩ := hσ
  have huJ : u ∈ UJset ε := K_mem_UJ hu
  have husJ : uᴴ ∈ UJset ε := K_mem_UJ (star_mem_K hu)
  have huu : uᴴ * u = 1 := unit_star_mul hu.1
  have huu' : u * uᴴ = 1 := unit_mul_star hu.1
  have hconj : ∀ g ∈ UJset ε, uᴴ * g * u ∈ UJset ε := fun g hg => conj_mem hu hg
  have key : ∀ g ∈ UJset ε, ∀ x : H, σ (uᴴ * g * u) x = σ uᴴ (σ g (σ u x)) := by
    intro g hg x
    rw [hmul _ (mul_mem_UJ husJ hg) _ huJ, hmul _ husJ _ hg]
    rfl
  have hinv1 : ∀ x : H, σ u (σ uᴴ x) = x := by
    intro x
    have h := hmul u huJ uᴴ husJ
    rw [huu', h1] at h
    exact (congrArg (fun L : H →L[ℂ] H => L x) h).symm
  have hinv2 : ∀ x : H, σ uᴴ (σ u x) = x := by
    intro x
    have h := hmul uᴴ husJ u huJ
    rw [huu, h1] at h
    exact (congrArg (fun L : H →L[ℂ] H => L x) h).symm
  let T : H ≃ₗ[ℂ] H := LinearEquiv.ofLinear (σ uᴴ : H →ₗ[ℂ] H) (σ u : H →ₗ[ℂ] H)
    (LinearMap.ext fun x => hinv2 x) (LinearMap.ext fun x => hinv1 x)
  have hT : ∀ x, T x = σ uᴴ x := fun x => rfl
  have hInter : Inter (ε := ε) σ (fun g => σ (uᴴ * g * u)) T := by
    intro g hg x
    show σ (uᴴ * g * u) (T x) = T (σ g x)
    rw [hT, hT, key g (K_mem_UJ hg), hinv1]
  refine ⟨hc, hnt, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ⟨S0.map (T : H →ₗ[ℂ] H), ktype_map hInter hS0⟩, ?_⟩
  · show σ (uᴴ * 1 * u) = 1
    rw [Matrix.mul_one, huu, h1]
  · intro a ha b hb
    show σ (uᴴ * (a * b) * u) = σ (uᴴ * a * u) ∘L σ (uᴴ * b * u)
    rw [← hmul _ (hconj a ha) _ (hconj b hb)]
    congr 1
    rw [show uᴴ * a * u * (uᴴ * b * u) = uᴴ * a * (u * uᴴ) * b * u by simp only [Matrix.mul_assoc],
      huu', Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  · intro g hg x
    exact hnorm _ (hconj g hg) x
  · intro x
    have hc' : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => uᴴ * g * u :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact (hcont x).comp hc'.continuousOn (fun g hg => hconj g hg)
  · intro S hS hst
    apply hirr S hS
    intro h hh x hx
    have hm := conj_mem (star_mem_K hu) hh
    rw [Matrix.conjTranspose_conjTranspose] at hm
    have hx' := hst _ hm x hx
    have e : uᴴ * (u * h * uᴴ) * u = h := by
      rw [show uᴴ * (u * h * uᴴ) * u = (uᴴ * u) * h * (uᴴ * u) by simp only [Matrix.mul_assoc],
        huu, Matrix.one_mul, Matrix.mul_one]
    dsimp only at hx'
    rwa [e] at hx'
  · intro v w
    have hsq' := hsq (σ u v) (σ u w)
    let Lu : H →ₗᵢ[ℂ] H := ⟨(σ u : H →ₗ[ℂ] H), fun x => hnorm u huJ x⟩
    have hfun : coefOn (ε := ε) (fun g => σ (uᴴ * g * u)) v w = coefOn (ε := ε) σ (σ u v) (σ u w) := by
      funext g
      have hg : umat g ∈ UJset ε := g.2
      show ⟪w, σ (uᴴ * umat g * u) v⟫_ℂ = ⟪σ u w, σ (umat g) (σ u v)⟫_ℂ
      rw [key _ hg]
      have h2 := Lu.inner_map_map w (σ uᴴ (σ (umat g) (σ u v)))
      have h3 : Lu (σ uᴴ (σ (umat g) (σ u v))) = σ (umat g) (σ u v) := hinv1 _
      rw [h3] at h2
      exact h2.symm
    rw [hfun]
    exact hsq'
  · intro μ S hS
    exact hmin μ _ (ktype_map (inter_symm hInter) hS)

end Conj

section Cayley

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

lemma cayley_K {P P' : Mat k r} (hP : IsCayleyU k r ε P) (hP' : IsCayleyU k r ε P') :
    P' * Pᴴ ∈ Formalism.REAL.Kset ε := by
  obtain ⟨⟨_, hP⟩, hU⟩ := hP
  obtain ⟨⟨_, hP'⟩, hU'⟩ := hP'
  have eJ : Formalism.REAL.Jm ε = P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by
    rw [← hP, show P * (Pᴴ * Formalism.REAL.Jm ε * P) * Pᴴ = (P * Pᴴ) * Formalism.REAL.Jm ε * (P * Pᴴ) by
      simp only [Matrix.mul_assoc], unit_mul_star hU, Matrix.one_mul, Matrix.mul_one]
  have eJ' : Formalism.REAL.Jm ε = P' * Formalism.QuantumDeterminants.Hpk k r * P'ᴴ := by
    rw [← hP', show P' * (P'ᴴ * Formalism.REAL.Jm ε * P') * P'ᴴ = (P' * P'ᴴ) * Formalism.REAL.Jm ε * (P' * P'ᴴ) by
      simp only [Matrix.mul_assoc], unit_mul_star hU', Matrix.one_mul, Matrix.mul_one]
  have hPs : Pᴴ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
    refine Matrix.mem_unitaryGroup_iff.2 ?_
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact unit_star_mul hU
  refine ⟨Submonoid.mul_mem _ hU' hPs, ?_⟩
  have e1 : P' * Pᴴ * Formalism.REAL.Jm ε = P' * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by
    conv_lhs => rw [eJ]
    rw [show P' * Pᴴ * (P * Formalism.QuantumDeterminants.Hpk k r * Pᴴ) = P' * (Pᴴ * P) * Formalism.QuantumDeterminants.Hpk k r * Pᴴ by
      simp only [Matrix.mul_assoc], unit_star_mul hU, Matrix.mul_one]
  have e2 : Formalism.REAL.Jm ε * (P' * Pᴴ) = P' * Formalism.QuantumDeterminants.Hpk k r * Pᴴ := by
    conv_lhs => rw [eJ']
    rw [show P' * Formalism.QuantumDeterminants.Hpk k r * P'ᴴ * (P' * Pᴴ) = P' * Formalism.QuantumDeterminants.Hpk k r * (P'ᴴ * P') * Pᴴ by
      simp only [Matrix.mul_assoc], unit_star_mul hU', Matrix.mul_one]
  rw [e1, e2]

theorem isDS_cayley {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mat k r → (H →L[ℂ] H)} {P P' : Mat k r} (hP : IsCayleyU k r ε P) (hP' : IsCayleyU k r ε P')
    (hσ : IsDS ε lam (fun g => σ (P⁻¹ * g * P))) : IsDS ε lam (fun g => σ (P'⁻¹ * g * P')) := by
  have hK := cayley_K hP hP'
  have hU := hP.2
  have hU' := hP'.2
  have h := isDS_conj hσ hK
  have hfun : (fun g => σ (P⁻¹ * ((P' * Pᴴ)ᴴ * g * (P' * Pᴴ)) * P)) = (fun g => σ (P'⁻¹ * g * P')) := by
    funext g
    congr 1
    rw [unit_inv hU, unit_inv hU', Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      show Pᴴ * (P * P'ᴴ * g * (P' * Pᴴ)) * P = (Pᴴ * P) * (P'ᴴ * g * P') * (Pᴴ * P) by
        simp only [Matrix.mul_assoc],
      unit_star_mul hU, Matrix.one_mul, Matrix.mul_one]
  rw [← hfun]
  exact h

end Cayley

end WlocSk.OneP

section Check
end Check
end
end

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas Matrix
open scoped InnerProductSpace ENNReal

namespace WlocSk.DecayR

lemma opn_conj {n : ℕ} {P g : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Formalism.L2.SG.WuDecay.opn (P⁻¹ * g * P) = Formalism.L2.SG.WuDecay.opn g := by
  unfold Formalism.L2.SG.WuDecay.opn
  have h1 : star P * P = 1 := by
    first
      | exact Unitary.star_mul_self_of_mem hP
      | exact unitary.star_mul_self_of_mem hP
  have h2 : P * star P = 1 := by
    first
      | exact Unitary.mul_star_self_of_mem hP
      | exact unitary.mul_star_self_of_mem hP
  have hPinv : P⁻¹ = star P := Matrix.inv_eq_left_inv h1
  have hU1 : star (Matrix.toEuclideanCLM (𝕜 := ℂ) P) * Matrix.toEuclideanCLM (𝕜 := ℂ) P = 1 := by
    rw [← map_star, ← map_mul, h1, map_one]
  have hU2 : Matrix.toEuclideanCLM (𝕜 := ℂ) P * star (Matrix.toEuclideanCLM (𝕜 := ℂ) P) = 1 := by
    rw [← map_star, ← map_mul, h2, map_one]
  have hU : Matrix.toEuclideanCLM (𝕜 := ℂ) P ∈ unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    ⟨hU1, hU2⟩
  have hUs : star (Matrix.toEuclideanCLM (𝕜 := ℂ) P) ∈
      unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := by
    refine ⟨?_, ?_⟩
    · rw [star_star]
      exact hU2
    · rw [star_star]
      exact hU1
  rw [hPinv, map_mul, map_mul, map_star, CStarRing.norm_mul_mem_unitary _ hU,
    CStarRing.norm_mem_unitary_mul _ hUs]

variable {k r : ℕ}

lemma transport {ε : Fin (2 * r + k + 1) → Bool} {P' : Mat k r} (hP' : IsCayleyU k r ε P')
    {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : IsHaarOn (Gr k r) μG) :
    ∃ cc : ℝ≥0∞, cc ≠ 0 ∧ cc ≠ ⊤ ∧ μG = (cc • PI.UpqRep.muG ε).map (Port.conjPrime₂ ε P') := by
  have : SigmaFinite μG := hG.1
  have hPJ' : P'ᴴ * PI.UpqRep.Jm ε * P' = PI.UpqRep.Hpk k r := hP'.1.2
  have hconc : μG {x | Matrix.of x ∉ PI.UpqRep.UH (P'ᴴ * PI.UpqRep.Jm ε * P')} = 0 := by
    rw [hPJ']; exact hG.2.2.1
  have hinv : ∀ s ∈ PI.UpqRep.UH (P'ᴴ * PI.UpqRep.Jm ε * P'),
      μG.map (fun x => Matrix.of.symm (s * Matrix.of x)) = μG := by
    rw [hPJ']; intro s hs; exact hG.2.2.2 s hs
  exact Port.haar_transport ε P' hP'.1.1 μG hG.2.1 hconc hinv

theorem decay_estimate : WlocSk.Decay := by
  intro hCW k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp
  obtain ⟨hS, hσ, _, hw, hG, _⟩ := hyp
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨P', hP', hLow⟩ := hw
  have hDS' := OneP.isDS_cayley hP hP' hDS
  obtain ⟨_, _, _, _, _, _, hHC, _, _, hGap⟩ := hS
  have hC := hCW k r v b hHC hGap H (fun g => σ (P'⁻¹ * g * P')) hDS' w hLow
  obtain ⟨cc, _, hctop, hμ⟩ := transport hP' hG
  have hE := Port.conjP_measurableEmbedding (eps48 k r) P' hP'.1.1
  rw [hμ, hE.lintegral_map, lintegral_smul_measure]
  refine ENNReal.mul_lt_top hctop.lt_top (lt_of_eq_of_lt (lintegral_congr fun g => ?_) hC)
  show ‖⟪w, σ (P'⁻¹ * uMat g * P') w⟫_ℂ‖ₑ *
      ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (P'⁻¹ * uMat g * P') ^ N1H k r) =
    ‖⟪w, σ (P'⁻¹ * uMat g * P') w⟫_ℂ‖ₑ *
      ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (uMat g)‖ ^
        (4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ))))
  rw [opn_conj hP'.2]
  rfl

theorem reproducing_formula_holds : WlocSk.ReprodG := by
  intro hR k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp
  obtain ⟨_, hσ, _, hw, hG, _⟩ := hyp
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨P', hP', hLow⟩ := hw
  have hDS' := OneP.isDS_cayley hP hP' hDS
  obtain ⟨α', Ω', a', hΩc, hαm, hαs, hαb, hαi, hαe⟩ :=
    hR _ (eps48 k r) (lam48 k r v b) H (fun g => σ (P'⁻¹ * g * P')) hDS' w hLow.2
  obtain ⟨cc, hc0, hctop, hμ⟩ := transport hP' hG
  have hE := Port.conjP_measurableEmbedding (eps48 k r) P' hP'.1.1
  have hct : 0 < cc.toReal := ENNReal.toReal_pos hc0 hctop
  set ψ := Port.conjPrime₂ (eps48 k r) P' with hψ
  set f : Formalism.REAL.UJ (eps48 k r) → ℂ := fun g => (cc.toReal⁻¹ : ℝ) • α' g with hf
  set α : Mat k r → ℂ := fun y => Function.extend ψ f (fun _ => 0) (Matrix.of.symm y) with hα
  have hαψ : ∀ g, α (Matrix.of (ψ g)) = f g := fun g => hE.injective.extend_apply _ _ g
  have hcase : ∀ y : Mat k r, α y ≠ 0 → ∃ g, ψ g = Matrix.of.symm y ∧ α y = f g := by
    intro y hy
    by_cases h : ∃ g, ψ g = Matrix.of.symm y
    · obtain ⟨g, hg⟩ := h
      refine ⟨g, hg, ?_⟩
      show Function.extend ψ f (fun _ => 0) (Matrix.of.symm y) = f g
      rw [← hg]; exact hE.injective.extend_apply _ _ g
    · exact absurd (Function.extend_apply' f (fun _ => (0 : ℂ)) _ h) hy
  have hcont : Continuous fun g : Formalism.REAL.UJ (eps48 k r) => P'⁻¹ * uMat g * P' :=
    (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
      continuous_const
  have hinv := OneP.unit_inv hP'.2
  have h1 := OneP.unit_star_mul hP'.2
  have h2 := OneP.unit_mul_star hP'.2
  refine ⟨α, (fun g => P'⁻¹ * uMat g * P') '' Ω', cc.toReal⁻¹ * max a' 0, hΩc.image hcont, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rintro _ ⟨g, _, rfl⟩
    have hg : (uMat g)ᴴ * Formalism.REAL.Jm (eps48 k r) * uMat g = Formalism.REAL.Jm (eps48 k r) := g.2
    show (P'⁻¹ * uMat g * P')ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P'⁻¹ * uMat g * P') = Formalism.QuantumDeterminants.Hpk k r
    rw [← hP'.1.2, hinv]
    calc (P'ᴴ * uMat g * P')ᴴ * (P'ᴴ * Formalism.REAL.Jm (eps48 k r) * P') * (P'ᴴ * uMat g * P')
        = P'ᴴ * (uMat g)ᴴ * (P' * P'ᴴ) * Formalism.REAL.Jm (eps48 k r) * (P' * P'ᴴ) * uMat g * P' := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = P'ᴴ * ((uMat g)ᴴ * Formalism.REAL.Jm (eps48 k r) * uMat g) * P' := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = P'ᴴ * Formalism.REAL.Jm (eps48 k r) * P' := by rw [hg]
  · have hfm : Measurable f := hαm.const_smul (cc.toReal⁻¹ : ℝ)
    exact hE.measurable_extend hfm measurable_const
  · intro y hy
    obtain ⟨g, hg, hyg⟩ := hcase y hy
    have hg0 : α' g ≠ 0 := by
      intro h0; apply hy; rw [hyg, hf]; simp [h0]
    refine ⟨g, hαs g hg0, ?_⟩
    rw [← Matrix.of.apply_symm_apply y, ← hg]
    rfl
  · intro y
    have hcn : 0 ≤ cc.toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
    by_cases hy : α y = 0
    · rw [hy, norm_zero]; exact mul_nonneg hcn (le_max_right _ _)
    · obtain ⟨g, _, hyg⟩ := hcase y hy
      rw [hyg, hf]
      simp only
      rw [norm_smul, Real.norm_of_nonneg hcn]
      exact mul_le_mul_of_nonneg_left ((hαb g).trans (le_max_left _ _)) hcn
  · have hfun : (fun x : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of x) • σ (Matrix.of x) w) ∘ ψ =
        fun g => (cc.toReal⁻¹ : ℝ) • (α' g • σ (P'⁻¹ * uMat g * P') w) := by
      funext g
      simp only [Function.comp]
      rw [hαψ, hf, smul_assoc]
      rfl
    rw [hμ, hE.integrable_map_iff, hfun]
    exact (hαi.smul_measure hctop).smul _
  · have hfun : (fun x : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of x) • σ (Matrix.of x) w) ∘ ψ =
        fun g => (cc.toReal⁻¹ : ℝ) • (α' g • σ (P'⁻¹ * uMat g * P') w) := by
      funext g
      simp only [Function.comp]
      rw [hαψ, hf, smul_assoc]
      rfl
    rw [hμ, hE.integral_map, integral_smul_measure]
    have hpt : ∀ x, α (Matrix.of (ψ x)) • σ (Matrix.of (ψ x)) w =
        (cc.toReal⁻¹ : ℝ) • (α' x • σ (P'⁻¹ * uMat x * P') w) := fun x => congrFun hfun x
    simp_rw [hpt]
    rw [integral_smul]
    have he : ∫ g, α' g • σ (P'⁻¹ * uMat g * P') w ∂(PI.UpqRep.muG (eps48 k r)) = w := hαe
    rw [he, smul_smul, mul_inv_cancel₀ hct.ne', one_smul]

end WlocSk.DecayR

section Check
end Check
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilradicalHaarUnique
noncomputable section

open MeasureTheory Formalism.MainNotions.S
open scoped ENNReal

namespace WlocSk

theorem nilradical_haar_unique : NUniq := by
  intro k r μ μ' hμ hμ'
  obtain ⟨c, hc0, hct, hc⟩ := HM.n_unique μ hμ
  obtain ⟨c', hc0', hct', hc'⟩ := HM.n_unique μ' hμ'
  refine ⟨c / c', ENNReal.div_ne_top hct hc0', ?_⟩
  rw [hc, hc', smul_smul, ENNReal.div_mul_cancel hc0' hct']

end WlocSk
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ANonzeroOf
noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas
open scoped ENNReal InnerProductSpace

namespace WlocSk.ANz

variable {k r : ℕ}

theorem haarG_pos {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : IsHaarOn (Gr k r) μG) {U : Set (Mat k r)}
    (hU : IsOpen U) {x : Mat k r} (hxU : x ∈ U) (hxG : x ∈ Gr k r) :
    0 < μG {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ U ∩ Gr k r} := by
  obtain ⟨c, hc0, -, hμeq⟩ := WlocSk.HM.haar_unique (Gr k r) WlocSk.HM.uh_clsub μG hμ
  have hVm : MeasurableSet {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ U ∩ Gr k r} :=
    (hU.preimage WlocSk.Grp.continuous_of).measurableSet.inter
      (WlocSk.Grp.isClosed_Gr.preimage WlocSk.Grp.continuous_of).measurableSet
  have hvt : Continuous (WlocSk.HM.Grp.vt :
      WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub → Formalism.QuantumDeterminants.Mt k r) := WlocSk.HM.Grp.embt.continuous
  have hO : IsOpen ((fun a => Matrix.of (WlocSk.HM.Grp.vt a)) ⁻¹' U :
      Set (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)) :=
    hU.preimage (WlocSk.Grp.continuous_of.comp hvt)
  have hne : ((fun a => Matrix.of (WlocSk.HM.Grp.vt a)) ⁻¹' U :
      Set (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)).Nonempty :=
    ⟨WlocSk.HM.Grp.mk x hxG, hxU⟩
  have hpos := hO.measure_pos (Measure.haar : Measure (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)) hne
  rw [hμeq, Measure.smul_apply, smul_eq_mul, WlocSk.HM.hmeas, Measure.map_apply hvt.measurable hVm]
  refine ENNReal.mul_pos hc0 (ne_of_gt (lt_of_lt_of_le hpos (measure_mono ?_)))
  intro a ha
  exact ⟨ha, WlocSk.HM.Grp.mem a⟩

theorem aNonzero_of (hSG : SGrp) (hPU : PiUnit) (hSP : SProd) (hAE : AEquiv) (hAC : ACont) :
    ANonzero := by
  intro hNV k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp hR hCW
  obtain ⟨hset, hDS, hHC, hLU, hG, -, -, hW, hN, -, -⟩ := id hyp
  obtain ⟨hk1, hev, hz, hT, hc, hu, hl, hI, hH2, hGB⟩ := hset
  have hk2 : 2 ≤ k := by obtain ⟨m, hm⟩ := hev; omega
  obtain ⟨x, x₀, hx, hx₀, hne⟩ :=
    hNV k r z c u v b hk2 hev hz hT hc hu hl hI hH2 hGB H σ hDS Vp π hHC w hLU μW μN hW hN
  have hFi : Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹) (μW.prod μN) := by
    by_contra hni
    exact hne (integral_undef hni)
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Vp, (∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹ ∂(μW.prod μN)) ξ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (ContinuousLinearMap.ext hall)
  rw [ContinuousLinearMap.integral_apply hFi] at hξ
  set A := Af z c σ π μW μN w x₀ ξ with hAdef
  have hAx : A x ≠ 0 := hξ
  have hcont : ContinuousOn A (Gr k r) :=
    hAC k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  have hequiv : IsSPsiEquiv z (psiGen k r z c) π A :=
    hAE k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  obtain ⟨hWG, hNG, -, hNg, -⟩ := hSG k r z c hz hT
  have hπ := (hPU k r z u Vp π hz hT hHC).2

  have hApos : 0 < ‖A x‖ := norm_pos_iff.mpr hAx
  obtain ⟨ε, hε, hεlt⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < ‖A x‖ := ⟨‖A x‖ / 2, half_pos hApos, half_lt_self hApos⟩
  have hevn : ∀ᶠ y in nhdsWithin x (Gr k r), ε < ‖A y‖ :=
    (hcont x hx).norm.eventually (lt_mem_nhds hεlt)
  obtain ⟨U, hUo, hxU, hUsub⟩ := mem_nhdsWithin.mp hevn

  set V : Set (Formalism.QuantumDeterminants.Mt k r) := {y | Matrix.of y ∈ U ∩ Gr k r} with hVdef
  have hVm : MeasurableSet V :=
    (hUo.preimage WlocSk.Grp.continuous_of).measurableSet.inter
      (WlocSk.Grp.isClosed_Gr.preimage WlocSk.Grp.continuous_of).measurableSet
  have hμV : 0 < μG V := haarG_pos hG hUo hxU hx

  obtain ⟨cS, hcS0, -, hunf⟩ := unfold_of hSP hyp
  have hfm : Measurable (V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)) := measurable_one.indicator hVm
  have := hW.1
  have := hN.1
  set g : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ∫⁻ p, V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
      (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) with hgdef
  have hU' : ∫⁻ x, g x ∂ν = cS * μG V := by
    have h := hunf _ hfm
    rw [lintegral_indicator_one hVm] at h
    exact h
  have hjoint : Measurable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (fun i j => (Matrix.of (mulP q.2) * Matrix.of q.1) i j)) := by
    refine hfm.comp (Continuous.measurable ?_)
    exact (WlocSk.Grp.continuous_of.comp (continuous_mulP.comp continuous_snd)).matrix_mul
      (WlocSk.Grp.continuous_of.comp continuous_fst)
  have hgm : Measurable g := hjoint.lintegral_prod_right'
  set P : Set (Formalism.QuantumDeterminants.Mt k r) := {x | 0 < g x} with hPdef
  have hPm : MeasurableSet P := measurableSet_lt measurable_const hgm
  have hPpos : ν P ≠ 0 := by
    intro h0
    have hae : ∀ᵐ x ∂ν, g x = 0 := by
      refine ae_iff.mpr (measure_mono_null (fun x hx => ?_) h0)
      exact pos_iff_ne_zero.mpr hx
    have h1 : ∫⁻ x, g x ∂ν = 0 := by rw [lintegral_congr_ae hae, lintegral_zero]
    rw [h1] at hU'
    exact (ENNReal.mul_pos hcS0 hμV.ne').ne' hU'.symm

  have hTae : ∀ᵐ p ∂(μW.prod μN),
      Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
    have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
      Measure.quasiMeasurePreserving_fst.ae (ae_iff.mpr hW.2.2.1)
    have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
      Measure.quasiMeasurePreserving_snd.ae (ae_iff.mpr hN.2.2.1)
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨hp1, hp2⟩

  have key : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ Gr k r → 0 < g x → ε < ‖A (Matrix.of x)‖ := by
    intro x hxG hgx
    by_contra hle
    apply hgx.ne'
    have hae : ∀ᵐ p ∂(μW.prod μN), V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
        (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) = 0 := by
      filter_upwards [hTae] with p hp
      apply Set.indicator_of_notMem
      intro hpV
      have h1 : ε < ‖A (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ := hUsub hpV
      have h2 : ‖A (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ = ‖A (Matrix.of x)‖ := by
        rw [hequiv _ hp.1 _ hp.2 _ hxG, norm_smul, (hNg _ hp.2 _ hp.2).2.2.2.2, hπ _ hp.1, one_mul]
      exact hle (h2 ▸ h1)
    show ∫⁻ p, V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
        (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) = 0
    rw [lintegral_congr_ae hae, lintegral_zero]
  have hνG : ∀ᵐ x ∂ν, Matrix.of x ∈ Gr k r := ae_iff.mpr (nu_conc_of hSG hyp)
  have hlow : ∀ᵐ x ∂ν, P.indicator (fun _ => ENNReal.ofReal ε ^ 2) x ≤
      (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [hνG] with x hxG
    by_cases hxP : x ∈ P
    · rw [Set.indicator_of_mem hxP]
      have hb : ENNReal.ofReal ε ≤ (‖A (Matrix.of x)‖₊ : ℝ≥0∞) := by
        refine ENNReal.ofReal_le_of_le_toReal ?_
        rw [ENNReal.coe_toReal, coe_nnnorm]
        exact (key x hxG hxP).le
      gcongr
    · rw [Set.indicator_of_notMem hxP]
      exact bot_le
  refine ⟨x₀, hx₀, ξ, fun hzero => ?_⟩
  have hmono : ∫⁻ x, P.indicator (fun _ => ENNReal.ofReal ε ^ 2) x ∂ν ≤
      ∫⁻ x, (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν := lintegral_mono_ae hlow
  have hz' : ∫⁻ x, (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν = 0 := hzero
  rw [lintegral_indicator_const hPm, hz'] at hmono
  have hne0 : ENNReal.ofReal ε ^ 2 * ν P ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hε).ne') hPpos
  exact hne0 (le_zero_iff.mp hmono)

end WlocSk.ANz
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.SigmaDecomposition
noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Matrix
open scoped InnerProductSpace

namespace WlocSk

section Cayley

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

lemma cay_inv_mul {P : Mat k r} (hP : IsUnit P) : P⁻¹ * P = 1 :=
  Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP)

lemma cay_mul_inv {P : Mat k r} (hP : IsUnit P) : P * P⁻¹ = 1 :=
  Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP)

lemma cay_mem {P : Mat k r} (hP : IsCayley k r ε P) {g : Mat k r} (hg : g ∈ Gr k r) :
    P * g * P⁻¹ ∈ UJset ε := by
  have h2 := cay_mul_inv hP.1
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  rw [← hP.2] at hg'
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hg']
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h2]; simp

lemma cay_back {P : Mat k r} (hP : IsUnit P) (g : Mat k r) : P⁻¹ * (P * g * P⁻¹) * P = g := by
  have h1 := cay_inv_mul hP
  have h2 := cay_mul_inv hP
  calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

end Cayley

theorem sigma_decomposition : SigmaG := by
  intro k r ε lam H _ _ σ hσ
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hDS.2.2.1
  have hPu := hP.1.1
  have hσ' : ∀ g, σ g = σ (P⁻¹ * (P * g * P⁻¹) * P) := fun g => by rw [cay_back hPu]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have := h1
    simp only [Matrix.mul_one, cay_inv_mul hPu] at this
    exact this
  · intro a ha b hb
    have hab : P * (a * b) * P⁻¹ = P * a * P⁻¹ * (P * b * P⁻¹) := by
      calc P * (a * b) * P⁻¹ = P * a * (P⁻¹ * P) * b * P⁻¹ := by
            rw [cay_inv_mul hPu]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = P * a * P⁻¹ * (P * b * P⁻¹) := by simp only [Matrix.mul_assoc]
    rw [hσ' (a * b), hab]
    have := hmul _ (cay_mem hP.1 ha) _ (cay_mem hP.1 hb)
    simp only at this
    rw [this, cay_back hPu, cay_back hPu]
  · intro g hg v
    rw [hσ' g]
    exact hiso _ (cay_mem hP.1 hg) v
  · intro v
    have hc : Continuous fun g : Mat k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hcont v).comp hc.continuousOn (fun g hg => cay_mem hP.1 hg)
    refine this.congr (fun g _ => ?_)
    simp only [Function.comp]
    rw [cay_back hPu]

end WlocSk
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.L2SGWfEqOne
noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas Matrix
open scoped InnerProductSpace ENNReal

namespace WlocSk

section Scale

variable {k r : ℕ} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

lemma rconv_smul (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) (e : Mat k r → ℂ) (A : Mat k r → Vp) (cc : ℂ)
    (x : Mat k r) : rconv μ e (fun g => cc • A g) x = cc • rconv μ e A x := by
  unfold rconv
  simp_rw [smul_comm (e _) cc]
  exact integral_smul cc _

lemma integrable_smul_fun (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) (e : Mat k r → ℂ) (A : Mat k r → Vp) (cc : ℂ)
    (x : Mat k r) (h : Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => e (Matrix.of g) • A (x * Matrix.of g)) μ) :
    Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => e (Matrix.of g) • (fun y => cc • A y) (x * Matrix.of g)) μ := by
  simp_rw [smul_comm (e _) cc]
  exact h.smul cc

lemma l2SG_const_smul (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : Mat k r → Vp) (cc : ℂ) :
    l2SG ν (fun g => cc • A g) = (‖cc‖₊ : ℝ≥0∞) ^ 2 * l2SG ν A := by
  unfold l2SG
  rw [← lintegral_const_mul' _ _ (by simp)]
  congr 1
  funext x
  rw [nnnorm_smul, ENNReal.coe_mul, mul_pow]

lemma l2SG_Wf_eq_one (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : Mat k r → Vp) (h0 : l2SG ν A ≠ 0)
    (h1 : l2SG ν A < ⊤) : l2SG ν (Wf ν A) = 1 := by
  have hW : Wf ν A = fun g => (((Real.sqrt (l2SG ν A).toReal)⁻¹ : ℝ) : ℂ) • A g := by
    funext g; unfold Wf; congr 1; push_cast; rfl
  rw [hW, l2SG_const_smul]
  set t := (l2SG ν A).toReal with ht_def
  have ht : 0 < t := ENNReal.toReal_pos h0 h1.ne
  have hA : l2SG ν A = ENNReal.ofReal t := (ENNReal.ofReal_toReal h1.ne).symm
  have hn : (‖(((Real.sqrt t)⁻¹ : ℝ) : ℂ)‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal t⁻¹ := by
    rw [ENNReal.ofReal, ← ENNReal.coe_pow]
    congr 1
    apply NNReal.coe_injective
    rw [NNReal.coe_pow, coe_nnnorm, Real.coe_toNNReal _ (inv_nonneg.mpr ht.le), Complex.norm_real,
      Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt ht.le]
  rw [hn, hA, ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le), inv_mul_cancel₀ ht.ne', ENNReal.ofReal_one]

lemma lint_smul (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : Mat k r → Vp) (cc : ℂ) (f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
    (h : ∫⁻ x, ‖A (Matrix.of x)‖ₑ * f x ∂ν < ⊤) :
    ∫⁻ x, ‖(fun g => cc • A g) (Matrix.of x)‖ₑ * f x ∂ν < ⊤ := by
  simp_rw [enorm_smul, mul_assoc]
  rw [lintegral_const_mul' _ _ enorm_ne_top]
  exact ENNReal.mul_lt_top enorm_lt_top h

end Scale

def WlocShape : Prop :=
  BesselNVGap → CoefWeightedLoc → ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μG μS ν : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r),
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS →
    IsQuotMeas μG μS ν →
  ∃ W : Mat k r → Vp, (ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) ∧ IsSPsiEquiv z (psiGen k r z c) π W ∧
    (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x) ∧
    ∫⁻ x, ‖W (Matrix.of x)‖ₑ ∂ν < ⊤ ∧ l2SG ν W = 1 ∧
    ∫⁻ x, ‖W (Matrix.of x)‖ₑ * ENNReal.ofReal (nuH k r z (Matrix.of x) ^ N1H k r) ∂ν < ⊤ ∧
    ∃ (α : Mat k r → ℂ) (Ω : Set (Mat k r)) (a : ℝ), IsCompact Ω ∧ (1 : Mat k r) ∈ Ω ∧
      Ω ⊆ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
      Measurable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g)) ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g) • W (x * Matrix.of g)) μG ∧
        rconv μG α W x = W x) ∧
  ∃ (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (cc : ℂ) (x₀ : Mat k r) (ξ : Vp),
    IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW ∧ IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN ∧
    x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    ∀ x, W x = cc • B0 z c σ π μW μN (σ x₀ w) ξ (σ x w)

theorem scWlocShape_of (hWN : HaarWN) (hEq : AEquiv) (hC : ACont) (hK : AKind) (hRp : AReprod)
    (hL : WavePacketL1L2) (hWt : AWeighted) (hNz : ANonzero) (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) :
    WlocShape := by
  intro hBNV hCW k r z c u v b hS H _ _ _ σ hσ Vp _ _ _ π hπ w hw μG μS ν hG hSμ hQ
  obtain ⟨μW, μN, hW, hN, hWf, hNc⟩ := hWN k r z hS.2.2.1 hS.2.2.2.1
  have hyp : Hyp k r z c u v b σ π w μG μS ν μW μN :=
    ⟨hS, hσ, hπ, hw, hG, hSμ, hQ, hW, hN, hWf, hNc⟩
  obtain ⟨x₀, hx₀, ξ, hne⟩ := hNz hBNV k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW
  have hL' := hL k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  set A := Af z c σ π μW μN w x₀ ξ with hA_def
  set cc : ℂ := (((Real.sqrt (l2SG ν A).toReal)⁻¹ : ℝ) : ℂ) with hcc
  have hW' : Wf ν A = fun g => cc • A g := by
    funext g; unfold Wf; congr 1; rw [hcc]; push_cast; rfl
  refine ⟨Wf ν A, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, μW, μN, cc, x₀, ξ, hW, hN, hx₀, fun x => by rw [hW']; rfl⟩
  · rw [hW']
    exact (hC k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ).const_smul cc
  · intro h hh m hm g hg
    rw [hW']
    have := hEq k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ h hh m hm g hg
    change cc • Af z c σ π μW μN w x₀ ξ (h * m * g) =
      psiGen k r z c m • (π h) (cc • Af z c σ π μW μN w x₀ ξ g)
    rw [this, smul_comm cc (psiGen k r z c m), map_smul]
  · intro x hx
    obtain ⟨hi, he⟩ := hK k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ x hx
    rw [hW']
    exact ⟨integrable_smul_fun μG _ A cc x hi, by rw [rconv_smul, he]⟩
  · rw [hW']
    have := lint_smul ν A cc (fun _ => 1) (by simpa using hL'.1)
    simpa using this
  · exact l2SG_Wf_eq_one ν A hne hL'.2
  · rw [hW']
    exact lint_smul ν A cc _ (hWt k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ)
  · obtain ⟨α, Ω, a, hΩ, h1, hΩG, hαm, hα0, hαa, hα⟩ :=
      hRp k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
    refine ⟨α, Ω, a, hΩ, h1, hΩG, hαm, hα0, hαa, fun x hx => ?_⟩
    obtain ⟨hi, he⟩ := hα x hx
    rw [hW']
    exact ⟨integrable_smul_fun μG _ A cc x hi, by rw [rconv_smul, he]⟩

theorem scWlocExists_of (hWN : HaarWN) (hEq : AEquiv) (hC : ACont) (hK : AKind) (hRp : AReprod)
    (hL : WavePacketL1L2) (hWt : AWeighted) (hNz : ANonzero) (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) :
    WlocExists := by
  intro hBNV hCW k r z c u v b hS H _ _ _ σ hσ Vp _ _ _ π hπ w hw μG μS ν hG hSμ hQ
  obtain ⟨W, hWc, _⟩ := scWlocShape_of hWN hEq hC hK hRp hL hWt hNz hR hBNV hCW k r z c u v b hS H σ hσ
    Vp π hπ w hw μG μS ν hG hSμ hQ
  exact ⟨W, hWc⟩

end WlocSk
end
end

noncomputable section

open Formalism.L2.SG.SplitPrimeNormLemmas

namespace WlocSk

theorem unipotent_set_compact : PtD.UWComp := fun _ _ z hz hT => HM.compactW z hz hT

theorem nIntDecay_of_chart (hNC : NChart) : NIntDecay := nIntDecay_of (nCoordHaar_of hNC nilradical_haar_unique)

theorem aInt_of_chart (hNC : NChart) : AInt :=
  PtD.wave_packet_integrable sigma_decomposition DecayR.decay_estimate DecayR.reproducing_formula_holds subgroup_hypothesis_holds representation_unitary
    (nIntDecay_of_chart hNC) unipotent_set_compact

theorem aCont_of_chart (hNC : NChart) : ACont :=
  PtD.wave_packet_continuous sigma_decomposition DecayR.decay_estimate DecayR.reproducing_formula_holds subgroup_hypothesis_holds representation_unitary
    (nIntDecay_of_chart hNC) unipotent_set_compact

theorem aBound_of_chart (hNC : NChart) : ABound :=
  PtD.aBound_of sigma_decomposition DecayR.decay_estimate DecayR.reproducing_formula_holds subgroup_hypothesis_holds representation_unitary
    (nIntDecay_of_chart hNC) unipotent_set_compact

theorem aEquiv_of_charts (hNC : NChart) (hWR : WRightInv) (hNU : NUnimod) : AEquiv :=
  aEquiv_of subgroup_hypothesis_holds representation_unitary sigma_decomposition hWR hNU (aInt_of_chart hNC)

theorem wave_packet_weighted_integrable : AWeighted :=
  AQ.aWeighted_of subgroup_hypothesis_holds representation_unitary sigma_decomposition product_decomposition_holds DecayR.decay_estimate

theorem aKind_of_chart (hNC : NChart) : AKind :=
  AK.aKind_of sigma_decomposition subgroup_hypothesis_holds (aBound_of_chart hNC) DecayR.decay_estimate Port.schur_orthogonality_relations

theorem aReprod_of_chart (hNC : NChart) : AReprod :=
  AK.aReprod_of sigma_decomposition subgroup_hypothesis_holds (aBound_of_chart hNC) DecayR.reproducing_formula_holds

theorem wave_packet_l1_l2_of_nilpotent_chart (hNC : NChart) (hWR : WRightInv) : WavePacketL1L2 :=
  AQ.wave_packet_l1_l2_of_hypotheses subgroup_hypothesis_holds representation_unitary sigma_decomposition product_decomposition_holds DecayR.decay_estimate hWR nilradical_unimodular_conj_invariant
    (aBound_of_chart hNC)

theorem aNonzero_of_charts (hNC : NChart) (hWR : WRightInv) : ANonzero :=
  ANz.aNonzero_of subgroup_hypothesis_holds representation_unitary product_decomposition_holds (aEquiv_of_charts hNC hWR nilradical_unimodular_conj_invariant)
    (aCont_of_chart hNC)

theorem wlocExists_of_charts (hNC : NChart) (hWR : WRightInv)
    (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) : WlocExists :=
  scWlocExists_of haar_measure_unipotent_nilradical (aEquiv_of_charts hNC hWR nilradical_unimodular_conj_invariant) (aCont_of_chart hNC)
    (aKind_of_chart hNC) (aReprod_of_chart hNC) (wave_packet_l1_l2_of_nilpotent_chart hNC hWR) wave_packet_weighted_integrable
    (aNonzero_of_charts hNC hWR) hR

theorem scWlocExists_of_chart (hNC : NChart) (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) : WlocExists :=
  wlocExists_of_charts hNC unipotent_right_invariance hR

end WlocSk
end
end

theorem scWlocExists (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) : Formalism.L2.SG.SplitPrimeNormLemmas.WlocExists :=
  WlocSk.scWlocExists_of_chart WlocSk.nilpotent_chart_exists hR
