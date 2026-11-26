module

public import Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.TubeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMassProductLowerBoundUnitaryPq

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.FrameCovolume.MeasTransl
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MainStatements.Tam.T2

theorem meas_transl (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ))
    (hV : V.SigOK) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (μ : Measure (GA D V)) [μ.IsMulLeftInvariant]
    (g : GA D V) (hg : g ∈ GfC V) (S : Set (GA D V)) (B : Set (∀ ρ, Upq V ρ)) :
    μ {y | g⁻¹ * y ∈ S ∧ rp y ∈ B} = μ {z | z ∈ S ∧ rp z ∈ B} := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have h1 : rp g = 1 := GlobalTheory.CovTop.VolBox.rp_eq_one V θ A rp hV hA hrp g hg
  rw [← measure_preimage_mul μ g⁻¹ {z | z ∈ S ∧ rp z ∈ B}]
  congr 1
  ext y
  show g⁻¹ * y ∈ S ∧ rp y ∈ B ↔ g⁻¹ * y ∈ S ∧ rp (g⁻¹ * y) ∈ B
  rw [map_mul rp, map_inv rp, h1, inv_one, one_mul]

theorem meas_low (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ))
    (hV : V.SigOK) (hA : IsFrames V A) (hrp : IsRealPart V θ A rp) (μ : Measure (GA D V)) [μ.IsMulLeftInvariant]
    (hidx : IdxSt) (M : ℕ) (hM : 1 ≤ M) (B : Set (∀ ρ, Upq V ρ)) :
    μ {h | h ∈ KM V 1 ∧ rp h ∈ B} ≤ ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * μ {h | h ∈ KM V M ∧ rp h ∈ B} := by
  classical
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfd : fdeg D.host.E = D.R.f := (GlobalTheory.T.two_le_hermitianRank_and_hostDegree_eq D).2
  obtain ⟨S, hScard, hS⟩ := hidx D.host.E V.rank M (-(V.gram)ᵀ) (GlobalTheory.Member.latC V) hM (GlobalTheory.T.selfDualLattice_neg_transpose_gram D V)
  set Q : Set (GA D V) := {h | h ∈ KM V M ∧ rp h ∈ B} with hQ
  let P : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E) → Set (GA D V) := fun s => {h | h ∈ KM V 1 ∧ rp h ∈ B ∧
    ∃ k, IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M k ∧
      ((finHom V h).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) = s * k}
  have hcov : {h | h ∈ KM V 1 ∧ rp h ∈ B} ⊆ ⋃ s ∈ S, P s := by
    intro h ⟨h1, hB⟩
    obtain ⟨s, hsS, -, k, hk, e⟩ := hS _ h1
    exact Set.mem_iUnion₂.2 ⟨s, hsS, h1, hB, k, hk, e⟩
  have hP : ∀ s ∈ S, μ (P s) ≤ μ Q := by
    intro s hsS
    rcases (P s).eq_empty_or_nonempty with he | ⟨z, hz1, hzB, kz, hkz, hzs⟩
    · rw [he, measure_empty]; exact bot_le
    obtain ⟨w, hw, hwz⟩ := GlobalTheory.SplitDec.exists_finPart V z
    have hw1 : rp w = 1 := GlobalTheory.CovTop.VolBox.rp_eq_one V θ A rp hV hA hrp w hw
    have hsu : IsUnit s.det := by
      have hu : IsUnit ((finHom V z).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)).det := Matrix.isUnits_det_units _
      rw [hzs, Matrix.det_mul] at hu
      exact isUnit_of_mul_isUnit_left hu
    refine (measure_mono fun x hx => ?_).trans (measure_preimage_mul μ w⁻¹ Q).le
    obtain ⟨-, hxB, kx, hkx, hxs⟩ := hx
    refine ⟨?_, ?_⟩
    · show IsKM (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
        ((finHom V (w⁻¹ * x)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
      have e1 : ((finHom V (w⁻¹ * x)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) = kz⁻¹ * kx := by
        rw [map_mul, map_inv, ← hwz, Units.val_mul, Matrix.coe_units_inv, hzs, hxs, Matrix.mul_inv_rev,
          Matrix.mul_assoc, ← Matrix.mul_assoc s⁻¹, Matrix.nonsing_inv_mul _ hsu, Matrix.one_mul]
      rw [e1]
      exact isKM_mul (isKM_inv hkz) hkx
    · show rp (w⁻¹ * x) ∈ B
      rw [map_mul, map_inv, hw1, inv_one, one_mul]
      exact hxB
  calc μ {h | h ∈ KM V 1 ∧ rp h ∈ B} ≤ μ (⋃ s ∈ S, P s) := measure_mono hcov
    _ ≤ ∑ s ∈ S, μ (P s) := measure_biUnion_finset_le S P
    _ ≤ ∑ s ∈ S, μ Q := Finset.sum_le_sum hP
    _ = (S.card : ℝ≥0∞) * μ Q := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * μ Q := by
      gcongr
      rw [← hfd]
      exact_mod_cast hScard

end MainStatements.Tam.T2
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.TubeMeasures.DisjointTubes.FrameCovolume.TubeDisj
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace MainStatements.Tam.T2

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tube_disj (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V) (rp : GA D V →* (∀ ρ, Upq V ρ))
    (Ψ : Finset (D.host.E →+* ℂ)) (Gm : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (σ : D.what₂.Tau ≃ Ψ)
    (π : (∀ ρ, Upq V ρ) → realSU Ψ Gm) (M : ℕ) (ι : Type) (X : ι → Data D.host.E V.rank) (g : ι → GA D V)
    (F : ι → Set (realSU Ψ Gm))
    (hM : 3 ≤ M) (hGm : Gm = -(V.gram)ᵀ) (hθ : IsInfFam θ) (hrp : IsRealPart V θ A rp)
    (hσ : ∀ ρ, (σ ρ).1 = tauE D ρ)
    (heq : ∀ (s' : realSU Ψ Gm) (b₀ : ∀ ρ, Upq V ρ), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ =
      A ρ * ((s'.1 (σ ρ) : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)) → ∀ b, π (b₀ * b) = s' * π b)
    (hF : ∀ k, ∀ γ ∈ inReal Ψ Gm (X k).Γ, ∀ y ∈ F k, γ * y ∈ F k → γ = 1)
    (hdist : ∀ k k', UEquiv (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ)
      (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) M
      ((finHom V (g k)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) ((finHom V (g k')).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) → k = k')
    (hXG : ∀ k, (X k).Gm = -(V.gram)ᵀ)
    (hXΛ : ∀ k, ((X k).Λ : Set (Fin V.rank → D.host.E)) = latOf (maximalRealSubfield D.host.E)
      ((finHom V (g k)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E)) (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)))
    (hXΓ : ∀ k γ, γ ∈ (X k).Γ ↔ IsUStab (X k).Gm (X k).Λ γ ∧ ∀ x ∈ (X k).Λ, ∃ y ∈ (X k).Λ,
      (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ x - x = M • y) :
    ∀ δ ∈ GQ V, ∀ (k k' : ι) (y : GA D V), ((g k)⁻¹ * y ∈ KM V M ∧ π (rp y) ∈ F k) →
      ((g k')⁻¹ * (δ * y) ∈ KM V M ∧ π (rp (δ * y)) ∈ F k') → δ = 1 ∧ k = k' := by
  intro δ hg k k' y hy hgy
  classical
  obtain ⟨δ0, hδU, hδeq⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
  have hmat : matHom V δ = Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) δ0 := hδeq.symm
  have h1 : (matHom V δ).1 = (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) := by rw [hmat]; rfl
  have hinf : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) δ = (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ) := by
    intro ρ
    have hinc : ((δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Ainf D.host.F))).map (θ ρ) =
        (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (tauE D ρ) := by
      ext a b
      exact (hθ ρ).1 _
    rw [← hinc, ← GlobalTheory.UnitaryGlue.map_map_inclR (fstA D.host.F), ← h1]; rfl
  have hfin : (finHom V δ).1 = (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Af D.host.F)) := by
    rw [← GlobalTheory.UnitaryGlue.map_map_inclR (sndA D.host.F), ← h1]; rfl
  have hfinv : (finHom V δ⁻¹).1 = ((δ0⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map
      (inclR (Af D.host.F)) := by
    rw [map_inv]
    apply Units.inv_eq_of_mul_eq_one_left
    rw [hfin, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)

  have hU : ((δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map cc)ᵀ * V.gram * δ0.1 = V.gram := by
    change Formalism.UG.cT _ δ0.1 * V.gram * δ0.1 = V.gram at hδU
    convert hδU using 3
    ext a b
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
    congr 1
  have hmatG : δ0.1ᵀ * -(V.gram)ᵀ * δ0.1.map cc = -(V.gram)ᵀ := by
    have := congrArg (fun A => -Aᵀ) hU
    simpa [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg] using this
  have hherm := GlobalTheory.MsRepsFwd.herm_mulVec _ _ hmatG

  have hmulKM : ∀ a b, a ∈ KM V M → b ∈ KM V M → a * b ∈ KM V M := fun a b ha hb => by
    show IsKM _ _ _ _ ((finHom V (a * b)).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    rw [map_mul, Units.val_mul]
    exact GlobalTheory.UCls.isKM_mul ha hb
  have hinvKM : ∀ a, a ∈ KM V M → a⁻¹ ∈ KM V M := fun a ha => by
    show IsKM _ _ _ _ ((finHom V a⁻¹).1 : Matrix (Fin V.rank) (Fin V.rank) (RA (maximalRealSubfield D.host.E) D.host.E))
    rw [map_inv, Matrix.coe_units_inv]
    exact GlobalTheory.UCls.isKM_inv ha
  have hκ : (g k')⁻¹ * δ * g k ∈ KM V M := by
    have e : (g k')⁻¹ * δ * g k = ((g k')⁻¹ * (δ * y)) * ((g k)⁻¹ * y)⁻¹ := by group
    rw [e]; exact hmulKM _ _ hgy.1 (hinvKM _ hy.1)
  have hκ' : (g k)⁻¹ * δ⁻¹ * g k' ∈ KM V M := by
    have e : (g k)⁻¹ * δ⁻¹ * g k' = ((g k)⁻¹ * y) * ((g k')⁻¹ * (δ * y))⁻¹ := by group
    rw [e]; exact hmulKM _ _ hy.1 (hinvKM _ hgy.1)
  have hUA : IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ) (ratM (maximalRealSubfield D.host.E) δ0.1) :=
    GlobalTheory.T.isInvertibleUnitaryAdelicMatrix_of_rational_unitary D.host.E V.rank _ δ0.1 (Matrix.isUnits_det_units δ0).ne_zero hherm
  have hratM : ratM (maximalRealSubfield D.host.E) δ0.1 = δ0.1.map (inclR (Af D.host.F)) := rfl
  have hkk : k = k' := hdist k k' ⟨δ0.1, hUA, (finHom V ((g k)⁻¹ * δ⁻¹ * g k')).1, hκ', by
    rw [hratM, ← hfin, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 2
    group⟩
  cases hkk

  haveI : Nontrivial (Af D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    exact (Formalism.UG.evalV D.host.F ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩).toRingHom.domain_nontrivial
  haveI : Nontrivial (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := Af D.host.F) (B := D.host.E)
      (algebraMap D.host.F D.host.E).injective).nontrivial
  have hinj : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)).injective
  have he1 : δ0.1.map (inclR (F := D.host.F) (Af D.host.F)) * (finHom V (g k)).1 =
      (finHom V (g k)).1 * (finHom V ((g k)⁻¹ * δ * g k)).1 := by
    rw [← hfin, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 2
    group
  have he2 : (δ0⁻¹ : GL (Fin V.rank) D.host.E).1.map (inclR (F := D.host.F) (Af D.host.F)) * (finHom V (g k)).1 =
      (finHom V (g k)).1 * (finHom V ((g k)⁻¹ * δ⁻¹ * g k)).1 := by
    rw [← hfinv, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 2
    group
  have C1 := GlobalTheory.MsRepsFwd.latOf_congr D.host.F D.host.E V.rank M (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
    (finHom V (g k)).1 (finHom V ((g k)⁻¹ * δ * g k)).1 δ0.1 hinj hκ.2.1 he1
  have C2 := GlobalTheory.MsRepsFwd.latOf_congr D.host.F D.host.E V.rank M (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
    (finHom V (g k)).1 (finHom V ((g k)⁻¹ * δ⁻¹ * g k)).1 (δ0⁻¹ : GL (Fin V.rank) D.host.E).1 hinj hκ'.2.1 he2
  have hmem : ∀ x, x ∈ (X k).Λ ↔ x ∈ GlobalTheory.AdLat.latOf D.host.F (finHom V (g k)).1
      (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    intro x
    rw [← SetLike.mem_coe, hXΛ k]
  have hcong : ∀ x ∈ (X k).Λ, ∃ y ∈ (X k).Λ, δ0.1 *ᵥ x - x = M • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := C1 x ((hmem x).1 hx)
    exact ⟨y, (hmem y).2 hy, e⟩
  have hcong' : ∀ x ∈ (X k).Λ, ∃ y ∈ (X k).Λ, (δ0⁻¹ : GL (Fin V.rank) D.host.E).1 *ᵥ x - x = M • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := C2 x ((hmem x).1 hx)
    exact ⟨y, (hmem y).2 hy, e⟩
  have hstab : ∀ x, x ∈ (X k).Λ ↔ δ0.1 *ᵥ x ∈ (X k).Λ := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, e⟩ := hcong x hx
      rw [show δ0.1 *ᵥ x = x + M • y by rw [← e]; abel]
      exact (X k).Λ.add_mem hx (nsmul_mem hy M)
    · intro hx
      obtain ⟨y, hy, e⟩ := hcong' _ hx
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at e
      rw [show x = δ0.1 *ᵥ x + M • y by rw [← e]; abel]
      exact (X k).Λ.add_mem hx (nsmul_mem hy M)
  have hΓ : δ0 ∈ (X k).Γ := (hXΓ k δ0).2 ⟨⟨by rw [hXG k]; exact hherm, hstab⟩, hcong⟩
  have hd1 : (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).det = 1 :=
    GlobalTheory.T.det_eq_one_unitary_principal_congruence_level_three D.host.E V.rank M (X k) hM (hXΓ k) δ0 hΓ

  have hmemSU : embGL Ψ V.rank δ0 ∈ realSU Ψ Gm := embGL_mem_realSU Ψ Gm δ0 hd1 (by rw [hGm]; exact hherm)
  have hin : (⟨embGL Ψ V.rank δ0, hmemSU⟩ : realSU Ψ Gm) ∈ inReal Ψ Gm (X k).Γ :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨δ0, hΓ, rfl⟩)
  have heqv := heq ⟨embGL Ψ V.rank δ0, hmemSU⟩ (rp δ) (fun ρ => by
    rw [hrp δ ρ, hinf ρ]
    show _ = A ρ * (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ).1
    rw [hσ ρ]) (rp y)
  have hs1 := hF k _ hin (π (rp y)) hy.2 (by rw [← heqv, ← map_mul]; exact hgy.2)
  have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]; omega
  have hδ1 : δ0 = 1 := by
    have h5 := congrArg (fun s : realSU Ψ Gm => ((s.1 (σ ρ₀) : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)) hs1
    have h6 : (δ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ₀).1 =
        (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (σ ρ₀).1 := by
      rw [Matrix.map_one _ (map_zero _) (map_one _)]
      exact h5
    exact Units.ext (Matrix.map_injective (σ ρ₀).1.injective h6)
  refine ⟨Subtype.ext ?_, rfl⟩
  rw [hδ1, map_one] at hmat
  exact hmat

end MainStatements.Tam.T2
end

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MainStatements.Tam.T2

theorem exists_frames (D : D7) (V : HSp D) (hV : V.SigOK) : ∃ A : Frames V, IsFrames V A := by
  classical
  have h : ∀ ρ : D.what₂.Tau, ∃ a : Matrix (Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2) (Fin V.rank) ℂ,
      aᴴ * Formalism.UG.Jpq (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 * a = gramAt D V ρ := by
    intro ρ
    obtain ⟨e, Q, hQ⟩ := hV (tauE D ρ)
    have hQ' : (Q : Matrix _ _ ℂ)ᴴ * ((HSpace.gram V).map (tauE D ρ)).reindex e e * (Q : Matrix _ _ ℂ) =
        Formalism.UG.Jpq _ _ := hQ
    have h1 : ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)ᴴ * Formalism.UG.Jpq _ _ * ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ) =
        ((HSpace.gram V).map (tauE D ρ)).reindex e e := by
      rw [← hQ']
      calc _ = ((Q : Matrix _ _ ℂ) * ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ))ᴴ *
            ((HSpace.gram V).map (tauE D ρ)).reindex e e * ((Q : Matrix _ _ ℂ) * ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [Units.mul_inv]; simp
    let Pm : Matrix (Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2)
        (Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2) ℂ := ((Q⁻¹ : GL _ ℂ) : Matrix _ _ ℂ)
    let a : Matrix (Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2) (Fin V.rank) ℂ := Pm.submatrix id e
    have h1' : Pmᴴ * Formalism.UG.Jpq (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 * Pm =
        ((HSpace.gram V).map (tauE D ρ)).reindex e e := h1
    refine ⟨a, ?_⟩
    have h2 : aᴴ * Formalism.UG.Jpq (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 * a =
        (Pmᴴ * Formalism.UG.Jpq (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2 * Pm).submatrix e e := by
      ext i j
      simp [a, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [h2, h1']
    ext a b
    simp [gramAt]
  choose A hA using h
  exact ⟨A, hA⟩

theorem covol_frame {E : Type} [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ Ψ' : Finset (E →+* ℂ))
    (G G' : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (x' : Frame Ψ' r) (p0 p1 : ℕ) (Γ : Subgroup (GL (Fin r) E))
    (hΨ : Ψ = Ψ') (hG : G = G') (hh : ∀ a b, cc (G a b) = G b a)
    (hx : ∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ))
    (hx' : ∀ τ : Ψ', gram τ.1 G' (mat x' τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) :
    covolume (inReal Ψ G Γ) (realSU Ψ G) (riemHaar Ψ G x) = covolume (inReal Ψ' G' Γ) (realSU Ψ' G') (riemHaar Ψ' G' x') := by
  subst hΨ
  subst hG
  rw [GlobalTheory.T.riemannianHaar_independent_of_orthonormal_frame E r p0 p1 Ψ G x x' hh hx hx']

end MainStatements.Tam.T2

namespace MainStatements.Tam

open MainStatements.Tam.T2

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tube : VolSt → StabSt → IdxSt → TubeSt := by
  intro hvol hstab hidx D V P Q hV hsig hr M hM ι _ X g x0 hdist hX
  classical
  obtain ⟨hLC, hSC, hBor, hC⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  let μ : Measure (GA D V) := Measure.haar
  haveI hμH : μ.IsHaarMeasure := by infer_instance
  obtain ⟨𝓕, hFD⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμH
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨A, hA⟩ := exists_frames D V hV
  choose mm hmm using GlobalTheory.MinfMeasure.exists_isMinf
  let m : ∀ ρ, Measure (Upq V ρ) := fun ρ => mm _ _
  have hm : ∀ ρ, IsMinf (m ρ) := fun ρ => hmm _ _
  obtain ⟨X₀, σ, x₀, e, hG, hσ, hx₀, hid⟩ := GlobalTheory.T.exists_flagDomain_orthonormalFrame_identification D V P Q hV hsig A hA
  obtain ⟨rp, hrpc, hrp⟩ := GlobalTheory.T.exists_continuous_realComponentHom_unitaryAdelic D V θ A hV hθ hA
  let a₀ : ∀ ρ : D.what₂.Tau, Fin (V.sig (tauE D ρ)).1 ⊕ Fin (V.sig (tauE D ρ)).2 :=
    fun ρ => (e ρ).symm ⟨0, by omega⟩
  obtain ⟨π, hπc, hπ, hπe⟩ := GlobalTheory.T.exists_continuous_equivariant_detOneFactorProjection D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x₀ σ A e a₀ hid
  have hcard : X₀.Ψ.card = D.R.f := by
    rw [← Fintype.card_coe, ← Fintype.card_congr σ, D.what₂.card_Tau]
  have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  obtain ⟨ρ₀⟩ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]; omega
  have hΨk : ∀ k, (X k).Ψ = X₀.Ψ := by
    intro k
    ext τ
    rw [(hX k).2.1 τ]
    constructor
    · rintro ⟨ρ, rfl⟩
      rw [← hσ ρ]
      exact (σ ρ).2
    · intro hτ
      obtain ⟨ρ, hρ⟩ := σ.surjective ⟨τ, hτ⟩
      exact ⟨ρ, by rw [← hσ ρ, hρ]⟩
  have htr : ∀ k, covolume (inReal (X k).Ψ (X k).Gm (X k).Γ) (realSU (X k).Ψ (X k).Gm) (riemHaar (X k).Ψ (X k).Gm (x0 k)) =
      covolume (inReal X₀.Ψ X₀.Gm (X k).Γ) (realSU X₀.Ψ X₀.Gm) (riemHaar X₀.Ψ X₀.Gm x₀) := fun k =>
    covol_frame V.rank _ _ _ _ (x0 k) x₀ (X k).p0 X₀.p0 (X k).Γ (hΨk k) ((hX k).1.trans hG.symm) (X k).Gm_herm
      (hX k).2.2.2.2 hx₀
  choose F hFm hFcov hFfree using fun k => GlobalTheory.T.exists_packingSet_measure_ge_covolume (realSU X₀.Ψ X₀.Gm) (riemHaar X₀.Ψ X₀.Gm x₀)
    (inReal X₀.Ψ X₀.Gm (X k).Γ) (GlobalTheory.T.countable_rationalSubgroupInRealSpecialUnitary _ _ _ _ _)
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  let B : ι → Set (∀ ρ, Upq V ρ) := fun k => π ⁻¹' F k ∩ {b | 0 < (UpqT.mat (b ρ₀)).det.im}
  have hBm : ∀ k, MeasurableSet (B k) := fun k =>
    (hπc.measurable (hFm k)).inter (GlobalTheory.T.measurableSet_det_im_pos_at_index D.what₂.Tau _ _ ρ₀)
  choose g' hg'C hg'f using fun k => GlobalTheory.SplitDec.exists_finPart V (g k)
  let T : ι → Set (GA D V) := fun k => {y | (g' k)⁻¹ * y ∈ KM V M ∧ rp y ∈ B k}
  have hKMo : IsOpen (KM V M) := (hstab.1 D V).2 M (by omega)
  have hTm : ∀ k, MeasurableSet (T k) := fun k =>
    ((hKMo.preimage (continuous_const.mul continuous_id)).measurableSet).inter (hrpc.measurable (hBm k))
  have hdisj := tube_disj D V θ A rp X₀.Ψ X₀.Gm σ π M ι X g' F hM hG hθ hrp hσ hπe hFfree
    (fun k k' h => hdist k k' (by rw [hg'f k, hg'f k']; exact h)) (fun k => (hX k).1)
    (fun k => by rw [← hg'f k]; exact (hX k).2.2.1) (fun k => (hX k).2.2.2.1)

  have hTd : Pairwise (Function.onFun Disjoint T) := by
    intro k k' hne
    refine Set.disjoint_left.2 fun y hy hy' => hne ?_
    exact (hdisj 1 (GQ V).one_mem k k' y ⟨hy.1, hy.2.1⟩ (by rw [one_mul]; exact ⟨hy'.1, hy'.2.1⟩)).2
  let S := ⋃ k, T k
  have hSm : MeasurableSet S := MeasurableSet.iUnion hTm
  have hμS : μ S = ∑ k, μ (T k) := by
    rw [measure_iUnion hTd hTm, tsum_fintype]
  have hSF : μ S ≤ μ 𝓕 := by
    refine hFD.measure_le_of_pairwise_disjoint hSm.nullMeasurableSet ?_
    intro γ γ' hne
    refine Disjoint.aedisjoint (Set.disjoint_left.2 fun z hz hz' => hne ?_)
    obtain ⟨y, hy, hyz⟩ := Set.mem_smul_set.1 hz.1
    obtain ⟨y', hy', hyz'⟩ := Set.mem_smul_set.1 hz'.1
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.1 hy
    obtain ⟨j', hyj'⟩ := Set.mem_iUnion.1 hy'
    have h1 : (γ : GA D V) * y = z := hyz
    have h2 : (γ' : GA D V) * y' = z := hyz'
    have e1 : ((γ'⁻¹ * γ : GQ V) : GA D V) * y = y' := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, h1, ← h2, ← mul_assoc, inv_mul_cancel, one_mul]
    have e2 := (hdisj _ (γ'⁻¹ * γ).2 j j' y ⟨hyj.1, hyj.2.1⟩ (by rw [e1]; exact ⟨hyj'.1, hyj'.2.1⟩)).1
    have e3 : γ'⁻¹ * γ = 1 := Subtype.ext e2
    exact (inv_mul_eq_one.1 e3).symm

  have hKM1 : Stab V = KM V 1 := (hstab.1 D V).1
  have hlowk : ∀ k, μ {h | h ∈ Stab V ∧ rp h ∈ B k} ≤ ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * μ (T k) := by
    intro k
    have e1 : μ (T k) = μ {z | z ∈ KM V M ∧ rp z ∈ B k} :=
      meas_transl D V θ A rp hV hA hrp μ (g' k) (hg'C k) (KM V M) (B k)
    rw [e1, hKM1]
    exact meas_low D V θ A rp hV hA hrp μ hidx M (by omega) (B k)
  have hvk : ∀ k, μ 𝓕 * Measure.pi m (B k) = μ {h | h ∈ Stab V ∧ rp h ∈ B k} *
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) := fun k =>
    hvol D V P Q hV hsig μ 𝓕 hFD θ A m rp hθ hA hm hrpc hrp (B k) (hBm k)
  have h16 : ∀ k, ENNReal.ofReal ((1 / 16 : ℝ) ^ (D.R.f * V.rank ^ 2)) * riemHaar X₀.Ψ X₀.Gm x₀ (F k) ≤
      Measure.pi m (B k) := by
    intro k
    rw [← hcard]
    exact GlobalTheory.T.archimedean_mass_product_lower_bound_unitary_pq D.host.E V.rank D.what₂.Tau _ _ X₀.Ψ X₀.Gm x₀ σ A e a₀ π m ρ₀ (by omega) hid hπc hπ hπe hm
      (F k) (hFm k)

  have hvolU : 0 < ReciprocityTheory.ChartRestriction.DS.volU V.rank := by
    unfold ReciprocityTheory.ChartRestriction.DS.volU
    exact Finset.prod_pos fun i _ => by positivity
  have hCpos : 0 < ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank :=
    mul_pos (pow_pos hvolU _) (Formalism.MainNotions.StandardLattice.massI_pos D V.rank)
  have hFtop : μ 𝓕 ≠ ⊤ := (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμH hFD).ne
  have hF0 : μ 𝓕 ≠ 0 := by
    intro h0
    have e0 := hvol D V P Q hV hsig μ 𝓕 hFD θ A m rp hθ hA hm hrpc hrp Set.univ MeasurableSet.univ
    rw [h0, zero_mul] at e0
    have hset : {h | h ∈ Stab V ∧ rp h ∈ (Set.univ : Set (∀ ρ, Upq V ρ))} = KM V 1 := by
      ext h
      simp [hKM1]
    have h1mem : (1 : GA D V) ∈ KM V 1 := by
      show IsKM _ _ _ _ _
      rw [map_one, Units.val_one]
      exact isKM_one _ _ _ _
    have hpos : 0 < μ (KM V 1) := ((hstab.1 D V).2 1 le_rfl).measure_pos μ ⟨1, h1mem⟩
    rw [hset] at e0
    exact (mul_ne_zero hpos.ne' (ENNReal.ofReal_pos.2 hCpos).ne') e0.symm

  have hsum : ∑ k, Measure.pi m (B k) ≤
      ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) * ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) := by
    have h1 : μ 𝓕 * ∑ k, Measure.pi m (B k) ≤ μ 𝓕 *
        (ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) * ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2))) := by
      rw [Finset.mul_sum]
      calc ∑ k, μ 𝓕 * Measure.pi m (B k)
          = ∑ k, μ {h | h ∈ Stab V ∧ rp h ∈ B k} *
              ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) :=
            Finset.sum_congr rfl fun k _ => hvk k
        _ ≤ ∑ k, ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * μ (T k) *
              ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) :=
            Finset.sum_le_sum fun k _ => by gcongr; exact hlowk k
        _ = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) *
              ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * ∑ k, μ (T k) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
        _ ≤ ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) *
              ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2)) * μ 𝓕 := by
            gcongr
            rw [← hμS]
            exact hSF
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_right hF0 hFtop).1 h1
  have hcov : ∀ k, covolume (inReal (X k).Ψ (X k).Gm (X k).Γ) (realSU (X k).Ψ (X k).Gm) (riemHaar (X k).Ψ (X k).Gm (x0 k)) ≤
      ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * V.rank ^ 2)) * Measure.pi m (B k) := by
    intro k
    rw [htr k]
    calc _ ≤ riemHaar X₀.Ψ X₀.Gm x₀ (F k) := hFcov k
      _ = ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * V.rank ^ 2)) *
            (ENNReal.ofReal ((1 / 16 : ℝ) ^ (D.R.f * V.rank ^ 2)) * riemHaar X₀.Ψ X₀.Gm x₀ (F k)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (16 : ℝ) ^ (D.R.f * V.rank ^ 2)), ← mul_pow]
          norm_num
      _ ≤ _ := by gcongr; exact h16 k
  calc _ ≤ ∑ k, ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * V.rank ^ 2)) * Measure.pi m (B k) :=
        Finset.sum_le_sum fun k _ => hcov k
    _ = ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * V.rank ^ 2)) * ∑ k, Measure.pi m (B k) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal ((16 : ℝ) ^ (D.R.f * V.rank ^ 2)) *
          (ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU V.rank ^ D.R.f * massI D V.rank) *
            ((M : ℝ≥0∞) ^ (2 * D.R.f * V.rank ^ 2))) := by gcongr
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (16 : ℝ) ^ (D.R.f * V.rank ^ 2) * (M : ℝ) ^ (2 * D.R.f * V.rank ^ 2)),
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (16 : ℝ) ^ (D.R.f * V.rank ^ 2)),
          ENNReal.ofReal_pow (Nat.cast_nonneg M), ENNReal.ofReal_natCast]
        ring

end MainStatements.Tam
