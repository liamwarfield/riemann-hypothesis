module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GelfandInvariantActionSmoothVectorsScalar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivariantMapCarriesGelfandInvariantToFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaEquivariantPairBoundedFunctions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevFormEqZeroOfSmoothOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevFormEqZeroOfSmoothOrbit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem cyc_mul_mem_UJset {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε)
    (hb : b ∈ UJset ε) : a * b ∈ UJset ε := by
  have h1 : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have h2 : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  calc (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h1, h2]

theorem clm_eq_zero_of_orbit {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (hi : IsIrredOn (UJset ε) σ)
    (L : H →L[ℂ] ℂ) {v : H} (hv : v ≠ 0) (h : ∀ g ∈ UJset ε, L (σ g v) = 0) (w : H) : L w = 0 := by
  let S : Submodule ℂ H :=
    { carrier := {x | ∀ g ∈ UJset ε, L (σ g x) = 0}
      add_mem' := fun ha hb g hg => by rw [map_add (f := _), map_add (f := _), ha g hg, hb g hg, add_zero]
      zero_mem' := fun g _ => by rw [map_zero, map_zero]
      smul_mem' := fun c x ha g hg => by rw [map_smul, map_smul, ha g hg, smul_zero] }
  have hc : IsClosed (S : Set H) := by
    have : (S : Set H) = ⋂ g ∈ UJset ε, {x | L (σ g x) = 0} := by
      ext x; simp only [Set.mem_iInter]; rfl
    rw [this]
    exact isClosed_biInter fun g _ => isClosed_eq (L.continuous.comp (σ g).continuous) continuous_const
  have hst : ∀ g ∈ UJset ε, ∀ x ∈ S, σ g x ∈ S := fun g hg x hx a ha => by
    have := hx (a * g) (cyc_mul_mem_UJset ha hg)
    rwa [hσ.1.2 a ha g hg] at this
  rcases hi S hc hst with h0 | h0
  · have : v ∈ S := h
    rw [h0] at this
    exact absurd this hv
  · have : w ∈ S := by rw [h0]; trivial
    have h1 := this 1 (by show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * 1 = Formalism.REAL.Jm ε; simp)
    rwa [hσ.1.1] at h1

theorem sobCont_eq_zero_of_orbit : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → ∀ v ∈ smSub G (trRep σ P), v ≠ 0 → (∀ g ∈ UJset ε, ℓ (σ g v) = 0) → ∀ w ∈ smSub G (trRep σ P), ℓ w = 0 := by
  intro n ε H _ _ _ σ P G hP hG hσ hi ℓ hℓ v hv hv0 h0 w hw
  obtain ⟨hb, hs⟩ := GlobalTheory.SobGarding.sobCont_gard n ε H σ P G hP hG hσ ℓ hℓ
  have key : ∀ φ, IsTest φ → ℓ (gard ε σ φ w) = 0 := fun φ hφ => by
    obtain ⟨C, hC⟩ := hb φ hφ
    let L : H →L[ℂ] ℂ :=
      (ℓ ∘ₗ GlobalTheory.LowTypeRestriction.garding hσ hφ.continuous hφ.2).mkContinuousOfExistsBound ⟨C, hC⟩
    refine clm_eq_zero_of_orbit hσ hi L hv0 (fun g hg => ?_) w
    show ℓ (gard ε σ φ (σ g v)) = 0
    rw [(hs _ (sigma_mem hP hG hσ hv hg)).2 φ hφ]
    have : ∀ a : Formalism.REAL.UJ ε, ℓ (σ (umat a) (σ g v)) = 0 := fun a => by
      have := h0 (umat a * g) (cyc_mul_mem_UJset a.2 hg)
      rwa [hσ.1.2 _ a.2 g hg] at this
    simp [this]
  have := eq_zero_of_forall_test (hs w hw).1 fun φ hφ => by rw [← (hs w hw).2 φ hφ, key φ hφ]
  have e : σ (umat (1 : Formalism.REAL.UJ ε)) w = w := by
    show σ 1 w = w
    rw [hσ.1.1]; rfl
  simpa only [e] using this

end GlobalTheory.SmVec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevFormEqZeroOfSmoothOrbitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolevForm_eq_zero_of_smooth_orbit : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → ∀ v ∈ smSub G (trRep σ P), v ≠ 0 → (∀ g ∈ UJset ε, ℓ (σ g v) = 0) → ∀ w ∈ smSub G (trRep σ P), ℓ w = 0 := by
  first | exact @GlobalTheory.SmVec.sobCont_eq_zero_of_orbit | exact GlobalTheory.SmVec.sobCont_eq_zero_of_orbit | (intros; apply GlobalTheory.SmVec.sobCont_eq_zero_of_orbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDimensionalKStableSmoothVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDimensionalKStableSmoothVectors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem exists_finiteDimensional_kStable_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → (∃ Λ S, IsKTypeOf ε σ Λ S) → ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧ W ≠ ⊥ ∧ W ≤ smSub G (trRep σ P) ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W := by
  rintro n ε H _ _ _ σ P G hP h hU ⟨Λ, S, hS⟩
  obtain ⟨w, hwS, hw, -⟩ := hS.2.2.2.1
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := (1 : Formalism.REAL.UJ ε).2
  have hnb : {g | ‖σ g w - w‖ < ‖w‖ / 2} ∈ 𝓝[UJset ε] (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h := (hU.2.2 w 1 hone) (Metric.ball_mem_nhds _ (half_pos hwpos))
    simpa [hU.1.1, Set.preimage, dist_eq_norm] using h
  obtain ⟨U, hUn, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnb
  obtain ⟨φ, hφ, hφc, hφU, hφ0, hφ1, hinv⟩ := GlobalTheory.LowTypeRestriction.exists_bump hUn
  have hT : IsTest φ := ⟨hφ, hφc⟩
  have hne := GlobalTheory.LowTypeRestriction.garding_ne_zero hU hT.continuous hφc hφ0 hφ1 hw
    fun g hg h0 => hUs ⟨hφU g h0, hg⟩
  have hK := GlobalTheory.LowTypeRestriction.isKTypeOf_map hS (GlobalTheory.LowTypeRestriction.garding hU hT.continuous hφc)
    (fun k hk w => GlobalTheory.LowTypeRestriction.garding_comm hU hT.continuous hφc hinv hk w) hwS hne
  refine ⟨S.map (GlobalTheory.LowTypeRestriction.garding hU hT.continuous hφc), hK.1,
    (Submodule.ne_bot_iff _).2 ⟨_, ⟨w, hwS, rfl⟩, hne⟩, ?_, fun k hk v hv => hK.2.1 k hk v hv⟩
  rintro _ ⟨v, -, rfl⟩
  exact gard_mem hP h hU hT v

end GlobalTheory.SmVec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDimensionalKStableSmoothVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_kStable_smoothVectors : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → (∃ Λ S, IsKTypeOf ε σ Λ S) → ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧ W ≠ ⊥ ∧ W ≤ smSub G (trRep σ P) ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W := by
  first | exact @GlobalTheory.SmVec.exists_finiteDimensional_kStable_smooth | exact GlobalTheory.SmVec.exists_finiteDimensional_kStable_smooth | (intros; apply GlobalTheory.SmVec.exists_finiteDimensional_kStable_smooth <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory
  Matrix
open scoped TensorProduct InnerProductSpace Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultFinite

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {S : D.what₂.Tau → SPar} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}

def pt (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  atTau θ V τ ((M.fr τ)⁻¹ * g * M.fr τ)

theorem mem_sm {τ : D.what₂.Tau} {w : M.H τ} :
    w ∈ M.sm τ ↔ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)) := by rw [sm_eq]

theorem sigma_mem_sm {τ : D.what₂.Tau} (w : M.sm τ) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ UJset (M.ε τ)) : M.σ τ g w ∈ M.sm τ :=
  mem_sm.2 (sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (mem_sm.1 w.2) hg)

theorem map_sigma {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (v : M.Vec) (w : M.sm τ)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ UJset (M.ε τ)) :
    T (Function.update v τ ⟨M.σ τ g w, sigma_mem_sm w hg⟩) = rTr V (pt θ M τ g) (T (Function.update v τ w)) := by
  have := hT.equiv τ _ (conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) hg) (Function.update v τ w)
    ⟨M.σ τ g w, sigma_mem_sm w hg⟩ (by
      rw [Function.update_self]
      exact (congrArg (fun L : M.H τ →L[ℂ] M.H τ => L w) (trRep_conj (σ := M.σ τ) (M.fr_unit τ) g)).symm)
  rwa [Function.update_idem] at this

theorem exists_continuousLinearMap_tens_update {T : MMap M} (hT : IsMultMap θ M J χ T) (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ a : M.H τ →ₗ[ℂ] (GA D V → ℂ), (∀ w : M.sm τ, a w = T (Function.update v τ w)) ∧
      (∀ x, Sobolev₂ (lieG (gramAt D V τ)) (trRep (M.σ τ) (M.fr τ)) ((LinearMap.proj x).comp a)) ∧
      ∀ g ∈ UJset (M.ε τ), ∀ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)),
        a (M.σ τ g w) = rTr V (pt θ M τ g) (a w) := by
  obtain ⟨a, ha⟩ := LinearMap.exists_extend (T.toLinearMap v τ)
  have ha' : ∀ w : M.sm τ, a w = T (Function.update v τ w) := fun w => LinearMap.congr_fun ha w
  refine ⟨a, ha', fun x => ?_, fun g hg w hw => ?_⟩
  · obtain ⟨ℓ, ⟨L, C, h1, h2⟩, e⟩ := hT.cont τ v x
    refine ⟨L, C, h1, fun w hw => ?_⟩
    have := h2 w hw
    rw [e ⟨w, mem_sm.2 hw⟩, ← ha'] at this
    exact this
  · rw [ha' ⟨w, mem_sm.2 hw⟩, ← map_sigma hT τ v _ hg, ← ha']

theorem eq_zero_of_apply {T : MMap M} (hT : IsMultMap θ M J χ T) (v₀ : M.Vec) (h₀ : ∀ τ, v₀ τ ≠ 0) (h : T v₀ = 0) :
    T = 0 := by
  have key : ∀ s : Finset D.what₂.Tau, ∀ v : M.Vec, (∀ ρ, ρ ∉ s → v ρ = v₀ ρ) → T v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro v hv; rw [show v = v₀ from funext fun ρ => hv ρ (by simp), h]
    | insert τ s _ ih =>
      intro v hv
      have h2 : T (Function.update v τ (v₀ τ)) = 0 := by
        refine ih _ fun ρ hρ => ?_
        by_cases hh : ρ = τ
        · subst hh; simp
        · rw [Function.update_of_ne hh]; exact hv ρ (by simp [hh, hρ])
      obtain ⟨a, e, hs, hq⟩ := exists_continuousLinearMap_tens_update hT τ v
      have := (M.ds τ).1
      funext x
      have h3 := GlobalTheory.T.sobolevForm_eq_zero_of_smooth_orbit _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 _ (hs x)
        (v₀ τ) (mem_sm.1 (v₀ τ).2) (fun c => h₀ τ (Subtype.ext c)) (fun g hg => by
          show a _ x = 0
          rw [hq g hg _ (mem_sm.1 (v₀ τ).2), e, h2]
          rfl) (v τ) (mem_sm.1 (v τ).2)
      have h4 : a (v τ) x = 0 := h3
      rwa [e, Function.update_eq_self] at h4
  exact MultilinearMap.ext fun v => key Finset.univ v (by simp)

def kRep {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (W : Submodule ℂ H)
    (hW : ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W) : Representation ℂ (Formalism.REAL.KG ε) W where
  toFun k := (σ (Formalism.REAL.toMK k) : H →ₗ[ℂ] H).restrict fun w hw => hW _ k.2 w hw
  map_one' := by
    ext w
    show σ 1 w = w
    rw [hσ.1.1]; rfl
  map_mul' k k' := by
    ext w
    show σ (Formalism.REAL.toMK k * Formalism.REAL.toMK k') w = σ (Formalism.REAL.toMK k) (σ (Formalism.REAL.toMK k') w)
    rw [hσ.1.2 _ (k : Formalism.REAL.UJ ε).2 _ (k' : Formalism.REAL.UJ ε).2]; rfl

theorem isContRep_kRep {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (hW : ∀ k ∈ Formalism.REAL.Kset ε, ∀ w ∈ W, σ k w ∈ W) :
    GlobalTheory.Published.AutFin.IsContRep (kRep hσ W hW) := fun ℓ w =>
  (LinearMap.continuous_of_finiteDimensional ℓ).comp
    (Continuous.subtype_mk ((continuous_orbit hσ w).comp continuous_subtype_val) _)

theorem hcFinite (hP : GlobalTheory.Published.HarishChandraFinite) : HCFinite θ M J χ := by
  rintro hθ ⟨U, hU, hUJ⟩
  have hc := fun τ => (M.ds τ).1
  choose W hWf hW0 hWs hWk using fun τ => GlobalTheory.T.exists_finiteDimensional_kStable_smoothVectors _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
    ⟨_, (M.ds τ).2.2.2.2.2.1⟩
  choose c hcs using fun τ => GlobalTheory.T.gelfandInvariantAction_smoothVectors_scalar _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1
  choose u huW hu0 using fun τ => (Submodule.ne_bot_iff _).1 (hW0 τ)
  let v₀ : M.Vec := fun τ => ⟨u τ, mem_sm.2 (hWs τ (huW τ))⟩
  have hfin := hP D θ hθ V U hU M.ε M.fr (fun τ => ⟨M.fr_unit τ, M.fr_gram τ⟩) (fun τ => W τ)
    (fun τ => kRep (M.ds τ).2.2.1 (W τ) (hWk τ)) (fun τ => isContRep_kRep _ _ _) c
  have hmem : ∀ T : Mult θ M J χ, (T : MMap M) v₀ ∈ GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr
      (fun τ => kRep (M.ds τ).2.2.1 (W τ) (hWk τ)) c := by
    intro T
    have hT := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 T.2
    refine ⟨hT.aut v₀, fun k hk hf g => ?_, fun τ => ?_, fun τ k => ?_⟩
    · rw [hT.lev v₀ k (hUJ k hk hf).1, (hUJ k hk hf).2, one_mul]
    · obtain ⟨a, e, -, hq⟩ := exists_continuousLinearMap_tens_update hT τ v₀
      have := GlobalTheory.Published.AutFin.hasTypeAt_of_map θ V τ (M.ε τ) (M.fr τ) (kRep (M.ds τ).2.2.1 (W τ) (hWk τ))
        (a.comp (W τ).subtype) (fun k w => hq (Formalism.REAL.toMK k) (GlobalTheory.LowTypeRestriction.kset_subset k.2) w (hWs τ w.2)) ⟨u τ, huW τ⟩
      have e' : (a.comp (W τ).subtype) ⟨u τ, huW τ⟩ = (T : MMap M) v₀ := by
        rw [← Function.update_eq_self τ v₀, ← e]; rfl
      rwa [e'] at this
    · rw [GlobalTheory.T.equivariant_map_carries_gelfandInvariant_to_function D θ V S M J χ hθ T hT τ k v₀ (c τ k • v₀ τ) (hcs τ k _ (mem_sm.1 (v₀ τ).2)).symm,
        MultilinearMap.map_update_smul, Function.update_eq_self]
      rfl
  let ev : Mult θ M J χ →ₗ[ℂ] Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr
      (fun τ => kRep (M.ds τ).2.2.1 (W τ) (hWk τ)) c) :=
    { toFun := fun T => ⟨(T : MMap M) v₀, Submodule.subset_span (hmem T)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun T hT => Subtype.ext ?_)
  exact eq_zero_of_apply ((GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 T.2) v₀
    (fun τ h => hu0 τ (congrArg Subtype.val h)) (congrArg Subtype.val hT)

theorem schur_multMap (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {T T' : MMap M} (hT : IsMultMap θ M J χ T)
    (hT' : IsMultMap θ M J χ T') (τ : D.what₂.Tau) (v v' : M.Vec) :
    ∃ c : ℂ, ∀ w w' : M.sm τ,
      ∫ g in 𝓕, star (T (Function.update v τ w) g) * T' (Function.update v' τ w') g ∂μ = c * ⟪w, w'⟫_ℂ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : SecondCountableTopology (GA D V) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).2.1
  have := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
  have := (M.ds τ).1
  obtain ⟨a, e, hs, hq⟩ := exists_continuousLinearMap_tens_update hT τ v
  obtain ⟨a', e', hs', hq'⟩ := exists_continuousLinearMap_tens_update hT' τ v'
  have hpt : Continuous fun g : Formalism.REAL.UJ (M.ε τ) => pt θ M τ (umat g) :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous
      ((continuous_const.matrix_mul continuous_umat).matrix_mul continuous_const)
      fun g => conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) g.2
  have hf : ∀ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)), IsAutFunSm θ V (a w) ∧ IsCuspFun V (a w) :=
    fun w hw => by rw [e ⟨w, mem_sm.2 hw⟩]; exact ⟨hT.aut _, hT.cusp _⟩
  have hf' : ∀ w ∈ smSub (gramAt D V τ) (trRep (M.σ τ) (M.fr τ)), IsAutFunSm θ V (a' w) ∧ IsCuspFun V (a' w) :=
    fun w hw => by rw [e' ⟨w, mem_sm.2 hw⟩]; exact ⟨hT'.aut _, hT'.cusp _⟩
  have hinv : ∀ (φ ψ : GA D V → ℂ) (k : GA D V), IsAutFunSm θ V φ → IsAutFunSm θ V ψ →
      ∫ x in 𝓕, star (rTr V k φ x) * rTr V k ψ x ∂μ = ∫ x in 𝓕, star (φ x) * ψ x ∂μ := fun φ ψ k hφ hψ =>
    (GlobalTheory.fundamentalDomain_integral_mul_right μ (GQ V) 𝓕 (fun x => star (φ x) * ψ x) k h𝓕 fun γ hγ g => by
      rw [hφ.left γ hγ, hψ.left γ hγ]).2
  obtain ⟨c, hc⟩ := GlobalTheory.T.schurLemma_equivariant_pair_boundedFunctions_alt _ _ _ _ _ _ (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 (GA D V)
    (μ.restrict 𝓕) (fun g x => x * pt θ M τ (umat g)) (continuous_snd.mul (hpt.comp continuous_fst)) a a'
    (fun w hw => ⟨(hf w hw).1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hf w hw).1 (hf w hw).2,
      fun g x => congrFun (hq _ g.2 w hw) x⟩) hs
    (fun w hw => ⟨(hf' w hw).1.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (hf' w hw).1 (hf' w hw).2,
      fun g x => congrFun (hq' _ g.2 w hw) x⟩) hs'
    (fun g hg u hu w hw => by rw [hq g hg u hu, hq g hg w hw]; exact hinv _ _ _ (hf u hu).1 (hf w hw).1)
    (fun g hg u hu w hw => by rw [hq' g hg u hu, hq' g hg w hw]; exact hinv _ _ _ (hf' u hu).1 (hf' w hw).1)
    (fun g hg u hu w hw => by rw [hq g hg u hu, hq' g hg w hw]; exact hinv _ _ _ (hf u hu).1 (hf' w hw).1)
  refine ⟨c, fun w w' => ?_⟩
  rw [← e, ← e']
  exact hc w (mem_sm.1 w.2) w' (mem_sm.1 w'.2)

theorem schurMult (hP : GlobalTheory.Published.CuspRapidDecay) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) :
    SchurMult θ M J χ μ 𝓕 := by
  intro hθ hμ h𝓕 T hT T' hT'
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT hT'
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_eq_const_mul_prod_inner_of_slotwise' D.what₂.Tau (fun τ => M.sm τ) (fun v v' => ∫ g in 𝓕, star (T v g) * T' v' g ∂μ)
    fun τ v v' => schur_multMap hP hθ hμ h𝓕 hT hT' τ v v'
  exact ⟨c, fun v v' => ⟨GlobalTheory.CuspDecay.integrableOn_star_mul hP GlobalTheory.Mem.VolFin.finVol hθ μ 𝓕 hμ h𝓕 (hT.aut v)
    (hT'.aut v') (hT'.cusp v'), hc v v'⟩⟩

theorem hcFinite_and_schurMult : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay →
    ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
      (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
      HCFinite θ M J χ ∧ SchurMult θ M J χ μ 𝓕 :=
  fun h h' _ _ _ _ _ _ _ μ 𝓕 => ⟨hcFinite h, schurMult h' μ 𝓕⟩

end GlobalTheory.MultFinite

end
