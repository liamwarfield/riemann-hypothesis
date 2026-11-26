module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HasAllKTypesOfClosureDiscreteSeriesCoefficients

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasDerivAtMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.TypeSum GlobalTheory.TypeSum.GrowthAtPlace Formalism.REAL

namespace GlobalTheory.TypeSum.GKCoef

theorem mem_kFin_iff {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Mx n → (H →L[ℂ] H)} {v : H} : v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ ↔ IsKFin ε σ v := by
  constructor
  · intro hv
    have : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ ≤ kfin ε σ := sSup_le fun W hW w hw => ⟨W, hW.1, hw, hW.2⟩
    exact this hv
  · rintro ⟨S, h1, h2, h3⟩
    exact (le_sSup (show S ∈ {W : Submodule ℂ H | FiniteDimensional ℂ W ∧ IsKStableOn ε σ W} from ⟨h1, h3⟩)) h2

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin V.rank → Bool}
  {σ : Mx V.rank → (H →L[ℂ] H)} {P : Mx V.rank} {T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)}

theorem map_K (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (h : Pᴴ * Jm ε * P = gramAt D V τ)
    (hT : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T) {k : Mx V.rank} (hk : k ∈ Kset ε)
    (v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) (hw : (w : H) = σ k v) (x : GA D V) {y : Mx V.rank} (hy : y ∈ UJset ε) :
    T w (x * atTau θ V τ (P⁻¹ * y * P)) = T v (x * atTau θ V τ (P⁻¹ * (y * k) * P)) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have hkU := K_le_UJ hk
  have e : P * (P⁻¹ * k * P) * P⁻¹ = k := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have := hT.mapK (P⁻¹ * k * P) (conj_inv_mem hP h hkU) (by rw [e]; exact hk) v w (by rw [e]; exact hw)
  rw [this, rTr, conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP h hy) (conj_inv_mem hP h hkU), mul_assoc]

theorem hasDerivAt_map (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (h : Pᴴ * Jm ε * P = gramAt D V τ)
    (hT : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T) (v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) {X : Mx V.rank}
    (hX : X ∈ lieSet ε) (hv : Sm ε σ (v : H)) (hw : (w : H) = dRep σ X v) (x : GA D V) {y : Mx V.rank}
    (hy : y ∈ UJset ε) :
    HasDerivAt (fun t : ℝ => T v (x * atTau θ V τ (P⁻¹ * (y * NormedSpace.exp (t • X)) * P)))
      (T w (x * atTau θ V τ (P⁻¹ * y * P))) 0 := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have hX' : P⁻¹ * X * P ∈ lieAt V τ := conj_lie hP h hX
  have e1 : ∀ t : ℝ, P * NormedSpace.exp (t • (P⁻¹ * X * P)) * P⁻¹ = NormedSpace.exp (t • X) := fun t => by
    rw [← conj_exp hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have hder : HasDerivAt (fun t : ℝ => σ (P * NormedSpace.exp (t • (P⁻¹ * X * P)) * P⁻¹) v) w 0 := by
    simp only [e1]; rw [hw]; exact hasDerivAt_dRep (G := Jm ε) hv hX
  have hTw := hT.mapLie _ hX' v w hder
  rw [hTw, Rder]
  have hdiff := differentiable_oneP (hT.aut v).smooth hX' (x * atTau θ V τ (P⁻¹ * y * P)) 0
  refine hdiff.hasDerivAt.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show T v (x * atTau θ V τ (P⁻¹ * (y * NormedSpace.exp (t • X)) * P)) =
    T v (x * atTau θ V τ (P⁻¹ * y * P) * oneP θ V τ (P⁻¹ * X * P) t)
  rw [conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP h hy) (conj_inv_mem hP h (exp_mem_UJ hX t)), conj_exp hP,
    ← mul_assoc]
  rfl

end GlobalTheory.TypeSum.GKCoef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesGKMapValuesEqGeneralisedCoefficien
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsGrowthExponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.TypeSum GlobalTheory.TypeSum.GrowthAtPlace Formalism.REAL

namespace GlobalTheory.TypeSum.GKCoef

theorem exists_growth_exponent : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau), IsInfFam (D := D) θ → GlobalTheory.Published.HarishChandraModules →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    IsDS ε lam σ → IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T → ∀ x : GA D V, ∃ N : ℕ, ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ, ∃ C : ℝ,
      ∀ y ∈ UJset ε, ‖T w (x * atTau θ V τ (P⁻¹ * y * P))‖ ≤ C * (1 + Formalism.REAL.hs y) ^ N := by
  intro D θ V τ hθ hHC H _ _ σ lam ε P T hDS hP hPG hT x
  haveI : CompleteSpace H := hDS.1
  have hstd : Std ε σ := std_of_isDS hHC hDS
  obtain ⟨Th, hTh⟩ := LinearMap.exists_extend T
  have eTh : ∀ v (hv : v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ), Th v = T ⟨v, hv⟩ := fun v hv => LinearMap.congr_fun hTh ⟨v, hv⟩
  have hkf : ∀ v, IsKFin ε σ v → v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ := fun v hv => mem_kFin_iff.2 hv
  have hDw : ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) → ∀ v, IsKFin ε σ v → IsKFin ε σ (Dw σ l v) := by
    intro l hl v hv
    induction l with
    | nil => exact hv
    | cons X l ih =>
      exact isKFin_dRep _ ε H σ hstd _ (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) X (hl X List.mem_cons_self)
  obtain ⟨u, hu, hu0⟩ := hstd.2.2.2.2
  obtain ⟨N, F, hF0, hFd, hFg⟩ := umg_atTau D θ hθ V τ (T ⟨u, hkf u hu⟩) (hT.aut _) ε P hP hPG x
  have hFeq : ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) → ∀ y ∈ UJset ε,
      F l y = Th (Dw σ l u) (x * atTau θ V τ (P⁻¹ * y * P)) := by
    intro l hl
    induction l with
    | nil => intro y hy; rw [hF0 y hy]; exact (congrFun (eTh u (hkf u hu)) _).symm
    | cons X l ih =>
      intro y hy
      have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
      have hX := hl X List.mem_cons_self
      have k1 := hDw l hl' u hu
      have k2 := hDw (X :: l) hl u hu
      have d1 := hFd l hl' X hX y hy
      have d2 := hasDerivAt_map hθ hP hPG hT ⟨Dw σ l u, hkf _ k1⟩ ⟨Dw σ (X :: l) u, hkf _ k2⟩ hX
        (hstd.2.2.1 _ k1) rfl x hy
      have d1' : HasDerivAt (fun t : ℝ => T ⟨Dw σ l u, hkf _ k1⟩
          (x * atTau θ V τ (P⁻¹ * (y * NormedSpace.exp (t • X)) * P))) (F (X :: l) y) 0 := by
        refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
        show _ = F l _
        rw [ih hl' _ (mul_mem_UJ hy (exp_mem_UJ hX t)), eTh _ (hkf _ k1)]
      rw [d1'.unique d2, eTh _ (hkf _ k2)]
  obtain ⟨Pr, hPr⟩ : ∃ Pr : H → Prop, ∀ w, Pr w ↔ ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) →
      ∃ C : ℝ, ∀ y ∈ UJset ε, ‖Th (Dw σ l w) (x * atTau θ V τ (P⁻¹ * y * P))‖ ≤ C * (1 + hs y) ^ N :=
    ⟨_, fun _ => Iff.rfl⟩
  have hSm : ∀ w, IsKFin ε σ w → Sm ε σ w := hstd.2.2.1
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ H, ∀ w, w ∈ W ↔ IsKFin ε σ w ∧ Pr w := by
    refine ⟨{ carrier := {w | IsKFin ε σ w ∧ Pr w}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ },
      fun _ => Iff.rfl⟩
    · rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
      refine ⟨mem_kfin.1 ((kfin ε σ).add_mem (mem_kfin.2 ha1) (mem_kfin.2 hb1)), (hPr _).2 fun l hl => ?_⟩
      obtain ⟨C1, h1⟩ := (hPr a).1 ha2 l hl
      obtain ⟨C2, h2⟩ := (hPr b).1 hb2 l hl
      refine ⟨C1 + C2, fun y hy => ?_⟩
      rw [Dw_add hstd.1 hl (hSm _ ha1) (hSm _ hb1), map_add (f := _), Pi.add_apply, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (h1 y hy) (h2 y hy))
    · have h0 : IsKFin ε σ (0 : H) := mem_kfin.1 (kfin ε σ).zero_mem
      refine ⟨h0, (hPr _).2 fun l hl => ⟨0, fun y hy => ?_⟩⟩
      have e := Dw_smul hstd.1 hl (0 : ℂ) (hSm _ h0)
      rw [zero_smul, zero_smul] at e
      rw [e, map_zero]
      simp
    · rintro c a ⟨ha1, ha2⟩
      refine ⟨mem_kfin.1 ((kfin ε σ).smul_mem c (mem_kfin.2 ha1)), (hPr _).2 fun l hl => ?_⟩
      obtain ⟨C, h1⟩ := (hPr a).1 ha2 l hl
      refine ⟨‖c‖ * C, fun y hy => ?_⟩
      rw [Dw_smul hstd.1 hl c (hSm _ ha1), map_smul, Pi.smul_apply, smul_eq_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_left (h1 y hy) (norm_nonneg c)).trans_eq (by ring)
  have hWk : ∀ w ∈ W, IsKFin ε σ w := fun w hw => ((hW w).1 hw).1
  have hWX : ∀ X, inG ε X → ∀ w ∈ W, dRep σ X w ∈ W := by
    intro X hXg w hw
    obtain ⟨hw1, hw2⟩ := (hW w).1 hw
    have hXl : X ∈ lieSet ε := hXg
    refine (hW _).2 ⟨isKFin_dRep _ ε H σ hstd w hw1 X hXl, (hPr _).2 fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := (hPr w).1 hw2 (l ++ [X]) (by
      intro Y hY
      rcases List.mem_append.1 hY with h | h
      · exact hl Y h
      · rw [List.mem_singleton] at h; rw [h]; exact hXl)
    refine ⟨C, fun y hy => ?_⟩
    have e : Dw σ l (dRep σ X w) = Dw σ (l ++ [X]) w := by rw [Dw_append]; rfl
    rw [e]
    exact hC y hy
  have hWK : ∀ k ∈ Kset ε, ∀ w ∈ W, σ k w ∈ W := by
    intro k hk w hw
    obtain ⟨hw1, hw2⟩ := (hW w).1 hw
    have hkU := K_le_UJ hk
    refine (hW _).2 ⟨isKFin_translate hw1 hk, (hPr _).2 fun l hl => ?_⟩
    have hl' : ∀ X ∈ l.map (fun X => k⁻¹ * X * k), X ∈ lieSet ε := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact conj_mem_lie (isUnit_Jm ε) hkU (hl Y hY)
    obtain ⟨C, hC⟩ := (hPr w).1 hw2 _ hl'
    have hv' := hDw _ hl' w hw1
    refine ⟨|C| * (1 + hs k) ^ N, fun y hy => ?_⟩
    rw [Dw_translate hstd.1 hkU (hSm _ hw1) hl, eTh _ (hkf _ (isKFin_translate hv' hk)),
      map_K hθ hP hPG hT hk ⟨_, hkf _ hv'⟩ _ rfl x hy, ← eTh _ (hkf _ hv')]
    refine (hC (y * k) (mul_mem_UJ hy hkU)).trans ?_
    have hp : (1 + hs (y * k)) ^ N ≤ (1 + hs y) ^ N * (1 + hs k) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith [hs_nonneg (y * k)]) (one_add_hs_mul_le y k) N
    calc C * (1 + hs (y * k)) ^ N ≤ |C| * (1 + hs (y * k)) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith [hs_nonneg (y * k)]) _)
      _ ≤ |C| * ((1 + hs y) ^ N * (1 + hs k) ^ N) := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
      _ = |C| * (1 + hs k) ^ N * (1 + hs y) ^ N := by ring
  have huW : u ∈ W := (hW u).2 ⟨hu, (hPr u).2 fun l hl => by
    obtain ⟨C, hC⟩ := hFg l hl
    exact ⟨C, fun y hy => by rw [← hFeq l hl y hy]; exact hC y hy⟩⟩
  have hW0 : W ≠ ⊥ := fun hb => hu0 ((Submodule.mem_bot ℂ).1 (hb ▸ huW))
  have hd := GlobalTheory.HCModIrred.dense_of_stable hHC hstd.1 hstd.2.1 hWk hWX hWK hW0
  refine ⟨N, fun w => ?_⟩
  have hmem := GlobalTheory.HCModIrred.mem_of_dense hstd hd hWk hWK (mem_kFin_iff.1 w.2)
  obtain ⟨C, hC⟩ := (hPr _).1 ((hW _).1 hmem).2 [] (by simp)
  refine ⟨C, fun y hy => ?_⟩
  have := hC y hy
  rwa [show Dw σ [] (w : H) = w from rfl, eTh _ w.2] at this

end GlobalTheory.TypeSum.GKCoef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesGKMapValuesEqGeneralisedCoefficien
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.TypeSum GlobalTheory.TypeSum.GrowthAtPlace Formalism.REAL

namespace GlobalTheory.TypeSum.GKCoef


open CoefLow in
theorem values_eq_coef : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau), IsInfFam (D := D) θ → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) (x : GA D V), ∃ ℓ : H →ₗ[ℂ] ℂ,
      Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ ∧ SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v : H) ∧
      ∀ y ∈ UJset ε, T v (x * atTau θ V τ (P⁻¹ * y * P)) = ℓ (σ y v) := by
  classical
  intro D θ V τ hθ hHC hCW H _ _ σ lam ε P T _ hDS hP h hT v x
  haveI : CompleteSpace H := hDS.1
  have hstd := std_of_isDS hHC hDS
  have hσ := hstd.1
  obtain ⟨N, hN⟩ := GlobalTheory.TypeSum.GKCoef.exists_growth_exponent θ V τ hθ hHC H σ lam ε P T hDS hP h hT x
  let F : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ → Mx V.rank → ℂ := fun w y => T w (x * atTau θ V τ (P⁻¹ * y * P))
  let f : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] Bd (Unit × UJset ε) :=
    { toFun := fun w => mkBd (fun i => F w i.2.1 / wt N i.2.1) (by
        obtain ⟨C, hC⟩ := hN w
        refine ⟨C, fun i => ?_⟩
        rw [norm_div, norm_wt, div_le_iff₀ (wt_pos _ _)]
        exact hC _ i.2.2)
      map_add' := fun v w => by ext i; simp [mkBd, F, add_div]; rfl
      map_smul' := fun c v => by ext i; simp [mkBd, F, mul_div_assoc] }
  obtain ⟨T₀, hT₀'⟩ := LinearMap.exists_extend f
  have hT₀ : ∀ (w : H) (hw : IsKFin ε σ w) (i : Unit × UJset ε),
      T₀ w i = F ⟨w, mem_kFin_iff.2 hw⟩ i.2.1 / wt N i.2.1 := fun w hw i => by
    have : T₀ w = f ⟨w, mem_kFin_iff.2 hw⟩ := LinearMap.congr_fun hT₀' ⟨w, mem_kFin_iff.2 hw⟩
    rw [this]; rfl
  let wcomp (c : (Unit × UJset ε) → ℂ) (B : ℝ) (hB0 : 0 ≤ B)
      (hB : ∀ i, ‖c i‖ ≤ B) (φ : (Unit × UJset ε) → (Unit × UJset ε)) :
      Bd (Unit × UJset ε) →L[ℂ] Bd (Unit × UJset ε) :=
    LinearMap.mkContinuous
      { toFun := fun F => mkBd (fun i => c i * F (φ i)) ⟨_, wcomp_le hB φ F⟩
        map_add' := fun F G => by ext i; simp [mkBd, mul_add]; rfl
        map_smul' := fun a F => by ext i; simp [mkBd]; ring } B
      fun F => lp.norm_le_of_forall_le (by positivity) (wcomp_le hB φ F)
  let rt (h : Mx V.rank) : Bd (Unit × UJset ε) →L[ℂ] Bd (Unit × UJset ε) :=
    if hh : h ∈ UJset ε then
      wcomp (fun i => (wt N (i.2.1 * h) : ℂ) / wt N i.2.1) (wt N h) (wt_pos N h).le
        (fun i => by
          rw [norm_div, norm_wt, norm_wt, div_le_iff₀' (wt_pos _ _)]
          exact wt_mul_le _ _ _) fun i => (i.1, ⟨i.2.1 * h, mul_mem_UJ i.2.2 hh⟩)
    else 0
  have rt_apply {h : Mx V.rank} (hh : h ∈ UJset ε) (F : Bd (Unit × UJset ε)) (i : Unit × UJset ε) :
      rt h F i = (wt N (i.2.1 * h) : ℂ) / wt N i.2.1 * F (i.1, ⟨i.2.1 * h, mul_mem_UJ i.2.2 hh⟩) := by
    simp only [rt, dif_pos hh]
    rfl
  have modRep_rt : ModRep ε rt := by
    refine ⟨?_, fun a ha b hb => ?_, 1, N, fun g hg => ?_⟩
    · ext F i
      rw [rt_apply (one_mem_UJ ε)]
      simp [div_self (wt_ne _ _)]
    · ext F i
      rw [ContinuousLinearMap.comp_apply, rt_apply (mul_mem_UJ ha hb), rt_apply ha, rt_apply hb]
      simp only [mul_assoc]
      have := wt_ne N (i.2.1 * a)
      field_simp
    · simp only [rt, dif_pos hg, one_mul]
      dsimp only [wcomp]
      exact LinearMap.mkContinuous_norm_le _ (wt_pos N g).le _
  have key : ∀ (w : H) (hw : IsKFin ε σ w), ∀ y ∈ UJset ε, ∀ i : Unit × UJset ε,
      rt y (T₀ w) i = F ⟨w, mem_kFin_iff.2 hw⟩ (i.2.1 * y) / wt N i.2.1 := by
    intro w hw y hy i
    rw [rt_apply hy, hT₀ w hw]
    have := wt_ne N (i.2.1 * y)
    field_simp

  have hder : ∀ (w : H) (hw : IsKFin ε σ w) {X : Mx V.rank} (hX : X ∈ lieSet ε) {g : Mx V.rank} (hg : g ∈ UJset ε)
      (s : ℝ), HasDerivAt (fun t : ℝ => F ⟨w, mem_kFin_iff.2 hw⟩ (g * NormedSpace.exp (t • X)))
        (F ⟨dRep σ X w, mem_kFin_iff.2 (isKFin_dRep _ ε H σ hstd w hw X hX)⟩ (g * NormedSpace.exp (s • X))) s := by
    intro w hw X hX g hg s
    have hs := mul_mem_UJ hg (exp_mem_UJ hX s)
    have h1 := hasDerivAt_map hθ hP h hT ⟨w, mem_kFin_iff.2 hw⟩
      ⟨dRep σ X w, mem_kFin_iff.2 (isKFin_dRep _ ε H σ hstd w hw X hX)⟩ hX (hstd.2.2.1 w hw) rfl x hs
    have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
    refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
    show F _ _ = F _ _
    simp only [F]
    rw [mul_assoc g (NormedSpace.exp (s • X)), ← exp_add_smul, add_sub_cancel]
  obtain ⟨T', hT1, hT2, S, C, hS, hC⟩ := GlobalTheory.TypeSum.casselmanWallach_banach hCW V.rank ε H σ hstd _ _
    modRep_rt T₀
    (fun k hk w hw => by
      ext i
      rw [key w hw k (K_le_UJ hk), hT₀ _ (isKFin_translate hw hk)]
      congr 1
      exact map_K hθ hP h hT hk _ _ rfl x i.2.2)
    (fun X hX w hw => by
      have hw1 := isKFin_dRep _ ε H σ hstd w hw X hX
      have hw2 := isKFin_dRep _ ε H σ hstd _ hw1 X hX
      obtain ⟨C2, hC2⟩ := hN ⟨_, mem_kFin_iff.2 hw2⟩
      obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).bddAbove_image
        ((continuous_wt N).comp (continuous_exp_smul X)).continuousOn)
      refine hasDerivAt_of_sq (K := |C2| * |B|) fun t ht => lp.norm_le_of_forall_le (by positivity) fun i => ?_
      have e : (t • T₀ (dRep σ X w)) i = t • T₀ (dRep σ X w) i := rfl
      rw [lp.coeFn_sub, lp.coeFn_sub, Pi.sub_apply, Pi.sub_apply, e, key w hw _ (exp_mem_UJ hX _),
        key w hw _ (exp_mem_UJ hX _), hT₀ _ hw1, zero_smul, NormedSpace.exp_zero, mul_one,
        ← smul_div_assoc, ← sub_div, ← sub_div, norm_div, norm_wt, div_le_iff₀ (wt_pos _ _)]
      have tb := taylor_two (hder w hw hX i.2.2) (hder _ hw1 hX i.2.2) (K := |C2| * |B| * wt N i.2.1)
        (fun s hs => by
          refine (hC2 _ (mul_mem_UJ i.2.2 (exp_mem_UJ hX s))).trans ?_
          have w1 := wt_mul_le N i.2.1 (NormedSpace.exp (s • X))
          have w2 : wt N (NormedSpace.exp (s • X)) ≤ |B| := (hB ⟨s, abs_le.1 hs, rfl⟩).trans (le_abs_self B)
          have w3 := wt_pos N i.2.1
          have w4 := wt_pos N (i.2.1 * NormedSpace.exp (s • X))
          change C2 * wt N _ ≤ _
          calc C2 * wt N (i.2.1 * NormedSpace.exp (s • X)) ≤ |C2| * (wt N i.2.1 * |B|) :=
                mul_le_mul (le_abs_self _) (w1.trans (mul_le_mul_of_nonneg_left w2 w3.le)) w4.le (abs_nonneg _)
            _ = _ := by ring) ht
      simp only [zero_smul, NormedSpace.exp_zero, mul_one] at tb
      calc _ ≤ |C2| * |B| * wt N i.2.1 * t ^ 2 := tb
        _ = _ := by ring)
  let ℓ : H →ₗ[ℂ] ℂ :=
    { toFun := fun w => wt N (1 : Mx V.rank) * T' w ((), ⟨1, one_mem_UJ ε⟩)
      map_add' := fun a b => by simp [mul_add]
      map_smul' := fun c a => by simp; ring }
  have hvK : IsKFin ε σ (v : H) := mem_kFin_iff.1 v.2
  refine ⟨ℓ, ⟨S, wt N (1 : Mx V.rank) * |C|, hS, fun w hw => ?_⟩, hstd.2.2.1 _ hvK, fun y hy => ?_⟩
  · change ‖(wt N (1 : Mx V.rank) : ℂ) * T' w ((), ⟨1, one_mem_UJ ε⟩)‖ ≤ _
    rw [norm_mul, norm_wt, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((apply_le _ _).trans ((hC w hw).trans ?_)) (wt_pos _ _).le
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (sobNorm_nonneg _ _ _)
  · change _ = (wt N (1 : Mx V.rank) : ℂ) * T' (σ y v) ((), ⟨1, one_mem_UJ ε⟩)
    rw [hT2 y hy _ (hstd.2.2.1 _ hvK), hT1 _ hvK, key _ hvK y hy]
    have := wt_ne N (1 : Mx V.rank)
    simp only [one_mul, F]
    field_simp

end GlobalTheory.TypeSum.GKCoef

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesGKMapValuesEqGeneralisedCoefficienStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_gKMap_values_eq_generalisedCoefficients : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau), IsInfFam (D := D) θ → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) (x : GA D V), ∃ ℓ : H →ₗ[ℂ] ℂ,
      Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ ∧ SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v : H) ∧
      ∀ y ∈ UJset ε, T v (x * atTau θ V τ (P⁻¹ * y * P)) = ℓ (σ y v) := by
  first | exact @GlobalTheory.TypeSum.GKCoef.values_eq_coef | exact GlobalTheory.TypeSum.GKCoef.values_eq_coef | (intros; apply GlobalTheory.TypeSum.GKCoef.values_eq_coef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MatrixCoefficientFrameChangeDiscreteSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MatrixCoefficientFrameChangeDiscreteSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory Matrix Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum

namespace GlobalTheory.TypeSum.FrameChange

variable {n : ℕ} {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Mx n → (H →L[ℂ] H)} {σ' : Mx n → (H' →L[ℂ] H')}

private theorem one_mem_UJset' : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * 1 = Formalism.REAL.Jm ε
  simp

private theorem mul_mem_UH_Hpk' {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) :
    a * b ∈ UJset ε := by
  have ha' : aᴴ * Formalism.REAL.Jm ε * a = Formalism.REAL.Jm ε := ha
  have hb' : bᴴ * Formalism.REAL.Jm ε * b = Formalism.REAL.Jm ε := hb
  show (a * b)ᴴ * Formalism.REAL.Jm ε * (a * b) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc _ = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha', hb']

private theorem exp_smul_mem_UJset' {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ lieSet ε) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UJset ε := by
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJinv : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Formalism.REAL.Jm ε) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hJJ)
  have hXh : Xᴴ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by
    have h1 : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := eq_neg_of_add_eq_zero_left hX'
    calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -(Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) := by rw [h1, Matrix.neg_mul]
  have hYh : (t • X)ᴴ = Formalism.REAL.Jm ε * (-(t • X)) * (Formalism.REAL.Jm ε)⁻¹ := by
    rw [Matrix.conjTranspose_smul, star_trivial, hXh, hJinv]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  have hEu : IsUnit (NormedSpace.exp (t • X)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  show (NormedSpace.exp (t • X))ᴴ * Formalism.REAL.Jm ε * NormedSpace.exp (t • X) = Formalism.REAL.Jm ε
  rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hJu, hJinv, Matrix.exp_neg]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), hJJ, Matrix.one_mul,
    Matrix.nonsing_inv_mul _ hEu, Matrix.mul_one]

theorem prod_mem {k : ℕ} {Xs : Fin k → Mx n} (hX : ∀ i, Xs i ∈ lieSet ε) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ UJset ε := by
  have key : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ a ∈ l, a ∈ UJset ε) → l.prod ∈ UJset ε := by
    intro l
    induction l with
    | nil => intro _; simpa using (one_mem_UJset' (ε := ε))
    | cons a l ih =>
      intro h
      rw [List.prod_cons]
      exact mul_mem_UH_Hpk' (h a (by simp)) (ih fun b hb => h b (by simp [hb]))
  apply key
  intro a ha
  rw [List.mem_ofFn] at ha
  obtain ⟨i, rfl⟩ := ha
  exact exp_smul_mem_UJset' (hX i) (t i)

def toReal (U : H' ≃ₗᵢ[ℂ] H) : H' ≃L[ℝ] H :=
  { U.toLinearEquiv.restrictScalars ℝ with
    continuous_toFun := U.continuous
    continuous_invFun := U.symm.continuous }

theorem toReal_apply (U : H' ≃ₗᵢ[ℂ] H) (x : H') : toReal U x = U x := rfl

theorem symm_intertwines (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ w, U (σ' g w) = σ g (U w)) :
    ∀ g ∈ UJset ε, ∀ w, U.symm (σ g w) = σ' g (U.symm w) := by
  intro g hg w
  apply U.injective
  rw [hU g hg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]

theorem smooth_map (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ w, U (σ' g w) = σ g (U w)) {w : H'}
    (hw : SmoothVec (lieSet ε) σ' w) : SmoothVec (lieSet ε) σ (U w) := by
  intro k Xs hXs
  have h := hw k Xs hXs
  have e : (fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (U w)) =
      fun t => (toReal U) (σ' ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) w) := by
    funext t
    rw [toReal_apply, hU _ (prod_mem hXs t)]
  rw [e]
  exact (toReal U).contDiff.comp h

private theorem deriv_continuousLinearMap_comp_zero {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] (A : E →L[ℂ] E') (B : E' →L[ℂ] E) (hBA : ∀ x, B (A x) = x)
    (f : ℝ → E) : deriv (fun t => A (f t)) 0 = A (deriv f 0) := by
  by_cases hf : DifferentiableAt ℝ f 0
  · exact ((A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf.hasDerivAt).deriv
  · have hg : ¬ DifferentiableAt ℝ (fun t => A (f t)) 0 := by
      intro h
      apply hf
      have h2 := (B.restrictScalars ℝ).differentiableAt.comp (0 : ℝ) h
      have heq : f = (B.restrictScalars ℝ) ∘ fun t => A (f t) := by
        funext t
        simp [hBA]
      rw [heq]
      exact h2
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hg, map_zero]

theorem dRep_map (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ w, U (σ' g w) = σ g (U w)) {X : Mx n}
    (hX : X ∈ lieSet ε) (w : H') : dRep σ X (U w) = U (dRep σ' X w) := by
  show deriv (fun t : ℝ => σ (NormedSpace.exp (t • X)) (U w)) 0 =
    U (deriv (fun t : ℝ => σ' (NormedSpace.exp (t • X)) w) 0)
  have e : (fun t : ℝ => σ (NormedSpace.exp (t • X)) (U w)) =
      fun t => (U.toContinuousLinearEquiv : H' →L[ℂ] H) (σ' (NormedSpace.exp (t • X)) w) := by
    funext t
    exact (hU _ (exp_smul_mem_UJset' hX t) w).symm
  rw [e]
  exact deriv_continuousLinearMap_comp_zero _ (U.symm.toContinuousLinearEquiv : H →L[ℂ] H') (fun x => U.symm_apply_apply x) _

theorem word_map (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ w, U (σ' g w) = σ g (U w)) (l : List (Mx n))
    (hl : ∀ X ∈ l, X ∈ lieSet ε) (w : H') : l.foldr (dRep σ) (U w) = U (l.foldr (dRep σ') w) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [List.foldr_cons]
    rw [ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)), dRep_map U hU (hl X (by simp))]

theorem sobNorm_map (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ w, U (σ' g w) = σ g (U w))
    {S : List (List (Mx n))} (hS : ∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) (w : H') :
    (S.map fun l => ‖l.foldr (dRep σ) (U w)‖).sum = (S.map fun l => ‖l.foldr (dRep σ') w‖).sum := by
  congr 1
  apply List.map_congr_left
  intro l hl
  rw [word_map U hU l (hS l hl), LinearIsometryEquiv.norm_map]

theorem sobCont_map (U : H' ≃ₗᵢ[ℂ] H) (hU : ∀ g ∈ UJset ε, ∀ w, U (σ' g w) = σ g (U w)) {ℓ : H' →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ' ℓ) :
    Sobolev₂ (lieSet ε) σ (ℓ ∘ₗ (U.symm.toLinearEquiv : H →ₗ[ℂ] H')) := by
  obtain ⟨S, C, hS, hb⟩ := hℓ
  refine ⟨S, C, hS, fun w hw => ?_⟩
  have hw' : SmoothVec (lieSet ε) σ' (U.symm w) := smooth_map U.symm (symm_intertwines U hU) hw
  have h1 := hb (U.symm w) hw'
  have e := sobNorm_map U hU hS (U.symm w)
  rw [LinearIsometryEquiv.apply_symm_apply] at e
  show ‖ℓ (U.symm w)‖ ≤ _
  rw [e]
  exact h1

private theorem mul_inv_mem_UJset_of_conjTranspose_Jm_eq {P P' G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) (hG' : P'ᴴ * Formalism.REAL.Jm ε * P' = G) : P' * P⁻¹ ∈ UJset ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).mp hP
  show (P' * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P' * P⁻¹) = Formalism.REAL.Jm ε
  rw [Matrix.conjTranspose_mul]
  calc _ = (P⁻¹)ᴴ * (P'ᴴ * Formalism.REAL.Jm ε * P') * P⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hG', hG]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
      rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [Matrix.mul_nonsing_inv _ hd]; simp

private theorem mul_mul_mem_lieSet_of_mem_UJset_of_mem_lieSet {Q R X : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∈ UJset ε) (hR : R ∈ UJset ε)
    (hQR : Q * R = 1) (hRQ : R * Q = 1) (hX : X ∈ lieSet ε) : R * X * Q ∈ lieSet ε := by
  have hQ' : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.REAL.Jm ε := hQ
  have hR' : Rᴴ * Formalism.REAL.Jm ε * R = Formalism.REAL.Jm ε := hR
  have hX' : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have e1 : Rᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Q := by
    calc Rᴴ * Formalism.REAL.Jm ε = Rᴴ * Formalism.REAL.Jm ε * (R * Q) := by rw [hRQ, Matrix.mul_one]
      _ = (Rᴴ * Formalism.REAL.Jm ε * R) * Q := by simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * Q := by rw [hR']
  have e2 : Formalism.REAL.Jm ε * R = Qᴴ * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * R = (Qᴴ * Formalism.REAL.Jm ε * Q) * R := by rw [hQ']
      _ = Qᴴ * Formalism.REAL.Jm ε * (Q * R) := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * Formalism.REAL.Jm ε := by rw [hQR, Matrix.mul_one]
  show (R * X * Q)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (R * X * Q) = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc _ = Qᴴ * (Xᴴ * (Rᴴ * Formalism.REAL.Jm ε)) + (Formalism.REAL.Jm ε * R) * X * Q := by
        simp only [Matrix.mul_assoc]
    _ = Qᴴ * (Xᴴ * (Formalism.REAL.Jm ε * Q)) + Qᴴ * Formalism.REAL.Jm ε * X * Q := by rw [e1, e2]
    _ = Qᴴ * (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X) * Q := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

private theorem mul_list_prod_mul_eq_prod_map_conj {Q R : Matrix (Fin n) (Fin n) ℂ} (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : R * l.prod * Q = (l.map fun a => R * a * Q).prod := by
  induction l with
  | nil => simp [hRQ]
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q R, hQR, Matrix.one_mul]

private theorem mul_exp_smul_mul_eq_exp_smul_conj {Q R : Matrix (Fin n) (Fin n) ℂ} (hQR : Q * R = 1)
    (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    R * NormedSpace.exp (t • X) * Q = NormedSpace.exp (t • (R * X * Q)) := by
  have hRi : R⁻¹ = Q := Matrix.inv_eq_left_inv hQR
  have hRu : IsUnit R := (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hQR)
  rw [show t • (R * X * Q) = R * (t • X) * R⁻¹ by rw [hRi, Matrix.mul_smul, Matrix.smul_mul],
    Matrix.exp_conj _ _ hRu, hRi]

private theorem mul_prod_ofFn_exp_smul_mul_eq_prod_exp_smul_conj {Q R : Matrix (Fin n) (Fin n) ℂ} (hQR : Q * R = 1) (hRQ : R * Q = 1) {k : ℕ}
    (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (t : Fin k → ℝ) :
    R * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * Q =
      (List.ofFn fun i => NormedSpace.exp (t i • (R * Xs i * Q))).prod := by
  rw [mul_list_prod_mul_eq_prod_map_conj hQR hRQ, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => mul_exp_smul_mul_eq_exp_smul_conj hQR (Xs i) (t i)))

private theorem smoothVec_translate_of_smoothVec (hσ : IsURepOn (UJset ε) σ) {Q R : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ UJset ε) (hR : R ∈ UJset ε) (hQR : Q * R = 1) (hRQ : R * Q = 1) {v : H}
    (hv : SmoothVec (lieSet ε) σ v) : SmoothVec (lieSet ε) σ (σ Q v) := by
  intro k Xs hXs
  have hXs' : ∀ i, R * Xs i * Q ∈ lieSet ε := fun i => mul_mul_mem_lieSet_of_mem_UJset_of_mem_lieSet hQ hR hQR hRQ (hXs i)
  have h := hv k (fun i => R * Xs i * Q) hXs'
  have e : (fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (σ Q v)) =
      fun t => ((σ Q).restrictScalars ℝ)
        (σ ((List.ofFn fun i => NormedSpace.exp (t i • (R * Xs i * Q))).prod) v) := by
    funext t
    rw [← mul_prod_ofFn_exp_smul_mul_eq_prod_exp_smul_conj hQR hRQ Xs t]
    have hA := prod_mem hXs t
    set A := (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod with hAdef
    have hB := mul_mem_UH_Hpk' (mul_mem_UH_Hpk' hR hA) hQ
    have hm : A * Q = Q * (R * A * Q) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQR, Matrix.one_mul]
    calc σ A (σ Q v) = σ (A * Q) v := by rw [hσ.1.2 _ hA _ hQ]; rfl
      _ = σ (Q * (R * A * Q)) v := by rw [hm]
      _ = σ Q (σ (R * A * Q) v) := by rw [hσ.1.2 _ hQ _ hB]; rfl
  rw [e]
  exact ((σ Q).restrictScalars ℝ).contDiff.comp h

private theorem dRep_apply_translate_eq_translate_dRep_conj (hσ : IsURepOn (UJset ε) σ) {Q R : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ UJset ε) (hR : R ∈ UJset ε) (hQR : Q * R = 1) (hRQ : R * Q = 1) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieSet ε) (x : H) : dRep σ X (σ Q x) = σ Q (dRep σ (R * X * Q) x) := by
  show deriv (fun t : ℝ => σ (NormedSpace.exp (t • X)) (σ Q x)) 0 =
    σ Q (deriv (fun t : ℝ => σ (NormedSpace.exp (t • (R * X * Q))) x) 0)
  have e : (fun t : ℝ => σ (NormedSpace.exp (t • X)) (σ Q x)) =
      fun t => σ Q (σ (NormedSpace.exp (t • (R * X * Q))) x) := by
    funext t
    have hA := exp_smul_mem_UJset' hX t
    have hB := mul_mem_UH_Hpk' (mul_mem_UH_Hpk' hR hA) hQ
    have hm : NormedSpace.exp (t • X) * Q = Q * (R * NormedSpace.exp (t • X) * Q) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQR, Matrix.one_mul]
    rw [← mul_exp_smul_mul_eq_exp_smul_conj hQR X t]
    calc σ (NormedSpace.exp (t • X)) (σ Q x) = σ (NormedSpace.exp (t • X) * Q) x := by
          rw [hσ.1.2 _ hA _ hQ]; rfl
      _ = σ (Q * (R * NormedSpace.exp (t • X) * Q)) x := by rw [hm]
      _ = σ Q (σ (R * NormedSpace.exp (t • X) * Q) x) := by rw [hσ.1.2 _ hQ _ hB]; rfl
  rw [e]
  refine deriv_continuousLinearMap_comp_zero (σ Q) (σ R) (fun y => ?_) _
  rw [show σ R (σ Q y) = ((σ R).comp (σ Q)) y from rfl, ← hσ.1.2 _ hR _ hQ, hRQ, hσ.1.1]
  rfl

private theorem foldr_dRep_translate_eq_translate_foldr_conj (hσ : IsURepOn (UJset ε) σ) {Q R : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ UJset ε) (hR : R ∈ UJset ε) (hQR : Q * R = 1) (hRQ : R * Q = 1)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hl : ∀ X ∈ l, X ∈ lieSet ε) (x : H) :
    l.foldr (dRep σ) (σ Q x) = σ Q ((l.map fun X => R * X * Q).foldr (dRep σ) x) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [List.foldr_cons, List.map_cons]
    rw [ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)),
      dRep_apply_translate_eq_translate_dRep_conj hσ hQ hR hQR hRQ (hl X (by simp))]

private theorem sobCont_comp_translate_of_sobCont (hσ : IsURepOn (UJset ε) σ) {Q R : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ UJset ε) (hR : R ∈ UJset ε) (hQR : Q * R = 1) (hRQ : R * Q = 1) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) : Sobolev₂ (lieSet ε) σ (ℓ ∘ₗ (σ Q : H →ₗ[ℂ] H)) := by
  obtain ⟨S, C, hS, hb⟩ := hℓ
  refine ⟨S.map (List.map fun X => R * X * Q), C, ?_, fun w hw => ?_⟩
  · intro l hl X hX
    obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hl
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
    exact mul_mul_mem_lieSet_of_mem_UJset_of_mem_lieSet hQ hR hQR hRQ (hS l₀ hl₀ Y hY)
  · have h1 := hb (σ Q w) (smoothVec_translate_of_smoothVec hσ hQ hR hQR hRQ hw)
    have e : (S.map fun l => ‖l.foldr (dRep σ) (σ Q w)‖).sum =
        ((S.map (List.map fun X => R * X * Q)).map fun l => ‖l.foldr (dRep σ) w‖).sum := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro l hl
      simp only [Function.comp_apply]
      rw [foldr_dRep_translate_eq_translate_foldr_conj hσ hQ hR hQR hRQ l (hS l hl), hσ.2.1 Q hQ]
    show ‖ℓ (σ Q w)‖ ≤ _
    rw [← e]
    exact h1

theorem coef_frame_change : GlobalTheory.Published.DiscreteSeriesUpqUnique → ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ),
    Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsDS ε lam σ → IsDS ε lam σ' →
    ∀ (P P' G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → IsUnit P' → Pᴴ * Formalism.REAL.Jm ε * P = G →
      P'ᴴ * Formalism.REAL.Jm ε * P' = G →
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (ℓ : H' →ₗ[ℂ] ℂ) (v : H'), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ' ℓ →
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ' v → (∀ y ∈ UJset ε, F (P'⁻¹ * y * P') = ℓ (σ' y v)) →
    ∃ (ℓ' : H →ₗ[ℂ] ℂ) (v' : H), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ' ∧
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ v' ∧ ∀ y ∈ UJset ε, F (P⁻¹ * y * P) = ℓ' (σ y v') := by
  intro hDS n ε lam hlam H H' _ _ _ _ σ σ' hσ hσ' P P' G hP hP' hG hG' F ℓ v hℓ hv hF
  obtain ⟨U, hU⟩ := hDS n ε lam hlam H' H σ' σ hσ' hσ
  have hdP := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hdP' := (Matrix.isUnit_iff_isUnit_det P').mp hP'
  have hQ : P' * P⁻¹ ∈ UJset ε := mul_inv_mem_UJset_of_conjTranspose_Jm_eq hP hG hG'
  have hR : P * P'⁻¹ ∈ UJset ε := mul_inv_mem_UJset_of_conjTranspose_Jm_eq hP' hG' hG
  have hQR : P' * P⁻¹ * (P * P'⁻¹) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹ P, Matrix.nonsing_inv_mul _ hdP, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hdP']
  have hRQ : P * P'⁻¹ * (P' * P⁻¹) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P'⁻¹ P', Matrix.nonsing_inv_mul _ hdP', Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hdP]
  have hσ'U : IsURepOn (UJset ε) σ' := hσ'.2.2.1
  refine ⟨(ℓ ∘ₗ (σ' (P' * P⁻¹) : H' →ₗ[ℂ] H')) ∘ₗ (U.symm.toLinearEquiv : H →ₗ[ℂ] H'),
    U (σ' (P * P'⁻¹) v), ?_, ?_, ?_⟩
  · exact sobCont_map U hU (sobCont_comp_translate_of_sobCont hσ'U hQ hR hQR hRQ hℓ)
  · exact smooth_map U hU (smoothVec_translate_of_smoothVec hσ'U hR hQ hRQ hQR hv)
  · intro y hy
    have hy' : P' * P⁻¹ * y * (P * P'⁻¹) ∈ UJset ε := mul_mem_UH_Hpk' (mul_mem_UH_Hpk' hQ hy) hR
    have hm : P'⁻¹ * (P' * P⁻¹ * y * (P * P'⁻¹)) * P' = P⁻¹ * y * P := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P'⁻¹ P', Matrix.nonsing_inv_mul _ hdP', Matrix.one_mul, Matrix.mul_one]
    rw [← hm, hF _ hy']
    show ℓ (σ' (P' * P⁻¹ * y * (P * P'⁻¹)) v) =
      ℓ (σ' (P' * P⁻¹) (U.symm (σ y (U (σ' (P * P'⁻¹) v)))))
    rw [symm_intertwines U hU y hy, LinearIsometryEquiv.symm_apply_apply,
      hσ'U.1.2 _ (mul_mem_UH_Hpk' hQ hy) _ hR, hσ'U.1.2 _ hQ _ hy]
    rfl

end GlobalTheory.TypeSum.FrameChange

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.MatrixCoefficientFrameChangeDiscreteSeriesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_frame_change_discrete_series : GlobalTheory.Published.DiscreteSeriesUpqUnique → ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ),
    Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsDS ε lam σ → IsDS ε lam σ' →
    ∀ (P P' G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → IsUnit P' → Pᴴ * Formalism.REAL.Jm ε * P = G →
      P'ᴴ * Formalism.REAL.Jm ε * P' = G →
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (ℓ : H' →ₗ[ℂ] ℂ) (v : H'), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ' ℓ →
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ' v → (∀ y ∈ UJset ε, F (P'⁻¹ * y * P') = ℓ (σ' y v)) →
    ∃ (ℓ' : H →ₗ[ℂ] ℂ) (v' : H), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ' ∧
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ v' ∧ ∀ y ∈ UJset ε, F (P⁻¹ * y * P) = ℓ' (σ y v') := by
  first | exact @GlobalTheory.TypeSum.FrameChange.coef_frame_change | exact GlobalTheory.TypeSum.FrameChange.coef_frame_change | (intros; apply GlobalTheory.TypeSum.FrameChange.coef_frame_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeries
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClosureSeries

open GlobalTheory.TypeSum

theorem coef_of_gkMap : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau), IsInfFam (D := D) θ → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) (x : GA D V), ∃ ℓ : H →ₗ[ℂ] ℂ,
      Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ ∧ SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v : H) ∧
      ∀ y ∈ UJset ε, T v (x * atTau θ V τ (P⁻¹ * y * P)) = ℓ (σ y v) := GlobalTheory.T.discreteSeries_gKMap_values_eq_generalisedCoefficients

theorem coef_transport : GlobalTheory.Published.DiscreteSeriesUpqUnique → ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ),
    Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsDS ε lam σ → IsDS ε lam σ' →
    ∀ (P P' G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → IsUnit P' → Pᴴ * Formalism.REAL.Jm ε * P = G →
      P'ᴴ * Formalism.REAL.Jm ε * P' = G →
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (ℓ : H' →ₗ[ℂ] ℂ) (v : H'), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ' ℓ →
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ' v → (∀ y ∈ UJset ε, F (P'⁻¹ * y * P') = ℓ (σ' y v)) →
    ∃ (ℓ' : H →ₗ[ℂ] ℂ) (v' : H), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ' ∧
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ v' ∧ ∀ y ∈ UJset ε, F (P⁻¹ * y * P) = ℓ' (σ y v') := GlobalTheory.T.matrix_coefficient_frame_change_discrete_series

theorem closure_model : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsDS ε lam σ → ∀ f : Matrix (Fin n) (Fin n) ℂ → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v j)) ∧
        ∀ y ∈ C, y ∈ UJset ε → ‖f y - ∑ j, ℓ j (σ y (v j))‖ < δ) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.TypeSum.lieOf (Formalism.REAL.Jm ε)) (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ f := GlobalTheory.T.hasAllKTypes_of_closure_discreteSeriesCoefficients

theorem isClosed_UJset {n : ℕ} (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  have : UJset ε = {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε} := rfl
  rw [this]
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem continuous_mul_left_GA {D : D7} (V : HSp D) (x : GA D V) : Continuous fun y : GA D V => x * y := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := inferInstance
  refine continuous_induced_rng.2 ?_
  exact (continuous_const_mul _).comp continuous_induced_dom

theorem closure_to_series : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau) (S : SPar) (φ : GA D V → ℂ),
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.DiscreteSeriesUpqUnique → GlobalTheory.Published.HarishChandraModules →
    GlobalTheory.Published.CasselmanWallach → IsInfFam (D := D) θ → V.SigOK →
    GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S → IsAutFunSm θ V φ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S φ → IsTypeAt θ V τ S φ := by
  intro D θ V τ S φ hEx hUn hHC hCW hθ hV hS hφ hT
  obtain ⟨lam₀, ε₀, hE₀, hP₀, hp, hq⟩ := hS
  obtain ⟨H, i1, i2, σ, hc, hnt, hU, hI, hL2, hK, hmin⟩ := hEx _ ε₀ lam₀ hP₀
  have hσ : IsDS ε₀ lam₀ σ := ⟨hc, hnt, hU, hI, hL2, hK, hmin⟩
  obtain ⟨P, hPu, hPG⟩ := GlobalTheory.Published.exists_frame_of_hasSignature (hV (tauE D τ)) ε₀ hp hq
  refine ⟨H, i1, i2, σ, lam₀, ε₀, P, hE₀, hσ, hPu, hPG, fun x => ?_⟩

  have hfin : ∀ ψ ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.finPartOfType θ V τ S, ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H),
      (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε₀) σ (ℓ j)) ∧ (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε₀) σ (v j)) ∧
      ∀ y ∈ UJset ε₀, ψ (x * atTau θ V τ (P⁻¹ * y * P)) = ∑ j, ℓ j (σ y (v j)) := by
    intro ψ hψ
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.finPartOfType, sSup_eq_iSup'] at hψ
    refine Submodule.iSup_induction (motive := fun ψ : GA D V → ℂ => ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ))
      (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε₀) σ (ℓ j)) ∧
      (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε₀) σ (v j)) ∧
      ∀ y ∈ UJset ε₀, ψ (x * atTau θ V τ (P⁻¹ * y * P)) = ∑ j, ℓ j (σ y (v j))) _ hψ ?_ ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0,
      fun y _ => by simp⟩ ?_
    · rintro ⟨W, H', j1, j2, σ', lam, ε, P', T, hE, hHC', hD', hP', hJ', hGK, rfl⟩ ψ ⟨w, rfl⟩
      obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE hE₀
      obtain ⟨ℓ, hℓ, hv, he⟩ := coef_of_gkMap θ V τ hθ hHC hCW H' σ' lam ε P' T hHC' hD' hP' hJ' hGK w x
      obtain ⟨ℓ', v', hℓ', hv', he'⟩ := coef_transport hUn _ ε lam hHC' H H' σ σ' hσ hD' P P' _ hPu hP' hPG hJ'
        (fun y => T w (x * atTau θ V τ y)) ℓ w hℓ hv he
      exact ⟨1, fun _ => ℓ', fun _ => v', fun _ => hℓ', fun _ => hv', fun y hy => by simpa using he' y hy⟩
    · rintro a b ⟨m, ℓ, v, h1, h2, h3⟩ ⟨m', ℓ', v', h1', h2', h3'⟩
      refine ⟨m + m', Fin.append ℓ ℓ', Fin.append v v', fun j => ?_, fun j => ?_, fun y hy => ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simpa using h1 i
        · simpa using h1' i
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simpa using h2 i
        · simpa using h2' i
      · show a _ + b _ = _
        rw [h3 y hy, h3' y hy, Fin.sum_univ_add]
        simp
  set f : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ := fun y => φ (x * atTau θ V τ (P⁻¹ * y * P)) with hf
  have hcont : ContinuousOn (fun y : Matrix (Fin V.rank) (Fin V.rank) ℂ => x * atTau θ V τ (P⁻¹ * y * P))
      (UJset ε₀) := by
    refine (continuous_mul_left_GA V x).comp_continuousOn ?_
    refine (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).continuousOn ?_
    intro y hy
    exact GlobalTheory.LowTypeDetermined.conj_inv_mem hPu hPG hy
  have hfc : ContinuousOn f (UJset ε₀) := hφ.cont.comp_continuousOn hcont
  have hB := closure_model hHC hCW _ ε₀ lam₀ hP₀ H σ hσ f hfc
    (GlobalTheory.TypeSum.GrowthAtPlace.umg_atTau D θ hθ V τ φ hφ ε₀ P hPu hPG x) (by
      intro C hC δ hδ
      have hK : IsCompact ((fun y => x * atTau θ V τ (P⁻¹ * y * P)) '' (C ∩ UJset ε₀)) :=
        (hC.inter_right (isClosed_UJset ε₀)).image_of_continuousOn (hcont.mono Set.inter_subset_right)
      obtain ⟨ψ, hψ, happ⟩ := hT _ hK δ hδ
      obtain ⟨m, ℓ, v, h1, h2, h3⟩ := hfin ψ hψ
      refine ⟨m, ℓ, v, h1, h2, fun y hyC hy => ?_⟩
      rw [← h3 y hy]
      exact happ _ ⟨y, ⟨hyC, hy⟩, rfl⟩)
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hPu
  have a1 := Matrix.mul_nonsing_inv _ hd
  have a2 := Matrix.nonsing_inv_mul _ hd
  have hi : P⁻¹⁻¹ = P := Matrix.nonsing_inv_nonsing_inv _ hd
  have t3 := GlobalTheory.TypeSum.hasTypeAll_transport _ H H σ (fun g => σ (P * g * P⁻¹)) (Formalism.REAL.Jm ε₀)
    (gramAt D V τ) P⁻¹ (GlobalTheory.TypeSum.isUnit_Jm ε₀) (IsUnit.of_mul_eq_one _ a2) (by
      rw [show gramAt D V τ = Pᴴ * Formalism.REAL.Jm ε₀ * P from hPG.symm]
      calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε₀ * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε₀ * (P * P⁻¹) := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [a1]; simp) (LinearIsometryEquiv.refl ℂ H) (fun g _ v => by
      have e : P * (P⁻¹ * g * P⁻¹⁻¹) * P⁻¹ = g := by
        rw [hi]
        calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
          _ = g := by rw [a1, Matrix.one_mul, Matrix.mul_one]
      show σ g v = σ (P * (P⁻¹ * g * P⁻¹⁻¹) * P⁻¹) v
      rw [e]) f hB
  have e' : (fun y => f (P⁻¹⁻¹ * y * P⁻¹)) = fun y => φ (x * atTau θ V τ y) := by
    funext y
    show φ (x * atTau θ V τ (P⁻¹ * (P⁻¹⁻¹ * y * P⁻¹) * P)) = φ (x * atTau θ V τ y)
    rw [hi]
    congr 3
    calc P⁻¹ * (P * y * P⁻¹) * P = (P⁻¹ * P) * y * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [a2, Matrix.one_mul, Matrix.mul_one]
  rw [e'] at t3
  exact GlobalTheory.TypeSum.hasTypeAll_iff.1 t3

end GlobalTheory.ClosureSeries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau) (S : SPar) (φ : GA D V → ℂ),
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.DiscreteSeriesUpqUnique → GlobalTheory.Published.HarishChandraModules →
    GlobalTheory.Published.CasselmanWallach → IsInfFam (D := D) θ → V.SigOK →
    GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S → IsAutFunSm θ V φ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S φ → IsTypeAt θ V τ S φ := by
  first | exact @GlobalTheory.ClosureSeries.closure_to_series | exact GlobalTheory.ClosureSeries.closure_to_series | (intros; apply GlobalTheory.ClosureSeries.closure_to_series <;> assumption)
end
