module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateShellLeDivModulus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCentreFlowConjScalesHaarIsotropicUnipotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeNormOneLeviWittFrameStabilizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightSlabSubsetUnipotentLeviCompact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameUnipotentRadicalClosedFundDomainMassOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameUnipotentRadicalClosedFundDomainMassOne
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem unipRad_frame_closed_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → IsClosed (unipRad σ J X : Set (GAd σ J)) ∧ ∃ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure ∧ IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν ∧ ν DN = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have e : X = X.submatrix id (Fin.castLE (le_refl (r + 1))) := by
    ext i j
    rfl
  have hC : GlobalTheory.UAut.IsIsoCols σ J X := e ▸ GlobalTheory.UAut.isIsoCols_of_isWittFrame hW (sigma_sigma h) hJ _
  haveI := GlobalTheory.UAut.locallyCompact_unipRad h hJ hC
  exact ⟨GlobalTheory.UAut.unipFlag_const (σ := σ) (J := J) X 0 ▸ GlobalTheory.UAut.isClosed_unipFlag hJ (sigma_sigma h) hC _,
    GlobalTheory.UAut.exists_mass_one (GlobalTheory.UAut.cocompact_unipRad h hJ hC)⟩

end GlobalTheory.ResidueEisenstein
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameUnipotentRadicalClosedFundDomainMassOneStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittFrameUnipotentRadical_closed_fundDomain_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → IsClosed (unipRad σ J X : Set (GAd σ J)) ∧ ∃ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure ∧ IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν ∧ ν DN = 1 := by
  first | exact @GlobalTheory.ResidueEisenstein.unipRad_frame_closed_mass_one | exact GlobalTheory.ResidueEisenstein.unipRad_frame_closed_mass_one | (intros; apply GlobalTheory.ResidueEisenstein.unipRad_frame_closed_mass_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsotropicStabiliserSplitLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsotropicStabiliserSplitLattice
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem inf_subgroupOf_of_le' {G : Type} [Group G] {Γ P H : Subgroup G} (h : H ≤ P) :
    (Γ ⊓ P).subgroupOf H = Γ.subgroupOf H := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun e => e.1, fun e => ⟨e, h x.2⟩⟩

theorem semiLat_frameGrp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J →
    IsWittFrame σ J X Y → ∀ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν → ν DN = 1 →
      ∃ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})),
        SemiLat (unipRad σ J X) (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤)
          ν π DN DM := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW ν DN hν hDN h1
  obtain ⟨π, DM, hπ, hDM⟩ := GlobalTheory.StdPar.exists_haar_leviOne (X := X) (Y := Y) {Fin.last r} h hJ hW
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := GlobalTheory.T.wittFrameLevi_normalizes_radical_properties F E σ n J r X Y h hJ hW
  have hN : unipRad σ J X ≤ GlobalTheory.StdPar.frameStab σ J X ⊤ := fun u hu => ⟨1, trivial, f3 u hu⟩
  have hM : GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r} ≤ GlobalTheory.StdPar.frameStab σ J X ⊤ := fun m hm => by
    obtain ⟨β, e, -⟩ := f4 m hm
    exact ⟨β, trivial, e⟩
  refine ⟨π, DM,
    { closedN := (GlobalTheory.T.wittFrameUnipotentRadical_closed_fundDomain_mass_one F E σ n J r X Y h hJ hW).1
      closedM := f7
      norm := fun m hm => f1 m (f6 hm)
      disj := fun g hg hg' => f2 g hg (f6 hg')
      dec := ?_
      haarN := hν
      haarM := hπ
      domN := by rw [inf_subgroupOf_of_le' hN]; exact hDN
      domM := by rw [inf_subgroupOf_of_le' hM]; exact hDM
      finN := by rw [h1]; exact ENNReal.one_ne_top
      finM := GlobalTheory.T.finiteCovolume_normOneLevi_wittFrameStabilizer F E σ n J r X Y h hJ hW π DM hπ hDM }⟩
  rintro γ ⟨hγ, β, -, e⟩
  obtain ⟨u, hu, m, -, hp, -, hr, ho⟩ := GlobalTheory.T.leviDecomposition_wittFrameStabilizer F E σ n J r X Y h hJ hW γ β e
  have hm := ho (f5 γ hγ β e)
  refine ⟨u, hu, m, hm, ⟨?_, hN hu⟩, ⟨hr hγ, hM hm⟩, hp⟩
  have : u = γ * m⁻¹ := by rw [hp, mul_inv_cancel_right]
  rw [this]
  exact (ratPts σ J).mul_mem hγ ((ratPts σ J).inv_mem (hr hγ))

end GlobalTheory.ResidueEisenstein
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsotropicStabiliserSplitLatticeStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_isotropicStabiliser_splitLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (ν : Measure (unipRad σ J X)) (DN : Set (unipRad σ J X)), ν.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J X)) DN ν → ν DN = 1 → ∃ (π : Measure (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})) (DM : Set (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r})), SemiLat (unipRad σ J X) (GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) (ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) ν π DN DM := by
  first | exact @GlobalTheory.ResidueEisenstein.semiLat_frameGrp | exact GlobalTheory.ResidueEisenstein.semiLat_frameGrp | (intros; apply GlobalTheory.ResidueEisenstein.semiLat_frameGrp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightSlabSubsetUnipotentLeviCompactStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heightSlab_subset_unipotent_levi_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ b, IsFlowJ σ J X Y b → ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ g, Real.exp (-1) ≤ h g → h g ≤ 1 → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}, ∃ y ∈ C, g = u * m * y := by
  first | exact @GlobalTheory.ResidueEisenstein.slab_subset | exact GlobalTheory.ResidueEisenstein.slab_subset | (intros; apply GlobalTheory.ResidueEisenstein.slab_subset <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviCentreFlowWittFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealIdeleFlow
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResLine

theorem exists_real_idele_flow (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ l : ℝ → (AF F ⊗[F] E)ˣ, Continuous l ∧ (∀ s t, l (s + t) = l s * l t) ∧
      (∀ t, sigR (AF F) σ (l t).1 = (l t).1) ∧ ∀ t, (absE F E (l t) : ℝ) = Real.exp t := by
  have := h.1
  let e := fun w : InfinitePlace F => InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)
  let ρ : ℝ →* AF F :=
    { toFun := fun x => ((fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm x :
        Ainf F), (1 : Af F))
      map_one' := Prod.ext (funext fun w => map_one _) rfl
      map_mul' := fun x y => Prod.ext (funext fun w => map_mul _ _ _) (mul_one _).symm }
  have hρ : Continuous ρ := (continuous_pi fun w => (e w).symm.continuous).prodMk continuous_const
  have hn : ∀ w x, ‖evInf F w (ρ x)‖ = ‖x‖ := fun w x =>
    (e w).symm.isometry.norm_map_of_map_zero
      (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm) x
  let ι : AF F →* AF F ⊗[F] E := (algebraMap (AF F) (AF F ⊗[F] E)).toMonoidHom
  have hι : Continuous ι := by
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
    exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  let d : ℕ := Fintype.card (InfinitePlace F)
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  let u : ℝ → ℝˣ := fun t => Units.mk0 (Real.exp (t / (2 * d))) (Real.exp_ne_zero _)
  have hu : Continuous u := Units.continuous_iff.2
    ⟨show Continuous fun t : ℝ => Real.exp (t / (2 * d)) by fun_prop,
      show Continuous fun t : ℝ => (Real.exp (t / (2 * d)))⁻¹ from
        Continuous.inv₀ (by fun_prop) fun _ => Real.exp_ne_zero _⟩
  refine ⟨fun t => Units.map (ι.comp ρ) (u t), (Continuous.units_map (ι.comp ρ) (show Continuous (ι ∘ ρ) from hι.comp hρ)).comp hu, fun s t => ?_,
    fun t => congrArg (ρ (u t) ⊗ₜ[F] ·) (map_one σ), fun t => ?_⟩
  · rw [← map_mul]
    exact congrArg _ (Units.ext (show Real.exp _ = Real.exp _ * Real.exp _ by rw [← Real.exp_add, add_div]))
  · have h1 : Algebra.norm (AF F) (Units.map (ι.comp ρ) (u t)).1 = ρ (u t) ^ 2 := by
      change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (ρ (u t))) = _
      haveI : Nontrivial (AF F) := (evInf F (Classical.arbitrary _)).toRingHom.domain_nontrivial
      rw [Algebra.norm_algebraMap, Module.finrank_baseChange, h.2.2.1]
    have h2 : ∀ v, evFin F v (ρ (u t)) = 1 := fun v => rfl
    have h3 : ∀ w : InfinitePlace F, w.mult = 1 := fun w => if_pos (IsTotallyReal.isReal w)
    simp only [GlobalTheory.Doubling.absE_apply, GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf, h1, map_pow, h2, h3,
      one_pow, nnnorm_one, finprod_one, mul_one, pow_one, NNReal.coe_prod, coe_nnnorm, norm_pow, hn,
      Finset.prod_const, Finset.card_univ]
    change (‖Real.exp (t / (2 * d))‖ ^ 2) ^ d = _
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← pow_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp

end GlobalTheory.ResLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviCentreFlowWittFrame
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueFlow

open Matrix GlobalTheory.StdPar GlobalTheory.IdTorus
open Formalism.UG (cT)
open GlobalTheory.Doubling (conjUnit)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

theorem row_of_stab {X Y : Matrix (Fin n) (Fin r) E} (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {g : GAd σ J} {B C : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)}
    (hX : (matHom _ σ J g).1 * adMat F X = adMat F X * B) (hY : (matHom _ σ J g⁻¹).1 * adMat F Y = adMat F Y * C) :
    adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J g).1 = B * adMat F (cT (σ : E →+* E) Y * J) := by
  set S := sigR (AF F) σ with hS
  set M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g).1 with hMdef
  set Mi : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := (matHom _ σ J g⁻¹).1 with hMidef
  have hinv : matHom (AF F) σ J g⁻¹ = (matHom (AF F) σ J g)⁻¹ := map_inv _ g
  have hMMi : M * Mi = 1 := by
    rw [hMdef, hMidef, hinv]; exact Units.mul_inv _
  have hU : cT S M * adMat F J * M = adMat F J := g.2
  have hadY : adMat F (cT (σ : E →+* E) Y * J) = cT S (adMat F Y) * adMat F J := by
    rw [adMat, Matrix.map_mul]
    congr 1
  have hJM : adMat F J * M = cT S Mi * adMat F J := by
    calc adMat F J * M = (cT S Mi * cT S M) * adMat F J * M := by
          rw [← Formalism.UG.cT_mul, hMMi, Formalism.UG.cT_one, Matrix.one_mul]
      _ = cT S Mi * (cT S M * adMat F J * M) := by simp only [Matrix.mul_assoc]
      _ = cT S Mi * adMat F J := by rw [hU]
  have h1 : adMat F (cT (σ : E →+* E) Y * J) * M = cT S C * adMat F (cT (σ : E →+* E) Y * J) := by
    rw [hadY, Matrix.mul_assoc, hJM, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, hY, Formalism.UG.cT_mul, Matrix.mul_assoc]
  have hyx : adMat F (cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, GlobalTheory.StdPar.yx hCM hJ hW]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have h2 : cT S C = B := by
    calc cT S C = cT S C * (adMat F (cT (σ : E →+* E) Y * J) * adMat F X) := by rw [hyx, Matrix.mul_one]
      _ = adMat F (cT (σ : E →+* E) Y * J) * M * adMat F X := by rw [h1, Matrix.mul_assoc]
      _ = B := by rw [Matrix.mul_assoc, hX, ← Matrix.mul_assoc, hyx, Matrix.one_mul]
  rw [h1, h2]

theorem const_centre {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y)
    {c : (AF F ⊗[F] E)ˣ} {a : GAd σ J} (ha : IsIdTorusElt σ J X Y (fun _ => c) a) :
    a ∈ levi σ J X Y {Fin.last r} ∧ ∀ m ∈ levi σ J X Y {Fin.last r}, a * m = m * a := by
  have ext : ∀ {m : GAd σ J}, m ∈ levi σ J X Y {Fin.last r} →
      (∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J m).1 * adMat F X = adMat F X * B) ∧
      ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E), (matHom _ σ J m).1 * adMat F Y = adMat F Y * C := by
    intro m hm
    simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf] at hm
    obtain ⟨⟨B, -, hB⟩, ⟨C, -, hC⟩⟩ := hm (Fin.last r) (Finset.mem_singleton_self _)
    exact ⟨⟨B.1, hB⟩, ⟨C.1, hC⟩⟩
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [levi, Subgroup.mem_iInf, Subgroup.mem_inf]
    intro k hk
    refine ⟨⟨⟨diagonal fun i => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => (((c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩,
      ⟨⟨diagonal fun i => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E),
      diagonal fun i => ((conjUnit σ c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E), by simp [diagonal_mul_diagonal],
      by simp [diagonal_mul_diagonal]⟩, Subgroup.mem_top _, ?_⟩⟩
    · ext i j
      have := congrFun (congrFun ha.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
    · ext i j
      have := congrFun (congrFun ha.2.1 i) (Fin.castLE k.2 j)
      rw [mul_diagonal] at this
      rw [mul_diagonal]
      simpa [Matrix.mul_apply, initCols] using this
  · obtain ⟨⟨B, hB⟩, ⟨C, hC⟩⟩ := ext hm
    obtain ⟨⟨B', hB'⟩, ⟨C', hC'⟩⟩ := ext (inv_mem hm)
    have rY := row_of_stab hCM hJ hW hB hC'
    have rX := row_of_stab hCM hJ (GlobalTheory.IdTorusCent.swap hCM hJ hW) hC hB'
    have dc : ∀ (d : AF F ⊗[F] E) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)),
        diagonal (fun _ : Fin (r + 1) => d) * Z = Z * diagonal (fun _ => d) := fun d Z => by
      ext i j; simp [diagonal_mul, mul_diagonal, mul_comm]
    have c1 : (matHom _ σ J m).1 * (adMat F X * diagonal (fun _ : Fin (r + 1) => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) Y * J)) = adMat F X * diagonal (fun _ : Fin (r + 1) => ((c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) Y * J) * (matHom _ σ J m).1 := by
      rw [Matrix.mul_assoc (adMat F X * _), rY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB,
        Matrix.mul_assoc (adMat F X) B, ← dc, ← Matrix.mul_assoc]
    have c2 : (matHom _ σ J m).1 * (adMat F Y * diagonal (fun _ : Fin (r + 1) => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) X * J)) = adMat F Y * diagonal (fun _ : Fin (r + 1) => (((conjUnit σ c)⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1) *
        adMat F (cT (σ : E →+* E) X * J) * (matHom _ σ J m).1 := by
      rw [Matrix.mul_assoc (adMat F Y * _), rX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hC,
        Matrix.mul_assoc (adMat F Y) C, ← dc, ← Matrix.mul_assoc]
    apply matHom_injective
    apply Units.ext
    simp only [map_mul, Units.val_mul, GlobalTheory.T.idelicFrameTorusElement_matrix_eq hCM hJ hW ha, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, c1, c2]

end GlobalTheory.ResidueFlow


open GlobalTheory.IdTorus in
theorem GlobalTheory.ResidueEisenstein.exists_isFlowJ : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ b : ℝ → GAd σ J, IsFlowJ σ J X Y b := by
  intro F E _ _ _ _ _ σ n J r X Y hc hJ hW
  obtain ⟨t, htc, ht⟩ := exists_continuous_isIdTorusElt hc hJ hW
  obtain ⟨l, lc, ladd, -, labs⟩ := exists_real_idele_flow F E σ hc
  have hd : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have cl := fun s : ℝ => GlobalTheory.ResidueFlow.const_centre hc hJ hW (ht fun _ => l (s / ((r + 1 : ℕ) : ℝ)))
  refine ⟨fun s => t fun _ => l (s / ((r + 1 : ℕ) : ℝ)),
    htc.comp (continuous_pi fun _ => lc.comp (continuous_id.div_const _)), fun s s' => ?_, fun s => ?_,
    fun s => (cl s).1, fun s => (cl s).2⟩
  · refine isIdTorusElt_uniq hc hJ hW (ht _) ?_
    have : (fun _ : Fin (r + 1) => l ((s + s') / ((r + 1 : ℕ) : ℝ))) =
        (fun _ => l (s / ((r + 1 : ℕ) : ℝ))) * fun _ => l (s' / ((r + 1 : ℕ) : ℝ)) := by
      funext k; rw [add_div, ladd]; rfl
    rw [this]; exact isIdTorusElt_mul (ht _) (ht _)
  · refine ⟨Units.map (Matrix.scalar (Fin (r + 1))).toMonoidHom (l (s / ((r + 1 : ℕ) : ℝ))), (ht _).1, ?_⟩
    have : Matrix.GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin (r + 1))).toMonoidHom (l (s / ((r + 1 : ℕ) : ℝ)))) =
        l (s / ((r + 1 : ℕ) : ℝ)) ^ (r + 1) := by
      apply Units.ext
      change Matrix.det (Matrix.diagonal fun _ : Fin (r + 1) => (l (s / ((r + 1 : ℕ) : ℝ))).1) = _
      rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Units.val_pow_eq_pow_val]
    rw [this, map_pow, NNReal.coe_pow, labs, ← Real.exp_nat_mul, mul_div_cancel₀ _ hd]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviCentreFlowWittFrameStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leviCentreFlow_wittFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ b : ℝ → GAd σ J, IsFlowJ σ J X Y b := by
  first | exact @GlobalTheory.ResidueEisenstein.exists_isFlowJ | exact GlobalTheory.ResidueEisenstein.exists_isFlowJ | (intros; apply GlobalTheory.ResidueEisenstein.exists_isFlowJ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureHeightShellLeIsotropicFrameQuotient
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem measure_shell_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ (μ : Measure (GAd σ J)) (D : Set (GAd σ J)), μ.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) : Subgroup (GAd σ J)) D μ → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ j : ℕ, μ.restrict D {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hD μ D hμ hFD
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_leviCentreFlow_wittFrame F E σ n J r X Y hD.cm hD.herm hD.witt
  obtain ⟨-, hHt, hlaw⟩ := GlobalTheory.T.isCompact_level_height_scales_isotropicFrame F E σ n J r X Y L a h hD
  obtain ⟨-, ν, DN, hν, hDN, hone⟩ := unipRad_frame_closed_mass_one F E σ n J r X Y hD.cm hD.herm hD.witt
  have hmod := GlobalTheory.T.leviCentreFlow_conj_scales_haar_isotropicUnipotent F E σ n J r X Y hD.cm hD.herm hD.witt b hb ν hν
  obtain ⟨π, DM, hSL⟩ := GlobalTheory.T.rational_isotropicStabiliser_splitLattice F E σ n J r X Y hD.cm hD.herm hD.witt ν DN hν hDN hone
  obtain ⟨C, hC, hslab⟩ := GlobalTheory.T.heightSlab_subset_unipotent_levi_compact F E σ n J r X Y L a h hD b hb
  haveI : Countable (ratPts σ J) := inferInstance
  haveI : Countable ((ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) : Subgroup (GAd σ J)) :=
    Function.Injective.countable (Subgroup.inclusion_injective
      (inf_le_left : ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤ ≤ ratPts σ J))
  obtain ⟨B, hB, hsh⟩ := GlobalTheory.ResLine.modulus_mul_measure_shell_le (GAd σ J) _ _ _ ν π DN DM hSL μ D hμ hFD C hC
  refine ⟨B, hB, fun j => ?_⟩
  have hS : MeasurableSet {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} :=
    (measurableSet_Ioc (a := Real.exp (-(j + 1 : ℝ))) (b := Real.exp (-(j : ℝ)))).preimage hHt.cont.measurable
  have key := hsh (b j) _ (fun m hm => hb.comm j m (Subgroup.mem_inf.mp hm).1) (hmod j) _ hS (fun x hx => by
    obtain ⟨β, hβ, e⟩ := hb.onX j
    have e2 : h (b j * x) = Real.exp j * h x := by rw [hlaw _ β hβ, e]
    have hp : 0 < Real.exp (j : ℝ) := Real.exp_pos _
    refine hslab _ ?_ ?_
    · rw [e2]
      have : Real.exp (-1) = Real.exp j * Real.exp (-(j + 1 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hx.1.le hp.le
    · rw [e2]
      have : (1 : ℝ) = Real.exp j * Real.exp (-(j : ℝ)) := by rw [← Real.exp_add]; simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hx.2 hp.le)
  rw [Measure.restrict_apply hS]
  have e1 : ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * j))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; simp
  calc _ = ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * (ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * j))) * _) := by
        rw [← mul_assoc, e1, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * B := by gcongr
    _ = _ := mul_comm _ _

end GlobalTheory.ResidueEisenstein
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureHeightShellLeIsotropicFrameQuotientStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_heightShell_le_isotropicFrame_quotient : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ (μ : Measure (GAd σ J)) (D : Set (GAd σ J)), μ.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) : Subgroup (GAd σ J)) D μ → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ j : ℕ, μ.restrict D {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) := by
  first | exact @GlobalTheory.ResidueEisenstein.measure_shell_le | exact GlobalTheory.ResidueEisenstein.measure_shell_le | (intros; apply GlobalTheory.ResidueEisenstein.measure_shell_le <;> assumption)
end
