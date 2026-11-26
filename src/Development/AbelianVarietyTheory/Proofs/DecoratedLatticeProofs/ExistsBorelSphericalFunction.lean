module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalFunction
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.CuspRep.ParLaws GlobalTheory.SatakeFlip

namespace GlobalTheory.BorelSphExist

section Char

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}


variable (k) in
def unrBorel (α : Fin N → ℂˣ) : borel k (Fin N) →* ℂˣ :=
  ((GlobalTheory.SmGL.torusChar fun i => SmGL.unrChar k (α i)).comp (leviTorus k (Fin N)).symm.toMonoidHom).comp
    (leviProj k (points (Fin N)))

theorem unrBorel_apply (α : Fin N → ℂˣ) (b : borel k (Fin N)) :
    unrBorel k α b = ∏ i : Fin N, α i ^ ord k (diagU b i) :=
  GlobalTheory.SmGL.torusChar_apply _ _

theorem unrBorel_eq_one (α : Fin N → ℂˣ) (b : borel k (Fin N)) (hb : b.1 ∈ KO k (Fin N)) :
    unrBorel k α b = 1 := by
  rw [unrBorel_apply]
  refine Finset.prod_eq_one fun i _ => ?_
  obtain ⟨h1, h2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff _).1 hb
  have h3 := congrArg (valuation k) (inv_diag_mul b.2 i)
  rw [map_mul, map_one] at h3
  have a1 : valuation k (b.1.val i i) ≤ 1 := h1 i i
  have a2 : valuation k ((b.1⁻¹).val i i) ≤ 1 := h2 i i
  have h : valuation k (diagU b i : k) = 1 := by
    rw [val_diagU]
    exact le_antisymm a1 (h3.ge.trans (mul_le_of_le_one_left' a2))
  rw [ord_eq_zero h, zpow_zero]

end Char

theorem exists_isBorelSph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (γ : Fin N → ℂ), (∀ i, γ i ≠ 0) →
    ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k γ ψ := by
  intro k _ _ _ _ N γ hγ
  let α : Fin N → ℂˣ := fun i => Units.mk0 (γ i) (hγ i)
  obtain ⟨φ, h1, h2, h3⟩ := exists_fun (borel k (Fin N)) (KO k (Fin N)) (unrBorel k α) (fun g => by
    obtain ⟨b, hb, x, hx, e⟩ := iwasawa_blockTriangular k (Fin N) Fin.val g
    exact ⟨⟨b, (mem_borel _).2 hb⟩, x, hx, e⟩) (unrBorel_eq_one α)
  refine ⟨φ, fun g x hx => h3 g x hx, fun b hb t ht => ?_⟩
  have hφ := h2 ⟨b, hb⟩ 1
  rw [mul_one, h1, mul_one] at hφ
  rw [hφ, unrBorel_apply, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hd : diagU ⟨b, hb⟩ i = t i := Units.ext ((val_diagU _ i).trans (ht i))
  rw [hd, Units.val_zpow_eq_zpow_val]
  rfl

end GlobalTheory.BorelSphExist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalFunctionStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_borelSphericalFunction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : Fin N → ℂ), (∀ i, γ i ≠ 0) → ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k γ ψ := by
  first | exact @GlobalTheory.BorelSphExist.exists_isBorelSph | exact GlobalTheory.BorelSphExist.exists_isBorelSph | (intros; apply GlobalTheory.BorelSphExist.exists_isBorelSph <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeLeRealSymplecticPairingSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeLeRealSymplecticPairingSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.RealPairBound

theorem trace_conjT_mul_single {r s : ℕ} (X : Matrix (Fin r) (Fin s) ℂ) (i : Fin r) (j : Fin s) (a : ℂ) :
    (Xᴴ * Matrix.single i j a).trace = star (X i j) * a := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

theorem gramAt_det_ne (D : D7) (T : HSp D) (τ : D.what₂.Tau) : (gramAt D T τ).det ≠ 0 := by
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne T)

theorem pair_single (D : D7) (T : HSp D) {ρ : ℕ} (τ : D.what₂.Tau) (X : Matrix (Fin T.rank) (Fin ρ) ℂ)
    (i : Fin T.rank) (j : Fin ρ) (a : ℂ) :
    tauE D τ D.host.xi0 * (Xᴴ * gramAt D T τ * ((gramAt D T τ)⁻¹ * Matrix.single i j a)).trace
      = tauE D τ D.host.xi0 * (star (X i j) * a) := by
  have hu : IsUnit (gramAt D T τ).det := isUnit_iff_ne_zero.2 (gramAt_det_ne D T τ)
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (gramAt D T τ), Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
    trace_conjT_mul_single]

theorem realSize_le_pairing : ∀ (D : D7) (θ : InfFam D) (T : HSp D) (ρ : ℕ), ∃ (k : ℕ) (τs : Fin k → D.what₂.Tau)
    (zs : Fin k → Matrix (Fin T.rank) (Fin ρ) ℂ) (C : ℝ), ∀ x : Mx D T.rank ρ,
      realSize θ x ≤ C * ∑ i, |2 * (tauE D (τs i) D.host.xi0 * ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| := by
  intro D θ T ρ
  classical
  let c : D.what₂.Tau → ℂ := fun τ => tauE D τ D.host.xi0
  have hc : ∀ τ, c τ ≠ 0 := fun τ => (map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  let α : D.what₂.Tau → Bool → ℂ := fun τ b => if b then (c τ)⁻¹ * Complex.I else (c τ)⁻¹
  let z : D.what₂.Tau × Fin T.rank × Fin ρ × Bool → Matrix (Fin T.rank) (Fin ρ) ℂ :=
    fun p => (gramAt D T p.1)⁻¹ * Matrix.single p.2.1 p.2.2.1 (α p.1 p.2.2.2)
  let e := (Fintype.equivFin (D.what₂.Tau × Fin T.rank × Fin ρ × Bool)).symm
  refine ⟨_, fun n => (e n).1, fun n => z (e n), 1, fun x => ?_⟩
  rw [one_mul]
  let v : D.what₂.Tau × Fin T.rank × Fin ρ × Bool → ℝ := fun p =>
    |2 * (tauE D p.1 D.host.xi0 * ((compAt θ p.1 x)ᴴ * gramAt D T p.1 * z p).trace).re|
  change realSize θ x ≤ ∑ n, v (e n)
  rw [Equiv.sum_comp e v, Fintype.sum_prod_type, realSize]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Fintype.sum_bool]
  have hv : ∀ b, v (τ, i, j, b) = |2 * (c τ * (star (compAt θ τ x i j) * α τ b)).re| := fun b => by
    simp only [v, z]
    rw [pair_single]
  rw [hv, hv]
  have h1 : c τ * (star (compAt θ τ x i j) * α τ true) = star (compAt θ τ x i j) * Complex.I := by
    simp only [α, if_true]
    field_simp [hc τ]
  have h0 : c τ * (star (compAt θ τ x i j) * α τ false) = star (compAt θ τ x i j) := by
    simp only [α, Bool.false_eq_true, if_false]
    field_simp [hc τ]
  rw [h1, h0]
  have hn := Complex.norm_le_abs_re_add_abs_im (compAt θ τ x i j)
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    abs_mul, mul_zero, mul_one, zero_sub, abs_neg, abs_two]
  linarith [abs_nonneg (compAt θ τ x i j).re, abs_nonneg (compAt θ τ x i j).im]

end GlobalTheory.RealPairBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeLeRealSymplecticPairingSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixRealSize_le_realSymplecticPairing_sum : ∀ (D : D7) (θ : InfFam D) (T : HSp D) (ρ : ℕ), ∃ (k : ℕ) (τs : Fin k → D.what₂.Tau) (zs : Fin k → Matrix (Fin T.rank) (Fin ρ) ℂ) (C : ℝ), ∀ x : Mx D T.rank ρ, realSize θ x ≤ C * ∑ i, |2 * (tauE D (τs i) D.host.xi0 * ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| := by
  first | exact @GlobalTheory.RealPairBound.realSize_le_pairing | exact GlobalTheory.RealPairBound.realSize_le_pairing | (intros; apply GlobalTheory.RealPairBound.realSize_le_pairing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFundamentalDomainProdOfKernelImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFundamentalDomainProdOfKernelImage
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped Pointwise

namespace GlobalTheory

theorem isFundamentalDomain_prod_of_ker_image : ∀ (N G : Type) [Group N] [Group G] [MeasurableSpace N] [MeasurableSpace G] [MeasurableMul N] [MeasurableMul G] (ν : Measure N) (μ : Measure G) [SFinite ν] [SFinite μ] [ν.IsMulLeftInvariant] [μ.IsMulLeftInvariant] (Γ : Subgroup (N × G)) [Countable Γ] (𝓐 : Set N) (𝓑 : Set G), IsFundamentalDomain (Γ.comap (MonoidHom.inl N G)) 𝓐 ν → IsFundamentalDomain (Γ.map (MonoidHom.snd N G)) 𝓑 μ → IsFundamentalDomain Γ (𝓐 ×ˢ 𝓑) (ν.prod μ) := by
  intro N G _ _ _ _ _ _ ν μ _ _ _ _ Γ _ 𝓐 𝓑 hA hB
  classical

  have hKc : Countable (Γ.comap (MonoidHom.inl N G)) := by
    refine Function.Injective.countable (f := fun k : Γ.comap (MonoidHom.inl N G) =>
      (⟨MonoidHom.inl N G k, k.2⟩ : Γ)) ?_
    intro a b hab
    apply Subtype.ext
    have := congrArg (fun x : Γ => (x : N × G).1) hab
    simpa using this
  have hHc : Countable (Γ.map (MonoidHom.snd N G)) := by
    refine Function.Surjective.countable (f := fun γ : Γ =>
      (⟨(γ : N × G).2, Subgroup.mem_map_of_mem _ γ.2⟩ : Γ.map (MonoidHom.snd N G))) ?_
    rintro ⟨h, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

  have hlift : ∀ h : Γ.map (MonoidHom.snd N G), ∃ m : N, ((m, (h : G)) : N × G) ∈ Γ := by
    rintro ⟨h, x, hx, rfl⟩
    exact ⟨x.1, by simpa using hx⟩
  choose mm hmm using hlift

  have memS : ∀ (γ : Γ) (p : N × G), p ∈ γ • (𝓐 ×ˢ 𝓑) →
      ((γ : N × G).1⁻¹ * p.1 ∈ 𝓐 ∧ (γ : N × G).2⁻¹ * p.2 ∈ 𝓑) := by
    rintro γ p ⟨q, hq, rfl⟩
    simpa [Subgroup.smul_def] using hq
  refine
    { nullMeasurableSet := hA.nullMeasurableSet.prod hB.nullMeasurableSet
      ae_covers := ?_
      aedisjoint := ?_ }
  · have h2 : ∀ᵐ g ∂μ, ∃ h : Γ.map (MonoidHom.snd N G), h • g ∈ 𝓑 := hB.ae_covers
    have h1 : ∀ᵐ n ∂ν, ∀ h : Γ.map (MonoidHom.snd N G),
        ∃ k : Γ.comap (MonoidHom.inl N G), k • (mm h * n) ∈ 𝓐 := by
      rw [ae_all_iff]
      intro h
      exact (measurePreserving_mul_left ν (mm h)).quasiMeasurePreserving.ae hA.ae_covers
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1,
      Measure.quasiMeasurePreserving_snd.ae h2] with p hn hg
    obtain ⟨h, hh⟩ := hg
    obtain ⟨k, hk⟩ := hn h
    have hk' : (((k : N), (1 : G)) : N × G) ∈ Γ := k.2
    refine ⟨⟨((k : N), (1 : G)) * (mm h, (h : G)), Γ.mul_mem hk' (hmm h)⟩, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [Subgroup.smul_def, mul_assoc] using hk
    · simpa [Subgroup.smul_def] using hh
  · intro γ γ' hne
    change (ν.prod μ) ((γ • (𝓐 ×ˢ 𝓑)) ∩ (γ' • (𝓐 ×ˢ 𝓑))) = 0
    by_cases hh : (γ : N × G).2 = (γ' : N × G).2
    ·
      have hkmem : MonoidHom.inl N G ((γ' : N × G).1⁻¹ * (γ : N × G).1) ∈ Γ := by
        have e : MonoidHom.inl N G ((γ' : N × G).1⁻¹ * (γ : N × G).1) = ((γ'⁻¹ * γ : Γ) : N × G) := by
          ext <;> simp [hh]
        rw [e]; exact (γ'⁻¹ * γ).2
      let k : Γ.comap (MonoidHom.inl N G) := ⟨(γ' : N × G).1⁻¹ * (γ : N × G).1, hkmem⟩
      have hk1 : (1 : Γ.comap (MonoidHom.inl N G)) ≠ k⁻¹ := by
        intro h1
        apply hne
        have h1' : (γ' : N × G).1⁻¹ * (γ : N × G).1 = 1 := by
          have := congrArg (fun x : Γ.comap (MonoidHom.inl N G) => ((x⁻¹ : Γ.comap (MonoidHom.inl N G)) : N)) h1
          simpa [k] using this.symm
        apply Subtype.ext
        exact Prod.ext (inv_mul_eq_one.mp h1').symm hh
      have hnull : ν (𝓐 ∩ k⁻¹ • 𝓐) = 0 := by
        have := hA.aedisjoint hk1
        simpa [Function.onFun, AEDisjoint] using this
      refine measure_mono_null (t := Prod.fst ⁻¹' ((fun x => (γ : N × G).1⁻¹ * x) ⁻¹' (𝓐 ∩ k⁻¹ • 𝓐))) ?_
        (Measure.quasiMeasurePreserving_fst.preimage_null
          ((measurePreserving_mul_left ν (γ : N × G).1⁻¹).quasiMeasurePreserving.preimage_null hnull))
      rintro p ⟨hp, hp'⟩
      obtain ⟨a1, -⟩ := memS γ p hp
      obtain ⟨a2, -⟩ := memS γ' p hp'
      refine ⟨a1, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Subgroup.smul_def, smul_eq_mul]
      show ((γ' : N × G).1⁻¹ * (γ : N × G).1) * ((γ : N × G).1⁻¹ * p.1) ∈ 𝓐
      simpa [mul_assoc] using a2
    ·
      let h : Γ.map (MonoidHom.snd N G) := ⟨(γ : N × G).2, Subgroup.mem_map_of_mem _ γ.2⟩
      let h' : Γ.map (MonoidHom.snd N G) := ⟨(γ' : N × G).2, Subgroup.mem_map_of_mem _ γ'.2⟩
      have hne' : h ≠ h' := fun e => hh (congrArg Subtype.val e)
      have hnull : μ ((h • 𝓑) ∩ (h' • 𝓑)) = 0 := hB.aedisjoint hne'
      refine measure_mono_null (t := Prod.snd ⁻¹' ((h • 𝓑) ∩ (h' • 𝓑))) ?_
        (Measure.quasiMeasurePreserving_snd.preimage_null hnull)
      rintro p ⟨hp, hp'⟩
      refine ⟨?_, ?_⟩
      · rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
        simpa [h] using (memS γ p hp).2
      · rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
        simpa [h'] using (memS γ' p hp').2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFundamentalDomainProdOfKernelImageStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFundamentalDomain_prod_of_kernel_image : ∀ (N G : Type) [Group N] [Group G] [MeasurableSpace N] [MeasurableSpace G] [MeasurableMul N] [MeasurableMul G] (ν : Measure N) (μ : Measure G) [SFinite ν] [SFinite μ] [ν.IsMulLeftInvariant] [μ.IsMulLeftInvariant] (Γ : Subgroup (N × G)) [Countable Γ] (𝓐 : Set N) (𝓑 : Set G), IsFundamentalDomain (Γ.comap (MonoidHom.inl N G)) 𝓐 ν → IsFundamentalDomain (Γ.map (MonoidHom.snd N G)) 𝓑 μ → IsFundamentalDomain Γ (𝓐 ×ˢ 𝓑) (ν.prod μ) := by
  first | exact @GlobalTheory.isFundamentalDomain_prod_of_ker_image | exact GlobalTheory.isFundamentalDomain_prod_of_ker_image | (intros; apply GlobalTheory.isFundamentalDomain_prod_of_ker_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralUnfoldSumTransitiveOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralUnfoldSumTransitiveOrbit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal Pointwise

namespace GlobalTheory
namespace Unf

theorem lintegral_integral_unfold_transitive : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (y₀ : Y), (∀ y, ∃ γ : Γ, γ • y₀ = y) → ∀ (𝓕 𝓖 : Set H), IsFundamentalDomain Γ 𝓕 ν → IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype) 𝓖 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → (∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν) ∧ (∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → ∫ h in 𝓖, Φ y₀ h ∂ν = ∫ h in 𝓕, ∑' y, Φ y h ∂ν) := by
  intro H _ _ _ ν _ Γ _ Y _ _ y₀ htr 𝓕 𝓖 hF hG Φ hΦ hinv
  set S : Subgroup H := (MulAction.stabilizer Γ y₀).map Γ.subtype with hSdef
  haveI : Countable S := by
    have hle : S ≤ Γ := Subgroup.map_subtype_le _
    exact Function.Injective.countable (Subgroup.inclusion_injective hle)
  choose σ hσ using htr
  have hO : ∀ γ : Γ, γ • y₀ ∈ (Set.univ : Set Y) := fun _ => Set.mem_univ _
  have hσ' : ∀ a : (Set.univ : Set Y), σ a • y₀ = a := fun a => hσ a
  let pull (g : H) : Set H := (fun h => g * h) ⁻¹' 𝓕
  have hnull (g : H) : NullMeasurableSet (pull g) ν :=
    hF.nullMeasurableSet.preimage (measurePreserving_mul_left ν g).quasiMeasurePreserving
  have hpull (c : Γ) : pull (c : H) = c⁻¹ • 𝓕 := by
    ext x
    simp [pull, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  have hG' : IsFundamentalDomain S (⋃ y : Y, pull (σ y : H)) ν := by
    refine ⟨.iUnion (fun y => hnull _), ?_, ?_⟩
    · filter_upwards [hF.ae_covers] with x ⟨γ, hγ⟩
      have hs : (σ (γ • y₀))⁻¹ * γ ∈ MulAction.stabilizer Γ y₀ := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hσ]
      refine ⟨⟨Γ.subtype ((σ (γ • y₀))⁻¹ * γ), Subgroup.mem_map_of_mem _ hs⟩,
        Set.mem_iUnion.2 ⟨γ • y₀, ?_⟩⟩
      simpa [pull, Subgroup.smul_def, mul_assoc] using hγ
    · rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hst
      have hset : ∀ (u : Γ) (hu : u ∈ MulAction.stabilizer Γ y₀) (a : Y),
          (⟨Γ.subtype u, Subgroup.mem_map_of_mem _ hu⟩ : S) • pull (σ a : H) =
            (σ a * u⁻¹)⁻¹ • 𝓕 := by
        intro u hu a
        ext x
        simp [Set.mem_smul_set_iff_inv_smul_mem, pull, Subgroup.smul_def, mul_assoc]
      simp only [Function.onFun, Set.smul_set_iUnion, hset s hs, hset t ht]
      refine AEDisjoint.iUnion_left_iff.2 fun a => AEDisjoint.iUnion_right_iff.2 fun b => ?_
      refine hF.aedisjoint (inv_injective.ne fun h => hst ?_)
      have hab : a = b := by
        have h1 := congrArg (· • y₀) h
        simp only [mul_smul] at h1
        rwa [inv_smul_eq_iff.2 hs.symm, inv_smul_eq_iff.2 ht.symm, hσ, hσ] at h1
      subst hab
      have : s = t := inv_injective (mul_left_cancel h)
      subst this
      rfl
  have hinvS : ∀ (s : S) (h : H), Φ y₀ (s • h) = Φ y₀ h := by
    rintro ⟨s, hs⟩ h
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
    have := hinv t y₀ h
    rw [show t • y₀ = y₀ from ht] at this
    simpa [Subgroup.smul_def] using this
  have hfun : ∀ (y : Y) (h : H), Φ y ((σ y : H) * h) = Φ y₀ h := fun y h => by
    have := hinv (σ y) y₀ h
    rwa [hσ y] at this
  have hlint : ∀ y : Y, ∫⁻ h in pull (σ y : H), ‖Φ y₀ h‖ₑ ∂ν
      = ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν := fun y => by
    rw [← (measurePreserving_mul_left ν (σ y : H)).setLIntegral_comp_preimage_emb (measurableEmbedding_mulLeft (σ y : H)) (fun h => ‖Φ y h‖ₑ) 𝓕]
    simp only [hfun, pull]
  have hint : ∀ y : Y, ∫ h in pull (σ y : H), Φ y₀ h ∂ν
      = ∫ h in 𝓕, Φ y h ∂ν := fun y => by
    rw [← (measurePreserving_mul_left ν (σ y : H)).setIntegral_preimage_emb (measurableEmbedding_mulLeft (σ y : H)) (Φ y) 𝓕]
    simp only [hfun, pull]
  have hd : Pairwise (Function.onFun (AEDisjoint ν) fun y : Y =>
      pull (σ y : H)) := by
    intro a b hab
    dsimp only [Function.onFun]
    rw [hpull, hpull]
    refine hF.aedisjoint (inv_injective.ne fun h => hab ?_)
    rw [← hσ a, ← hσ b, h]
  have hL1 : ∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν
      = ∫⁻ h in ⋃ y : Y, pull (σ y : H), ‖Φ y₀ h‖ₑ ∂ν :=
    hG.setLIntegral_eq hG' (fun h => ‖Φ y₀ h‖ₑ) (fun s h => by simp only [hinvS])
  have hL2 : ∫⁻ h in ⋃ y : Y, pull (σ y : H), ‖Φ y₀ h‖ₑ ∂ν
      = ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν := by
    rw [lintegral_iUnion₀ (fun y => hnull _) hd]
    simp only [hlint]
  have hL3 : ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν = ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν :=
    lintegral_tsum fun y => (hΦ y).enorm.aemeasurable
  have hmain : ∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν := by
    rw [hL1, hL2, hL3]
  refine ⟨hmain, fun hfin => ?_⟩
  have hfin' : ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ := by rwa [← hL3]
  have hI : IntegrableOn (Φ y₀) (⋃ y : Y, pull (σ y : H)) ν := by
    refine ⟨(hΦ y₀).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hL2]
    exact lt_top_iff_ne_top.2 hfin'
  have hI1 : ∫ h in 𝓖, Φ y₀ h ∂ν
      = ∫ h in ⋃ y : Y, pull (σ y : H), Φ y₀ h ∂ν :=
    hG.setIntegral_eq hG' (fun s h => hinvS s h)
  rw [hI1, integral_iUnion_ae (fun y => hnull _) hd hI]
  simp only [hint]
  exact (integral_tsum (fun y => (hΦ y).aestronglyMeasurable) hfin').symm

end Unf
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralUnfoldSumTransitiveOrbitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_unfold_sum_transitive_orbit : ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y] [MulAction Γ Y] (y₀ : Y), (∀ y, ∃ γ : Γ, γ • y₀ = y) → ∀ (𝓕 𝓖 : Set H), IsFundamentalDomain Γ 𝓕 ν → IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype) 𝓖 ν → ∀ Φ : Y → H → ℂ, (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) → (∫⁻ h in 𝓖, ‖Φ y₀ h‖ₑ ∂ν = ∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν) ∧ (∫⁻ h in 𝓕, ∑' y, ‖Φ y h‖ₑ ∂ν ≠ ⊤ → ∫ h in 𝓖, Φ y₀ h ∂ν = ∫ h in 𝓕, ∑' y, Φ y h ∂ν) := by
  first | exact @GlobalTheory.Unf.lintegral_integral_unfold_transitive | exact GlobalTheory.Unf.lintegral_integral_unfold_transitive | (intros; apply GlobalTheory.Unf.lintegral_integral_unfold_transitive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMulRightInvariantMapWittFlagCoordinatesHaar
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMulRightInvariantMapWittFlagCoordinatesHaar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf.HaarCoord

theorem measurePreserving_skew_add {A B : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] [μ.IsAddLeftInvariant] {f : B → A} (hf : Measurable f) :
    MeasurePreserving (fun p : A × B => (f p.2 + p.1, p.2)) (μ.prod ν) (μ.prod ν) := by
  have h : MeasurePreserving (fun p : B × A => (id p.1, f p.1 + p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (g := fun b a => f b + a)
      ((hf.comp measurable_fst).add measurable_snd) (Filter.Eventually.of_forall fun b => map_add_left_eq_self μ (f b))
  exact Measure.measurePreserving_swap.comp (h.comp Measure.measurePreserving_swap)

theorem isMulRightInvariant_map {X G : Type*} [MeasurableSpace X] [MeasurableSpace G] [Mul G] (P : Measure X) (e : X ≃ᵐ G)
    (h : ∀ q, ∃ T : X → X, MeasurePreserving T P P ∧ ∀ p, e (T p) = e p * e q) : (P.map e).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨T, hT, hTe⟩ := h (e.symm g)
  have hg : (fun x : G => x * g) = e ∘ T ∘ e.symm := by
    funext x
    simp only [Function.comp, hTe, e.apply_symm_apply]
  rw [hg]
  have h1 : MeasurePreserving e P (P.map e) := ⟨e.measurable, rfl⟩
  exact (h1.comp (hT.comp (h1.symm e))).map_eq

theorem coord_mul {D : D7} {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (c c' : skewA D ρ) (b b' : Mx D ρ V₀.rank)
    (u u' : GL (Fin ρ) (AE D)) :
    d.nC ((skewConj u.1 c' + cComm V₀ b (u.1 ⬝ b')) + c) * (d.nB (u.1 ⬝ b' + b) * d.levi (u * u')) =
      d.nC c * (d.nB b * d.levi u) * (d.nC c' * (d.nB b' * d.levi u')) := by
  have h1 : d.levi u * (d.nC c' * (d.nB b' * d.levi u')) =
      d.nC (skewConj u.1 c') * (d.nB (u.1 ⬝ b') * d.levi (u * u')) := by
    rw [← mul_assoc, d.levi_mul_nC, mul_assoc, ← mul_assoc (d.levi u), d.levi_mul_nB, mul_assoc, map_mul]
  rw [mul_assoc, mul_assoc, h1, ← mul_assoc (d.nB b), ← d.nC_mul_nB, mul_assoc, ← mul_assoc (d.nB b), d.nB_mul_nB,
    ← d.nC_mul_nB, add_comm _ c, add_comm _ b, d.nC_add, d.nC_add]
  simp only [mul_assoc]

theorem measurableAdd₂_addSubgroup {A : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] (H : AddSubgroup A) :
    MeasurableAdd₂ H :=
  ⟨Measurable.subtype_mk ((measurable_subtype_coe.comp measurable_fst).add (measurable_subtype_coe.comp measurable_snd))⟩

theorem measurePreserving_triple {A B U : Type*} [AddGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [AddGroup B]
    [MeasurableSpace B] [MeasurableAdd₂ B] [Mul U] [MeasurableSpace U] [MeasurableMul U]
    (l : Measure A) (μ : Measure B) (ν : Measure U) [SFinite l] [SFinite μ] [SFinite ν] [l.IsAddLeftInvariant]
    [μ.IsAddLeftInvariant] [ν.IsMulRightInvariant] {f : B × U → A} (hf : Measurable f) {g : U → B} (hg : Measurable g)
    (u' : U) :
    MeasurePreserving (fun p : A × (B × U) => (f p.2 + p.1, (g p.2.2 + p.2.1, p.2.2 * u')))
      (l.prod (μ.prod ν)) (l.prod (μ.prod ν)) := by
  have T1 := measurePreserving_skew_add l (μ.prod ν) hf
  have T2 := (MeasurePreserving.id l).prod (measurePreserving_skew_add μ ν hg)
  have T3 := (MeasurePreserving.id l).prod ((MeasurePreserving.id μ).prod (measurePreserving_mul_right ν u'))
  exact T3.comp (T2.comp T1)

theorem continuous_UX_val (D : D7) (ρ : ℕ) : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_UX_mul {D : D7} {ρ n : ℕ} (b' : Mx D ρ n) : Continuous fun u : UX D ρ => (u.1.1 ⬝ b' : Mx D ρ n) :=
  (continuous_UX_val D ρ).matrix_mul continuous_const

theorem continuous_skewConj {D : D7} {ρ : ℕ} (c' : skewA D ρ) : Continuous fun a : Mx D ρ ρ => skewConj a c' := by
  have h1 : Continuous fun a : Mx D ρ ρ => (a ⬝ c'.1 : Mx D ρ ρ) := continuous_id.matrix_mul continuous_const
  have h2 : Continuous fun a : Mx D ρ ρ => (a ⬝ c'.1 ⬝ adj a : Mx D ρ ρ) := h1.matrix_mul continuous_adj
  exact Continuous.subtype_mk h2 _

theorem continuous_cComm {D : D7} (V₀ : HSp D) (ρ : ℕ) :
    Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank => cComm V₀ x.1 x.2 := by
  have := (lattice_Mx D ρ ρ).1
  have : ContinuousSub (Mx D ρ ρ) := IsTopologicalAddGroup.to_continuousSub
  have hp : Continuous (plus V₀ : Mx D ρ V₀.rank → _) := continuous_const.matrix_mul continuous_adj
  have h1 : Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank => (x.2 ⬝ plus V₀ x.1 : Mx D ρ ρ) :=
    continuous_snd.matrix_mul (hp.comp continuous_fst)
  have h2 : Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank => (x.1 ⬝ plus V₀ x.2 : Mx D ρ ρ) :=
    continuous_fst.matrix_mul (hp.comp continuous_snd)
  have h3 : Continuous fun x : Mx D ρ V₀.rank × Mx D ρ V₀.rank =>
      (half D • (x.2 ⬝ plus V₀ x.1 - x.1 ⬝ plus V₀ x.2) : Mx D ρ ρ) := (h1.sub h2).const_smul (half D)
  exact Continuous.subtype_mk h3 _

set_option synthInstance.maxHeartbeats 200000 in
theorem continuous_shift {D : D7} (V₀ : HSp D) (ρ : ℕ) (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) :
    Continuous fun y : Mx D ρ V₀.rank × UX D ρ => skewConj y.2.1.1 c' + cComm V₀ y.1 (y.2.1.1 ⬝ b') := by
  have := (lattice_Mx D ρ ρ).1
  have h1 : Continuous fun y : Mx D ρ V₀.rank × UX D ρ => skewConj y.2.1.1 c' :=
    (continuous_skewConj c').comp (f := fun y : Mx D ρ V₀.rank × UX D ρ => y.2.1.1)
      ((continuous_UX_val D ρ).comp continuous_snd)
  have h2 : Continuous fun y : Mx D ρ V₀.rank × UX D ρ => cComm V₀ y.1 (y.2.1.1 ⬝ b') :=
    (continuous_cComm V₀ ρ).comp (f := fun y : Mx D ρ V₀.rank × UX D ρ => (y.1, (y.2.1.1 ⬝ b' : Mx D ρ V₀.rank)))
      (continuous_fst.prodMk ((continuous_UX_mul b').comp continuous_snd))
  exact h1.add h2

set_option synthInstance.maxHeartbeats 200000 in
theorem measurable_shift {D : D7} (V₀ : HSp D) (ρ : ℕ) (c' : skewA D ρ) (b' : Mx D ρ V₀.rank) :
    Measurable fun y : Mx D ρ V₀.rank × UX D ρ => skewConj y.2.1.1 c' + cComm V₀ y.1 (y.2.1.1 ⬝ b') := by
  obtain ⟨b1, b2, b3, b4, -⟩ := lattice_Mx D ρ V₀.rank
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  exact (continuous_shift V₀ ρ c' b').measurable


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 400000 in
theorem isMulRightInvariant_map_coord : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → ((lC.prod (vb.μ.prod vU.ν)).map e).IsMulRightInvariant := by
  intro D V V₀ ρ d vb vU e he lC hC hS
  obtain ⟨a1, a2, a3, a4, -⟩ := lattice_Mx D ρ ρ
  obtain ⟨b1, b2, b3, b4, -⟩ := lattice_Mx D ρ V₀.rank
  obtain ⟨u1, u2, u3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := vb.covol.1
  have := vU.unit.1
  have : vU.ν.IsMulRightInvariant := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ vU.unit
  have : SFinite vb.μ := inferInstance
  have : SFinite vU.ν := by
    haveI : SigmaFinite vU.ν := Measure.IsHaarMeasure.sigmaFinite _
    haveI : ∀ n, Fact (vU.ν (disjointed (spanningSets vU.ν) n) < ⊤) :=
      fun n => ⟨(measure_mono (disjointed_subset _ _)).trans_lt (measure_spanningSets_lt_top vU.ν n)⟩
    exact ⟨⟨fun n => vU.ν.restrict (disjointed (spanningSets vU.ν) n), fun _ => inferInstance,
      (sum_restrict_disjointed_spanningSets vU.ν vU.ν).symm⟩⟩
  have : MeasurableAdd₂ (Mx D ρ ρ) := inferInstance
  have : MeasurableAdd₂ (skewA D ρ) := measurableAdd₂_addSubgroup _
  have : MeasurableAdd₂ (Mx D ρ V₀.rank) := inferInstance
  have : MeasurableMul (UX D ρ) := inferInstance
  refine isMulRightInvariant_map _ e ?_
  rintro ⟨c', b', u'⟩
  refine ⟨_, measurePreserving_triple lC vb.μ vU.ν (measurable_shift V₀ ρ c' b') (continuous_UX_mul b').measurable u', ?_⟩
  rintro ⟨c, b, u⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, he, he, he]
  exact coord_mul d c c' b b' u.1 u'.1

end GlobalTheory.Unf.HaarCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMulRightInvariantMapWittFlagCoordinatesHaarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMulRightInvariant_map_wittFlagCoordinates_haar : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → ((lC.prod (vb.μ.prod vU.ν)).map e).IsMulRightInvariant := by
  first | exact @GlobalTheory.Unf.HaarCoord.isMulRightInvariant_map_coord | exact GlobalTheory.Unf.HaarCoord.isMulRightInvariant_map_coord | (intros; apply GlobalTheory.Unf.HaarCoord.isMulRightInvariant_map_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmallCompactLevelSymplecticCharacterTrivia
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmallCompactLevelSymplecticCharacterTrivia
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.SmallLevel

theorem exists_open_subgroup (F : Type) [Field F] [NumberField F] (V : Set (Af F)) (hV : V ∈ 𝓝 (0 : Af F)) :
    ∃ S : AddSubgroup (Af F), IsOpen (S : Set (Af F)) ∧ (S : Set (Af F)) ⊆ V := by
  obtain ⟨M, hM, hMV⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F V hV
  let S : AddSubgroup (Af F) :=
    { carrier := {c | ∃ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ c = M • a}
      zero_mem' := ⟨0, fun v => zero_mem _, (smul_zero M).symm⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, fun v => add_mem (ha v) (hb v), (smul_add M a b).symm⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun v => neg_mem (ha v), (smul_neg M a).symm⟩ }
  refine ⟨S, S.isOpen_of_mem_nhds (g := 0) (GlobalTheory.AdLat.OpenLat.nsmul_integral_mem_nhds F M hM), ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact hMV a ha

theorem infPart_smul_eq_zero {D : D7} (y : Af D.host.F) (x : AE D) : infPart D (pairA D.host.F 0 y • x) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 y)) = 0 := by
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [this, zero_mul]

theorem exists_closed_level (D : D7) (m n : ℕ) (N : Set (Mx D m n)) (hN : N ∈ 𝓝 (0 : Mx D m n)) :
    ∃ K : AddSubgroup (Mx D m n), IsClosed (K : Set (Mx D m n)) ∧ (K : Set (Mx D m n)) ⊆ N ∧
      (∀ u ∈ K, u.map (infPart D) = 0) ∧
      ∃ U : AddSubgroup (Mx D m n), IsOpen (U : Set (Mx D m n)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K := by
  classical
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (AE D) := IsModuleTopology.topologicalAddGroup (AF D.host.F) _
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : T2Space (InfiniteAdeleRing D.host.F) := inferInstanceAs (T2Space ((v : InfinitePlace D.host.F) → v.Completion))
  let b := Module.finBasis D.host.F D.host.E
  let B := Algebra.TensorProduct.basis (AF D.host.F) b
  let Φ : (Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Af D.host.F) → Mx D m n :=
    fun x i j => ∑ k, pairA D.host.F 0 (x (i, j, k)) • B k
  have hΦ : Continuous Φ := by
    refine continuous_pi fun i => continuous_pi fun j => continuous_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun x : Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
        pairA D.host.F 0 (x (i, j, k)) := continuous_const.prodMk (continuous_apply _)
    exact h1.smul continuous_const
  have h0 : Φ 0 = 0 := by
    funext i j
    refine Finset.sum_eq_zero fun k _ => ?_
    exact zero_smul (AF D.host.F) (B k)
  have h1 : Φ ⁻¹' N ∈ 𝓝 0 := hΦ.continuousAt.preimage_mem_nhds (h0 ▸ hN)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, -, t, ht, hsub⟩ := h1
  obtain ⟨S, hS, hSt⟩ := exists_open_subgroup D.host.F (⋂ p, t p) (Filter.iInter_mem.mpr ht)
  let c : Fin m × Fin n × Fin (Module.finrank D.host.F D.host.E) → Mx D m n →+ AF D.host.F := fun p =>
    { toFun := fun u => B.coord p.2.2 (u p.1 p.2.1)
      map_zero' := map_zero _
      map_add' := fun u u' => map_add _ _ _ }
  have hc : ∀ p, Continuous (c p) := fun p =>
    (IsModuleTopology.continuous_of_linearMap (B.coord p.2.2)).comp
      ((continuous_apply p.2.1).comp (continuous_apply p.1))
  let U : AddSubgroup (Mx D m n) := ⨅ p, S.comap ((sndA D.host.F).toRingHom.toAddMonoidHom.comp (c p))
  let Z : AddSubgroup (Mx D m n) := ⨅ p, ((fstA D.host.F).toRingHom.toAddMonoidHom.comp (c p)).ker
  have hU : ∀ u, u ∈ U ↔ ∀ p, (c p u).2 ∈ S := fun u => AddSubgroup.mem_iInf
  have hZ : ∀ u, u ∈ Z ↔ ∀ p, (c p u).1 = 0 := fun u => AddSubgroup.mem_iInf
  have hUe : (U : Set (Mx D m n)) = ⋂ p, (fun u => (c p u).2) ⁻¹' S := by
    ext u; rw [Set.mem_iInter]; exact hU u
  have hZe : (Z : Set (Mx D m n)) = ⋂ p, {u | (c p u).1 = 0} := by
    ext u; rw [Set.mem_iInter]; exact hZ u
  have hrec : ∀ u ∈ Z, Φ (fun p => (c p u).2) = u := by
    intro u hu
    funext i j
    conv_rhs => rw [← B.sum_repr (u i j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact Prod.ext ((hZ u).mp hu (i, j, k)).symm rfl
  refine ⟨U ⊓ Z, ?_, ?_, ?_, U, ?_, ?_⟩
  · rw [AddSubgroup.coe_inf, hUe, hZe]
    exact (isClosed_iInter fun p => (S.isClosed_of_isOpen hS).preimage (continuous_snd.comp (hc p))).inter
      (isClosed_iInter fun p => isClosed_eq (continuous_fst.comp (hc p)) continuous_const)
  · intro u hu
    have h4 : (fun p => (c p u).2) ∈ I.pi t := fun p _ => Set.mem_iInter.mp (hSt ((hU u).mp hu.1 p)) p
    have h5 := hsub h4
    rwa [Set.mem_preimage, hrec u hu.2] at h5
  · intro u hu
    funext i j
    have h4 : ∑ k, pairA D.host.F 0 (c (i, j, k) u).2 • B k = u i j := congrFun (congrFun (hrec u hu.2) i) j
    rw [Matrix.map_apply, ← h4]
    exact (infPart D).toAddMonoidHom.ker.sum_mem fun k _ => infPart_smul_eq_zero _ _
  · rw [hUe]
    exact isOpen_iInter_of_finite fun p => hS.preimage (continuous_snd.comp (hc p))
  · intro u hu hu'
    refine ⟨hu, (hZ u).mpr fun p => ?_⟩
    have h2 := GlobalTheory.FinTranslate.smul_eq_zero_of_inf (congrFun (congrFun hu' p.1) p.2.1)
    have h3 : GlobalTheory.FinTranslate.eInf D * c p u = 0 := by
      have := congrArg (B.coord p.2.2) h2
      rwa [map_smul, map_zero, smul_eq_mul] at this
    exact (one_mul _).symm.trans (congrArg Prod.fst h3)

theorem exists_small_level : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D), ∀ N ∈ 𝓝 (0 : WO A T), ∃ K : AddSubgroup (WO A T), IsCompact (K : Set (WO A T)) ∧ (K : Set (WO A T)) ⊆ N ∧ (∀ u ∈ K, u.map (infPart D) = 0) ∧ (∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K) ∧ ∀ u ∈ K, ∀ u' ∈ K, ψ (symplOH A T u u') = 1 := by
  intro D ψ hψ A T N hN
  haveI : LocallyCompactSpace (WO A T) := (GlobalTheory.MixModel.lattice_Mx D T.rank A.rank).2.1
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : WO A T)
  have hs : Continuous fun p : WO A T × WO A T => (symplOH A T p.1 p.2).2 :=
    continuous_snd.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_fst continuous_snd)
  have h2 := hs.continuousAt.preimage_mem_nhds (x := (0, 0)) (t := {a | ψ (pairA D.host.F 0 a) = 1})
    (by
      have h0 : (symplOH A T (0 : WO A T) 0).2 = 0 := congrArg Prod.snd (GlobalTheory.FinTranslate.symplOH_zero_left A T 0)
      have h1 := GlobalTheory.FinTranslate.ker_mem_nhds hψ.1.1 hψ.1.2.1
      rwa [← h0] at h1)
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := mem_nhds_prod_iff.mp h2
  obtain ⟨K, hK, hKN, hKf, hKU⟩ := exists_closed_level D T.rank A.rank (N ∩ C ∩ (P ∩ Q))
    (Filter.inter_mem (Filter.inter_mem hN hC0) (Filter.inter_mem hP hQ))
  refine ⟨K, hC.of_isClosed_subset hK fun u hu => (hKN hu).1.2, fun u hu => (hKN hu).1.1, hKf, hKU,
    fun u hu u' hu' => ?_⟩
  have h3 : GlobalTheory.FinTranslate.eInf D * symplOH A T u u' = 0 := by
    rw [← GlobalTheory.FinTranslate.symplOH_smul_right, GlobalTheory.FinTranslate.smul_fin (hKf u' hu'),
      GlobalTheory.FinTranslate.symplOH_zero_right]
  have h4 : symplOH A T u u' = pairA D.host.F 0 (symplOH A T u u').2 :=
    Prod.ext ((one_mul _).symm.trans (congrArg Prod.fst h3)) rfl
  rw [h4]
  have h5 := hPQ (Set.mk_mem_prod (hKN hu).2.1 (hKN hu').2.2)
  rw [Set.mem_preimage, Set.mem_setOf_eq] at h5
  exact h5

end GlobalTheory.SmallLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSmallCompactLevelSymplecticCharacterTriviaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_compact_level_symplecticCharacter_trivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D), ∀ N ∈ 𝓝 (0 : WO A T), ∃ K : AddSubgroup (WO A T), IsCompact (K : Set (WO A T)) ∧ (K : Set (WO A T)) ⊆ N ∧ (∀ u ∈ K, u.map (infPart D) = 0) ∧ (∃ U : AddSubgroup (WO A T), IsOpen (U : Set (WO A T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → u ∈ K) ∧ ∀ u ∈ K, ∀ u' ∈ K, ψ (symplOH A T u u') = 1 := by
  first | exact @GlobalTheory.SmallLevel.exists_small_level | exact GlobalTheory.SmallLevel.exists_small_level | (intros; apply GlobalTheory.SmallLevel.exists_small_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryTransvectionUnitaryAndConjugation
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EichlerTransvectionUnitaryInverseConj
open Matrix

namespace GlobalTheory

theorem eichlerTransvection_unitary_inverse_conj :
    ∀ (A : Type) [CommRing A] [StarRing A] [Invertible (2 : A)] (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι A) (_ : Gᴴ = G) (h : (ι → A) → (ι → A) → A) (_ : ∀ x y, h x y = star y ⬝ᵥ G.mulVec x) (E : (ι → A) → (ι → A) → (ι → A) → (ι → A)) (_ : ∀ w v y, E w v y = y + h y v • w - h y w • v - (⅟(2 : A) * h v v * h y w) • w), (∀ w v, h w w = 0 → h w v = 0 → ∀ x y, h (E w v x) (E w v y) = h x y) ∧ (∀ w v, h w w = 0 → h w v = 0 → ∀ y, E w (-v) (E w v y) = y) ∧ ∀ (g : Matrix ι ι A), (∀ x y, h (g.mulVec x) (g.mulVec y) = h x y) → ∀ w v y, g.mulVec (E w v y) = E (g.mulVec w) (g.mulVec v) (g.mulVec y) := by
  intro A _ _ _ ι _ _ G hG h hh E hE
  have addl : ∀ x x' y, h (x + x') y = h x y + h x' y := by
    intro x x' y; simp only [hh, mulVec_add, dotProduct_add]
  have subl : ∀ x x' y, h (x - x') y = h x y - h x' y := by
    intro x x' y; simp only [hh, mulVec_sub, dotProduct_sub]
  have negl : ∀ x y, h (-x) y = - h x y := by
    intro x y; simp only [hh, mulVec_neg, dotProduct_neg]
  have smull : ∀ (a : A) x y, h (a • x) y = a * h x y := by
    intro a x y; simp only [hh, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have addr : ∀ x y y', h x (y + y') = h x y + h x y' := by
    intro x y y'; simp only [hh, star_add, add_dotProduct]
  have subr : ∀ x y y', h x (y - y') = h x y - h x y' := by
    intro x y y'; simp only [hh, star_sub, sub_dotProduct]
  have negr : ∀ x y, h x (-y) = - h x y := by
    intro x y; simp only [hh, star_neg, neg_dotProduct]
  have smulr : ∀ (a : A) x y, h x (a • y) = star a * h x y := by
    intro a x y; simp only [hh, star_smul, smul_dotProduct, smul_eq_mul]
  have symm : ∀ x y, star (h x y) = h y x := by
    intro x y
    rw [hh, hh, ← star_dotProduct_star, star_star, star_mulVec, hG, dotProduct_mulVec]
  have h2 : ⅟(2 : A) * 2 = 1 := invOf_mul_self _
  have s2 : star (⅟(2 : A)) = ⅟(2 : A) := by
    have := congrArg star h2
    rw [star_mul', star_one, star_ofNat] at this
    linear_combination (⅟(2 : A)) * this - (star (⅟(2 : A))) * h2
  refine ⟨?_, ?_, ?_⟩
  · intro w v hww hwv x y
    have hvw : h v w = 0 := by rw [← symm, hwv, star_zero]
    rw [hE, hE]
    simp only [addl, subl, smull, addr, subr, smulr, star_mul', symm, s2, hww, hwv, hvw]
    linear_combination (-(h v v * h x w * h w y)) * h2
  · intro w v hww hwv y
    have hvw : h v w = 0 := by rw [← symm, hwv, star_zero]
    rw [hE w (-v), hE w v]
    simp only [addl, subl, smull, negl, negr, hww, hwv, hvw]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    linear_combination (-(h v v * h y w * w i)) * h2
  · intro g hg w v y
    rw [hE, hE]
    simp only [hg, mulVec_add, mulVec_sub, mulVec_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryTransvectionUnitaryAndConjugation
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open GlobalTheory.MixModel GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransvAdelic

variable {D : D7}

theorem form_mulVec (S : HSp D) {k l : ℕ} (M : Mx D S.rank k) (N : Mx D S.rank l) (x : Fin k → AE D)
    (y : Fin l → AE D) :
    form S (M *ᵥ x) (N *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj N ⬝ (gA S ⬝ M)) *ᵥ x) := by
  have h : (fun i => cA D ((N *ᵥ y) i)) = (N.map (cA D)) *ᵥ fun i => cA D (y i) := by
    funext i
    exact RingHom.map_mulVec (cA D) N y i
  rw [form, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec _ (adj N), adj,
    Matrix.vecMul_transpose]

theorem form_act (S : HSp D) (g : GA D S) (x y : VA S) : form S (act S g x) (act S g y) = form S x y := by
  rw [act, act, form_mulVec, mt_unitary, form]

theorem unitary_of_form (S : HSp D) (M : Mx D S.rank S.rank)
    (h : ∀ x y, form S (M *ᵥ x) (M *ᵥ y) = form S x y) : adj M * (gA S * M) = gA S := by
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  have e : (fun k => cA D ((Pi.single i 1 : VA S) k)) = Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [form_mulVec, form, e] at this
  simpa using this

theorem form_vecX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (a : Fin ρ → AE D) :
    form S (vecX d a) (vecX d a) = 0 := by
  rw [vecX, form_mulVec, d.gram_XX, Matrix.zero_mulVec, dotProduct_zero]

@[reducible] def starRingA (D : D7) : StarRing (AE D) where
  star := cA D
  star_involutive := cA_cA
  star_mul x y := by rw [map_mul, mul_comm]
  star_add := map_add (cA D)

@[reducible] def invTwo (D : D7) : Invertible (2 : AE D) where
  invOf := half D
  invOf_mul_self := by rw [mul_two, half_add_half]
  mul_invOf_self := by rw [two_mul, half_add_half]

theorem form_transv (S : HSp D) (w v : VA S) (hw : form S w w = 0) (hv : form S w v = 0) (x y : VA S) :
    form S (transv S w v x) (transv S w v y) = form S x y := by
  letI := starRingA D
  letI := invTwo D
  exact (GlobalTheory.eichlerTransvection_unitary_inverse_conj (AE D) (Fin S.rank) (gA S) (adj_gA S) (form S)
    (fun _ _ => rfl) (transv S) (fun _ _ _ => rfl)).1 w v hw hv x y

def transvLin (S : HSp D) (w v : VA S) : VA S →ₗ[AE D] VA S where
  toFun := transv S w v
  map_add' x y := by
    funext i
    simp only [transv, form, Matrix.mulVec_add, dotProduct_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  map_smul' s x := by
    funext i
    simp only [transv, form, Matrix.mulVec_smul, dotProduct_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

theorem toMatrix_transvLin (S : HSp D) (w v y : VA S) :
    LinearMap.toMatrix' (transvLin S w v) *ᵥ y = transv S w v y := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rfl

theorem act_transv (S : HSp D) (g : GA D S) (w v y : VA S) :
    act S g (transv S w v y) = transv S (act S g w) (act S g v) (act S g y) := by
  rw [transv, transv, form_act, form_act, form_act]
  simp only [act, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul]

theorem act_mul (S : HSp D) (g h : GA D S) (y : VA S) : act S (g * h) y = act S g (act S h y) := by
  rw [act, act, act, mt_mul, Matrix.mulVec_mulVec]

theorem transv_unitary_conj :
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvUnitary D ∧ GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvConj D := by
  intro D
  refine ⟨fun S S₀ ρ d a v hv => ?_, fun S S₀ ρ d a v _ u g hu y => ?_⟩
  · refine ⟨ofMat S (LinearMap.toMatrix' (transvLin S (vecX d a) v)) (unitary_of_form S _ fun x y => ?_), fun y => ?_⟩
    · rw [toMatrix_transvLin, toMatrix_transvLin, form_transv S _ _ (form_vecX d a) hv]
    · rw [act, mt_ofMat, toMatrix_transvLin]
  · rw [act_mul, act_mul, hu, act_transv, ← act_mul S g g⁻¹, mul_inv_cancel]
    congr 1
    rw [act, mt_one, Matrix.one_mulVec]

end GlobalTheory.TransvAdelic

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryTransvectionUnitaryAndConjugationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTransvection_unitary_and_conjugation : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvUnitary D ∧ GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvConj D := by
  first | exact @GlobalTheory.TransvAdelic.transv_unitary_conj | exact GlobalTheory.TransvAdelic.transv_unitary_conj | (intros; apply GlobalTheory.TransvAdelic.transv_unitary_conj <;> assumption)
end
end
