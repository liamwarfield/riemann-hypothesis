module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedLatticeFiniteExpansionsLocalField
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliser
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopVectorMemExtraProjection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoprimeScalingIdealValuationLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem natInv_mem_adicIntegers (F : Type) [Field F] [NumberField F] (T : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (h : ((T : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    algebraMap F (v.adicCompletion F) ((T : F)⁻¹) ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (T : F) = 1 := by
    have : (T : F) = algebraMap (𝓞 F) F (T : 𝓞 F) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) ((T : F)⁻¹)) = v.valuation F ((T : F)⁻¹) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h2, map_inv₀, h1, inv_one]

theorem natInv_smul_mem_intAf (F : Type) [Field F] [NumberField F] (T : ℕ) (v : HeightOneSpectrum (𝓞 F))
    (h : ((T : ℕ) : 𝓞 F) ∉ v.asIdeal) (α : Af F) (h1 : α ∈ intAf F) (h2 : ∀ w, w ≠ v → evalV F w α = 0) :
    ((T : F)⁻¹ : F) • α ∈ intAf F ∧ ∀ w, w ≠ v → evalV F w (((T : F)⁻¹ : F) • α) = 0 := by
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · change evalV F w _ ∈ w.adicCompletionIntegers F
    rw [map_smul]
    by_cases hw : w = v
    · subst hw
      rw [Algebra.smul_def]
      exact mul_mem (natInv_mem_adicIntegers F T w h) (h1 w)
    · rw [h2 w hw, smul_zero]; exact zero_mem _
  · rw [map_smul, h2 w hw, smul_zero]

theorem smul_pairA_zero (F : Type) [Field F] [NumberField F] (t : F) (α : Af F) :
    t • pairA F 0 α = pairA F 0 (t • α) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  exact Prod.ext (mul_zero _) rfl

theorem pairA_zero_tmul_smul (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (t : F) (α : Af F) (c : E) :
    pairA F 0 α ⊗ₜ[F] (t • c) = pairA F 0 (t • α) ⊗ₜ[F] c := by
  rw [← smul_pairA_zero, TensorProduct.smul_tmul]

theorem idV_natInv_mul_le (D : D7) (𝔠 : FI D) (T : ℕ) (v : Pl D) (h : ((T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) :
    idV (FractionalIdeal.spanSingleton _ ((T : D.host.E)⁻¹) * 𝔠) v ≤ idV 𝔠 v := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨α, h1, h2, a, ha, rfl⟩
  obtain ⟨c, hc, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 ha
  have e : ((T : D.host.E)⁻¹) * c = ((T : D.host.F)⁻¹ : D.host.F) • c := by
    rw [Algebra.smul_def, map_inv₀, map_natCast]
  obtain ⟨g1, g2⟩ := natInv_smul_mem_intAf D.host.F T v h α h1 h2
  refine AddSubgroup.subset_closure ⟨((T : D.host.F)⁻¹ : D.host.F) • α, g1, g2, c, hc, ?_⟩
  rw [e]
  exact pairA_zero_tmul_smul D.host.F D.host.E _ α c

end GlobalTheory.SeeSaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitLatMonoId
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem sum_pair_eq {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_mul {m n : ℕ} (A B : Matrix (Fin m) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    star x ⬝ᵥ ((Aᴴ * B) *ᵥ y) = star (A *ᵥ x) ⬝ᵥ (B *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

variable (d : HypDec S S₀ ρ)

theorem pair_decomp (x y : Fin S.rank → D.host.E) :
    star x ⬝ᵥ (S.gram *ᵥ y) = star (d.qY *ᵥ x) ⬝ᵥ (d.qX *ᵥ y) + star (d.q0 *ᵥ x) ⬝ᵥ (S₀.gram *ᵥ (d.q0 *ᵥ y)) +
      star (d.qX *ᵥ x) ⬝ᵥ (d.qY *ᵥ y) := by
  rw [gram_eq d, Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add, pair_mul, pair_mul, pair_mul,
    ← Matrix.mulVec_mulVec]

theorem star_single (i : Fin ρ) (b : D.host.E) : star (Pi.single i b : Fin ρ → D.host.E) = Pi.single i (star b) := by
  funext j; by_cases h : j = i <;> simp [h, Pi.single_apply]

theorem pair_e (i : Fin ρ) (b : D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.e *ᵥ Pi.single i b) ⬝ᵥ (S.gram *ᵥ y) = star b * (d.qY *ᵥ y) i := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_e, wittDecomposition_coreProj_mul_e_eq_zero, qY_e, Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add, star_single, single_dotProduct]

theorem pair_e' (i : Fin ρ) (c : D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.e' *ᵥ Pi.single i c) ⬝ᵥ (S.gram *ᵥ y) = star c * (d.qX *ᵥ y) i := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_e', wittZeroProjection_mul_dualBasis_eq_zero, qY_e', Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add, star_single, single_dotProduct]

theorem pair_i₀ (x₀ : Fin S₀.rank → D.host.E) (y : Fin S.rank → D.host.E) :
    star (d.i₀ *ᵥ x₀) ⬝ᵥ (S.gram *ᵥ y) = star x₀ ⬝ᵥ (S₀.gram *ᵥ (d.q0 *ᵥ y)) := by
  rw [pair_decomp d]
  simp only [Matrix.mulVec_mulVec, qX_i₀, wittDecomposition_coreProj_mul_core_eq_one, qY_i₀, Matrix.one_mulVec, Matrix.zero_mulVec, star_zero,
    zero_dotProduct, add_zero, zero_add]

theorem decomp (y : Fin S.rank → D.host.E) : y = d.e *ᵥ (d.qX *ᵥ y) + d.i₀ *ᵥ (d.q0 *ᵥ y) + d.e' *ᵥ (d.qY *ᵥ y) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
    d.sum_eq_one_rat, Matrix.one_mulVec]

theorem exists_ne_zero {𝔟 : FI D} (h : 𝔟 ≠ 0) : ∃ b ∈ 𝔟, b ≠ 0 := by
  by_contra hc
  push_neg at hc
  exact h (FractionalIdeal.eq_zero_iff.2 hc)

theorem exists_ne_zero_dualC (𝔟 : FI D) : ∃ c ∈ dualC 𝔟, c ≠ 0 := by
  obtain ⟨a, ha, hint⟩ := 𝔟.isFractional
  refine ⟨star (algebraMap (𝓞 D.host.E) D.host.E a), fun b hb => ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hint b hb
    have : star b * star (algebraMap (𝓞 D.host.E) D.host.E a) = star (algebraMap (𝓞 D.host.E) D.host.E r) := by
      rw [hr, Algebra.smul_def, star_mul', mul_comm]
    rw [this]
    exact GlobalTheory.HypLattice.star_mem_int ⟨r, rfl⟩
  · rw [Ne, star_eq_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).2 (nonZeroDivisors.ne_zero ha)

theorem dualC_le_span {𝔟 : FI D} (h : 𝔟 ≠ 0) : ∃ γ : D.host.E, dualC 𝔟 ≤ Submodule.span (𝓞 D.host.E) {γ} := by
  obtain ⟨β, hβ, hβ0⟩ := exists_ne_zero h
  refine ⟨(star β)⁻¹, fun c hc => ?_⟩
  obtain ⟨o, ho⟩ := hc β hβ
  have hs : star β ≠ 0 := by rwa [Ne, star_eq_zero]
  refine Submodule.mem_span_singleton.2 ⟨o, ?_⟩
  rw [Algebra.smul_def, ho, mul_comm (star β), mul_assoc, mul_inv_cancel₀ hs, mul_one]

theorem mulVec_single_smul {n : ℕ} (M : Matrix (Fin S.rank) (Fin n) D.host.E) (i : Fin n) {a b : D.host.E} (hb : b ≠ 0) :
    M *ᵥ Pi.single i a = (a * b⁻¹) • (M *ᵥ Pi.single i b) := by
  rw [← Matrix.mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_assoc, inv_mul_cancel₀ hb, mul_one]

variable {L₀ : Lat S₀} {𝔟 : ℕ → FI D}

theorem isLattice_splitL (h𝔟 : ∀ i, 𝔟 i ≠ 0) (hL₀ : Submodule.IsLattice D.host.E L₀) :
    Submodule.IsLattice D.host.E (splitL d L₀ 𝔟) := by
  choose γ hγ using fun i : Fin ρ => dualC_le_span (h𝔟 i)
  refine ⟨?_, ?_⟩
  · let T : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
      (⨆ i : Fin ρ, (𝔟 i : Submodule (𝓞 D.host.E) D.host.E).map
          ((LinearMap.toSpanSingleton D.host.E _ (d.e *ᵥ Pi.single i 1)).restrictScalars (𝓞 D.host.E))) ⊔
        L₀.map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ⊔
        ⨆ i : Fin ρ, (Submodule.span (𝓞 D.host.E) {γ i}).map
          ((LinearMap.toSpanSingleton D.host.E _ (d.e' *ᵥ Pi.single i 1)).restrictScalars (𝓞 D.host.E))
    have hT : T.FG :=
      ((Submodule.fg_iSup _ fun i : Fin ρ => (FractionalIdeal.fg_of_isNoetherianRing le_rfl (𝔟 i)).map _).sup
        (hL₀.fg.map _)).sup (Submodule.fg_iSup _ fun i : Fin ρ => (Submodule.fg_span_singleton _).map _)
    refine hT.of_le fun y hy => ?_
    obtain ⟨h1, h2, h3⟩ := (mem_splitL d L₀ 𝔟 y).1 hy
    have hs : ∀ (M : Matrix (Fin S.rank) (Fin ρ) D.host.E) (w : Fin ρ → D.host.E), M *ᵥ w = ∑ i, w i • (M *ᵥ Pi.single i 1) := by
      intro M w
      conv_lhs => rw [← Finset.univ_sum_single w]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Matrix.mulVec_smul, ← Pi.single_smul', smul_eq_mul, mul_one]
    rw [decomp d y, hs d.e, hs d.e']
    refine add_mem (add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left ?_))
      (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨_, h2, rfl⟩)))
      (Submodule.mem_sup_right ?_)
    · exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i ⟨_, h1 i, rfl⟩
    · exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i ⟨_, hγ i (h3 i), rfl⟩
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem isSelfDualC_splitL (h𝔟 : ∀ i, 𝔟 i ≠ 0) (hL₀ : IsSelfDualC S₀ L₀) : IsSelfDualC S (splitL d L₀ 𝔟) := by
  have hR : ∀ z : D.host.E, (∃ b : 𝓞 D.host.E, (b : D.host.E) = z) ↔ z ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
    fun z => Iff.rfl
  have h0 : ∀ y₀ : Fin S₀.rank → D.host.E, y₀ ∈ L₀ ↔ ∀ x₀ ∈ L₀, star x₀ ⬝ᵥ (S₀.gram *ᵥ y₀) ∈
      (algebraMap (𝓞 D.host.E) D.host.E).range := fun y₀ => by
    rw [hL₀.2 y₀]
    simp only [hR, sum_pair_eq]
  refine ⟨isLattice_splitL d h𝔟 hL₀.1, fun y => ?_⟩
  simp only [hR, sum_pair_eq]
  constructor
  · intro hy x hx
    obtain ⟨hy1, hy2, hy3⟩ := (mem_splitL d L₀ 𝔟 y).1 hy
    obtain ⟨hx1, hx2, hx3⟩ := (mem_splitL d L₀ 𝔟 x).1 hx
    rw [pair_decomp]
    refine add_mem (add_mem (sum_mem fun i _ => ?_) ((h0 _).1 hy2 _ hx2)) (sum_mem fun i _ => ?_)
    · have := GlobalTheory.HypLattice.star_mem_int (hx3 i _ (hy1 i))
      rwa [star_mul', star_star, mul_comm] at this
    · exact hy3 i _ (hx1 i)
  · intro hy
    refine (mem_splitL d L₀ 𝔟 y).2 ⟨fun i => ?_, ?_, fun i => ?_⟩
    · have hi : 𝔟 i ≠ 0 := h𝔟 i
      rw [← inv_inv (𝔟 i), FractionalIdeal.mem_inv_iff (inv_ne_zero hi)]
      intro z hz
      have hc : star z ∈ dualC (𝔟 i) := fun b hb => by
        have := GlobalTheory.HypLattice.star_mem_int (GlobalTheory.HypLattice.mem_one_iff_range.1 ((FractionalIdeal.mem_inv_iff hi).1 hz b hb))
        rwa [star_mul', mul_comm] at this
      have := hy _ (e'_mem (single_mem_of_mem (I := fun j => dualC (𝔟 j)) i hc))
      rw [pair_e', star_star, mul_comm] at this
      exact GlobalTheory.HypLattice.mem_one_iff_range.2 this
    · rw [h0]
      intro x₀ hx₀
      have := hy _ (i₀_mem (d := d) (𝔟 := 𝔟) hx₀)
      rwa [pair_i₀] at this
    · intro b hb
      have := hy _ (e_mem (L₀ := L₀) (single_mem_of_mem (I := fun j => (𝔟 j : Submodule (𝓞 D.host.E) D.host.E)) i hb))
      rwa [pair_e] at this

end GlobalTheory.SeeSaw.SplitLat

namespace GlobalTheory.SeeSaw

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SourceLiftAtGluedPlaceProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SourceLiftAtGluedPlaceProof
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcGl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_mul_blk (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (g : GL n' k) (x : Matrix n (n' ⊕ Fin 1) k) :
    tensCol Ψ a (x * (blk g).val) = tensCol (fun x₀ => Ψ (x₀ * g.val)) a x := by
  simp only [tensCol, blk_val]
  congr 2
  · ext i j
    simp [Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type]
  · ext i
    simp [Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type]

theorem phiOne_smul_left (g : GL n' k) (P : Pair k n') (Q : Pair k n) (x : Matrix n n' k) :
    phiOne (g • P) Q x = phiOne P Q (x * g.val) := by
  classical
  have hs : ∀ (h : GL n' k) (y : n' → k), h • y = h.val *ᵥ y := fun _ _ => rfl
  unfold phiOne
  congr 1
  apply propext
  rw [maps_iff_hasVal, maps_iff_hasVal]
  constructor
  · intro h y a hy
    have := h (g • y) a (hy.gl_smul g)
    simpa [hs, Matrix.mulVec_mulVec] using this
  · intro h y a hy
    have := h (g⁻¹ • y) a (Pair.smul_hasVal.1 hy)
    simpa [hs, Matrix.mulVec_mulVec] using this

end GlobalTheory.FinPl.SrcGl

namespace GlobalTheory.FinPl.SrcGl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {n' : Type} [Fintype n'] [DecidableEq n']

theorem coe_FFStar {A : HSp D} (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n' (CA A)) (P : Pair k n') :
    ((FFStar q χ φ P : CA A) : GA D A → ℂ) = FFStar q χ (fun P => (φ P : GA D A → ℂ)) P := by
  simp [FFStar_apply]

def toCA {A : HSp D} (φ : Form k n' (GA D A → ℂ)) (h : ∀ P, IsContAut A (φ P)) : Form k n' (CA A) :=
  fun P => ⟨φ P, h P⟩

theorem toCA_ram {A : HSp D} {α : Frame p A n'} {φ : Form k n' (GA D A → ℂ)} (hφ : IsRam α φ) :
    toCA φ hφ.2.2 ∈ Mram k n' (CA A) ∧ toCA φ hφ.2.2 ∈ EqForm (caRep α) := by
  letI := Fintype.ofFinite 𝓀[k]ˣ
  refine ⟨(mem_Mram _).2 fun P => Subtype.ext ?_, fun g P => Subtype.ext (hφ.1 g P)⟩
  simpa [toCA] using (mem_Mram φ).1 hφ.2.1 P

theorem exists_lat_eq (P : Pair k n') : ∃ P' : Pair k n', P'.lat = P.ker := by
  have h1 : Module.finrank 𝓀[k] (Red P.ker) = Module.finrank 𝓀[k] (Red P.lat) := by
    rw [Red.finrank_eq, Red.finrank_eq]
  have h2 : Nontrivial (Red P.lat) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact P.red_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
  have h3 : 0 < Module.finrank 𝓀[k] (Red P.ker) := h1 ▸ Module.finrank_pos
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 h3
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual 𝓀[k] (Red P.ker), f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff 𝓀[k] x).1 h)
  exact ⟨ofDual P.ker ⟨f, fun h0 => hf (by rw [h0]; rfl)⟩, ofDual_lat _ _⟩

variable {n : Type} [Fintype n] [DecidableEq n]

def tensL (a : (n → k) → ℂ) : (Matrix n n' k → ℂ) →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) where
  toFun Ψ := tensCol Ψ a
  map_add' Ψ Ψ' := by ext x; simp [tensCol, add_mul]
  map_smul' c Ψ := by ext x; simp [tensCol, mul_assoc]

@[simp] theorem tensL_apply (a : (n → k) → ℂ) (Ψ : Matrix n n' k → ℂ) : tensL a Ψ = tensCol Ψ a := rfl

theorem tensCol_add (Ψ Ψ' : Matrix n n' k → ℂ) (a : (n → k) → ℂ) : tensCol (Ψ + Ψ') a = tensCol Ψ a + tensCol Ψ' a :=
  (tensL a).map_add Ψ Ψ'

end GlobalTheory.FinPl.SrcGl

open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl in
theorem GlobalTheory.FinPl.sourceGlued : ∀ D : D7, GlobalTheory.FinPl.SourceGlued D := by
  intro D k _ _ _ _ p n n' _ _ _ _ q χ₀ hχ χ hχχ ψ S A L T o ζ hL hA vA χS χT om hW _ hT α α₀ β hsum P P₁ Λ _
  obtain ⟨lS, hlS, hθ⟩ := GlobalTheory.T.exists_bilinear_equivariant_orthogonalSummandLift D k p n n' ψ S A L T o ζ hL hA vA χS χT om hW α α₀ β hsum
  have hdet : ∀ L' : Submodule 𝒪[k] (n' → k), L'.IsFullLattice k → ∀ g ∈ latStab L',
      ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 1 := fun L' hL' g hg => by
    rw [GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one k n' L' hL' g hg lS (hlS hT), Units.val_one]
  have hsb := GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts k n n'

  have hinv : ∀ (θ : CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ)),
      (∀ (g : GL n' k) (v : CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) →
        θ (caRep α g v) (fun x => Φ (x * (blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ) →
      ∀ a ∈ SB (n → k), ∀ L' : Submodule 𝒪[k] (n' → k), L'.IsFullLattice k →
        GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.IsLiftInv (caRep α) (θ.compl₂ (tensL a)) L' := by
    intro θ hθe a ha L' hL' g hg v Ψ hΨ
    simp only [LinearMap.compl₂_apply, tensL_apply]
    have := hθe g v _ (hsb.1 Ψ a hΨ ha)
    rw [hdet L' hL' g hg, inv_one, one_smul] at this
    refine Eq.trans (congrArg _ ?_) this
    funext x
    exact (tensCol_mul_blk Ψ a g x).symm
  obtain ⟨P', hP'⟩ := exists_lat_eq P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n' k) P' P₁
  refine ⟨⟨((resCard k : ℂ) ^ Fintype.card n)⁻¹ * ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ), ?_⟩, ?_⟩
  · intro LS LT f₀ Ξ Ξ' hΞ hΞ' φ hφ
    obtain ⟨θ, hθv, hθe⟩ := hθ LS LT f₀ hΞ.1 hΞ.2.1 hΞ.2.2.1
    obtain ⟨hram, heq⟩ := toCA_ram hφ
    set φc := toCA φ hφ.2.2 with hφc
    have hχ1 : χ ≠ 1 := hχχ ▸ resChar_ne_one hχ q
    rw [show liftA o om vA (φ P) Ξ = θ (φc P) _ from (hθv (φc P) _ _ hΞ).symm,
      ((GlobalTheory.T.gluedLattice_finite_expansions_localField k n n' q χ hχ1 Λ).1 P).1]
    have e0 : θ (φc P) (tensCol (latInd P.ker Λ) (vecInd Λ)) = 0 :=
      GlobalTheory.LastSteps.lift_latInd P hram heq (hinv θ hθe _ (hsb.2.1 Λ inferInstance) P.ker inferInstance) Λ
    have e1 : ∀ Q ∈ withLat Λ, θ (φc P) (tensCol (latInd P.ker Q.ker + GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mainDatum q χ 1 P Q)
        (charInd χ Q)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • liftA o om vA (FFStar q χ φ P₁) (Ξ' Q) := by
      intro Q hQ
      have hI := hinv θ hθe _ (hsb.2.2 χ Q) P.ker inferInstance
      have a0 : θ (φc P) (tensCol (latInd P.ker Q.ker) (charInd χ Q)) = 0 :=
        GlobalTheory.LastSteps.lift_latInd P hram heq hI Q.ker
      have a1 := GlobalTheory.LastSteps.lift_mainDatum q χ 1 heq hI Q rfl hP'
      simp only [LinearMap.compl₂_apply, tensL_apply, map_one, Module.End.one_apply] at a1
      have a2 := hθe g⁻¹ (FFStar q χ φc P₁) _ (hΞ' Q hQ).2.2.2.1
      have b1 : caRep α g⁻¹ (FFStar q χ φc P₁) = FFStar q χ φc P' := by
        rw [← hg, FFStar_mem_EqForm q χ heq g P', ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]
      have b2 : (fun x => tensCol (phiOne P₁ Q) (charInd χ Q) (x * (blk g⁻¹).val)) = tensCol (phiOne P' Q) (charInd χ Q) := by
        funext x
        rw [tensCol_mul_blk]
        congr 1
        funext x₀
        rw [← hg, phiOne_smul_left, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      rw [b1, b2, hθv _ _ _ (hΞ' Q hQ), coe_FFStar] at a2
      rw [tensCol_add, map_add (f := _), a0, zero_add, a1, a2, map_inv, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_add (f := _), map_sum, e0, zero_add, Finset.sum_congr rfl e1, ← Finset.smul_sum, smul_smul]
  · intro LS LT f₀ Ξ a hor φ hφ
    obtain ⟨L₁, hL₁, hO⟩ : ∃ L₁ : Submodule 𝒪[k] (n' → k), (L₁ = P.lat ∨ L₁ = P.ker) ∧
        Over ψ α₀ β LS LT f₀ (tensCol (latInd L₁ Λ) a) Ξ := by
      rcases hor with h | h
      exacts [⟨_, Or.inl rfl, h⟩, ⟨_, Or.inr rfl, h⟩]
    haveI : L₁.IsFullLattice k := by rcases hL₁ with rfl | rfl <;> infer_instance
    obtain ⟨θ, hθv, hθe⟩ := hθ LS LT f₀ hO.1 hO.2.1 hO.2.2.1
    obtain ⟨hram, heq⟩ := toCA_ram hφ
    set φc := toCA φ hφ.2.2 with hφc
    rw [show liftA o om vA (φ P) Ξ = θ (φc P) _ from (hθv (φc P) _ _ hO).symm]
    have hinvL : ∀ g ∈ latStab L₁, ∀ w, θ (caRep α g w) (tensCol (latInd L₁ Λ) a) = θ w (tensCol (latInd L₁ Λ) a) := by
      intro g hg w
      have := hθe g w _ hO.2.2.2.1
      rw [hdet L₁ inferInstance g hg, inv_one, one_smul] at this
      refine Eq.trans (congrArg _ ?_) this
      funext x
      rw [tensCol_mul_blk]
      congr 1
      funext x₀
      exact (GlobalTheory.LastSteps.latInd_mul hg Λ x₀).symm
    have hv : formOf (caRep α) P (evalEquiv (caRep α) P ⟨φc, heq⟩) = φc :=
      congrArg Subtype.val ((evalEquiv (caRep α) P).left_inv ⟨φc, heq⟩)
    exact (GlobalTheory.PairOp.vanishing q).invariant_eq_zero (caRep α) P (evalEquiv (caRep α) P ⟨φc, heq⟩) (hv.symm ▸ hram) _
      (θ.flip (tensCol (latInd L₁ Λ) a)) (by
        rcases hL₁ with rfl | rfl
        exacts [Or.inl fun g hg w => hinvL g hg w, Or.inr fun g hg w => hinvL g hg w])
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SourceLiftAtGluedPlaceProofStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sourceLiftAtGluedPlace_proof : ∀ D : D7, GlobalTheory.FinPl.SourceGlued D := by
  first | exact @GlobalTheory.FinPl.sourceGlued | exact GlobalTheory.FinPl.sourceGlued | (intros; apply GlobalTheory.FinPl.sourceGlued <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommon
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BrEquivAll
open MvPolynomial Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.BranchFormula

open Formalism.L2.Col.Br

theorem brEquiv_all : ∀ (K : Type) [Field K] [CharZero K] {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n), Br.BrEquiv K hN lam sg := by
  intro K _ _ ι _ N n hN lam sg hS g g' h G
  have hB : ∀ τ, IsBlock hN (g' τ : Matrix (Fin N) (Fin N) K) (g τ : Matrix (Fin n) (Fin n) K) 1 := h
  apply Subtype.ext
  have hd : detTwK lam g' = detTwK sg g := by
    rw [detTwK, detTwK]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [detPow, detPow, hS τ, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, (hB τ).det, mul_one]
  simp only [brStd, brStdP, LinearMap.comp_apply, Submodule.subtype_apply, rhoK_coe, LinearMap.smul_apply, actP, trAct,
    AlgHom.toLinearMap_apply, map_smul, Submodule.coe_smul]
  rw [coefLast_blockAct K ι hN _ _ _ (fun _ => 1) fun τ => (hB τ).transpose, map_smul, Submodule.coe_smul, projVV_blockAct]
  simp only [smul_smul, one_pow, Finset.prod_const_one, mul_one]
  rw [hd]
  congr 1
  ring

end GlobalTheory.BranchFormula
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommon
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrueBranch

section Gen

open _root_.Formalism.L2.DIV _root_.Formalism.L2.Col

variable {ι : Type} [Fintype ι] {N n : ℕ}

theorem cSpan_eq_VV {m : ℕ} (lam : ι → DomWeight m) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  unfold CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Formalism.L2.Col.nablaSq_eq_delSq]
  rfl

theorem det_ne_zero_of_mem_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : k.det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hk)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem polOf_fnOf_frOne (G : ι → Matrix (Fin N) (Fin N) ℂ) (sh : ι → ℤ) (o : Frames G) (ho : ∀ τ, o.1 τ = 1)
    (P : MvPolynomial (ι × Fin N × Fin N) ℂ) : Formalism.L2.Col.polOf G sh o (fnOf G sh 1 P) = P := by
  have e : (fun τ => (o.1 τ)⁻¹) = (1 : ι → Matrix (Fin N) (Fin N) ℂ) := funext fun τ => by rw [ho τ, inv_one]; rfl
  have h := Formalism.L2.Col.polOf_fnOf G sh o P
  rwa [e] at h

theorem fnOf_actP_tr (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (P : Pol ℂ ι n) (y y' : Frames G) (h : IsTr (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) y y') :
    fnOf G (shiftOf lam) 1 (actP lam g P) y = fnOf G (shiftOf lam) 1 P y' := by
  have e1 := congrFun (Formalism.L2.Col.fnOf_mul G (shiftOf lam) (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) 1 P) y
  have e2 := Formalism.L2.Col.fnOf_tr (G := G) (G' := G) (shiftOf lam) 1 (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) P y' y h
  have e3 : (fun τ => (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ * ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) =
      fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ * (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ := by
    funext τ; simp
  rw [e2, e3, e1]
  have e4 : actP lam g P = (∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ.det ^ shiftOf lam τ) •
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) P := by
    simp only [actP, detTwK, trAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_transpose]
    simp [detPow, shiftOf, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [e4]

theorem brEqv_formula (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (c : ℂ) (o : Frames G)
    (ho : ∀ τ, o.1 τ = 1) :
    BrEqv hN G G' lam sg (fnOf G' (shiftOf sg) 1 ∘ₗ (c • ((Formalism.L2.DIV.VV ℂ sg).subtype ∘ₗ Br.brStdP hN lam sg)) ∘ₗ
      Formalism.L2.Col.polOf G (shiftOf lam) o) := by
  have hp := polOf_fnOf_frOne G (shiftOf lam) o ho
  refine ⟨?_, ?_⟩
  · rintro _ ⟨P, -, rfl⟩
    refine ⟨c • (Br.brStdP hN lam sg P : Pol ℂ ι n), ?_, ?_⟩
    · rw [cSpan_eq_VV]; exact (Formalism.L2.DIV.VV ℂ sg).smul_mem c (Br.brStdP hN lam sg P).2
    · simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply]
  · rintro k kt hk hb _ ⟨P, hP, rfl⟩ Φ' hΦ' z z' hz
    have hk0 : ∀ τ, (k τ)ᵀ.det ≠ 0 := fun τ => by
      rw [Matrix.det_transpose]; exact det_ne_zero_of_mem_unitary (hk τ)
    have hkt0 : ∀ τ, (kt τ)ᵀ.det ≠ 0 := fun τ => by
      rw [Matrix.det_transpose, (hb τ).det, mul_one, ← Matrix.det_transpose]; exact hk0 τ
    let g : ι → GL (Fin n) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hk0 τ)
    let g' : ι → GL (Fin N) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hkt0 τ)
    have hblk : ∀ τ, GlobalTheory.BranchFormula.IsBlock hN ((g' τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
        ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) 1 := fun τ => (hb τ).transpose
    have hPV : P ∈ Formalism.L2.DIV.VV ℂ lam := cSpan_eq_VV lam ▸ hP
    have hE := GlobalTheory.BranchFormula.brEquiv_all ℂ hN lam sg hS g g' (fun τ => hblk τ) ⟨P, hPV⟩
    have h2 : (Br.brStdP hN lam sg (actP lam g' P) : Pol ℂ ι n) = actP sg g (Br.brStdP hN lam sg P : Pol ℂ ι n) :=
      congrArg Subtype.val hE
    have hΦe : Φ' = fnOf G (shiftOf lam) 1 (actP lam g' P) := by
      funext y
      have hd : ∀ τ, IsUnit (kt τ * y.1 τ).det := fun τ => by
        rw [Matrix.det_mul]
        refine IsUnit.mul (Ne.isUnit ?_) (y.2 τ)
        rw [← Matrix.det_transpose]; exact hkt0 τ
      let y' : Frames G := ⟨fun τ => kt τ * y.1 τ, hd⟩
      rw [hΦ' y y' (fun τ => rfl), fnOf_actP_tr G lam g' P y y' (fun τ => by
        show kt τ * y.1 τ = ((kt τ)ᵀ)ᵀ * y.1 τ
        rw [Matrix.transpose_transpose])]
    rw [hΦe]
    simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply]
    rw [h2, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, fnOf_actP_tr G' sg g _ z z' (fun τ => by
      rw [hz τ]
      show k τ * z.1 τ = ((k τ)ᵀ)ᵀ * z.1 τ
      rw [Matrix.transpose_transpose])]

theorem ne_formula (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ))
    (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (c : ℂ) (hc : c ≠ 0) (o : Frames G) (ho : ∀ τ, o.1 τ = 1) :
    ∃ Φ ∈ ValC G lam, (fnOf G' (shiftOf sg) 1 ∘ₗ (c • ((Formalism.L2.DIV.VV ℂ sg).subtype ∘ₗ Br.brStdP hN lam sg)) ∘ₗ
      Formalism.L2.Col.polOf G (shiftOf lam) o) Φ ≠ 0 := by
  have hp := polOf_fnOf_frOne G (shiftOf lam) o ho
  have h1 := GlobalTheory.BranchFormula.onePlace Formalism.L2.DIV.BrJ.branching_interlacing_pairs
  choose f hf hf0 using fun τ => (h1 N n hN (lam τ) (sg τ) (hI τ) (hS τ)).2.2.1
  have hn : ∀ τ, f τ ∈ nablaSq ℂ N (lam τ) := fun τ => by rw [Formalism.L2.Col.nablaSq_eq_delSq]; exact hf τ
  have hmem : Formalism.L2.DIV.ten f ∈ Formalism.L2.DIV.VV ℂ lam := GlobalTheory.Proof.TensorMapDescent.ten_mem lam f hn
  have ht := GlobalTheory.BranchFormula.tensor ℂ ι N n hN lam sg hI hS f ⟨_, hmem⟩ hn rfl
  refine ⟨fnOf G (shiftOf lam) 1 (Formalism.L2.DIV.ten f), ⟨_, (cSpan_eq_VV lam).symm ▸ hmem, rfl⟩, fun h => ?_⟩
  simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply] at h
  have h' : (Br.brStdP hN lam sg (Formalism.L2.DIV.ten f) : Pol ℂ ι n) =
      Formalism.L2.DIV.ten fun τ => GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ hN (lam τ) (sg τ) (f τ) := ht
  rw [h', map_smul] at h
  have h0 := Formalism.L2.Col.fnOf_injective G' (shiftOf sg) 1 (fun _ => by simp) ⟨fun _ => 1, fun _ => by simp⟩
    (((smul_eq_zero.1 h).resolve_left hc).trans (map_zero _).symm)
  exact GlobalTheory.Proof.TensorMapDescent.ten_ne_zero _ hf0 h0

end Gen

section True

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

theorem half_mul (R : Ranks) (j : ℕ) : ((j * (R.t + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨a, ha⟩ := R.t_odd
  have h1 : (R.t + 1) / 2 = a + 1 := by omega
  have h2 : j * (R.t + 1) / 2 = j * (a + 1) := by
    rw [ha, show j * (2 * a + 1 + 1) = 2 * (j * (a + 1)) by ring]; omega
  rw [h1, h2]; push_cast; ring

theorem domWeight_ext {M : ℕ} {a b : DomWeight M} (h : a.w = b.w) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

theorem lamT_record (j : ℕ) : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j = GlobalTheory.Mem.Col2.lamT (B.hcW u) j := by
  funext τ
  apply domWeight_ext
  funext i
  show (Examples₂.lamOf (B.hcW u τ) j).w i - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (Examples₂.lamOf (B.hcW u τ) j).w i + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

theorem sgT_record (a : I.ι) : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = (I.perIn u a).sgT := by
  funext τ
  apply domWeight_ext
  funext i
  show (B.wts.sgW τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (B.wts.sgW τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

end True

section Main

theorem branching_true_columns : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m τ) (sgT (D := (I.rec7 l Z)) u τ)) ∧ BrEqv hN _ _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m) (sgT (D := (I.rec7 l Z)) u) (lowOf I l Z u) ∧ (∃ Φ ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m), lowOf I l Z u Φ ≠ 0) ∧ ∀ (a : I.ι) z c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)), (I.per l u a).lowerMap z c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => z c ⟨y'.1, y'.2⟩) y := by
  intro B X I _ _ l Z u hN
  have hM := fun τ => GlobalTheory.BranchMembers.members B.fields B.Word B.R B.wts B.wts_isOk u τ
  have hI' : ∀ τ, Formalism.L2.Col.Br.Interlace hN (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ) :=
    fun τ => (hM τ).1
  have hS' : ∀ τ, Formalism.L2.Col.Br.SameShift (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ) :=
    fun τ => (hM τ).2
  have hc : (∏ τ, Formalism.L2.Col.embAt B.embLL B.fields.emb τ (I.perIn u I.mu0).tz ^
      (-Formalism.L2.Col.Br.nBr (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((map_ne_zero _).2 (l.per u I.mu0).tz_ne)
  have hlow : lowOf I l Z u = fnOf _ (shiftOf (I.perIn u I.mu0).sgT) 1 ∘ₗ
      ((∏ τ, Formalism.L2.Col.embAt B.embLL B.fields.emb τ (I.perIn u I.mu0).tz ^
        (-Formalism.L2.Col.Br.nBr (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ))) •
        ((Formalism.L2.DIV.VV ℂ (I.perIn u I.mu0).sgT).subtype ∘ₗ
          Formalism.L2.Col.Br.brStdP hN (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (I.perIn u I.mu0).sgT)) ∘ₗ
      Formalism.L2.Col.polOf _ (shiftOf (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m)) ⟨fun _ => 1, fun _ => by simp⟩ := by
    unfold lowOf
    rw [lamT_record I l Z u, sgT_record I l Z u I.mu0]
    rfl
  refine ⟨?_, ?_, ?_, fun a z c y => ?_⟩
  · rw [lamT_record I l Z u, sgT_record I l Z u I.mu0]; exact hI'
  · rw [lamT_record I l Z u, sgT_record I l Z u I.mu0, hlow]
    exact brEqv_formula hN _ _ _ _ hS' _ _ (fun _ => rfl)
  · rw [lamT_record I l Z u, hlow]
    exact ne_formula hN _ _ _ _ hI' hS' _ hc _ (fun _ => rfl)
  · unfold lowOf
    rw [lamT_record I l Z u, sgT_record I l Z u a]
    rfl

end Main

end GlobalTheory.TrueBranch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommonStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_branchingMap_equivariant_nonzero_common : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m τ) (sgT (D := (I.rec7 l Z)) u τ)) ∧ BrEqv hN _ _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m) (sgT (D := (I.rec7 l Z)) u) (lowOf I l Z u) ∧ (∃ Φ ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m), lowOf I l Z u Φ ≠ 0) ∧ ∀ (a : I.ι) z c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)), (I.per l u a).lowerMap z c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => z c ⟨y'.1, y'.2⟩) y := by
  first | exact @GlobalTheory.TrueBranch.branching_true_columns | exact GlobalTheory.TrueBranch.branching_true_columns | (intros; apply GlobalTheory.TrueBranch.branching_true_columns <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConjugateAtFinitePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConjugateAtFinitePlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.FinPl.SelfDualConj

theorem conj_at_place : ∀ (D : D7) (V : HSp D) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M →
    ∀ x : Pl D, ∃ g ∈ grpAt V (· = x), Moves V g L M (· = x) := by
  intro D V L M hL hM x
  obtain ⟨γ, hγ, h⟩ := GlobalTheory.T.selfDualLattices_single_orbit_tamePlace D V x (latV V L (· = x)) (latV V M (· = x)) (GlobalTheory.FinPl.TamePlaces.tame D x)
    (GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V L x hL) (GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V M x hM)
  exact ⟨γ, hγ, fun y hy => h y hy⟩

end GlobalTheory.FinPl.SelfDualConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConjugateAtFinitePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattices_conjugate_at_finitePlace : ∀ (D : D7) (V : HSp D) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M → ∀ x : Pl D, ∃ g ∈ grpAt V (· = x), Moves V g L M (· = x) := by
  first | exact @GlobalTheory.FinPl.SelfDualConj.conj_at_place | exact GlobalTheory.FinPl.SelfDualConj.conj_at_place | (intros; apply GlobalTheory.FinPl.SelfDualConj.conj_at_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StpTopIdxEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.TwDat.Is

theorem stp_top_idx_eq {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι)
    (b b' : (I.stp u a B.R.m).β) : b = b' := by
  show (b : Idx I.sel (I.tup a) (I.idx a) B.R.m) = b'
  obtain ⟨x, hx⟩ := b
  obtain ⟨y, hy⟩ := b'
  have h1 : x = none := by simpa using hx
  have h2 : y = none := by simpa using hy
  subst h1; subst h2; rfl

theorem chOf_top_eq : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ (c₀ : (I.stp u a B.R.m).Cl) (β : Ch₀ B.R.m), A.chOf B.R.m c₀ = β := by
  intro B X I _ _ l Z u a Ch₀ A hA c₀ β
  obtain ⟨c, rfl⟩ := hA.chOf_onto B.R.m le_rfl β
  exact ((hA.reads B.R.m le_rfl).key c₀ c).2
    ⟨stp_top_idx_eq I u a _ _, GlobalTheory.Mem.Col2.ChEx.cos_of_neT I (by omega) _ _⟩

end GlobalTheory.AdForm.TwDat.Is
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOConstMul
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.FlatUnitPf

theorem idAt_mul_idOff {D : D7} (P : Pl D → Prop) (a b : AE D) (ha : a ∈ idAt D P) (hb : b ∈ idOff D P) : a * b = 0 := by
  have h1 : a * b ∈ idAt D P := Ideal.mul_mem_right _ _ ha
  have h2 : a * b ∈ idOff D P := Ideal.mul_mem_left _ _ hb
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at h1
  rw [idOff, Ideal.mem_iInf] at h2
  obtain ⟨hinf, hfin⟩ := h1
  rw [RingHom.mem_ker] at hinf
  apply GlobalTheory.LatVac.eq_zero_of_parts
  · exact hinf
  · apply GlobalTheory.SelfDualAt.eq_zero_of_compFin
    intro w
    by_cases hw : P w
    · have := h2 ⟨w, hw⟩
      rw [RingHom.mem_ker] at this
      exact this
    · have := hfin ⟨w, hw⟩
      rw [RingHom.mem_ker] at this
      exact this

end GlobalTheory.FinPl.FlatUnitPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameVectorLatticeCriterion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

theorem mulVec_sec_split {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {n : ℕ} (g : Matrix (Fin n) (Fin n) (AE D)) (w : Fin n → k) :
    g *ᵥ (fun i => q.sec (w i)) = fun i => q.sec ((g.map q.pr *ᵥ w) i) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := GlobalTheory.LocMod.PinEx.sec_mul q (q.pr (g i j)) (w j)
  have h2 := q.sec_pr (g i j)
  have h3 : q.e * q.sec (w j) = q.sec (w j) := by
    have := q.sec_pr (q.sec (w j))
    rw [q.pr_sec] at this
    exact this.symm
  rw [← h1, h2, mul_assoc, mul_left_comm, h3]

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch


end GlobalTheory.Core.Mi.LatMatch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineOfGlued
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MiTop.GluedLine

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.LiftModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_mem_of_intAt (p : SplitPt D k) {a : AE D} (ha : finPart D a ∈ intAE D) : p.pr a ∈ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr, RingHom.map_mul]
  exact mul_mem_intAE (e_mem_intAt p).2 ha

theorem eq_sec_add (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a = p.sec (p.pr a) + cA D (p.sec (p.pr (cA D a))) := by
  rw [p.sec_pr, p.sec_pr, RingHom.map_mul, Formalism.L2.Theta.cA_cA, ← add_mul, (idem_iff p a).1 ha]

theorem mem_intAt_iff (p : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = p.v)) :
    a ∈ intAt D (· = p.v) ↔ p.pr a ∈ 𝒪[k] ∧ p.pr (cA D a) ∈ 𝒪[k] := by
  refine ⟨fun h => ⟨pr_mem_of_intAt p h.2, pr_mem_of_intAt p ((cA_int_iff a).2 h.2)⟩, fun h => ⟨ha, ?_⟩⟩
  rw [eq_sec_add p ha, RingHom.map_add (f := _)]
  exact add_mem ((p.int_iff _).1 h.1) ((cA_int_iff _).2 ((p.int_iff _).1 h.2))

theorem valuation_xi_zero_eq_one (p : SplitPt D k) (hp : p.UnitAA) : valuation k (p.pr (incA D D.host.xi0)) = 1 := by
  obtain ⟨h1, h2⟩ := hp.1 _ (e_mem_intAt p)
  have he : p.pr p.e = 1 := by rw [← sec_one, p.pr_sec]
  have h3 := pr_mem_of_intAt p h1.2
  have h4 := pr_mem_of_intAt p h2.2
  rw [RingHom.map_mul, he, mul_one, Valuation.mem_integer_iff] at h3 h4
  have h5 : valuation k (p.pr (incA D D.host.xi0)) * valuation k (p.pr (incA D D.host.xi0⁻¹)) = 1 := by
    rw [← map_mul, ← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one,
      RingHom.map_one, map_one]
  refine le_antisymm h3 ?_
  rw [← h5]
  exact mul_le_of_le_one_right' h4

end GlobalTheory.MiTop.GluedLine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateCompactMemLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevConj

variable {D : D7}

theorem mem_idAt_of_eq {P : Pl D → Prop} {v : Pl D} (hv : P v) {a : AE D} (ha : a ∈ idAt D (· = v)) : a ∈ idAt D P := by
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hw => w.2 (by rw [hw]; exact hv)⟩⟩

theorem latV_supp_iff (S : HSp D) (L : Lat S) (hL : Submodule.IsLattice D.host.E L) {P : Pl D → Prop} {v : Pl D}
    (hv : P v) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ latV S L P ↔ y ∈ latV S L (· = v) := by
  have hT := ((GlobalTheory.FinPl.localComponents D P).2 S).2.2.2 L y hL
  have hV := ((GlobalTheory.FinPl.localComponents D (· = v)).2 S).2.2.2 L y hL
  rw [hT, hV]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨hy, fun w hw e he => h w (by rw [hw]; exact hv) e he⟩
  · rintro ⟨_, h⟩
    refine ⟨fun i => mem_idAt_of_eq hv (hy i), fun w _ e he => ?_⟩
    by_cases hwv : w = v
    · exact h w hwv e he
    · obtain ⟨ε, -, -, -, hAt, hOff⟩ := (GlobalTheory.FinPl.localComponents D (· = w)).1
      have hzero : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = w) := by
          have h' := hy i
          simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf] at h'
          simp only [idOff, Submodule.mem_iInf]
          intro u
          exact h'.2 ⟨u.1, by rw [u.2]; exact hwv⟩
        have h1 : ε * e = e := (hAt e).1 he.1
        have h2 : ε * y i = 0 := (hOff (y i)).1 hyi
        show e * y i = 0
        rw [← h1, mul_comm ε e, mul_assoc, h2, mul_zero]
      rw [hzero]
      exact (latV S L (· = w)).zero_mem

theorem moves_at_of_moves {S : HSp D} {L : Lat S} (hL : Submodule.IsLattice D.host.E L) {P : Pl D → Prop} {v : Pl D}
    (hv : P v) {g : GA D S} (h : Moves S g L L P) : Moves S g L L (· = v) := by
  intro y hy
  rw [← latV_supp_iff S L hL hv y hy, ← latV_supp_iff S L hL hv _ (GlobalTheory.FinPl.KOpen.supp_mulVec S _ g hy)]
  exact h y fun i => mem_idAt_of_eq hv (hy i)

end GlobalTheory.LevConj
end
end
