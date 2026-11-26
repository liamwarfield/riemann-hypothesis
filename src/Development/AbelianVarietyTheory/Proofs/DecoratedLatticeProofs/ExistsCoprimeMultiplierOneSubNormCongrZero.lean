module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CapelliLowestGelfandConj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateTsumLeOfThetaLevelMultiple
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowSizesNR
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorGiven
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierOneSubNormCongrZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierOneSubNormCongrZero
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TorusCong

open Formalism.L2.SG.Pf.unitaryCongruence GlobalTheory.St.G.FrameClose

theorem one_sub_T_zmod : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ZMod' X.B.I X.B.g ((M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := by
  intro D X u
  obtain ⟨c', hc', hm⟩ := X.xu_z u
  obtain ⟨-, hz0, -⟩ := X.vectorsInLattice
  set z' : VA X.B.I := X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) with hz'
  have hm' : (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) ∈ mL X.B.I X.B.g := hm
  have hzz : hA X.B.I z' z' = -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    rw [hz', Formalism.L2.SG.PoincareInHH.Cut.hA_fmat, HidaSetting.zR, Formalism.L2.SG.PoincareInHH.Cut.hA_crd, X.zu_norm,
      map_neg, map_natCast, map_neg, map_natCast]
  set m : VA X.B.I := (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) with hmdef
  set w0 : VA X.B.I := (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.z0 with hw0def
  have hw0 : w0 ∈ X.B.I.Lf := nat_smul_mem c' hz0
  have hw : m + w0 ∈ X.B.I.Lf := add_mem (mL_le X.B.g hm') hw0
  have h1 : ZMod' X.B.I X.B.g (hA X.B.I m (m + w0)) := zmod_of_mL hm' hw
  have h2 : ZMod' X.B.I X.B.g (hA X.B.I w0 m) := by
    rw [hA_symm]; exact Z_sig _ _ (zmod_of_mL hm' hw0)
  have hsplit : hA X.B.I (m + w0) (m + w0) - hA X.B.I w0 w0 = hA X.B.I m (m + w0) + hA X.B.I w0 m := by
    rw [hA_add_left, hA_add_right, hA_add_right]; ring
  have hmw : m + w0 = (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' := by
    rw [hmdef, hw0def, ← smul_add, sub_add_cancel]
  have hsq : ∀ x : VA X.B.I, hA X.B.I ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x) ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x)
      = (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * hA X.B.I x x := by
    intro x; rw [hA_nat_left, hA_smul_right]; ring
  have hA1 : ZMod' X.B.I X.B.g ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0)) := by
    have e : (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0) =
        hA X.B.I m (m + w0) + hA X.B.I w0 m := by
      rw [← hsplit, hmw, hw0def, hsq, hsq]; ring
    rw [e]; exact Z_add _ _ h1 h2
  have hA2 : ZMod' X.B.I X.B.g ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I X.z0 X.z0 + 1)) := by
    have := Z_smul X.B.I X.B.g (natCast_mem (IntAf X.B.I.F X.B.I.E) (c' ^ 2)) X.formsAtZero.1
    simpa [Nat.cast_pow] using this
  refine ⟨c' ^ 2, Nat.Coprime.pow_left 2 hc', ?_⟩
  have e : ((c' ^ 2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) =
      (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0) +
      (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I X.z0 X.z0 + 1) := by
    rw [hzz, Nat.cast_pow]; ring
  rw [e]; exact Z_add _ _ hA1 hA2

end GlobalTheory.TorusCong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierOneSubNormCongrZeroStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_multiplier_one_sub_norm_congr_zero : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ZMod' X.B.I X.B.g ((M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := by
  first | exact @GlobalTheory.TorusCong.one_sub_T_zmod | exact GlobalTheory.TorusCong.one_sub_T_zmod | (intros; apply GlobalTheory.TorusCong.one_sub_T_zmod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCoprimeOfCongrMulOneSubModLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCoprimeOfCongrMulOneSubModLevel
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TorusCop

theorem natCoprime_of_zmod_mul_one_sub : ∀ (I : AutInst) (g T M : ℕ), 1 ≤ g → Nat.Coprime M g →
    ZMod' I g ((M : I.E ⊗[I.F] Af I.F) * (1 - (T : I.E ⊗[I.F] Af I.F))) → Nat.Coprime T g := by
  intro I g T M hg hMg hz
  obtain ⟨t, ht, hc⟩ := hz
  obtain ⟨-, hint, hu, -⟩ := GlobalTheory.RowLev.intAf_approx_inter_unit_conj I g hg
  have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast (show g ≠ 0 by omega)
  set q : ℚ := (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) / (g : ℚ) with hqdef
  have hgq : (g : I.E) * (q : I.E) = (M : I.E) * (1 - (T : I.E)) := by
    have : (g : ℚ) * q = (M : ℚ) * (1 - (T : ℚ)) := by
      rw [hqdef]; field_simp; push_cast; ring
    have := congrArg (fun x : ℚ => (x : I.E)) this
    simpa using this
  have key : Formalism.UG.inclE (F := I.F) (Af I.F) (q : I.E) = t := by
    apply hu.mul_left_cancel
    rw [← hc]
    calc (g : I.E ⊗[I.F] Af I.F) * Formalism.UG.inclE (F := I.F) (Af I.F) (q : I.E)
        = Formalism.UG.inclE (F := I.F) (Af I.F) ((g : I.E) * (q : I.E)) := by rw [map_mul, map_natCast]
      _ = Formalism.UG.inclE (F := I.F) (Af I.F) ((M : I.E) * (1 - (T : I.E))) := by rw [hgq]
      _ = _ := by rw [map_mul, map_sub, map_one, map_natCast, map_natCast]
  have hq : (q : I.E) ∈ (algebraMap (𝓞 I.E) I.E).range := (hint _).1 (key ▸ ht)
  obtain ⟨b, hb⟩ := hq
  have h1 : IsIntegral ℤ (algebraMap ℚ I.E q) := by
    rw [eq_ratCast, ← hb]; exact RingOfIntegers.isIntegral_coe b
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff ).1 h1
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have h3 : (M : ℤ) * (1 - (T : ℤ)) = (g : ℤ) * n := by
    have hn' : (n : ℚ) = q := by simpa using hn
    have : (((M : ℤ) * (1 - (T : ℤ)) : ℤ) : ℚ) = (((g : ℤ) * n : ℤ) : ℚ) := by
      rw [hqdef] at hn'
      push_cast
      rw [hn']
      field_simp
      push_cast; ring
    exact_mod_cast this
  have h5 : (g : ℤ) ∣ 1 - (T : ℤ) := by
    refine Int.dvd_of_dvd_mul_right_of_gcd_one ⟨n, h3⟩ ?_
    rw [Int.gcd_natCast_natCast]; exact hMg.symm
  have hd1 : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1 := by
    have a : ((Nat.gcd T g : ℕ) : ℤ) ∣ (T : ℤ) := Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)
    have b : ((Nat.gcd T g : ℕ) : ℤ) ∣ 1 - (T : ℤ) :=
      (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_right _ _)).trans h5
    have := dvd_add b a
    simpa using this
  exact Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 (by simpa using hd1))

end GlobalTheory.TorusCop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCoprimeOfCongrMulOneSubModLevelStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nat_coprime_of_congr_mul_one_sub_mod_level : ∀ (I : AutInst) (g T M : ℕ), 1 ≤ g → Nat.Coprime M g → ZMod' I g ((M : I.E ⊗[I.F] Af I.F) * (1 - (T : I.E ⊗[I.F] Af I.F))) → Nat.Coprime T g := by
  first | exact @GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub | exact GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub | (intros; apply GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsInCuspSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsInCuspSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

variable {D : D7}

theorem multT_le_noLevel {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) : MultT θ M J χ ≤ MultT θ M ∅ 1 := by
  intro x hx
  rw [mem_multT] at hx ⊢
  refine Submodule.span_mono ?_ hx
  intro T hT
  exact ⟨hT.aut, hT.cusp, fun v k hk => absurd hk (Set.notMem_empty k), hT.equiv, hT.cont⟩

theorem conj_inv_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : conj z⁻¹ = z := by
  have h1 : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  rw [Complex.inv_def, h1, inv_one, Complex.ofReal_one, mul_one, Complex.conj_conj]

theorem upSpan_of : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
    GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.ChainOnto.LevFacts D → GlobalTheory.ChainOnto.LevelLaw D → GlobalTheory.ChainOnto.UpSpan D := by
  intro h1 h2 h3 h4 D hLF hLL hgap c hc k hk s s' hs hs' p hp u φ v _hv
  have hLF' := hLF c hc (k + 1) (Nat.succ_le_of_lt hk) s' hs'
  beta_reduce at hLF'
  obtain ⟨hwe, hvac⟩ := GlobalTheory.T.thetaChainStep_weilDatum_nonzero_fockVacuum D hgap c hc k hk s s' hs hs' p hp hk
  have hpar := GlobalTheory.T.chainPar_of_nodeGap' D hgap ⟨k, hk⟩
  obtain ⟨T, hTK, hKT, hL⟩ := GlobalTheory.T.thetaLift_upward_multiplicity_cuspidal_realType h1 h2 h3 h4 D ⟨k, hk⟩ s.V s'.V s.par s'.par s.M s'.M c.θ c.ψ p.ω p.f
    hs.par hs'.par hc.inf hpar hwe hvac s.ν s.fd hs.haar hs.fund
  obtain ⟨F', hF', hint⟩ := hL _ (multT_le_noLevel c.θ s.M _ _ u.2)

  have hlaw : ∀ P v', ∀ κ ∈ Lev.levG s'.V s'.β s'.L, ∀ g,
      F' (T P v') (g * κ) = Lev.levChi s'.V s'.β s'.L κ * F' (T P v') g := by
    intro P v' κ hκ g
    rw [← (hint P v' (g * κ)).2, ← (hint P v' g).2, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
    have hω : thetaKO p.ω g' (g * κ) (ptOf c.ψ c.θ s.M s'.M p.f P) =
        (Lev.levChi s'.V s'.β s'.L κ)⁻¹ * thetaKO p.ω g' g (ptOf c.ψ c.θ s.M s'.M p.f P) := by
      have hm : ((g', g * κ) : GA D s.V × GA D s'.V) = (g', g) * (1, κ) := by simp
      have h2 := (hLL hgap c hc k hk s s' hs hs' p hp P).2 κ hκ
      simp only [thetaKO]
      rw [hm, map_mul, Module.End.mul_apply]
      erw [h2]
      rw [map_smul]
      rfl
    simp only
    rw [hω, map_mul, conj_inv_of_norm_one (hLF'.2.2.2.2.2 κ hκ), mul_assoc]
  have hCC : F' ∈ s'.CC c := by
    refine GlobalTheory.T.mem_multiplicitySpace_level_of_KFinite_tensors D s'.V s'.par s'.M c.θ hc.inf _ _ ?_ F' hF' ?_
    · intro κ hκ
      exact (Subgroup.mem_inf.1 hκ).1
    · intro w hw κ hκ g
      have hx := hKT hw
      clear hw
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨P, v', _, rfl⟩ := hx
        exact hlaw P v' κ hκ g
      | zero => simp
      | add x y _ _ hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, mul_add]
      | smul a x _ hx => simp only [map_smul, Pi.smul_apply, smul_eq_mul, hx]; ring
  have hup : p.up φ (PiLocalization₂.val u v) = F' (T φ v) := by
    funext h
    exact (hint φ v h).2
  rw [hup]
  exact Submodule.subset_span ⟨⟨F', hCC⟩, T φ v, hTK φ v, rfl⟩

end GlobalTheory.ChainOnto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftUpwardsInCuspSpanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftUpwards_in_cuspSpan : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, GlobalTheory.ChainOnto.LevFacts D → GlobalTheory.ChainOnto.LevelLaw D → GlobalTheory.ChainOnto.UpSpan D := by
  first | exact @GlobalTheory.ChainOnto.upSpan_of | exact GlobalTheory.ChainOnto.upSpan_of | (intros; apply GlobalTheory.ChainOnto.upSpan_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateAbsSumWeilTranslateModerateGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateTsumLeOfThetaLevelMultipleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedCoordinate_tsum_le_of_theta_level_multiple : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ), ∃ k : ℕ, ∀ K₀ ∈ nhds (0 : WO S T), ∃ C : ℝ≥0, ∀ n : ℕ, 0 < n → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) f = f) → ∀ w, (∑' x : ratMx D T.rank ρ, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ) ≤ C * (n : ℝ≥0∞) ^ k * supSob ψ θ k f := by
  first | exact @GlobalTheory.MixSumBound.mixS_tsum_le | exact GlobalTheory.MixSumBound.mixS_tsum_le | (intros; apply GlobalTheory.MixSumBound.mixS_tsum_le <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateAbsSumWeilTranslateModerateGrowth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped ENNReal NNReal

namespace GlobalTheory.MixedAbsGrowth

theorem map_infPart_nsmul {D : D7} {m r : ℕ} (n : ℕ) (u : Mx D m r) (hu : u.map (infPart D) = 0) :
    (n • u).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hu i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at h ⊢
  rw [Matrix.smul_apply, nsmul_eq_mul, (infPart D).map_mul, h, mul_zero]

theorem map_infPart_actO {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (u : WO S T)
    (hu : u.map (infPart D) = 0) : (actO S T g h u).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]

theorem actO_actO_inv {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  have := GlobalTheory.WeilVacMove.actO_inv_actO g⁻¹ h⁻¹ x
  rwa [inv_inv, inv_inv] at this

theorem mixed_abs_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h (w : WO S₀ T), (∑' x : ratMx D T.rank ρ, ‖d.mixS T ψ v.μ v.𝓕 (om (g, h) f) x w‖ₑ) ≤ ENNReal.ofReal (C * (height S g * height T h) ^ A) := by
  intro D ψ S T χS χT om hW S₀ ρ d v f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨K₀, hK₀, -, m, hm⟩ := GlobalTheory.KernelSeminorm.exists_level_multiple hUo
  obtain ⟨k, hk⟩ := GlobalTheory.T.mixedCoordinate_tsum_le_of_theta_level_multiple D ψ hW.std θ hθ S S₀ T ρ d v
  obtain ⟨C, hC⟩ := hk K₀ hK₀
  obtain ⟨A, hA⟩ := GlobalTheory.WeilWordGrowth.sup_words_growth D ψ S T χS χT om hW θ hθ k
  obtain ⟨c, hc⟩ := hA f hf
  refine ⟨(C : ℝ) * (m : ℝ) ^ k * max c 0, A + k, fun g h w => ?_⟩
  obtain ⟨n, hn0, hnm, hnU⟩ := hm g h
  have hF := hW.om_pres (g, h) f hf
  have hlev : ∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) (om (g, h) f) = om (g, h) f := by
    intro u hu hinf
    have h1 := hU _ (hnU u hu hinf) (map_infPart_actO _ _ _ (map_infPart_nsmul n u hinf))
    have h2 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ (n • u)) f hf
    rw [h1, actO_actO_inv] at h2
    exact h2.symm
  have h1 := hC n hn0 (om (g, h) f) hF hlev w
  have h2 : supSob ψ θ k (om (g, h) f) ≤ ENNReal.ofReal (c * (height S g * height T h) ^ A) := hc g h
  set H : ℝ := height S g * height T h with hH
  have H0 : 0 ≤ H := mul_nonneg (height_pos S g).le (height_pos T h).le
  refine h1.trans ?_
  have e1 : ((C : ℝ≥0∞) * (n : ℝ≥0∞) ^ k) = ENNReal.ofReal ((C : ℝ) * (n : ℝ) ^ k) := by
    rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow (Nat.cast_nonneg n),
      ENNReal.ofReal_natCast]
  rw [e1]
  refine (mul_le_mul' le_rfl (h2.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left c 0) (pow_nonneg H0 A))))).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hn : (n : ℝ) ^ k ≤ ((m : ℝ) * H) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg n) hnm k
  have hc0 : 0 ≤ max c 0 := le_max_right c 0
  calc (C : ℝ) * (n : ℝ) ^ k * (max c 0 * H ^ A) ≤ (C : ℝ) * ((m : ℝ) * H) ^ k * (max c 0 * H ^ A) := by
        gcongr
    _ = (C : ℝ) * (m : ℝ) ^ k * max c 0 * H ^ (A + k) := by rw [mul_pow, pow_add]; ring

end GlobalTheory.MixedAbsGrowth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateAbsSumWeilTranslateModerateGrowthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedCoordinate_absSum_weilTranslate_moderateGrowth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h (w : WO S₀ T), (∑' x : ratMx D T.rank ρ, ‖d.mixS T ψ v.μ v.𝓕 (om (g, h) f) x w‖ₑ) ≤ ENNReal.ofReal (C * (height S g * height T h) ^ A) := by
  first | exact @GlobalTheory.MixedAbsGrowth.mixed_abs_growth | exact GlobalTheory.MixedAbsGrowth.mixed_abs_growth | (intros; apply GlobalTheory.MixedAbsGrowth.mixed_abs_growth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepFockVectorsSphericalOffS
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepFockVectorsSphericalOffS
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw

theorem fock_sph_tw : ∀ D : D7, ForStepQ D fun c _ k s s' p => (∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) ∧ ∀ v ∉ c.S, GlobalTheory.FinZeta.VacFin c.ψ s.V s'.V v (p.pt φ)) ∧ GlobalTheory.LFun.UnrOff (c.chS (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) ∧ GlobalTheory.LFun.UnrOff (c.chT (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
  classical
  intro D _ c w hw k hk s s' hs hs' p hp
  have hc : c.Is := hw.com
  obtain ⟨hr₁, hL, hfl⟩ := hs
  obtain ⟨hr₂, -, hfl'⟩ := hs'
  obtain ⟨f₀, hvec⟩ := hp.vec
  have hψ : IsStdChar D c.ψ (-1) := hc.std
  have hθ : IsInfFam c.θ := hc.inf
  have hrk : s.V.rank ≤ s'.V.rank := by
    have e1 : s.V.rank = D.R.rankY k := hfl.rank
    have e2 : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
    rw [e1, e2]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hsd' : IsSelfDualC s'.V s'.Λ := hfl'.selfDual
  obtain ⟨hfθ, -, hfv⟩ := GlobalTheory.Chain.StepVac.stepVec_vac hsd hsd' hrk hvec
  have hPS : ∀ PP ∈ s.L.Pg ∪ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ c.S := by
    intro PP hPP
    rw [hL] at hPP
    have hPP' : PP ∈ c.Pg := by rw [hw.union]; exact hPP
    exact Finset.mem_image_of_mem _ hPP'
  refine ⟨fun φ => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hfθ hfv φ
  · obtain ⟨hvac, e, he, hth⟩ := hvec
    exact GlobalTheory.FockSph.isLatVac_pureTensorO_off hθ (onb s.M) (onb s'.M) hvac he hth c.S hPS hp.theta φ
  · intro v hv
    obtain ⟨hf₀, e, he, hth⟩ := hvec
    obtain ⟨NS, hNS, hNSv⟩ := hfl.base
    obtain ⟨NT, hNT, hNTv⟩ := hfl'.base
    have hM : ((NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
      obtain ⟨P, hP⟩ := GlobalTheory.ChainOnto.VacOffS.exists_under (D := D) v
      have hPv : P.under (𝓞 D.host.F) ∉ c.S := by rw [hP]; exact hv
      have h1 := hNSv P hPv
      have h2 := hNTv P hPv
      intro h
      rw [← hP] at h
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h
      rw [map_natCast, Nat.cast_mul] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact h1 h
      · exact h2 h
    have hle := GlobalTheory.ChainOnto.VacOffS.latO_at_le hNS.2.2.2.1 hNT.2.2.2.1 hM
    have hoff : ∀ PP ∈ s.L.Pg ∪ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := by
      intro PP hPP h0
      exact hv (h0 ▸ hPS PP hPP)
    have hfix : ∀ u ∈ latO s.V s'.V (GlobalTheory.AdelicU.frameLat s.V : Set (Fin s.V.rank → D.host.E))
        (GlobalTheory.AdelicU.frameLat s'.V : Set (Fin s'.V.rank → D.host.E)) (fun u => u = v),
        heisO c.ψ s.V s'.V u f₀ = f₀ → heisO c.ψ s.V s'.V u (p.pt φ) = p.pt φ := fun u hu h0 =>
      GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite c.ψ c.θ s.V s'.V hc.inf _ _ _ _ p.f hp.theta u
        (GlobalTheory.VacGood.infPart_latO (hle hu))
        (GlobalTheory.Hk3.heisO_fix_thetaAt_off c.ψ _ _ _ _ _ _ _ _ hth u
          (fun i j => GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff hu i j) h0) φ
    refine ⟨hp.theta φ, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · exact hfix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hf₀.2.lat.1 u (hle hu))
    · exact hfix u hu (hf₀.2.lat.2 e' he' u (hle hu) hh)
  · intro v hv
    have hμ : GlobalTheory.LFun.UnrAt (c.μ (k + 1)) v := hc.unr ⟨k, hk⟩ v hv
    have hη : GlobalTheory.LFun.UnrAt c.η⁻¹ v := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 v).inv
    have hμη : GlobalTheory.LFun.UnrAt (c.μ (k + 1) * c.η⁻¹) v := hμ.mul hη
    unfold Com.chS Lift.chrStep
    split_ifs <;> assumption
  · intro v hv
    have hμ : GlobalTheory.LFun.UnrAt (c.μ (k + 1)) v := hc.unr ⟨k, hk⟩ v hv
    have hη : GlobalTheory.LFun.UnrAt c.η⁻¹ v := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 v).inv
    have hμη : GlobalTheory.LFun.UnrAt (c.μ (k + 1) * c.η⁻¹) v := hμ.mul hη
    unfold Com.chT Lift.chrStep
    split_ifs <;> assumption

end GlobalTheory.ChainTw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepFockVectorsSphericalOffSStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedChainStep_fockVectors_spherical_offS : ∀ D : D7, ForStepQ D fun c _ k s s' p => (∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) ∧ ∀ v ∉ c.S, GlobalTheory.FinZeta.VacFin c.ψ s.V s'.V v (p.pt φ)) ∧ GlobalTheory.LFun.UnrOff (c.chS (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) ∧ GlobalTheory.LFun.UnrOff (c.chT (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
  first | exact @GlobalTheory.ChainTw.fock_sph_tw | exact GlobalTheory.ChainTw.fock_sph_tw | (intros; apply GlobalTheory.ChainTw.fock_sph_tw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnits
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.LeviUnitK

variable {D : D7}

theorem mul_mem_of_sub_one {S : HSp D} {L : Lat S} {P : Pl D → Prop} {c : AE D} (hc : finPart D (c - 1) ∈ intAE D)
    {z : Fin S.rank → AE D} (hz : z ∈ latV S L P) : (fun k => c * z k) ∈ latV S L P := by
  have h := GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hc hz
  have e : (fun k => c * z k) = z + fun k => (c - 1) * z k := by
    funext k; simp only [Pi.add_apply]; ring
  rw [e]; exact add_mem hz h

theorem mem_iff_of_unit {S : HSp D} {L : Lat S} {P : Pl D → Prop} {c c' : AE D} (hc : finPart D (c - 1) ∈ intAE D)
    (hc' : finPart D (c' - 1) ∈ intAE D) (h1 : c' * c = 1) (z : Fin S.rank → AE D) :
    z ∈ latV S L P ↔ (fun k => c * z k) ∈ latV S L P := by
  refine ⟨mul_mem_of_sub_one hc, fun h => ?_⟩
  have h2 := mul_mem_of_sub_one hc' h
  have e : (fun k => c' * (c * z k)) = z := by funext k; rw [← mul_assoc, h1, one_mul]
  rwa [e] at h2

theorem colMul_mul {m n : ℕ} (x : Mx D m n) (i : Fin n) (c a : AE D) :
    colMul x i (c * a) = fun k => c * colMul x i a k := by
  funext k; simp only [colMul, mul_assoc]

theorem diag_mulVec {R : Type} [CommRing R] {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (h : ∀ i j, i ≠ j → M i j = 0) (w : Fin n → R) (i : Fin n) : (M *ᵥ w) i = M i i * w i := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_eq_single i (fun j _ hj => by rw [h i j (Ne.symm hj), zero_mul]) (by simp)

theorem inv_offdiag {R : Type} [CommRing R] {n : ℕ} (t : GL (Fin n) R) (ht : ∀ i j, i ≠ j → t.1 i j = 0) :
    ∀ i j, i ≠ j → (t⁻¹).1 i j = 0 := by
  intro i j hij
  have h1 : ((t⁻¹).1 * t.1) i j = 0 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_ne hij]
  have h2 : (t.1 * (t⁻¹).1) j j = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [ht k j hk, mul_zero]) (by simp)] at h1
  rw [Matrix.mul_apply, Finset.sum_eq_single j (fun k _ hk => by rw [ht j k (Ne.symm hk), zero_mul]) (by simp)] at h2
  calc (t⁻¹).1 i j = (t⁻¹).1 i j * (t.1 j j * (t⁻¹).1 j j) := by rw [h2, mul_one]
    _ = 0 := by rw [← mul_assoc, h1, zero_mul]

theorem inv_mul_diag {R : Type} [CommRing R] {n : ℕ} (t : GL (Fin n) R) (ht : ∀ i j, i ≠ j → t.1 i j = 0) (i : Fin n) :
    (t⁻¹).1 i i * t.1 i i = 1 := by
  have h1 : ((t⁻¹).1 * t.1) i i = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  rwa [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [ht k i hk, mul_zero]) (by simp)] at h1

theorem adj_apply' {m n : ℕ} (x : Mx D m n) (i : Fin n) (j : Fin m) : GlobalTheory.MixModel.adj x i j = cA D (x j i) := rfl

theorem cA_sub_one {a : AE D} (h : finPart D (a - 1) ∈ intAE D) : finPart D (cA D a - 1) ∈ intAE D := by
  rw [← map_one (cA D), ← map_sub]
  exact (GlobalTheory.FinPl.FrameLat.cA_int_iff _).2 h

end GlobalTheory.FinPl.LeviUnitK


open GlobalTheory.FinPl.LeviUnitK in
theorem GlobalTheory.FinPl.LeviUnitK.inK_levi : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → d.levi t ∈ grpAt S (· = v) → (∀ i, t.1 i i - 1 ∈ intAt D (· = v) ∧ (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → InK S L (· = v) (d.levi t) := by
  intro D S S₀ ρ d L L₀ v _hL hM t ht hg hu
  refine ⟨hg, fun y _ => ?_⟩
  have ht' := inv_offdiag t ht
  have hadj : ∀ i j, i ≠ j → GlobalTheory.MixModel.adj (t⁻¹).1 i j = 0 := fun i j hij => by
    rw [adj_apply', ht' j i (Ne.symm hij), map_zero]
  have eX : ∀ i, (d.pX *ᵥ (mt S (d.levi t) *ᵥ y)) i = t.1 i i * (d.pX *ᵥ y) i := by
    intro i
    rw [Matrix.mulVec_mulVec, d.pX_levi t, ← Matrix.mulVec_mulVec, diag_mulVec ht]
  have eY : ∀ i, (d.pY *ᵥ (mt S (d.levi t) *ᵥ y)) i = cA D ((t⁻¹).1 i i) * (d.pY *ᵥ y) i := by
    intro i
    rw [Matrix.mulVec_mulVec, d.pY_levi t, ← Matrix.mulVec_mulVec, diag_mulVec hadj, adj_apply']
  have e0 : d.p0 *ᵥ (mt S (d.levi t) *ᵥ y) = d.p0 *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_levi t]
  rw [hM y, hM (mt S (d.levi t) *ᵥ y), e0]
  simp only [eX, eY, colMul_mul]
  have hX : ∀ i, colMul d.jX i ((d.pX *ᵥ y) i) ∈ latV S L (· = v) ↔
      (fun k => t.1 i i * colMul d.jX i ((d.pX *ᵥ y) i) k) ∈ latV S L (· = v) := fun i =>
    mem_iff_of_unit (hu i).1.2 (hu i).2.2 (inv_mul_diag t ht i) _
  have hY : ∀ i, colMul d.jY i ((d.pY *ᵥ y) i) ∈ latV S L (· = v) ↔
      (fun k => cA D ((t⁻¹).1 i i) * colMul d.jY i ((d.pY *ᵥ y) i) k) ∈ latV S L (· = v) := fun i =>
    mem_iff_of_unit (cA_sub_one (hu i).2.2) (cA_sub_one (hu i).1.2)
      (by rw [← map_mul, mul_comm, inv_mul_diag t ht i, map_one]) _
  exact and_congr (forall_congr' hX) (and_congr (forall_congr' hY) Iff.rfl)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnitsStatement
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittLeviDiagonal_mem_latticeStabilizer_of_units : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), IsSelfDualC S L → MonoAt d L L₀ v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → d.levi t ∈ grpAt S (· = v) → (∀ i, t.1 i i - 1 ∈ intAt D (· = v) ∧ (t⁻¹).1 i i - 1 ∈ intAt D (· = v)) → InK S L (· = v) (d.levi t) := by
  first | exact @GlobalTheory.FinPl.LeviUnitK.inK_levi | exact GlobalTheory.FinPl.LeviUnitK.inK_levi | (intros; apply GlobalTheory.FinPl.LeviUnitK.inK_levi <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChartIntegralGLEqLatticeStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChartIntegralGLEqLatticeStabilizer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section
namespace GlobalTheory.ChartStab


set_option maxHeartbeats 1000000 in
theorem mem_splitLat_iff {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (u : Fin n → Fv D.host.F v) :
    u ∈ GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ ↔
      ∀ i, Valued.v ((((frCo φ β)⁻¹ : GL (Fin n) (Fv D.host.F v)).1 *ᵥ u) i) ≤ 1 := by
  set e := GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ) with he_def
  have hπ : GlobalTheory.SplitHecke.Chart e v (rdA φ) := GlobalTheory.SplitProjChart.chart_idem φ
  have he : IsSplitIdem D e := GlobalTheory.EmbChart.isSplitIdem_idem _
  have hemb : GlobalTheory.AdelicU.chartEmb hπ = GlobalTheory.SplitProjChart.emb φ := AlgHom.ext fun x => by
    rw [GlobalTheory.AdelicU.chartEmb_apply, GlobalTheory.SplitProjChart.rdA_incA]; rfl
  choose y hy using fun k => hπ.1 (u k)
  obtain ⟨Λ₁, hle, hfg, heq⟩ := GlobalTheory.ChainOnto.LStab.exists_fg_sub hβ
  have hsl : GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ₁ = GlobalTheory.AdelicU.splitLat (GlobalTheory.SplitProjChart.emb φ) Λ := by
    ext w
    rw [GlobalTheory.AdelicU.mem_splitLat, GlobalTheory.AdelicU.mem_splitLat, GlobalTheory.ChainOnto.LStab.latLoc_eq hle hfg heq v]
  have h1 := GlobalTheory.AdelicU.SplitFrame.mem_latHat_iff_of_support (GlobalTheory.AdelicU.isCMExt_host D) _ hfg
    (GlobalTheory.AdelicU.SplitFrame.vecLoc_self he hπ y) (GlobalTheory.AdelicU.SplitFrame.vecLoc_ne he hπ y)
  rw [hemb, hsl, show (fun k => rdA φ (y k)) = u from funext hy] at h1
  rw [← h1, GlobalTheory.SplitFrameColumn.latHat_iff_hatL, heq]
  have hβ' := hβ (fun k => Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * y k)))
  rw [hβ']
  have hsw : (fun k => Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * y k))) =
      toEAf D e • fun k => toEAf D (y k) := funext fun k => (toEAf D).map_mul e (y k)
  rw [hsw, Matrix.mulVec_smul]
  set w : Fin n → EAf D := (β⁻¹).1 *ᵥ fun k => toEAf D (y k) with hw
  refine forall_congr' fun i => ?_
  have h2 : (toEAf D e • w) i = toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (w i)) := by
    rw [map_mul, GlobalTheory.SplitFrameColumn.toEAf_finEmb]; rfl
  have h3 : rdA φ (GlobalTheory.AdelicLatMove.finEmb D (w i)) =
      ((((frCo φ β)⁻¹ : GL (Fin n) (Fv D.host.F v)).1 *ᵥ u) i) := by
    rw [← GlobalTheory.SplitProjChart.rdE_toEAf, GlobalTheory.SplitFrameColumn.toEAf_finEmb, hw, RingHom.map_mulVec]
    unfold frCo
    rw [← map_inv]
    congr 1
    funext k
    exact (GlobalTheory.SplitProjChart.rdE_toEAf φ (y k)).trans (hy k)
  rw [h2, show toEAf D (e * GlobalTheory.AdelicLatMove.finEmb D (w i)) =
      Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E (finPart D (e * GlobalTheory.AdelicLatMove.finEmb D (w i))) from rfl,
    GlobalTheory.SplitFrameColumn.comm_mem_intAf_iff, hπ.2.2.2, GlobalTheory.SplitHecke.isInt_Ov, HeightOneSpectrum.mem_adicCompletionIntegers, h3]

theorem hermND (D : D7) (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V

theorem isSelfDualAt_of_isSelfDualC {D : D7} (V : HSp D) {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hΛ : IsSelfDualC V Λ) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.IsSelfDualAt D.sp.cm.sig V.gram Λ v := by
  refine (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff (hermND D V).2 (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice V Λ hΛ)).2 (fun y => ?_) v
  refine (hΛ.2 y).trans (forall₂_congr fun x _ => ?_)
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, hb⟩

theorem isSplitBasis_frCo {D : D7} {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (EAf D)}
    (hβ : Formalism.L2.DIV.IsFrame β Λ) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) :
    GlobalTheory.AdelicU.IsSplitBasis (GlobalTheory.SplitProjChart.emb φ) Λ (frCo φ β) := fun u => by
  rw [mem_splitLat_iff hβ φ, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  simp only [HeightOneSpectrum.mem_adicCompletionIntegers]

theorem grpCo_emb {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v)
    (B : GL (Fin V.rank) (Fv D.host.F v)) (x : GlobalTheory.FinZeta.Gv V v) :
    grpCo φ V B (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v x) =
      GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) (hermND D V) (GlobalTheory.SplitProjChart.emb φ) B x := by
  rw [GlobalTheory.AdelicU.splitEquivIn_apply, ← GlobalTheory.SplitChartLink.rdA_matHom_embV]
  rfl

section Reindex

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem reindex_mem_KO {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (ε : ι ≃ m)
    {x : GL m K} (hx : x ∈ GlobalTheory.SplitWeil.KO K m) (y : GL ι K) (h : ∀ i j, y.1 i j = x.1 (ε i) (ε j)) :
    y ∈ GlobalTheory.SplitWeil.KO K ι := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨Units.map (Matrix.reindexAlgEquiv (ValuativeRel.valuation K).integer (ValuativeRel.valuation K).integer ε.symm).toMonoidHom a, ?_⟩
  ext i j
  rw [h]
  simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

theorem mem_KO_iff_reindex {m ι : Type} [Fintype m] [DecidableEq m] [Fintype ι] [DecidableEq ι] (ε : ι ≃ m)
    (x : GL m K) (y : GL ι K) (h : ∀ i j, y.1 i j = x.1 (ε i) (ε j)) :
    x ∈ GlobalTheory.SplitWeil.KO K m ↔ y ∈ GlobalTheory.SplitWeil.KO K ι :=
  ⟨fun hx => reindex_mem_KO ε hx y h,
    fun hy => reindex_mem_KO ε.symm hy x fun i j => by rw [h]; simp⟩

end Reindex

theorem chart_stab : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) → ∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _ := by
  intro D s k v φ ι hsd hfr hch e he y
  obtain ⟨ε, -, hε⟩ := hch
  have hB := isSplitBasis_frCo hfr φ
  have hL := isSelfDualAt_of_isSelfDualC s.V hsd v
  rw [GlobalTheory.AdelicU.mem_stabLoc_iff_GLint (GlobalTheory.AdelicU.isCMExt_host D) (hermND D s.V) hL hB,
    (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne v _).1]
  have h2 := (hε y).2
  rw [he y, grpCo_emb] at h2
  exact mem_KO_iff_reindex ε _ y fun i j => by rw [← h2]; rfl

end GlobalTheory.ChartStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChartIntegralGLEqLatticeStabilizerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoric_chart_integral_GL_eq_lattice_stabilizer : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ → IsChart s k φ ι → ∀ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) → GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) → ∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _ := by
  first | exact @GlobalTheory.ChartStab.chart_stab | exact GlobalTheory.ChartStab.chart_stab | (intros; apply GlobalTheory.ChartStab.chart_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMemSpanHeisenbergTranslatesOfNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMemSpanHeisenbergTranslatesOfNeZero
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacCyclic

theorem exists_mem_of_eigen {X ι U : Type} [AddCommGroup X] [Module ℂ X] (v : ι → X) (A : U → X →ₗ[ℂ] X) (χ : ι → U → ℂ)
    (hA : ∀ i u, A u (v i) = χ i u • v i) (hp : ∀ i j, (∀ u, χ i u = χ j u) → v i ∈ Submodule.span ℂ {v j})
    (W : Submodule ℂ X) (hW : ∀ u, ∀ x ∈ W, A u x ∈ W) (s : Finset ι) :
    ∀ f ∈ Submodule.span ℂ (v '' s), f ∈ W → f ≠ 0 → ∃ i, v i ∈ W := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  intro f hf hfW hf0

  have hrem : ∀ i ∈ s, ∀ u, A u f - χ i u • f ∈ Submodule.span ℂ (v '' (s.erase i : Finset ι)) := by
    intro i _ u
    have : Submodule.span ℂ (v '' s) ≤
        (Submodule.span ℂ (v '' (s.erase i : Finset ι))).comap (A u - χ i u • LinearMap.id) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      show A u (v j) - χ i u • v j ∈ Submodule.span ℂ (v '' (s.erase i : Finset ι))
      rw [hA, ← sub_smul]
      by_cases h : j = i
      · rw [h, sub_self, zero_smul]; exact zero_mem _
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, Finset.mem_coe.2 (Finset.mem_erase.2 ⟨h, hj⟩), rfl⟩)
    exact this hf
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · simp at hf; exact absurd hf hf0
  by_cases hall : ∀ j ∈ s, ∀ u, χ j u = χ i u
  · have : Submodule.span ℂ (v '' s) ≤ Submodule.span ℂ {v i} := by
      rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      exact hp j i (hall j hj)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (this hf)
    have hc : c ≠ 0 := by rintro rfl; exact hf0 (zero_smul _ _)
    exact ⟨i, (W.smul_mem_iff hc).1 hfW⟩
  · push Not at hall
    obtain ⟨j, hj, u, hu⟩ := hall
    have hm : ∀ k, A u f - χ k u • f ∈ W := fun k => W.sub_mem (hW u f hfW) (W.smul_mem _ hfW)
    by_cases h0 : A u f - χ i u • f = 0
    · refine ih _ (Finset.erase_ssubset hj) _ (hrem j hj u) (hm j) fun h1 => hf0 ?_
      have : (χ j u - χ i u) • f = 0 := by
        rw [sub_smul, ← sub_eq_zero.1 h0, ← sub_eq_zero.1 h1, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hu)
    · exact ih _ (Finset.erase_ssubset hi) _ (hrem i hi u) (hm i) h0

theorem psi_ne_zero {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (x : A) : ψ x ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem fin_add {D : D7} {S T : HSp D} {a b : WO S T} (ha : a.map (infPart D) = 0) (hb : b.map (infPart D) = 0) :
    (a + b).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (a i j) = 0 := congrFun (congrFun ha i) j
  have h2 : infPart D (b i j) = 0 := congrFun (congrFun hb i) j
  show infPart D (a i j + b i j) = 0
  rw [RingHom.map_add (f := _), h1, h2, add_zero]

theorem fin_neg {D : D7} {S T : HSp D} {a : WO S T} (ha : a.map (infPart D) = 0) : (-a).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (a i j) = 0 := congrFun (congrFun ha i) j
  show infPart D (-a i j) = 0
  rw [RingHom.map_neg, h1, neg_zero]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem fin_zero : (0 : WO S T).map (infPart D) = 0 := by
  ext i j
  show infPart D (0 : AE D) = 0
  exact RingHom.map_zero _

theorem symplO_neg_right (u b : WO S T) : symplO S T u (-b) = -symplO S T u b := by
  refine eq_neg_of_add_eq_zero_left ?_
  rw [← GlobalTheory.LatVac.symplO_add_right, neg_add_cancel, GlobalTheory.SplitScalar.symplO_zero_right]

theorem psi_diff {u a b : WO S T} (h : ψ (symplO S T u a) = ψ (symplO S T u b)) : ψ (symplO S T (-b + a) u) = 1 := by
  rw [GlobalTheory.SplitScalar.symplO_skew S T u, GlobalTheory.LatVac.symplO_add_right, symplO_neg_right, neg_add, neg_neg,
    ψ.map_add_eq_mul, ← h, ← ψ.map_add_eq_mul, add_neg_cancel, ψ.map_zero_eq_one]

theorem prop_of_eigen {a b : WO S T} {f₀ : WO S T → ℂ} {ε : ℂ} (h : heisO ψ S T (-b + a) f₀ = ε • f₀) :
    heisO ψ S T a f₀ ∈ Submodule.span ℂ {heisO ψ S T b f₀} := by
  have e := GlobalTheory.LatVac.heisO_heisO ψ b (-b + a) f₀
  rw [h, GlobalTheory.LatVac.heisO_smul, add_neg_cancel_left] at e
  refine (Submodule.smul_mem_iff _ (psi_ne_zero ψ (symplOH S T b (-b + a)))).1 ?_
  rw [← e]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem heis_mem_span {f x : WO S T → ℂ} {b : WO S T} (hb : b.map (infPart D) = 0)
    (hx : x ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f)) :
    heisO ψ S T b x ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← GlobalTheory.SplitScalar.heisL_apply, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [map_smul, GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.LatVac.heisO_heisO]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨b + a, fin_add hb a.2⟩, rfl⟩))

theorem mem_of_heis_mem {W : Submodule ℂ (WO S T → ℂ)} {f₀ : WO S T → ℂ} {a : WO S T}
    (h : heisO ψ S T (-a) (heisO ψ S T a f₀) ∈ W) : f₀ ∈ W := by
  rw [GlobalTheory.LatVac.heisO_heisO, neg_add_cancel, GlobalTheory.LatVac.heisO_zero] at h
  exact (W.smul_mem_iff (psi_ne_zero ψ _)).1 h

theorem mem_span_of_dual (Λ : AddSubgroup (WO S T)) (hfin : ∀ u ∈ Λ, u.map (infPart D) = 0)
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (∀ u' ∈ Λ, ψ (symplO S T u u') = 1) → u ∈ Λ) {f₀ f : WO S T → ℂ}
    (hε : ∀ u : Λ, ∃ ε : ℂ, ε ≠ 0 ∧ heisO ψ S T u f₀ = ε • f₀)
    (hf : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀))
    (hf0 : f ≠ 0) :
    f₀ ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  choose ε hε0 hε using hε
  have hfW : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) :=
    Submodule.subset_span ⟨⟨0, fin_zero⟩, GlobalTheory.LatVac.heisO_zero ψ f⟩
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  have hfs : f ∈ Submodule.span ℂ ((fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) '' c.support) := by
    rw [← hc]
    exact Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)
  obtain ⟨a, ha⟩ := exists_mem_of_eigen (fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀)
    (fun u : Λ => GlobalTheory.SplitScalar.heisL ψ S T u) (fun a u => ψ (symplO S T u a) * ε u)
    (fun a u => by
      rw [GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisO_comm, hε, GlobalTheory.LatVac.heisO_smul, smul_smul])
    (fun a b h => prop_of_eigen (hε ⟨_, hdual _ (fin_add (fin_neg b.2) a.2) fun u hu =>
      psi_diff (mul_right_cancel₀ (hε0 ⟨u, hu⟩) (h ⟨u, hu⟩))⟩))
    _ (fun u x hx => by
      rw [GlobalTheory.SplitScalar.heisL_apply]
      exact heis_mem_span (hfin u u.2) hx) c.support f hfs hfW hf0
  exact mem_of_heis_mem (heis_mem_span (fin_neg a.2) ha)

theorem vac_mem_span : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {f₀ f : WO S T → ℂ}, IsVacO ψ θ S T sS sT ΛS ΛT f₀ → IsSelfDualC S ΛS → IsSelfDualC T ΛT → f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) → f ≠ 0 → f₀ ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ f hv hS hT hf hf0
  obtain ⟨hdual, -, hsign⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hv.1 hS hT
  refine mem_span_of_dual _ (fun u hu => GlobalTheory.SplitScalar.latO_fin hu) (fun u hu h => (hdual u hu).2 h) (fun u => ?_) hf hf0
  obtain ⟨ε, h1, h2⟩ := hsign f₀ hv.2.lat u u.2
  refine ⟨ε, ?_, h2 f₀ hv.2.lat⟩
  rcases h1 with rfl | rfl <;> simp

end GlobalTheory.VacCyclic

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMemSpanHeisenbergTranslatesOfNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_mem_span_heisenbergTranslates_of_ne_zero : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {f₀ f : WO S T → ℂ}, IsVacO ψ θ S T sS sT ΛS ΛT f₀ → IsSelfDualC S ΛS → IsSelfDualC T ΛT → f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) → f ≠ 0 → f₀ ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  first | exact @GlobalTheory.VacCyclic.vac_mem_span | exact GlobalTheory.VacCyclic.vac_mem_span | (intros; apply GlobalTheory.VacCyclic.vac_mem_span <;> assumption)
end
end
