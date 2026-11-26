module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorIdentificationNatural
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaximalIdealIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameBreuilKisinDatumExists
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulNormLe
namespace GlobalTheory.NatCastNormLtOne

theorem norm_natCast_lt_one {l : ℕ} [Fact (Nat.Prime l)] {K : Type} [NormedField K]
    [NormedAlgebra ℚ_[l] K] : ‖(l : K)‖ < 1 := by
  have h : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem exists_pow_mul_norm_le {K : Type} [NormedField K] {x : K} (hx : ‖x‖ < 1) (a : K) :
    ∃ n : ℕ, ‖x ^ n * a‖ ≤ 1 := by
  have h : Filter.Tendsto (fun n : ℕ => ‖x‖ ^ n * ‖a‖) Filter.atTop (nhds (0 * ‖a‖)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg x) hx).mul_const _
  rw [zero_mul] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds (zero_lt_one' ℝ))).exists
  exact ⟨n, by rw [norm_mul, norm_pow]; exact hn.le⟩

theorem exists_pow_smul_mem {l : ℕ} [hl : Fact (Nat.Prime l)] {O K : Type} [CommRing O]
    [NormedField K] [Algebra O K] [GlobalTheory.BK.IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (T : Submodule O V) (hT : Submodule.span K (T : Set V) = ⊤) (v : V) :
    ∃ n : ℕ, (l : K) ^ n • v ∈ T := by
  have hpow : ∀ (k : ℕ) (w : V), w ∈ T → (l : K) ^ k • w ∈ T := by
    intro k w hw
    have h : (l : K) ^ k = algebraMap O K ((l : O) ^ k) := by simp
    rw [h, algebraMap_smul]
    exact T.smul_mem _ hw
  have hv : v ∈ Submodule.span K (T : Set V) := by rw [hT]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]; exact hpow _ _ hn
    · rw [pow_add, mul_smul]; exact hpow _ _ hm
  | smul a x _ hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (norm_natCast_lt_one (l := l) (K := K)) a
    obtain ⟨b, hb⟩ := (GlobalTheory.BK.IsUnitBall.mem_range_iff (O := O) ((l : K) ^ m * a)).2 hm
    refine ⟨m + n, ?_⟩
    have h : (l : K) ^ (m + n) • a • x = b • ((l : K) ^ n • x) := by
      rw [← algebraMap_smul K b, hb, smul_smul, smul_smul]
      congr 1
      ring
    rw [h]
    exact T.smul_mem _ hn

theorem main : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] {O K : Type} [inst : CommRing O]
    [inst_1 : NormedField K] [inst_2 : Algebra O K] [GlobalTheory.BK.IsUnitBall O K]
    [inst_4 : NormedAlgebra ℚ_[l] K] {G : Type} [inst_5 : Group G] [inst_6 : TopologicalSpace G]
    (T : Formalism.BasicNotions.LocLat G ℚ_[l] K O) (v : Formalism.BasicNotions.LocLat.V T),
    ∃ (n : ℕ), (↑l : K) ^ n • v ∈ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T) := by
  intro l _ O K _ _ _ _ _ G _ _ T v
  exact exists_pow_smul_mem T.L.T T.L.span v

end GlobalTheory.NatCastNormLtOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameBreuilKisinDatumExists
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CocycleNat

theorem exists_pow_smul_mem {l : ℕ} [hl : Fact l.Prime] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G]
    (T : LocLat G ℚ_[l] K O) (v : T.V) : ∃ n : ℕ, (l : K) ^ n • v ∈ T.L.T := by
  first
  | exact @_root_.GlobalTheory.NatCastNormLtOne.main
  | exact _root_.GlobalTheory.NatCastNormLtOne.main
  | (apply _root_.GlobalTheory.NatCastNormLtOne.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatCastNormLtOne.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatCastNormLtOne.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatCastNormLtOne.main ..)

end GlobalTheory.CocycleNat

noncomputable section

namespace GlobalTheory.CocycleNat

theorem actB_map {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [Algebra O K]
    [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G] (s : G →* GQ l)
    {T₁ T₂ : LocLat G ℚ_[l] K O} (f : LatHom T₁.L T₂.L) (g : G) (z : TW (OB l O) T₁) :
    TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) (actB s T₁ g z) =
      actB s T₂ g (TensorProduct.map LinearMap.id ((f.f.restrictScalars O).restrict f.T_le) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r x =>
    simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
    congr 1
    exact Subtype.ext (f.equiv g x)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.CocycleNat

namespace GlobalTheory.CocycleNat

theorem main (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ)
    (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (T₁ T₂ : LocLat (Gl l) ℚ_[l] K O)
    (R₁ : GalDat t ϖ (sQ l) D₁ T₁) (R₂ : GalDat t ϖ (sQ l) D₂ T₂) (f : LatHom T₁.L T₂.L) (F : BKHom D₁ D₂) :
    IsMapOf R₁.I R₂.I f F.toHom → ∀ y c, R₁.ClassOf y c → R₂.ClassOf (F.app y) (f.post c) := by
  intro hF y c hc
  obtain ⟨b, ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, hb⟩, hcob⟩ := hc
  have N := GlobalTheory.T.bcrisTensorIdentification_natural l a e O K t ϖ ι D₁.toPhiMod T₁ R₁.I R₁.jB R₁.cmp κ D₂.toPhiMod T₂ R₂.I R₂.jB f
    F.toHom R₂.cmp hF
  set Φ := TensorProduct.map (R := O) (LinearMap.id (R := O) (M := OB l O))
    ((f.f.restrictScalars O).restrict f.T_le) with hΦ
  have hy' : F.app y ∈ ME D₂.toPhiMod := F.app_mem_Mext (le_away _ _) hy
  have hσ' : F.app σ.1 ∈ D₂.MMl := F.toHom.app_mem_ext ((A_le_S (l := l) (e := e)).trans (le_away _ _)) σ.2
  refine ⟨Φ b, ⟨hy', homW t ϖ F.toHom m₀, ⟨F.app σ.1, hσ'⟩, Φ b₀, ?_, F.app_mem_inv h2, ?_, ?_, ?_⟩, ?_⟩
  · rw [← homW_phiW, ← map_sub, h1, homW_toW]
  · change D₂.conn (F.app σ.1) = D₂.zeta (F.app y)
    rw [← F.toHom.app_conn, h3, F.toHom.app_zeta]
  · have := N.2 _ _ h4
    rwa [homW_phiW] at this
  · rw [hb, map_sub, N.1 σ ⟨F.app σ.1, hσ'⟩ rfl]
  · intro g n x' hx'
    obtain ⟨N', hN'⟩ := exists_pow_smul_mem T₁ (c g)
    have hc2 := congrArg Φ (hcob g N' ⟨_, hN'⟩ rfl)
    rw [map_smul, map_sub, actB_map, hΦ, TensorProduct.map_tmul, LinearMap.id_apply] at hc2
    rw [← hΦ] at hc2
    have hsm : ∀ (k : ℕ) (v : T₂.V), ((l : O) ^ k) • v = (l : K) ^ k • v := fun k v => by
      rw [← algebraMap_smul K ((l : O) ^ k) v, map_pow, map_natCast]
    have hx'' : (l : O) ^ N' • x' = (l : O) ^ n • ((f.f.restrictScalars O).restrict f.T_le ⟨_, hN'⟩) := by
      apply Subtype.ext
      change (l : O) ^ N' • (x' : T₂.V) = (l : O) ^ n • f.f ((l : K) ^ N' • c g)
      rw [hx', hsm, hsm, map_smul, smul_smul, smul_smul, mul_comm]
      rfl
    have key : ∀ z w : TW (OB l O) T₂, (l : O) ^ N' • z = (l : O) ^ N' • w → z = w := by
      intro z w h
      have hu : IsUnit ((l : OB l O) ^ N') := by
        have := (GlobalTheory.MemLoc.isUnit_l_Bcris l).map
          (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        rw [map_natCast] at this
        exact this.pow N'
      rw [← algebraMap_smul (OB l O) ((l : O) ^ N') z, ← algebraMap_smul (OB l O) ((l : O) ^ N') w,
        map_pow, map_natCast] at h
      exact hu.smul_left_cancel.1 h
    apply key
    rw [← TensorProduct.tmul_smul, hx'', TensorProduct.tmul_smul, hc2, smul_comm]

end GlobalTheory.CocycleNat
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameBreuilKisinDatumExistsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_breuil_kisin_datum_exists : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (T₁ T₂ : LocLat (Gl l) ℚ_[l] K O) (R₁ : GalDat t ϖ (sQ l) D₁ T₁) (R₂ : GalDat t ϖ (sQ l) D₂ T₂) (f : LatHom T₁.L T₂.L) (F : BKHom D₁ D₂), IsMapOf R₁.I R₂.I f F.toHom → ∀ y c, R₁.ClassOf y c → R₂.ClassOf (F.app y) (f.post c) := by
  first | exact @GlobalTheory.CocycleNat.main | exact GlobalTheory.CocycleNat.main | (intros; apply GlobalTheory.CocycleNat.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRankBound
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousDualMat
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocDirect

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def dualMat {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) :
    Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) (Br.LL D.nbr i w hw) :=
  GlobalTheory.TateDualX.dualTw (cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw)) (Br.loc D.nbr i w hw M)

theorem dualMat_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    dualMat i w hw M g = ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) :
      Br.LL D.nbr i w hw) • (Br.loc D.nbr i w hw M g⁻¹).transpose := rfl

theorem continuous_dualMat {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous (dualMat i w hw M) := by
  haveI := isTopRing i w hw
  exact GlobalTheory.TateDualX.continuous_dualTw _ _ (GlobalTheory.TateDualX.continuous_cyc D i w hw)
    (GlobalTheory.PotDual.continuous_loc D i w hw M hM)

def Udual {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) :=
  haveI := isTopRing i w hw
  GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) (dualMat i w hw M) (continuous_dualMat i w hw M hM)

theorem cyc_mem (g : Br.G D.nbr i w hw) : ∃ c : Br.OLL D.nbr i w hw,
    algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) c =
      ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) := by
  rw [← GlobalTheory.CycBridge.locChi_epsU_eq_cycLL D i w hw]
  exact ⟨_, rfl⟩

theorem dualMat_integral {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    ∃ N : Matrix (Fin k) (Fin k) (Br.OLL D.nbr i w hw),
      dualMat i w hw M g = N.map (algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw)) := by
  obtain ⟨c, hc⟩ := cyc_mem i w hw g
  refine ⟨c • (Br.locO (D.nbr i w hw) (M.comp (decS D.nd w)) g⁻¹).transpose, ?_⟩
  rw [dualMat_apply, ← hc, Matrix.map_smul' _ _ _ (map_mul _), Matrix.transpose_map]
  rfl

def latDual {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) :
    Lattice (O := Br.OLL D.nbr i w hw) (Udual i w hw M hM).ρ :=
  GlobalTheory.BKLatticeCochain.stdLattice Subtype.val_injective (Udual i w hw M hM).ρ fun g => by
    obtain ⟨N, hN⟩ := dualMat_integral i w hw M g
    exact ⟨N, fun x => by rw [← hN]; rfl⟩

end GlobalTheory.Pass.LocDirect

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRankBound
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocDirect

theorem isDualLat1_dual : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g), IsDualLat1 (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) (GlobalTheory.Pass.LocDirect.latDual i w hw M hM) (dotProductBilin (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)) := by
  intro D i w hw k M hM
  refine ⟨GlobalTheory.PotDual.isDual1_of_eq (Br.PD D.loc D.nbr i w hw) (Br.loc D.nbr i w hw M) (dualMat i w hw M)
    (fun g => dualMat_apply i w hw M g), fun y => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨z, rfl⟩ _ ⟨z', rfl⟩
    exact ⟨_, GlobalTheory.BKLatticeCochain.incl_dot z' z⟩
  · refine (GlobalTheory.BKLatticeCochain.mem_range_incl _).2 fun a => ?_
    obtain ⟨o, ho⟩ := h (GlobalTheory.BKLatticeCochain.incl (Br.LL D.nbr i w hw) (Pi.single a (1 : Br.OLL D.nbr i w hw))) ⟨_, rfl⟩
    refine ⟨o, ?_⟩
    rw [← ho]
    change GlobalTheory.BKLatticeCochain.incl (Br.LL D.nbr i w hw) (Pi.single a (1 : Br.OLL D.nbr i w hw)) ⬝ᵥ
      (y : Fin k → Br.LL D.nbr i w hw) = y a
    simp [GlobalTheory.BKLatticeCochain.incl_apply, dotProduct, Pi.single_apply,
      apply_ite (algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw))]
    exact (Finset.sum_ite_eq' _ _ _).trans (if_pos (Finset.mem_univ a))

theorem isCrys_dual : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) → IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.Udual i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) := by
  intro D hF i w hw k M hM K' h hcrys
  haveI := isTopRing i w hw
  have hi : Continuous (Subgroup.inclusion (GK_le h)) := continuous_subtype_val.subtype_mk _
  have hU : Continuous ((Br.loc D.nbr i w hw M).comp (Subgroup.inclusion (GK_le h))) :=
    (GlobalTheory.PotDual.continuous_loc D i w hw M hM).comp hi
  have hU' : Continuous ((dualMat i w hw M).comp (Subgroup.inclusion (GK_le h))) :=
    (continuous_dualMat i w hw M hM).comp hi
  have hc : ∀ g : ↥(GK K'), ((cycLL ((D.loc (D.nd.l i)).PD K') (Br.LL D.nbr i w hw) g : (Br.LL D.nbr i w hw)ˣ) :
      Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw)
        (Subgroup.inclusion (GK_le h) g) : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) := by
    intro g
    simp only [cycLL, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe]
    congr 1
    rw [(D.loc (D.nd.l i)).PD_χ, Br.PD, (D.loc (D.nd.l i)).PD_χ]
    rfl
  have hd : IsDual1 ((D.loc (D.nd.l i)).PD K')
      (matRep ((Br.loc D.nbr i w hw M).comp (Subgroup.inclusion (GK_le h))))
      (matRep ((dualMat i w hw M).comp (Subgroup.inclusion (GK_le h))))
      (dotProductBilin (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)) := by
    refine GlobalTheory.PotDual.isDual1_of_eq _ _ _ fun g => ?_
    rw [hc]
    rfl
  exact (hF (D.nd.l i) K' (D.nbr i w hw).LL).2.2.1
    (GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ hU)
    (GlobalTheory.PotDual.bundle ℚ_[D.nd.l i] (Br.OLL D.nbr i w hw) _ hU') _ hd hcrys

theorem finrank_H1fT_eq : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL] (A : GRep G Qp LL O) (L : Lattice (O := O) A.ρ), (∀ y : G → A.V, Continuous y → ∃ m : O, m ≠ 0 ∧ ∀ g, m • y g ∈ L.T) → finrank O ↥(latticeFiniteCohomology PD L) = finrank LL (FiniteCohomology PD A.ρ) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ _ _ A L hT
  have h := GlobalTheory.BlochKatoRank.rank_subquotient_eq (O := O) (K := LL) (X := G → A.V) (Y := G → A.V)
    LinearMap.id (latticeCocycles L) (latticeCoboundaries L) (latticeFiniteCocycles PD L) (finiteCocycles PD A.ρ) (Formalism.WeaklyAdmissibleFiltrations.B1 A.ρ)
    (fun a ha => ha.2) ?_ ?_ ?_
  · exact congrArg Cardinal.toNat h
  · rintro b ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · rintro a ⟨x, rfl⟩
    obtain ⟨m, hm, hx⟩ := hT (fun _ => x) continuous_const
    refine ⟨m, hm, m • x, hx Classical.ofNonempty, ?_⟩
    change cob A.ρ (m • x) = m • cob A.ρ x
    exact LinearMap.map_smul_of_tower _ _ _
  · intro y hy
    obtain ⟨m, hm, hy'⟩ := hT y hy.1.1
    have hZ : m • y ∈ latticeCocycles L :=
      ⟨(continuousCocycles A.ρ).smul_of_tower_mem m hy.1, Submodule.mem_pi.2 fun g _ => hy' g⟩
    exact ⟨m, hm, m • y, hZ, ⟨hZ, (finiteCocycles PD A.ρ).smul_of_tower_mem m hy⟩, rfl⟩

theorem latDual_bounded {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) (y : Br.G D.nbr i w hw → (Udual i w hw M hM).V) (hy : Continuous y) :
    ∃ m : Br.OLL D.nbr i w hw, m ≠ 0 ∧ ∀ g, m • y g ∈ (latDual i w hw M hM).T := by
  haveI : CompactSpace (Br.G D.nbr i w hw) := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK _
  obtain ⟨N, hN⟩ := GlobalTheory.BlochKatoIntegralScalars.exists_pow_mul_mem_OL (D.nbr i w hw).LL
    (m := k) y hy
  refine ⟨(D.nd.l i : Br.OLL D.nbr i w hw) ^ N, ?_, fun g => ?_⟩
  · intro h0
    have := congrArg (algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw)) h0
    rw [map_pow, map_natCast, map_zero] at this
    exact (Fact.out : (D.nd.l i).Prime).ne_zero (by exact_mod_cast (eq_zero_of_pow_eq_zero this))
  · refine (GlobalTheory.BKLatticeCochain.mem_range_incl _).2 fun j => ⟨⟨_, hN g j⟩, ?_⟩
    change _ = ((D.nd.l i : Br.OLL D.nbr i w hw) ^ N) • (y g : Fin k → Br.LL D.nbr i w hw) j
    rw [Algebra.smul_def, map_pow, map_natCast]
    rfl

theorem dualLat_rank : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → admBK (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) → ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)), letI := U'.modO; letI := U'.towO; ∃ (LT' : Lattice (O := Br.OLL D.nbr i w hw) U'.ρ) (PU : (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw), IsDualLat1 (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) LT' PU ∧ finrank (Br.OLL D.nbr i w hw) ↥(latticeFiniteCohomology (Br.PD D.loc D.nbr i w hw) LT') ≤ k := by
  intro D hF hBK hPDR i w hw hdeg k M hM K' h hcrys
  refine ⟨Udual i w hw M hM, latDual i w hw M hM, dotProductBilin _ _, isDualLat1_dual D i w hw M hM, ?_⟩
  have hcrys' := isCrys_dual D hF i w hw M hM K' h hcrys
  have hdR : IsDR (Br.PD D.loc D.nbr i w hw) (Udual i w hw M hM).ρ :=
    hPDR (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h (Udual i w hw M hM) hcrys'
  have hle := GlobalTheory.Pass.RankDeRham.finrank_H1f_le (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw
    (D.nbr i w hw).LL hdeg (hBK (D.nd.l i) _) (Udual i w hw M hM) hdR
  haveI : IsFractionRing (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) :=
    (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL).1.2.2
  haveI : IsDomain (Br.OLL D.nbr i w hw) := inferInstance
  rw [finrank_H1fT_eq (Br.PD D.loc D.nbr i w hw) (Udual i w hw M hM) (latDual i w hw M hM) (latDual_bounded i w hw M hM)]
  refine hle.trans (le_of_eq ?_)
  exact Module.finrank_fin_fun _

end GlobalTheory.Pass.LocDirect

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRankBoundStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_over_extension : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → admBK (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) → ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)), letI := U'.modO; letI := U'.towO; ∃ (LT' : Lattice (O := Br.OLL D.nbr i w hw) U'.ρ) (PU : (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw), IsDualLat1 (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) LT' PU ∧ finrank (Br.OLL D.nbr i w hw) ↥(latticeFiniteCohomology (Br.PD D.loc D.nbr i w hw) LT') ≤ k := by
  first | exact @GlobalTheory.Pass.LocDirect.dualLat_rank | exact GlobalTheory.Pass.LocDirect.dualLat_rank | (intros; apply GlobalTheory.Pass.LocDirect.dualLat_rank <;> assumption)
end
end
