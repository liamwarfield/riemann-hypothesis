module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesSubsetAdmissibleOfGoodO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleTameDescentGoodLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExactTripleBreuilKisinOfShortExactLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisOfEtaleInvariantBoundedPoles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinExactTripleJumpsCharactersLift
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodRingGaloisInvariantsIffConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionLatticeIsCrysTameTypeWithJumps
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineOfExtensionLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineOfExtensionLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ExtLatCrys

theorem isCrys_comp_extRep {l : ℕ} [Fact l.Prime] {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] (K : FinExt l) (Pl : LocPrime l)
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] (ρ : Representation LL (Gl l) V)
    (hT : IsCrys (Pl.PD K) (ρ.comp (inclG K) : Representation LL ↥(GK K) V)) (z : ↥(continuousCocycles ρ))
    (hz : (z : Gl l → V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ) :
    IsCrys (Pl.PD K) ((GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep ρ z).comp (inclG K) : Representation LL ↥(GK K) (V × LL)) := by
  let ρ' : Representation LL ↥(GK K) V := ρ.comp (inclG K)
  have hρ' : ∀ g, ρ' g = ρ (inclG K g) := fun _ => rfl
  have hc : (fun g => (z : Gl l → V) (inclG K g)) ∈ continuousCocycles ρ' :=
    ⟨z.2.1.comp (continuous_subtype_val.subtype_mk _), fun g k => by
      have := z.2.2 (inclG K g) (inclG K k)
      rw [← map_mul] at this
      exact this⟩
  have h0 := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep_isExt ρ' ⟨_, hc⟩
  have h2 : ∀ (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] Pl.R.B), actVB (Pl.PD K) ρ' g y =
      actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) ρ (inclG K g) y := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, Pl.PD_actB, hρ']; rfl
    | add u w hu hw => rw [map_add (f := _), map_add (f := _), hu, hw]
  have h1 := (GlobalTheory.CrysExt.isCrystalline_iff_mem_H1f (Pl.PD K) (ρ := ρ') hT h0.1 ⟨_, hc⟩ h0.2).mpr
    ((GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.mk_mem_H1fSub (Pl.PD K) ρ' ⟨_, hc⟩).mpr (by
      obtain ⟨-, x, hx⟩ := hz
      refine ⟨hc, x, fun g => ?_⟩
      rw [h2]
      exact hx (inclG K g)))
  exact h1

theorem isCrys_comp_extRep_lat {l : ℕ} [Fact l.Prime] {LL O : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (K : FinExt l) (Pl : LocPrime l)
    (T : LocLat (Gl l) ℚ_[l] LL O)
    (hT : IsCrys (Pl.PD K) (T.ρ.comp (inclG K) : Representation LL ↥(GK K) T.V)) (z : ↥(continuousCocycles T.ρ))
    (hz : (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ) :
    IsCrys (Pl.PD K) ((GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep T.ρ z).comp (inclG K) : Representation LL ↥(GK K) (T.V × LL)) :=
  isCrys_comp_extRep K Pl T.ρ hT z hz

theorem isCrys_resF_extLat : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL), IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → ∀ z : ↥(latticeCocycles T.L), (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ → IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ := by
  intro l _ a e _ _ ϖ LL _ _ Pl T hT z hz
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact isCrys_comp_extRep_lat (ϖ.field a) Pl T hT ⟨z, z.2.1⟩ hz

end GlobalTheory.ExtLatCrys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineOfExtensionLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_of_extension_lattice : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL), IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → ∀ z : ↥(latticeCocycles T.L), (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ → IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ := by
  first | exact @GlobalTheory.ExtLatCrys.isCrys_resF_extLat | exact GlobalTheory.ExtLatCrys.isCrys_resF_extLat | (intros; apply GlobalTheory.ExtLatCrys.isCrys_resF_extLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionOfJumps
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionOfJumps
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.ExtJumps

open Module Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence


set_option maxHeartbeats 1000000 in
theorem jumps_of_ses {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (Tt : LocTied l P AI)
    {K LL : FinExt l} (T T₁ T₂ : Lat K LL) (f : T.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V)
    (hses : IsSES f g) (hdr0 : IsDR (P.PD K) T.ρ) (hdr1 : IsDR (P.PD K) T₁.ρ) (hdr2 : IsDR (P.PD K) T₂.ρ)
    (τ : Emb K LL) (h2 : ∀ b : ℤ, finrank ↥LL.1 ↥(FildR (P.PD K) T₂.ρ τ b) = if b ≤ 0 then 1 else 0)
    (U : Set ℤ) (hU : (0 : ℤ) ∈ U) (hJ : JumpsInV (P.PD K) T.ρ τ U) : JumpsInV (P.PD K) T₁.ρ τ U := by
  have := K.2
  have := LL.2
  have hfin : ∀ b, FiniteDimensional ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b) := by
    intro b
    haveI := (GlobalTheory.T.concretePeriod_deRham_module_finrank_le l P AI Tt K LL T₁.V T₁.ρ).1
    exact Submodule.finiteDimensional_of_le (inf_le_left.trans inf_le_left)
  have key : ∀ b : ℤ, finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b) =
      finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ b) + if b ≤ 0 then 1 else 0 := by
    intro b
    have hs : StrictAt P K LL := GlobalTheory.DRFil.strictAt Tt K LL
    have hs2 := hs T T₁ T₂ f g hses hdr0 hdr1 hdr2 τ b
    unfold SubSES at hs2
    obtain ⟨k₀, k₁, k₂⟩ := hs2
    haveI := hfin b
    have h := GlobalTheory.CrysExt.finrank_add_of_exact (LL := ↥LL.1) (mapdR P f) (mapdR P g) (FildR (P.PD K) T.ρ τ b)
      (FildR (P.PD K) T₁.ρ τ b) (FildR (P.PD K) T₂.ρ τ b) k₀ (Submodule.ext k₁) (Submodule.ext k₂)
    have h3 := h2 b
    omega
  intro b hb
  by_contra hbU
  have hTb : FildR (P.PD K) T.ρ τ (b + 1) = FildR (P.PD K) T.ρ τ b := by
    by_contra h
    exact hbU (hJ b h)
  have hb0 : b ≠ 0 := by rintro rfl; exact hbU hU
  apply hb
  haveI := hfin b
  have hle : FildR (P.PD K) T₁.ρ τ (b + 1) ≤ FildR (P.PD K) T₁.ρ τ b :=
    GlobalTheory.DRFil.FildR_antitone (P.PD K) T₁.ρ τ (Int.le_add_one le_rfl)
  have e3 : finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ (b + 1)) = finrank ↥LL.1 ↥(FildR (P.PD K) T.ρ τ b) :=
    congrArg (fun S : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) => finrank ↥LL.1 ↥S) hTb
  have e1 := key (b + 1)
  have e2 := key b
  have hr : finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ (b + 1)) = finrank ↥LL.1 ↥(FildR (P.PD K) T₁.ρ τ b) := by
    have h4 : (if b + 1 ≤ 0 then 1 else 0 : ℕ) = if b ≤ 0 then 1 else 0 := by
      split_ifs <;> omega
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle hr

theorem jumps_extLat : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (T : QLat LL) (U : Finset ℤ), (0 : ℤ) ∈ U → IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ (U : Set ℤ)) → ∀ z : ↥(latticeCocycles T.L), IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ → ∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z).ρ τ (U : Set ℤ) := by
  intro l _ a e _ _ ϖ LL _ _ Pl AI hstd T U hU hT hJ z hz τ
  obtain ⟨Tt⟩ := hstd
  have hK : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ (ϖ.field a).1 := bot_le
  have := (Formalism.MainNotions.ElementDenominator.qlExt l).2
  have := LL.2
  have hdr0 := GlobalTheory.DRFil.potCrysDeRhamAt Tt (Formalism.MainNotions.ElementDenominator.qlExt l) LL T (ϖ.field a) hK hT
  have hdr1 := GlobalTheory.DRFil.potCrysDeRhamAt Tt (Formalism.MainNotions.ElementDenominator.qlExt l) LL
    (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a) hK hz
  have hext := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.extRep_isExt T.ρ ⟨(z : Gl l → T.V), z.2.1⟩
  refine jumps_of_ses Tt T (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (unitLat (Gl l))
    (LinearMap.inl ↥LL.1 T.V ↥LL.1) (LinearMap.snd ↥LL.1 T.V ↥LL.1)
    ⟨hext.1.2.2.2.1, hext.1.2.2.2.2, hext.1.1, hext.1.2.1, hext.1.2.2.1⟩ hdr0 hdr1
    (GlobalTheory.CrysExt.isDR_trivial (G := Gl l) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1)) τ
    (fun b => GlobalTheory.CrysExt.finrank_fildR_trivial (G := Gl l) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) τ b) _ hU (hJ τ)

end GlobalTheory.ExtJumps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionOfJumpsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_extension_of_jumps : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (T : QLat LL) (U : Finset ℤ), (0 : ℤ) ∈ U → IsCrys (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ → (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ (U : Set ℤ)) → ∀ z : ↥(latticeCocycles T.L), IsCrys (Pl.PD (ϖ.field a)) (resF (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) (ϖ.field a)).ρ → ∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z).ρ τ (U : Set ℤ) := by
  first | exact @GlobalTheory.ExtJumps.jumps_extLat | exact GlobalTheory.ExtJumps.jumps_extLat | (intros; apply GlobalTheory.ExtJumps.jumps_extLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTypeOfExtensionLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTypeOfExtensionLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TameExt

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions

theorem aeval_intertwine {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N) (a : Module.End R M) (b : Module.End R N) (hab : ∀ v, b (f v) = f (a v))
    (p : Polynomial R) (v : M) : Polynomial.aeval b p (f v) = f (Polynomial.aeval a p v) := by
  have hpow : ∀ (n : ℕ) v, (b ^ n) (f v) = f ((a ^ n) v) := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, hab, ih, pow_succ, Module.End.mul_apply]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow, map_smul]

section Gen

variable {G H : Type} [Group G] [Group H] (ι : H →* G)
  {Qp K₀ K K₀' K' B BdR : Type} [Field Qp] [Field K₀] [Field K] [Field K₀'] [Field K']
  [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
  [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
  [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
  [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
  [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
  [Algebra K₀' B] [IsScalarTower Qp K₀' B]
  [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
  [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
  (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData H Qp K₀' K' B BdR)
  {LL : Type} [Field LL] [Algebra Qp LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem actVB_comp' (hι : ∀ h b, PD'.actB h b = PD.actB (ι h) b) (ρ : Representation LL G V) (h : H)
    (v : V ⊗[Qp] B) : actVB PD' (ρ.comp ι) h v = actVB PD ρ (ι h) v := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v b =>
    change ρ (ι h) v ⊗ₜ[Qp] PD'.actB h b = ρ (ι h) v ⊗ₜ[Qp] PD.actB (ι h) b
    rw [hι]

theorem actVB_mulVB' (ρ : Representation LL G V) (g : G) (k : K₀')
    (hk : PD.actB g (algebraMap K₀' B k) = algebraMap K₀' B k) (v : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (LL := LL) k v) = mulVB (LL := LL) k (actVB PD ρ g v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul v b =>
    change ρ g v ⊗ₜ[Qp] PD.actB g (algebraMap K₀' B k * b) = ρ g v ⊗ₜ[Qp] (algebraMap K₀' B k * PD.actB g b)
    rw [map_mul, hk]

theorem snd_actVB' (ρ : Representation LL H (V × LL)) (hρ : ∀ h v, (ρ h v).2 = v.2) (h : H)
    (w : (V × LL) ⊗[Qp] B) :
    AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) (((PD'.actB h).toAlgHom.toLinearMap).restrictScalars Qp)
        (AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) w) =
      AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) (actVB PD' ρ h w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add w w' hw hw' => simp only [map_add (f := _), hw, hw']
  | tmul v b =>
    have h2 : LinearMap.snd LL V LL (ρ h v) = v.2 := hρ h v
    simp only [actVB, AlgebraTensorModule.map_tmul, AlgebraTensorModule.rTensor_tmul, h2]
    rfl

theorem aeval_extRep' [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [FiniteDimensional Qp LL]
    (hι : ∀ h b, PD'.actB h b = PD.actB (ι h) b) (ρ : Representation LL G V) (c : ↥(continuousCocycles ρ))
    (hc : ∃ β : V ⊗[Qp] B, ∀ h, (c : G → V) h ⊗ₜ[Qp] (1 : B) = actVB PD ρ h β - β)
    (g : G) (hg : ∀ k : K₀', PD.actB g (algebraMap K₀' B k) = algebraMap K₀' B k)
    (P : Polynomial LL) (hP : (Polynomial.X - Polynomial.C 1) ∣ P)
    (hTP : ∀ x ∈ Dcris PD' (ρ.comp ι), Polynomial.aeval (actVB PD ρ g : Module.End LL (V ⊗[Qp] B)) P x = 0)
    (x : (V × LL) ⊗[Qp] B) (hx : x ∈ Dcris PD' ((extRep ρ c).comp ι)) :
    Polynomial.aeval (actVB PD (extRep ρ c) g : Module.End LL ((V × LL) ⊗[Qp] B)) P x = 0 := by
  have hE := extRep_isExt ρ c
  obtain ⟨y, hy, hpy⟩ := (GlobalTheory.CrysExt.coboundary_iff_lift PD hE.1 hE.2).1 hc
  have hyfix : ∀ h : G, actVB PD (extRep ρ c) h y = y := (GlobalTheory.CrysSub.mem_Dcris _ _ _).1 hy
  have hf : ∀ (h : H) (v : V), LinearMap.inl LL V LL ((ρ.comp ι) h v) =
      ((extRep ρ c).comp ι) h (LinearMap.inl LL V LL v) := fun h v => hE.1.2.2.2.1 _ v
  have hq : ∀ (h : H) (v : V × LL), LinearMap.snd LL V LL (((extRep ρ c).comp ι) h v) =
      Representation.trivial LL H LL h (LinearMap.snd LL V LL v) := fun h v => hE.1.2.2.2.2 _ v
  have hkF : ∀ (h : H) (k : K₀'), PD.actB (ι h) (algebraMap K₀' B k) = algebraMap K₀' B k :=
    fun h k => (hι h _).symm.trans (AlgEquiv.commutes _ k)
  have hsm : ∀ (k : K₀') (v : (V × LL) ⊗[Qp] B),
      AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) (mulVB (LL := LL) k v) =
        mulVB (LL := LL) k (AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) v) := by
    intro k v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVB]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

  have hlift1 : ∀ u : LL ⊗[Qp] K₀', ∃ x₁ : (V × LL) ⊗[Qp] B,
      x₁ ∈ Dcris PD' ((extRep ρ c).comp ι) ∧
      AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) x₁ = GlobalTheory.CrysExt.incl Qp K₀' B LL u ∧
      actVB PD (extRep ρ c) g x₁ = x₁ := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, zero_mem _, by simp, by simp⟩
    | tmul a k =>
      refine ⟨a • mulVB (LL := LL) k y, (GlobalTheory.CrysSub.mem_Dcris _ _ _).2 fun h => ?_, ?_, ?_⟩
      · rw [map_smul, actVB_comp' ι PD PD' hι, actVB_mulVB' PD _ _ k (hkF h k), hyfix]
      · rw [map_smul, hsm, hpy]
        simp [mulVB, smul_tmul', GlobalTheory.CrysExt.incl, AlgebraTensorModule.map_tmul]
      · rw [map_smul, actVB_mulVB' PD _ _ k (hg k), hyfix]
    | add u v hu hv =>
      obtain ⟨x₁, h1, h2, h3⟩ := hu
      obtain ⟨x₂, h4, h5, h6⟩ := hv
      exact ⟨x₁ + x₂, add_mem h1 h4, by rw [map_add (f := _), map_add (f := _), h2, h5], by rw [map_add (f := _), h3, h6]⟩

  obtain ⟨u, hu⟩ := (GlobalTheory.CrysExt.invariant_iff (fun h : H => PD'.actB h) PD'.invB _).1 fun h => by
    rw [snd_actVB' PD' ((extRep ρ c).comp ι) (fun h v => hE.1.2.2.2.2 (ι h) v) h x, (GlobalTheory.CrysSub.mem_Dcris _ _ _).1 hx h]
  obtain ⟨x₁, hx₁, hsx₁, hgx₁⟩ := hlift1 u

  have hD : x - x₁ ∈ Dcris PD' ((extRep ρ c).comp ι) := sub_mem hx hx₁
  have hker : (⟨x - x₁, hD⟩ : ↥(Dcris PD' ((extRep ρ c).comp ι))) ∈
      LinearMap.ker (GlobalTheory.CrysSub.Dmap PD' _ _ _ hq) := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change AlgebraTensorModule.rTensor Qp B (LinearMap.snd LL V LL) (x - x₁) = 0
    rw [map_sub, hsx₁, hu, sub_self]
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.CrysSub.exact_Dmap PD' (ρ.comp ι) ((extRep ρ c).comp ι)
    (Representation.trivial LL H LL) (LinearMap.inl LL V LL) (LinearMap.snd LL V LL)
    hf hq LinearMap.inl_injective Function.Exact.inl_snd LinearMap.snd_surjective hker
  have hx0 : AlgebraTensorModule.rTensor Qp B (LinearMap.inl LL V LL) (x₀ : V ⊗[Qp] B) = x - x₁ :=
    congrArg Subtype.val hx₀
  have hxe : x = x₁ + AlgebraTensorModule.rTensor Qp B (LinearMap.inl LL V LL) (x₀ : V ⊗[Qp] B) := by
    rw [hx0]; abel

  have hpart1 : Polynomial.aeval (actVB PD (extRep ρ c) g : Module.End LL ((V × LL) ⊗[Qp] B)) P x₁ = 0 := by
    obtain ⟨Q, rfl⟩ := hP
    rw [mul_comm, map_mul, Module.End.mul_apply]
    have h1 : Polynomial.aeval (actVB PD (extRep ρ c) g : Module.End LL ((V × LL) ⊗[Qp] B))
        (Polynomial.X - Polynomial.C (1 : LL)) x₁ = 0 := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, map_one, LinearMap.sub_apply, Module.End.one_apply,
        hgx₁, sub_self]
    rw [h1, map_zero]
  have hpart2 := aeval_intertwine (AlgebraTensorModule.rTensor Qp B (LinearMap.inl LL V LL))
    (actVB PD ρ g) (actVB PD (extRep ρ c) g)
    (fun v => (GlobalTheory.CrysSub.rTensor_act _ _ _ _ hE.1.2.2.2.1 g v).symm) P (x₀ : V ⊗[Qp] B)
  rw [hxe, map_add (f := _), hpart1, hpart2, hTP _ x₀.2, map_zero, add_zero]

end Gen

end GlobalTheory.TameExt

namespace GlobalTheory.TameExt

theorem tameType_extLat {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l}
    [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL) (Sig : Finset (ZMod e))
    (h0 : (0 : ZMod e) ∈ Sig) (hT : TameType a ϖ Pl T Sig) (z : ↥(latticeCocycles T.L))
    (hz : (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ) :
    TameType a ϖ Pl (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) Sig := by
  intro g hg w hw x hx
  have hFD : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hP : (Polynomial.X - Polynomial.C (1 : ↥LL.1)) ∣ ∏ c ∈ Sig, (Polynomial.X - Polynomial.C (w ^ c.val)) := by
    have h1 := Finset.dvd_prod_of_mem (fun c : ZMod e => Polynomial.X - Polynomial.C (w ^ c.val)) h0
    rwa [ZMod.val_zero, pow_zero] at h1
  exact aeval_extRep' (inclG (ϖ.field a)) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (Pl.PD (ϖ.field a))
    (fun h b => (Pl.PD_actB _ h b).trans (Pl.PD_actB _ (inclG _ h) b).symm) T.ρ ⟨z, z.2.1⟩ hz.2 g
    (fun k => (Pl.PD_actB _ g _).trans (Pl.actQ_Kur _ ⟨k, k.2.2⟩ ⟨k, k.2.2⟩
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (GlobalTheory.BKGal.UnitModel.fix_Kur hg) _ k.2.2)))
    _ hP (hT g hg w hw) x hx

end GlobalTheory.TameExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTypeOfExtensionLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_type_of_extension_lattice : ∀ {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (T : QLat LL) (Sig : Finset (ZMod e)), (0 : ZMod e) ∈ Sig → TameType a ϖ Pl T Sig → ∀ z : ↥(latticeCocycles T.L), (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ → TameType a ϖ Pl (GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z) Sig := by
  first | exact @GlobalTheory.TameExt.tameType_extLat | exact GlobalTheory.TameExt.tameType_extLat | (intros; apply GlobalTheory.TameExt.tameType_extLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionLatticeIsCrysTameTypeWithJumps
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.ExtGood

variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {LL : FinExt l}
  [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l)

abbrev ext (T : QLat LL) (z : ↥(latticeCocycles T.L)) : QLat LL :=
  GlobalTheory.FiniteAdm.extLat (O := ↥(OL LL)) Subtype.val_injective T z

theorem aeval_mul_eq_zero {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (A : Module.End K M)
    (p q : Polynomial K) (x : M) (h : Polynomial.aeval A q x = 0) : Polynomial.aeval A (p * q) x = 0 := by
  rw [map_mul, Module.End.mul_apply, h, map_zero]

theorem isGood_mono (T : QLat LL) {Sig : Finset (ZMod e)} {U : Finset ℤ} (h : IsGood a ϖ Pl T {0} {0})
    (hS : (0 : ZMod e) ∈ Sig) (hU : (0 : ℤ) ∈ U) : IsGood a ϖ Pl T Sig U := by
  refine ⟨h.crys, fun g hg w hw x hx => ?_, fun τ j hj => ?_⟩
  · have h1 := h.type g hg w hw x hx
    rw [Finset.prod_singleton] at h1
    rw [← Finset.prod_erase_mul _ _ hS]
    exact aeval_mul_eq_zero _ _ _ _ h1
  · have h2 := h.jumps τ j hj
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at h2
    subst h2
    exact hU

def incl (T : QLat LL) (z : ↥(latticeCocycles T.L)) : LatHom T.L (ext T z).L where
  f := LinearMap.inl ↥LL.1 T.V ↥LL.1
  equiv g x := by
    change ((T.ρ g x, 0) : T.V × ↥LL.1) = (T.ρ g x + (0 : ↥LL.1) • (z : Gl l → T.V) g, 0)
    simp
  cont := continuous_id.prodMk continuous_const
  T_le x hx := ⟨hx, 0, map_zero _⟩

def proj (T : QLat LL) (z : ↥(latticeCocycles T.L)) : LatHom (ext T z).L (unitLat (Gl l) : QLat LL).L where
  f := LinearMap.snd ↥LL.1 T.V ↥LL.1
  equiv g x := rfl
  cont := continuous_snd
  T_le x hx := hx.2

theorem extLat_isGood : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ), (0 : ZMod e) ∈ Sig → (0 : ℤ) ∈ U → IsGood a ϖ Pl (unitLat (Gl l) : QLat LL) Sig U ∧ ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ (Tp : QLat LL) (f : LatHom T.L Tp.L) (g : LatHom Tp.L (unitLat (Gl l) : QLat LL).L) (v : Tp.V), IsSESLat (Qp := ℚ_[l]) f g ∧ v ∈ Tp.L.T ∧ g.f v = (1 : ↥LL.1) ∧ (∀ h, Tp.ρ h v - v = f.f (c h)) ∧ IsGood a ϖ Pl Tp Sig U := by
  intro _ l _ a e _ _ ϖ LL _ _ Pl AI hstd Sig U hS hU
  refine ⟨isGood_mono ϖ Pl _ (UnitModel.isGood_of_trivial ϖ Pl _ fun _ _ => rfl) hS hU, fun T hT c hc => ?_⟩
  let z : ↥(latticeCocycles T.L) := ⟨c, hc.1⟩
  have hz : (z : Gl l → T.V) ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ := hc.2
  have hcr := GlobalTheory.T.crystalline_of_extension_lattice ϖ Pl T hT.crys z hz
  refine ⟨ext T z, incl T z, proj T z, ((0 : T.V), (1 : ↥LL.1)), ⟨LinearMap.inl_injective,
    fun y => ⟨(0, y), rfl⟩, fun y hy => ?_, fun x => ?_, fun y hy => ?_⟩, ⟨zero_mem _, 1, (algebraMap (OL LL) LL.1).map_one⟩, rfl,
    fun h => ?_, ⟨hcr, GlobalTheory.T.tame_type_of_extension_lattice ϖ Pl T Sig hS hT.type z hz, GlobalTheory.T.crystalline_extension_of_jumps ϖ Pl AI hstd T U hU hT.crys hT.jumps z hcr⟩⟩
  · obtain ⟨o, rfl⟩ := hy
    exact ⟨(0, Algebra.linearMap _ _ o), ⟨zero_mem _, o, rfl⟩, rfl⟩
  · change x.2 = 0 ↔ ∃ y, ((y, 0) : T.V × ↥LL.1) = x
    exact ⟨fun h0 => ⟨x.1, Prod.ext rfl h0.symm⟩, fun ⟨y, hy⟩ => by rw [← hy]⟩
  · exact hy.1
  · change ((T.ρ h 0 + (1 : ↥LL.1) • (z : Gl l → T.V) h, (1 : ↥LL.1)) : T.V × ↥LL.1) - (0, 1) = (c h, 0)
    simp only [map_zero, zero_add, one_smul]
    exact Prod.ext (sub_zero _) (sub_self _)

end GlobalTheory.ExtGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionLatticeIsCrysTameTypeWithJumpsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extensionLattice_isCrysTameTypeWithJumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ), (0 : ZMod e) ∈ Sig → (0 : ℤ) ∈ U → IsGood a ϖ Pl (unitLat (Gl l) : QLat LL) Sig U ∧ ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ (Tp : QLat LL) (f : LatHom T.L Tp.L) (g : LatHom Tp.L (unitLat (Gl l) : QLat LL).L) (v : Tp.V), IsSESLat (Qp := ℚ_[l]) f g ∧ v ∈ Tp.L.T ∧ g.f v = (1 : ↥LL.1) ∧ (∀ h, Tp.ρ h v - v = f.f (c h)) ∧ IsGood a ϖ Pl Tp Sig U := by
  first | exact @GlobalTheory.ExtGood.extLat_isGood | exact GlobalTheory.ExtGood.extLat_isGood | (intros; apply GlobalTheory.ExtGood.extLat_isGood <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPreimageInvertedPrimeBreuilOfExactTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPreimageInvertedPrimeBreuilOfExactTriple
noncomputable section

namespace GlobalTheory.BK.ExtExact

open PowerSeries GlobalTheory.BK Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] {ι κ μ : Type} [Fintype ι]
  [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}

theorem exists_pow_of_coker (G : Hom Q T) (h : IsFiniteLength (A O K) G.coker) :
    ∃ n : ℕ, ∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y := by
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isFiniteLength (l : A O K)
    (isUnit_one_sub_mul_l l) _ h
  refine ⟨n, fun y hy => ?_⟩
  have h1 := hn (Submodule.Quotient.mk ⟨y, hy⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  change _ ∈ (G.imM).comap T.M.subtype at h1
  rw [Submodule.mem_comap, Hom.imM, Submodule.mem_map] at h1
  obtain ⟨x, hx, hxy⟩ := h1
  refine ⟨x, hx, ?_⟩
  rw [LinearMap.restrictScalars_apply] at hxy
  rw [hxy]
  ext τ i
  simp [Algebra.smul_def]


open IntegralLeftInverseExactTriple in
theorem exists_split (F : Hom P Q) (G : Hom Q T) (hFG : IsExactTriple F G) (n : ℕ)
    (hG : ∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y) (τ : ZMod a) :
    ∃ (W : Matrix ι κ K⟦X⟧) (Xm : Matrix κ μ K⟦X⟧), (∀ i k, W i k ∈ A O K) ∧
      (∀ k j, Xm k j ∈ A O K) ∧
      F.mat τ * W + Xm * G.mat τ = (l : K) ^ n • (1 : Matrix κ κ K⟦X⟧) := by
  have h1 : ∀ j : μ, ∃ x ∈ Q.M, G.app x = ((l : K) ^ n) • (Pi.single τ (Pi.single j 1) : Vec K a μ) :=
    fun j => hG _ (mem_M_single T τ _ fun i => by
      by_cases h : i = j
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
  choose x hxM hx using h1
  let Xm : Matrix κ μ K⟦X⟧ := Matrix.of fun k j => x j τ k
  have hXA : ∀ k j, Xm k j ∈ A O K := fun k j => mem_vecs.1 (mem_tot.1 (hxM j) τ) k
  have hGX : G.mat τ * Xm = ((l : K) ^ n) • (1 : Matrix μ μ K⟦X⟧) := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hx j) τ) i
    rw [Hom.app_apply, Pi.smul_apply, Pi.single_eq_same] at this
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simpa [Matrix.mulVec, dotProduct, Xm, Pi.single_apply, eq_comm] using this
  let Z : Matrix κ κ K⟦X⟧ := ((l : K) ^ n) • (1 : Matrix κ κ K⟦X⟧) - Xm * G.mat τ
  have hZA : ∀ k k', Z k k' ∈ A O K := fun k k' => sub_mem (smul_one_mem κ n k k')
    (Subalgebra.sum_mem _ fun j _ => mul_mem (hXA _ _) (G.mem _ _ _))
  have hGZ : G.mat τ * Z = 0 := by
    simp only [Z, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc, hGX,
      Matrix.smul_mul, Matrix.one_mul, sub_self]
  have h2 : ∀ k : κ, ∃ w ∈ P.M, F.app w = Pi.single τ (fun k' => Z k' k) := by
    intro k
    have hm := mem_M_single Q τ (fun k' => Z k' k) fun k' => hZA k' k
    have hz : G.mat τ *ᵥ (fun k' => Z k' k) = 0 := by
      funext i
      have := congrFun (congrFun hGZ i) k
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    obtain ⟨w, hw, h⟩ := (hFG.exact _ hm).1 (by rw [app_single, hz, Pi.single_zero])
    exact ⟨w, hw, h⟩
  choose w hwM hw using h2
  let W : Matrix ι κ K⟦X⟧ := Matrix.of fun i k => w k τ i
  have hWA : ∀ i k, W i k ∈ A O K := fun i k => mem_vecs.1 (mem_tot.1 (hwM k) τ) i
  have hFW : F.mat τ * W = Z := by
    refine Matrix.ext fun i k => ?_
    have := congrFun (congrFun (hw k) τ) i
    rw [Hom.app_apply, Pi.single_eq_same] at this
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, W] using this
  refine ⟨W, Xm, hWA, hXA, ?_⟩
  rw [hFW, sub_add_cancel]

theorem map_frob_smul_one (n : ℕ) :
    ((l : K) ^ n • (1 : Matrix κ κ K⟦X⟧)).map (frob K l) = (l : K) ^ n • (1 : Matrix κ κ K⟦X⟧) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.BK.ExtExact

namespace GlobalTheory.BK.ExtExact

open PowerSeries GlobalTheory.BK Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] {ι κ μ : Type} [Fintype ι]
  [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}

theorem exists_comp [NeZero e] (F : Hom P Q) (G : Hom Q T) (hFG : IsExactTriple F G)
    {v : Vec K a κ} (hv : v ∈ Q.ext (invL l (S O K e))) (hGv : G.app v = 0) (τ : ZMod a) :
    ∃ c' ∈ vecs ι (invL l (S O K e)), v τ = F.mat τ *ᵥ (P.mx τ *ᵥ c') := by
  obtain ⟨n, hn⟩ := exists_pow_of_coker G hFG.finiteLength
  have hAB : ∀ f ∈ A O K, f ∈ invL l (S O K e) := fun f hf => le_away _ _ (A_le_S l e hf)
  obtain ⟨c, hc, hvc⟩ := Q.mem_extc.1 (mem_tot.1 hv τ)
  obtain ⟨W, Xm, hWA, -, hsplit⟩ := exists_split F G hFG n hn (τ - 1)
  have hGc : (G.mat (τ - 1)).map (frob K l) *ᵥ c = 0 := by
    have h1 := congrFun hGv τ
    rw [Pi.zero_apply, Hom.app_apply, hvc, Matrix.mulVec_mulVec, G.comm,
      ← Matrix.mulVec_mulVec] at h1
    have h2 : (T.mxInv τ * T.mx τ) *ᵥ ((G.mat (τ - 1)).map (frob K l) *ᵥ c) = 0 := by
      rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]
    rwa [T.mxInv_mul_mx, Matrix.one_mulVec] at h2
  have hs : (F.mat (τ - 1)).map (frob K l) * W.map (frob K l) +
      Xm.map (frob K l) * (G.mat (τ - 1)).map (frob K l) = (l : K) ^ n • (1 : Matrix κ κ K⟦X⟧) := by
    have : (F.mat (τ - 1) * W + Xm * G.mat (τ - 1)).map (frob K l).toRingHom =
        ((l : K) ^ n • (1 : Matrix κ κ K⟦X⟧)).map (frob K l).toRingHom := by rw [hsplit]
    rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul] at this
    rw [← map_frob_smul_one]
    exact this
  have hc2 : (l : K) ^ n • c = (F.mat (τ - 1)).map (frob K l) *ᵥ (W.map (frob K l) *ᵥ c) := by
    have := congrArg (· *ᵥ c) hs
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hGc, Matrix.mulVec_zero,
      add_zero, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    exact this.symm
  refine ⟨((l : K) ^ n)⁻¹ • (W.map (frob K l) *ᵥ c), fun i => ?_, ?_⟩
  · rw [Pi.smul_apply, PowerSeries.smul_eq_C_mul]
    refine mul_mem (HasK.C_mem _) (Subalgebra.sum_mem _ fun k _ => mul_mem ?_ (hc k))
    exact hAB _ (frob_mem_A l (hWA i k))
  · rw [hvc, Matrix.mulVec_mulVec, F.comm, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, ← hc2,
      inv_smul_smul₀ (pow_ne_zero _ (l_ne_zero l))]

end GlobalTheory.BK.ExtExact


open PowerSeries GlobalTheory.BK Matrix in
theorem GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple : ∀ (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NeZero e]
    [NormedAlgebra ℚ_[l] K] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ)
    (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G →
    ∀ v ∈ Q.ext (invL l (S O K e)), G.app v = 0 → ∃ w ∈ P.ext (invL l (S O K e)), F.app w = v := by
  intro O K _ _ _ _ _ l e a _ _ _ ι κ μ _ _ _ _ _ _ P Q T F G hFG v hv hGv
  choose c' hc' hvc' using fun τ => ExtExact.exists_comp F G hFG hv hGv τ
  refine ⟨fun τ => P.mx τ *ᵥ c' τ, mem_tot.2 fun τ => P.mem_extc.2 ⟨_, hc' τ, rfl⟩, ?_⟩
  funext τ
  rw [Hom.app_apply]
  exact (hvc' τ).symm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPreimageInvertedPrimeBreuilOfExactTripleStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preimage_invertedPrime_breuil_of_exactTriple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NeZero e] [NormedAlgebra ℚ_[l] K] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → ∀ v ∈ Q.ext (invL l (S O K e)), G.app v = 0 → ∃ w ∈ P.ext (invL l (S O K e)), F.app w = v := by
  first | exact @GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple | exact GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple | (intros; apply GlobalTheory.BK.exists_preimage_invL_S_of_exactTriple <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfPhiModuleExactTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulVecEqZeroOfSubalgebra
namespace GlobalTheory.SubalgebraMulVecZero

theorem mulVec_frac_eq_zero {B : Type} [CommRing B] [IsDomain B] {ι κ : Type} [Fintype ι]
    (A : Matrix κ ι B) (hA : ∀ u : ι → B, A.mulVec u = 0 → u = 0)
    (v : ι → FractionRing B)
    (hv : (A.map (algebraMap B (FractionRing B))).mulVec v = 0) : v = 0 := by
  classical
  obtain ⟨⟨b, hbM⟩, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors B) Finset.univ v
  choose u hu using fun i => hb i (Finset.mem_univ i)
  have hAu : A.mulVec u = 0 := by
    funext k
    apply IsFractionRing.injective B (FractionRing B)
    rw [Pi.zero_apply, map_zero]
    have e : algebraMap B (FractionRing B) (A.mulVec u k) =
        (A.map (algebraMap B (FractionRing B))).mulVec (fun i => algebraMap B (FractionRing B) (u i)) k := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [e]
    have e2 : (fun i => algebraMap B (FractionRing B) (u i)) = b • v := funext hu
    rw [e2, Matrix.mulVec_smul, hv, smul_zero]
    rfl
  have hu0 := hA u hAu
  funext i
  have h1 := hu i
  rw [hu0, Pi.zero_apply, map_zero] at h1
  have hb0 : algebraMap B (FractionRing B) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbM
  rw [Algebra.smul_def] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left hb0

theorem exists_left_inv {K : Type} [Field K] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix κ ι K) (hA : ∀ v : ι → K, A.mulVec v = 0 → v = 0) :
    ∃ N : Matrix ι κ K, N * A = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A) (by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hA v hv)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have e : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' A) = LinearMap.toMatrix' g * A := by
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  rw [← e, hg, LinearMap.toMatrix'_id]

theorem mulVec_eq_zero_of_subalgebra {O S : Type} [CommRing O] [CommRing S] [IsDomain S]
    [Algebra O S] (B : Subalgebra O S) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix κ ι S) (hM : ∀ (i : κ) (j : ι), M i j ∈ B)
    (hinj : ∀ v : ι → S, (∀ j, v j ∈ B) → Matrix.mulVec M v = 0 → v = 0)
    (w : ι → S) (hw : Matrix.mulVec M w = 0) : w = 0 := by
  let A : Matrix κ ι B := Matrix.of fun i j => ⟨M i j, hM i j⟩
  let c : B →+* S := B.val.toRingHom
  have hc : Function.Injective c := Subtype.val_injective
  have hAM : A.map c = M := by
    ext i j
    rfl
  have hA : ∀ u : ι → B, A.mulVec u = 0 → u = 0 := by
    intro u hu
    have h1 : M.mulVec (c ∘ u) = 0 := by
      funext i
      rw [← hAM, ← RingHom.map_mulVec, hu]
      simp
    have h2 := hinj (c ∘ u) (fun j => (u j).2) h1
    funext j
    apply hc
    have := congrFun h2 j
    simpa using this
  obtain ⟨N, hN⟩ := exists_left_inv (A.map (algebraMap B (FractionRing B)))
    (mulVec_frac_eq_zero A hA)
  have hL := IsFractionRing.injective S (FractionRing S)
  let g : B →+* FractionRing S := (algebraMap S (FractionRing S)).comp c
  have hg : Function.Injective g := hL.comp hc
  let φ : FractionRing B →+* FractionRing S := IsFractionRing.lift hg
  have hmap : (A.map (algebraMap B (FractionRing B))).map φ
      = M.map (algebraMap S (FractionRing S)) := by
    ext i j
    simp only [Matrix.map_apply]
    exact IsFractionRing.lift_algebraMap hg (A i j)
  have hN' : N.map φ * M.map (algebraMap S (FractionRing S)) = 1 := by
    rw [← hmap, ← Matrix.map_mul, hN]
    exact Matrix.map_one _ (map_zero φ) (map_one φ)
  have hw' : (M.map (algebraMap S (FractionRing S))).mulVec
      ((algebraMap S (FractionRing S)) ∘ w) = 0 := by
    funext i
    rw [← RingHom.map_mulVec, hw]
    simp
  have h0 : (algebraMap S (FractionRing S)) ∘ w = 0 := by
    rw [← Matrix.one_mulVec ((algebraMap S (FractionRing S)) ∘ w), ← hN',
      ← Matrix.mulVec_mulVec, hw', Matrix.mulVec_zero]
  funext j
  apply hL
  have := congrFun h0 j
  simpa using this

end GlobalTheory.SubalgebraMulVecZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfPhiModuleExactTriple
open PowerSeries GlobalTheory.BK

open Matrix

namespace GlobalTheory.BK

theorem mulVec_eq_zero_of_subalgebra {O S : Type} [CommRing O] [CommRing S] [IsDomain S] [Algebra O S]
    (B : Subalgebra O S) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix κ ι S) (hM : ∀ i j, M i j ∈ B)
    (hinj : ∀ v : ι → S, (∀ j, v j ∈ B) → M *ᵥ v = 0 → v = 0) (w : ι → S) (hw : M *ᵥ w = 0) :
    w = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_9 h_10 h_11 h_12; revert O S h_2 h_3 h_4 h_5 B ι κ h_9 h_10 h_11 h_12 M hM hinj w hw; exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra)
  | exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra
  | exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra
  | (apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra ..)

end GlobalTheory.BK

theorem GlobalTheory.BK.IsExactTriple.injective_app : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → Function.Injective F.app := by
  intro O K _ _ _ _ _ l e a _ ι κ μ _ _ _ _ _ _ P Q T F G hex
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  funext τ
  refine mulVec_eq_zero_of_subalgebra (A O K) (F.mat τ) (F.mem τ) ?_ (w τ) ?_
  · intro v hv hMv
    have hu : Pi.single τ v ∈ P.M := mem_tot.2 fun τ' => by
      by_cases h : τ' = τ
      · subst h; simpa using (mem_vecs.2 hv)
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h0 : F.app (Pi.single τ v) = 0 := by
      funext τ'
      rw [Hom.app_apply]
      by_cases h : τ' = τ
      · subst h; simpa using hMv
      · rw [Pi.single_eq_of_ne h, Matrix.mulVec_zero]; rfl
    have := congrFun (hex.inj _ hu h0) τ
    simpa using this
  · have := congrFun hw τ
    rwa [Hom.app_apply] at this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfPhiModuleExactTripleStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_phiModule_exact_triple : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → Function.Injective F.app := by
  first | exact @GlobalTheory.BK.IsExactTriple.injective_app | exact GlobalTheory.BK.IsExactTriple.injective_app | (intros; apply GlobalTheory.BK.IsExactTriple.injective_app <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineClassFromMonodromyKernelElement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.ExtClass

theorem lift_phi_sub {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ]
    [DecidableEq μ] {η H : ℕ} {D₀ : BKDat O K l e a ι η H} {D₁ : BKDat O K l e a κ η H}
    {D₂ : BKDat O K l e a μ η H} (F : BKHom D₀ D₁) (G : BKHom D₁ D₂) (hex : IsExactTriple F.toHom G.toHom)
    {x : Vec K a κ} (hx : x ∈ D₁.Minv) (hG : G.app (D₁.phi x - x) = 0) :
    ∃ y ∈ D₀.Y, F.app y = D₁.phi x - x ∧ D₀.Mon y = 0 := by
  have hL : D₁.phi x ∈ D₁.L := D₁.phi_mem_L hx.1
  have hM : E K l e ^ η • (D₁.phi x - x) ∈ D₁.M := by
    rw [smul_sub]
    exact sub_mem (D₁.upper _ hL) (D₁.M.smul_mem (EIn l e (A O K) ^ η) hx.1)
  have hG0 : G.app (E K l e ^ η • (D₁.phi x - x)) = 0 := by rw [map_smul, hG, smul_zero]
  obtain ⟨w, hw, hFw⟩ := (hex.exact _ hM).1 hG0
  have hu : IsUnit (E K l e ^ η) := (isUnit_E l e).pow η
  set y₀ := Ezpow K l e (-(η : ℤ)) • w with hy₀def
  have hE : E K l e ^ η • y₀ = w := by
    rw [hy₀def, smul_smul, E_pow_mul_Ezpow_neg, one_smul]
  have hFy₀ : F.app y₀ = D₁.phi x - x := by
    refine (hu.smul_left_cancel).1 ?_
    rw [← map_smul, hE]
    exact hFw
  have hy₀ : y₀ ∈ D₀.EM η := by
    rw [mem_divE, hE]
    exact hw
  have hinj : ∀ v ∈ D₀.EM η, F.app v = 0 → v = 0 := fun v hv h =>
    (hu.smul_left_cancel).1 (by
      rw [smul_zero]
      exact hex.inj _ hv (by rw [map_smul, h, smul_zero]))
  have hinv2 : ∀ g, D₁.desc.act g (D₁.phi x - x) = D₁.phi x - x := fun g => by
    rw [map_sub, D₁.desc.act_phi, hx.2 g]
  refine ⟨y₀, ⟨hy₀, fun g => ?_⟩, hFy₀, ?_⟩
  · rw [← sub_eq_zero]
    refine hinj _ (sub_mem (D₀.desc.act_mem_EM g hy₀) hy₀) ?_
    rw [map_sub, F.app_act, hFy₀, hinv2, sub_self]
  · refine (GlobalTheory.T.breuilKisin_exactTriple_jumps_characters_lift O K l e a ι κ μ η H D₀ D₁ D₂ F G hex).2.2.1 ?_
    rw [map_zero, Hom.onPol_Mon, hFy₀, PhiMod.Mon_phi_sub,
      (D₁.cls_eq_zero_iff).2 (D₁.EN_mem_Man (D₁.M_le_Man hx.1)), neg_zero]

end GlobalTheory.BKGal.ExtClass

namespace GlobalTheory.BKGal.ExtClass

theorem xi_red_of_phi_eq {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PhiMod O K l e a ι) {u : Vec K a ι} (hu : P.phi u = u) : P.xi (red u) = u := by
  have := P.raises_phi.eq_zero (α := Unit) (σ := id) Function.surjective_id
    (δ := fun _ => u - P.xi (red u)) (fun _ => by rw [mem_uPow_one, map_sub, PhiMod.red_xi, sub_self])
    (fun _ => by rw [map_sub, hu, PhiMod.phi_xi, ← PhiMod.red_phi, hu]) ()
  exact (sub_eq_zero.1 this).symm


set_option maxHeartbeats 4000000 in
theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ Pk : Pack a ϖ η H T, ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ y ∈ Pk.D.Y, Pk.D.Mon y = 0 ∧ Pk.R.ClassOf y ((l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) • c) := by
  intro hBS hFB l _ a e _ _ ϖ LL _ _ Pl AI hStd N η H Sig U hN T hT Pk c hc
  have hl2 : l ≠ 2 := by
    have h1 := hN.large
    have h2 := hN.two_le
    rintro rfl
    have : 8 ≤ N ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ N ^ 3 := Nat.pow_le_pow_left h2 3
    omega
  obtain ⟨hUnit, hExt⟩ := GlobalTheory.T.extensionLattice_isCrysTameTypeWithJumps hFB l a e ϖ LL Pl AI hStd Sig U hN.zero_mem_Sig hN.zero_mem_U
  obtain ⟨Tp, f, g, v, hfg, hv, hgv, hcv, hTp⟩ := hExt T hT c hc
  obtain ⟨Pp, hPp⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFB l a e ϖ LL hl2 Pl AI hStd η H Sig U hN.range_U Tp hTp
  obtain ⟨Pu, hPu⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFB l a e ϖ LL hl2 Pl AI hStd η H Sig U hN.range_U _ hUnit
  obtain ⟨F, hF⟩ := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H T Tp Pk Pp f
  have hG' := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H Tp (unitLat (Gl l) : QLat LL) Pp Pu g
  obtain ⟨G, hG⟩ := hG'
  have hex : IsExactTriple F.toHom G.toHom :=
    GlobalTheory.T.isExactTriple_breuilKisin_of_shortExactLattices l a e ϖ LL _ _ _ Pk.D.toPhiMod Pp.D.toPhiMod Pu.D.toPhiMod T Tp (unitLat (Gl l) : QLat LL) Pk.R.I Pp.R.I Pu.R.I f g
      F.toHom G.toHom hfg hF hG
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H :=
    ⟨hN.frob_mem, hN.zero_mem_Sig, hN.card_Sig, hN.two_le, hN.range_U, hN.zero_mem_U, hN.card_U, hN.one_le,
      hN.lt, hN.large⟩
  have hK := GlobalTheory.T.cokernel_latticeMap_killed_by_prime_pow (↥(OL LL)) (↥LL.1) l e a (Fin Pp.n) (Fin Pu.n) Sig U N η H hB Pp.D Pu.D hPp
    hPu.chars_subset G hex.finiteLength
  obtain ⟨u, x, hx1, hu, hφu, hux⟩ := GlobalTheory.T.breuilKisinDescent_unitLattice_datum hBS l a e ϖ LL η H Pu
  obtain ⟨x₂, hx₂, hGx₂⟩ := hK.2.2.2.1 u.1 hu
  have hG0 : G.app (Pp.D.phi x₂ - x₂) = 0 := by
    rw [map_sub, G.toHom.app_phi, hGx₂, map_nsmul, hφu, sub_self]
  obtain ⟨y, hy, hFy, hMon⟩ := lift_phi_sub F G hex hx₂ hG0
  refine ⟨y, hy, hMon, ?_⟩
  have hFinj := GlobalTheory.T.injective_of_phiModule_exact_triple _ _ _ _ _ _ _ _ _ _ _ F.toHom G.toHom hex
  set d := red (Pp.D.phi x₂) with hd
  have hL : Pp.D.phi x₂ ∈ Pp.D.L := Pp.D.phi_mem_L hx₂.1
  have hσp : Pp.D.phi x₂ - Pp.D.xi d ∈ Pp.D.MMl := by
    refine sub_mem (Pp.D.ext_mono ((A_le_S l e).trans (le_away _ _)) hL) ?_
    rw [PhiMod.xi_apply]
    refine ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor (↥(OL LL)) (↥LL.1) l e a (Fin Pp.n) Pp.D.toPhiMod).2 _).2 ?_
    exact mem_tot.2 fun τ i => by
      rw [cst_apply]
      exact HasK.C_mem _
  have hGσ : G.app (Pp.D.phi x₂ - Pp.D.xi d) = 0 := by
    rw [map_sub, Hom.app_xi, hd, ← Hom.red_app, G.toHom.app_phi, hGx₂, map_nsmul, hφu, map_nsmul, map_nsmul,
      xi_red_of_phi_eq _ hφu, sub_self]
  obtain ⟨σ, hσ, hFσ⟩ := GlobalTheory.T.exists_preimage_invertedPrime_breuil_of_exactTriple _ _ _ _ _ _ _ _ _ _ _ F.toHom G.toHom hex _ hσp hGσ
  have hσinv : σ ∈ Pk.D.desc.inv := fun γ => hFinj (by
    rw [F.app_act, hFσ, map_sub, Pp.D.desc.act_phi, hx₂.2 γ, Descent.act_xi, hd, ← Descent.red_act,
      Pp.D.desc.act_phi, hx₂.2 γ])
  exact GlobalTheory.T.extensionClass_eq_lPow_smul_galois l a e ϖ LL η H T Tp f g hfg Pk Pp Pu F G hF hG hex hFinj u x hx1 hu hφu hux
    (GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) x₂ hx₂ hGx₂ v c hv hgv hcv σ hσ hσinv hFσ y hy hFy

end GlobalTheory.BKGal.ExtClass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineClassFromMonodromyKernelElementStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_class_from_monodromy_kernel_element : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ T : QLat LL, IsGood a ϖ Pl T Sig U → ∀ Pk : Pack a ϖ η H T, ∀ c ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, ∃ y ∈ Pk.D.Y, Pk.D.Mon y = 0 ∧ Pk.R.ClassOf y ((l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) • c) := by
  first | exact @GlobalTheory.BKGal.ExtClass.main | exact GlobalTheory.BKGal.ExtClass.main | (intros; apply GlobalTheory.BKGal.ExtClass.main <;> assumption)
end
