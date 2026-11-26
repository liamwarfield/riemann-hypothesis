module

public import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction
public import Formalism.SharpRestriction.LevelLetterCocycles.RealisedOfCoordArc

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.KillWinFromCut
namespace Formalism.MainNotions.UnusedSlot80.CutU

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

def RATCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ (A : ArcP n) (a : ZMod n) (e : ℕ) (E₀ : ℕ) (E : ℕ → ℤ), E₀ ≤ 1 →
    (∀ s < e, -(A.Hs a e s : ℤ) ≤ E s ∧ E s ≤ A.Hs a e s) →
    ∀ f : W.EE, InFr W a 1 (abelian₂ W A a e) f →
      (∀ s < e, ∃ κ : ℕ, ∃ f₁ f₂ : W.EE, lE W κ * f = f₁ + f₂ ∧
        InFr W a (ps W s ^ (E s).toNat)
          (ps W s ^ (-(E s)).toNat * ∏ t ∈ (Finset.range e).erase s, ps W t ^ A.Hs a e t) f₁ ∧
        InFr W a (W.π₀ * abelian₂ W A a e) 1 f₂) →
      (E₀ = 1 → ∃ κ : ℕ, ∃ f₁ f₂ : W.EE, lE W κ * f = f₁ + f₂ ∧
        InFr W a W.π₀ (abelian₂ W A a e) f₁ ∧ InFr W a (W.π₀ * abelian₂ W A a e) 1 f₂) →
      ∃ f₁ f₂ : W.EE, f = f₁ + f₂ ∧
        InFr W a (W.π₀ ^ E₀ * ∏ s ∈ Finset.range e, ps W s ^ (E s).toNat)
          (∏ s ∈ Finset.range e, ps W s ^ (-(E s)).toNat) f₁ ∧
        InFr W a (W.π₀ * abelian₂ W A a e) 1 f₂

def InvLevCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ (a : ZMod n) (s : ℕ) (T : Finset ℕ) (e : ℕ → ℕ), s ∉ T →
    ∀ f : W.EE, InFr W a 1 (∏ t ∈ T, ps W t ^ e t) f →
    (∃ κ : ℕ, InFr W a (ps W s) (∏ t ∈ T, ps W t ^ e t) (lE W κ * (W.γE W.gam f - f))) →
    ∃ (κ : ℕ) (x : O), InFr W a (ps W s) (∏ t ∈ T, ps W t ^ e t)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE a) * algebraMap O W.EE x)

def KillWinFromCut [IsDomain O] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W → KillerLevCore W → Formalism.MainNotions.UnusedSlot80.KL.PsStable W → W.π₀ ∈ W.AΔ → RATCore W → InvLevCore W →
    Formalism.MainNotions.UnusedSlot80.UnivF.KillWinCore W

end Core

end Formalism.MainNotions.UnusedSlot80.CutU
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CoordStepsOf
noncomputable section

namespace Formalism.MainNotions.N.Ln03

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]


variable (W) in
def EEl (i : ZMod n) : AddSubgroup W.EE where
  carrier := {ε | (letE i : LetA O n) • ε = ε ∧ ∀ δ ∈ W.DelF, W.γE δ ε = ε}
  zero_mem' := ⟨smul_zero _, fun δ _ => map_zero _⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [smul_add, ha, hb], fun δ hδ => by rw [map_add (f := _), ha' δ hδ, hb' δ hδ]⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨by rw [smul_neg, ha], fun δ hδ => by rw [map_neg, ha' δ hδ]⟩

def lc {T : LocLat G Qp LL O} {ι : Type} [Fintype ι] (b : ι → W.DD T) (c : ι → W.EE) : W.DD T :=
  ∑ j, c j • b j


variable (W) in
def LBasis (T : LocLat G Qp LL O) (i : ZMod n) {ι : Type} [Fintype ι] (b : ι → W.DD T) : Prop :=
  (∀ c : ι → W.EE, (∀ j, c j ∈ EEl W i) → lc b c ∈ DDl W T i) ∧
  (∀ c c' : ι → W.EE, (∀ j, c j ∈ EEl W i) → (∀ j, c' j ∈ EEl W i) → lc b c = lc b c' → c = c') ∧
  (∀ x ∈ DDl W T i, ∃ c : ι → W.EE, (∀ j, c j ∈ EEl W i) ∧ lc b c = x)

structure CoeffData (hR : Ring9 W) where
  M : Type
  [acg : AddCommGroup M]
  [mod : Module (PowerSeries O) M]
  κ : ZMod n → M →+ W.EE
  m₁ : M
  mem : ∀ i m, κ i m ∈ EEl W i
  surj : ∀ i, ∀ ε ∈ EEl W i, ∃ m, κ i m = ε
  inj : ∀ i, Function.Injective (κ i)
  semi : ∀ i (a : PowerSeries O) (m : M),
    κ i (a • m) = algebraMap (LetA O n) W.EE ((baseIdOf hR).d a) * κ i m
  unit : ∀ i, κ i m₁ = algebraMap (LetA O n) W.EE (letE i)

attribute [instance] CoeffData.acg CoeffData.mod

def CoeffStep (hR : Ring9 W) : Prop := Nonempty (CoeffData hR)


variable (W) in
def SplitStep : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∃ r k : ℕ, ∀ i : ZMod n, ∃ (b₁ : Fin r ⊕ Fin k → W.DD T₁) (b₂ : Fin r → W.DD T₂),
      LBasis W T₁ i b₁ ∧ LBasis W T₂ i b₂ ∧ (∀ j, W.map F (b₁ (Sum.inl j)) = b₂ j) ∧
        ∀ j, W.map F (b₁ (Sum.inr j)) = 0


variable (W) in
def UnitStep (e : W.DD W.one) : Prop := ∀ i : ZMod n, LBasis W W.one i (fun _ : Unit => e)

section Build

variable {hR : Ring9 W} (D : CoeffData hR) {T : LocLat G Qp LL O} {ι : Type} [Fintype ι]
  (b : ZMod n → ι → W.DD T) (hb : ∀ i, LBasis W T i (b i))

def toL (i : ZMod n) : (ι → D.M) →+ ↥(DDl W T i) where
  toFun c := ⟨lc (b i) (fun j => D.κ i (c j)), (hb i).1 _ (fun j => D.mem i _)⟩
  map_zero' := by
    apply Subtype.ext
    simp [lc]
  map_add' c c' := by
    apply Subtype.ext
    simp [lc, add_smul, Finset.sum_add_distrib]

theorem toL_coe (i : ZMod n) (c : ι → D.M) :
    ((toL D b hb i c : ↥(DDl W T i)) : W.DD T) = lc (b i) (fun j => D.κ i (c j)) := rfl

theorem toL_bij (i : ZMod n) : Function.Bijective (toL D b hb i) := by
  constructor
  · intro c c' h
    have h1 := congrArg Subtype.val h
    rw [toL_coe, toL_coe] at h1
    have h2 := (hb i).2.1 _ _ (fun j => D.mem i _) (fun j => D.mem i _) h1
    funext j
    exact D.inj i (congrFun h2 j)
  · rintro ⟨x, hx⟩
    obtain ⟨c, hc, hcx⟩ := (hb i).2.2 x hx
    choose m hm using fun j => D.surj i (c j) (hc j)
    refine ⟨m, Subtype.ext ?_⟩
    rw [toL_coe]
    change lc (b i) (fun j => D.κ i (m j)) = x
    rw [← hcx]
    congr 1
    funext j
    exact hm j

def coordOf : Coord W (baseIdOf hR) T where
  V := ι → D.M
  θ i := AddEquiv.ofBijective (toL D b hb i) (toL_bij D b hb i)
  θ_smul i a c := by
    change lc (b i) (fun j => D.κ i ((a • c) j)) = (baseIdOf hR).d a • lc (b i) (fun j => D.κ i (c j))
    simp only [lc, Pi.smul_apply, D.semi, Finset.smul_sum, mul_smul, algebraMap_smul]

end Build

theorem coordSteps_of (hR : Ring9 W) (e : W.DD W.one) (hK : CoeffStep hR) (hS : SplitStep W)
    (hU : UnitStep W e) : CoordSteps hR e := by
  intro T₁ T₂ F hc₁ hc₂ hon
  obtain ⟨D⟩ := hK
  obtain ⟨r, k, hb⟩ := hS T₁ T₂ F hc₁ hc₂ hon
  choose b₁ b₂ h₁ h₂ hin hout using hb
  refine ⟨coordOf D b₁ h₁, coordOf D b₂ h₂,
    coordOf (ι := Unit) D (fun (_ : ZMod n) (_ : Unit) => e) (fun i => hU i),
    { f := LinearMap.funLeft (PowerSeries O) D.M Sum.inl
      coord_hom_map_trace := fun i c => ?_
      crys := hc₁.2.2.2
      crys' := hc₂.2.2.2 }, fun _ => D.m₁, fun i => ?_⟩
  · change ∑ j, D.κ i (c (Sum.inl j)) • b₂ i j = W.map F (∑ j, D.κ i (c j) • b₁ i j)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Fintype.sum_sum_type]
    simp only [map_smul, hin, hout, smul_zero, Finset.sum_const_zero, add_zero]
  · change ∑ _u : Unit, D.κ i D.m₁ • e = (letE i : LetA O n) • e
    rw [Fintype.sum_unique, D.unit, algebraMap_smul]

end Formalism.MainNotions.N.Ln03
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.At0HomApply
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

def at0Hom (W : LocWach PD LL O v n) (hz : PowerSeries.constantCoeff W.π₀₁ = 0) :
    PowerSeries O →+* LetA O n where
  toFun := Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W
  map_one' := by
    have := Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_C W (1 : O)
    rw [map_one, map_one] at this
    exact this
  map_mul' := Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_mul W hz
  map_zero' := by
    have := Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_C W (0 : O)
    rw [map_zero, map_zero] at this
    exact this
  map_add' := Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evaluation_add W hz

theorem at0Hom_apply (W : LocWach PD LL O v n) (hz : PowerSeries.constantCoeff W.π₀₁ = 0) (f : PowerSeries O) :
    at0Hom W hz f = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W f := rfl

theorem gCoord_holds (W : LocWach PD LL O v n) : GCoordProp W := by
  intro T i h c r e e' he P Z hP hz hqpu k hg hgDL a ha l
  classical
  have hqp : Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) = Formalism.MainNotions.LiftingTheory.qp W := by
    rw [Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evaluation_add W hz, Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_X_eq_pi0 W hz, Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.evalZero_C, map_natCast]
    rfl
  set x := Formalism.MainNotions.LiftingTheory.qp W ^ c • Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE W T h c e' Z k with hx
  have hxN : x ∈ W.N T := (W.N T).smul_mem _ hg
  have hxDL : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x := by
    refine ⟨by rw [hx, smul_comm, hgDL.1], fun δ hδ => ?_⟩
    rw [hx, Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA, map_pow,
      Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.qp_mem W (Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.uniformizer_mem_delta_invariants W) δ hδ, hgDL.2 δ hδ]

  have e1 : x = ∑ l, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W ((PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ c * a l) • e l := by
    rw [hx, ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul]
    congr 1
    rw [show Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W ((PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ c * a l) =
      at0Hom W hz ((PowerSeries.X + PowerSeries.C ((PD.p : ℕ) : O)) ^ c * a l) from rfl, map_mul, map_pow,
      at0Hom_apply, at0Hom_apply, hqp]

  have hcancel : x = Formalism.MainNotions.LiftingTheory.qp W ^ h • Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.ftE W T e' Z k := by
    rw [hx, Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.gE, ← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ c), smul_smul, map_pow,
      ← mul_pow, Ring.mul_inverse_cancel _ hqpu, one_pow, one_smul]
  have e2 : x = ∑ l, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W ((P * Z) l k) • e l := by
    rw [hcancel, Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.ftE, Finset.smul_sum]
    simp only [pow_one]
    have : ∀ m₁, Formalism.MainNotions.LiftingTheory.qp W ^ h • (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (Z m₁ k) • W.φD T (e' m₁)) =
        ∑ l, (Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (Z m₁ k) * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (P l m₁)) • e l := by
      intro m₁
      rw [smul_comm, hP m₁, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_smul, Matrix.mul_apply, ← at0Hom_apply W hz, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [map_mul, at0Hom_apply, at0Hom_apply, mul_comm]
  have huniq := (he.2 x hxN hxDL).unique e1.symm.symm e2
  exact congrFun huniq l

end Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CrtFamDet
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem crt_fam {ι : Type} [DecidableEq ι] (x₀ : LetA O n) (x : ι → LetA O n) (hx₀ : x₀ ∈ W.AΔ)
    (hx : ∀ i, x i ∈ W.AΔ) (s : Finset ι) (h0 : ∀ i ∈ s, Cop W x₀ (x i))
    (hp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Cop W (x i) (x j)) :
    ∃ κ : ℕ, ∃ r₀ ∈ W.AΔ, ∃ R : ι → LetA O n, (∀ i ∈ s, R i ∈ W.AΔ) ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ = (∏ i ∈ s, x i) * r₀ + ∑ i ∈ s, x₀ * (∏ j ∈ s.erase i, x j) * R i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, W.AΔ.one_mem, 0, by simp, by simp⟩
  | insert a s ha ih =>
    obtain ⟨κ, r₀, hr₀, R, hR, hsum⟩ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij => hp i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    have hQ : Cop W (x a) (x₀ * ∏ i ∈ s, x i) :=
      cop_symm W (cop_mul W hx₀ (hx a) (h0 a (Finset.mem_insert_self a s))
        (cop_prod W s x hx (hx a) fun i hi => hp i (Finset.mem_insert_of_mem hi) a
          (Finset.mem_insert_self a s) (fun h => ha (h ▸ hi))))
    obtain ⟨m, r, hr, t, ht, hm⟩ := hQ
    refine ⟨κ + m, r₀ * r, W.AΔ.mul_mem hr₀ hr,
      fun i => if i = a then Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ * t else R i * r, ?_, ?_⟩
    · intro i hi
      by_cases hia : i = a
      · simp only [hia, if_true]; exact W.AΔ.mul_mem (lA_mem W κ) ht
      · simp only [hia, if_false]
        exact W.AΔ.mul_mem (hR i ((Finset.mem_insert.1 hi).resolve_left hia)) hr
    · rw [Finset.sum_insert ha]
      dsimp only
      rw [if_pos rfl, Finset.erase_insert ha, Finset.prod_insert ha]
      have hs : ∑ i ∈ s, x₀ * (∏ j ∈ (insert a s).erase i, x j) *
          (if i = a then Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ * t else R i * r) =
          (∑ i ∈ s, x₀ * (∏ j ∈ s.erase i, x j) * R i) * r * x a := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        rw [if_neg hia, Finset.erase_insert_of_ne (Ne.symm hia),
          Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
        ring
      rw [hs, pow_add]
      linear_combination (r * x a) * hsum + Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ * hm

variable [IsDomain O]

theorem cop_pi_ps (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (s : ℕ) : Cop W W.π₀ (Formalism.MainNotions.ArcLiftingSetup.ps W s) := by
  obtain ⟨a, ha⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_π₀ (W := W) hR s
  have haΔ : a ∈ W.AΔ := by
    refine Formalism.MainNotions.UnusedSlot80.ToolsR.cancel_AΔ hR.1 (fun _ => Formalism.MainNotions.UnusedSlot80.ToolsR.π₀₁_ne hR) ?_
    rw [← ha]; exact Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_AΔ s hR.1
  have e1 : Formalism.MainNotions.ArcLiftingSetup.ps W s - Formalism.MainNotions.ArcLiftingSetup.lA W = (W.φA ^ s) W.π₀ :=
    Formalism.MainNotions.UnusedSlot80.ToolsR.pS_sub s
  refine ⟨1, -a, W.AΔ.neg_mem haΔ, 1, W.AΔ.one_mem, ?_⟩
  linear_combination (-1 : LetA O n) * e1 - ha

variable [NeZero n]

theorem cop_ps_ps (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (s t : ℕ) (hst : s ≠ t) :
    Cop W (Formalism.MainNotions.ArcLiftingSetup.ps W s) (Formalism.MainNotions.ArcLiftingSetup.ps W t) := by
  obtain ⟨κ, a, ha, b, hb, e⟩ := Formalism.MainNotions.UnusedSlot80.KF.psCoprime_of W hR s t hst
  exact ⟨κ, a, ha, b, hb, e⟩

theorem crtLev (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (e : ℕ) (N : ℕ → ℕ) :
    ∃ κ : ℕ, ∃ u₀ ∈ W.AΔ, ∃ u : ℕ → LetA O n, (∀ s < e, u s ∈ W.AΔ) ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ = u₀ + ∑ s ∈ Finset.range e, u s ∧
      (∃ r ∈ W.AΔ, u₀ = (∏ t ∈ Finset.range e, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t) * r) ∧
      ∀ s < e, ∃ r ∈ W.AΔ,
        u s = W.π₀ * (∏ t ∈ (Finset.range e).erase s, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t) * r := by
  have hps : ∀ t, Formalism.MainNotions.ArcLiftingSetup.ps W t ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hR.1
  have hx : ∀ t, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t ∈ W.AΔ := fun t => W.AΔ.pow_mem (hps t) _
  obtain ⟨κ, r₀, hr₀, R, hRm, hsum⟩ := crt_fam W W.π₀ (fun t => Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t) hR.1 hx
    (Finset.range e)
    (fun t _ => cop_symm W (cop_pow W (hps t) hR.1 (cop_symm W (cop_pi_ps W hR t)) (N t)))
    (fun i _ j _ hij => cop_pow W (hps i) (hx j)
      (cop_symm W (cop_pow W (hps j) (hps i) (cop_ps_ps W hR j i (Ne.symm hij)) (N j))) (N i))
  refine ⟨κ, _, W.AΔ.mul_mem (W.AΔ.prod_mem fun t _ => hx t) hr₀,
    fun s => W.π₀ * (∏ t ∈ (Finset.range e).erase s, Formalism.MainNotions.ArcLiftingSetup.ps W t ^ N t) * R s,
    fun s hs => W.AΔ.mul_mem (W.AΔ.mul_mem hR.1 (W.AΔ.prod_mem fun t _ => hx t))
      (hRm s (Finset.mem_range.2 hs)), by dsimp only; exact hsum, ⟨r₀, hr₀, rfl⟩,
    fun s hs => ⟨R s, hRm s (Finset.mem_range.2 hs), rfl⟩⟩

end Formalism.MainNotions.UnusedSlot80.LevC
end
end
