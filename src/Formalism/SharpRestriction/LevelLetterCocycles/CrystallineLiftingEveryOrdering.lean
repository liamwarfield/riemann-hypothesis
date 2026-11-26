module

public import Formalism.SharpRestriction.LevelLetterCocycles.ThmELiftAtOf
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.MatOfEquiv
public import Formalism.SharpRestriction.LevelLetterCocycles.RealExtOfExact

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusCocycleOfRhoData
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {I : BaseId W} {T₁ T₂ : LocLat G Qp LL O}

def mapZ (F : LatHom T₁.L T₂.L) : ↥(W.wachCocyclesDelta T₁) →ₗ[O] ↥(W.wachCocyclesDelta T₂) :=
  (((W.map F).restrictScalars O).prodMap ((W.map F).restrictScalars O)).restrict
    (fun w hw => map_mem_Z1DΔ F ⟨w, hw⟩)

theorem mapZ_coe (F : LatHom T₁.L T₂.L) (w : ↥(W.wachCocyclesDelta T₁)) :
    (mapZ F w : W.DD T₂ × W.DD T₂) =
      (W.map F (w : W.DD T₁ × W.DD T₁).1, W.map F (w : W.DD T₁ × W.DD T₁).2) := rfl

def ZfDN (F : LatHom T₁.L T₂.L) : Submodule O (W.DD T₁ × W.DD T₁) :=
  ((latticeFiniteCohomology PD T₁.L).comap (W.clK T₁) ⊓
    LinearMap.eqLocus (F.H1map.comp (W.clK T₁)) ((W.clK T₂).comp (mapZ F))).map (W.wachCocyclesDelta T₁).subtype

def ZfN (C₁ : Coord W I T₁) (F : LatHom T₁.L T₂.L) :
    AddSubgroup ((ZMod n → C₁.V) × (ZMod n → C₁.V)) :=
  (ZfDN F).toAddSubgroup.comap (totP C₁)

theorem mem_ZfN (C₁ : Coord W I T₁) (F : LatHom T₁.L T₂.L)
    (κ : (ZMod n → C₁.V) × (ZMod n → C₁.V)) :
    κ ∈ ZfN C₁ F ↔ ∃ w : ↥(W.wachCocyclesDelta T₁), (W.clK T₁ w ∈ latticeFiniteCohomology PD T₁.L ∧
      F.H1map (W.clK T₁ w) = W.clK T₂ (mapZ F w)) ∧
      (w : W.DD T₁ × W.DD T₁) = (tot C₁ κ.1, tot C₁ κ.2) := by
  exact Iff.rfl

theorem ZfN_smul (C₁ : Coord W I T₁) (F : LatHom T₁.L T₂.L) (m : O)
    (κ : (ZMod n → C₁.V) × (ZMod n → C₁.V)) (h : κ ∈ ZfN C₁ F) :
    (PowerSeries.C m • κ.1, PowerSeries.C m • κ.2) ∈ ZfN C₁ F := by
  show totP C₁ (PowerSeries.C m • κ.1, PowerSeries.C m • κ.2) ∈ ZfDN F
  have e : totP C₁ (PowerSeries.C m • κ.1, PowerSeries.C m • κ.2) = m • totP C₁ κ := by
    show (tot C₁ (PowerSeries.C m • κ.1), tot C₁ (PowerSeries.C m • κ.2)) =
      m • (tot C₁ κ.1, tot C₁ κ.2)
    rw [tot_smulC, tot_smulC]
    rfl
  rw [e]
  exact (ZfDN F).smul_mem m h

theorem liftF_ofN {F : LatHom T₁.L T₂.L} {C₁ : Coord W I T₁} {C₂ : Coord W I T₂}
    (h : CoordHom C₁ C₂ F) (hs : W.s = 1) (hp : PD.p ≠ 2) (herr : Formalism.MainNotions.DeltaInvariantLattices.p2aK W T₂) (e : ℕ)
    (key : ∀ κ ∈ Zf C₂, ∃ κ₁ ∈ ZfN C₁ F,
      (latOf C₂).IsCobound (I.Bs.lc ^ e • κ.1 - fun i => (latHomOf h).f (κ₁.1 i))
        (I.Bs.lc ^ e • κ.2 - fun i => (latHomOf h).f (κ₁.2 i))) :
    F.LiftF PD e := by
  intro c hc
  have hcZ : c ∈ latticeCocycles T₂.L := hc.1
  have hcls : (Submodule.Quotient.mk (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) : LatticeCohomology T₂.L) ∈ latticeFiniteCohomology PD T₂.L :=
    ⟨⟨c, hcZ⟩, hc, rfl⟩
  obtain ⟨hsurj, hker⟩ := herr hs hp
  obtain ⟨w, hw⟩ : ∃ w : ↥(W.wachCocyclesDelta T₂), W.clK T₂ w =
      Submodule.Quotient.mk (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) := hsurj _
  obtain ⟨-, hwa, hwb⟩ := (mem_Z1DΔ (w : W.DD T₂ × W.DD T₂).1 (w : W.DD T₂ × W.DD T₂).2).1 w.2
  obtain ⟨y, hy⟩ := tot_surj C₂ _ hwa
  obtain ⟨z, hz⟩ := tot_surj C₂ _ hwb
  have hκ : (y, z) ∈ Zf C₂ := (mem_Zf C₂ _).2 ⟨w, hw ▸ hcls, Prod.ext hy.symm hz.symm⟩
  obtain ⟨κ₁, hκ₁, m, hm1, hm2⟩ := key _ hκ
  obtain ⟨w₁, ⟨hw₁f, hnat⟩, hw₁⟩ := (mem_ZfN C₁ F _).1 hκ₁
  have hzero : W.clK T₂ ((((PD.p : ℕ) : O) ^ e) • w - mapZ F w₁) = 0 := by
    refine (hker _).2 ⟨tot C₂ m, fun δ hδ => tot_Δ C₂ m δ hδ, ?_⟩
    have e1 := congrArg (tot C₂) hm1
    have e2 := congrArg (tot C₂) hm2
    rw [tot_sub, lc_pow, tot_smulC, tot_map, tot_dφ] at e1
    rw [tot_sub, lc_pow, tot_smulC, tot_map, tot_dγ] at e2
    have a1 : tot C₁ κ₁.1 = (w₁ : W.DD T₁ × W.DD T₁).1 := by rw [hw₁]
    have a2 : tot C₁ κ₁.2 = (w₁ : W.DD T₁ × W.DD T₁).2 := by rw [hw₁]
    rw [a1] at e1
    rw [a2] at e2
    simp only at e1 e2
    rw [hy] at e1
    rw [hz] at e2
    exact Prod.ext e1 e2
  have e3 : W.clK T₂ ((((PD.p : ℕ) : O) ^ e) • w - mapZ F w₁) =
      (((PD.p : ℕ) : O) ^ e) • W.clK T₂ w - W.clK T₂ (mapZ F w₁) :=
    ((W.clK T₂).map_sub ((((PD.p : ℕ) : O) ^ e) • w) (mapZ F w₁)).trans
      (congrArg (· - W.clK T₂ (mapZ F w₁)) ((W.clK T₂).map_smul _ w))
  have hz2 : (((PD.p : ℕ) : O) ^ e) • (Submodule.Quotient.mk (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L)) : LatticeCohomology T₂.L) =
      F.H1map (W.clK T₁ w₁) := by
    rw [hnat, ← hw]
    exact sub_eq_zero.1 (e3.symm.trans hzero)
  obtain ⟨c₁, hc₁, hc₁e⟩ := hw₁f
  rw [← hc₁e] at hz2
  have hq : (Submodule.Quotient.mk ((((PD.p : ℕ) : O) ^ e) • (⟨c, hcZ⟩ : ↥(latticeCocycles T₂.L))) : LatticeCohomology T₂.L) =
      Submodule.Quotient.mk (⟨F.post c₁, F.post_Z1T _ c₁.2⟩ : ↥(latticeCocycles T₂.L)) := hz2
  have hB := (Submodule.Quotient.eq _).1 hq
  have hB' : (((PD.p : ℕ) : O) ^ e) • c - F.post c₁ ∈ latticeCoboundaries T₂.L := hB
  have : (((PD.p : ℕ) : O) ^ e) • c = F.post c₁ + ((((PD.p : ℕ) : O) ^ e) • c - F.post c₁) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hc₁) hB'

theorem map_NΔ (F : LatHom T₁.L T₂.L) (h₁ : IsCrys PD T₁.ρ) (h₂ : IsCrys PD T₂.ρ) {x : W.DD T₁}
    (hx : x ∈ W.NΔ T₁) : W.map F x ∈ W.NΔ T₂ := by
  unfold Formalism.BasicNotions.LocWach.NΔ at hx ⊢
  obtain ⟨hN, hΔ⟩ := hx
  refine ⟨W.map_N F h₁ h₂ _ hN, fun δ hδ => ?_⟩
  rw [← W.map_γ, hΔ δ hδ]

theorem map_mulSet (F : LatHom T₁.L T₂.L) (h₁ : IsCrys PD T₁.ρ) (h₂ : IsCrys PD T₂.ρ) (a : LetA O n) {x : W.DD T₁}
    (hx : x ∈ mulSet W T₁ a (W.NΔ T₁)) : W.map F x ∈ mulSet W T₂ a (W.NΔ T₂) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨W.map F y, map_NΔ F h₁ h₂ hy, map_smulA W F a y⟩

theorem frobenius_cocycle_map (F : LatHom T₁.L T₂.L) (h₁ : IsCrys PD T₁.ρ) (h₂ : IsCrys PD T₂.ρ) (M : ℕ) (c : ZMod n) (x : ↥(W.wachCocyclesDelta T₁))
    (hx : HerrCocycleAtLetter W T₁ M c x) : HerrCocycleAtLetter W T₂ M c (mapZ F x) := by
  obtain ⟨h1, h2, h3⟩ := hx
  unfold HerrCocycleAtLetter
  simp only [mapZ_coe]
  refine ⟨?_, ?_, ?_⟩
  · unfold InLetter at h1 ⊢
    rw [← map_smulA W F, h1]
  · rw [← W.map_γ, ← map_sub]
    exact map_mulSet F h₁ h₂ _ h2
  · exact map_mulSet F h₁ h₂ _ h3

theorem frobenius_cocycle_of_rho_data {T : LocLat G Qp LL O} (hF1 : F1 W) (hcr : IsCrys PD T.ρ) (hh M : ℕ)
    (hJ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T.ρ τ (Set.Icc (-(hh : ℤ)) hh))
    (hM : hh < (PD.p - 1) * M) (C : Coord W I T) (c : ZMod n) (w : C.V) (j g sig : ℕ)
    (y z : ZMod n → C.V) (hρ : (latOf C).IsRho c j M g sig w y z)
    (hZ : (tot C y, tot C z) ∈ W.wachCocyclesDelta T) : HerrCocycleAtLetter W T M (c + (j : ZMod n)) ⟨_, hZ⟩ := by
  obtain ⟨τ, -, hy, -, hz⟩ := hρ
  have hzM := tot_sm C M z hz
  refine ⟨?_, ?_, hzM⟩
  · change (letE (c + (j : ZMod n)) : LetA O n) • tot C y = tot C y
    rw [hy, tot_single]
    exact C.t_letter _ _
  · change W.γD T W.gamK (tot C y) - tot C y ∈ mulSet W T (W.π₀ ^ M) (W.NΔ T)
    rw [((mem_Z1DΔ _ _).1 hZ).1]
    obtain ⟨x, hx, hxz⟩ := hzM
    obtain ⟨x', hx', hφ⟩ := ((hF1 hh M hM).1 T hcr hJ).1 x hx
    refine ⟨I.d I.Bs.q • x' - x, (W.NΔ T).sub_mem (d_smul_NΔ _ hx') hx, ?_⟩
    rw [hxz, hφ, smul_sub, I.d_q, mul_smul]

theorem rho_fieldN (hF1 : F1 W) (hF2 : F2 W) (F : LatHom T₁.L T₂.L) (hcr₁ : IsCrys PD T₁.ρ)
    (hcr₂ : IsCrys PD T₂.ρ) (hh : ℕ)
    (hJ₁ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ (Set.Icc (-(hh : ℤ)) hh))
    (hJ₂ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₂.ρ τ (Set.Icc (-(hh : ℤ)) hh)) (hp : 2 ≤ PD.p)
    (C : Coord W I T₁) (h5 : ∀ i, (latOf C).P5M i hh) (Cu : Formalism.ExponentWindows.E.Cuts n) (H : ZMod n → ℕ → ℕ)
    (j g sig : ℕ) :
    ∀ c ∈ Cu.cuts, ∀ w, (latOf C).Wc Cu (Formalism.ExponentWindows.E.LamOf I.Bs Cu H) c w →
      ∀ y z, (latOf C).IsRho c j (Formalism.ExponentWindows.E.parM I.Bs.ℓ hh g) g sig w y z → (y, z) ∈ ZfN C F := by
  intro c hc w hw y z hρ
  have hM : hh < (PD.p - 1) * Formalism.ExponentWindows.E.parM I.Bs.ℓ hh g := by
    rw [Formalism.ExponentWindows.E.parM, I.ℓ_eq]
    have := Nat.lt_mul_div_succ (hh + 2 * g) (show 0 < PD.p - 1 by omega)
    omega
  obtain ⟨x, hxf, hx⟩ := (mem_Zf C _).1 (rho_field hF1 hF2 hcr₁ hh hJ₁ hp C h5 Cu H j g sig c hc w hw y z hρ)
  have hZ : (tot C y, tot C z) ∈ W.wachCocyclesDelta T₁ := hx ▸ x.2
  have hxe : x = ⟨_, hZ⟩ := Subtype.ext hx
  have hcoc := frobenius_cocycle_of_rho_data hF1 hcr₁ hh _ hJ₁ hM C c w j g sig y z hρ hZ
  rw [← hxe] at hcoc
  refine (mem_ZfN C F _).2 ⟨x, ⟨hxf, ?_⟩, hx⟩
  exact ((hF1 hh _ hM).2 T₁ T₂ F hcr₁ hcr₂ hJ₁ hJ₂ (c + (j : ZMod n)) x (mapZ F x) hcoc
    (frobenius_cocycle_map F hcr₁ hcr₂ _ _ x hcoc) rfl).symm

end Formalism.MainNotions.WachCoordinates.Br
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.FinrankEqOneOfBijective
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

theorem wprime_mono {O : Type} [CommRing O] {Bs : Formalism.ExponentWindows.E.Base O} {n : ℕ} {V₁ V₂ : Type}
    [AddCommGroup V₁] [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂]
    {L₁ : Formalism.ExponentWindows.E.Lat Bs n V₁} {L₂ : Formalism.ExponentWindows.E.Lat Bs n V₂} (h : Formalism.ExponentWindows.E.LatHom L₁ L₂)
    {c : ZMod n} {r r' : ℕ} (hr : h.WPrime c r) (hle : r ≤ r') : h.WPrime c r' := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hr x hx
  refine ⟨Bs.lc ^ (r' - r) • y, (L₁.N c).smul_mem _ hy, ?_⟩
  rw [map_smul, hxy, smul_smul, ← pow_add, Nat.sub_add_cancel hle]

theorem hmax_eq (n : ℕ) [NeZero n] (Mi hi : ZMod n → ℕ) :
    Formalism.MainNotions.LiftingTheory.Hmax n Mi hi = Hmax n (Mi + hi) := by
  unfold Formalism.MainNotions.LiftingTheory.Hmax Hmax
  apply le_antisymm
  · refine Finset.sup_le fun k _ => ?_
    exact Finset.le_sup (f := Mi + hi) (Finset.mem_univ (k : ZMod n))
  · refine Finset.sup_le fun i _ => ?_
    have h1 : ZMod.val i ∈ Finset.range n := Finset.mem_range.2 (ZMod.val_lt i)
    have h2 := Finset.le_sup (f := fun k : ℕ => Mi (k : ZMod n) + hi (k : ZMod n)) h1
    simpa [ZMod.natCast_zmod_val] using h2

theorem cH_eq (l n : ℕ) [NeZero n] (Mi hi : ZMod n → ℕ) :
    Formalism.MainNotions.LiftingTheory.cH l (Formalism.MainNotions.LiftingTheory.Hmax n Mi hi) = ccPar l (Hmax n (Mi + hi)) := by
  rw [hmax_eq]
  rfl

theorem le_floor_add (l r s c Hm : ℕ) (sb : ℝ) (h1 : (r : ℝ) ≤ (s : ℝ) * l / ((l : ℝ) - 1) ^ 2 + c)
    (h2 : s ≤ Hm) (h3 : (s : ℝ) ≤ sb) :
    r ≤ ⌊min (⌊sb⌋₊ : ℝ) (Hm : ℝ) * l / ((l : ℝ) - 1) ^ 2⌋₊ + c := by
  have hs1 : (s : ℝ) ≤ (⌊sb⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor h3
  have hs2 : (s : ℝ) ≤ (Hm : ℝ) := by exact_mod_cast h2
  have hmin : (s : ℝ) ≤ min (⌊sb⌋₊ : ℝ) (Hm : ℝ) := le_min hs1 hs2
  have hq : 0 ≤ (l : ℝ) / ((l : ℝ) - 1) ^ 2 := by positivity
  have h4 : (s : ℝ) * l / ((l : ℝ) - 1) ^ 2 ≤ min (⌊sb⌋₊ : ℝ) (Hm : ℝ) * l / ((l : ℝ) - 1) ^ 2 := by
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right hmin hq
  by_cases hrc : r ≤ c
  · omega
  · have h5 : r - c ≤ ⌊min (⌊sb⌋₊ : ℝ) (Hm : ℝ) * l / ((l : ℝ) - 1) ^ 2⌋₊ := by
      apply Nat.le_floor
      rw [Nat.cast_sub (by omega : c ≤ r)]
      linarith
    omega

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {I : BaseId W} {T₁ T₂ : LocLat G Qp LL O}

theorem X_eq_letπ (hs : W.s = 1) : W.X = letπ := by
  rw [LocWach.X, hs]
  rfl

theorem sI_le_Hmax (hs : W.s = 1) (hX : Formalism.MainNotions.LiftingTheory.coreWX W) (F : LatHom T₁.L T₂.L)
    (Mi hi : ZMod n → ℕ) (hF : Formalism.MainNotions.LiftingTheory.Sur W F) (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi) (i : ZMod n) :
    Formalism.MainNotions.LiftingTheory.sI W F i ≤ Formalism.MainNotions.LiftingTheory.Hmax n Mi hi := by
  have h := hX T₁ T₂ F Mi hi hF hJ i
  rw [X_eq_letπ hs] at h
  exact Nat.sInf_le h

theorem rI_le_rF {Cc : ℝ} (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hR : Formalism.MainNotions.LiftingTheory.coreWR W Cc)
    (hS : Formalism.MainNotions.LiftingTheory.coreWX W) (F : LatHom T₁.L T₂.L) (Mi hi : ZMod n → ℕ)
    (hF : Formalism.MainNotions.LiftingTheory.Sur W F) (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi) (i : ZMod n) :
    Formalism.MainNotions.LiftingTheory.rI W F i ≤ rF PD.p n (Mi + hi) i := by
  obtain ⟨h1, -, h3, -⟩ := hR hA T₁ T₂ F Mi hi hF hJ i
  have h4 := sI_le_Hmax hA.2.1 hS F Mi hi hF hJ i
  rw [cH_eq] at h1 h3
  rw [hmax_eq] at h4
  unfold rF
  refine le_floor_add PD.p _ (Formalism.MainNotions.LiftingTheory.sI W F i) _ _ _ h3 h4 ?_
  refine le_of_le_of_eq h1 ?_
  unfold sBd
  refine tsum_congr fun a => ?_
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
  rfl

theorem DelF_mul {δ δ' : W.Gam} (h : δ ∈ W.DelF) (h' : δ' ∈ W.DelF) : δ * δ' ∈ W.DelF := by
  obtain ⟨k, hk, e⟩ := (W.DelF_def δ).1 h
  obtain ⟨k', hk', e'⟩ := (W.DelF_def δ').1 h'
  refine (W.DelF_def _).2 ⟨k * k', Nat.mul_pos hk hk', ?_⟩
  rw [mul_pow, pow_mul, e, one_pow, mul_comm k k', pow_mul, e', one_pow, one_mul]

theorem DelF_inv {δ : W.Gam} (h : δ ∈ W.DelF) : δ⁻¹ ∈ W.DelF := by
  obtain ⟨k, hk, e⟩ := (W.DelF_def δ).1 h
  exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, e, inv_one]⟩

def trΔ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T) : W.DD T :=
  ∑ δ ∈ W.DelF, W.γD T δ x

theorem trΔ_inv (T : LocLat G Qp LL O) (x : W.DD T) (δ' : W.Gam) (h' : δ' ∈ W.DelF) :
    W.γD T δ' (trΔ W T x) = trΔ W T x := by
  unfold trΔ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_bij' (fun δ _ => δ' * δ) (fun δ _ => δ'⁻¹ * δ) ?_ ?_ ?_ ?_ ?_
  · intro δ hδ; exact DelF_mul h' hδ
  · intro δ hδ; exact DelF_mul (DelF_inv h') hδ
  · intro δ _; simp
  · intro δ _; simp
  · intro δ _; rw [W.γD_mul]

theorem trΔ_mem_N (T : LocLat G Qp LL O) (x : W.DD T) (hx : x ∈ W.N T) : trΔ W T x ∈ W.N T :=
  (W.N T).sum_mem fun δ _ => W.N_Γ T δ x hx

theorem trΔ_letter (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T)
    (hx : (letE i : LetA O n) • x = x) : (letE i : LetA O n) • trΔ W T x = trΔ W T x := by
  unfold trΔ
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  conv_lhs => rw [← γA_letE W δ i, ← γD_smulA, hx]

theorem trΔ_map (F : LatHom T₁.L T₂.L) (x : W.DD T₁) :
    W.map F (trΔ W T₁ x) = trΔ W T₂ (W.map F x) := by
  unfold trΔ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun δ _ => W.map_γ F δ x

theorem trΔ_fixed (T : LocLat G Qp LL O) (x : W.DD T) (hx : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    trΔ W T x = ((W.DelF.card : ℕ) : O) • x := by
  rw [trΔ, Finset.sum_congr rfl hx, Finset.sum_const, Nat.cast_smul_eq_nsmul]

theorem lp_smul (T : LocLat G Qp LL O) (r : ℕ) (x : W.DD T) :
    Formalism.MainNotions.LiftingTheory.lp W r • x = (((PD.p : ℕ) : O) ^ r) • x := by
  rw [← algebraMap_smul (LetA O n) ((((PD.p : ℕ) : O) ^ r)) x, map_pow, map_natCast]
  rfl

theorem map_smulO (F : LatHom T₁.L T₂.L) (m : O) (x : W.DD T₁) : W.map F (m • x) = m • W.map F x := by
  rw [← algebraMap_smul (LetA O n) m x, map_smulA, algebraMap_smul]

theorem wprime_of_kills {F : LatHom T₁.L T₂.L} {C₁ : Coord W I T₁} {C₂ : Coord W I T₂}
    (h : CoordHom C₁ C₂ F) (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) (c : ZMod n) (r : ℕ)
    (hk : Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W r)) : (latHomOf h).WPrime c r := by
  intro x hx
  obtain ⟨u, hu⟩ := hΔ
  have hxN : C₂.t c x ∈ W.N T₂ := hx
  have hxl : C₂.t c x ∈ W.Nl T₂ c := ⟨C₂.t c x, hxN, C₂.t_letter c x⟩
  obtain ⟨Y, hY, hYx⟩ := hk _ hxl (fun δ hδ => C₂.t_Δ c x δ hδ)
  obtain ⟨Y', hY', rfl⟩ := hY
  have hYN : (letE c : LetA O n) • Y' ∈ W.N T₁ := (W.N T₁).smul_mem _ hY'
  have hYl : (letE c : LetA O n) • ((letE c : LetA O n) • Y') = (letE c : LetA O n) • Y' := by
    rw [smul_smul, letE_mul_self]
  have hmap : W.map F ((letE c : LetA O n) • Y') = (((PD.p : ℕ) : O) ^ r) • C₂.t c x := by
    rw [← lp_smul]
    exact hYx

  obtain ⟨y, hy⟩ := C₁.t_surj c (((u⁻¹ : Oˣ) : O) • trΔ W T₁ ((letE c : LetA O n) • Y'))
    (by rw [smul_comm, trΔ_letter T₁ c _ hYl])
    (fun δ hδ => by rw [map_smul, trΔ_inv T₁ _ δ hδ])
  refine ⟨y, ?_, ?_⟩
  · rw [mem_N, hy, ← algebraMap_smul (LetA O n)]
    exact (W.N T₁).smul_mem _ (trΔ_mem_N T₁ _ hYN)
  · apply C₂.t_inj c
    change C₂.t c (h.f y) = _
    rw [h.coord_hom_map_trace, hy, map_smulO, trΔ_map, hmap, C₂.t_smul, lc_pow, I.d_C, algebraMap_smul,
      trΔ_fixed T₂ _ (fun δ hδ => by rw [map_smul, C₂.t_Δ c x δ hδ]), smul_smul, ← hu,
      Units.inv_mul, one_smul]

theorem wprime_of {Cc : ℝ} (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hR : Formalism.MainNotions.LiftingTheory.coreWR W Cc)
    (hS : Formalism.MainNotions.LiftingTheory.coreWX W) {F : LatHom T₁.L T₂.L} {C₁ : Coord W I T₁} {C₂ : Coord W I T₂}
    (h : CoordHom C₁ C₂ F) (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) (Mi hi : ZMod n → ℕ)
    (hF : Formalism.MainNotions.LiftingTheory.Sur W F) (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi) (c : ZMod n) :
    (latHomOf h).WPrime c (rF PD.p n (Mi + hi) c) :=
  wprime_mono _ (wprime_of_kills h hΔ c _ (hR hA T₁ T₂ F Mi hi hF hJ c).2.2.2.1)
    (rI_le_rF hA hR hS F Mi hi hF hJ c)

theorem wprimeCuts_of {Cc : ℝ} (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hR : Formalism.MainNotions.LiftingTheory.coreWR W Cc)
    (hS : Formalism.MainNotions.LiftingTheory.coreWX W) {F : LatHom T₁.L T₂.L} {C₁ : Coord W I T₁} {C₂ : Coord W I T₂}
    (h : CoordHom C₁ C₂ F) (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) (Mi hi H₂ : ZMod n → ℕ)
    (hF : Formalism.MainNotions.LiftingTheory.Sur W F) (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi hi)
    {j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hC : CutsOK n j ty cuts arcLen) :
    Formalism.ExponentWindows.E.WPrimeCuts (latHomOf h) (cutsOf hC) (rrPar PD.p n (Mi + hi) H₂ cuts) := by
  intro c hc
  refine wprime_mono _ (wprime_of hA hR hS h hΔ Mi hi hF hJ c) ?_
  exact le_trans (le_max_left _ _)
    (Finset.le_sup (f := fun c => max (rF PD.p n (Mi + hi) c) (rF PD.p n H₂ c)) hc)

theorem lift_of {Cc : ℝ} (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hR : Formalism.MainNotions.LiftingTheory.coreWR W Cc)
    (hS : Formalism.MainNotions.LiftingTheory.coreWX W) {T : LocLat G Qp LL O} {C : Coord W I T} {C₀ : Coord W I W.one}
    (R : RealExt C C₀) (hE : R.Exact) (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) (H₁ Mi hi : ZMod n → ℕ)
    (hF : Formalism.MainNotions.LiftingTheory.Sur W R.π) (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W R.Y Mi hi) (e₀ : C₀.V)
    {cuts : Finset (ZMod n)} {c : ZMod n} (hc : c ∈ cuts) (he : e₀ ∈ (latOf C₀).N c) :
    (R.ext hE).Lift e₀ c (rrPar PD.p n H₁ (Mi + hi) cuts) := by
  have hw : (latHomOf R.hπ).WPrime c (rrPar PD.p n H₁ (Mi + hi) cuts) :=
    wprime_mono _ (wprime_of hA hR hS R.hπ hΔ Mi hi hF hJ c)
      (le_trans (le_max_right _ _)
        (Finset.le_sup (f := fun c => max (rF PD.p n H₁ c) (rF PD.p n (Mi + hi) c)) hc))
  exact hw e₀ he

theorem jumpsLet_ext (hH : HodgeExact PD LL O) {T Y : LocLat G Qp LL O} (ι : LatHom T.L Y.L)
    (π : LatHom Y.L W.one.L) (hses : IsSESLat (Qp := Qp) ι π) (hY : CrysLat PD Y)
    (Mi hi : ZMod n → ℕ) (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi) : Formalism.MainNotions.LiftingTheory.JumpsLet W Y Mi hi := by
  intro i τ hτ a ha
  rcases ((hH.2.1 T Y W.one ι π hses hY).2.2 τ a).1 ha with h | h
  · exact hJ i τ hτ a h
  · have h0 : a = 0 := hH.2.2 W.one W.one_triv τ a h
    subst h0
    constructor <;> simp

theorem sur_ext (hH : HodgeExact PD LL O) {T Y : LocLat G Qp LL O} (ι : LatHom T.L Y.L)
    (π : LatHom Y.L W.one.L) (hses : IsSESLat (Qp := Qp) ι π) (hY : CrysLat PD Y) :
    Formalism.MainNotions.LiftingTheory.Sur W π :=
  ⟨hY.2.2.2, (hH.2.1 T Y W.one ι π hses hY).2.1.2.2.2, hses.2.2.1⟩

theorem wprimeCuts_of' {Cc : ℝ} (hK : Function.Bijective (algebraMap K₀ K)) (hs : W.s = 1)
    (hp : PD.p ≠ 2) (hR : Formalism.MainNotions.LiftingTheory.coreWR W Cc) (hS : Formalism.MainNotions.LiftingTheory.coreWX W)
    {F : LatHom T₁.L T₂.L} {C₁ : Coord W I T₁} {C₂ : Coord W I T₂} (h : CoordHom C₁ C₂ F)
    (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) (hc₁ : CrysLat PD T₁) (hc₂ : CrysLat PD T₂) (hon : F.Onto)
    (Mb₁ hb₁ H₂ : ZMod n → ℕ)
    (hJ : ∀ i, JumpsAtE PD T₁ W.emb i (Set.Icc (-(Mb₁ i : ℤ)) (hb₁ i)))
    {j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hC : CutsOK n j ty cuts arcLen) :
    Formalism.ExponentWindows.E.WPrimeCuts (latHomOf h) (cutsOf hC) (rrPar PD.p n (Mb₁ + hb₁) H₂ cuts) :=
  wprimeCuts_of ⟨hK, hs, hp⟩ hR hS h hΔ Mb₁ hb₁ H₂ ⟨hc₁.2.2.2, hc₂.2.2.2, hon⟩ hJ hC

theorem lift_of' {Cc : ℝ} (hK : Function.Bijective (algebraMap K₀ K)) (hs : W.s = 1)
    (hp : PD.p ≠ 2) (hR : Formalism.MainNotions.LiftingTheory.coreWR W Cc) (hS : Formalism.MainNotions.LiftingTheory.coreWX W)
    (hH : HodgeExact PD LL O) {C₂ : Coord W I T₂} {C₀ : Coord W I W.one}
    (R : RealExt C₂ C₀) (hE : R.Exact) (hΔ : IsUnit ((W.DelF.card : ℕ) : O))
    (hses : IsSESLat (Qp := Qp) R.ι R.π) (hY : CrysLat PD R.Y) (H₁ Mb₂ hb₂ : ZMod n → ℕ)
    (hJ : ∀ i, JumpsAtE PD T₂ W.emb i (Set.Icc (-(Mb₂ i : ℤ)) (hb₂ i))) (e₀ : C₀.V)
    (he : ∀ i, e₀ ∈ (latOf C₀).N i)
    {j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hC : CutsOK n j ty cuts arcLen) :
    ∀ c ∈ (cutsOf hC).cuts, (R.ext hE).Lift e₀ c (rrPar PD.p n H₁ (Mb₂ + hb₂) cuts) :=
  fun c hc => lift_of ⟨hK, hs, hp⟩ hR hS R hE hΔ H₁ Mb₂ hb₂ (sur_ext hH R.ι R.π hses hY)
    (jumpsLet_ext hH R.ι R.π hses hY Mb₂ hb₂ hJ) e₀ hc (he c)

end Formalism.MainNotions.WachCoordinates.Br
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ArcParametersShiftInvariant
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Comb

variable {n : ℕ} (a : ZMod n)

def sh {α : Type*} (f : ZMod n → α) : ZMod n → α := fun i => f (i - a)

def shC (cuts : Finset (ZMod n)) : Finset (ZMod n) := cuts.image (· + a)

theorem mem_shC {cuts : Finset (ZMod n)} {c : ZMod n} : c ∈ shC a cuts ↔ c - a ∈ cuts := by
  simp only [shC, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨c - a, h, sub_add_cancel c a⟩

theorem ellMax_sh (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    ellMax (shC a cuts) (sh a arcLen) = ellMax cuts arcLen := by
  unfold ellMax shC
  rw [Finset.sup_image]
  congr 1
  funext x
  simp [sh]

theorem cutsOK_sh {j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (h : CutsOK n j ty cuts arcLen) : CutsOK n j (sh a ty) (shC a cuts) (sh a arcLen) := by
  obtain ⟨hne, hj, h3, h4, h5⟩ := h
  refine ⟨hne.image _, hj, fun c hc ↦ ?_, fun c hc ↦ h4 _ ((mem_shC a).1 hc), fun c hc k hk1 hkj ↦ ?_⟩
  · obtain ⟨e1, e2, e3, e4⟩ := h3 _ ((mem_shC a).1 hc)
    refine ⟨e1, e2, (mem_shC a).2 ?_, fun d hd1 hd2 hmem ↦ e4 d hd1 hd2 ?_⟩
    · rw [sub_right_comm]
      exact e3
    · have hm := (mem_shC a).1 hmem
      rwa [sub_right_comm] at hm
  · show ty (c + (k : ZMod n) - a) = LT.thin
    rw [show c + (k : ZMod n) - a = c - a + k by ring]
    exact h5 _ ((mem_shC a).1 hc) k hk1 hkj

theorem ro_sh (ty : ZMod n → LT) (arcLen : ZMod n → ℕ) (c : ZMod n) :
    ro (sh a ty) (sh a arcLen) c = ro ty arcLen (c - a) := by
  rw [Formalism.MainNotions.LocalTheoryWindows.ro, Formalism.MainNotions.LocalTheoryWindows.ro, Formalism.MainNotions.LocalTheoryWindows.thickLv, Formalism.MainNotions.LocalTheoryWindows.thickLv]
  congr 1
  apply Finset.filter_congr
  intro s _
  simp only [sh]
  rw [show c - (s : ZMod n) - a = c - a - s by ring]

theorem thickLe2_sh {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (h : ThickLe2 ty cuts arcLen) : ThickLe2 (sh a ty) (shC a cuts) (sh a arcLen) := by
  intro c hc
  rw [ro_sh]
  exact h _ ((mem_shC a).1 hc)

theorem wordOK_sh {l a₀ : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (h : WordOK l a₀ ty cuts arcLen) : WordOK l a₀ (sh a ty) (shC a cuts) (sh a arcLen) := by
  intro c hc s₀ s₁ hs hs1 b₀ b₁
  have h' := h _ ((mem_shC a).1 hc) s₀ s₁ hs hs1 b₀ b₁
  simp only [sh]
  rw [sub_right_comm c (s₁ : ZMod n) a, sub_right_comm c (s₀ : ZMod n) a]
  exact h'

theorem sizesOK_sh {g S h : ℕ} {ty : ZMod n → LT} (H : SizesOK g S h ty) :
    SizesOK g S h (sh a ty) := fun i ↦ H (i - a)

variable [NeZero n]

theorem Hmax_sh (H : ZMod n → ℕ) : Hmax n (sh a H) = Hmax n H := by
  unfold Hmax
  apply le_antisymm
  · exact Finset.sup_le fun i _ ↦ Finset.le_sup (f := H) (Finset.mem_univ (i - a))
  · refine Finset.sup_le fun i _ ↦ ?_
    have hle := Finset.le_sup (f := sh a H) (Finset.mem_univ (i + a))
    simpa [sh] using hle

theorem sBd_sh (l : ℕ) (H : ZMod n → ℕ) (i : ZMod n) : sBd l n (sh a H) i = sBd l n H (i - a) := by
  unfold sBd
  rw [Hmax_sh]
  congr 1
  funext k
  simp only [sh]
  rw [show i + ((k + 1 : ℕ) : ZMod n) - a = i - a + ((k + 1 : ℕ) : ZMod n) by ring]

theorem rF_sh (l : ℕ) (H : ZMod n → ℕ) (i : ZMod n) : rF l n (sh a H) i = rF l n H (i - a) := by
  unfold rF
  rw [sBd_sh, Hmax_sh]

theorem rrPar_sh (l : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n)) :
    rrPar l n (sh a H₁) (sh a H₂) (shC a cuts) = rrPar l n H₁ H₂ cuts := by
  unfold rrPar shC
  rw [Finset.sup_image]
  congr 1
  funext c
  simp [rF_sh]

theorem arc_parameters_shift_invariant (l j g h : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    initialExponentBound l n j g h (sh a H₁) (sh a H₂) (shC a cuts) (sh a arcLen) =
      initialExponentBound l n j g h H₁ H₂ cuts arcLen := by
  unfold initialExponentBound
  rw [rrPar_sh, ellMax_sh]

theorem ePar_sh (l j g h : ℕ) (H₁ H₂ : ZMod n → ℕ) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    ePar l n j g h (sh a H₁) (sh a H₂) (shC a cuts) (sh a arcLen) =
      ePar l n j g h H₁ H₂ cuts arcLen := by
  unfold ePar
  rw [rrPar_sh, arc_parameters_shift_invariant, ellMax_sh]

end Comb

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]

theorem jumpsAtE_sh (T : LocLat G Qp LL O) (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (a i : ZMod n) (S : Set ℤ)
    (h : JumpsAtE PD T (fun k => emb (k + a)) (i - a) S) : JumpsAtE PD T emb i S := by
  intro τ hτ
  exact h τ (by simp only [sub_add_cancel]; exact hτ)

theorem exists_rot {emb emb' : ZMod n → (K₀ →ₐ[Qp] LL)} (hb : Function.Surjective emb')
    (h : ∀ i, (emb (i + 1)).comp PD.σ = emb i) (h' : ∀ i, (emb' (i + 1)).comp PD.σ = emb' i) :
    ∃ a : ZMod n, emb = fun i => emb' (i + a) := by
  obtain ⟨a, ha⟩ := hb (emb 0)
  refine ⟨a, ?_⟩
  have key : ∀ k : ℕ, emb (-(k : ZMod n)) = emb' (-(k : ZMod n) + a) := by
    intro k
    induction k with
    | zero => simp [ha]
    | succ k ih =>
      have e1 := h (-((k + 1 : ℕ) : ZMod n))
      have e2 := h' (-((k + 1 : ℕ) : ZMod n) + a)
      rw [show -((k + 1 : ℕ) : ZMod n) + 1 = -(k : ZMod n) by push_cast; ring, ih] at e1
      rw [show -((k + 1 : ℕ) : ZMod n) + a + 1 = -(k : ZMod n) + a by push_cast; ring] at e2
      rw [← e1, e2]
  funext i
  have hi := key ((-i).val)
  rwa [ZMod.natCast_zmod_val, neg_neg] at hi

variable [Fintype (K →ₐ[Qp] LL)]

theorem thmELiftAt_rot (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (a : ZMod n)
    (H : ThmELiftAt PD (O := O) n emb v) : ThmELiftAt PD (O := O) n (fun i => emb (i + a)) v := by
  intro hLet hp T₁ T₂ F hGood hC1 hC2 hOnto j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hKind hJ hg
    hSizes hCuts hThick hJ1 hJ2 hWord
  have hLet' : Letters PD LL v emb := by
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hLet
    refine ⟨e1, e2, e3, ?_, fun i ↦ ?_, e6⟩
    · have he : emb = (fun i ↦ emb (i + a)) ∘ (fun i ↦ i - a) := funext fun i ↦ by simp
      rw [he]
      exact e4.comp (Equiv.subRight a).bijective
    · have e := e5 (i - a)
      simp only [sub_add_cancel, show i - a + 1 + a = i + 1 by ring] at e
      exact e
  have hW : WordOK PD.p (initialExponentBound PD.p n j (gPar Gp S η) h (sh a Mb₁ + sh a hb₁) (sh a Mb₂ + sh a hb₂)
      (shC a cuts) (sh a arcLen)) (sh a ty) (shC a cuts) (sh a arcLen) := by
    rw [show sh a Mb₁ + sh a hb₁ = sh a (Mb₁ + hb₁) from rfl,
      show sh a Mb₂ + sh a hb₂ = sh a (Mb₂ + hb₂) from rfl, arc_parameters_shift_invariant]
    exact wordOK_sh a hWord
  have hL := H hLet' hp T₁ T₂ F hGood hC1 hC2 hOnto j Gp S η h (sh a ty) (shC a cuts) (sh a arcLen)
    (sh a Mb₁) (sh a hb₁) (sh a Mb₂) (sh a hb₂) (fun i ↦ jumpsAtE_sh T₁ emb a i _ (hKind (i - a))) hJ hg
    (sizesOK_sh a hSizes) (cutsOK_sh a hCuts) (thickLe2_sh a hThick)
    (fun i ↦ jumpsAtE_sh T₁ emb a i _ (hJ1 (i - a))) (fun i ↦ jumpsAtE_sh T₂ emb a i _ (hJ2 (i - a))) hW
  rwa [show sh a Mb₁ + sh a hb₁ = sh a (Mb₁ + hb₁) from rfl,
    show sh a Mb₂ + sh a hb₂ = sh a (Mb₂ + hb₂) from rfl, ePar_sh] at hL

end Formalism.MainNotions.WachCoordinates.Br
end
end

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

structure BrData2 (hR : Ring9 W) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) where
  C₁ : Coord W (baseIdOf hR) T₁
  C₂ : Coord W (baseIdOf hR) T₂
  C₀ : Coord W (baseIdOf hR) W.one
  h : CoordHom C₁ C₂ F
  e₀ : C₀.V
  Ks : ℕ → Type
  [ksRing : ∀ s, CommRing (Ks s)]
  [ksAlg : ∀ s, Algebra LL (Ks s)]
  Δ : Type

attribute [instance] BrData2.ksRing BrData2.ksAlg

structure BrProps2 {hR : Ring9 W} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L}
    (D : BrData2 hR T₁ T₂ F) (e : W.DD W.one) (Cu : Formalism.ExponentWindows.E.Cuts n) (kd : ZMod n → Formalism.ExponentWindows.Kind)
    (bb : ZMod n → ℕ) (j g G₀ Sz η hh : ℕ) : Prop where

  he₀ : ∀ i, D.C₀.t i D.e₀ = (letE i : LetA O n) • e

  arcs : ∀ ϖ : O, Irreducible ϖ → ∀ c ∈ Cu.cuts, Formalism.ExponentWindows.E.FinalArc (latHomOf D.h) c (Cu.ell c)
    (Formalism.ExponentWindows.E.HArc g G₀ Sz η kd bb c) LL D.Ks D.Δ ϖ (W.χΓ W.gam) j
    (Formalism.ExponentWindows.E.parM (baseIdOf hR).Bs.ℓ hh g) g G₀ Sz η (Formalism.ExponentWindows.E.kindAt kd c)
    (Formalism.ExponentWindows.E.sizeAt bb c)

variable [Fintype (K →ₐ[Qp] LL)]

def Realised2 (hR : Ring9 W) (e : W.DD W.one) : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L),
    GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := T₁.V) →
    CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∀ (j Gp S η h : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ)
      (hC : CutsOK n j ty cuts arcLen),
      KindJumps PD T₁ W.emb Gp S η ty →
      (∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) →
      gPar Gp S η ≤ h → SizesOK (gPar Gp S η) S h ty → ThickLe2 ty cuts arcLen →
      ∃ D : BrData2 hR T₁ T₂ F,
        BrProps2 D e (cutsOf hC) (kdOf ty) (bbOf ty) j (gPar Gp S η) Gp S η h


variable (W) in
structure BrHyp2 (Cc : ℝ) : Prop where

  s_one : W.s = 1

  unram : Function.Bijective (algebraMap K₀ K)

  five_le : 5 ≤ PD.p

  P5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W

  P6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W

  P9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W

  herr : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFirstProperty W

  wx : Formalism.MainNotions.LiftingTheory.coreWX W

  wr : Formalism.MainNotions.LiftingTheory.coreWR W Cc

  tools : ToolsAlg W

  f1 : F1 W

  f2 : F2 W

  hodge : HodgeExact PD LL O

  valRing : ValRing O v

  complete : IsAdicComplete (Ideal.span {(((PD.p : ℕ) : O))}) O

  real : ∃ e : W.DD W.one, UnitGen W e ∧ BKExt W e ∧ ∀ hR : Ring9 W, Realised2 hR e

theorem realised_of {Cc : ℝ} (H : BrHyp2 W Cc) : Realised W := by
    intro T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hC hK hJ hg hS hT hb1 hb2 _
    obtain ⟨e, he, hbk, hreal⟩ := H.real
    have h5 := H.five_le
    have hp2 : PD.p ≠ 2 := by omega
    have hR : Ring9 W := ring_condition_of_delta_invariants (H.P9 T₁ hc₁.2.2.2) H.s_one hp2 (unram_of H.unram)
    obtain ⟨D, P⟩ := hreal hR T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen hC hK hJ hg hS hT
    obtain ⟨-, -, hO, hD, -⟩ := hG
    have := hO
    have := hD
    obtain ⟨ϖ, eO, x, hϖ, hprim, hu⟩ :=
      ground_of hR H.s_one (by omega) H.valRing H.complete
    have hcard : IsUnit ((W.DelF.card : ℕ) : O) :=
      cardΔ_of (not_isUnit_p W H.valRing)
        (card_DelF H.s_one hp2 (unram_of H.unram) (H.P9 T₁ hc₁.2.2.2))
    have Q : LocalWachInputs W (baseIdOf hR) :=
      { s_one := H.s_one
        p_ne_two := hp2
        unram := unram_of H.unram
        P9 := H.P9
        P5 := H.P5
        P6 := H.P6
        tools := H.tools
        p_ne_zero := p_ne_zero_of W
        cardΔ := hcard
        inj := baseIdOf_inj hR
        full := baseIdOf_full hR }
    have hK₂ : ∀ i, JumpsAtE PD T₂ W.emb i ((ty i).win Gp S η) := fun i =>
      kind_quot H.hodge F hc₁ hc₂ hon (hK i)
    have hl₁ := finalLat_of Q hc₁.2.2.2 hC hg hS
      (fun i => jumpsAtE_mono (hK i) Set.subset_union_left) D.C₁
    have hl₂ := finalLat_of Q hc₂.2.2.2 hC hg hS
      (fun i => jumpsAtE_mono (hK₂ i) Set.subset_union_left) D.C₂
    have hunit := primUnit_of (baseIdOf_inj hR) (baseIdOf_full hR) he D.C₀ D.e₀ P.he₀
    refine ⟨{ I := baseIdOf hR, C₁ := D.C₁, C₂ := D.C₂, C₀ := D.C₀, h := D.h, e₀ := D.e₀, ϖ := ϖ,
              eO := eO, u := W.χΓ W.gam, x := x, Ks := D.Ks, Δ := D.Δ }, ?_⟩
    exact
      { irr := hϖ
        prim := hprim
        u_eq := hu
        lat₁ := hl₁
        lat₂ := hl₂
        unit := hunit
        rho := rho_field H.f1 H.f2 hc₁.2.2.2 h hJ (by omega) D.C₁ hl₁.prim.p5M (cutsOf hC) _ j _ _
        ext := fun κ hκ => by
          obtain ⟨R, hE, hses, hY, hrep⟩ :=
            ext_of' he H.hodge hbk hc₂.2.2.2 D.C₂ D.C₀ D.e₀ P.he₀ κ hκ
          exact ⟨R.ext hE, hrep, primExt_of Q H.hodge hC hS hK₂ R hE hses hY D.e₀
            (lift_of' H.unram H.s_one hp2 H.wr H.wx H.hodge R hE hcard hses hY (Mb₁ + hb₁) Mb₂ hb₂ hb2
              D.e₀ (fun i => by rw [hunit.N_eq i]; exact Submodule.mem_span_singleton_self _) hC)⟩
        wprime := wprimeCuts_of' H.unram H.s_one hp2 H.wr H.wx D.h hcard hc₁ hc₂ hon Mb₁ hb₁
          (Mb₂ + hb₂) hb1 hC
        arcs := P.arcs ϖ hϖ }

theorem crystalline_lifting_second_form {Cc : ℝ} (H : BrHyp2 W Cc) : ThmELiftAt PD (O := O) n W.emb v := by
  intro _ h5 T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hK hJ hg hS hC hT hb1 hb2
    hW
  obtain ⟨D, P⟩ := realised_of H T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hC hK
    hJ hg hS hT hb1 hb2 hW
  obtain ⟨-, -, hO, hD, hF⟩ := hG
  have := hO
  have := hD
  have hnum := finalNum_of PD.p (by omega) n j Gp S η h ty cuts arcLen (Mb₁ + hb₁) (Mb₂ + hb₂) hC hg hS
    hT hW
  have hnum' : Formalism.ExponentWindows.E.FinalNum D.I.Bs.ℓ (cutsOf hC) (kdOf ty) (bbOf ty) j (gPar Gp S η) Gp S η h
      (sigPar PD.p (gPar Gp S η) h j) (rrPar PD.p n (Mb₁ + hb₁) (Mb₂ + hb₂) cuts)
      (kapPar PD.p (gPar Gp S η) h (ellMax cuts arcLen)) (ellMax cuts arcLen) := by
    rw [D.I.ℓ_eq]
    exact hnum
  have hJ₂ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₂.ρ τ (Set.Icc (-(h : ℤ)) h) := fun τ a ha =>
    hJ τ a (H.hodge.1 T₁ T₂ F hc₁ hc₂ hon τ a ha)
  have key := Formalism.ExponentWindows.E.theorem_E_final_form O D.ϖ P.irr D.I.Bs D.eO n (cutsOf hC) (kdOf ty) (bbOf ty) j
    (gPar Gp S η) Gp S η h _ _ _ _ D.u D.x LL D.Ks D.Δ D.C₁.V D.C₂.V D.C₀.V (latOf D.C₁) (latOf D.C₂)
    (latOf D.C₀) D.e₀ (latHomOf D.h) (ZfN D.C₁ F) (Zf D.C₂) ⟨P.prim, P.u_eq, hF⟩ hnum'
    P.lat₁ P.lat₂ P.unit
    ⟨fun m κ hκ => ZfN_smul D.C₁ F m κ hκ,
      rho_fieldN H.f1 H.f2 F hc₁.2.2.2 hc₂.2.2.2 h hJ hJ₂ (by omega) D.C₁ P.lat₁.prim.p5M (cutsOf hC) _ j
        _ _, P.ext⟩ P.wprime P.arcs
  rw [parE_eq_ePar] at key
  exact liftF_ofN D.h H.s_one (by omega) (H.herr T₂ hc₂.2.2.2).2 _ key

end Formalism.MainNotions.WachCoordinates.Br
