module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.AdSurj
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.adSurj :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (R : RingBr L) (n : ℕ) (g : UA L n), ∃ x : ∀ v : Pl (Lp L), Matrix (Fin n) (Fin n) (Lsq (Kv v) (cv v R.Δ)), (∀ v, star (x v) * x v = 1) ∧ (∀ᶠ v in Filter.cofinite, ∀ i j, IsIntegral (Ov v) (x v i j)) ∧ ∀ w, mL w g = (x (un w)).map (R.ρ _ w rfl) := by
  intro L _ _ _ R n g
  classical
  let G : Matrix (Fin n) (Fin n) (Ad L) := (g.1 : Matrix (Fin n) (Fin n) (Ad L))
  let A : Matrix (Fin n) (Fin n) (Af L) := G.map (pFin L)
  have hU : ∀ i j, ∑ k, cjF (L := L) (A k i) * A k j = (1 : Matrix (Fin n) (Fin n) (Af L)) i j := by
    have hG : Formalism.UG.cT (conjAd L) G * 1 * G = 1 := g.2
    have h1 := congrArg (pFin L).mapMatrix hG
    rw [map_one, map_mul, map_mul, map_one, Matrix.mul_one] at h1
    intro i j
    have h2 := congrFun (congrFun h1 i) j
    rw [Matrix.mul_apply] at h2
    exact h2
  have hx : ∀ v i j, ∃ x : Lsq (Kv v) (cv v R.Δ), ∀ w h, R.ρ v w h x = pLoc L w (A i j) :=
    fun v i j => R.ρ_surj v (A i j)
  choose x hx using hx
  refine ⟨fun v => Matrix.of (x v), ?_, ?_, ?_⟩
  · intro v
    ext1 i j
    rw [← sub_eq_zero]
    apply R.ρ_inj v
    intro w h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, Matrix.mul_apply, map_sum]
    have e1 : ∀ k, R.ρ v w h ((star (Matrix.of (x v))) i k * (Matrix.of (x v)) k j) =
        pLoc L w (cjF (L := L) (A k i) * A k j) := by
      intro k
      rw [map_mul, map_mul, Matrix.star_apply, Matrix.of_apply, Matrix.of_apply,
        R.ρ_star v _ _ (hx v k i) w h, hx v k j w h]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl fun k _ => e1 k, ← map_sum, hU i j]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  · have hfin : ∀ i j, {w : Plc L | pLoc L w (A i j) ∉ w.adicCompletionIntegers L}.Finite := by
      intro i j
      exact (A i j).2
    have hall : {w : Plc L | ∃ i j, pLoc L w (A i j) ∉ w.adicCompletionIntegers L}.Finite := by
      have : {w : Plc L | ∃ i j, pLoc L w (A i j) ∉ w.adicCompletionIntegers L} =
          ⋃ i, ⋃ j, {w : Plc L | pLoc L w (A i j) ∉ w.adicCompletionIntegers L} := by
        ext w; simp
      rw [this]
      exact Set.finite_iUnion fun i => Set.finite_iUnion fun j => hfin i j
    have hbad := hall.image (fun w : Plc L => un w)
    rw [Filter.eventually_cofinite]
    refine hbad.subset ?_
    intro v hv
    simp only [Set.mem_setOf_eq, not_forall] at hv
    obtain ⟨i, j, hij⟩ := hv
    have : ¬ ∀ w h, R.ρ v w h (x v i j) ∈ w.adicCompletionIntegers L := fun h => hij ((R.ρ_int v _).2 h)
    simp only [not_forall] at this
    obtain ⟨w, h, hw⟩ := this
    exact ⟨w, ⟨i, j, by rwa [hx v i j w h] at hw⟩, h⟩
  · intro w
    refine Matrix.ext fun i j => ?_
    change mL w g i j = R.ρ _ w rfl (x (un w) i j)
    rw [hx (un w) i j w rfl]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.LocBase
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.locBase :
    ∀ (F : Type) [Field F] [NumberField F] (v : Pl F), IsFractionRing (Ov v) (Kv v) ∧ IsAdicComplete (IsLocalRing.maximalIdeal (Ov v)) (Ov v) ∧ Finite (IsLocalRing.ResidueField (Ov v)) ∧ ((2 : 𝓞 F) ∉ v.asIdeal → IsUnit (2 : Ov v)) := by
  intro F _ _ v
  refine ⟨inferInstance, GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v,
    GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v, fun h => ?_⟩
  have := (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v (2 : 𝓞 F)).2 h
  rwa [map_ofNat] at this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.MemDxIff
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem mem_dx_iff {K : Type} [Field K] {Δ : K} (g : GL (Fin 2) (Lsq K Δ)) :
    g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map star =
      !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0] := by
  constructor
  · intro h
    exact congrArg Units.val h
  · intro h
    exact Units.ext h

private theorem conj_two {R : Type} [CommRing R] (a b c d : R) :
    (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) R) * !![a, b; c, d] * !![0, 1; -1, 0] = !![d, -c; -b, a] := by
  simp [Matrix.mul_fin_two]

private theorem dx_form {K : Type} [Field K] {Δ : K} (g : DX Δ) :
    ∃ a b : Lsq K Δ, mt g = !![a, b; -star b, star a] := by
  have h := (mem_dx_iff _).1 g.2
  obtain ⟨a, b, c, d, hm⟩ : ∃ a b c d, ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hm, conj_two] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp at h00 h01
  refine ⟨a, b, ?_⟩
  show ((g : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = _
  rw [hm, h00, show c = -star b by rw [h01, neg_neg]]

theorem UpperTheory.V.Z.Sym.Dict.Br.suIff :
    ∀ (K : Type) [Field K] (Δ : K), (∀ g : DX Δ, star (mt g) * mt g = (mt g).det • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) ∧ star (mt g).det = (mt g).det) ∧ ∀ x : Matrix (Fin 2) (Fin 2) (Lsq K Δ), star x * x = 1 → x.det = 1 → ∃ g : DX Δ, mt g = x := by
  intro K _ Δ
  refine ⟨fun g => ?_, fun x hx hd => ?_⟩
  · obtain ⟨a, b, h⟩ := dx_form g
    rw [h, Matrix.det_fin_two_of]
    constructor
    · rw [Matrix.star_eq_conjTranspose, Matrix.one_fin_two]
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    · simp [mul_comm]
  · have hadj : star x = x.adjugate := by
      calc star x = star x * (x * x.adjugate) := by rw [Matrix.mul_adjugate, hd, one_smul, mul_one]
        _ = x.adjugate := by rw [← mul_assoc, hx, one_mul]
    let u : GL (Fin 2) (Lsq K Δ) :=
      ⟨x, x.adjugate, by rw [Matrix.mul_adjugate, hd, one_smul], by rw [Matrix.adjugate_mul, hd, one_smul]⟩
    have hu : u ∈ DX Δ := by
      refine (mem_dx_iff u).2 ?_
      show x.map star = !![0, -1; 1, 0] * x * !![0, 1; -1, 0]
      obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, x = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two _⟩
      rw [conj_two]
      rw [Matrix.star_eq_conjTranspose, Matrix.adjugate_fin_two_of] at hadj
      have h00 := congrFun (congrFun hadj 0) 0
      have h01 := congrFun (congrFun hadj 0) 1
      have h10 := congrFun (congrFun hadj 1) 0
      have h11 := congrFun (congrFun hadj 1) 1
      simp at h00 h01 h10 h11
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
    exact ⟨⟨u, hu⟩, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RatFacts
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br

private theorem ratGL_val {L : Type} [Field L] [NumberField L] (n : ℕ) (g : GL (Fin n) L) :
    ((ratGL L n g : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) =
      (g : Matrix (Fin n) (Fin n) L).map (algebraMap L (Ad L)) := rfl

private theorem ratGL_map {L : Type} [Field L] [NumberField L] (n : ℕ) (g : GL (Fin n) L) :
    ratGL L n g = GeneralLinearGroup.map (algebraMap L (Ad L)) g :=
  Units.ext (ratGL_val n g)

private theorem alg_inj {L : Type} [Field L] [NumberField L] [IsCMField L] :
    Function.Injective (algebraMap L (Ad L)) := by
  obtain ⟨τ⟩ : Nonempty (L →+* ℂ) := inferInstance
  intro x y h
  have e := congrArg (fun z => coord τ (pInf L z)) h
  simp only [coord_algebraMap] at e
  exact τ.injective e

private theorem loc_alg {L : Type} [Field L] [NumberField L] (w : Plc L) (x : L) :
    pLoc L w (pFin L (algebraMap L (Ad L) x)) = algebraMap L (Kw w) x := rfl

end UpperTheory.V.Z.Sym.Dict.Br

theorem UpperTheory.V.Z.Sym.Dict.Br.ratFacts :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (g : GL (Fin n) L), (ratGL L n g ∈ UA L n ↔ ((g : Matrix (Fin n) (Fin n) L).map (IsCMField.complexConj L))ᵀ * (g : Matrix (Fin n) (Fin n) L) = 1) ∧ Function.Injective (ratGL L n) ∧ ∀ h : ratGL L n g ∈ UA L n, (∀ w, mL w ⟨_, h⟩ = (g : Matrix (Fin n) (Fin n) L).map (algebraMap L (Kw w))) ∧ (∀ τ : L →+* ℂ, (cEmb τ ⟨_, h⟩ : Matrix (Fin n) (Fin n) ℂ) = (g : Matrix (Fin n) (Fin n) L).map τ) ∧ ((GeneralLinearGroup.det (ratGL L n g) = 1) ↔ GeneralLinearGroup.det g = 1) := by
  intro L _ _ _ n g
  have hinj := alg_inj (L := L)
  refine ⟨?_, ?_, fun h => ⟨fun w => ?_, fun τ => ?_, ?_⟩⟩
  · have key : Formalism.UG.cT (conjAd L) ((ratGL L n g : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) * 1 *
        ((ratGL L n g : GL (Fin n) (Ad L)) : Matrix (Fin n) (Fin n) (Ad L)) =
        (((g : Matrix (Fin n) (Fin n) L).map (IsCMField.complexConj L))ᵀ * (g : Matrix (Fin n) (Fin n) L)).map
          (algebraMap L (Ad L)) := by
      rw [ratGL_val, mul_one, Formalism.UG.cT, Matrix.map_mul]
      congr 1
      ext i j
      simp [conjAd_algebraMap]
    change Formalism.UG.cT (conjAd L) _ * 1 * _ = 1 ↔ _
    rw [key]
    constructor
    · intro e
      ext i j
      have := congrFun (congrFun e i) j
      apply hinj
      rw [Matrix.map_apply] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · intro e
      rw [e]
      simp
  · intro a b e
    ext i j
    have := congrArg (fun x : GL (Fin n) (Ad L) => (x : Matrix (Fin n) (Fin n) (Ad L)) i j) e
    simp only [ratGL_val, Matrix.map_apply] at this
    exact hinj this
  · exact Matrix.ext fun i j => loc_alg w _
  · exact Matrix.ext fun i j => coord_algebraMap τ _
  · have hd : ((GeneralLinearGroup.det (ratGL L n g) : (Ad L)ˣ) : Ad L) =
        algebraMap L (Ad L) ((GeneralLinearGroup.det g : Lˣ) : L) := by
      rw [ratGL_map, GlobalTheory.CuspRep.det_map]
    constructor
    · intro e
      rw [e] at hd
      apply Units.ext
      apply hinj
      rw [← hd]
      simp
    · intro e
      apply Units.ext
      rw [hd, e]
      simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IsoVal
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

section SlopeTestRemainingChoices

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {i : k ≃+* k'}

private theorem iso_le (h : IsoOk i) (a b : k) :
    valuation k' (i a) ≤ valuation k' (i b) ↔ valuation k a ≤ valuation k b := by
  by_cases hb : b = 0
  · subst hb
    simp
  · have hb' : i b ≠ 0 := fun e => hb (by simpa using e)
    have e1 := h.int (a / b)
    rw [map_div₀, map_div₀, map_div₀,
      div_le_one₀ (zero_lt_iff.2 ((valuation k').ne_zero_iff.2 hb')),
      div_le_one₀ (zero_lt_iff.2 ((valuation k).ne_zero_iff.2 hb))] at e1
    exact e1

private theorem iso_symm (h : IsoOk i) : IsoOk i.symm :=
  ⟨fun a => by simpa using (h.int (i.symm a)).symm⟩

private theorem iso_lt (h : IsoOk i) (a : k) : valuation k' (i a) < 1 ↔ valuation k a < 1 := by
  have e := iso_le h 1 a
  simp only [map_one] at e
  rw [← not_le, ← not_le, e]

private theorem val_unif (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k (UpperTheory.V.Hi.unif k : k) = uniformizer k := by
  have hex : ∃ x : kˣ, valuation k (x : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)
    exact ⟨Units.mk0 x hx0, hx⟩
  exact Classical.epsilon_spec hex

private theorem locO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    IsLocalRing 𝒪[k] :=
  (inferInstance : IsDiscreteValuationRing 𝒪[k]).toIsLocalRing

attribute [local instance 5000] locO

private def intIso (h : IsoOk i) : 𝒪[k] ≃+* 𝒪[k'] where
  toFun x := ⟨i x, (h.int x).2 x.2⟩
  invFun y := ⟨i.symm y, (iso_symm h |>.int y).2 y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

private theorem intIso_max (h : IsoOk i) (x : 𝒪[k]) (hx : x ∈ IsLocalRing.maximalIdeal 𝒪[k]) :
    intIso h x ∈ IsLocalRing.maximalIdeal 𝒪[k'] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  exact fun e => hx ((isUnit_map_iff (intIso h) x).1 e)

private theorem intIso_pow (h : IsoOk i) (c : ℕ) (x : 𝒪[k]) (hx : x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c) :
    intIso h x ∈ IsLocalRing.maximalIdeal 𝒪[k'] ^ c := by
  have h1 : Ideal.map (intIso h : 𝒪[k] →+* 𝒪[k']) (IsLocalRing.maximalIdeal 𝒪[k]) ≤
      IsLocalRing.maximalIdeal 𝒪[k'] :=
    Ideal.map_le_iff_le_comap.2 fun y hy => intIso_max h y hy
  have h2 := Ideal.mem_map_of_mem (intIso h : 𝒪[k] →+* 𝒪[k']) hx
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 c h2

private theorem Uc_fwd (h : IsoOk i) (c : ℕ) (a : kˣ) (ha : a ∈ UpperTheory.V.Hi.Uc k c) :
    Units.map (i : k →* k') a ∈ UpperTheory.V.Hi.Uc k' c := by
  obtain ⟨u, hu, rfl⟩ := ha
  have hu1 : (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c := by
    have e := congrArg Units.val (MonoidHom.mem_ker.1 hu)
    exact Ideal.Quotient.eq.1 (by simpa using e)
  refine ⟨Units.map (intIso h : 𝒪[k] →* 𝒪[k']) u, ?_, ?_⟩
  · refine MonoidHom.mem_ker.2 (Units.ext ?_)
    have e := intIso_pow h c _ hu1
    rw [map_sub, map_one] at e
    simpa using Ideal.Quotient.eq.2 e
  · exact Units.ext rfl

end SlopeTestRemainingChoices

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.isoVal :
    ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), IsoOk i → (∀ a b, valuation k' (i a) ≤ valuation k' (i b) ↔ valuation k a ≤ valuation k b) ∧ valuation k' (i (Hi.unif k : k)) = valuation k' (Hi.unif k' : k') ∧ (∀ a : kˣ, Units.map (i : k →* k') a ∈ Hi.Uo k' ↔ a ∈ Hi.Uo k) ∧ ∀ (c : ℕ) (a : kˣ), Units.map (i : k →* k') a ∈ Hi.Uc k' c ↔ a ∈ Hi.Uc k c := by
  intro k k' _ _ _ _ _ _ _ _ i h
  refine ⟨iso_le h, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [val_unif k']
      refine le_uniformizer_iff.2 ((iso_lt h _).2 ?_)
      rw [val_unif k]
      exact uniformizer_lt_one
    · have h1 : valuation k (i.symm (Hi.unif k' : k')) < 1 := by
        refine (iso_lt (iso_symm h) _).2 ?_
        rw [val_unif k']
        exact uniformizer_lt_one
      have h2 : valuation k (i.symm (Hi.unif k' : k')) ≤ valuation k (Hi.unif k : k) := by
        rw [val_unif k]
        exact le_uniformizer_iff.2 h1
      simpa using (iso_le h _ _).2 h2
  · intro a
    change valuation k' (i (a : k)) = 1 ↔ valuation k (a : k) = 1
    have e1 := iso_le h (a : k) 1
    have e2 := iso_le h 1 (a : k)
    simp only [map_one] at e1 e2
    rw [le_antisymm_iff, le_antisymm_iff, e1, e2]
  · intro c a
    refine ⟨fun ha => ?_, Uc_fwd h c a⟩
    have e := Uc_fwd (iso_symm h) c _ ha
    have e' : Units.map (i.symm : k' →* k) (Units.map (i : k →* k') a) = a := Units.ext (by simp)
    rwa [e'] at e
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.IntsOv
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem mem_adicCompletionIntegers_iff_valuation_le_one (F : Type) [Field F] [NumberField F] (v : Pl F) (x : Kv v) :
    x ∈ v.adicCompletionIntegers F ↔ valuation (Kv v) x ≤ 1 := by
  rw [← (valuation (Kv v)).vle_one_iff, HeightOneSpectrum.mem_adicCompletionIntegers]
  change _ ↔ Valued.v x ≤ Valued.v (1 : Kv v)
  rw [map_one]

theorem UpperTheory.V.Z.Sym.Dict.Br.intsOv :
    ∀ (F : Type) [Field F] [NumberField F] (v : Pl F), Sig.IsInts (Kv v) (Ov v) ∧ ∀ x : Kv v, x ∈ v.adicCompletionIntegers F ↔ valuation (Kv v) x ≤ 1 := by
  intro F _ _ v
  refine ⟨⟨Subtype.val_injective, fun x => ?_⟩, mem_adicCompletionIntegers_iff_valuation_le_one F v⟩
  rw [← mem_adicCompletionIntegers_iff_valuation_le_one F v x]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoStar
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoStar :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v (x : Lsq (Kv v) (cv v P.Δ)) (a : Af L), (∀ w h, P.rho v w h x = pLoc L w a) → ∀ w h, P.rho v w h (star x) = pLoc L w (cjF a) := by
  intro L _ _ _ P v x a hx w h
  have hu : un (conjSrc (IsCMField.complexConj L).toRingEquiv w) = v := by
    rw [← h]; exact GlobalTheory.LocInj.under_conjSrc w
  have hφ : ∀ y : Kv v, conjLoc (IsCMField.complexConj L).toRingEquiv w
      (P.φ v _ hu y) = P.φ v w h y := by
    intro y
    refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (Lp L) v).equalizer
      ((conjLoc_spec _ w).1.comp (P.φ_cont v _ hu)) (P.φ_cont v w h) (funext fun b => ?_)) y
    simp only [Function.comp_apply]
    rw [P.φ_alg, P.φ_alg, (conjLoc_spec _ w).2.1]
    congr 1
    exact AlgEquiv.commutes (IsCMField.complexConj L) b
  have hrt : conjLoc (IsCMField.complexConj L).toRingEquiv w (P.rt (conjSrc (IsCMField.complexConj L).toRingEquiv w)) = - P.rt w := by
    rw [Pre.rt, (conjLoc_spec _ w).2.1, Pre.rt, ← map_neg, ← map_neg]
    congr 1
    have hs : star (QuadraticAlgebra.omega : Lsq (Lp L) P.Δ) = - QuadraticAlgebra.omega := by
      ext <;> simp
    change IsCMField.complexConj L (P.e QuadraticAlgebra.omega) = _
    rw [← P.e_star, hs]
  rw [cjF, pLoc_conjFin, ← hx _ hu]
  change P.φ v w h (star x).re + P.φ v w h (star x).im * P.rt w =
    conjLoc (IsCMField.complexConj L).toRingEquiv w (P.φ v _ hu x.re + P.φ v _ hu x.im * P.rt _)
  rw [map_add (f := _), map_mul, hφ, hφ, hrt]
  simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoDiv
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoDiv :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v w h (a : Kv v), P.φ v w h a ∈ w.adicCompletionIntegers L ↔ a ∈ v.adicCompletionIntegers (Lp L) := by
  intro L _ _ _ P v w h a
  subst h
  have hval : ∀ (F : Type) [Field F] [NumberField F] (u : Pl F) (x : F),
      Valued.v (algebraMap F (u.adicCompletion F) x) = u.valuation F x := fun F _ _ u x =>
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u x
  have he : (un w).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (un w).ne_bot
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (un w).asIdeal w.asIdeal (un w).ne_bot] at he
  have key : ∀ x : Lp L, P.φ (un w) w rfl (cv (un w) x) ∈ w.adicCompletionIntegers L ↔
      cv (un w) x ∈ (un w).adicCompletionIntegers (Lp L) := by
    intro x
    have h1 := hval (Lp L) (un w) x
    have h2 := hval L w (algebraMap (Lp L) L x)
    rw [P.φ_alg, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, cv, h1, h2,
      ← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L (un w) w x]
    first
      | exact pow_le_one_iff he
      | exact pow_le_one_iff_of_nonneg zero_le' he
      | exact pow_le_one_iff_of_nonneg (zero_le' (a := _)) he
  have hd : DenseRange (cv (un w)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (Lp L) (un w)
  have hc := P.φ_cont (un w) w rfl
  have o1 : IsClopen ((P.φ (un w) w rfl) ⁻¹' (w.adicCompletionIntegers L : Set (Kw w))) :=
    (Valued.isClopen_integer (Kw w)).preimage hc
  have o2 : IsClopen ((un w).adicCompletionIntegers (Lp L) : Set (Kv (un w))) :=
    Valued.isClopen_integer (Kv (un w))
  constructor
  · intro ha
    by_contra hb
    obtain ⟨x, hx⟩ := hd.exists_mem_open (o1.isOpen.inter o2.compl.isOpen) ⟨a, ha, hb⟩
    exact hx.2 ((key x).1 hx.1)
  · intro ha
    by_contra hb
    obtain ⟨x, hx⟩ := hd.exists_mem_open (o2.isOpen.inter o1.compl.isOpen) ⟨a, ha, hb⟩
    exact hx.2 ((key x).2 hx.1)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.RhoBij
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)
open scoped TensorProduct
open GroundTheory.Global.SemiLocal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.V.Z.Sym.Dict.Br

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

private theorem lies {v : Pl (Lp L)} {w : Plc L} (h : un w = v) : w.asIdeal.LiesOver v.asIdeal := by
  subst h
  exact ⟨rfl⟩

private theorem unOf {v : Pl (Lp L)} {w : Plc L} (h : w.asIdeal.LiesOver v.asIdeal) : un w = v :=
  HeightOneSpectrum.ext h.over.symm

private theorem phi_eq (P : Pre L) (v : Pl (Lp L)) (w : Plc L) (h : un w = v)
    [w.asIdeal.LiesOver v.asIdeal] (a : Kv v) : P.φ v w h a = completionMap v w a := by
  have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 (Lp L)) (Lp L) v
  have key : (P.φ v w h) ∘ algebraMap (Lp L) (Kv v) =
      (completionMap v w) ∘ algebraMap (Lp L) (Kv v) := by
    funext x
    simp only [Function.comp_apply]
    rw [completionMap_algebraMap]
    exact (P.φ_alg v w h x).trans (IsScalarTower.algebraMap_apply (Lp L) L _ x).symm
  exact congrFun (hd.equalizer (P.φ_cont v w h) (continuous_completionMap v w) key) a

private def bas (P : Pre L) : Module.Basis (Fin 2) (Lp L) L :=
  (QuadraticAlgebra.basis P.Δ 0).map (AlgEquiv.ofRingEquiv (f := P.e) P.e_alg).toLinearEquiv

private theorem bas_zero (P : Pre L) : bas P 0 = 1 := by
  have h0 : QuadraticAlgebra.basis P.Δ (0 : Lp L) 0 = 1 := by
    ext <;> simp [QuadraticAlgebra.basis] <;> rfl
  rw [bas, Module.Basis.map_apply, h0]
  simp

private theorem bas_one (P : Pre L) : bas P 1 = P.e QuadraticAlgebra.omega := by
  have h1 : QuadraticAlgebra.basis P.Δ (0 : Lp L) 1 = QuadraticAlgebra.omega := by
    ext <;> simp [QuadraticAlgebra.basis]
  rw [bas, Module.Basis.map_apply, h1]
  rfl

private def tt (P : Pre L) (v : Pl (Lp L)) (x : Lsq (Kv v) (cv v P.Δ)) : Kv v ⊗[Lp L] L :=
  x.re ⊗ₜ 1 + x.im ⊗ₜ P.e QuadraticAlgebra.omega

private theorem tt_apply (P : Pre L) (v : Pl (Lp L)) (x : Lsq (Kv v) (cv v P.Δ)) (p : PlacesOver L v) :
    tensorEquiv L v (tt P v x) p = P.rho v p.1 (unOf p.2) x := by
  simp only [tt, map_add (f := _), tensorEquiv_tmul, map_one, mul_one, Pi.add_apply, Pi.mul_apply]
  haveI := p.2
  show completionMap v p.1 x.re + completionMap v p.1 x.im * algebraMap L _ (P.e QuadraticAlgebra.omega) =
    P.φ v p.1 (unOf p.2) x.re + P.φ v p.1 (unOf p.2) x.im * P.rt p.1
  rw [phi_eq P v p.1 (unOf p.2), phi_eq P v p.1 (unOf p.2)]
  rfl

private theorem tt_eq (P : Pre L) (v : Pl (Lp L)) (x : Lsq (Kv v) (cv v P.Δ)) :
    tt P v x = (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun.symm ![x.re, x.im] := by
  rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
  simp only [Algebra.TensorProduct.basis_apply, bas_zero, bas_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

private theorem tt_inj (P : Pre L) (v : Pl (Lp L)) : Function.Injective (tt P v) := by
  intro x y h
  rw [tt_eq, tt_eq] at h
  have h' := (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun.symm.injective h
  refine QuadraticAlgebra.ext ?_ ?_
  · simpa using congrFun h' 0
  · simpa using congrFun h' 1

private theorem tt_surj (P : Pre L) (v : Pl (Lp L)) : Function.Surjective (tt P v) := by
  intro t
  set c := (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun t
  refine ⟨⟨c 0, c 1⟩, ?_⟩
  rw [tt_eq]
  have hc : (![c 0, c 1] : Fin 2 → Kv v) = c := by
    funext i
    fin_cases i <;> rfl
  simp only [QuadraticAlgebra.re, QuadraticAlgebra.im]
  rw [hc]
  exact (Algebra.TensorProduct.basis (Kv v) (bas P)).equivFun.symm_apply_apply t

end UpperTheory.V.Z.Sym.Dict.Br

end

theorem UpperTheory.V.Z.Sym.Dict.Br.rhoBij :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (P : Pre L), ∀ v : Pl (Lp L), Function.Bijective fun (x : Lsq (Kv v) (cv v P.Δ)) (w : {w : Plc L // un w = v}) => P.rho v w.1 w.2 x := by
  intro L _ _ _ P v
  constructor
  · intro x y hxy
    refine tt_inj P v ((tensorEquiv L v).injective (funext fun p => ?_))
    rw [tt_apply, tt_apply]
    exact congrFun hxy ⟨p.1, unOf p.2⟩
  · intro f
    obtain ⟨t, ht⟩ := (tensorEquiv L v).surjective (fun p => f ⟨p.1, unOf p.2⟩)
    obtain ⟨x, rfl⟩ := tt_surj P v t
    refine ⟨x, funext fun w => ?_⟩
    have := congrFun ht ⟨w.1, lies w.2⟩
    rw [tt_apply] at this
    exact this
end
