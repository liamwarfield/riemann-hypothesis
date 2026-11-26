module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.TranslInv
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.SupportedComposition.ProjectionOfOrbitClosure
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.Imports
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ExistsEquivLs
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.IsCompactSubgroupOf
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusSquares.ModBoundT

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.HomomorphismContinuity.T2SpaceLocalField
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusHeights.StepModH
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.ModulusHeights.ContinuousHom
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker MulAction

open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Orb

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BStep

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

attribute [local instance] t2Sp lcSp tdSp contSMul lcH tdH scH contSMulH

theorem hom_act (t : kˣ) (h : GL (Fin n) k) (q : Sp k n) :
    PositivityTheory.RgUd.TP.Nil.hom t (act h q) = act h (PositivityTheory.RgUd.TP.Nil.hom t q) := by
  simp only [PositivityTheory.RgUd.TP.Nil.hom, act, Prod.mk.injEq, and_true]
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem hom_inv_hom (t : kˣ) (q : Sp k n) :
    PositivityTheory.RgUd.TP.Nil.hom t⁻¹ (PositivityTheory.RgUd.TP.Nil.hom t q) = q := by
  simp only [PositivityTheory.RgUd.TP.Nil.hom, smul_smul]
  simp

theorem continuous_hom (t : kˣ) : Continuous (PositivityTheory.RgUd.TP.Nil.hom (n := n) t) :=
  (continuous_fst.const_smul (t : k)).prodMk continuous_snd

def homE (t : kˣ) : Sp k n ≃ₜ Sp k n where
  toFun := PositivityTheory.RgUd.TP.Nil.hom t
  invFun := PositivityTheory.RgUd.TP.Nil.hom t⁻¹
  left_inv := hom_inv_hom t
  right_inv q := by simpa using hom_inv_hom t⁻¹ q
  continuous_toFun := continuous_hom t
  continuous_invFun := continuous_hom t⁻¹

theorem comp_hom_mem (t : kˣ) {f : Sp k n → ℂ} (hf : f ∈ supportedIn UU) :
    (fun q => f (PositivityTheory.RgUd.TP.Nil.hom t q)) ∈ supportedIn UU := by
  refine ⟨⟨hf.1.1.comp_continuous (homE (n := n) t).continuous, hf.1.2.comp_homeomorph (homE t)⟩, fun q hq => ?_⟩
  have := hf.2 (show PositivityTheory.RgUd.TP.Nil.hom t q ∈ Function.support f from hq)
  exact this

theorem piece_countU (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hξ : InvU Z ξ)
    {C U₁ : Set (Sp k n)} (hC : IsClosed C) (hU₁ : IsOpen U₁) (hU₁UU : U₁ ⊆ UU) {p : Sp k n}
    (hCinv : ∀ h ∈ Gz Z, ∀ q ∈ C, act h q ∈ C)
    (hO : U₁ ∩ C = orb Z p) (hξC : PositivityTheory.RgUd.T.Nil.Orb.SuppU ξ C)
    {J A : Subgroup (GzS Z)} (hJc : IsCompact (J : Set (GzS Z))) (hAo : IsOpen (A : Set (GzS Z))) (hAJ : A ≤ J)
    (hn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A)
    {fJ fA : Sp k n → ℂ} (hfJ : fJ ∈ supportedIn U₁) (hfA : fA ∈ supportedIn U₁)
    (hfJO : ∀ x ∈ orb Z p, fJ x = (orbitPiece J (toT p)).indicator 1 (toT x))
    (hfAO : ∀ x ∈ orb Z p, fA x = (orbitPiece A (toT p)).indicator 1 (toT x)) :
    ξ fJ * ((A ⊓ stabilizer (GzS Z) (toT p)).relIndex (J ⊓ stabilizer (GzS Z) (toT p)) : ℂ) =
      (A.relIndex J : ℂ) * ξ fA := by
  classical
  have hOorb : orbit (GzS Z) (toT p) = orb Z p := Set.ext fun q => mem_orbit_iff' Z (p := p) (q := q)
  have hO' : ((U₁ : Set (SpT k n)) ∩ C) = orbit (GzS Z) (toT p) := by rw [hOorb]; exact hO
  have hOl : IsLocallyClosed (orbit (GzS Z) (toT p)) := ⟨U₁, C, hU₁, hC, hO'.symm⟩
  obtain ⟨𝒮, -, h𝒮, hsum⟩ := exists_finset_orbitPiece (X := SpT k n) hOl hJc hAo hAJ hn (mem_orbit_self (toT p))
  choose! j hjJ hjS using h𝒮
  have hPsub : ∀ B : Subgroup (GzS Z), ∀ x, toT x ∈ orbitPiece B (toT p) → x ∈ orb Z p := by
    intro B x hx
    exact (mem_orbit_iff' Z).1 (orbitPiece_subset_orbit (mem_orbit_self (toT p)) hx)
  have hfAUU : fA ∈ supportedIn UU := supportedIn_mono hU₁UU hfA
  have htr : ∀ S ∈ 𝒮, ξ (fun q => fA (act (((j S)⁻¹ : GzS Z) : GL (Fin n) k) q)) = ξ fA := by
    intro S _
    exact hξ _ ((j S)⁻¹).2 fA hfAUU
  have hsumξ : ξ fJ = ∑ S ∈ 𝒮, ξ (fun q => fA (act (((j S)⁻¹ : GzS Z) : GL (Fin n) k) q)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    refine xi_eq hξC (supportedIn_mono hU₁UU hfJ)
      (Submodule.sum_mem _ fun S _ => comp_act_memUU ((j S)⁻¹ : GzS Z).1 hfAUU) fun x hx => ?_
    rw [lift_on_C' hO (hPsub J) hfJ hfJO x hx, hsum (toT x), Finset.sum_apply]
    refine Finset.sum_congr rfl fun S hS => ?_
    have hx' : act (((j S)⁻¹ : GzS Z) : GL (Fin n) k) x ∈ C := hCinv _ ((j S)⁻¹).2 x hx
    rw [lift_on_C' hO (hPsub A) hfA hfAO _ hx']
    conv_lhs => rw [hjS S hS]
    by_cases hxS : toT (act (((j S)⁻¹ : GzS Z) : GL (Fin n) k) x) ∈ orbitPiece A (toT p)
    · rw [Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 (show (j S)⁻¹ • toT x ∈ _ from hxS)),
        Set.indicator_of_mem hxS]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => hxS (Set.mem_smul_set_iff_inv_smul_mem.1 h')),
        Set.indicator_of_notMem hxS]
  have hcard : ξ fJ = (𝒮.card : ℂ) * ξ fA := by
    rw [hsumξ, Finset.sum_congr rfl htr, Finset.sum_const, nsmul_eq_mul]
  have hset : ((𝒮 : Set (Set (SpT k n)))) =
      (fun i : GzS Z => i • orbitPiece A (toT p)) '' (J : Set (GzS Z)) := by
    ext P
    constructor
    · intro hP
      exact ⟨j P, hjJ P hP, (hjS P hP).symm⟩
    · rintro ⟨i, hi, rfl⟩
      have hx : i • toT p ∈ orbitPiece J (toT p) := ⟨i, hi, rfl⟩
      have h1 := hsum (i • toT p)
      rw [Set.indicator_of_mem hx] at h1
      obtain ⟨S, hS, hiS⟩ : ∃ S ∈ 𝒮, i • toT p ∈ S := by
        by_contra hcon
        push Not at hcon
        rw [Finset.sum_eq_zero (fun S hS => Set.indicator_of_notMem (hcon S hS) _)] at h1
        exact one_ne_zero h1
      have e1 : i • orbitPiece A (toT p) = orbitPiece A (i • toT p) :=
        smul_orbitPiece (hn i hi) (fun a ha => by simpa using hn i⁻¹ (J.inv_mem hi) a ha) _
      have e2 : S = orbitPiece A (j S • toT p) := (hjS S hS).trans
        (smul_orbitPiece (hn _ (hjJ S hS)) (fun a ha => by simpa using hn _ (J.inv_mem (hjJ S hS)) a ha) _)
      have e3 : orbitPiece A (i • toT p) = orbitPiece A (j S • toT p) :=
        orbitPiece_eq_of_mem (e2 ▸ hiS)
      show i • orbitPiece A (toT p) ∈ (𝒮 : Set (Set (SpT k n)))
      rw [Finset.mem_coe, e1, e3, ← e2]
      exact hS
  have hc := count J A hAJ hn (toT p)
  change Nat.card ((fun i : GzS Z => i • orbitPiece A (toT p)) '' (J : Set (GzS Z))) * _ = _ at hc
  rw [← hset, Nat.card_coe_set_eq, Set.ncard_coe_finset] at hc
  rw [hcard, mul_assoc, mul_comm (ξ fA), ← mul_assoc]
  exact_mod_cast congrArg (fun N : ℕ => (N : ℂ) * ξ fA) hc

end PositivityTheory.RgUd.TP.Nil.Orb
end
end

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker MulAction

open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Orb

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BStep

attribute [local instance] t2Sp lcSp tdSp contSMul lcH tdH scH contSMulH

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def StepModH : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ (t : kˣ) (p : Sp k n) (g : GL (Fin n) k),
    g ∈ Gz Z → act g p = PositivityTheory.RgUd.TP.Nil.hom t p → p.2 ≠ 0 → ∀ (K : Subgroup (GL (Fin n) k)), K ≤ GzS Z → IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) →
    IsCompact (K : Set (GL (Fin n) k)) → ∀ L : Subgroup (GL (Fin n) k), IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) →
    L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom → L.Normal' K → L.Normal' (K.map (MulAut.conj g).toMonoidHom) →
    ∀ (C U : Set (Sp k n)), IsClosed C → IsOpen U → U ∩ C = orb Z p →
    (∀ h ∈ Gz Z, ∀ q ∈ C, act h q ∈ C) → (∀ q ∈ C, PositivityTheory.RgUd.TP.Nil.hom t q ∈ C) → ∀ ξ, PositivityTheory.RgUd.TP.Nil.InvU Z ξ →
      PositivityTheory.RgUd.TP.Nil.SuppU ξ C →
      PositivityTheory.RgUd.TP.Nil.SuppU (PositivityTheory.RgUd.TP.Nil.pullH t ξ - ((modul (stab Z p) K L g : ℝ) : ℂ) • ξ) (C \ U)

theorem stepH : StepModH k := by
  intro n Z _hZ t p g hg hgp hp2 K hKG hKo hKc L hLo hLK hLn hLn' C U hC hU hUC hCinv hCsig ξ hξ hξC
  classical
  have hξC : PositivityTheory.RgUd.T.Nil.Orb.SuppU ξ C := hξC
  have : T2Space (SpT k n) := t2Sp
  have : LocallyCompactSpace (SpT k n) := lcSp
  have : TotallyDisconnectedSpace (SpT k n) := tdSp
  have : ContinuousSMul (GL (Fin n) k) (SpT k n) := contSMul
  have : LocallyCompactSpace (GzS Z) := lcH Z
  have : TotallyDisconnectedSpace (GzS Z) := tdH Z
  have : SigmaCompactSpace (GzS Z) := scH Z
  have : ContinuousSMul (GzS Z) (SpT k n) := contSMulH Z

  let gH : GzS Z := ⟨g, hg⟩
  set K' : Subgroup (GL (Fin n) k) := K.map (MulAut.conj g).toMonoidHom with hK'def
  have hK'G : K' ≤ GzS Z := by
    rintro _ ⟨x, hx, rfl⟩
    exact (GzS Z).mul_mem ((GzS Z).mul_mem hg (hKG hx)) ((GzS Z).inv_mem hg)
  set KH := K.subgroupOf (GzS Z) with hKHdef
  set K'H := K'.subgroupOf (GzS Z) with hK'Hdef
  set LH := L.subgroupOf (GzS Z) with hLHdef
  have hKHc : IsCompact (KH : Set (GzS Z)) := isCompact_subgroupOf Z hKG hKc
  have hKHo : IsOpen (KH : Set (GzS Z)) := hKo
  have hLHo : IsOpen (LH : Set (GzS Z)) := hLo
  have hK'H : K'H = KH.map (MulAut.conj gH).toMonoidHom := by
    ext x
    simp only [hK'Hdef, hKHdef, Subgroup.mem_subgroupOf, Subgroup.mem_map, hK'def]
    constructor
    · rintro ⟨y, hy, hyx⟩
      refine ⟨⟨y, hKG hy⟩, hy, Subtype.ext ?_⟩
      simpa [MulAut.conj_apply] using hyx
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp [MulAut.conj_apply, gH]⟩
  have hK'Hco := isCompact_isOpen_map_conj hKHc hKHo gH
  rw [← hK'H] at hK'Hco
  have hLKH : LH ≤ KH := fun x hx => (hLK hx).1
  have hLK'H : LH ≤ K'H := fun x hx => (hLK hx).2
  have hLHc : IsCompact (LH : Set (GzS Z)) :=
    hKHc.of_isClosed_subset (LH.isClosed_of_isOpen hLHo) hLKH
  have hnK : ∀ j ∈ KH, ∀ a ∈ LH, j * a * j⁻¹ ∈ LH := fun j hj a ha => hLn _ hj _ ha
  have hnK' : ∀ j ∈ K'H, ∀ a ∈ LH, j * a * j⁻¹ ∈ LH := fun j hj a ha => hLn' _ hj _ ha

  let U₁ : Set (Sp k n) := {q | q.2 ≠ 0 ∧ ∃ h ∈ Gz Z, act h q ∈ U}
  have hU₁o : IsOpen U₁ := by
    have e : U₁ = UU ∩ ⋃ h : GzS Z, (fun q => act (h : GL (Fin n) k) q) ⁻¹' U := by
      ext q
      simp only [U₁, UU, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨h2, h, hh, hq⟩
        exact ⟨h2, ⟨h, hh⟩, hq⟩
      · rintro ⟨h2, h, hq⟩
        exact ⟨h2, h.1, h.2, hq⟩
    rw [e]
    refine isOpen_UU.inter (isOpen_iUnion fun h => hU.preimage ?_)
    exact (continuous_const_smul (h : GL (Fin n) k) : Continuous fun q : SpT k n => (h : GL (Fin n) k) • q)
  have hU₁UU : U₁ ⊆ UU := fun q hq => hq.1
  have hU₁inv : ∀ h : GzS Z, ∀ x : SpT k n, x ∈ (U₁ : Set (SpT k n)) → h • x ∈ (U₁ : Set (SpT k n)) := by
    rintro h x ⟨hx2, h', hh', hx⟩
    refine ⟨act_snd_ne (h : GL (Fin n) k) hx2, h' * (h : GL (Fin n) k)⁻¹,
      (GzS Z).mul_mem hh' ((GzS Z).inv_mem h.2), ?_⟩
    have e : act (h' * (h : GL (Fin n) k)⁻¹) (act (h : GL (Fin n) k) (x : Sp k n)) = act h' x := by
      rw [act_mul]
      exact congrArg (act h') (act_inv_act _ _)
    change act (h' * (h : GL (Fin n) k)⁻¹) (act (h : GL (Fin n) k) (x : Sp k n)) ∈ U
    rw [e]
    exact hx
  have hU₁oT : IsOpen (X := SpT k n) U₁ := hU₁o
  have hCT : IsClosed (X := SpT k n) C := hC
  have horb : orb Z p ⊆ U ∩ C := by rw [hUC]
  have hO₁ : U₁ ∩ C = orb Z p := by
    ext q
    constructor
    · rintro ⟨⟨-, h, hh, hqU⟩, hqC⟩
      have hm : act h q ∈ orb Z p := hUC ▸ ⟨hqU, hCinv h hh q hqC⟩
      obtain ⟨g', hg', e⟩ := hm
      refine ⟨h⁻¹ * g', (GzS Z).mul_mem ((GzS Z).inv_mem hh) hg', ?_⟩
      rw [act_mul, e, act_inv_act]
    · intro hq
      have hq' := horb hq
      obtain ⟨h, _, rfl⟩ := hq
      exact ⟨⟨act_snd_ne h hp2, 1, (GzS Z).one_mem, by rw [act_one]; exact hq'.1⟩, hq'.2⟩
  have hOorb : orbit (GzS Z) (toT p) = orb Z p := Set.ext fun q => mem_orbit_iff' Z (p := p) (q := q)
  have hO₁' : ((U₁ : Set (SpT k n)) ∩ C) = orbit (GzS Z) (toT p) := by rw [hOorb]; exact hO₁
  have hp0 : toT p ∈ orbit (GzS Z) (toT p) := mem_orbit_self (toT p)
  have hlift : ∀ B : Subgroup (GzS Z), IsCompact (B : Set (GzS Z)) → IsOpen (B : Set (GzS Z)) →
      ∃ f ∈ supportedIn U₁, ∀ x ∈ orb Z p, f x = (orbitPiece B (toT p)).indicator 1 (toT x) := by
    intro B hBc hBo
    obtain ⟨f, hf, hfO⟩ := exists_lift_orbit_piece (X := SpT k n) hU₁oT hCT hO₁' hBc hBo hp0
    exact ⟨f, hf, fun x hx => hfO (toT x) (hOorb ▸ hx)⟩
  obtain ⟨f₀, hf₀, hf₀O⟩ := hlift KH hKHc hKHo
  obtain ⟨f₁, hf₁, hf₁O⟩ := hlift K'H hK'Hco.1 hK'Hco.2
  obtain ⟨fL, hfL, hfLO⟩ := hlift LH hLHc hLHo
  have hPsub : ∀ B : Subgroup (GzS Z), ∀ x, toT x ∈ orbitPiece B (toT p) → x ∈ orb Z p := by
    intro B x hx
    exact (mem_orbit_iff' Z).1 (orbitPiece_subset_orbit hp0 hx)

  set m : ℂ := ((modul (stab Z p) K L g : ℝ) : ℂ) with hm
  set ψ := PositivityTheory.RgUd.TP.Nil.pullH t ξ - m • ξ with hψdef
  have hψ : ∀ f, ψ f = ξ (fun q => f (PositivityTheory.RgUd.TP.Nil.hom t q)) - m * ξ f := fun f => rfl

  have hV : ∀ v ∈ supportedIn UU, (∀ q ∈ C, v q = 0) → ψ v = 0 := by
    intro v hv hvC
    rw [hψ, hξC v hv hvC, hξC _ (comp_hom_mem t hv) (fun q hq => hvC _ (hCsig q hq))]
    simp

  have hR : relSpan (X := SpT k n) (1 : GzS Z →* ℂ) U₁ ≤ LinearMap.ker ψ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, f, hf, rfl⟩
    have hfUU : f ∈ supportedIn UU := supportedIn_mono hU₁UU hf
    simp only [MonoidHom.one_apply, one_smul]
    change ψ (transl (X := SpT k n) h f - f) = 0
    have e1 : ξ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)) = ξ f :=
      hξ _ (h⁻¹).2 f hfUU
    have e2 : ξ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) (PositivityTheory.RgUd.TP.Nil.hom t q))) = ξ (fun q => f (PositivityTheory.RgUd.TP.Nil.hom t q)) := by
      have := hξ _ (h⁻¹).2 (fun q => f (PositivityTheory.RgUd.TP.Nil.hom t q)) (comp_hom_mem t hfUU)
      rw [← this]
      congr 1
      funext q
      rw [hom_act t]
    have key : ψ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)) = ψ f := by
      rw [hψ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)), hψ f, e1]
      exact congrArg (· - m * ξ f) e2
    have hs : ψ (fun q : Sp k n => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q) - f q) =
        ψ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)) - ψ f :=
      ψ.map_sub (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)) f
    change ψ (fun q : Sp k n => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q) - f q) = 0
    rw [hs, key, sub_self]

  have hsig_piece : ∀ q : Sp k n, toT (PositivityTheory.RgUd.TP.Nil.hom t q) ∈ orbitPiece KH (toT p) ↔
      toT (act g q) ∈ orbitPiece K'H (toT p) := by
    intro q
    constructor
    · rintro ⟨κ, hκ, e⟩
      change act (κ : GL (Fin n) k) p = PositivityTheory.RgUd.TP.Nil.hom t q at e
      have hq : q = act ((κ : GL (Fin n) k) * g⁻¹) p := by
        have h1 : PositivityTheory.RgUd.TP.Nil.hom t (act ((κ : GL (Fin n) k) * g⁻¹) p) = PositivityTheory.RgUd.TP.Nil.hom t q := by
          rw [hom_act t, ← hgp, ← act_mul,
            inv_mul_cancel_right, e]
        have := congrArg (PositivityTheory.RgUd.TP.Nil.hom t⁻¹) h1
        rw [hom_inv_hom t, hom_inv_hom t] at this
        exact this.symm
      refine ⟨⟨g * (κ : GL (Fin n) k) * g⁻¹, hK'G ⟨κ, hκ, rfl⟩⟩, ⟨κ, hκ, rfl⟩, ?_⟩
      change act (g * (κ : GL (Fin n) k) * g⁻¹) p = act g q
      rw [hq, ← act_mul, mul_assoc]
    · rintro ⟨κ', ⟨κ, hκ, hκe⟩, e⟩
      change act (κ' : GL (Fin n) k) p = act g q at e
      have hκ' : (κ' : GL (Fin n) k) = g * κ * g⁻¹ := by simpa [MulAut.conj_apply] using hκe.symm
      have hq : q = act (κ * g⁻¹) p := by
        have := congrArg (act g⁻¹) e
        rw [act_inv_act, ← act_mul, hκ'] at this
        rw [← this]
        congr 1
        group
      refine ⟨⟨κ, hKG hκ⟩, hκ, ?_⟩
      change act κ p = PositivityTheory.RgUd.TP.Nil.hom t q
      rw [hq, hom_act t, ← hgp, ← act_mul,
        inv_mul_cancel_right]
  have hf₀UU : f₀ ∈ supportedIn UU := supportedIn_mono hU₁UU hf₀
  have hf₁UU : f₁ ∈ supportedIn UU := supportedIn_mono hU₁UU hf₁
  have hX1 : ξ (fun q => f₀ (PositivityTheory.RgUd.TP.Nil.hom t q)) = ξ f₁ := by
    rw [← hξ g hg f₁ hf₁UU]
    refine xi_eq hξC (comp_hom_mem t hf₀UU) (comp_act_memUU g hf₁UU) fun q hq => ?_
    rw [lift_on_C' hO₁ (hPsub KH) hf₀ hf₀O _ (hCsig q hq),
      lift_on_C' hO₁ (hPsub K'H) hf₁ hf₁O _ (hCinv g hg q hq)]
    by_cases h : toT (PositivityTheory.RgUd.TP.Nil.hom t q) ∈ orbitPiece KH (toT p)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hsig_piece q).1 h)]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hsig_piece q).2 h'))]

  have hc0 := piece_countU Z hξ hC hU₁o hU₁UU hCinv hO₁ hξC hKHc hLHo hLKH hnK hf₀ hfL hf₀O hfLO
  have hc1 := piece_countU Z hξ hC hU₁o hU₁UU hCinv hO₁ hξC hK'Hco.1 hLHo hLK'H hnK' hf₁ hfL hf₁O hfLO
  have ha0 : LH.relIndex KH ≠ 0 := relIndex_ne_zero hKHc hLHo
  have ha1 : LH.relIndex K'H ≠ 0 := relIndex_ne_zero hK'Hco.1 hLHo
  have hb0 := right_ne_zero_of_mul ((count KH LH hLKH hnK (toT p)).symm ▸ ha0)
  have hb1 := right_ne_zero_of_mul ((count K'H LH hLK'H hnK' (toT p)).symm ▸ ha1)
  obtain ⟨r0, s0⟩ := relIndex_H Z p (L := L) hKG
  obtain ⟨r1, s1⟩ := relIndex_H Z p (L := L) hK'G
  have hmodul : modul (stab Z p) K L g =
      ((LH.relIndex K'H : ℝ) / ((LH ⊓ stabilizer (GzS Z) (toT p)).relIndex (K'H ⊓ stabilizer (GzS Z) (toT p)) : ℝ)) /
      ((LH.relIndex KH : ℝ) / ((LH ⊓ stabilizer (GzS Z) (toT p)).relIndex (KH ⊓ stabilizer (GzS Z) (toT p)) : ℝ)) := by
    rw [modul, ← hK'def, r0, s0, r1, s1]
  have hP : ψ f₀ = 0 := by
    rw [hψ, hX1, hm, hmodul]
    have ha0' : (LH.relIndex KH : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha0
    have ha1' : (LH.relIndex K'H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ha1
    have hb0' : ((LH ⊓ stabilizer (GzS Z) (toT p)).relIndex (KH ⊓ stabilizer (GzS Z) (toT p)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 hb0
    have hb1' : ((LH ⊓ stabilizer (GzS Z) (toT p)).relIndex (K'H ⊓ stabilizer (GzS Z) (toT p)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 hb1
    have e0 := eq_div_of_mul_eq hb0' hc0
    have e1 := eq_div_of_mul_eq hb1' hc1
    rw [e0, e1]
    push_cast
    field_simp
    ring

  have hWU : relSpan (X := SpT k n) (1 : GzS Z →* ℂ) U₁ ⊔ Submodule.span ℂ {f₀} ≤ supportedIn (X := SpT k n) U₁ :=
    sup_le (relSpan_le_supportedIn _ hU₁inv) ((Submodule.span_singleton_le_iff_mem _ _).2 hf₀)
  have hle := supportedIn_le_of_base (X := SpT k n) hU₁oT hCT hO₁' hU₁inv (1 : GzS Z →* ℂ) hWU le_sup_left KH hKHc hKHo
    (fun _ _ => rfl) f₀ (fun x hx => hf₀O x (hOorb ▸ hx))
    (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self f₀)))
  have hker : supportedIn (X := SpT k n) U₁ ≤ LinearMap.ker ψ :=
    hle.trans (sup_le (sup_le hR ((Submodule.span_singleton_le_iff_mem _ _).2 hP))
      fun v hv => hV v (supportedIn_mono hU₁UU hv.1) hv.2)

  intro f hf hfCU
  have hKc' : IsCompact (X := SpT k n) (C ∩ Function.support f) := (isCompact_support hf.1).inter_left hC
  have hsub : C ∩ Function.support f ⊆ U₁ := by
    rintro q ⟨hqC, hqf⟩
    have hqU : q ∈ U := by
      by_contra h
      exact hqf (hfCU q ⟨hqC, h⟩)
    have hq : q ∈ orb Z p := hUC ▸ ⟨hqU, hqC⟩
    rw [← hO₁] at hq
    exact hq.1
  obtain ⟨B, hBc, hBo, hKB, hBU⟩ := exists_isCompact_isOpen_between (X := SpT k n) hKc' hU₁oT hsub
  set f₂ : Sp k n → ℂ := fun x => B.indicator 1 (toT x) * f x with hf₂def
  have hf₂ : f₂ ∈ supportedIn (X := SpT k n) U₁ := by
    refine ⟨(indicator_mul_mem (X := SpT k n) ⟨hBc.isClosed, hBo⟩ hf).1, fun x hx => ?_⟩
    have hxB : toT x ∈ B := by
      by_contra h
      have h0 : B.indicator 1 (toT x) = (0 : ℂ) := Set.indicator_of_notMem h _
      exact hx (show B.indicator 1 (toT x) * f x = 0 by rw [h0, zero_mul])
    exact hBU hxB
  have e : f = f₂ + (f - f₂) := by abel
  change ψ f = 0
  rw [e, map_add (f := _), hker hf₂, zero_add]
  refine hV _ (Submodule.sub_mem _ hf (supportedIn_mono hU₁UU hf₂)) fun q hq => ?_
  by_cases hfq : f q = 0
  · simp [f₂, hfq]
  · have hqB : toT q ∈ B := hKB ⟨hq, hfq⟩
    simp [f₂, Set.indicator_of_mem hqB]

end PositivityTheory.RgUd.TP.Nil.Orb
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.QuasiOrbits.OrbitRepresentatives.Reps0
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.TP.Nil.Orb

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb PositivityTheory.RgUd.T.Nil.Orb.BReps

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Reps0 : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∃ s : Finset (Sp k n),
    (∀ p ∈ s, p.1 ∈ Bz Z ∧ IsNilpotent p.1 ∧ p.2 ≠ 0 ∧
      ∃ (P : GL (Fin n) k) (w : Fin n → ℤ), (∀ t : kˣ,
        let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * p.1 = (t : k) • (p.1 * g) ∧ g *ᵥ p.2 = p.2) ∧
      ∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * p.1 = p.1 * a →
        ∃ u : Fin n → k, a *ᵥ p.2 = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) ∧
    ∀ x ∈ Bz Z, IsNilpotent x → ∀ v : Fin n → k, v ≠ 0 → ∃ p ∈ s, (x, v) ∈ orb Z p

theorem repsP : PositivityTheory.RgUd.T.Nil.Orb.Reps (k := k) := by
  classical
  intro n Z hZ c hc
  obtain ⟨M, _, L, _, hL, R, o, hF⟩ := PositivityTheory.RgUd.T.Nil.Orb.BReps.exists_frames Z hZ.1 hZ.2
  haveI := hL
  let typ : ∀ (N : Matrix (Fin n) (Fin n) k) (v : Fin n → k),
      PositivityTheory.RgUd.T.Nil.Orb.BReps.Frame Z M L R o N v →
      (M → Fin (n + 1) → Fin (n + 1) → Fin (n + 1)) := fun N v F m ℓ σ =>
    ⟨Nat.card {a : F.ι m // F.l m a = (ℓ : ℕ) ∧ F.s m a = (σ : ℕ)}, by
      haveI := F.fι m
      exact Nat.lt_succ_of_le ((Finite.card_subtype_le _).trans (F.card_le m))⟩
  let Good : (M → Fin (n + 1) → Fin (n + 1) → Fin (n + 1)) → Prop := fun θ =>
    ∃ q : Sp k n, q.1 ∈ Bz Z ∧ IsNilpotent (q.1 - c) ∧ q.2 ≠ 0 ∧
      ∃ F : PositivityTheory.RgUd.T.Nil.Orb.BReps.Frame Z M L R o (q.1 - c) q.2, typ _ _ F = θ
  refine ⟨(Finset.univ.filter Good).image
    (fun θ => if h : Good θ then Classical.choose h else ((0 : Matrix (Fin n) (Fin n) k), (0 : Fin n → k))),
    ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨θ, hθ, rfl⟩ := hp
    have hG : Good θ := (Finset.mem_filter.1 hθ).2
    simp only [dif_pos hG]
    obtain ⟨h1, h2, h3, F, -⟩ := Classical.choose_spec hG
    refine ⟨h1, h2, h3, ?_⟩
    obtain ⟨P, w, hPw, hA⟩ := PositivityTheory.RgUd.T.Nil.Orb.BReps.grade_of_frame F
    refine ⟨P, w, hPw, ?_⟩
    intro a ha hap
    apply hA a ha
    have hca : c * a = a * c := ha c hc
    rw [mul_sub, sub_mul, hap, hca]
  · intro x hx hnil v hv
    have hcomm : ∀ z ∈ Z, z * (x - c) = (x - c) * z := by
      intro z hz
      rw [mul_sub, sub_mul, hx z hz, hZ.1 z hz c hc]
    obtain ⟨F⟩ := hF (x - c) hcomm hnil v
    have hG : Good (typ _ _ F) := ⟨(x, v), hx, hnil, hv, F, rfl⟩
    refine ⟨Classical.choose hG, ?_, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨typ _ _ F, Finset.mem_filter.2 ⟨Finset.mem_univ _, hG⟩, dif_pos hG⟩
    · obtain ⟨h1, h2, h3, F', hF'⟩ := Classical.choose_spec hG
      obtain ⟨g, hgZ, hgN, hgv⟩ := PositivityTheory.RgUd.T.Nil.Orb.BReps.conj_of_frames F' F (by
        intro m ℓ σ hℓ hσ
        have e := congrFun (congrFun (congrFun hF' m) ⟨ℓ, Nat.lt_succ_of_le hℓ⟩)
          ⟨σ, Nat.lt_succ_of_le hσ⟩
        exact congrArg Fin.val e)
      refine ⟨g, hgZ, ?_⟩
      have hcg : c * (g : Matrix (Fin n) (Fin n) k) = g * c := hgZ c hc
      have e : (g : Matrix (Fin n) (Fin n) k) * (Classical.choose hG).1 = x * g := by
        have h4 := hgN
        rw [mul_sub, sub_mul, ← hcg] at h4
        exact sub_left_inj.mp h4
      show ((g : Matrix (Fin n) (Fin n) k) * (Classical.choose hG).1 *
          ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k),
          (g : Matrix (Fin n) (Fin n) k) *ᵥ (Classical.choose hG).2) = (x, v)
      rw [e, mul_assoc, Units.mul_inv, mul_one, hgv]

theorem reps0 : Reps0 k := by
  intro n Z hZ
  obtain ⟨s, hs1, hs2⟩ := repsP k n Z hZ 0 Z.zero_mem
  refine ⟨s, ?_, ?_⟩
  · intro p hp
    simpa using hs1 p hp
  · intro x hx hnil v hv
    exact hs2 x hx (by simpa using hnil) v hv

end PositivityTheory.RgUd.TP.Nil.Orb
end
end

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil Set Polynomial

namespace PositivityTheory.RgUd.TP.Nil.Orb.Asm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil
open PositivityTheory.RgUd.T.Nil.Orb (GzS orb stab modul act_mul act_one)
open PositivityTheory.RgUd.T.Nil.Orb.Oasm (exists_open_orbit isClosed_Bz isNilpotent_iff_pow comp_mem_supportedIn orb_subset_UU
  action_mem_orbit_closure)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

local instance t2SpaceLocalField : T2Space k := GlobalTheory.SplitWeil.t2Space k


variable (k) in
def ModH : Prop :=
  TraceForm k → ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → 0 < dB0 Z → ∀ (p : Sp k n) (P : GL (Fin n) k)
    (w : Fin n → ℤ), p.1 ∈ Bz Z → IsNilpotent p.1 → p.2 ≠ 0 →
    (∀ t : kˣ, let g : Matrix (Fin n) (Fin n) k := P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val
        (∀ a ∈ Z, a * g = g * a) ∧ g * p.1 = (t : k) • (p.1 * g) ∧ g *ᵥ p.2 = p.2) →
    (∀ a : Matrix (Fin n) (Fin n) k, (∀ z ∈ Z, z * a = a * z) → a * p.1 = p.1 * a →
        ∃ u : Fin n → k, a *ᵥ p.2 = P.val *ᵥ u ∧ ∀ i, w i < 0 → u i = 0) →
    ∃ a : ℝ, 2 * a < dB0 Z ∧ ∀ t : kˣ, nabs k t < 1 → ∃ (K L : Subgroup (GL (Fin n) k)) (g : GL (Fin n) k),
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) ∧
      IsCompact (K : Set (GL (Fin n) k)) ∧
      IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) ∧ L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧
      L.Normal' K ∧ L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      g.val = P.val * diagonal (fun i => ((t ^ w i : kˣ) : k)) * P⁻¹.val ∧
      modul (stab Z p) K L g = (nabs k t)⁻¹ ^ a

section Hom

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem hom_hom (t : kˣ) (p : Sp k n) : hom t⁻¹ (hom t p) = p := by
  refine Prod.ext ?_ rfl
  simp [hom, smul_smul]

theorem continuous_hom (t : kˣ) : Continuous (hom (n := n) t) :=
  (continuous_fst.const_smul (t : k)).prodMk continuous_snd

def homH (t : kˣ) : Sp k n ≃ₜ Sp k n where
  toFun := hom t
  invFun := hom t⁻¹
  left_inv p := hom_hom t p
  right_inv p := by simpa using hom_hom t⁻¹ p
  continuous_toFun := continuous_hom t
  continuous_invFun := continuous_hom t⁻¹

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem hom_act (t : kˣ) (g : GL (Fin n) k) (p : Sp k n) : hom t (act g p) = act g (hom t p) := by
  simp only [hom, act]
  refine Prod.ext ?_ rfl
  simp only [mul_smul_comm, smul_mul_assoc]

theorem comp_hom_mem (t : kˣ) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) :
    (fun p => f (hom t p)) ∈ supportedIn (UU : Set (Sp k n)) :=
  comp_mem_supportedIn (homH t) hf

theorem invU_pullH (t : kˣ) {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hξ : InvU Z ξ) : InvU Z (pullH t ξ) := by
  intro g hg f hf
  show ξ (fun p => f (act g (hom t p))) = ξ (fun p => f (hom t p))
  have e : (fun p => f (act g (hom t p))) = fun p => (fun q => f (hom t q)) (act g p) := by
    funext p; show f (act g (hom t p)) = f (hom t (act g p)); rw [hom_act]
  rw [e]
  exact hξ g hg _ (comp_hom_mem t hf)

theorem invU_sub_smul {ξ η : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h1 : InvU Z ξ) (h2 : InvU Z η) (a : ℂ) : InvU Z (ξ - a • η) := by
  intro g hg f hf
  simp [h1 g hg f hf, h2 g hg f hf]

theorem kills_pullH (t : kˣ) {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hξ : Kills ξ UU) : Kills (pullH t ξ) UU :=
  fun f hf => hξ _ (comp_hom_mem t hf)

theorem kills_aevalH (t : kˣ) {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hξ : Kills ξ UU) (Q : ℂ[X]) :
    Kills (aeval (pullH (n := n) t) Q ξ) UU := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => intro f hf; simp [hp f hf, hq f hf]
  | monomial m a =>
    intro f hf
    have key : ∀ m : ℕ, Kills (((pullH (n := n) t) ^ m : Module.End ℂ _) ξ) UU := by
      intro m
      induction m with
      | zero => simpa using hξ
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact kills_pullH t ih
    simp [aeval_monomial, key m f hf]

theorem aeval_X_subH (t : kˣ) (a : ℂ) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) :
    aeval (pullH (n := n) t) (X - Polynomial.C a) ξ = pullH t ξ - a • ξ := by
  simp [Algebra.algebraMap_eq_smul_one]

theorem kills_of_suppU {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} {D : Set (Sp k n)} (hD : D ∩ UU = ∅) (h : SuppU ξ D) :
    Kills ξ UU := by
  intro f hf
  refine h f hf fun q hq => ?_
  by_contra hfq
  have : q ∈ D ∩ UU := ⟨hq, hf.2 hfq⟩
  rw [hD] at this
  exact this

theorem isClosed_NB : IsClosed (NB Z ×ˢ (Set.univ : Set (Fin n → k))) := by
  have : NB Z = Bz Z ∩ {x | x ^ n = 0} := by
    ext x; simp [NB, isNilpotent_iff_pow]
  rw [this]
  exact (isClosed_Bz.inter (isClosed_eq (continuous_id.pow n) continuous_const)).prod isClosed_univ

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem act_mem_NB (hZ : CR Z) {g : GL (Fin n) k} (hg : g ∈ Gz Z) {q : Sp k n}
    (hq : q ∈ NB Z ×ˢ (Set.univ : Set (Fin n → k))) : act g q ∈ NB Z ×ˢ (Set.univ : Set (Fin n → k)) := by
  have h := action_mem_orbit_closure hZ (zero_mem Z) hg (q := q) ⟨hq.1.1, by simpa using hq.1.2⟩
  exact ⟨⟨h.1, by simpa using h.2⟩, mem_univ _⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem hom_mem_NB (t : kˣ) {q : Sp k n} (hq : q ∈ NB Z ×ˢ (Set.univ : Set (Fin n → k))) :
    hom t q ∈ NB Z ×ˢ (Set.univ : Set (Fin n → k)) := by
  refine ⟨⟨fun a ha => ?_, hq.1.2.smul _⟩, mem_univ _⟩
  show a * ((t : k) • q.1) = (t : k) • q.1 * a
  rw [mul_smul_comm, smul_mul_assoc, hq.1.1 a ha]

end Hom

section Main

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem main_ind (h4 : StepModH k) (hZ : CR Z) (t : kˣ) (mm : Sp k n → ℂ) (s : Finset (Sp k n))
    (hs : ∀ p ∈ s, p.2 ≠ 0 ∧ ∃ (K L : Subgroup (GL (Fin n) k)) (g : GL (Fin n) k), g ∈ Gz Z ∧ act g p = hom t p ∧
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) ∧
      IsCompact (K : Set (GL (Fin n) k)) ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) ∧
      L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧ L.Normal' K ∧ L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      ((modul (stab Z p) K L g : ℝ) : ℂ) = mm p) :
    ∀ (N : ℕ) (T : Finset (Sp k n)), T.card ≤ N → T ⊆ s → ∀ D : Set (Sp k n), IsClosed D →
      (∀ h ∈ Gz Z, ∀ q ∈ D, act h q ∈ D) → (∀ q ∈ D, hom t q ∈ D) → D ∩ UU ⊆ ⋃ p ∈ T, orb Z p →
      ∀ ξ, InvU Z ξ → SuppU ξ D → ∀ Q : ℂ[X], (∏ p ∈ T, (X - Polynomial.C (mm p))) ∣ Q →
        Kills (aeval (pullH (n := n) t) Q ξ) UU := by
  classical
  intro N
  induction N with
  | zero =>
    intro T hT hTs D hD hinv hsig hcov ξ hξ hS Q hQ
    have hT0 : T = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hT)
    subst hT0
    have hD0 : D ∩ UU = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun q hq => ?_
      simpa using hcov hq
    exact kills_aevalH t (kills_of_suppU hD0 hS) Q
  | succ N ih =>
    intro T hT hTs D hD hinv hsig hcov ξ hξ hS Q hQ
    by_cases hne : (D ∩ UU).Nonempty
    swap
    · exact kills_aevalH t (kills_of_suppU (Set.not_nonempty_iff_eq_empty.1 hne) hS) Q
    obtain ⟨p₀, hp₀T, hO, hcl⟩ := exists_open_orbit T (fun p hp => (hs p (hTs hp)).1) D hD hinv hcov hne
    obtain ⟨hp₀2, K, L, g, hg, hgp, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hm⟩ := hs p₀ (hTs hp₀T)
    set O := orb Z p₀ with hOdef
    set U := (UU : Set (Sp k n)) ∩ (D \ O)ᶜ with hUdef
    have hU : IsOpen U := PositivityTheory.RgUd.T.Nil.Orb.Oasm.isOpen_UU.inter hcl.isOpen_compl
    have hUD : U ∩ D = O := by
      ext q
      constructor
      · rintro ⟨⟨_, hqn⟩, hqD⟩
        by_contra hqO
        exact hqn ⟨hqD, hqO⟩
      · intro hqO
        exact ⟨⟨orb_subset_UU hp₀2 hqO, fun h => h.2 hqO⟩, hO hqO⟩
    have hstep := h4 n Z hZ t p₀ g hg hgp hp₀2 K hK hKo hKc L hLo hLKK hLn1 hLn2 D U hD hU hUD hinv hsig ξ hξ hS
    have hDU : D \ U = D \ O := by
      ext q
      constructor
      · rintro ⟨hqD, hqU⟩
        refine ⟨hqD, fun hqO => hqU ⟨orb_subset_UU hp₀2 hqO, fun h => h.2 hqO⟩⟩
      · rintro ⟨hqD, hqO⟩
        exact ⟨hqD, fun h => h.2 ⟨hqD, hqO⟩⟩
    rw [hDU, hm] at hstep
    have hOinv : ∀ h ∈ Gz Z, ∀ q, act h q ∈ O → q ∈ O := by
      rintro h hh q ⟨g', hg', hg'q⟩
      refine ⟨h⁻¹ * g', (GzS Z).mul_mem ((GzS Z).inv_mem hh) hg', ?_⟩
      rw [act_mul, hg'q, ← act_mul, inv_mul_cancel, act_one]
    have hsig0 : hom t⁻¹ p₀ = act g⁻¹ p₀ := by
      have e1 : hom t⁻¹ (act g p₀) = p₀ := by rw [hgp, hom_hom]
      rw [hom_act] at e1
      calc hom t⁻¹ p₀ = act g⁻¹ (act g (hom t⁻¹ p₀)) := by rw [← act_mul, inv_mul_cancel, act_one]
        _ = act g⁻¹ p₀ := by rw [e1]
    have hsigO : ∀ q, hom t q ∈ O → q ∈ O := by
      rintro q ⟨g', hg', hg'q⟩
      refine ⟨g' * g⁻¹, (GzS Z).mul_mem hg' ((GzS Z).inv_mem hg), ?_⟩
      rw [act_mul, ← hsig0, ← hom_act, hg'q, hom_hom]
    set T' := T.filter (fun p => orb Z p ≠ O) with hT'def
    have hT'sub : T' ⊆ T.erase p₀ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact Finset.mem_erase.2 ⟨fun h => hp.2 (by rw [h]), hp.1⟩
    have hT'card : T'.card ≤ N := by
      have := Finset.card_le_card hT'sub
      rw [Finset.card_erase_of_mem hp₀T] at this
      omega
    obtain ⟨Q0, hQ0⟩ := hQ
    set R := (∏ p ∈ T.erase p₀, (X - Polynomial.C (mm p))) * Q0 with hRdef
    have hQR : Q = R * (X - Polynomial.C (mm p₀)) := by
      rw [hQ0, ← Finset.mul_prod_erase T _ hp₀T, hRdef]
      ring
    have hT'R : (∏ p ∈ T', (X - Polynomial.C (mm p))) ∣ R :=
      dvd_mul_of_dvd_left (Finset.prod_dvd_prod_of_subset _ _ _ hT'sub) Q0
    have key : aeval (pullH (n := n) t) Q ξ = aeval (pullH (n := n) t) R (pullH t ξ - mm p₀ • ξ) := by
      rw [hQR, map_mul, Module.End.mul_apply, aeval_X_subH]
    rw [key]
    refine ih T' hT'card (fun p hp => hTs (Finset.mem_of_mem_filter p hp)) (D \ O) hcl ?_ ?_ ?_ _
      (invU_sub_smul (invU_pullH t hξ) hξ _) hstep R hT'R
    · rintro h hh q ⟨hqD, hqO⟩
      exact ⟨hinv h hh q hqD, fun h' => hqO (hOinv h hh q h')⟩
    · rintro q ⟨hqD, hqO⟩
      exact ⟨hsig q hqD, fun h' => hqO (hsigO q h')⟩
    · rintro q ⟨⟨hqD, hqO⟩, hqU⟩
      obtain ⟨p, hpT, hqp⟩ := Set.mem_iUnion₂.1 (hcov ⟨hqD, hqU⟩)
      refine Set.mem_iUnion₂.2 ⟨p, Finset.mem_filter.2 ⟨hpT, fun h => hqO (h ▸ hqp)⟩, hqp⟩

end Main

section Final


variable (k) in
theorem orbQ_of (h3 : Reps0 k) (h4 : StepModH k) (h5 : ModH k) : OrbQ k := by
  classical
  intro hT _ n Z hZ hd t ht
  obtain ⟨s, hs, hcov⟩ := h3 n Z hZ
  have H : ∀ p ∈ s, ∃ a : ℝ, 2 * a < dB0 Z ∧ ∃ (K L : Subgroup (GL (Fin n) k)) (g : GL (Fin n) k),
      g ∈ Gz Z ∧ act g p = hom t p ∧
      K ≤ GzS Z ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (K : Set (GL (Fin n) k))) ∧
      IsCompact (K : Set (GL (Fin n) k)) ∧ IsOpen (((↑) : GzS Z → GL (Fin n) k) ⁻¹' (L : Set (GL (Fin n) k))) ∧
      L ≤ K ⊓ K.map (MulAut.conj g).toMonoidHom ∧ L.Normal' K ∧ L.Normal' (K.map (MulAut.conj g).toMonoidHom) ∧
      modul (stab Z p) K L g = (nabs k t)⁻¹ ^ a := by
    intro p hp
    obtain ⟨hp1, hpn, hp2, P, w, hgr, hpos⟩ := hs p hp
    obtain ⟨a, ha, hat⟩ := h5 hT n Z hZ hd p P w hp1 hpn hp2 hgr hpos
    obtain ⟨K, L, g, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hgval, hmod⟩ := hat t ht
    have hgr' := hgr t
    simp only [← hgval] at hgr'
    obtain ⟨hgZ, hE, hv⟩ := hgr'
    have hgG : g ∈ Gz Z := fun b hb => hgZ b hb
    have e1 : g.val * p.1 * g⁻¹.val = (t : k) • p.1 := by
      rw [hE, smul_mul_assoc, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    have hact : act g p = hom t p := Prod.ext e1 hv
    exact ⟨a, ha, K, L, g, hgG, hact, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hmod⟩
  choose! a ha hKLg using H
  refine ⟨s.toList.map a, ?_, ?_⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact ha p (Finset.mem_toList.1 hp)
  · intro ξ hsupp hinv
    set mm : Sp k n → ℂ := fun p => (((nabs k t)⁻¹ ^ a p : ℝ) : ℂ) with hmm
    have hprod : (polyH t (s.toList.map a) : Module.End ℂ ((Sp k n → ℂ) →ₗ[ℂ] ℂ)) =
        aeval (pullH (n := n) t) (∏ p ∈ s, (X - Polynomial.C (mm p))) := by
      unfold polyH
      rw [← Finset.prod_map_toList s (fun p => X - Polynomial.C (mm p)), map_list_prod, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left fun p _ => ?_
      simp only [mm, Function.comp_apply, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]
      rfl
    rw [hprod]
    refine main_ind h4 hZ t mm s ?_ s.card s le_rfl subset_rfl (NB Z ×ˢ Set.univ) isClosed_NB
      (fun h hh q hq => act_mem_NB hZ hh hq) (fun q hq => hom_mem_NB t hq) ?_ ξ hinv hsupp _ dvd_rfl
    · intro p hp
      obtain ⟨K, L, g, hgG, hact, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, hmod⟩ := hKLg p hp
      exact ⟨(hs p hp).2.2.1, K, L, g, hgG, hact, hK, hKo, hKc, hLo, hLKK, hLn1, hLn2, by rw [hmod]⟩
    · rintro q ⟨⟨⟨hq1, hqn⟩, -⟩, hqU⟩
      obtain ⟨p, hp, hqp⟩ := hcov q.1 hq1 hqn q.2 hqU
      exact Set.mem_iUnion₂.2 ⟨p, hp, hqp⟩

end Final

end PositivityTheory.RgUd.TP.Nil.Orb.Asm
end
end

namespace PositivityTheory.RgUd.TP.Nil.Orb

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem orbQ : PositivityTheory.RgUd.TP.Nil.OrbQ k := Asm.orbQ_of k (reps0 k) (stepH k) (modBound0 k)

end PositivityTheory.RgUd.TP.Nil.Orb
