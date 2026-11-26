module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpotentHypotheses.ContinuousLin
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.FourP
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.MainE
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CompactPowers.ExistsPowSmulMemOfIsCompact
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.Imports
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ExistsEquivLs
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.NabsPow
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.SupportedComposition.ProjectionOfOrbitClosure
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.IsCompactSubgroupOf

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.OrbP
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.StepModPf
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker MulAction

open scoped Pointwise

namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

attribute [local instance] t2Sp lcSp tdSp contSMul lcH tdH scH contSMulH

theorem stepMod_pf (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CharZero k] : StepMod (k := k) := by
  intro n Z hZ t p g hg hgp hp2 K hKG hKo hKc L hLo hLK hLn hLn' C U hC hU hUC hCinv hCsig ξ hξ hξC
  classical
  haveI : T2Space (SpT k n) := t2Sp
  haveI : LocallyCompactSpace (SpT k n) := lcSp
  haveI : TotallyDisconnectedSpace (SpT k n) := tdSp
  haveI : ContinuousSMul (GL (Fin n) k) (SpT k n) := contSMul
  haveI : LocallyCompactSpace (GzS Z) := lcH Z
  haveI : TotallyDisconnectedSpace (GzS Z) := tdH Z
  haveI : SigmaCompactSpace (GzS Z) := scH Z
  haveI : ContinuousSMul (GzS Z) (SpT k n) := contSMulH Z

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
  set ψ := pull Z t ξ - m • ξ with hψdef
  have hψ : ∀ f, ψ f = ξ (fun q => f (sig Z t q)) - m * ξ f := fun f => rfl

  have hV : ∀ v ∈ supportedIn UU, (∀ q ∈ C, v q = 0) → ψ v = 0 := by
    intro v hv hvC
    rw [hψ, hξC v hv hvC, hξC _ (comp_sig_mem Z hZ t hv) (fun q hq => hvC _ (hCsig q hq))]
    simp

  have hR : relSpan (X := SpT k n) (1 : GzS Z →* ℂ) U₁ ≤ LinearMap.ker ψ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, f, hf, rfl⟩
    have hfUU : f ∈ supportedIn UU := supportedIn_mono hU₁UU hf
    simp only [MonoidHom.one_apply, one_smul]
    change ψ (transl (X := SpT k n) h f - f) = 0
    have e1 : ξ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)) = ξ f :=
      hξ _ (h⁻¹).2 f (supportedIn_mono (Set.subset_univ _) hf)
    have e2 : ξ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) (sig Z t q))) = ξ (fun q => f (sig Z t q)) := by
      have := hξ _ (h⁻¹).2 (fun q => f (sig Z t q))
        (supportedIn_mono (Set.subset_univ _) (comp_sig_mem Z hZ t hfUU))
      rw [← this]
      congr 1
      funext q
      rw [sig_act Z t _ (h⁻¹).2]
    have key : ψ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)) = ψ f := by
      rw [hψ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)), hψ f, e1]
      exact congrArg (· - m * ξ f) e2
    have hs : ψ (fun q : Sp k n => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q) - f q) =
        ψ (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)) - ψ f :=
      ψ.map_sub (fun q => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q)) f
    change ψ (fun q : Sp k n => f (act ((h⁻¹ : GzS Z) : GL (Fin n) k) q) - f q) = 0
    rw [hs, key, sub_self]

  have hsig_piece : ∀ q : Sp k n, toT (sig Z t q) ∈ orbitPiece KH (toT p) ↔
      toT (act g q) ∈ orbitPiece K'H (toT p) := by
    intro q
    constructor
    · rintro ⟨κ, hκ, e⟩
      change act (κ : GL (Fin n) k) p = sig Z t q at e
      have hq : q = act ((κ : GL (Fin n) k) * g⁻¹) p := by
        have h1 : sig Z t (act ((κ : GL (Fin n) k) * g⁻¹) p) = sig Z t q := by
          rw [sig_act Z t _ ((GzS Z).mul_mem κ.2 ((GzS Z).inv_mem hg)), ← hgp, ← act_mul,
            inv_mul_cancel_right, e]
        have := congrArg (sig Z t⁻¹) h1
        rw [sig_inv_sig Z hZ, sig_inv_sig Z hZ] at this
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
      change act κ p = sig Z t q
      rw [hq, sig_act Z t _ ((GzS Z).mul_mem (hKG hκ) ((GzS Z).inv_mem hg)), ← hgp, ← act_mul,
        inv_mul_cancel_right]
  have hf₀UU : f₀ ∈ supportedIn UU := supportedIn_mono hU₁UU hf₀
  have hf₁UU : f₁ ∈ supportedIn UU := supportedIn_mono hU₁UU hf₁
  have hX1 : ξ (fun q => f₀ (sig Z t q)) = ξ f₁ := by
    rw [← hξ g hg f₁ (supportedIn_mono (Set.subset_univ _) hf₁)]
    refine xi_eq hξC (comp_sig_mem Z hZ t hf₀UU) (comp_act_memUU g hf₁UU) fun q hq => ?_
    rw [lift_on_C' hO₁ (hPsub KH) hf₀ hf₀O _ (hCsig q hq),
      lift_on_C' hO₁ (hPsub K'H) hf₁ hf₁O _ (hCinv g hg q hq)]
    by_cases h : toT (sig Z t q) ∈ orbitPiece KH (toT p)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hsig_piece q).1 h)]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hsig_piece q).2 h'))]

  have hc0 := piece_count Z hξ hC hU₁o hU₁UU hCinv hO₁ hξC hKHc hLHo hLKH hnK hf₀ hfL hf₀O hfLO
  have hc1 := piece_count Z hξ hC hU₁o hU₁UU hCinv hO₁ hξC hK'Hco.1 hLHo hLK'H hnK' hf₁ hfL hf₁O hfLO
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

end PositivityTheory.RgUd.T.Nil.Orb.BStep
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.CentralizerRepresentatives.ImportsAlt
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Orb.BReps

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reps [CharZero k] : Reps (k := k) := by
  unfold Reps
  intro n Z hZ c hc
  obtain ⟨hcomm, hred⟩ := hZ
  obtain ⟨M, hM, L, hLf, hL, R, o, hF⟩ := exists_frames Z hcomm hred
  classical
  have hcZ : ∀ a ∈ Z, a * c = c * a := fun a ha => hcomm a ha c hc
  have hN : ∀ x ∈ Bz Z, ∀ z ∈ Z, z * (x - c) = (x - c) * z := by
    intro x hx z hz
    rw [mul_sub, sub_mul, hx z hz, hcZ z hz]
  let S : Type := {p : Sp k n // p.1 ∈ Bz Z ∧ IsNilpotent (p.1 - c) ∧ p.2 ≠ 0}
  let F : (p : S) → Frame Z M L R o (p.1.1 - c) p.1.2 := fun p =>
    Classical.choice (hF _ (hN _ p.2.1) p.2.2.1 p.1.2)
  have hb : ∀ (p : S) (m : M) (ℓ σ : ℕ),
      Nat.card {a : (F p).ι m // (F p).l m a = ℓ ∧ (F p).s m a = σ} < n + 1 := by
    intro p m ℓ σ
    haveI := (F p).fι m
    exact Nat.lt_succ_of_le ((Finite.card_subtype_le _).trans ((F p).card_le m))
  let τ : S → M → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) := fun p m ℓ σ =>
    ⟨Nat.card {a : (F p).ι m // (F p).l m a = ℓ.1 ∧ (F p).s m a = σ.1}, hb p m ℓ σ⟩
  have hrep : ∀ t : Set.range τ, ∃ p : S, τ p = t.1 := fun t => t.2
  let rep : Set.range τ → S := fun t => Classical.choose (hrep t)
  have hrepτ : ∀ t, τ (rep t) = t.1 := fun t => Classical.choose_spec (hrep t)
  refine ⟨(Set.finite_range (fun t : Set.range τ => (rep t).1)).toFinset, ?_, ?_⟩
  · intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    obtain ⟨t, rfl⟩ := hp
    obtain ⟨h1, h2, h3⟩ := (rep t).2
    obtain ⟨P, w, hPw, hu⟩ := grade_of_frame (F (rep t))
    refine ⟨h1, h2, h3, P, w, hPw, ?_⟩
    intro a haZ hax
    apply hu a haZ
    have hac : a * c = c * a := (haZ c hc).symm
    rw [mul_sub, sub_mul, hac]
    show a * (rep t).1.1 - c * a = (rep t).1.1 * a - c * a
    rw [hax]
  · intro x hx hnil v hv
    let q : S := ⟨(x, v), hx, hnil, hv⟩
    let t : Set.range τ := ⟨τ q, q, rfl⟩
    refine ⟨(rep t).1, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]
      exact ⟨t, rfl⟩
    · have he : τ (rep t) = τ q := hrepτ t
      obtain ⟨g, hgZ, hgN, hgv⟩ := conj_of_frames (F (rep t)) (F q) (by
        intro m ℓ σ hℓ hσ
        exact congrArg (fun f => (f m ⟨ℓ, Nat.lt_succ_of_le hℓ⟩ ⟨σ, Nat.lt_succ_of_le hσ⟩).1) he)
      refine ⟨g, hgZ, ?_⟩
      have hgc : (g : Matrix (Fin n) (Fin n) k) * c = c * g := (hgZ c hc).symm
      have key : (g : Matrix (Fin n) (Fin n) k) * (rep t).1.1 = x * g := by
        have h := hgN
        simp only [mul_sub, sub_mul] at h
        rw [hgc] at h
        simpa using h
      refine Prod.ext ?_ ?_
      · show (g : Matrix (Fin n) (Fin n) k) * (rep t).1.1 * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = x
        rw [key, mul_assoc, Units.mul_inv, mul_one]
      · exact hgv

end PositivityTheory.RgUd.T.Nil.Orb.BReps
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.IdempotentFibres.TraceNeZeroOfIdem
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.Ofib

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem trace_ne_zero_of_idem [CharZero k] {e : Matrix (Fin n) (Fin n) k} (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    trace e ≠ 0 := by
  have he' : IsIdempotentElem (Matrix.toLin' e) := by
    have h2 : Matrix.toLin' (e * e) = Matrix.toLin' e := by rw [he.eq]
    rw [Matrix.toLin'_mul] at h2
    exact h2
  intro h
  apply h0
  have ht : LinearMap.trace k (Fin n → k) (Matrix.toLin' e) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
    exact h
  have h1 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff (e := Matrix.toLin' e) he').1 ht
  exact Matrix.toLin'.injective (by rw [h1, map_zero])


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem exists_pow_eq {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) :
    ∃ (m : ℕ) (d : Matrix (Fin n) (Fin n) k), d ∈ Z ∧ c ^ m = c ^ (m + 1) * d := by
  let W : ℕ → Submodule k (Matrix (Fin n) (Fin n) k) := fun j =>
    (Subalgebra.toSubmodule Z).map (LinearMap.mulLeft k (c ^ j))
  have hmono : ∀ j, W (j + 1) ≤ W j := by
    intro j x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    refine Submodule.mem_map.2 ⟨c * y, Z.mul_mem hc hy, ?_⟩
    simp [pow_succ, mul_assoc]
  have hex : ∃ j, W (j + 1) = W j := by
    by_contra hne
    push Not at hne
    have hlt : ∀ j, Module.finrank k (W (j + 1)) < Module.finrank k (W j) := fun j =>
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hmono j) (hne j))
    have hb : ∀ j, Module.finrank k (W j) + j ≤ Module.finrank k (W 0) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => have := hlt j; omega
    have h1 := hb (Module.finrank k (Matrix (Fin n) (Fin n) k) + 1)
    have h2 := Submodule.finrank_le (W 0)
    omega
  obtain ⟨m, hm⟩ := hex
  have hcm : c ^ m ∈ W m := Submodule.mem_map.2 ⟨1, Z.one_mem, by simp⟩
  rw [← hm] at hcm
  obtain ⟨d, hd, e⟩ := Submodule.mem_map.1 hcm
  exact ⟨m, d, hd, by simpa using e.symm⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem eq_zero_of_trace [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z)
    {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) (h : ∀ b ∈ Z, trace (b * c) = 0) : c = 0 := by
  obtain ⟨m, d, hd, hmd⟩ := exists_pow_eq hc
  have hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := hZ.1
  have hdc : d * c = c * d := hcomm d hd c hc

  have key : ∀ j, c ^ m = c ^ (m + j) * d ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [ih]
      calc c ^ (m + j) * d ^ j = c ^ j * c ^ m * d ^ j := by rw [← pow_add, add_comm]
        _ = c ^ j * (c ^ (m + 1) * d) * d ^ j := by rw [← hmd]
        _ = c ^ j * c ^ (m + 1) * (d * d ^ j) := by simp only [mul_assoc]
        _ = c ^ (m + (j + 1)) * d ^ (j + 1) := by
          rw [← pow_add, pow_succ' d j, show j + (m + 1) = m + (j + 1) by omega]
  set e := c ^ m * d ^ m with he_def
  have hcd : Commute c d := by rw [Commute, SemiconjBy, hdc]
  have he_idem : IsIdempotentElem e := by
    unfold IsIdempotentElem
    have h2 := key m
    calc e * e = c ^ m * (d ^ m * c ^ m) * d ^ m := by simp only [he_def, mul_assoc]
      _ = c ^ m * (c ^ m * d ^ m) * d ^ m := by rw [← (hcd.pow_pow m m).eq]
      _ = c ^ (m + m) * d ^ m * d ^ m := by rw [pow_add]; simp only [mul_assoc]
      _ = c ^ m * d ^ m := by rw [← h2]
  have he_mem : e ∈ Z := Z.mul_mem (Z.pow_mem hc m) (Z.pow_mem hd m)
  by_contra hne
  by_cases he0 : e = 0
  ·
    have hcm0 : c ^ m = 0 := by
      have h2 := key m
      rw [h2, pow_add, mul_assoc, ← he_def, he0, mul_zero]
    have hnil : IsNilpotent (⟨c, hc⟩ : Z) := ⟨m, Subtype.ext (by simpa using hcm0)⟩
    have := hZ.2
    have := hnil.eq_zero
    exact hne (by simpa using congrArg Subtype.val this)
  ·
    have hb : c ^ m * d ^ (m + 1) ∈ Z := Z.mul_mem (Z.pow_mem hc m) (Z.pow_mem hd _)
    have hbe : c ^ m * d ^ (m + 1) * c = e := by
      calc c ^ m * d ^ (m + 1) * c = c ^ m * (c * d ^ (m + 1)) := by
            rw [mul_assoc, ← (hcd.pow_right (m + 1)).eq]
        _ = c ^ (m + 1) * (d * d ^ m) := by rw [← mul_assoc, ← pow_succ, pow_succ' d m]
        _ = e := by rw [← mul_assoc, ← hmd]
    exact trace_ne_zero_of_idem he_idem he0 (by rw [← hbe]; exact h _ hb)


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_add (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x y : Matrix (Fin n) (Fin n) k) :
    qZ Z (x + y) = qZ Z x + qZ Z y := by
  funext i
  simp [qZ, mul_add, trace_add]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_sub (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x y : Matrix (Fin n) (Fin n) k) :
    qZ Z (x - y) = qZ Z x - qZ Z y := by
  funext i
  simp [qZ, mul_sub, trace_sub]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_nil (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z)
    (hn : IsNilpotent x) : qZ Z x = 0 := by
  funext i
  have hb : ((Module.finBasis k Z i : Z) : Matrix (Fin n) (Fin n) k) ∈ Z := (Module.finBasis k Z i).2
  have hcomm : Commute ((Module.finBasis k Z i : Z) : Matrix (Fin n) (Fin n) k) x := hx _ hb
  have := Matrix.isNilpotent_trace_of_isNilpotent (hcomm.isNilpotent_mul_left hn)
  simpa [qZ] using this.eq_zero


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_inj [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {c c' : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) (hc' : c' ∈ Z) (h : qZ Z c = qZ Z c') : c = c' := by
  have h0 : qZ Z (c - c') = 0 := by rw [qZ_sub, h, sub_self]
  rw [← sub_eq_zero]
  refine eq_zero_of_trace hZ (Z.sub_mem hc hc') fun b hb => ?_
  let ℓ : Z →ₗ[k] k :=
    { toFun := fun a => trace ((a : Matrix (Fin n) (Fin n) k) * (c - c'))
      map_add' := fun a b => by simp [add_mul, trace_add]
      map_smul' := fun a b => by simp [trace_smul] }
  have hℓ : ℓ = 0 := (Module.finBasis k Z).ext fun i => by
    have := congrFun h0 i
    simpa [qZ, ℓ] using this
  exact congrArg (fun f : Z →ₗ[k] k => f ⟨b, hb⟩) hℓ


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem qZ_surj [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z)
    (y : Fin (Module.finrank k Z) → k) : ∃ c ∈ Z, qZ Z c = y := by
  let φ : Z →ₗ[k] (Fin (Module.finrank k Z) → k) :=
    { toFun := fun c => qZ Z (c : Matrix (Fin n) (Fin n) k)
      map_add' := fun a b => qZ_add Z a b
      map_smul' := fun a b => by funext i; simp [qZ, trace_smul] }
  have hinj : Function.Injective φ := fun a b h => Subtype.ext (qZ_inj hZ a.2 b.2 h)
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨c, hc⟩ := hsurj y
  exact ⟨c, c.2, hc⟩


theorem fibZN [CharZero k] : FibZN (k := k) := by
  intro n Z hZ y
  obtain ⟨c, hc, hcy⟩ := qZ_surj hZ y
  refine ⟨c, hc, hcy, fun x hx => ⟨fun ⟨hqy, c', hc', hnil⟩ => ?_, fun hnil => ⟨?_, c, hc, hnil⟩⟩⟩
  · have hx' : x - c' ∈ Bz Z := fun a ha => by
      rw [mul_sub, sub_mul, hx a ha, hZ.1 a ha c' hc']
    have h1 : qZ Z x = qZ Z c' := by
      have := qZ_nil Z hx' hnil
      rw [qZ_sub, sub_eq_zero] at this
      exact this
    have : c' = c := qZ_inj hZ hc' hc (by rw [← h1, hqy, hcy])
    rwa [this] at hnil
  · have hx' : x - c ∈ Bz Z := fun a ha => by
      rw [mul_sub, sub_mul, hx a ha, hZ.1 a ha c hc]
    have := qZ_nil Z hx' hnil
    rw [qZ_sub, sub_eq_zero] at this
    rw [this, hcy]

end PositivityTheory.RgUd.T.Nil.Orb.Ofib
end
end

namespace PositivityTheory.RgUd.T.Nil.Orb.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem orbP [CharZero k] : OrbP (k := k) :=
  Oasm.orbP_of k (Ozn.zNClosed (k := k)) (Ofib.fibZN (k := k)) (BReps.reps k) (BStep.stepMod_pf k) (BModbound.modBound k)

end PositivityTheory.RgUd.T.Nil.Orb.Final
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.BasePPf
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Nil

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil.BasePf

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem usage₁₀ [CharZero k] : BaseP (k := k) := by
  intro n Z hZ h0 ξ hS hI
  have : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  have : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  intro f hf
  have hle : supportedIn {p : Sp k n | p.2 ≠ 0} ≤ LinearMap.ker ξ := supportedIn_le_of_local fun p hp => by
    obtain ⟨e, he, hee, hev, hprim⟩ := prim Z hZ.1 hZ.2 p.2 hp
    refine ⟨{q : Sp k n | e *ᵥ q.2 ≠ 0}, ?_, hev, fun g hg =>
      LinearMap.mem_ker.2 (mainE Z hZ h0 e he hee hprim p.2 hev ξ hS hI g hg)⟩
    exact isOpen_ne_fun (continuous_const.matrix_mulVec continuous_snd) continuous_const
  exact LinearMap.mem_ker.1 (hle hf)

end PositivityTheory.RgUd.T.Nil
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpotentHypotheses.Assembly
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Asm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]

theorem nilpB_of (fourP : FourP (k := k)) (orbP : OrbP (k := k)) (locQ : LocQ (k := k)) (baseP : BaseP (k := k)) :
    NilpB (k := k) := by
  unfold NilpB
  intro n Z hCR hH
  by_cases hd : dB0 Z = 0
  · exact baseP n Z hCR hd
  refine locQ n Z hCR fun y ξ hξ hinv => ?_
  have hmono : ∀ η : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp η (Fib Z y) → Supp η (Bz Z ×ˢ Set.univ) := by
    intro η hη f hf hvan
    refine hη f hf fun p hp => hvan p ?_
    have hp' : p ∈ (Bz Z ∩ qZ Z ⁻¹' {y}) ×ˢ (Set.univ : Set (Fin n → k)) := hp
    exact ⟨hp'.1.1, hp'.2⟩
  obtain ⟨t, ht0, ht1⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator k
  obtain ⟨𝓕, hF1, hF2, hF3, hF4, hF5, hF6⟩ := fourP n Z hCR
  obtain ⟨a, ha, hP⟩ := orbP n Z hCR (Nat.pos_of_ne_zero hd) t ht1 y
  have hξB := hmono ξ hξ
  have hFξ := hP (𝓕 ξ) (hF2 ξ y hξ) (hF3 ξ hξB hinv) (hH (𝓕 ξ) (hF1 ξ hξB) (hF3 ξ hξB hinv))
  have hξK := hP ξ hξ hinv (hH ξ hξB hinv)
  have hc : 1 < (nabs k t)⁻¹ := one_lt_inv_iff₀.2 ⟨ht0, ht1⟩
  have key : ξ ∈ (supportedIn (UU : Set (Sp k n))).dualAnnihilator := by
    refine bez _ (pull Z t) (pull Z t⁻¹) (pull_inv Z hCR t).1 (pull_inv Z hCR t).2 ?_
      ((nabs k t)⁻¹) hc (dB0 Z) a ha ξ ?_ ?_
    · intro m hm
      rw [Submodule.mem_dualAnnihilator] at hm ⊢
      exact pull_kills Z hCR t m hm
    · rw [Submodule.mem_dualAnnihilator]
      exact hξK
    · rw [Submodule.mem_dualAnnihilator]
      refine (hF4 _ (prod_supp Z hCR t _ a ξ hξB)).2 ?_
      intro f hf
      have hfu : f ∈ supportedIn (Set.univ : Set (Sp k n)) :=
        (show f ∈ supportedIn (Set.univ : Set (Sp k n)) ↔
            (IsLocallyConstant f ∧ HasCompactSupport f) ∧ Function.support f ⊆ Set.univ from Iff.rfl).2
          ⟨((show f ∈ supportedIn (UU : Set (Sp k n)) ↔
            (IsLocallyConstant f ∧ HasCompactSupport f) ∧ Function.support f ⊆ UU from Iff.rfl).1 hf).1,
            Set.subset_univ _⟩
      rw [four_prod Z hCR 𝓕 hF1 hF5 hF6 t a ξ hξB f hfu]
      exact hFξ f hf
  exact (Submodule.mem_dualAnnihilator ξ).1 key

end PositivityTheory.RgUd.T.Nil.Asm
end
end

namespace PositivityTheory.RgUd.T.Nil.Final

theorem nilpB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] :
    PositivityTheory.RgUd.T.NilpB (k := k) :=
  PositivityTheory.RgUd.T.Nil.Asm.nilpB_of k (PositivityTheory.RgUd.T.Nil.Four.Final.fourP k) (PositivityTheory.RgUd.T.Nil.Orb.Final.orbP k)
    (PositivityTheory.RgUd.T.Nil.Four.Final.locQ k) (PositivityTheory.RgUd.T.Nil.usage₁₀ k)

end PositivityTheory.RgUd.T.Nil.Final
