module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIdentificationEqOfGlobalLatticesEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularOfLocalStandardLatticeTranslates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalInnerDatumEqIffLocalDataEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalGraphEqOfLocalIotaAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalGraphEqOfLocalIotaAgree
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.IotaGlob

theorem mem_localLattice_inf_of_mem_span : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (U : Submodule D.host.E (VS D).V) (Λ : LV D),
    Submodule.IsLattice D.host.E Λ → ∀ y ∈ lattice₂ D Z.M p Λ,
    y ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → y ∈ lattice₂ D Z.M p (Λ ⊓ toO (VS D) U) := by
  intro D Z p U Λ h y hy hs
  have e := Formalism.L2.SG.Pf.locSatC_holds D Z p Λ U h.fg
  exact (Set.ext_iff.1 e y).2 ⟨hy, hs⟩

theorem O_eq {D : D7} (Z : LocDat D) (p : PlF D) : (Z.M p).L.O = (D.s.atP p).O := (Z.agree p).2.2.2.1

theorem gS_unit : ∀ (D : D7) (Z : LocDat D) (p : PlF D), (Z.M p).split = none →
    ∃ u ∈ (Z.M p).L.O, u * ((gS D : ℕ) : (D.s.atP p).Ep) = 1 := by
  intro D Z p hs
  refine ⟨(D.s.atP p).ιE (uP p : D.host.E), ?_, ?_⟩
  · rw [O_eq Z p]; exact Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p
  · rw [mul_comm, ← map_natCast (D.s.atP p).ιE]
    exact Formalism.L2.SG.Pf.StabIntSh.gS_mul_uP Z.δ Z.M Z.agree p hs

theorem gS_split : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g →
    ∃ u ∈ (Z.M p).L.O, ∃ v ∈ (Z.M p).L.O,
      ((gS D : ℕ) : (D.s.atP p).Ep) = u * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) ∧ u * v = 1 := by
  intro D Z p g hs
  have hagree := (Z.agree p).2.2.2.2.2
  rcases hs' : (D.s.atP p).split with _ | sg
  · rw [hs, hs'] at hagree; exact hagree.elim
  rw [hs, hs'] at hagree
  have hq : g.q = sg.q := hagree.2
  refine ⟨(D.s.atP p).ιE ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E), ?_, (D.s.atP p).ιE (uP p : D.host.E), ?_, ?_, ?_⟩
  · rw [O_eq Z p, map_natCast]; exact natCast_mem _ _
  · rw [O_eq Z p]; exact Formalism.L2.SG.Pf.LocFacts.unitPart_mem₂ p
  · rw [hq, sg.q_eq, ← Formalism.MainNotions.BridgeLemma.gpart_mul_oth p, Formalism.MainNotions.BridgeLemma.gpart_some p sg hs']
    simp only [Nat.cast_mul, map_natCast]
    rw [← map_natCast (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), mul_comm]
  · rw [← map_mul, Formalism.MainNotions.BridgeLemma.unitAt_eq p]
    have h0 : ((Formalism.MainNotions.BridgeLemma.oth p : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast Formalism.MainNotions.BridgeLemma.oth_ne_zero p
    push_cast
    rw [mul_inv_cancel₀ h0, map_one]

end GlobalTheory.Unfold.IotaGlob

namespace GlobalTheory.Unfold.IotaGlob

variable {D : D7}

theorem mem_iff_loc (Z : LocDat D) (N : LV D) (hN : Submodule.IsLattice D.host.E N) (x : (VS D).V) :
    x ∈ N ↔ ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p N := by
  exact GlobalTheory.Unfold.StdDual.mem_iff_local Z N hN x

theorem smul_mem_latP (Z : LocDat D) (p : PlF D) (Λ : LV D) {u : (D.s.atP p).Ep} (hu : u ∈ (Z.M p).L.O)
    {w : Vp D p} (hw : w ∈ lattice₂ D Z.M p Λ) : u • w ∈ lattice₂ D Z.M p Λ := by
  have := (lattice₂ D Z.M p Λ).smul_mem (⟨u, hu⟩ : (Z.M p).L.O) hw
  rwa [Subring.smul_def] at this

theorem baseChange_natCast_smul (p : PlF D) (n : ℕ) (x : (VS D).V) :
    baseChange₂ D p ((n : 𝓞 D.host.E) • x) = ((n : (D.s.atP p).Ep)) • baseChange₂ D p x := by
  rw [← algebraMap_smul D.host.E (n : 𝓞 D.host.E) x, map_natCast, baseChange_smul₂, map_natCast]

theorem gsmul_mem (Z : LocDat D) (p : PlF D) (Λ : LV D) {w : Vp D p} (hw : w ∈ lattice₂ D Z.M p Λ) :
    ((gS D : ℕ) : (D.s.atP p).Ep) • w ∈ lattice₂ D Z.M p (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  unfold lattice₂ at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    rw [← baseChange_natCast_smul]
    exact Submodule.subset_span ⟨_, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hl, rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, smul_comm]
    exact smul_mem_latP Z p _ a.2 hx

theorem bcP_mem_X (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    {f : Fin (D.R.rS + 1) → Vp D p} (hf : f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))
    {ξ : (VS D).V} (hξ : ξ ∈ Xsp G) : baseChange₂ D p ξ ∈ (locH Z p).X f := by
  subst hf
  have hξ' : ξ ∈ Submodule.span D.host.E (Set.range G.fl.e) := hξ
  clear hξ
  induction hξ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨u, hu⟩ := Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Z p a.castSucc
    have e : baseChange₂ D p (G.fl.e a) =
        (↑u⁻¹ : (D.s.atP p).Ep) • (frFac Z.δ p a.castSucc • baseChange₂ D p (frame G a.castSucc)) := by
      rw [← hu, smul_smul, Units.inv_mul, one_smul]
      simp [frame, FlagG.fvec]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [(baseChange₂ D p).map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem X_le_span (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    {f : Fin (D.R.rS + 1) → Vp D p} (hf : f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) :
    (locH Z p).X f ≤ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (Xsp G : Set (VS D).V)) := by
  subst hf
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨G.fl.e a, Submodule.subset_span ⟨a, rfl⟩, ?_⟩)
  simp [frame, FlagG.fvec]

theorem baseChange_mem_perp (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T)
    {f : Fin (D.R.rS + 1) → Vp D p} (hf : f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))
    {l : (VS D).V} (hl : l ∈ orth (VS D) (Xsp G)) : baseChange₂ D p l ∈ (locH Z p).perp ((locH Z p).X f) := by
  intro x hx
  have hx' := X_le_span Z p G hf hx
  clear hx
  have key : (locH Z p).h x (baseChange₂ D p l) = 0 := by
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨ξ, hξ, rfl⟩ := hy
      rw [(locH Z p).h_herm]
      have h0 : (locH Z p).h (baseChange₂ D p l) (baseChange₂ D p ξ) = 0 := by
        show LocFacts₂ Z.M p (baseChange₂ D p l) (baseChange₂ D p ξ) = 0
        rw [baseChangeAt_form Z.M p (Z.hcj p)]
        have : (VS D).hT ξ l = 0 := (GlobalTheory.FrameProj.mem_orth_iff _ _).1 hl ξ hξ
        simp [brS, this]
      rw [h0, map_zero]
    | zero => exact (locH Z p).h_zero_left _
    | add x y _ _ hx hy => rw [(locH Z p).h_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [(locH Z p).h_smul_left, hx, mul_zero]
  rw [(locH Z p).h_herm, key, map_zero]

theorem X_le_orth {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) : Xsp G ≤ orth (VS D) (Xsp G) := by
  intro y hy
  rw [GlobalTheory.FrameProj.mem_orth_iff]
  intro u hu
  have hu' : u ∈ Submodule.span D.host.E (Set.range G.fl.e) := hu
  have hy' : y ∈ Submodule.span D.host.E (Set.range G.fl.e) := hy
  clear hu hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    induction hu' using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact G.fl.e_iso a b
    | zero => simp
    | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
    | smul c x _ hx => simp [hx]
  | zero => simp
  | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
  | smul c x _ hx => simp [hx]

theorem gS_ne : ((gS D : ℕ) : D.host.E) ≠ 0 := by
  have h0 := (D.host.g_prime 0).pos
  have h1 := (D.host.g_prime 1).pos
  have : 0 < gS D := Nat.mul_pos h0 h1
  exact_mod_cast this.ne'

theorem ngx_lattice {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Λ : LV D)
    (h : Submodule.IsLattice D.host.E Λ) : Submodule.IsLattice D.host.E (NgX Λ (gS D) F F') := by
  have hle : NgX Λ (gS D) F F' ≤ Λ := sup_le (sup_le Submodule.smul_le_right inf_le_left) inf_le_left
  refine ⟨h.fg.of_le hle, ?_⟩
  intro s hs hli
  exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem lrep_mem_lsub {T : D.host.E} {Λ : LV D} {G : LFlag (D.sp.Y 0) D.R.rS T} {l : (VS D).V}
    (hl : l ∈ Lrep Λ G) : l ∈ Lsub Λ G :=
  Submodule.mem_inf.2 ⟨Submodule.mem_sup_left hl, (Submodule.mem_inf.1 hl).2⟩

end GlobalTheory.Unfold.IotaGlob

namespace GlobalTheory.Unfold.IotaGlob
variable {D : D7}
theorem smulLat_mem (Z : LocDat D) (p : PlF D) (c : (D.s.atP p).Ep) (L : Submodule (Z.M p).L.O (Vp D p)) (w : Vp D p)
    (hw : w ∈ L) : c • w ∈ (locH Z p).smulLat c L := by
  unfold Loc.HermSp.smulLat; exact Submodule.subset_span ⟨w, hw, rfl⟩

theorem mem_iota (Z : LocDat D) (p : PlF D) (g : Loc.SplitG (Z.M p).L) (L : Submodule (Z.M p).L.O (Vp D p))
    (f f' : Fin (D.R.rS + 1) → Vp D p) (T T' : (D.s.atP p).Fp)
    (x' : (locH Z p).perp ((locH Z p).X f')) (x : (locH Z p).perp ((locH Z p).X f))
    (hx' : (x' : Vp D p) ∈ L) (hx : (x : Vp D p) ∈ L)
    (hxx : (x : Vp D p) - x' ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) L) :
    ((locH Z p).mkW f' x', (locH Z p).mkW f x) ∈ (locH Z p).iotaGraph g ⟨L, f, f', T, T'⟩ :=
  ⟨x', x, hx', hx, hxx, rfl⟩

theorem of_mem_iota (Z : LocDat D) (p : PlF D) (g : Loc.SplitG (Z.M p).L) (L : Submodule (Z.M p).L.O (Vp D p))
    (f f' : Fin (D.R.rS + 1) → Vp D p) (T T' : (D.s.atP p).Fp)
    (x' : (locH Z p).perp ((locH Z p).X f')) (x : (locH Z p).perp ((locH Z p).X f))
    (h : ((locH Z p).mkW f' x', (locH Z p).mkW f x) ∈ (locH Z p).iotaGraph g ⟨L, f, f', T, T'⟩) :
    ∃ y' : (locH Z p).perp ((locH Z p).X f'), ∃ y : (locH Z p).perp ((locH Z p).X f),
      (y' : Vp D p) ∈ L ∧ (y : Vp D p) ∈ L ∧
      (y : Vp D p) - y' ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) L ∧
      (x' : Vp D p) - y' ∈ (locH Z p).X f' ∧ (x : Vp D p) - y ∈ (locH Z p).X f := by
  obtain ⟨y', y, hy', hy, hyy, heq⟩ := h
  obtain ⟨e1, e2⟩ := Prod.mk.inj heq
  refine ⟨y', y, hy', hy, hyy, ?_, ?_⟩
  · have := (Submodule.Quotient.eq _).1 e1
    simpa using this
  · have := (Submodule.Quotient.eq _).1 e2
    simpa using this

theorem of_mem_iota2 (Z : LocDat D) (p : PlF D) (g : Loc.SplitG (Z.M p).L) (L₁ L₂ : Submodule (Z.M p).L.O (Vp D p))
    (f f' : Fin (D.R.rS + 1) → Vp D p) (T T' : (D.s.atP p).Fp) (x' x : Vp D p)
    (hx' : x' ∈ (locH Z p).perp ((locH Z p).X f')) (hx : x ∈ (locH Z p).perp ((locH Z p).X f))
    (hI : (locH Z p).iotaGraph g ⟨L₁, f, f', T, T'⟩ = (locH Z p).iotaGraph g ⟨L₂, f, f', T, T'⟩)
    (h1 : x' ∈ L₁) (h2 : x ∈ L₁)
    (h3 : x - x' ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) L₁) :
    ∃ y' y : Vp D p, y' ∈ L₂ ∧ y ∈ L₂ ∧
      y - y' ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) L₂ ∧
      x' - y' ∈ (locH Z p).X f' ∧ x - y ∈ (locH Z p).X f := by
  have h := mem_iota Z p g L₁ f f' T T' ⟨x', hx'⟩ ⟨x, hx⟩ h1 h2 h3
  rw [hI] at h
  obtain ⟨y', y, h1, h2, h3, h4, h5⟩ := of_mem_iota Z p g L₂ f f' T T' ⟨x', hx'⟩ ⟨x, hx⟩ h
  exact ⟨y', y, h1, h2, h3, h4, h5⟩

theorem bc1 (p : PlF D) (a c d : (VS D).V) (y : Vp D p) :
    baseChange₂ D p a - y = baseChange₂ D p (d - c) + (baseChange₂ D p (a + c - d) - y) := by
  simp only [map_sub, map_add (f := _)]; abel

theorem bc2 (p : PlF D) (a c d : (VS D).V) (y : Vp D p) :
    baseChange₂ D p a - y = baseChange₂ D p (-(d + c)) + (baseChange₂ D p (a + c + d) - y) := by
  simp only [map_neg, map_add (f := _)]; abel

theorem bc3 (p : PlF D) (a a' : (VS D).V) (y y' : Vp D p) :
    baseChange₂ D p (a - a') = (baseChange₂ D p a - y) - (baseChange₂ D p a' - y') + (y - y') := by
  rw [map_sub]; abel

theorem mem_of_baseChangeAtPlace_split_difference_mem (p : PlF D) (a c d : (VS D).V) (y : Vp D p) (S : Submodule (D.s.atP p).Ep (Vp D p))
    (h : baseChange₂ D p (d - c) + (baseChange₂ D p (a + c - d) - y) ∈ S) : baseChange₂ D p a - y ∈ S := by
  rw [bc1 p a c d y]; exact h

theorem mem_of_baseChangeAtPlace_split_negSum_mem (p : PlF D) (a c d : (VS D).V) (y : Vp D p) (S : Submodule (D.s.atP p).Ep (Vp D p))
    (h : baseChange₂ D p (-(d + c)) + (baseChange₂ D p (a + c + d) - y) ∈ S) : baseChange₂ D p a - y ∈ S := by
  rw [bc2 p a c d y]; exact h

theorem smulLat_le_g (Z : LocDat D) (p : PlF D) (c u v : (D.s.atP p).Ep) (hv : v ∈ (Z.M p).L.O)
    (hg : ((gS D : ℕ) : (D.s.atP p).Ep) = u * c) (huv : u * v = 1) (Λ : LV D) (w : Vp D p)
    (hw : w ∈ (locH Z p).smulLat c (lattice₂ D Z.M p Λ)) :
    w ∈ lattice₂ D Z.M p (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  unfold Loc.HermSp.smulLat at hw
  refine (Submodule.span_le.2 ?_) hw
  rintro _ ⟨z, hz, rfl⟩
  have e : c • z = v • (((gS D : ℕ) : (D.s.atP p).Ep) • z) := by
    rw [hg, smul_smul, ← mul_assoc, mul_comm v u, huv, one_mul]
  show c • z ∈ _
  rw [e]
  exact smul_mem_latP Z p _ hv (gsmul_mem Z p Λ hz)

theorem baseChangeAtPlace_sub_mem_of_three_mem (Z : LocDat D) (p : PlF D) (a a' : (VS D).V) (y y' : Vp D p) (S : Submodule (Z.M p).L.O (Vp D p))
    (h1 : baseChange₂ D p a - y ∈ S) (h2 : baseChange₂ D p a' - y' ∈ S) (h3 : y - y' ∈ S) : baseChange₂ D p (a - a') ∈ S := by
  rw [bc3 p a a' y y']; exact add_mem (sub_mem h1 h2) h3
end GlobalTheory.Unfold.IotaGlob

namespace GlobalTheory.Unfold.IotaGlob

variable {D : D7}

set_option maxHeartbeats 1000000 in
theorem graph_sub (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (Λ₁ Λ₂ : LV D)
    (h₂ : Submodule.IsLattice D.host.E Λ₂) (hL : Lsub Λ₁ F = Lsub Λ₂ F) (hL' : Lsub Λ₁ F' = Lsub Λ₂ F')
    (hI : ∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g →
      (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ =
      (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩) :
    (gdat F F' Λ₁).2.2 ⊆ (gdat F F' Λ₂).2.2 := by
  rintro ⟨p₁, p₂⟩ ⟨l', hl', l, hl, hp₁, hp₂, hll⟩
  obtain ⟨l₂, hl₂, t, ht, rfl⟩ := Submodule.mem_sup.1 (Submodule.mem_inf.1 (hL ▸ lrep_mem_lsub hl)).1
  obtain ⟨l'₂, hl'₂, t', ht', rfl⟩ := Submodule.mem_sup.1 (Submodule.mem_inf.1 (hL' ▸ lrep_mem_lsub hl')).1
  refine ⟨l'₂, hl'₂, l₂, hl₂, ?_, ?_, ?_⟩
  · have e : p₁ - l'₂ = (p₁ - (l'₂ + t')) + t' := by abel
    rw [e]; exact add_mem hp₁ ht'
  · have e : p₂ - l₂ = (p₂ - (l₂ + t)) + t := by abel
    rw [e]; exact add_mem hp₂ ht
  · rw [mem_iff_loc Z _ (ngx_lattice F F' Λ₂ h₂)]
    intro p
    have hΛl₂ : l₂ ∈ Λ₂ := (Submodule.mem_inf.1 hl₂).1
    have hΛl'₂ : l'₂ ∈ Λ₂ := (Submodule.mem_inf.1 hl'₂).1
    have hw : baseChange₂ D p (l₂ - l'₂) ∈ lattice₂ D Z.M p Λ₂ := Submodule.subset_span ⟨_, sub_mem hΛl₂ hΛl'₂, rfl⟩
    have hgle : lattice₂ D Z.M p (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ₂) ≤
        lattice₂ D Z.M p (NgX Λ₂ (gS D) F F') :=
      GlobalTheory.FrameProj.localLattice_mono Z p (le_sup_left.trans le_sup_left)
    cases hs : (Z.M p).split with
    | none =>
      obtain ⟨u, hu, hug⟩ := gS_unit D Z p hs
      have e : baseChange₂ D p (l₂ - l'₂) = ((gS D : ℕ) : (D.s.atP p).Ep) • (u • baseChange₂ D p (l₂ - l'₂)) := by
        rw [smul_smul, mul_comm, hug, one_smul]
      rw [e]
      exact hgle (gsmul_mem Z p Λ₂ (smul_mem_latP Z p Λ₂ hu hw))
    | some g =>
      obtain ⟨u, hu, v, hv, hg, huv⟩ := gS_split D Z p g hs
      obtain ⟨ab, hab, ξ', hξ', habξ⟩ := Submodule.mem_sup.1 hll
      obtain ⟨a, ha, ξ, hξ, haξ⟩ := Submodule.mem_sup.1 hab
      rw [Submodule.ideal_span_singleton_smul] at ha
      obtain ⟨lam, hlam, hlamE⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ha
      have hA := (hB p).1
      have hBf := (hB p).2.1
      have hlΛ : l₂ + t ∈ Λ₁ := (Submodule.mem_inf.1 hl).1
      have hl'Λ : l'₂ + t' ∈ Λ₁ := (Submodule.mem_inf.1 hl').1
      have hξΛ : ξ ∈ Λ₁ := (Submodule.mem_inf.1 hξ).1
      have hξ'Λ : ξ' ∈ Λ₁ := (Submodule.mem_inf.1 hξ').1
      have hξX : ξ ∈ Xsp F := (Submodule.mem_inf.1 hξ).2
      have hξ'X : ξ' ∈ Xsp F' := (Submodule.mem_inf.1 hξ').2
      have hxO : l₂ + t - ξ ∈ orth (VS D) (Xsp F) := sub_mem (Submodule.mem_inf.1 hl).2 (X_le_orth F hξX)
      have hx'O : l'₂ + t' + ξ' ∈ orth (VS D) (Xsp F') := add_mem (Submodule.mem_inf.1 hl').2 (X_le_orth F' hξ'X)
      have hxP := baseChange_mem_perp Z p F hA hxO
      have hx'P := baseChange_mem_perp Z p F' hBf hx'O
      have hxΛ : baseChange₂ D p (l₂ + t - ξ) ∈ lattice₂ D Z.M p Λ₁ := Submodule.subset_span ⟨_, sub_mem hlΛ hξΛ, rfl⟩
      have hx'Λ : baseChange₂ D p (l'₂ + t' + ξ') ∈ lattice₂ D Z.M p Λ₁ := Submodule.subset_span ⟨_, add_mem hl'Λ hξ'Λ, rfl⟩
      have hxx : baseChange₂ D p (l₂ + t - ξ) - baseChange₂ D p (l'₂ + t' + ξ') ∈ (locH Z p).smulLat
          (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ₁) := by
        have e1 : l₂ + t - ξ - (l'₂ + t' + ξ') = a := by
          have : l₂ + t - ξ - (l'₂ + t' + ξ') = (l₂ + t - (l'₂ + t')) - ξ - ξ' := by abel
          rw [this, ← habξ, ← haξ]; abel
        rw [← map_sub, e1, ← hlamE, baseChange_natCast_smul, hg, mul_comm, mul_smul]
        exact smulLat_mem Z p _ _ _ (smul_mem_latP Z p Λ₁ hu (Submodule.subset_span ⟨lam, hlam, rfl⟩))
      have hm1 := of_mem_iota2 Z p g (lattice₂ D Z.M p Λ₁) (lattice₂ D Z.M p Λ₂)
        (FP p).A.f (FP p).B.f (FP p).A.T (FP p).B.T _ _ hx'P hxP (hI p g hs) hx'Λ hxΛ hxx
      clear hI
      obtain ⟨y', y, hy'Λ, hyΛ, hyy, hx'y', hxy⟩ := hm1
      have hd1 : baseChange₂ D p l₂ - y ∈ lattice₂ D Z.M p Λ₂ := sub_mem (Submodule.subset_span ⟨l₂, hΛl₂, rfl⟩) hyΛ
      have hd2 := X_le_span Z p F hA (add_mem (bcP_mem_X Z p F hA (sub_mem hξX ht)) hxy)
      have hd : baseChange₂ D p l₂ - y ∈ lattice₂ D Z.M p (XLam Λ₂ F) :=
        mem_localLattice_inf_of_mem_span D Z p (Xsp F) Λ₂ h₂ _ hd1 (mem_of_baseChangeAtPlace_split_difference_mem p l₂ t ξ y _ hd2)
      have hd1' : baseChange₂ D p l'₂ - y' ∈ lattice₂ D Z.M p Λ₂ := sub_mem (Submodule.subset_span ⟨l'₂, hΛl'₂, rfl⟩) hy'Λ
      have hd2' := X_le_span Z p F' hBf (add_mem (bcP_mem_X Z p F' hBf (neg_mem (add_mem hξ'X ht'))) hx'y')
      have hd' : baseChange₂ D p l'₂ - y' ∈ lattice₂ D Z.M p (XLam Λ₂ F') :=
        mem_localLattice_inf_of_mem_span D Z p (Xsp F') Λ₂ h₂ _ hd1' (mem_of_baseChangeAtPlace_split_negSum_mem p l'₂ t' ξ' y' _ hd2')
      exact baseChangeAtPlace_sub_mem_of_three_mem Z p l₂ l'₂ y y' _ (GlobalTheory.FrameProj.localLattice_mono Z p (le_sup_right.trans le_sup_left) hd)
        (GlobalTheory.FrameProj.localLattice_mono Z p le_sup_right hd') (hgle (smulLat_le_g Z p _ u v hv hg huv Λ₂ _ hyy))

theorem graph_eq_of_local_iota : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩) → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 := by
  intro D Z FP Tn T'n F F' hB Λ₁ Λ₂ h₁ h₂ hL hL' hI
  exact Set.Subset.antisymm (graph_sub Z FP Tn T'n F F' hB Λ₁ Λ₂ h₂ hL hL' hI)
    (graph_sub Z FP Tn T'n F F' hB Λ₂ Λ₁ h₁ hL.symm hL'.symm fun p g hs => (hI p g hs).symm)

end GlobalTheory.Unfold.IotaGlob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalGraphEqOfLocalIotaAgreeStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_graph_eq_of_local_iota_agree : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩) → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 := by
  first | exact @GlobalTheory.Unfold.IotaGlob.graph_eq_of_local_iota | exact GlobalTheory.Unfold.IotaGlob.graph_eq_of_local_iota | (intros; apply GlobalTheory.Unfold.IotaGlob.graph_eq_of_local_iota <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericDatumLatticeEqPerpQuotientImageTerm
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericDatumLatticeEqPerpQuotientImageTerm
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

noncomputable section

namespace GlobalTheory.InnerRead

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def hL (y : V) : V →+ E := ⟨⟨fun x => H.h x y, H.h_zero_left y⟩, fun x x' => H.h_add_left x x' y⟩

lemma h_add_right (x y z : V) : H.h x (y + z) = H.h x y + H.h x z := by
  rw [H.h_herm (y + z) x, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

lemma h_smul_right (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

lemma h_zero_right (x : V) : H.h x 0 = 0 := by
  have := h_smul_right H 0 x 0
  simpa using this

lemma h_sub_left (x y z : V) : H.h (x - y) z = H.h x z - H.h y z := map_sub (hL H z) x y

lemma h_sum_left {ι : Type} (s : Finset ι) (u : ι → V) (y : V) :
    H.h (∑ i ∈ s, u i) y = ∑ i ∈ s, H.h (u i) y := map_sum (hL H y) u s

lemma mkW_eq {r : ℕ} {f : Fin (r + 1) → V} (x y : ↥(H.perp (H.X f))) (h : (x : V) - y ∈ H.X f) :
    H.mkW f x = H.mkW f y := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  simpa using h

def Good (X : Submodule E V) (u : V ≃ₗ[E] V) : Prop :=
  IsUnitary H u ∧ ∀ v ∈ H.perp X, u v - v ∈ X

lemma good_map_le {X : Submodule E V} {u : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u) :
    ∀ x ∈ X, u x ∈ X := by
  intro x hx
  have := X.add_mem (hu.2 x (hX hx)) hx
  simpa using this

lemma good_perp {X : Submodule E V} {u : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u) :
    ∀ v ∈ H.perp X, u v ∈ H.perp X := by
  intro v hv
  have := (H.perp X).add_mem (hX (hu.2 v hv)) hv
  simpa using this

lemma good_inv {X : Submodule E V} {u : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u) :
    Good H X u⁻¹ := by
  refine ⟨fun x y => ?_, fun v hv => ?_⟩
  · have := hu.1 (u.symm x) (u.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have hv' : u.symm v ∈ H.perp X := by
    intro x hx
    have := hu.1 (u.symm v) x
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this]
    exact hv _ (good_map_le H hX hu x hx)
  have := X.neg_mem (hu.2 _ hv')
  rw [LinearEquiv.apply_symm_apply, neg_sub] at this
  exact this

lemma good_mul {X : Submodule E V} {u w : V ≃ₗ[E] V} (hX : X ≤ H.perp X) (hu : Good H X u)
    (hw : Good H X w) : Good H X (u * w) := by
  refine ⟨fun x y => ?_, fun v hv => ?_⟩
  · change H.h (u (w x)) (u (w y)) = _
    rw [hu.1, hw.1]
  · change u (w v) - v ∈ X
    have e : u (w v) - v = (u (w v) - w v) + (w v - v) := by abel
    rw [e]
    exact X.add_mem (hu.2 _ (good_perp H hX hw v hv)) (hw.2 v hv)

variable {H} {r : ℕ} (Fr : FrameD H r)

lemma h_ee (a b : Fin r) : H.h (Fr.e a) (Fr.e b) = 0 :=
  Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))

lemma h_e_es (a b : Fin r) : H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := Fr.h_es a b

lemma h_es_e (a b : Fin r) : H.h (Fr.es a) (Fr.e b) = if b = a then 1 else 0 := by
  rw [H.h_herm (Fr.e b) (Fr.es a), h_e_es]
  split_ifs <;> simp

lemma mem_perp_iff (v : V) : v ∈ H.perp (H.X Fr.f) ↔ ∀ a, H.h v (Fr.e a) = 0 := by
  constructor
  · intro hv a
    exact hv _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact h a
    | zero => exact h_zero_right H v
    | add x y _ _ hx hy => rw [h_add_right, hx, hy, add_zero]
    | smul c x _ hx => rw [h_smul_right, hx, mul_zero]

lemma X_le_perp : H.X Fr.f ≤ H.perp (H.X Fr.f) := by
  intro x hx
  rw [mem_perp_iff]
  intro a
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact h_ee Fr b a
  | zero => exact H.h_zero_left _
  | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]

lemma prF_e (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.e b) = 0 := by
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  simp only [H.h_smul_left, h_ee, h_es_e, mul_zero, Finset.sum_const_zero, mul_ite, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

lemma prF_es (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.es b) = 0 := by
  unfold FrameD.prF
  rw [h_sub_left, h_sub_left, h_sum_left, h_sum_left]
  simp only [H.h_smul_left, h_e_es, Fr.h_ss, mul_zero, Finset.sum_const_zero, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma prF_perp (v : V) : Fr.prF v ∈ H.perp (H.X Fr.f) := (mem_perp_iff Fr _).2 (prF_e Fr v)

lemma prF_add (x y : V) : Fr.prF (x + y) = Fr.prF x + Fr.prF y := by
  unfold FrameD.prF
  simp only [H.h_add_left, add_smul, Finset.sum_add_distrib]
  abel

lemma prF_smul (c : E) (x : V) : Fr.prF (c • x) = c • Fr.prF x := by
  unfold FrameD.prF
  simp only [smul_sub, Finset.smul_sum, smul_smul, H.h_smul_left]

lemma prF_of (v : V) (h1 : ∀ a, H.h v (Fr.es a) = 0) (h2 : ∀ a, H.h v (Fr.e a) = 0) :
    Fr.prF v = v := by
  unfold FrameD.prF
  simp [h1, h2]

lemma sub_prF_mem (v : V) (hv : v ∈ H.perp (H.X Fr.f)) : v - Fr.prF v ∈ H.X Fr.f := by
  have h2 := (mem_perp_iff Fr v).1 hv
  have e : v - Fr.prF v = ∑ a, H.h v (Fr.es a) • Fr.e a + ∑ a, H.h v (Fr.e a) • Fr.es a := by
    unfold FrameD.prF; abel
  rw [e]
  simp only [h2, zero_smul, Finset.sum_const_zero, add_zero]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem Lset_LamStd (L : Submodule M.L.O (H.Wb Fr.f)) :
    H.Lset (Fr.LamStd L) Fr.f = (L : Set (H.Wb Fr.f)) := by
  ext w
  constructor
  · rintro ⟨x, hxΛ, rfl⟩
    have hQ : ∀ v ∈ Fr.LamStd L, H.mkW Fr.f ⟨Fr.prF v, prF_perp Fr v⟩ ∈ L := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨-, -, w, hw, hwL⟩ := hv
        have e : (⟨Fr.prF v, prF_perp Fr v⟩ : ↥(H.perp (H.X Fr.f))) = w := Subtype.ext hw.symm
        rw [e]; exact hwL
      | zero =>
        have e : (⟨Fr.prF 0, prF_perp Fr 0⟩ : ↥(H.perp (H.X Fr.f))) = 0 :=
          Subtype.ext (by simpa using prF_smul Fr 0 0)
        rw [e, map_zero]; exact L.zero_mem
      | add x y _ _ hx hy =>
        have e : (⟨Fr.prF (x + y), prF_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) =
            ⟨Fr.prF x, prF_perp Fr x⟩ + ⟨Fr.prF y, prF_perp Fr y⟩ := Subtype.ext (prF_add Fr x y)
        rw [e, map_add (f := _)]; exact L.add_mem hx hy
      | smul c x _ hx =>
        have e : (⟨Fr.prF (c • x), prF_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) =
            (c : E) • ⟨Fr.prF x, prF_perp Fr x⟩ := Subtype.ext (prF_smul Fr (c : E) x)
        rw [e, map_smul]
        exact L.smul_mem c hx
    have := hQ x hxΛ
    rwa [mkW_eq H ⟨Fr.prF x, prF_perp Fr x⟩ x (by
      have := (H.X Fr.f).neg_mem (sub_prF_mem Fr x x.2); simpa using this)] at this
  · intro hw
    obtain ⟨x0, rfl⟩ := Submodule.mkQ_surjective _ w
    refine ⟨⟨Fr.prF x0, prF_perp Fr x0⟩, ?_, ?_⟩
    · have hp : Fr.prF (Fr.prF x0) = Fr.prF x0 := prF_of Fr _ (prF_es Fr x0) (prF_e Fr x0)
      refine Submodule.subset_span ⟨fun a => ?_, fun a => ?_, ⟨Fr.prF x0, prF_perp Fr x0⟩, hp.symm, ?_⟩
      · change H.h (Fr.prF x0) (Fr.es a) ∈ _; rw [prF_es]; exact zero_mem _
      · change H.h (Fr.prF x0) (Fr.e a) ∈ _; rw [prF_e]; exact zero_mem _
      · rw [mkW_eq H ⟨Fr.prF x0, prF_perp Fr x0⟩ x0 (by
          have := (H.X Fr.f).neg_mem (sub_prF_mem Fr x0 x0.2); simpa using this)]
        exact hw
    · have := (H.X Fr.f).neg_mem (sub_prF_mem Fr x0 x0.2)
      show H.mkW Fr.f _ = H.mkW Fr.f x0
      exact mkW_eq H _ _ (by simpa using this)

lemma good_of_mem_N {g : V ≃ₗ[E] V} (hg : g ∈ Fr.N) : Good H (H.X Fr.f) g := by
  have hX := X_le_perp Fr
  unfold FrameD.N at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨hx.1, hx.2.2⟩
  | one => exact ⟨fun x y => rfl, fun v _ => by simp⟩
  | mul x y _ _ hx hy => exact good_mul H hX hx hy
  | inv x _ hx => exact good_inv H hX hx

lemma mem_img (u : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ img u Λ ↔ ∃ y ∈ Λ, u y = x := by
  unfold img
  rw [Submodule.mem_map]
  rfl

theorem Lset_img {u : V ≃ₗ[E] V} (hu : u ∈ Fr.N) (Λ : Submodule M.L.O V) :
    H.Lset (img u Λ) Fr.f = H.Lset Λ Fr.f := by
  have hX := X_le_perp Fr
  have g1 := good_of_mem_N Fr hu
  have g2 := good_inv H hX g1
  ext w
  constructor
  · rintro ⟨x, hxΛ, rfl⟩
    obtain ⟨y, hy, hyx⟩ := (mem_img u Λ x).1 hxΛ
    have hyp : y ∈ H.perp (H.X Fr.f) := by
      have := good_perp H hX g2 (x : V) x.2
      rw [← hyx] at this
      change u.symm (u y) ∈ _ at this
      rwa [LinearEquiv.symm_apply_apply] at this
    refine ⟨⟨y, hyp⟩, hy, (mkW_eq H _ _ ?_).symm⟩
    change (x : V) - y ∈ _
    rw [← hyx]
    exact g1.2 y hyp
  · rintro ⟨y, hyΛ, rfl⟩
    exact ⟨⟨u y, good_perp H hX g1 y y.2⟩, (mem_img u Λ _).2 ⟨y, hyΛ, rfl⟩,
      mkW_eq H _ _ (g1.2 y y.2)⟩

theorem datum_eq_Lset : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r), LocNG.IsTermOver P d τ → (d.L : Set (H.Wb P.A.f)) = H.Lset τ.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset τ.abelian₂ P.B.f := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r P d τ hτ
  obtain ⟨-, -, ⟨n, hn, -, hΛ⟩, ⟨n', hn', -, hΛ'⟩, -⟩ := hτ
  constructor
  · rw [hΛ, Lset_img P.A hn, Lset_LamStd]
  · rw [hΛ', Lset_img P.B hn', Lset_LamStd]

end GlobalTheory.InnerRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericDatumLatticeEqPerpQuotientImageTermStatement
open Formalism.MainNotions.S

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGenericDatum_lattice_eq_perpQuotientImage_term : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r), LocNG.IsTermOver P d τ → (d.L : Set (H.Wb P.A.f)) = H.Lset τ.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset τ.abelian₂ P.B.f := by
  first | exact @GlobalTheory.InnerRead.datum_eq_Lset | exact GlobalTheory.InnerRead.datum_eq_Lset | (intros; apply GlobalTheory.InnerRead.datum_eq_Lset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalInnerDatumEqIffLocalDataEq
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.InnerDict

theorem inner_of_term : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (P : LocNG.FPair H r) (d : LocNG.Datum P) (τ : Loc.Term V M r), LocNG.IsTermOver P d τ → (d.L : Set (H.Wb P.A.f)) = H.Lset τ.abelian₂ P.A.f ∧ (d.L' : Set (H.Wb P.B.f)) = H.Lset τ.abelian₂ P.B.f := GlobalTheory.T.nonGenericDatum_lattice_eq_perpQuotientImage_term

theorem lset_eq_of_lsub_eq : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (Fr : LocNG.FrameD (locH Z p) D.R.rS), Fr.f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ G = Lsub Λ₂ G → (locH Z p).Lset (lattice₂ D Z.M p Λ₁) Fr.f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) Fr.f := GlobalTheory.T.localInnerLattice_eq_of_innerPreimage_eq

theorem lsub_eq_of_lset_eq : ∀ (D : D7) (Z : LocDat D) {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (Fr : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (Fr p).f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → (∀ p, (locH Z p).Lset (lattice₂ D Z.M p Λ₁) (Fr p).f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) (Fr p).f) → Lsub Λ₁ G = Lsub Λ₂ G := GlobalTheory.T.innerPreimage_eq_of_local_innerLattice_eq

theorem iota_eq_of_graph_eq : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 → ∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ := GlobalTheory.T.local_identification_eq_of_global_lattices_eq

theorem graph_eq_of_iota_eq : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ F = Lsub Λ₂ F → Lsub Λ₁ F' = Lsub Λ₂ F' → (∀ (p : PlF D) (g : Loc.SplitG (Z.M p).L), (Z.M p).split = some g → (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₁, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ₂, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩) → (gdat F F' Λ₁).2.2 = (gdat F F' Λ₂).2.2 := GlobalTheory.T.global_graph_eq_of_local_iota_agree

theorem datum_ext {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Loc.HermSp M V} {r : ℕ} {P : LocNG.FPair H r} (d d' : LocNG.Datum P) (h1 : d.L = d'.L) (h2 : d.L' = d'.L') (h3 : d.io = d'.io) : d = d' := by
  cases d; cases d'; simp only at h1 h2 h3; subst h1 h2 h3; rfl

theorem gdat_eq_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ₁ Λ₂ : LV D) (y₁ y₂ : Dat Z FP), LocOver Λ₁ y₁ → LocOver Λ₂ y₂ → (gdat F F' Λ₁ = gdat F F' Λ₂ ↔ y₁ = y₂) := by
  intro D X Y u u' F F' w _ _ Z FP hB _ Λ₁ Λ₂ y₁ y₂ h₁ h₂
  have hL : ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ p,
      ((y p).L : Set _) = (locH Z p).Lset (lattice₂ D Z.M p Λ) (FP p).A.f ∧
      ((y p).L' : Set _) = (locH Z p).Lset (lattice₂ D Z.M p Λ) (FP p).B.f ∧
      ∀ g, (Z.M p).split = some g → (y p).io = (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ, (FP p).A.f, (FP p).B.f, (FP p).A.T, (FP p).B.T⟩ := by
    intro Λ y hy p
    obtain ⟨τ, hτ, hlam⟩ := hy.2 p
    have h1 := inner_of_term (locH Z p) D.R.rS (FP p) (y p) τ hτ
    refine ⟨h1.1.trans (congrArg (fun L => (locH Z p).Lset L (FP p).A.f) hlam),
      h1.2.trans (congrArg (fun L => (locH Z p).Lset L (FP p).B.f) hlam), fun g hg => ?_⟩
    have h2 := (hτ.2.2.2.2 g hg).2
    have e4 : ∀ (L : Submodule (Z.M p).L.O (Vp D p)) (a b c e : (D.s.atP p).Fp), L = lattice₂ D Z.M p Λ →
        (locH Z p).iotaGraph g ⟨L, (FP p).A.f, (FP p).B.f, a, b⟩ =
          (locH Z p).iotaGraph g ⟨lattice₂ D Z.M p Λ, (FP p).A.f, (FP p).B.f, c, e⟩ := by
      intro L a b c e hL; subst hL; rfl
    exact h2.symm.trans (e4 _ _ _ _ _ hlam)
  constructor
  · intro hg
    have hF : Lsub Λ₁ F = Lsub Λ₂ F := congrArg (fun t => t.1) hg
    have hF' : Lsub Λ₁ F' = Lsub Λ₂ F' := congrArg (fun t => t.2.1) hg
    have hΓ := congrArg (fun t => t.2.2) hg
    funext p
    apply datum_ext
    · apply SetLike.coe_injective
      exact (hL Λ₁ y₁ h₁ p).1.trans ((lset_eq_of_lsub_eq D Z p F (FP p).A (hB p).1 Λ₁ Λ₂ h₁.1 h₂.1 hF).trans (hL Λ₂ y₂ h₂ p).1.symm)
    · apply SetLike.coe_injective
      exact (hL Λ₁ y₁ h₁ p).2.1.trans ((lset_eq_of_lsub_eq D Z p F' (FP p).B (hB p).2.1 Λ₁ Λ₂ h₁.1 h₂.1 hF').trans (hL Λ₂ y₂ h₂ p).2.1.symm)
    · cases hs : (Z.M p).split with
      | none => exact ((y₁ p).io_L hs).trans ((y₂ p).io_L hs).symm
      | some g =>
        exact ((hL Λ₁ y₁ h₁ p).2.2 g hs).trans ((iota_eq_of_graph_eq D Z FP _ _ F F' hB Λ₁ Λ₂ h₁.1 h₂.1 hF hF' hΓ p g hs).trans
          ((hL Λ₂ y₂ h₂ p).2.2 g hs).symm)
  · intro hy
    subst hy
    have hF : Lsub Λ₁ F = Lsub Λ₂ F :=
      lsub_eq_of_lset_eq D Z F (fun p => (FP p).A) (fun p => (hB p).1) Λ₁ Λ₂ h₁.1 h₂.1
        (fun p => (hL Λ₁ y₁ h₁ p).1.symm.trans (hL Λ₂ y₁ h₂ p).1)
    have hF' : Lsub Λ₁ F' = Lsub Λ₂ F' :=
      lsub_eq_of_lset_eq D Z F' (fun p => (FP p).B) (fun p => (hB p).2.1) Λ₁ Λ₂ h₁.1 h₂.1
        (fun p => (hL Λ₁ y₁ h₁ p).2.1.symm.trans (hL Λ₂ y₁ h₂ p).2.1)
    have hΓ := graph_eq_of_iota_eq D Z FP _ _ F F' hB Λ₁ Λ₂ h₁.1 h₂.1 hF hF'
      (fun p g hs => ((hL Λ₁ y₁ h₁ p).2.2 g hs).symm.trans ((hL Λ₂ y₁ h₂ p).2.2 g hs))
    exact Prod.ext hF (Prod.ext hF' hΓ)

end GlobalTheory.Unfold.InnerDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalInnerDatumEqIffLocalDataEqStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalInnerDatum_eq_iff_local_data_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ₁ Λ₂ : LV D) (y₁ y₂ : Dat Z FP), LocOver Λ₁ y₁ → LocOver Λ₂ y₂ → (gdat F F' Λ₁ = gdat F F' Λ₂ ↔ y₁ = y₂) := by
  first | exact @GlobalTheory.Unfold.InnerDict.gdat_eq_iff | exact GlobalTheory.Unfold.InnerDict.gdat_eq_iff | (intros; apply GlobalTheory.Unfold.InnerDict.gdat_eq_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalClassLatticesIffRationalClassLocalFrameP
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

namespace GlobalTheory.Unfold.RatCls

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T T' : D.host.E} {F : LFlag (D.sp.Y 0) D.R.rS T} {F' : LFlag (D.sp.Y 0) D.R.rS T'}

theorem principalPolarisation_exists_unique_section : (1 : GV D) ∈ H0 F F' := ⟨Subgroup.one_mem _, fun _ => rfl, fun _ => rfl⟩

theorem mul_mem_isometriesFixingBothFrames {g h : GV D} (hg : g ∈ H0 F F') (hh : h ∈ H0 F F') : g * h ∈ H0 F F' := by
  refine ⟨Subgroup.mul_mem _ hg.1 hh.1, fun a => ?_, fun a => ?_⟩
  · show g (h (frame F a)) = frame F a
    rw [hh.2.1 a, hg.2.1 a]
  · show g (h (frame F' a)) = frame F' a
    rw [hh.2.2 a, hg.2.2 a]

theorem inv_mem_isometriesFixingBothFrames {h : GV D} (hh : h ∈ H0 F F') : h⁻¹ ∈ H0 F F' := by
  refine ⟨Subgroup.inv_mem _ hh.1, fun a => ?_, fun a => ?_⟩
  · show h.symm (frame F a) = frame F a
    rw [LinearEquiv.symm_apply_eq, hh.2.1 a]
  · show h.symm (frame F' a) = frame F' a
    rw [LinearEquiv.symm_apply_eq, hh.2.2 a]

theorem ext_one (p : PlF D) : Ext p (1 : GV D) 1 := fun _ => rfl

theorem ext_mul {p : PlF D} {g h : GV D} {g' h' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p}
    (hg : Ext p g g') (hh : Ext p h h') : Ext p (g * h) (g' * h') := fun x => by
  show g' (h' (baseChange₂ D p x)) = baseChange₂ D p (g (h x))
  rw [hh x, hg (h x)]

theorem ext_inv {p : PlF D} {g : GV D} {g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p}
    (hg : Ext p g g') : Ext p g⁻¹ g'⁻¹ := fun x => by
  show g'.symm (baseChange₂ D p x) = baseChange₂ D p (g.symm x)
  rw [LinearEquiv.symm_apply_eq, hg, LinearEquiv.apply_symm_apply]

end GlobalTheory.Unfold.RatCls


open GlobalTheory.Unfold.RatCls in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem GlobalTheory.Unfold.ratCls_agree : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → Equivalence (GRel (Z := Z) (FP := FP) F F') ∧ (∀ y y' : Dat Z FP, GRel F F' y y' → (stabY F F' y).encard = (stabY F F' y').encard) ∧ ∀ (Λ₁ Λ₂ : LV D) (y₁ y₂ : Dat Z FP), LocOver Λ₁ y₁ → LocOver Λ₂ y₂ → (LRel F F' Λ₁ Λ₂ ↔ GRel F F' y₁ y₂) ∧ stabL F F' Λ₁ = stabY F F' y₁ := by
  intro D X Y u u' F F' w hZ hG Z FP hB hR
  have hact : ∀ p, ∃ act : MulAction (FP p).UW0 (LocNG.Datum (FP p)),
      (∀ (g : (FP p).UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧
      ∀ d (g : (FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d := by
    intro p
    refine GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) ?_ (hR p)
    rw [finrank_Vp]
    obtain ⟨j, hj⟩ := D.R.m_even
    have h2 := D.R.two_le_m
    show D.R.k + D.R.m - 1 = D.R.k + 2 * (D.R.m / 2 - 1) + 1
    omega
  choose act hmv _ using hact
  obtain ⟨hu, hw, -, hlift⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hZ hG Z FP hB hR
  have hdict := GlobalTheory.T.globalInnerDatum_eq_iff_local_data_eq D X Y u u' F F' w hZ hG Z FP hB hR

  have rm_fun : ∀ h ∈ H0 F F', ∀ y y₁ y₂ : Dat Z FP, RMoves h y y₁ → RMoves h y y₂ → y₁ = y₂ := by
    intro h hh y y₁ y₂ r₁ r₂
    funext p
    obtain ⟨g₁, e₁, m₁⟩ := r₁ p
    obtain ⟨g₂, e₂, m₂⟩ := r₂ p
    obtain rfl : g₁ = g₂ := (hu h p).unique e₁ e₂
    have hm := hw h hh p g₁ e₁
    exact ((hmv p ⟨g₁, hm⟩ _ _).1 m₁).symm.trans ((hmv p ⟨g₁, hm⟩ _ _).1 m₂)
  have rm_one : ∀ y : Dat Z FP, RMoves (1 : GV D) y y := by
    intro y p
    refine ⟨1, ext_one p, (hmv p 1 _ _).2 ?_⟩
    letI := act p
    exact one_smul _ _
  have rm_mul : ∀ h₁ ∈ H0 F F', ∀ h₂ ∈ H0 F F', ∀ y y' y'' : Dat Z FP,
      RMoves h₁ y y' → RMoves h₂ y' y'' → RMoves (h₂ * h₁) y y'' := by
    intro h₁ hh₁ h₂ hh₂ y y' y'' r₁ r₂ p
    obtain ⟨g₁, e₁, m₁⟩ := r₁ p
    obtain ⟨g₂, e₂, m₂⟩ := r₂ p
    let a₁ : (FP p).UW0 := ⟨g₁, hw h₁ hh₁ p g₁ e₁⟩
    let a₂ : (FP p).UW0 := ⟨g₂, hw h₂ hh₂ p g₂ e₂⟩
    refine ⟨g₂ * g₁, ext_mul e₂ e₁, (hmv p (a₂ * a₁) _ _).2 ?_⟩
    letI := act p
    have f₁ : a₁ • y p = y' p := (hmv p a₁ _ _).1 m₁
    have f₂ : a₂ • y' p = y'' p := (hmv p a₂ _ _).1 m₂
    show (a₂ * a₁) • y p = y'' p
    rw [mul_smul, f₁, f₂]
  have rm_inv : ∀ h ∈ H0 F F', ∀ y y' : Dat Z FP, RMoves h y y' → RMoves h⁻¹ y' y := by
    intro h hh y y' r p
    obtain ⟨g, e, m⟩ := r p
    let a : (FP p).UW0 := ⟨g, hw h hh p g e⟩
    refine ⟨g⁻¹, ext_inv e, (hmv p a⁻¹ _ _).2 ?_⟩
    letI := act p
    have f : a • y p = y' p := (hmv p a _ _).1 m
    show a⁻¹ • y' p = y p
    rw [inv_smul_eq_iff, f]
  have conj : ∀ h ∈ H0 F F', ∀ y y' : Dat Z FP, RMoves h y y' →
      ∀ k ∈ stabY F F' y, h * k * h⁻¹ ∈ stabY F F' y' := by
    intro h hh y y' hm k hk
    refine ⟨mul_mem_isometriesFixingBothFrames (mul_mem_isometriesFixingBothFrames hh hk.1) (inv_mem_isometriesFixingBothFrames hh), ?_⟩
    rw [mul_assoc]
    exact rm_mul _ (mul_mem_isometriesFixingBothFrames hk.1 (inv_mem_isometriesFixingBothFrames hh)) h hh _ _ _
      (rm_mul _ (inv_mem_isometriesFixingBothFrames hh) k hk.1 _ _ _ (rm_inv h hh y y' hm) hk.2) hm
  refine ⟨⟨fun y => ⟨1, principalPolarisation_exists_unique_section, rm_one y⟩, fun ⟨h, hh, hm⟩ => ⟨h⁻¹, inv_mem_isometriesFixingBothFrames hh, rm_inv h hh _ _ hm⟩,
    fun ⟨h₁, hh₁, m₁⟩ ⟨h₂, hh₂, m₂⟩ => ⟨h₂ * h₁, mul_mem_isometriesFixingBothFrames hh₂ hh₁, rm_mul h₁ hh₁ h₂ hh₂ _ _ _ m₁ m₂⟩⟩, ?_, ?_⟩
  · rintro y y' ⟨h, hh, hm⟩
    have e : stabY F F' y' = (MulAut.conj h) '' stabY F F' y := by
      ext k
      constructor
      · intro hk
        refine ⟨h⁻¹ * k * h⁻¹⁻¹, conj h⁻¹ (inv_mem_isometriesFixingBothFrames hh) y' y (rm_inv h hh y y' hm) k hk, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
      · rintro ⟨k, hk, rfl⟩
        exact conj h hh y y' hm k hk
    rw [e, (MulAut.conj h).injective.encard_image]
  · intro Λ₁ Λ₂ y₁ y₂ h₁ h₂
    have key : ∀ h ∈ H0 F F', ∀ (Λ Λ' : LV D) (y y' : Dat Z FP), LocOver Λ y → LocOver Λ' y' →
        (gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = gdat F F' Λ' ↔ RMoves h y y') := by
      intro h hh Λ Λ' y y' hl hl'
      obtain ⟨y'', hl'', hm''⟩ := hlift h hh Λ y hl
      rw [hdict _ _ y'' y' hl'' hl']
      constructor
      · rintro rfl
        exact hm''
      · intro hm
        exact rm_fun h hh y y'' y' hm'' hm
    refine ⟨⟨fun ⟨h, hh, he⟩ => ⟨h, hh, (key h hh _ _ _ _ h₁ h₂).1 he⟩,
      fun ⟨h, hh, hm⟩ => ⟨h, hh, (key h hh _ _ _ _ h₁ h₂).2 hm⟩⟩, ?_⟩
    ext h
    exact ⟨fun ⟨hh, he⟩ => ⟨hh, (key h hh _ _ _ _ h₁ h₁).1 he⟩, fun ⟨hh, hm⟩ => ⟨hh, (key h hh _ _ _ _ h₁ h₁).2 hm⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalClassLatticesIffRationalClassLocalFramePStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalClass_lattices_iff_rationalClass_localFramePairs : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → Equivalence (GRel (Z := Z) (FP := FP) F F') ∧ (∀ y y' : Dat Z FP, GRel F F' y y' → (stabY F F' y).encard = (stabY F F' y').encard) ∧ ∀ (Λ₁ Λ₂ : LV D) (y₁ y₂ : Dat Z FP), LocOver Λ₁ y₁ → LocOver Λ₂ y₂ → (LRel F F' Λ₁ Λ₂ ↔ GRel F F' y₁ y₂) ∧ stabL F F' Λ₁ = stabY F F' y₁ := by
  first | exact @GlobalTheory.Unfold.ratCls_agree | exact GlobalTheory.Unfold.ratCls_agree | (intros; apply GlobalTheory.Unfold.ratCls_agree <;> assumption)
end
