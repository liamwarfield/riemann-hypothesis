module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameIotaA
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFrameIota

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Proj

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hT_span_zero (e : Fin r → S.V) (v : S.V) (h : ∀ b, S.hT (e b) v = 0) :
    ∀ x ∈ Submodule.span E (Set.range e), S.hT x v = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact h b
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]

theorem proj_exists (Λ : Submodule (𝓞 E) S.V) (hL : Submodule.IsFullLattice E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {T' : E} (F' : LFlag S r T') :
    ∃ u : Fin r → S.V, ∀ l ∈ Λ, l - ∑ a, S.hT (F'.fl.e a) l • u a ∈ Lrep Λ F' := by
  obtain ⟨ρ, hρX, hρid⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract Λ hL.fg (Xsp F')
  have li := F'.fl.e_indep
  have hmem : ∀ y : Λ, ((ρ y : Λ) : S.V) ∈ Submodule.span E (Set.range F'.fl.e) := fun y => hρX y

  let co : Fin r → Λ →ₗ[𝓞 E] E := fun a =>
    { toFun := fun y => li.repr ⟨((ρ y : Λ) : S.V), hmem y⟩ a
      map_add' := fun y y' => by
        have e : (⟨((ρ (y + y') : Λ) : S.V), hmem (y + y')⟩ : Submodule.span E (Set.range F'.fl.e)) =
            ⟨((ρ y : Λ) : S.V), hmem y⟩ + ⟨((ρ y' : Λ) : S.V), hmem y'⟩ :=
          Subtype.ext (by simp only [map_add (f := _), Submodule.coe_add])
        rw [e, map_add (f := _), Finsupp.add_apply]
      map_smul' := fun c y => by
        have e : (⟨((ρ (c • y) : Λ) : S.V), hmem (c • y)⟩ : Submodule.span E (Set.range F'.fl.e)) =
            (algebraMap (𝓞 E) E c) • ⟨((ρ y : Λ) : S.V), hmem y⟩ :=
          Subtype.ext (by
            show ((ρ (c • y) : Λ) : S.V) = (algebraMap (𝓞 E) E c) • ((ρ y : Λ) : S.V)
            rw [LinearMap.map_smul, Submodule.coe_smul, algebraMap_smul])
        rw [e, LinearMap.map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  have hco : ∀ a y, co a y = li.repr ⟨((ρ y : Λ) : S.V), hmem y⟩ a := fun _ _ => rfl
  have hexp : ∀ y : Λ, ((ρ y : Λ) : S.V) = ∑ a, co a y • F'.fl.e a := by
    intro y
    have h := li.linearCombination_repr ⟨((ρ y : Λ) : S.V), hmem y⟩
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ (fun i (c : E) => c • F'.fl.e i) (fun i => zero_smul E _)] at h
    rw [← h]
    rfl
  have hR := fun a => PI.UnitaryGroupMassFormula.BetaModX.Iota.riesz S.hT S.herm S.nondeg Λ hL.fg hL.span_eq_top (co a)
  choose u hu using hR

  have hdual : ∀ a b, S.hT (F'.fl.e b) (u a) = if a = b then 1 else 0 := by
    intro a b
    obtain ⟨d, hd0, hdΛ⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_smul_mem Λ hL.span_eq_top (F'.fl.e b)
    have hdE : ((d : 𝓞 E) : E) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0
    have hdX : d • F'.fl.e b ∈ Xsp F' := by
      rw [← algebraMap_smul E d]
      exact (Xsp F').smul_mem _ (Submodule.subset_span ⟨b, rfl⟩)
    have hρd : ρ ⟨d • F'.fl.e b, hdΛ⟩ = ⟨d • F'.fl.e b, hdΛ⟩ := hρid _ hdX
    have hrep : co a ⟨d • F'.fl.e b, hdΛ⟩ = (d : E) * (if b = a then 1 else 0) := by
      rw [hco]
      have e : (⟨((ρ ⟨d • F'.fl.e b, hdΛ⟩ : Λ) : S.V), hmem _⟩ : Submodule.span E (Set.range F'.fl.e)) =
          ((d : 𝓞 E) : E) • ⟨F'.fl.e b, Submodule.subset_span ⟨b, rfl⟩⟩ :=
        Subtype.ext (by
          show ((ρ ⟨d • F'.fl.e b, hdΛ⟩ : Λ) : S.V) = ((d : 𝓞 E) : E) • F'.fl.e b
          rw [hρd]
          exact (algebraMap_smul E d _).symm)
      rw [e, LinearMap.map_smul, li.repr_eq_single b _ rfl, Finsupp.smul_apply, Finsupp.single_apply,
        smul_eq_mul]
    have h1 := hu a (d • F'.fl.e b) hdΛ
    rw [hrep, ← algebraMap_smul E d, LinearMap.map_smul, smul_eq_mul] at h1
    have h2 : S.hT (u a) (F'.fl.e b) = if b = a then 1 else 0 := mul_left_cancel₀ hdE h1
    rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'', h2]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (Ne.symm hab), if_neg hab, star_zero]
  refine ⟨u, fun l hl => ⟨?_, ?_⟩⟩
  ·
    refine Λ.sub_mem hl ?_
    have hU' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hU
    rw [← hU', Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    have hval : S.hT y (∑ a, S.hT (F'.fl.e a) l • u a) = S.hT ((ρ ⟨y, hy⟩ : Λ) : S.V) l := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hexp, map_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.map_smul, smul_eq_mul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (u a) y, hu a y hy, starRingEnd_apply, mul_comm]
    rw [hval]
    obtain ⟨o, ho⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.int_val hU (ρ ⟨y, hy⟩).2 hl
    rw [← ho, Submodule.mem_one]
    exact ⟨o, rfl⟩
  ·
    show l - ∑ a, S.hT (F'.fl.e a) l • u a ∈ orth S (Xsp F')
    rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.mem_orth'']
    refine hT_span_zero F'.fl.e _ fun b => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [LinearMap.map_smul, smul_eq_mul, hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, sub_self]

end Proj

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem glob_beta {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hF : FixedHyp D Λ F) (hc' : IsFixedConv Λ (gS D) F') (hc'' : IsFixedConv Λ (gS D) F'')
    (ha' : IsAdmissible Λ (gS D) F F') (ha'' : IsAdmissible Λ (gS D) F F'')
    (hP : IsPair Λ F F' F'' β (gS D)) :
    ∀ w ∈ Lrep Λ F', β w - w ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F := by
  intro w hw
  have hg : gS D ≠ 0 := Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨l, hl, hlw⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.iota_gen Λ hF.1 hF.2.1 (gS D) hg F F' hF.2.2.2 ha' w hw
  have h2 := (hP.2.2.2 w hw l hl).1 hlw
  have hle : ∀ F₁ : LFlag (D.sp.Y 0) D.R.rS T', IsAdmissible Λ (gS D) F F₁ → IsFixedConv Λ (gS D) F₁ →
      NgX Λ (gS D) F F₁ ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F := by
    intro F₁ ha hc
    unfold NgX
    exact sup_le le_rfl (Formalism.L2.SG.Pf.Act.xlam_le Λ (gS D) ha hF.2.2.2 hc)
  have e : β w - w = (l - w) - (l - β w) := by abel
  rw [e]
  exact Submodule.sub_mem _ (hle F' ha' hc' hlw) (hle F'' ha'' hc'' h2)

end D7

end Formalism.L2.SG.Pf.ScalarFrameIota
end
end

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFrameIota

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel
  Formalism.L2.SG.Pf.ScalarFramePf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Local

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem mem_perpP {X : Submodule (D.s.atP p).Ep (Vp D p)} {v : Vp D p} :
    v ∈ (locH Z p).perp X ↔ ∀ x ∈ X, (locH Z p).h v x = 0 := Iff.rfl

def XO (X : Submodule (D.s.atP p).Ep (Vp D p)) : Submodule (Z.M p).L.O (Vp D p) where
  carrier := (X : Set (Vp D p))
  add_mem' hx hy := X.add_mem hx hy
  zero_mem' := X.zero_mem
  smul_mem' c x hx := by rw [Subring.smul_def]; exact X.smul_mem _ hx

theorem h_bc (x y : (VS D).V) :
    (locH Z p).h (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE ((VS D).hT y x) := by
  have h := hermitian_base_change_smul (Z := Z) (p := p) 1 x y
  rw [one_smul, one_mul] at h
  rw [h]
  rfl

theorem betaL_proj {r : ℕ} (e u : Fin r → (VS D).V) (v : Vp D p) :
    betaL p (LinearMap.id - ∑ a, ((VS D).hT (e a)).smulRight (u a)) v =
      v - ∑ a, (locH Z p).h v (baseChange₂ D p (e a)) • baseChange₂ D p (u a) := by
  let φ : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p :=
    { toFun := fun v => v - ∑ a, (locH Z p).h v (baseChange₂ D p (e a)) • baseChange₂ D p (u a)
      map_add' := fun v w => by
        simp only [(locH Z p).h_add_left, add_smul, Finset.sum_add_distrib]
        abel
      map_smul' := fun c v => by
        simp only [(locH Z p).h_smul_left, mul_smul, ← Finset.smul_sum, smul_sub, RingHom.id_apply] }
  have hφ : betaL p (LinearMap.id - ∑ a, ((VS D).hT (e a)).smulRight (u a)) = φ := by
    refine (Pi.basisFun (D.s.atP p).Ep (Fin (nV D))).ext fun i => ?_
    rw [betaL_basis]
    show _ = Pi.basisFun (D.s.atP p).Ep (Fin (nV D)) i -
      ∑ a, (locH Z p).h (Pi.basisFun (D.s.atP p).Ep (Fin (nV D)) i) (baseChange₂ D p (e a)) • baseChange₂ D p (u a)
    rw [Pi.basisFun_apply, ← baseChangeAt_frame]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
      LinearMap.smulRight_apply, map_sub]
    rw [baseChangeAt_sum (p := p) Finset.univ]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [h_bc]
  exact LinearMap.congr_fun hφ v

theorem loc_gen (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hL : Submodule.IsLattice D.host.E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) {T' : D.host.E} (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (X₁ : Submodule (D.s.atP p).Ep (Vp D p)) (hX : ∀ a, baseChange₂ D p (F'.fl.e a) ∈ X₁) {x : Vp D p}
    (hx : x ∈ lattice₂ D Z.M p Λ) (hxo : x ∈ (locH Z p).perp X₁) :
    x ∈ Submodule.span (Z.M p).L.O (baseChange₂ D p '' (Lrep Λ F' : Set (VS D).V)) := by
  have hFull : Submodule.IsFullLattice D.host.E Λ := by
    let := hL
    refine { span_eq_top := ?_ }
    let W := Submodule.span D.host.E (Λ : Set (VS D).V)
    change W = ⊤
    by_contra h
    let e : (VS D).V ≃ₗ⋆[D.host.E] (VS D).V :=
      (VS D).frame.equivFun.trans ((starLinearEquiv D.host.E).trans (VS D).frame.equivFun.symm)
    let g : (VS D).V →ₗ[D.host.E] Module.Dual D.host.E W :=
      (LinearMap.domRestrict' W).comp ((VS D).hT.comp e.toLinearMap)
    have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E (VS D).V := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : D.host.E) : a • e x ∈ Λ := by
      rw [← hU, Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      intro y hy
      have hxy : (VS D).hT (e x) y = 0 :=
        congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      have hyx : (VS D).hT y (e x) = 0 := by
        have hh := (VS D).herm.eq (e x) y
        simpa [hxy] using hh.symm
      simp [map_smul, hyx]
    let i : D.host.E →ₗ[𝓞 D.host.E] Λ :=
      ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict Λ hsmul
    let : Module.Finite (𝓞 D.host.E) Λ := Module.Finite.iff_fg.mpr hL.fg
    let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
  obtain ⟨u, hu⟩ := proj_exists Λ hFull hU F'
  have hPv : ∀ v, (LinearMap.id - ∑ a, ((VS D).hT (F'.fl.e a)).smulRight (u a) :
      (VS D).V →ₗ[D.host.E] (VS D).V) v = v - ∑ a, (VS D).hT (F'.fl.e a) v • u a := fun v => by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
      LinearMap.smulRight_apply]
  have h1 : betaL p (LinearMap.id - ∑ a, ((VS D).hT (F'.fl.e a)).smulRight (u a)) x = x := by
    have h0 : ∀ a ∈ Finset.univ, (locH Z p).h x (baseChange₂ D p (F'.fl.e a)) • baseChange₂ D p (u a) = 0 := fun a _ => by
      rw [(mem_perpP Z p).1 hxo _ (hX a), zero_smul]
    rw [betaL_proj, Finset.sum_eq_zero h0, sub_zero]
  have h2 : ∀ y ∈ lattice₂ D Z.M p Λ, betaL p (LinearMap.id - ∑ a, ((VS D).hT (F'.fl.e a)).smulRight (u a)) y ∈
      Submodule.span (Z.M p).L.O (baseChange₂ D p '' (Lrep Λ F' : Set (VS D).V)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      rw [betaL_bc]
      exact Submodule.subset_span ⟨_, by rw [hPv]; exact hu v hv, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y y' _ _ hy hy' => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hy'
    | smul o y _ hy =>
      rw [Subring.smul_def, map_smul, ← Subring.smul_def]
      exact Submodule.smul_mem _ _ hy
  rw [← h1]
  exact h2 x hx

theorem g_loc (Λ : Submodule (𝓞 D.host.E) (VS D).V) (gg : Loc.SplitG (Z.M p).L)
    (hgg : (Z.M p).split = some gg) {l : (VS D).V} (hl : l ∈ Λ) :
    baseChange₂ D p (((gS D : ℕ) : 𝓞 D.host.E) • l) ∈
      (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (gg.q : (D.s.atP p).Fp))
        (lattice₂ D Z.M p Λ) := by
  obtain ⟨-, -, -, -, -, hm⟩ := Z.agree p
  rw [hgg] at hm
  rcases hs : (D.s.atP p).split with _ | sg
  · rw [hs] at hm
    simp at hm
  · rw [hs] at hm
    obtain ⟨-, hq⟩ := hm
    have hres : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := (D.s_split p).1 (by rw [hs]; rfl)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, gS D = Loc.resChar p * k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hres
      rcases hres with h | h
      · exact ⟨D.host.g 1, by rw [h]; rfl⟩
      · exact ⟨D.host.g 0, by rw [h, mul_comm]; rfl⟩
    have e : baseChange₂ D p (((gS D : ℕ) : 𝓞 D.host.E) • l) = (k : (Z.M p).L.O) •
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (gg.q : (D.s.atP p).Fp) • baseChange₂ D p l) := by
      rw [Subring.smul_def, hq, sg.q_eq, map_natCast, Subring.coe_natCast, smul_smul, ← Nat.cast_mul,
        mul_comm, ← hk, Nat.cast_smul_eq_nsmul (𝓞 D.host.E), Nat.cast_smul_eq_nsmul (D.s.atP p).Ep,
        map_nsmul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨baseChange₂ D p l, Submodule.subset_span ⟨l, hl, rfl⟩, rfl⟩)

theorem bcP_N (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (gg : Loc.SplitG (Z.M p).L) (hgg : (Z.M p).split = some gg) {v : (VS D).V}
    (hv : v ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F) :
    baseChange₂ D p v ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (gg.q : (D.s.atP p).Fp))
        (lattice₂ D Z.M p Λ) ⊔
      (lattice₂ D Z.M p Λ ⊓ XO Z p ((locH Z p).X (fun a => sF Z p a • baseChange₂ D p (frame F a)))) := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add (f := _)]
  refine Submodule.add_mem_sup ?_ ⟨Submodule.subset_span ⟨z, hz.1, rfl⟩, ?_⟩
  · obtain ⟨w, hw, rfl⟩ := (Formalism.L2.SG.Pf.mem_gSmul (gS D) Λ y).1 hy
    exact g_loc Z p Λ gg hgg hw
  · have h := hz.2
    rw [Xsp_eq_Xs] at h
    exact bcP_mem_X Z p (frame F) (sF Z p) (isUnit_sF Z p) h

theorem loc_beta (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (gg : Loc.SplitG (Z.M p).L) (hgg : (Z.M p).split = some gg)
    (hglob : ∀ w ∈ Lrep Λ F', β w - w ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F)
    {x : Vp D p} (hx : x ∈ Submodule.span (Z.M p).L.O (baseChange₂ D p '' (Lrep Λ F' : Set (VS D).V))) :
    betaP p β x - x ∈ (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (gg.q : (D.s.atP p).Fp))
        (lattice₂ D Z.M p Λ) ⊔
      (lattice₂ D Z.M p Λ ⊓ XO Z p ((locH Z p).X (fun a => sF Z p a • baseChange₂ D p (frame F a)))) := by
  have key : ∀ w ∈ Lrep Λ F', betaP p β (baseChange₂ D p w) - baseChange₂ D p w ∈
      (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (gg.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ) ⊔
        (lattice₂ D Z.M p Λ ⊓ XO Z p ((locH Z p).X (fun a => sF Z p a • baseChange₂ D p (frame F a)))) := by
    intro w hw
    rw [betaP_bc, ← map_sub]
    exact bcP_N Z p Λ F gg hgg (hglob w hw)
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    exact key w hw
  | zero => simp
  | add a b _ _ ha hb =>
    rw [map_add (f := _), add_sub_add_comm]
    exact add_mem ha hb
  | smul c a _ ha =>
    have e : betaP p β (c • a) - c • a = c • (betaP p β a - a) := by
      simp only [Subring.smul_def, map_smul, smul_sub]
    rw [e]
    exact Submodule.smul_mem _ c ha

theorem iotaG_main (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F' F'' : LFlag (D.sp.Y 0) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hF : FixedHyp D Λ F) (hc' : IsFixedConv Λ (gS D) F') (hc'' : IsFixedConv Λ (gS D) F'')
    (ha' : IsAdmissible Λ (gS D) F F') (ha'' : IsAdmissible Λ (gS D) F F'')
    (hP : IsPair Λ F F' F'' β (gS D))
    (hG : GFacts Λ (frame F) (frameAct (frame F') (admXi D Λ F F')⁻¹)
      (frameAct (frame F'') (admXi D Λ F F'')⁻¹) β)
    (gg : Loc.SplitG (Z.M p).L) (hgg : (Z.M p).split = some gg) :
    IotaG (locH Z p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (gg.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ)
      (fun a => sF Z p a • baseChange₂ D p (frame F a))
      (fun b => sF' Z p b • baseChange₂ D p (frameAct (frame F') (admXi D Λ F F')⁻¹ b))
      (fun b => sF' Z p b • baseChange₂ D p (frameAct (frame F'') (admXi D Λ F F'')⁻¹ b)) (betaP p β) := by
  have hglob := glob_beta Λ F F' F'' β hF hc' hc'' ha' ha'' hP
  have hX1 : ∀ a, baseChange₂ D p (F'.fl.e a) ∈
      (locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (frameAct (frame F') (admXi D Λ F F')⁻¹ b)) := by
    intro a
    refine bcP_mem_X Z p _ (sF' Z p) (isUnit_sF' Z p) ?_
    have h := Xs_frameAct_inv (S := VS D) (frame F') (admXi D Λ F F') (admissibility_witness_unitriangular Λ F F').1
      (admissibility_witness_unitriangular Λ F F').2
    have h2 : F'.fl.e a ∈ Xsp F' := Submodule.subset_span ⟨a, rfl⟩
    rw [Xsp_eq_Xs, ← h] at h2
    exact h2
  have hL1 : ∀ x' ∈ lattice₂ D Z.M p Λ, x' ∈ (locH Z p).perp
      ((locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (frameAct (frame F') (admXi D Λ F F')⁻¹ b))) →
      betaP p β x' - x' ∈
        (locH Z p).smulLat (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (gg.q : (D.s.atP p).Fp))
          (lattice₂ D Z.M p Λ) ⊔
        (lattice₂ D Z.M p Λ ⊓ XO Z p ((locH Z p).X (fun a => sF Z p a • baseChange₂ D p (frame F a)))) :=
    fun x' hx hxo => loc_beta Z p Λ F F' β gg hgg hglob (loc_gen Z p Λ hF.1 hF.2.1 F' _ hX1 hx hxo)
  have hX0 : ∀ a ∈ (locH Z p).X (fun a => sF Z p a • baseChange₂ D p (frame F a)),
      ∀ b ∈ (locH Z p).X (fun a => sF Z p a • baseChange₂ D p (frame F a)), (locH Z p).h a b = 0 := by
    apply iso_span
    intro i j
    rw [h_bcP, brS, hG.fiso j i, map_zero, mul_zero]
  have hiso : ∀ v w, (locH Z p).h (betaP p β v) (betaP p β w) = (locH Z p).h v w := betaP_iso Z p β hG.iso
  constructor
  · intro x x' hx hx' hxo hx'o hd
    obtain ⟨n, hn, a, ha, hna⟩ := Submodule.mem_sup.1 (hL1 x' hx' hx'o)
    refine ⟨x + a, betaP p β x', Submodule.add_mem _ hx ha.1, betaP_lat Z p β Λ hG.lam hx', ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_perpP]
      intro b hb
      rw [(locH Z p).h_add_left, (mem_perpP Z p).1 hxo b hb, hX0 a ha.2 b hb, add_zero]
    · rw [mem_perpP]
      intro b hb
      have hb1 := betaP_symm_mem_X Z p β _ _ (sF' Z p) (isUnit_sF' Z p) hG.xmap' hb
      rw [← LinearEquiv.apply_symm_apply (betaP p β) b, hiso]
      exact (mem_perpP Z p).1 hx'o _ hb1
    · rw [show x - (x + a) = -a by abel]
      exact Submodule.neg_mem _ ha.2
    · rw [sub_self]
      exact Submodule.zero_mem _
    · have e : x + a - betaP p β x' = (x - x') - n := by
        rw [← sub_add_cancel (betaP p β x') x', ← hna]
        abel
      rw [e]
      exact Submodule.sub_mem _ hd hn
  · intro x x'' hx hx'' hxo hx''o hd
    obtain ⟨y, rfl⟩ := (betaP p β).surjective x''
    rw [LinearEquiv.symm_apply_apply]
    have hy : y ∈ lattice₂ D Z.M p Λ := by
      have h := betaP_symm_lat Z p β Λ hG.lam' hx''
      rwa [LinearEquiv.symm_apply_apply] at h
    have hyo : y ∈ (locH Z p).perp
        ((locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (frameAct (frame F') (admXi D Λ F F')⁻¹ b))) := by
      rw [mem_perpP]
      intro b hb
      rw [← hiso]
      exact (mem_perpP Z p).1 hx''o _ (betaP_mem_X Z p β _ _ (sF' Z p) (isUnit_sF' Z p) hG.xmap hb)
    obtain ⟨n, hn, a, ha, hna⟩ := Submodule.mem_sup.1 (hL1 y hy hyo)
    refine ⟨x - a, y, Submodule.sub_mem _ hx ha.1, hy, ?_, hyo, ?_, ?_, ?_⟩
    · rw [mem_perpP]
      intro b hb
      rw [ScalarFramePf.h_sub_left, (mem_perpP Z p).1 hxo b hb, hX0 a ha.2 b hb, sub_zero]
    · rw [sub_sub_cancel]
      exact ha.2
    · rw [sub_self]
      exact Submodule.zero_mem _
    · have e : x - a - y = (x - betaP p β y) + n := by
        rw [← sub_add_cancel (betaP p β y) y, ← hna]
        abel
      rw [e]
      exact Submodule.add_mem _ hd hn

end Local

end Formalism.L2.SG.Pf.ScalarFrameIota

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.ScalarFramePf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iotaStep_holds : ScalarFramePf.IotaStep := by
  intro D Z Λ T T' F F' F'' β hF hl' hl'' hc' hc'' ha' ha'' hP hg' hg'' hs hsc hG' hG'' hT hT' p gg hgg
  exact ScalarFrameIota.iotaG_main Z p Λ F F' F'' β hF hc' hc'' ha' ha'' hP
    (gfacts_of Λ F F' F'' β hF hl' hl'' hc' hc'' hP hs hsc hG' hG'' hT hT') gg hgg

end Formalism.L2.SG.Pf
