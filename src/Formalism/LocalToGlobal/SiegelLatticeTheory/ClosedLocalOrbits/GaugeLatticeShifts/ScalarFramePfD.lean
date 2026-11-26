module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfC
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfB
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

section Beta

variable {D : D7} (Z : LocDat D) (p : PlF D)

def betaL (β : (VS D).V →ₗ[D.host.E] (VS D).V) : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p :=
  (Pi.basisFun (D.s.atP p).Ep (Fin (nV D))).constr (D.s.atP p).Ep fun i => baseChange₂ D p (β ((VS D).frame i))

theorem baseChangeAt_eq_sum (x : (VS D).V) :
    baseChange₂ D p x = ∑ i, (D.s.atP p).ιE ((VS D).frame.repr x i) • Pi.basisFun (D.s.atP p).Ep (Fin (nV D)) i := by
  funext j
  have hj : baseChange₂ D p x j = (D.s.atP p).ιE ((VS D).frame.repr x j) := rfl
  simp [hj, Finset.sum_apply, Pi.single_apply]

theorem betaL_bc (β : (VS D).V →ₗ[D.host.E] (VS D).V) (x : (VS D).V) :
    betaL p β (baseChange₂ D p x) = baseChange₂ D p (β x) := by
  have hx : x = ∑ i, (VS D).frame.repr x i • (VS D).frame i := ((VS D).frame.sum_repr x).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [baseChangeAt_eq_sum p x, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [hx, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, baseChange_smul₂]
  congr 1
  simp only [betaL, Module.Basis.constr_basis]

theorem betaL_basis (β : (VS D).V →ₗ[D.host.E] (VS D).V) (i : Fin (nV D)) :
    betaL p β (Pi.basisFun (D.s.atP p).Ep (Fin (nV D)) i) = baseChange₂ D p (β ((VS D).frame i)) := by
  simp only [betaL, Module.Basis.constr_basis]

def betaP (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p :=
  LinearEquiv.ofLinear (betaL p (β : (VS D).V →ₗ[D.host.E] (VS D).V))
    (betaL p (β.symm : (VS D).V →ₗ[D.host.E] (VS D).V))
    ((Pi.basisFun (D.s.atP p).Ep (Fin (nV D))).ext fun i => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [betaL_basis, betaL_bc, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        baseChangeAt_frame, Pi.basisFun_apply])
    ((Pi.basisFun (D.s.atP p).Ep (Fin (nV D))).ext fun i => by
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [betaL_basis, betaL_bc, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        baseChangeAt_frame, Pi.basisFun_apply])

theorem betaP_bc (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V) :
    betaP p β (baseChange₂ D p x) = baseChange₂ D p (β x) := by
  show betaL p (β : (VS D).V →ₗ[D.host.E] (VS D).V) (baseChange₂ D p x) = _
  rw [betaL_bc]
  rfl

theorem betaP_symm_bc (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V) :
    (betaP p β).symm (baseChange₂ D p x) = baseChange₂ D p (β.symm x) := by
  show betaL p (β.symm : (VS D).V →ₗ[D.host.E] (VS D).V) (baseChange₂ D p x) = _
  rw [betaL_bc]
  rfl

theorem vp_eq_sum (v : Vp D p) : v = ∑ i, v i • baseChange₂ D p ((VS D).frame i) := by
  funext j
  simp [baseChangeAt_frame, Finset.sum_apply, Pi.single_apply]

private theorem h_bc_lemma (u w : (VS D).V) :
    (locH Z p).h (baseChange₂ D p u) (baseChange₂ D p w) = (D.s.atP p).ιE (brS (VS D) u w) := by
  have hb : ∀ (v : (VS D).V) (k : Fin (nV D)), baseChange₂ D p v k = (D.s.atP p).ιE ((VS D).frame.repr v k) :=
    fun _ _ => rfl
  have hu : u = ∑ k, (VS D).frame.repr u k • (VS D).frame k := ((VS D).frame.sum_repr u).symm
  have hw : w = ∑ l, (VS D).frame.repr w l • (VS D).frame l := ((VS D).frame.sum_repr w).symm
  show LocFacts₂ Z.M p (baseChange₂ D p u) (baseChange₂ D p w) = _
  simp only [LocFacts₂, hb, cj_iota (Z.hcj p), gramV, brS]
  conv_rhs => rw [hw, hu]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, RingHom.id_apply, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem h_sum_bc {ι : Type} [Fintype ι] (a b : ι → (D.s.atP p).Ep) (x y : ι → (VS D).V) :
    (locH Z p).h (∑ i, a i • baseChange₂ D p (x i)) (∑ j, b j • baseChange₂ D p (y j)) =
      ∑ i, ∑ j, a i * (Z.M p).L.cj (b j) * (D.s.atP p).ιE (brS (VS D) (x i) (y j)) := by
  have hL : ∀ (f : ι → Vp D p) (w : Vp D p),
      (locH Z p).h (∑ i, f i) w = ∑ i, (locH Z p).h (f i) w := fun f w =>
    map_sum (AddMonoidHom.mk' (fun v => (locH Z p).h v w) fun v v' => (locH Z p).h_add_left v v' w) f
      Finset.univ
  have hR : ∀ (v : Vp D p) (g : ι → Vp D p),
      (locH Z p).h v (∑ j, g j) = ∑ j, (locH Z p).h v (g j) := by
    intro v g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [(locH Z p).h_herm (∑ j, g j) v, hL, map_sum]
    exact Finset.sum_congr rfl fun j _ => ((locH Z p).h_herm (g j) v).symm
  have hS : ∀ (v : Vp D p) (c : (D.s.atP p).Ep) (w : Vp D p),
      (locH Z p).h v (c • w) = (Z.M p).L.cj c * (locH Z p).h v w := by
    intro v c w
    rw [(locH Z p).h_herm (c • w) v, (locH Z p).h_smul_left, map_mul, ← (locH Z p).h_herm w v]
  rw [hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(locH Z p).h_smul_left, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hS, h_bc_lemma]
  ring

theorem betaP_iso (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hiso : ∀ x y, (VS D).hT (β x) (β y) = (VS D).hT x y) (v w : Vp D p) :
    (locH Z p).h (betaP p β v) (betaP p β w) = (locH Z p).h v w := by
  rw [vp_eq_sum p v, vp_eq_sum p w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, betaP_bc]
  rw [h_sum_bc, h_sum_bc]
  simp only [brS, hiso]

theorem betaP_lat (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hβ : ∀ v ∈ Λ, β v ∈ Λ) {x : Vp D p} (hx : x ∈ lattice₂ D Z.M p Λ) : betaP p β x ∈ lattice₂ D Z.M p Λ := by
  unfold lattice₂ at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, hv, rfl⟩ := hy
    rw [betaP_bc]
    exact Submodule.subset_span ⟨β v, hβ v hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have e : betaP p β (c • y) = c • betaP p β y := LinearMapClass.map_smul_of_tower _ c y
    rw [e]
    exact Submodule.smul_mem _ c hy

theorem betaP_symm_lat (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hβ : ∀ v ∈ Λ, β.symm v ∈ Λ) {x : Vp D p} (hx : x ∈ lattice₂ D Z.M p Λ) :
    (betaP p β).symm x ∈ lattice₂ D Z.M p Λ := by
  unfold lattice₂ at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, hv, rfl⟩ := hy
    rw [betaP_symm_bc]
    exact Submodule.subset_span ⟨β.symm v, hβ v hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have e : (betaP p β).symm (c • y) = c • (betaP p β).symm y := LinearMapClass.map_smul_of_tower _ c y
    rw [e]
    exact Submodule.smul_mem _ c hy

theorem bcP_mem_X (u : Fin (D.R.rS + 1) → (VS D).V) (c : Fin (D.R.rS + 1) → (D.s.atP p).Ep)
    (hc : ∀ a, IsUnit (c a)) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => u a.castSucc)) :
    baseChange₂ D p x ∈ (locH Z p).X (fun a => c a • baseChange₂ D p (u a)) := by
  show baseChange₂ D p x ∈ Submodule.span (D.s.atP p).Ep
    (Set.range fun a : Fin D.R.rS => c a.castSucc • baseChange₂ D p (u a.castSucc))
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    show baseChange₂ D p (u a.castSucc) ∈ _
    have h1 : baseChange₂ D p (u a.castSucc) =
        (((hc a.castSucc).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep) • (c a.castSucc • baseChange₂ D p (u a.castSucc)) := by
      rw [smul_smul, IsUnit.val_inv_mul, one_smul]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul e y _ hy => rw [baseChange_smul₂]; exact Submodule.smul_mem _ _ hy

theorem betaP_mem_X (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (u v : Fin (D.R.rS + 1) → (VS D).V)
    (c : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (hc : ∀ a, IsUnit (c a))
    (hmap : ∀ a : Fin D.R.rS, β (u a.castSucc) ∈
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => v b.castSucc))
    {x : Vp D p} (hx : x ∈ (locH Z p).X (fun a => c a • baseChange₂ D p (u a))) :
    betaP p β x ∈ (locH Z p).X (fun a => c a • baseChange₂ D p (v a)) := by
  show betaP p β x ∈ Submodule.span (D.s.atP p).Ep
    (Set.range fun a : Fin D.R.rS => c a.castSucc • baseChange₂ D p (v a.castSucc))
  replace hx : x ∈ Submodule.span (D.s.atP p).Ep
      (Set.range fun a : Fin D.R.rS => c a.castSucc • baseChange₂ D p (u a.castSucc)) := hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    show betaP p β (c a.castSucc • baseChange₂ D p (u a.castSucc)) ∈ _
    rw [map_smul, betaP_bc]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p v c hc (hmap a))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul e y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

theorem betaP_symm_mem_X (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (u v : Fin (D.R.rS + 1) → (VS D).V)
    (c : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (hc : ∀ a, IsUnit (c a))
    (hmap : ∀ a : Fin D.R.rS, β.symm (v a.castSucc) ∈
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => u b.castSucc))
    {x : Vp D p} (hx : x ∈ (locH Z p).X (fun a => c a • baseChange₂ D p (v a))) :
    (betaP p β).symm x ∈ (locH Z p).X (fun a => c a • baseChange₂ D p (u a)) := by
  show (betaP p β).symm x ∈ Submodule.span (D.s.atP p).Ep
    (Set.range fun a : Fin D.R.rS => c a.castSucc • baseChange₂ D p (u a.castSucc))
  replace hx : x ∈ Submodule.span (D.s.atP p).Ep
      (Set.range fun a : Fin D.R.rS => c a.castSucc • baseChange₂ D p (v a.castSucc)) := hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    show (betaP p β).symm (c a.castSucc • baseChange₂ D p (v a.castSucc)) ∈ _
    rw [map_smul, betaP_symm_bc]
    exact Submodule.smul_mem _ _ (bcP_mem_X Z p u c hc (hmap a))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul e y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

end Beta

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

section Quot

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem perp_map (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h21 : ∀ y ∈ X2, e.symm y ∈ X1) {x : V} (hx : x ∈ H.perp X1) : e x ∈ H.perp X2 := by
  intro y hy
  rw [show y = e (e.symm y) from (e.apply_symm_apply y).symm, hiso]
  exact hx _ (h21 y hy)

theorem perp_map_symm (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) {y : V} (hy : y ∈ H.perp X2) : e.symm y ∈ H.perp X1 := by
  intro x hx
  rw [← hiso, e.apply_symm_apply]
  exact hy _ (h12 x hx)

def perpEquiv (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) (h21 : ∀ y ∈ X2, e.symm y ∈ X1) : ↥(H.perp X1) ≃ₗ[E] ↥(H.perp X2) :=
  e.ofSubmodules (H.perp X1) (H.perp X2) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact perp_map H e hiso X1 X2 h21 hx
    · intro hy
      exact ⟨e.symm y, perp_map_symm H e hiso X1 X2 h12 hy, e.apply_symm_apply y⟩)

def qEquiv (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) (h21 : ∀ y ∈ X2, e.symm y ∈ X1) :
    (↥(H.perp X1) ⧸ X1.comap (H.perp X1).subtype) ≃ₗ[E] (↥(H.perp X2) ⧸ X2.comap (H.perp X2).subtype) :=
  Submodule.Quotient.equiv _ _ (perpEquiv H e hiso X1 X2 h12 h21) (by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨x, hx⟩, hx1, hxy⟩
      have h' : e x = y := congrArg Subtype.val hxy
      rw [← h']
      exact h12 x hx1
    · intro hy2
      refine ⟨⟨e.symm y, perp_map_symm H e hiso X1 X2 h12 hy⟩, h21 y hy2, ?_⟩
      apply Subtype.ext
      show e (e.symm y) = y
      exact e.apply_symm_apply y)

theorem qEquiv_mk (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) (h21 : ∀ y ∈ X2, e.symm y ∈ X1) (x : ↥(H.perp X1)) :
    qEquiv H e hiso X1 X2 h12 h21 (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (perpEquiv H e hiso X1 X2 h12 h21 x) := rfl

theorem mk_eq_iff (X : Submodule E V) (x y : ↥(H.perp X)) :
    (Submodule.Quotient.mk x : ↥(H.perp X) ⧸ X.comap (H.perp X).subtype) = Submodule.Quotient.mk y ↔
      (x : V) - y ∈ X := by
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]

theorem smul_mk_eq (X : Submodule E V) (c₁ c₂ : E) (x y : ↥(H.perp X)) (h : c₁ • (x : V) - c₂ • (y : V) ∈ X) :
    c₁ • (Submodule.Quotient.mk x : ↥(H.perp X) ⧸ X.comap (H.perp X).subtype) = c₂ • Submodule.Quotient.mk y := by
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, mk_eq_iff]
  simpa using h

theorem iso_span {ι : Type} (w : ι → V) (hw : ∀ i j, H.h (w i) (w j) = 0) :
    ∀ a ∈ Submodule.span E (Set.range w), ∀ b ∈ Submodule.span E (Set.range w), H.h a b = 0 := by
  have hle : Submodule.span E (Set.range w) ≤ H.perp (Submodule.span E (Set.range w)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_perp_span]
    rintro _ ⟨j, rfl⟩
    exact hw i j
  intro a ha b hb
  exact hle ha b hb

end Quot

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Assembly

variable {D : D7} (Z : LocDat D) (p : PlF D)

def lt (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g : Fin (D.R.rS + 1) → (VS D).V) (Tn T'n : ℕ) :
    Loc.Term (Vp D p) (Z.M p) D.R.rS where
  abelian₂ := lattice₂ D Z.M p Λ
  f a := sF Z p a • baseChange₂ D p (f a)
  f' b := sF' Z p b • baseChange₂ D p (g b)
  T := (Tn : (D.s.atP p).Fp)
  T' := (T'n : (D.s.atP p).Fp)

structure GFacts (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop where
  iso : ∀ x y, (VS D).hT (β x) (β y) = (VS D).hT x y
  lam : ∀ v ∈ Λ, β v ∈ Λ
  lam' : ∀ v ∈ Λ, β.symm v ∈ Λ
  xmap : ∀ a : Fin D.R.rS, β (g1 a.castSucc) ∈
    Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)
  xmap' : ∀ a : Fin D.R.rS, β.symm (g2 a.castSucc) ∈
    Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g1 b.castSucc)
  zmap : β (g1 (Fin.last _)) - g2 (Fin.last _) ∈
    Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)
  fiso : ∀ a b : Fin D.R.rS, (VS D).hT (f a.castSucc) (f b.castSucc) = 0
  g2iso : ∀ a b : Fin D.R.rS, (VS D).hT (g2 a.castSucc) (g2 b.castSucc) = 0
  proj : ∀ y, ∃ u ∈ Submodule.span D.host.E (Set.range (Sum.elim f g1)),
    ∀ i, (VS D).hT (Sum.elim f g1 i) (y - u) = 0
  gram : (Matrix.of fun i k => brS (VS D) (Sum.elim f g1 i) (Sum.elim f g1 k)).det ≠ 0
  theta : ∀ x1, (∀ i, (VS D).hT (Sum.elim f g1 i) x1 = 0) → ∃ x2, (∀ i, (VS D).hT (Sum.elim f g2 i) x2 = 0) ∧
    x1 - x2 ∈ Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => f a.castSucc) ∧
    β x1 - x2 ∈ Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)
  ratio : GDl f g1 D.R.rS * GDl f g2 (D.R.rS + 1) = GDl f g2 D.R.rS * GDl f g1 (D.R.rS + 1)
  omp : GDl f g2 (D.R.rS + 1) • Gom' f g1 - GDl f g1 (D.R.rS + 1) • Gom' f g2 ∈
    Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => f a.castSucc)
  om : star (GDl f g2 (D.R.rS + 1)) • β (Gom f g1) - star (GDl f g1 (D.R.rS + 1)) • Gom f g2 ∈
    Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => g2 b.castSucc)

theorem hermitian_base_change_smul (a : (D.s.atP p).Ep) (x y : (VS D).V) :
    (locH Z p).h (a • baseChange₂ D p x) (baseChange₂ D p y) = a * (D.s.atP p).ιE (brS (VS D) x y) := by
  have := h_bcP Z p a 1 x y
  rwa [one_smul, map_one, mul_one] at this

theorem h_zero_of_smul {c : (D.s.atP p).Ep} (hc : IsUnit c) {w y : Vp D p}
    (h : (locH Z p).h w (c • y) = 0) : (locH Z p).h w y = 0 := by
  rw [h_smul_right] at h
  exact (hc.map (Z.M p).L.cj).mul_right_eq_zero.1 h

theorem baseChange_mem_span {ι : Type} (v : ι → (VS D).V) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range v)) :
    baseChange₂ D p x ∈ Submodule.span (D.s.atP p).Ep (Set.range fun i => baseChange₂ D p (v i)) := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul e x _ hx => rw [baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem mem_orthogonal_frame_iff (u v : Fin (D.R.rS + 1) → Vp D p) (w : Vp D p) :
    w ∈ (locH Z p).W0 u v ↔ (∀ a, (locH Z p).h w (u a) = 0) ∧ ∀ b, (locH Z p).h w (v b) = 0 := by
  unfold Loc.HermSp.W0 Loc.HermSp.Xp
  rw [← Submodule.span_union, mem_perp_span]
  constructor
  · intro h
    exact ⟨fun a => h _ (Or.inl ⟨a, rfl⟩), fun b => h _ (Or.inr ⟨b, rfl⟩)⟩
  · rintro ⟨h1, h2⟩ x (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact h1 a
    · exact h2 b

theorem scalar_frame_w_zero_exists (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hG : GFacts Λ f g1 g2 β) {w : Vp D p}
    (hw : w ∈ (locH Z p).W0 (fun a => sF Z p a • baseChange₂ D p (f a)) (fun b => sF' Z p b • baseChange₂ D p (g1 b))) :
    ∃ w₂ ∈ (locH Z p).W0 (fun a => sF Z p a • baseChange₂ D p (f a)) (fun b => sF' Z p b • baseChange₂ D p (g2 b)),
      w - w₂ ∈ (locH Z p).X (fun a => sF Z p a • baseChange₂ D p (f a)) ∧
      betaP p β w - w₂ ∈ (locH Z p).X (fun b => sF' Z p b • baseChange₂ D p (g2 b)) := by
  rw [mem_orthogonal_frame_iff] at hw
  have hperp : ∀ i, (locH Z p).h w (baseChange₂ D p (Sum.elim f g1 i)) = 0 := by
    rintro (a | b)
    · exact h_zero_of_smul Z p (isUnit_sF Z p a) (hw.1 a)
    · exact h_zero_of_smul Z p (isUnit_sF' Z p b) (hw.2 b)
  choose u hu hpu using fun j => hG.proj ((VS D).frame j)

  set U : Vp D p := ∑ j, w j • baseChange₂ D p (u j) with hU
  set Hh : Vp D p := ∑ j, w j • baseChange₂ D p ((VS D).frame j - u j) with hHh
  have hw_eq : w = U + Hh := by
    conv_lhs => rw [vp_eq_sum p w]
    rw [hU, hHh, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_add, ← map_add (f := _), add_sub_cancel]
  have hHperp : ∀ i, (locH Z p).h Hh (baseChange₂ D p (Sum.elim f g1 i)) = 0 := by
    intro i
    rw [hHh, h_sum_left]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hermitian_base_change_smul, brS, hpu j i, map_zero, mul_zero]
  have hUperp : ∀ i, (locH Z p).h U (baseChange₂ D p (Sum.elim f g1 i)) = 0 := by
    intro i
    have e : U = w - Hh := by rw [hw_eq]; abel
    rw [e, h_sub_left, hperp i, hHperp i, sub_zero]
  have hUspan : U ∈ Submodule.span (D.s.atP p).Ep (Set.range fun i => baseChange₂ D p (Sum.elim f g1 i)) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (baseChange_mem_span p _ (hu j))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hUspan
  have hU0 : U = 0 := by
    set G0 := Matrix.of fun i k => brS (VS D) (Sum.elim f g1 i) (Sum.elim f g1 k) with hG0
    have hvm : Matrix.vecMul c ((D.s.atP p).ιE.mapMatrix G0) = 0 := by
      funext k
      have := hUperp k
      rw [← hc, h_sum_left] at this
      simp only [hermitian_base_change_smul] at this
      simpa [Matrix.vecMul, dotProduct, hG0] using this
    have hdet : IsUnit ((D.s.atP p).ιE.mapMatrix G0).det := by
      rw [← RingHom.map_det]
      exact (isUnit_iff_ne_zero.2 hG.gram).map _
    have hc0 : c = 0 := by
      have h1 := congrArg (fun v => Matrix.vecMul v ((D.s.atP p).ιE.mapMatrix G0)⁻¹) hvm
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one,
        Matrix.zero_vecMul] at h1
      exact h1
    rw [← hc, hc0]
    simp
  have hw' : w = Hh := by rw [hw_eq, hU0, zero_add]
  have hperp1 : ∀ j, ∀ i, (VS D).hT (Sum.elim f g1 i) ((VS D).frame j - u j) = 0 := fun j i => hpu j i
  choose x2 hx2 using fun j => hG.theta ((VS D).frame j - u j) (hperp1 j)
  refine ⟨∑ j, w j • baseChange₂ D p (x2 j), ?_, ?_, ?_⟩
  · rw [mem_orthogonal_frame_iff]
    constructor
    · intro a
      rw [h_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [h_bcP, brS, show (VS D).hT (f a) (x2 j) = 0 from (hx2 j).1 (Sum.inl a), map_zero, mul_zero]
    · intro b
      rw [h_sum_left]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [h_bcP, brS, show (VS D).hT (g2 b) (x2 j) = 0 from (hx2 j).1 (Sum.inr b), map_zero, mul_zero]
  · have e : w - ∑ j, w j • baseChange₂ D p (x2 j) = ∑ j, w j • baseChange₂ D p ((VS D).frame j - u j - x2 j) := by
      nth_rewrite 1 [hw']
      rw [hHh, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_sub, ← map_sub]
    rw [e]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (bcP_mem_X Z p f (sF Z p) (isUnit_sF Z p) (hx2 j).2.1)
  · have e : betaP p β w - ∑ j, w j • baseChange₂ D p (x2 j) =
        ∑ j, w j • baseChange₂ D p (β ((VS D).frame j - u j) - x2 j) := by
      nth_rewrite 1 [hw']
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hHh, map_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, betaP_bc, ← smul_sub, ← map_sub]
    rw [e]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (bcP_mem_X Z p g2 (sF' Z p) (isUnit_sF' Z p) (hx2 j).2.2)

end Assembly

end Formalism.L2.SG.Pf.ScalarFramePf
