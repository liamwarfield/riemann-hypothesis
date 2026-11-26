module

public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralHeckeForms
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DifferentCoprimeSplit

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LatticeUnimodular
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LatticeFlagExists
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RsMemPerpIff
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.PartnerVectorExists
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem hT_sub_sum_left {r : ℕ} (x w : S.V) (c : Fin r → E) (y : Fin r → S.V) :
    S.hT (x - ∑ d, c d • y d) w = S.hT x w - ∑ d, star (c d) * S.hT (y d) w := by
  first
  | simp [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  | simp [map_sub, map_sum, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem hT_sub_sum_right {r : ℕ} (x w : S.V) (c : Fin r → E) (y : Fin r → S.V) :
    S.hT w (x - ∑ d, c d • y d) = S.hT w x - ∑ d, c d * S.hT w (y d) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sub, map_sum, map_smul, smul_eq_mul]

theorem coord_surj {r : ℕ} {T : E} (F0 : FlagG S r T) :
    Function.Surjective (LinearMap.pi (fun a => S.hT (F0.e a)) : S.V →ₗ[E] (Fin r → E)) := by
  classical
  by_contra hns
  have hlt : LinearMap.range (LinearMap.pi (fun a => S.hT (F0.e a)) : S.V →ₗ[E] (Fin r → E)) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hns (LinearMap.range_eq_top.mp h)
  obtain ⟨ψ, hψne, hψ⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  have key : ∀ x : S.V, ∑ a, ψ (Pi.single a 1) * S.hT (F0.e a) x = 0 := by
    intro x
    have hx := hψ (LinearMap.mem_range_self (LinearMap.pi (fun a => S.hT (F0.e a)) : S.V →ₗ[E] (Fin r → E)) x)
    rw [LinearMap.mem_ker] at hx
    have hdec : (LinearMap.pi (fun a => S.hT (F0.e a)) : S.V →ₗ[E] (Fin r → E)) x
        = ∑ a, S.hT (F0.e a) x • (Pi.single a 1 : Fin r → E) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hdec, map_sum] at hx
    simpa [map_smul, smul_eq_mul, mul_comm] using hx
  have hv : (∑ a, star (ψ (Pi.single a 1)) • F0.e a) = 0 := by
    apply S.nondeg.1
    intro x
    first
    | simpa [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply, star_star] using key x
    | simpa [map_sum, LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply, star_star] using key x
  have hc : ∀ a, ψ (Pi.single a 1) = 0 := by
    intro a
    have h0 := (Fintype.linearIndependent_iff.mp F0.e_indep) _ hv a
    simpa using h0
  apply hψne
  apply LinearMap.pi_ext
  intro i x
  have hs : (Pi.single i x : Fin r → E) = x • (Pi.single i 1 : Fin r → E) := by
    ext j
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  rw [hs, map_smul, hc i]
  simp

private theorem star_hT_eq_hT_swap (x y : S.V) : star (S.hT x y) = S.hT y x := by
  have h : starRingEnd E (S.hT x y) = S.hT y x := by
    first
    | exact S.herm.eq x y
    | exact S.herm x y
  simpa [starRingEnd_apply] using h

theorem partner_exists {r : ℕ} {T : E} (F0 : FlagG S r T) (hT0 : T ≠ 0) :
    ∃ f : Fin r → S.V, (∀ a b, S.hT (F0.e a) (f b) = if a = b then 1 else 0) ∧
      (∀ a b, S.hT (f a) (f b) = 0) ∧ ∀ a, S.hT (f a) F0.z = 0 := by
  classical
  have hE : ∀ b, ∃ g0 : S.V, ∀ a, S.hT (F0.e a) g0 = if a = b then 1 else 0 := by
    intro b
    obtain ⟨g0, hg0⟩ := coord_surj S F0 (fun a => if a = b then (1 : E) else 0)
    refine ⟨g0, fun a => ?_⟩
    have h1 := congrFun hg0 a
    simpa using h1
  choose g0 hg0 using hE
  have hZ : S.hT F0.z F0.z ≠ 0 := by
    rw [F0.z_norm]
    exact neg_ne_zero.mpr hT0
  set g : Fin r → S.V := fun b => g0 b - (S.hT F0.z (g0 b) / S.hT F0.z F0.z) • F0.z with hgdef
  have hgE : ∀ a b, S.hT (F0.e a) (g b) = if a = b then 1 else 0 := by
    intro a b
    simp [g, map_sub, map_smul, smul_eq_mul, F0.z_orth, hg0]
  have hgZ : ∀ b, S.hT F0.z (g b) = 0 := by
    intro b
    simp only [g, map_sub, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hZ, sub_self]
  have hZg : ∀ b, S.hT (g b) F0.z = 0 := by
    intro b
    rw [← star_hT_eq_hT_swap, hgZ, star_zero]
  have hgeE : ∀ a d, S.hT (g a) (F0.e d) = if d = a then 1 else 0 := by
    intro a d
    rw [← star_hT_eq_hT_swap, hgE]
    split_ifs <;> simp
  set c : Fin r → Fin r → E := fun b d => S.hT (g d) (g b) / 2 with hcdef
  have hf1 : ∀ a b, S.hT (F0.e a) (g b - ∑ d, c b d • F0.e d) = if a = b then 1 else 0 := by
    intro a b
    rw [hT_sub_sum_right]
    simp [hgE, F0.e_iso]
  refine ⟨fun b => g b - ∑ d, c b d • F0.e d, hf1, ?_, ?_⟩
  · intro a b
    rw [hT_sub_sum_left]
    simp only [hf1]
    rw [hT_sub_sum_right]
    simp only [hgeE, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hs : star (c a b) = S.hT (g a) (g b) / 2 := by
      simp only [c]
      rw [← star_hT_eq_hT_swap (S := S) (g a) (g b)]
      first
      | simp [star_div₀]
      | simp [star_div']
      | simp
    rw [hs]
    simp only [c]
    ring
  · intro a
    rw [hT_sub_sum_left]
    simp [hZg, F0.z_orth]

end Gen

theorem partner_vector_exists : PartnerEx := by
  intro D u F0
  refine partner_exists (VS D) F0 ?_
  unfold Tn
  exact_mod_cast (D.mem u).A.T_prime.ne_zero

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coord

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem rs_e_mem_X (a : Fin D.R.rS) : F0.e a ∈ F0.X := Submodule.subset_span ⟨a, rfl⟩

theorem rs_hT_e_X (a : Fin D.R.rS) {x : (VS D).V} (hx : x ∈ F0.X) : (VS D).hT (F0.e a) x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact F0.e_iso a b
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

theorem rs_mem_perp_iff' (y : (VS D).V) : y ∈ perpS (VS D) F0.X ↔ ∀ a, (VS D).hT (F0.e a) y = 0 := by
  constructor
  · intro hy a
    exact hy _ (rs_e_mem_X D F0 a)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, rfl⟩ := hw
      exact h b
    | zero => simp
    | add w w' _ _ h1 h2 => simp [h1, h2]
    | smul c w _ h' => simp [h']

theorem rs_X_le_perp : F0.X ≤ perpS (VS D) F0.X := fun x hx =>
  (rs_mem_perp_iff' D F0 x).2 fun a => rs_hT_e_X D F0 a hx

theorem rs_mk_X_zero {x : (VS D).V} (hx : x ∈ F0.X) (hp : x ∈ perpS (VS D) F0.X) :
    (Submodule.Quotient.mk (⟨x, hp⟩ : perpS (VS D) F0.X) : WbQ D F0) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact hx

variable {D F0} {f : Fin D.R.rS → (VS D).V}

theorem rs_hT_f_e (hf : PartnerOK D F0 f) (a b : Fin D.R.rS) :
    (VS D).hT (f a) (F0.e b) = if b = a then 1 else 0 := by
  rw [← (VS D).herm.eq (F0.e b) (f a), hf.1 b a]
  split_ifs <;> simp

end Coord

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Flag

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {f : Fin D.R.rS → (VS D).V}
  {M : Submodule (𝓞 D.host.E) (WbQ D F0)}

theorem rs_mem_lamC_perp {v : (VS D).V} (hv : v ∈ perpS (VS D) F0.X) :
    v ∈ lamC D F0 f M ↔ (Submodule.Quotient.mk (⟨v, hv⟩ : perpS (VS D) F0.X) : WbQ D F0) ∈ M ∧
      ∀ a, (VS D).hT (f a) v ∈ aaI D a := by
  have h0 : ∀ a, (VS D).hT (F0.e a) v = 0 := fun a => hv _ (Submodule.subset_span ⟨a, rfl⟩)
  have hvPr : vPr D F0 f v = v := by simp [vPr, h0]
  constructor
  · rintro ⟨-, ⟨w, hw, hwM⟩, h3⟩
    have hwv : w = ⟨v, hv⟩ := Subtype.ext (hw.trans hvPr)
    subst hwv
    exact ⟨hwM, fun a => by rw [← hvPr]; exact h3 a⟩
  · rintro ⟨hM, h3⟩
    refine ⟨fun a => ?_, ⟨⟨v, hv⟩, hvPr.symm, hM⟩, fun a => ?_⟩
    · simp only [h0, star_zero]
      exact fi_zero D _
    · rw [hvPr]
      exact h3 a

theorem rs_orth_perp {y : (VS D).V} (hy : y ∈ orth (VS D) F0.X) : y ∈ perpS (VS D) F0.X := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy
  exact fun x hx => hy x hx

theorem rs_z_mem (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) :
    F0.z ∈ lamC D F0 f M := by
  rw [rs_mem_lamC_perp (z_mem_perp D F0)]
  refine ⟨hM.2.2.1, fun a => ?_⟩
  rw [hf.2.2 a]
  exact fi_zero D _

theorem rs_smul_e_mem (hf : PartnerOK D F0 f) {a : Fin D.R.rS} {x : D.host.E} (hx : x ∈ aaI D a) :
    x • F0.e a ∈ lamC D F0 f M := by
  have hXe : ∀ y ∈ F0.X, ∀ b, (VS D).hT y (F0.e b) = 0 := by
    intro y hy b
    have hy' : y ∈ Submodule.span D.host.E (Set.range F0.e) := hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, rfl⟩ := hz
      exact F0.e_iso c b
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add y z _ _ hy hz => rw [map_add (f := _), LinearMap.add_apply, hy, hz, add_zero]
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]
  have hperp : x • F0.e a ∈ perpS (VS D) F0.X := by
    intro y hy
    rw [map_smul, hXe y hy a, smul_zero]
  rw [rs_mem_lamC_perp hperp]
  refine ⟨?_, fun b => ?_⟩
  · have hmem : x • F0.e a ∈ F0.X := Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    have h0 : (Submodule.Quotient.mk (⟨x • F0.e a, hperp⟩ : perpS (VS D) F0.X) : WbQ D F0) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hmem
    rw [h0]
    exact zero_mem _
  · have hs : starRingEnd D.host.E ((VS D).hT (F0.e a) (f b)) = (VS D).hT (f b) (F0.e a) := by
      first
        | exact (VS D).herm (F0.e a) (f b)
        | exact (VS D).herm.eq (F0.e a) (f b)
    rw [map_smul, ← hs, hf.1 a b, smul_eq_mul]
    split_ifs with hab
    · subst hab
      simpa using hx
    · simp only [map_zero, mul_zero]
      exact FractionalIdeal.zero_mem _

theorem rs_xlam (hf : PartnerOK D F0 f) : XLam (lamC D F0 f M) (lf D F0) = XS D F0 := by
  apply le_antisymm
  · rintro v ⟨hvΛ, hvX⟩
    have hvX' : v ∈ F0.X := hvX
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hvX'
    have hα := ((rs_mem_lamC_perp (rs_X_le_perp D F0 hvX')).1 hvΛ).2
    have hca : ∀ a, c a ∈ aaI D a := by
      intro a
      have h := hα a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hc, map_sum] at h
      simp only [map_smul, rs_hT_f_e hf, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at h
      exact h
    rw [← hc]
    refine Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨a, c a, hca a, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, hx, rfl⟩
    exact ⟨rs_smul_e_mem hf hx, Submodule.smul_mem _ x (rs_e_mem_X D F0 a)⟩

theorem rs_prim (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) (c : D.host.E)
    (hc : c • F0.z ∈ Lsub (lamC D F0 f M) (lf D F0)) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  obtain ⟨y, hy, x, hx, hyx⟩ := Submodule.mem_sup.1 hc.1
  have hyΛ : y ∈ lamC D F0 f M := hy.1
  have hyp : y ∈ perpS (VS D) F0.X := rs_orth_perp hy.2
  have hxX : x ∈ F0.X := hx
  have hxp : x ∈ perpS (VS D) F0.X := rs_X_le_perp D F0 hxX
  have hyM := ((rs_mem_lamC_perp hyp).1 hyΛ).1
  apply hM.2.2.2 c
  have hsum : c • (⟨F0.z, z_mem_perp D F0⟩ : perpS (VS D) F0.X) = ⟨y, hyp⟩ + ⟨x, hxp⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Submodule.coe_add]
    exact hyx.symm
  rw [zbar, ← Submodule.Quotient.mk_smul, hsum, Submodule.Quotient.mk_add, rs_mk_X_zero D F0 hxX, add_zero]
  exact hyM

def rsLift (w : perpS (VS D) F0.X) : (VS D).V := (w : (VS D).V) - ∑ a, (VS D).hT (f a) w • F0.e a

theorem rs_lift_perp (w : perpS (VS D) F0.X) : rsLift (f := f) w ∈ perpS (VS D) F0.X := by
  show ∀ x ∈ F0.X, (VS D).hT x (rsLift (f := f) w) = 0
  intro x hx
  have hxe : ∀ b, (VS D).hT x (F0.e b) = 0 := by
    intro b
    have hx' : x ∈ Submodule.span D.host.E (Set.range F0.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact F0.e_iso a b
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add y z _ _ hy hz => rw [map_add (f := _), LinearMap.add_apply, hy, hz, add_zero]
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rsLift, map_sub, map_sum, map_smul, hxe, smul_zero, Finset.sum_const_zero, sub_zero]
  exact w.2 x hx

theorem rs_lift_mk (w : perpS (VS D) F0.X) :
    (Submodule.Quotient.mk (⟨rsLift (f := f) w, rs_lift_perp w⟩ : perpS (VS D) F0.X) : WbQ D F0) =
      Submodule.Quotient.mk w := by
  apply (Submodule.Quotient.eq _).mpr
  show (((⟨rsLift (f := f) w, rs_lift_perp w⟩ : perpS (VS D) F0.X) - w : perpS (VS D) F0.X) : (VS D).V) ∈ F0.X
  simp only [Submodule.coe_sub, rsLift, sub_sub_cancel_left]
  exact neg_mem (sum_mem fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

theorem rs_hT_f_lift (hf : PartnerOK D F0 f) (w : perpS (VS D) F0.X) (b : Fin D.R.rS) :
    (VS D).hT (f b) (rsLift (f := f) w) = 0 := by
  have hfe : ∀ a, (VS D).hT (f b) (F0.e a) = if a = b then 1 else 0 := by
    intro a
    have hs : starRingEnd D.host.E ((VS D).hT (F0.e a) (f b)) = (VS D).hT (f b) (F0.e a) := by
      first
        | exact (VS D).herm (F0.e a) (f b)
        | exact (VS D).herm.eq (F0.e a) (f b)
    rw [← hs, hf.1 a b]
    split_ifs <;> simp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rsLift, map_sub, map_sum, map_smul, hfe, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]

theorem rs_lift_mem (hf : PartnerOK D F0 f) (w : perpS (VS D) F0.X)
    (hw : (Submodule.Quotient.mk w : WbQ D F0) ∈ M) : rsLift (f := f) w ∈ lamC D F0 f M := by
  rw [rs_mem_lamC_perp (rs_lift_perp w)]
  refine ⟨?_, fun a => ?_⟩
  · rw [rs_lift_mk]
    exact hw
  · rw [rs_hT_f_lift hf w a]
    exact FractionalIdeal.zero_mem _

theorem rs_mof (hf : PartnerOK D F0 f) : Mof D F0 (lamC D F0 f M) = M := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : (VS D).V) ∈ lamC D F0 f M := hw
    exact ((rs_mem_lamC_perp w.2).1 hw').1
  · intro m hm
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    refine ⟨⟨rsLift (f := f) w, rs_lift_perp w⟩, rs_lift_mem hf w hm, ?_⟩
    exact rs_lift_mk w

end Flag

theorem lattice_flag_exists : LamFlag := by
  intro D u F0 f M hf hM
  exact ⟨rs_z_mem hf hM, rs_xlam hf, rs_prim hf hM, rs_mof hf⟩

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CoordLInjective
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable (D : D7)

theorem ddS_ne_zero : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

theorem aaI_ne_zero (a : Fin D.R.rS) : aaI D a ≠ 0 := by
  unfold aaI
  exact zpow_ne_zero _ (ddS_ne_zero D)

theorem int_mul_of_ne {b : 𝓞 D.host.E} (hb : b ≠ 0) : ∃ k : ℕ, k ≠ 0 ∧ ∃ c : 𝓞 D.host.E, (k : 𝓞 D.host.E) = b * c := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    exact ⟨c, by rw [← hc, mul_comm]⟩

theorem fi_nat_mul {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} (hI : I ≠ 0) (x : D.host.E) :
    ∃ k : ℕ, k ≠ 0 ∧ (k : D.host.E) * x ∈ I := by
  obtain ⟨y, hyI, hy0⟩ : ∃ y ∈ I, y ≠ 0 := by
    by_contra h
    push Not at h
    apply hI
    ext z
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨h z, fun hz => hz ▸ fi_zero D I⟩
  obtain ⟨a0, b0, hb0, rfl⟩ := IsFractionRing.div_surjective (𝓞 D.host.E) y
  have hb0' : algebraMap (𝓞 D.host.E) D.host.E b0 ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    exact nonZeroDivisors.ne_zero hb0
  have ha0I : algebraMap (𝓞 D.host.E) D.host.E a0 ∈ I := by
    have := fi_mul D b0 hyI
    have e : (b0 : D.host.E) * (algebraMap (𝓞 D.host.E) D.host.E a0 / algebraMap (𝓞 D.host.E) D.host.E b0) =
        algebraMap (𝓞 D.host.E) D.host.E a0 := by
      rw [show (b0 : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b0 from rfl, mul_div_cancel₀ _ hb0']
    rwa [e] at this
  have ha00 : a0 ≠ 0 := by
    rintro rfl
    simp at hy0
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 D.host.E) x
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap (𝓞 D.host.E) D.host.E b ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    exact hbne
  obtain ⟨k, hk, c, hc⟩ := int_mul_of_ne D hbne
  obtain ⟨k0, hk0, c0, hc0⟩ := int_mul_of_ne D ha00
  refine ⟨k0 * k, mul_ne_zero hk0 hk, ?_⟩
  have hcE : (k : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E b * algebraMap (𝓞 D.host.E) D.host.E c := by
    rw [← map_mul, ← hc]; simp
  have hc0E : (k0 : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E a0 * algebraMap (𝓞 D.host.E) D.host.E c0 := by
    rw [← map_mul, ← hc0]; simp
  have e : ((k0 * k : ℕ) : D.host.E) * (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E b) =
      ((c0 * c * a : 𝓞 D.host.E) : D.host.E) * algebraMap (𝓞 D.host.E) D.host.E a0 := by
    rw [Nat.cast_mul, hcE, hc0E]
    show _ = algebraMap (𝓞 D.host.E) D.host.E (c0 * c * a) * _
    rw [map_mul, map_mul]
    field_simp
  rw [e]
  exact fi_mul D _ ha0I

variable {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (f : Fin D.R.rS → (VS D).V)

theorem M_nat_smul (M : Submodule (𝓞 D.host.E) (WbQ D F0)) (hsp : Submodule.span D.host.E (M : Set (WbQ D F0)) = ⊤)
    (m : WbQ D F0) : ∃ k : ℕ, k ≠ 0 ∧ (k : 𝓞 D.host.E) • m ∈ M := by
  first | exact UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul .. | (apply UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (intros; apply UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (apply @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> assumption) | (apply @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 M hsp m | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 M hsp | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 M | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T F0 | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D T | exact @UpperTheory.Reformulated.B.IntegralHeckeForms.M_nat_smul D

theorem vPr_perp (hf : PartnerOK D F0 f) (v : (VS D).V) : vPr D F0 f v ∈ perpS (VS D) F0.X := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    simp [vPr, hf.1]
  | zero => simp
  | add y w _ _ h1 h2 => simp [h1, h2]
  | smul c y _ h => simp [h]

def vPrLin : (VS D).V →ₗ[D.host.E] (VS D).V where
  toFun := vPr D F0 f
  map_add' := vPr_add D F0 f
  map_smul' := vPr_smul D F0 f

def coordL (hf : PartnerOK D F0 f) :
    (VS D).V →ₗ[D.host.E] (Fin D.R.rS → D.host.E) × (WbQ D F0) × (Fin D.R.rS → D.host.E) :=
  LinearMap.prod (LinearMap.pi fun a => ((VS D).hT (f a)).comp (vPrLin D F0 f))
    (LinearMap.prod ((nX D F0).mkQ.comp (LinearMap.codRestrict _ (vPrLin D F0 f) (vPr_perp D F0 f hf)))
      (LinearMap.pi fun a => (VS D).hT (F0.e a)))

theorem coordL_apply (hf : PartnerOK D F0 f) (v : (VS D).V) :
    coordL D F0 f hf v = ((fun a => (VS D).hT (f a) (vPr D F0 f v)),
      (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) : WbQ D F0),
      (fun a => (VS D).hT (F0.e a) v)) := rfl

theorem coordL_injective (hf : PartnerOK D F0 f) : Function.Injective (coordL D F0 f hf) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rw [coordL_apply] at hv
  simp only [Prod.mk_eq_zero] at hv
  obtain ⟨h1, h2, h3⟩ := hv
  have hb : ∀ a, (VS D).hT (F0.e a) v = 0 := fun a => congrFun h3 a
  have hvv : vPr D F0 f v = v := by simp [vPr, hb]
  have hX : v ∈ F0.X := by
    rw [Submodule.Quotient.mk_eq_zero] at h2
    have : vPr D F0 f v ∈ F0.X := h2
    rwa [hvv] at this
  obtain ⟨c, hc⟩ := Submodule.mem_span_range_iff_exists_fun D.host.E |>.1 hX
  have ha : ∀ a, (VS D).hT (f a) v = 0 := fun a => by
    have := congrFun h1 a
    rwa [hvv] at this
  have hc0 : ∀ a, c a = 0 := by
    intro a
    have h := ha a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum] at h
    have e : ∀ b, (VS D).hT (f a) (c b • F0.e b) = c b * (if b = a then 1 else 0) := by
      intro b
      rw [map_smul, smul_eq_mul, ← (VS D).herm.eq (F0.e b) (f a), hf.1 b a]
      split_ifs <;> simp
    simp only [e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  rw [← hc]
  simp [hc0]

theorem fi_bound (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    ∃ d : D.host.E, ∀ x ∈ I, ∃ o : 𝓞 D.host.E, x = (o : D.host.E) * d := by
  obtain ⟨d, hdS, hd⟩ := I.isFractional
  refine ⟨(algebraMap (𝓞 D.host.E) D.host.E d)⁻¹, fun x hx => ?_⟩
  obtain ⟨o, ho⟩ := hd x hx
  have hd0 : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)]
    exact nonZeroDivisors.ne_zero hdS
  refine ⟨o, ?_⟩
  rw [Algebra.smul_def] at ho
  show x = algebraMap (𝓞 D.host.E) D.host.E o * _
  rw [ho]
  field_simp

theorem pi_mem_span {x : Fin D.R.rS → D.host.E} {d : Fin D.R.rS → D.host.E}
    (h : ∀ a, ∃ o : 𝓞 D.host.E, x a = (o : D.host.E) * d a) :
    x ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => (Pi.single a (d a) : Fin D.R.rS → D.host.E)) := by
  choose o ho using h
  have e : x = ∑ a, o a • (Pi.single a (d a) : Fin D.R.rS → D.host.E) := by
    ext b
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    simp [ho b]
    rfl
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem lamC_fg (hf : PartnerOK D F0 f) (M : Submodule (𝓞 D.host.E) (WbQ D F0)) (hM : M.FG) :
    (lamC D F0 f M).FG := by
  choose dα hdα using fun a => fi_bound D (aaI D a)
  choose dβ hdβ using fun a => fi_bound D (aaI D a)⁻¹
  let P : Submodule (𝓞 D.host.E) ((Fin D.R.rS → D.host.E) × (WbQ D F0) × (Fin D.R.rS → D.host.E)) :=
    (Submodule.span (𝓞 D.host.E) (Set.range fun a => (Pi.single a (dα a) : Fin D.R.rS → D.host.E))).prod
      (M.prod (Submodule.span (𝓞 D.host.E) (Set.range fun a =>
        (Pi.single a (star (dβ a)) : Fin D.R.rS → D.host.E))))
  have hPfg : P.FG := Submodule.FG.prod (Submodule.fg_span (Set.finite_range _))
    (Submodule.FG.prod hM (Submodule.fg_span (Set.finite_range _)))
  have hle : (lamC D F0 f M).map ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E)) ≤ P := by
    rintro _ ⟨v, ⟨h1, ⟨w, hw, hwM⟩, h3⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · exact pi_mem_span D (fun a => hdα a _ (h3 a))
    · have e : (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) = w := Subtype.ext hw.symm
      show (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X) : WbQ D F0) ∈ M
      rw [e]; exact hwM
    · refine pi_mem_span D (fun a => ?_)
      obtain ⟨o, ho⟩ := hdβ a _ (h1 a)
      obtain ⟨o', ho'⟩ := star_int D o
      refine ⟨o', ?_⟩
      show (VS D).hT (F0.e a) v = _
      rw [ho', ← star_mul, mul_comm, ← ho, star_star]
  exact Submodule.fg_of_fg_map_injective ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E)) (coordL_injective D F0 f hf)
    (Submodule.FG.of_le (S := (lamC D F0 f M).map ((coordL D F0 f hf).restrictScalars (𝓞 D.host.E))) hPfg hle)

theorem lamC_span (hf : PartnerOK D F0 f) (M : Submodule (𝓞 D.host.E) (WbQ D F0))
    (hsp : Submodule.span D.host.E (M : Set (WbQ D F0)) = ⊤) :
    Submodule.span D.host.E (lamC D F0 f M : Set (VS D).V) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  choose kα hkα hα using fun a => fi_nat_mul D (aaI_ne_zero D a) ((VS D).hT (f a) (vPr D F0 f v))
  choose kβ hkβ hβ using fun a => fi_nat_mul D (inv_ne_zero (aaI_ne_zero D a)) (star ((VS D).hT (F0.e a) v))
  obtain ⟨kM, hkM, hM⟩ := M_nat_smul D F0 M hsp
    (Submodule.Quotient.mk (⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩ : perpS (VS D) F0.X))
  set K : ℕ := (∏ a, kα a) * kM * ∏ a, kβ a with hK
  have hK0 : K ≠ 0 := by
    rw [hK]
    refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun a _ => hkα a) hkM)
      (Finset.prod_ne_zero_iff.2 fun a _ => hkβ a)
  have hdvd : ∀ {k : ℕ} {I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E} {x : D.host.E},
      k ∣ K → (k : D.host.E) * x ∈ I → (K : D.host.E) * x ∈ I := by
    rintro k I x ⟨m, hm⟩ hx
    rw [hm, Nat.cast_mul, mul_comm (k : D.host.E) (m : D.host.E), mul_assoc]
    have := fi_mul D (m : 𝓞 D.host.E) hx
    simpa using this
  have hmem : (K : 𝓞 D.host.E) • v ∈ lamC D F0 f M := by
    have hs : (K : 𝓞 D.host.E) • v = (K : D.host.E) • v := by
      rw [← algebraMap_smul D.host.E (K : 𝓞 D.host.E) v, map_natCast]
    rw [hs]
    refine ⟨fun a => ?_, ⟨(K : 𝓞 D.host.E) • ⟨vPr D F0 f v, vPr_perp D F0 f hf v⟩, ?_, ?_⟩, fun a => ?_⟩
    · rw [map_smul, smul_eq_mul, star_mul, star_natCast, mul_comm]
      exact hdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ a) |>.trans (dvd_mul_left _ _)) (hβ a)
    · rw [vPr_smul]
      show (K : 𝓞 D.host.E) • vPr D F0 f v = _
      rw [← algebraMap_smul D.host.E (K : 𝓞 D.host.E), map_natCast]
    · rw [Submodule.Quotient.mk_smul]
      obtain ⟨m, hm⟩ : kM ∣ K := by
        rw [hK]; exact (dvd_mul_left _ _).mul_right _
      rw [hm, Nat.cast_mul, mul_comm, mul_smul]
      exact M.smul_mem _ hM
    · rw [vPr_smul, map_smul, smul_eq_mul]
      exact hdvd ((Finset.dvd_prod_of_mem _ (Finset.mem_univ a)).mul_right _ |>.mul_right _) (hα a)
  have hK' : (K : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hK0
  have e : v = (K : D.host.E)⁻¹ • ((K : 𝓞 D.host.E) • v) := by
    rw [← algebraMap_smul D.host.E (K : 𝓞 D.host.E) v, map_natCast, smul_smul, inv_mul_cancel₀ hK', one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem lattice_integral : LamLattice := by
  intro D u F0 f M hf hM
  exact Submodule.IsLattice.of_fg D.host.E (lamC_fg D F0 f hf M hM.1.fg)

end Lat

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Unimod

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {f : Fin D.R.rS → (VS D).V}
  {M : Submodule (𝓞 D.host.E) (WbQ D F0)}

theorem rs_mem_one_iff (x : D.host.E) :
    x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = x := by
  rw [Submodule.mem_one]
  all_goals first
    | rfl
    | exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩

theorem rs_fone_iff (x : D.host.E) :
    x ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = x := by
  rw [FractionalIdeal.mem_one_iff]
  all_goals first
    | rfl
    | exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩

theorem rs_mem_dual {h : (VS D).V →ₗ⋆[D.host.E] (VS D).V →ₗ[D.host.E] D.host.E}
    {L : Submodule (𝓞 D.host.E) (VS D).V} {v : (VS D).V} :
    v ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y v ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, LinearMap.coe_restrictScalars]

theorem rs_mem_dualW {h : WbQ D F0 →ₗ⋆[D.host.E] WbQ D F0 →ₗ[D.host.E] D.host.E}
    {L : Submodule (𝓞 D.host.E) (WbQ D F0)} {v : WbQ D F0} :
    v ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y v ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, LinearMap.coe_restrictScalars]

theorem rs_inv_mul {a : Fin D.R.rS} {s x : D.host.E} (hs : s ∈ (aaI D a)⁻¹) (hx : x ∈ aaI D a) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = s * x := by
  by_cases hI : aaI D a = 0
  · rw [hI, inv_zero] at hs
    simp only [FractionalIdeal.mem_zero_iff] at hs
    exact ⟨0, by simp [hs]⟩
  · exact (rs_fone_iff _).1 ((FractionalIdeal.mem_inv_iff hI).1 hs x hx)

theorem rs_int_star {x : D.host.E} (hx : ∃ o : 𝓞 D.host.E, (o : D.host.E) = x) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = star x := by
  obtain ⟨o, rfl⟩ := hx
  exact star_int D o

private theorem mem_lamC_iff {v : (VS D).V} : v ∈ lamC D F0 f M ↔
    ((∀ a, star ((VS D).hT (F0.e a) v) ∈ (aaI D a)⁻¹) ∧
      (∃ w : perpS (VS D) F0.X, (w : (VS D).V) = vPr D F0 f v ∧
        (Submodule.Quotient.mk w : WbQ D F0) ∈ M) ∧
      ∀ a, (VS D).hT (f a) (vPr D F0 f v) ∈ aaI D a) := Iff.rfl

private theorem hs_lemma_2 (x z : (VS D).V) : star ((VS D).hT x z) = (VS D).hT z x := by
  have h := (VS D).herm.eq x z
  first
    | exact h
    | rwa [starRingEnd_apply] at h

private theorem hT_eq_hT_vPr_right_add_sum (x z : (VS D).V) : (VS D).hT x z =
    (VS D).hT x (vPr D F0 f z) + ∑ b, (VS D).hT (F0.e b) z * (VS D).hT x (f b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [vPr, map_sub, map_sum, map_smul]

private theorem hT_eq_hT_vPr_left_add_sum (x z : (VS D).V) : (VS D).hT x z =
    (VS D).hT (vPr D F0 f x) z + ∑ a, star ((VS D).hT (F0.e a) x) * (VS D).hT (f a) z := by
  simp [vPr, LinearMap.map_sub₂, LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂, starRingEnd_apply]

private theorem mem_perpS_X_of_hT_e_eq_zero (z : (VS D).V) (hz : ∀ b, (VS D).hT (F0.e b) z = 0) :
    z ∈ perpS (VS D) F0.X := by
  have hK : F0.X ≤ LinearMap.ker ((VS D).hT z) := by
    rw [FlagG.X, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← hs_lemma_2, hz b, star_zero]
  intro x hx
  rw [← hs_lemma_2, LinearMap.mem_ker.1 (hK hx), star_zero]

private theorem hT_e_vPr_eq_zero_of_partnerOK (hf : PartnerOK D F0 f) (z : (VS D).V) (b : Fin D.R.rS) :
    (VS D).hT (F0.e b) (vPr D F0 f z) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [vPr, map_sub, map_sum, map_smul, hf.1]

theorem rs_lam_le_dual (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) :
    lamC D F0 f M ≤ Formalism.HermitianLatticesTheory.dual (VS D).hT (lamC D F0 f M) := by
  intro v hv
  rw [rs_mem_dual]
  intro y hy
  obtain ⟨hv1, ⟨w, hw, hwM⟩, hv3⟩ := mem_lamC_iff.1 hv
  obtain ⟨hy1, ⟨u, hu, huM⟩, hy3⟩ := mem_lamC_iff.1 hy
  have hU : Formalism.HermitianLatticesTheory.dual (hWb D F0) M = M := hM.2.1
  have hwD : (Submodule.Quotient.mk w : WbQ D F0) ∈ Formalism.HermitianLatticesTheory.dual (hWb D F0) M := by
    rw [hU]; exact hwM
  have hqp : (VS D).hT (vPr D F0 f y) (vPr D F0 f v) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    have h1 := rs_mem_dualW.1 hwD _ huM
    rw [← hu, ← hw, ← hWbFun_mk]
    exact h1
  rw [hT_eq_hT_vPr_right_add_sum (F0 := F0) (f := f) y v]
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun b _ => ?_)
  · rw [hT_eq_hT_vPr_left_add_sum (F0 := F0) (f := f) y (vPr D F0 f v)]
    refine Submodule.add_mem _ hqp (Submodule.sum_mem _ fun a _ => ?_)
    exact (rs_mem_one_iff _).2 (rs_inv_mul (hy1 a) (hv3 a))
  · have e0 : (VS D).hT y (f b) = (VS D).hT (vPr D F0 f y) (f b) := by
      rw [hT_eq_hT_vPr_left_add_sum (F0 := F0) (f := f) y (f b)]
      simp [hf.2.1]
    rw [e0, ← hs_lemma_2 (f b) (vPr D F0 f y)]
    obtain ⟨o, ho⟩ := rs_int_star (rs_inv_mul (hv1 b) (hy3 b))
    refine (rs_mem_one_iff _).2 ⟨o, ?_⟩
    rw [ho, star_mul', star_star]

theorem rs_vPr_smul_f (hf : PartnerOK D F0 f) (a : Fin D.R.rS) (c : D.host.E) : vPr D F0 f (c • f a) = 0 := by
  rw [vPr_smul]
  have h0 : vPr D F0 f (f a) = 0 := by simp [vPr, hf.1]
  rw [h0, smul_zero]

theorem rs_smul_f_mem (hf : PartnerOK D F0 f) {a : Fin D.R.rS} {s : D.host.E} (hs : s ∈ (aaI D a)⁻¹) :
    star s • f a ∈ lamC D F0 f M := by
  refine mem_lamC_iff.2 ⟨fun b => ?_, ⟨0, ?_, ?_⟩, fun b => ?_⟩
  · rw [map_smul, hf.1, smul_eq_mul]
    by_cases hab : b = a
    · subst hab; rw [if_pos rfl, mul_one, star_star]; exact hs
    · rw [if_neg hab, mul_zero, star_zero]; exact fi_zero D _
  · simp [rs_vPr_smul_f hf]
  · rw [Submodule.Quotient.mk_zero]; exact M.zero_mem
  · rw [rs_vPr_smul_f hf, map_zero]; exact fi_zero D _

theorem rs_dual_le_lam (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) :
    Formalism.HermitianLatticesTheory.dual (VS D).hT (lamC D F0 f M) ≤ lamC D F0 f M := by
  intro v hv
  have hv' := rs_mem_dual.1 hv
  have hI0 : ∀ a, aaI D a ≠ 0 := by
    intro a
    have hd : ddS D ≠ 0 := by
      rw [ddS, Ne, FractionalIdeal.coeIdeal_eq_zero]
      first
        | exact Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot
        | exact Ideal.map_ne_bot_of_ne_bot (differentIdeal_ne_bot (A := ℤ))
        | (intro h
           rw [Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h
           exact differentIdeal_ne_bot h)
    rw [aaI]
    exact zpow_ne_zero _ hd
  have heX : ∀ a, F0.e a ∈ F0.X := by
    intro a
    rw [FlagG.X]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hfe : ∀ a b, (VS D).hT (f b) (F0.e a) = if a = b then 1 else 0 := by
    intro a b
    rw [← hs_lemma_2 (F0.e a) (f b), hf.1 a b]
    split_ifs <;> simp
  have hxe : ∀ a, ∀ x ∈ aaI D a, x • F0.e a ∈ lamC D F0 f M := by
    intro a x hx
    have hv0 : vPr D F0 f (x • F0.e a) = x • F0.e a := by
      simp [vPr, map_smul, F0.e_iso]
    have hxP : x • F0.e a ∈ perpS (VS D) F0.X :=
      Submodule.smul_mem _ x (mem_perpS_X_of_hT_e_eq_zero _ fun b => F0.e_iso b a)
    refine mem_lamC_iff.2 ⟨fun b => ?_, ⟨⟨x • F0.e a, hxP⟩, hv0.symm, ?_⟩, fun b => ?_⟩
    · rw [map_smul, F0.e_iso, smul_zero, star_zero]; exact fi_zero D _
    · rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_comap.2 (Submodule.smul_mem _ x (heX a)))]
      exact M.zero_mem
    · rw [hv0, map_smul, hfe a b, smul_eq_mul]
      split_ifs with hab
      · subst hab; simpa using hx
      · rw [mul_zero]; exact fi_zero D _
  have hPerp : vPr D F0 f v ∈ perpS (VS D) F0.X := mem_perpS_X_of_hT_e_eq_zero _ (hT_e_vPr_eq_zero_of_partnerOK hf v)
  have key : ∀ u' : perpS (VS D) F0.X, (Submodule.Quotient.mk u' : WbQ D F0) ∈ M →
      (VS D).hT (u' : (VS D).V) (vPr D F0 f v) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro u' hy
    obtain ⟨t, ht⟩ : ∃ t : (VS D).V, t = (u' : (VS D).V) - ∑ a, (VS D).hT (f a) u' • F0.e a :=
      ⟨_, rfl⟩
    have ht1 : ∀ b, (VS D).hT (F0.e b) t = 0 := by
      intro b
      rw [ht]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sub, map_sum, map_smul, F0.e_iso, hT_X_perp D F0 (heX b) u'.2]
    have ht3 : ∀ b, (VS D).hT (f b) t = 0 := by
      intro b
      rw [ht]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sub, map_sum, map_smul, hfe]
    have htP : t ∈ perpS (VS D) F0.X := mem_perpS_X_of_hT_e_eq_zero t ht1
    have hvt : vPr D F0 f t = t := by simp [vPr, ht1]
    have hq : (Submodule.Quotient.mk ⟨t, htP⟩ : WbQ D F0) = Submodule.Quotient.mk u' := by
      rw [Submodule.Quotient.eq]
      show t - (u' : (VS D).V) ∈ F0.X
      rw [ht, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (heX a))
    have htL : t ∈ lamC D F0 f M := by
      refine mem_lamC_iff.2 ⟨fun b => ?_, ⟨⟨t, htP⟩, hvt.symm, ?_⟩, fun b => ?_⟩
      · rw [ht1 b, star_zero]; exact fi_zero D _
      · rw [hq]; exact hy
      · rw [hvt, ht3 b]; exact fi_zero D _
    have htf : ∀ b, (VS D).hT t (f b) = 0 := fun b => by
      rw [← hs_lemma_2 (f b) t, ht3 b, star_zero]
    have e1 : (VS D).hT t v = (VS D).hT (u' : (VS D).V) (vPr D F0 f v) := by
      rw [hT_eq_hT_vPr_right_add_sum (F0 := F0) (f := f) t v]
      simp only [htf, mul_zero, Finset.sum_const_zero, add_zero]
      rw [ht]
      simp [LinearMap.map_sub₂, LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂, hT_e_vPr_eq_zero_of_partnerOK hf]
    rw [← e1]
    exact hv' t htL
  have hWM : (Submodule.Quotient.mk ⟨vPr D F0 f v, hPerp⟩ : WbQ D F0) ∈
      Formalism.HermitianLatticesTheory.dual (hWb D F0) M := by
    rw [rs_mem_dualW]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H u' =>
      have e2 : hWb D F0 (Submodule.Quotient.mk u') (Submodule.Quotient.mk ⟨vPr D F0 f v, hPerp⟩) =
          (VS D).hT (u' : (VS D).V) (vPr D F0 f v) := hWbFun_mk D F0 u' ⟨vPr D F0 f v, hPerp⟩
      rw [e2]
      exact key u' hy
  have hU : Formalism.HermitianLatticesTheory.dual (hWb D F0) M = M := hM.2.1
  rw [hU] at hWM
  refine mem_lamC_iff.2 ⟨fun a => ?_, ⟨⟨_, hPerp⟩, rfl, hWM⟩, fun a => ?_⟩
  · rw [FractionalIdeal.mem_inv_iff (hI0 a)]
    intro x hx
    obtain ⟨o, ho⟩ := rs_int_star ((rs_mem_one_iff _).1 (hv' _ (hxe a x hx)))
    rw [rs_fone_iff]
    refine ⟨o, ?_⟩
    rw [ho, LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul, star_mul', star_star, mul_comm]
  · have e3 : (VS D).hT (f a) (vPr D F0 f v) = (VS D).hT (f a) v := by
      rw [hT_eq_hT_vPr_right_add_sum (F0 := F0) (f := f) (f a) v]
      simp [hf.2.1]
    rw [e3, ← inv_inv (aaI D a), FractionalIdeal.mem_inv_iff (inv_ne_zero (hI0 a))]
    intro s hs
    obtain ⟨o, ho⟩ := (rs_mem_one_iff _).1 (hv' _ (rs_smul_f_mem hf hs))
    rw [rs_fone_iff]
    refine ⟨o, ?_⟩
    rw [ho, LinearMap.map_smulₛₗ₂, starRingEnd_apply, star_star, smul_eq_mul, mul_comm]

end Unimod

theorem lamUnimod : LamUnimod := by
  intro D u F0 f M hf hM
  exact le_antisymm (rs_dual_le_lam hf hM) (rs_lam_le_dual hf hM)

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem rowSurj_of_genus (hJ : UnimodOneGenus) : RowSurj :=
  rowSurj_of hJ partner_vector_exists lattice_integral lamUnimod lattice_flag_exists local_genus_exists

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
