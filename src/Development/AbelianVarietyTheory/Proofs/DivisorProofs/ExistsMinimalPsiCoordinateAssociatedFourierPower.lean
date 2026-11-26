module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantFourierPartsBoundedClassMinima
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAtFirstOrderOfTangents

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormLeOfMemMapPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.CplDiv

theorem dvd_of_forall_mem_sup_pow : ∀ (O R : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] (j : O →+* R), IsCpl j → ∀ (c s : R), (∀ e : ℕ, s ∈ Ideal.span {c} ⊔ (maximalIdeal O ^ e).map j) → c ∣ s := by
  intro O R _ _ _ _ j hj c s hs
  obtain ⟨e, he⟩ := hj
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal O) O) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion O (maximalIdeal O)
  haveI : IsNoetherianRing R := isNoetherianRing_of_ringEquiv _ e
  haveI : IsLocalRing R := e.isLocalRing
  have hjl : (maximalIdeal O).map j ≤ maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha hu
    have h1 : IsUnit (algebraMap O (AdicCompletion (maximalIdeal O) O) a) := by
      have := hu.map e.symm.toRingHom
      rw [← he a] at this
      simpa using this
    exact ha (isUnit_of_map_unit _ _ h1)
  have hJ : (maximalIdeal O).map j ≠ ⊤ := fun h => by
    have := hjl
    rw [h, top_le_iff] at this
    exact (maximalIdeal.isMaximal R).ne_top this
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ Ideal.span {c}) ((maximalIdeal O).map j) hJ
  have hmem : (Ideal.Quotient.mk (Ideal.span {c}) s : R ⧸ Ideal.span {c}) ∈ (⨅ i : ℕ, ((maximalIdeal O).map j) ^ i • ⊤ : Submodule R (R ⧸ Ideal.span {c})) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hs i)
    rw [Ideal.map_pow] at hv
    have : (Ideal.Quotient.mk (Ideal.span {c}) s : R ⧸ Ideal.span {c}) = v • (Ideal.Quotient.mk (Ideal.span {c}) 1) := by
      rw [← huv, Algebra.smul_def, map_one, _root_.mul_one, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hu, _root_.zero_add]
      rfl
    rw [this]
    exact Submodule.smul_mem_smul hv trivial
  rw [hK, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmem
  exact hmem

theorem exists_sub_mem_map_pow : ∀ (O R : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] (j : O →+* R), IsCpl j → ∀ (s : R) (n : ℕ), ∃ t : O, s - j t ∈ (maximalIdeal O ^ n).map j := by
  intro O R _ _ _ _ j hj s n
  obtain ⟨e, he⟩ := hj
  have fg : (maximalIdeal O).FG := (maximalIdeal O).fg_of_isNoetherianRing
  obtain ⟨t, ht⟩ := Submodule.Quotient.mk_surjective _ ((e.symm s).val n)
  refine ⟨t, ?_⟩
  have hker : e.symm s - algebraMap O _ t ∈ (AdicCompletion.eval (maximalIdeal O) O n).ker := by
    rw [LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of]
    rw [Algebra.algebraMap_self, RingHom.id_apply, Submodule.mkQ_apply, ht, AdicCompletion.eval_apply, sub_self]
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval fg, Ideal.smul_top_eq_map] at hker
  have h2 := Ideal.mem_map_of_mem e.toRingHom hker
  rw [Ideal.map_map] at h2
  have hc : e.toRingHom.comp (algebraMap O _) = j := RingHom.ext fun a => he a
  rw [hc] at h2
  simpa [he] using h2

theorem exists_norm_le_of_mem_map_pow : ∀ (O R : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] (j : O →+* R) (p : ℕ) [Fact p.Prime] (ev : R →+* OO p) (n : ℕ) (t : R), t ∈ (maximalIdeal O ^ n).map j → ∃ g ∈ maximalIdeal O, ‖(ev t : PadicAlgCl p)‖ ≤ ‖(ev (j g) : PadicAlgCl p)‖ ^ n := by
  intro O R _ _ _ _ j p _ ev n t ht
  have hle1 : ∀ r : R, ‖(ev r : PadicAlgCl p)‖ ≤ 1 := fun r => (mem_OO_iff _).1 (ev r).2
  have hadd : ∀ (x y : R) (B : ℝ), ‖(ev x : PadicAlgCl p)‖ ≤ B → ‖(ev y : PadicAlgCl p)‖ ≤ B →
      ‖(ev (x + y) : PadicAlgCl p)‖ ≤ B := by
    intro x y B hx hy
    rw [map_add (f := _), AddMemClass.coe_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  have hmul : ∀ (x y : R) (B : ℝ), ‖(ev y : PadicAlgCl p)‖ ≤ B → ‖(ev (x * y) : PadicAlgCl p)‖ ≤ B := by
    intro x y B hy
    rw [map_mul, MulMemClass.coe_mul, norm_mul]
    calc ‖(ev x : PadicAlgCl p)‖ * ‖(ev y : PadicAlgCl p)‖ ≤ 1 * ‖(ev y : PadicAlgCl p)‖ :=
          mul_le_mul_of_nonneg_right (hle1 x) (norm_nonneg _)
      _ ≤ B := by rw [_root_.one_mul]; exact hy
  obtain ⟨S, hS⟩ := (maximalIdeal O).fg_of_isNoetherianRing
  let N : O → ℝ := fun g => ‖(ev (j g) : PadicAlgCl p)‖
  obtain ⟨g, hgS, hgmax⟩ := (insert 0 S).exists_max_image N ⟨0, Finset.mem_insert_self _ _⟩
  have hgm : g ∈ maximalIdeal O := by
    rcases Finset.mem_insert.1 hgS with h | h
    · rw [h]; exact Ideal.zero_mem _
    · rw [← hS]; exact Ideal.subset_span h
  refine ⟨g, hgm, ?_⟩
  have c1 : ∀ a ∈ maximalIdeal O, N a ≤ N g := by
    intro a ha
    rw [← hS] at ha
    induction ha using Submodule.span_induction with
    | mem x hx => exact hgmax x (Finset.mem_insert_of_mem hx)
    | zero => exact hgmax 0 (Finset.mem_insert_self _ _)
    | add x y _ _ hx hy =>
      show ‖(ev (j (x + y)) : PadicAlgCl p)‖ ≤ N g
      rw [map_add (f := _)]; exact hadd _ _ _ hx hy
    | smul r x _ hx =>
      show ‖(ev (j (r • x)) : PadicAlgCl p)‖ ≤ N g
      rw [smul_eq_mul, map_mul]; exact hmul _ _ _ hx
  have c2 : ∀ k : ℕ, ∀ a ∈ maximalIdeal O ^ k, N a ≤ N g ^ k := by
    intro k
    induction k with
    | zero => intro a _; rw [pow_zero]; exact hle1 _
    | succ k ih =>
      intro a ha
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on ha ?_ ?_
      · intro x hx y hy
        show ‖(ev (j (x * y)) : PadicAlgCl p)‖ ≤ N g ^ (k + 1)
        rw [map_mul, map_mul, MulMemClass.coe_mul, norm_mul, pow_succ]
        exact mul_le_mul (ih x hx) (c1 y hy) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
      · intro x y hx hy
        show ‖(ev (j (x + y)) : PadicAlgCl p)‖ ≤ N g ^ (k + 1)
        rw [map_add (f := _)]; exact hadd _ _ _ hx hy
  unfold Ideal.map at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact c2 n a ha
  | zero => rw [map_zero, ZeroMemClass.coe_zero, norm_zero]; exact pow_nonneg (norm_nonneg _) _
  | add x y _ _ hx hy => exact hadd _ _ _ hx hy
  | smul r x _ hx => rw [smul_eq_mul]; exact hmul _ _ _ hx

theorem val_stalkHom_eq : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) (x : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (φ : M.Z.presheaf.stalk x →+* OO p), y (cPt p) = x → spMap φ ≫ M.Z.fromSpecStalk x = y → ∀ a : M.Z.presheaf.stalk x, M.val (gPt p ≫ y) (M.stalkHom x a) = ((φ a : OO p) : PadicAlgCl p) := by
  intro o' Ω _ _ _ M x p _ y φ hy hφ a
  have h : y (cPt p) ⤳ x := hy ▸ specializes_rfl
  have hψ : Spec.map (M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo y) ≫ M.Z.fromSpecStalk x = y := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  haveI : Mono (M.Z.fromSpecStalk x) := inferInstance
  have heq : spMap φ = Spec.map (M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo y) := by
    rw [← cancel_mono (M.Z.fromSpecStalk x), hφ, hψ]
  have hφψ := Spec.map_injective heq
  have e1 : M.stalkHom x a = (M.stalkEquiv x a : Ω) := rfl
  rw [e1, RatModel.val_gPt hy (M.stalkEquiv x a)]
  simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  have := congrArg (fun g => ((g.hom a : OO p) : PadicAlgCl p)) hφψ
  exact this.symm

theorem dvd_of_norm_le_at_classical : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U₀ : M.Z.Opens), (U₀ : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → ∀ (b : M.Z.presheaf.stalk x) (s : R), b ≠ 0 → (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ‖(ev s : PadicAlgCl p)‖ ≤ ‖(ev (j b) : PadicAlgCl p)‖) → j b ∣ s := by
  intro o' Ω _ _ _ _ M hN U₀ hU₀ x hx R _ j hj b s hb hs
  haveI : IsNoetherianRing (M.O x) := GlobalTheory.FibreCorr.isNoetherianRing_O M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := isNoetherianRing_of_ringEquiv _ (M.stalkEquiv x).symm
  have hfO : M.stalkHom x b ∈ M.O x := (M.stalkEquiv x b).2
  have hf0 : M.stalkHom x b ≠ 0 := fun h => hb ((map_eq_zero_iff _ (M.stalkHom_injective x)).1 h)
  obtain ⟨C, hC⟩ := GlobalTheory.T.izumi_bound_mod_principal_ideal o' Ω M hN U₀ hU₀ x hx _ hfO hf0
  refine dvd_of_forall_mem_sup_pow _ _ j hj (j b) s fun e => ?_
  obtain ⟨t, ht⟩ := exists_sub_mem_map_pow _ _ j hj s (max e (C e))
  obtain ⟨a, c, hac, hc⟩ := hC e (M.stalkEquiv x t) (by
    intro p _ y hy
    obtain ⟨V, _, _, _, ev₀, i, -, -, -, -, hev, -⟩ := GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hj p y hy.1
    have hsb := hs p y (i.comp ev₀) hy hev
    have hφ : spMap ((i.comp ev₀).comp j) ≫ M.Z.fromSpecStalk x = y := by
      rw [← hev, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hval := val_stalkHom_eq o' Ω M x p y _ hy.1 hφ
    have e1 : M.val (gPt p ≫ y) (M.stalkEquiv x t : Ω) = ((i.comp ev₀) (j t) : PadicAlgCl p) := hval t
    have e2 : M.val (gPt p ≫ y) (M.stalkHom x b) = ((i.comp ev₀) (j b) : PadicAlgCl p) := hval b
    obtain ⟨g, hg, hgn⟩ := exists_norm_le_of_mem_map_pow _ _ j p (i.comp ev₀) _ _ ht
    rw [e1, e2]
    have key : ((i.comp ev₀) (j t) : PadicAlgCl p) = ((i.comp ev₀) s : PadicAlgCl p) - ((i.comp ev₀) (s - j t) : PadicAlgCl p) := by
      simp
    have hmax : ‖((i.comp ev₀) s : PadicAlgCl p) - ((i.comp ev₀) (s - j t) : PadicAlgCl p)‖ ≤ max ‖((i.comp ev₀) s : PadicAlgCl p)‖ ‖((i.comp ev₀) (s - j t) : PadicAlgCl p)‖ := by
      rw [sub_eq_add_neg, ← norm_neg ((i.comp ev₀) (s - j t) : PadicAlgCl p)]
      exact IsUltrametricDist.norm_add_le_max _ _
    by_cases hle : ‖((i.comp ev₀) (s - j t) : PadicAlgCl p)‖ ≤ ‖((i.comp ev₀) s : PadicAlgCl p)‖
    · left
      rw [key]
      exact hmax.trans ((max_le le_rfl hle).trans hsb)
    · right
      refine ⟨M.stalkHom x g, ⟨(M.stalkEquiv x g).2, ?_⟩, ?_⟩
      · have hnu : ¬ IsUnit (M.stalkEquiv x g) := fun h => hg (by simpa using h.map (M.stalkEquiv x).symm)
        rw [RatModel.isUnit_O_iff] at hnu
        by_cases h0 : (M.stalkEquiv x g : Ω) = 0
        · exact Or.inl h0
        · exact Or.inr fun h => hnu ⟨h0, h⟩
      · rw [hval g, key]
        have h1 : ‖((i.comp ev₀) (j g) : PadicAlgCl p)‖ ≤ 1 := (mem_OO_iff _).1 ((i.comp ev₀) (j g)).2
        have h2 := pow_le_pow_of_le_one (norm_nonneg _) h1 (le_max_right e (C e))
        exact hmax.trans ((max_le (le_of_not_ge hle) le_rfl).trans (hgn.trans h2)))
  have hmax : maximalIdeal (M.O x) = (maximalIdeal (M.Z.presheaf.stalk x)).map (M.stalkEquiv x) := by
    have : ((maximalIdeal (M.Z.presheaf.stalk x)).map (M.stalkEquiv x)).IsMaximal :=
      Ideal.map_isMaximal_of_equiv (M.stalkEquiv x)
    exact (IsLocalRing.eq_maximalIdeal this).symm
  have hspan : Ideal.span {c : M.O x | ¬ IsUnit c} = maximalIdeal (M.O x) := by
    have : {c : M.O x | ¬ IsUnit c} = (maximalIdeal (M.O x) : Set (M.O x)) := rfl
    rw [this, Ideal.span_eq]
  rw [hspan, hmax, ← Ideal.map_pow] at hc
  have hc' : (M.stalkEquiv x).symm c ∈ maximalIdeal (M.Z.presheaf.stalk x) ^ e := by
    obtain ⟨c₀, hc₀, hc₀e⟩ := (Ideal.mem_map_of_equiv (M.stalkEquiv x) c).1 hc
    rw [← hc₀e, RingEquiv.symm_apply_apply]
    exact hc₀
  have ht' : t = (M.stalkEquiv x).symm a * b + (M.stalkEquiv x).symm c := by
    apply (M.stalkEquiv x).injective
    apply Subtype.ext
    rw [map_add (f := _), map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact hac
  have hle : (maximalIdeal (M.Z.presheaf.stalk x) ^ max e (C e)).map j ≤ (maximalIdeal (M.Z.presheaf.stalk x) ^ e).map j :=
    Ideal.map_mono (Ideal.pow_le_pow_right (le_max_left _ _))
  have hs' : s = (j t + (s - j t)) := by ring
  have hd := hle ht
  rw [hs']
  refine Ideal.add_mem _ ?_ (Ideal.mem_sup_right hd)
  rw [ht', map_add (f := _), map_mul]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hc'))

end GlobalTheory.CplDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialisationCoordinateNeZeroClassical
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialisationCoordinateNeZeroClassical
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.CoordNe

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem perp_top (S : ThetaSys o Ω) : S.perp ⊤ = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  have ha' : ∀ h : S.Gam, eStd S.g _ a h = 0 := fun h => ha h trivial
  funext k
  rcases k with i | i
  · have := ha' (Pi.single (Sum.inr i) 1)
    simpa [eStd, Pi.single_apply] using this
  · have := ha' (Pi.single (Sum.inl i) 1)
    simpa [eStd, Pi.single_apply] using this

theorem TT_eq_bot {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {z : M.Z} (hz : z ∈ U₀) :
    S.TT M z = ⊥ := by
  have h : S.supI M z = {x | S.th x ≠ 0} := by
    refine Set.ext fun x => ⟨fun hx => hx.1, fun hx => ⟨hx, fun i => ?_⟩⟩
    rw [div_eq_mul_inv]
    exact RatModel.ringOn_le_O hz (mul_mem (hO.le (S.th_mem i)) (hO.th_unit x hx))
  unfold ThetaSys.TT ThetaSys.HH
  rw [h, S.supp, perp_top]

theorem isOpen_TT (S : ThetaSys o Ω) (M : RatModel o Ω) : IsOpen {z | S.TT M z = ⊥} := by
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  have : Finite S.Gam := inferInstance
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨⋂ x ∈ S.supI M z, {w | M.Div S.th x w}, fun w hw => ?_,
    (Set.toFinite _).isOpen_biInter fun x _ => M.isOpen_setOf_div S.th x, Set.mem_iInter₂.2 fun x hx => hx⟩
  have hsup : S.supI M z ⊆ S.supI M w := fun x hx => Set.mem_iInter₂.1 hw x hx
  have h : S.TT M w ≤ S.TT M z := fun a ha x hx => ha x (AddSubgroup.closure_mono hsup hx)
  exact le_bot_iff.1 (h.trans (le_of_eq hz))

theorem coord_ne_zero : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (x : M.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R) (D : DegData R (maximalIdeal R)), (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ α s, PsiCoord D.toPre α s → (ev s : PadicAlgCl p) ≠ 0 := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm hO x R _ _ _ j D hPsi p _ y ev hCen hfac α s hs h0
  let w : Sp (PadicAlgCl p) := (⊥ : PrimeSpectrum (PadicAlgCl p))
  have hW : IsOpen ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G) := by
    refine IsOpen.preimage (spMap j ≫ M.Z.fromSpecStalk x).continuous ?_
    rw [FinalForm.ab]
    exact isOpen_TT S M
  have hp : spMap ev (gPt p w) ∈ (spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G := by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hfac, FinalForm.ab]
    exact TT_eq_bot hO (hCen.2 ⟨w, rfl⟩)
  apply GlobalTheory.PsiCoordLocal.not_mem_of_coord hW hp (hPsi α) hs
  change (ev s : PadicAlgCl p) ∈ (⊥ : Ideal (PadicAlgCl p))
  exact h0

end GlobalTheory.Poinc.CoordNe
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialisationCoordinateNeZeroClassicalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTrivialisation_coordinate_ne_zero_classical : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (x : M.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R) (D : DegData R (maximalIdeal R)), (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ α s, PsiCoord D.toPre α s → (ev s : PadicAlgCl p) ≠ 0 := by
  first | exact @GlobalTheory.Poinc.CoordNe.coord_ne_zero | exact GlobalTheory.Poinc.CoordNe.coord_ne_zero | (intros; apply GlobalTheory.Poinc.CoordNe.coord_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStalkOfClassicalValuesNormLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStalkOfClassicalValuesNormLeOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem mem_O_of_norm_val_le_one : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U₀ : M.Z.Opens), (U₀ : Set M.Z).Nonempty → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ f ∈ M.ringOn (U₀ : Set M.Z), (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ x y → ‖M.val (gPt p ≫ y) f‖ ≤ 1) → f ∈ M.O x := by
  intro o' Ω _ _ _ _ M hn U₀ hU x hx f hf hb
  obtain ⟨h1, h2⟩ := flat_and_lft_toInt M
  letI : Flat (M.s ≫ spMap (algebraMap ℤ o')) := h1
  letI : LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o')) := h2
  obtain ⟨φ, rfl⟩ := (RatModel.mem_ringOn_iff_exists hU).1 hf
  obtain ⟨W, ψ, hxW, h⟩ := GlobalTheory.regular_of_bounded_at_padicAlgCl_points.1 M.Z (M.s ≫ spMap (algebraMap ℤ o')) x hx
    (hn x).2 U₀ φ hU fun p _ y e1 e2 => (RatModel.val_valF e2 φ) ▸ hb p y ⟨e1, e2⟩
  have hWU := M.nonempty_inf ⟨x, hxW⟩ hU
  have e : valF M.pt W ψ = valF M.pt U₀ φ := (M.valF_resG inf_le_left hWU ψ).symm.trans
    ((congrArg _ h).trans (M.valF_resG inf_le_right hWU φ))
  exact e ▸ RatModel.valF_mem_O hxW ψ

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStalkOfClassicalValuesNormLeOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_stalk_of_classicalValues_norm_le_one : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U₀ : M.Z.Opens), (U₀ : Set M.Z).Nonempty → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ f ∈ M.ringOn (U₀ : Set M.Z), (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ x y → ‖M.val (gPt p ≫ y) f‖ ≤ 1) → f ∈ M.O x := by
  first | exact @GlobalTheory.Poinc.mem_O_of_norm_val_le_one | exact GlobalTheory.Poinc.mem_O_of_norm_val_le_one | (intros; apply GlobalTheory.Poinc.mem_O_of_norm_val_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalPsiCoordinateAssociatedFourierPower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.QUnit

theorem FF_mem {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) : S.FF T c k ∈ S.R := by
  unfold ThetaSys.FF
  refine finsum_induction (fun v => v ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_
  exact mul_mem (Subalgebra.algebraMap_mem _ _) (sum_mem fun i _ => mul_mem (Subalgebra.algebraMap_mem _ _) (S.ev_mem _ _))

theorem main : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ α₀ : D.toPre.X, ∃ mu : D.toPre.X, CongMod S.N mu α₀ ∧ (∀ α, CongMod S.N α α₀ → ∀ r s, PsiCoord D.toPre mu r → PsiCoord D.toPre α s → r ∣ s) ∧ ∃ (e : Ω) (a : M.Z.presheaf.stalk x), e ≠ 0 ∧ (∃ (T₀ : AddSubgroup S.Gam) (c' : T₀ →+ ZMod S.N) (κ : S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) (x₀ : S.Gam), S.IsoFree T₀ ∧ e = S.FF T₀ c' κ / S.th x₀) ∧ M.stalkHom x a = e ^ S.N ∧ ∀ r, PsiCoord D.toPre mu r → Associated (j a) r := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hB hj G _ _ gm hpb D A U hLB hPsi α₀
  obtain ⟨hiso, hc⟩ := GlobalTheory.T.thetaConstant_fourierParts_bounded_classMinima o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hB hj G gm hpb D A U hLB hPsi
  obtain ⟨c', hc'⟩ := hc α₀
  have hO := hAdm.1
  obtain ⟨x₀, hx₀⟩ := hO.div x
  have hRU : ∀ v ∈ S.R, v ∈ M.ringOn (U₀ : Set M.Z) := fun v hv => hO.le hv
  have hext : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ x y →
      ∃ ev : R →+* OO p, IsLocalHom ev ∧ spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y := by
    intro p _ y hy
    obtain ⟨V, _, _, _, ev₀, i, -, hl₀, hli, -, hev, -⟩ := GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hj p y hy.1
    haveI := hl₀
    haveI := hli
    exact ⟨i.comp ev₀, RingHom.isLocalHom_comp _ _, hev⟩
  obtain ⟨p₁, hp₁, y₁, hy₁⟩ := GlobalTheory.Poinc.exists_cen_main o' Ω M x hx U₀ hO.ne
  obtain ⟨ev₁, hl₁, hev₁⟩ := hext p₁ y₁ hy₁
  have hN0 : S.N ≠ 0 := by have := S.N_ge; omega
  have hFFne : S.FF (S.TT M x) c' ≠ 0 := by
    intro h0
    obtain ⟨hlow, κ₂, hup⟩ := hc' p₁ y₁ ev₁ hy₁ hev₁ x₀ hx₀
    obtain ⟨α, s, hα, hs, -⟩ := hlow κ₂
    have h1 := hup α s hα hs
    rw [show S.FF (S.TT M x) c' κ₂ = 0 from congrFun h0 κ₂, zero_div, RatModel.val_zero, norm_zero,
      zero_pow hN0] at h1
    exact GlobalTheory.T.thetaTrivialisation_coordinate_ne_zero_classical o' Ω S ρ M U₀ EE FinalForm hO x R j D hPsi p₁ y₁ ev₁ hy₁ hev₁ α s hs (norm_le_zero_iff.1 h1)
  obtain ⟨κ₁, hκ₁⟩ := hAdm.2 (S.TT M x) c' hiso hFFne x
  have he0 : S.FF (S.TT M x) c' κ₁ / S.th x₀ ≠ 0 := div_ne_zero hκ₁.1 hx₀.1
  have heU : S.FF (S.TT M x) c' κ₁ / S.th x₀ ∈ M.ringOn (U₀ : Set M.Z) := by
    rw [div_eq_mul_inv]
    exact mul_mem (hRU _ (FF_mem S (S.TT M x) c' κ₁)) (hO.th_unit x₀ hx₀.1)
  have heU' : (S.FF (S.TT M x) c' κ₁ / S.th x₀)⁻¹ ∈ M.ringOn (U₀ : Set M.Z) := by
    rw [inv_div, div_eq_mul_inv]
    exact mul_mem (hRU _ (S.th_mem x₀)) (hO.FF_unit (S.TT M x) c' κ₁ hiso hκ₁.1)
  have hpt : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y →
      spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y →
      0 < ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ∧
      ‖M.val (gPt p ≫ y) ((S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N)‖ = ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ^ S.N ∧
      (∀ α s, CongMod S.N α α₀ → PsiCoord D.toPre α s →
        ‖(ev s : PadicAlgCl p)‖ ≤ ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ^ S.N) ∧
      ∃ mu s, CongMod S.N mu α₀ ∧ PsiCoord D.toPre mu s ∧
        ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ^ S.N ≤ ‖(ev s : PadicAlgCl p)‖ := by
    intro p _ y ev hy hev
    have hrange : Set.range (gPt p ≫ y) = {(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))} :=
      RatModel.range_eq_singleton _ _
    have hsp := RatModel.specializes_of_range_eq hrange
    have hz'U : (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ (U₀ : Set M.Z) := hy.2 ⟨_, rfl⟩
    have hz'x := RatModel.gPt_specializes hy.1 (IsLocalRing.closedPoint (PadicAlgCl p))
    have heO := RatModel.ringOn_le_O hz'U heU
    have heO' := RatModel.ringOn_le_O hz'U heU'
    have hpos : 0 < ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ :=
      norm_pos_iff.2 ((RatModel.val_ne_zero_iff hrange ⟨_, heO⟩).2 ((RatModel.isUnit_O_iff _).2 ⟨he0, heO'⟩))
    have hpow : ‖M.val (gPt p ≫ y) ((S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N)‖ =
        ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ ^ S.N := by
      have := map_pow (RatModel.valHomOf (gPt p ≫ y) _ hsp) ⟨_, heO⟩ S.N
      rw [RatModel.valHomOf_apply, RatModel.valHomOf_apply] at this
      rw [← norm_pow, ← this]
      rfl
    have hle : ∀ κ, ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ / S.th x₀)‖ ≤
        ‖M.val (gPt p ≫ y) (S.FF (S.TT M x) c' κ₁ / S.th x₀)‖ := by
      intro κ
      have hq : S.FF (S.TT M x) c' κ / S.FF (S.TT M x) c' κ₁ ∈ M.O x := hκ₁.2 κ
      have hq' := RatModel.O_le_of_specializes hz'x hq
      have eq : S.FF (S.TT M x) c' κ / S.th x₀ =
          (S.FF (S.TT M x) c' κ / S.FF (S.TT M x) c' κ₁) * (S.FF (S.TT M x) c' κ₁ / S.th x₀) := by
        have := hκ₁.1
        have := hx₀.1
        field_simp
      rw [eq, RatModel.val_mul hsp hq' heO, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one hy.1 hq)
    obtain ⟨hlow, κ₂, hup⟩ := hc' p y ev hy hev x₀ hx₀
    refine ⟨hpos, hpow, fun α s hα hs => (hup α s hα hs).trans (pow_le_pow_left₀ (norm_nonneg _) (hle κ₂) _), ?_⟩
    exact hlow κ₁
  have hmem : (S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N ∈ M.O x := by
    refine GlobalTheory.T.mem_stalk_of_classicalValues_norm_le_one o' Ω M hO.normal U₀ hO.ne x hx _ (pow_mem heU _) fun p _ y hy => ?_
    obtain ⟨ev, -, hev⟩ := hext p y hy
    obtain ⟨-, hpow, -, mu, s, -, -, h⟩ := hpt p y ev hy hev
    rw [hpow]
    exact h.trans ((mem_OO_iff _).1 (ev s).2)
  have hstalk : M.stalkHom x ((M.stalkEquiv x).symm ⟨_, hmem⟩) = (S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N := by
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  have ha0 : (M.stalkEquiv x).symm ⟨_, hmem⟩ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hstalk
    exact pow_ne_zero _ he0 hstalk.symm
  have hva : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y →
      spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y →
      ((ev (j ((M.stalkEquiv x).symm ⟨_, hmem⟩)) : OO p) : PadicAlgCl p) =
        M.val (gPt p ≫ y) ((S.FF (S.TT M x) c' κ₁ / S.th x₀) ^ S.N) := by
    intro p _ y ev hy hev
    have hφ : spMap (ev.comp j) ≫ M.Z.fromSpecStalk x = y := by
      rw [← hev]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    have := GlobalTheory.CplDiv.val_stalkHom_eq o' Ω M x p y (ev.comp j) hy.1 hφ ((M.stalkEquiv x).symm ⟨_, hmem⟩)
    rw [hstalk] at this
    exact this.symm
  have hdvd : ∀ α s, CongMod S.N α α₀ → PsiCoord D.toPre α s → j ((M.stalkEquiv x).symm ⟨_, hmem⟩) ∣ s := by
    intro α s hα hs
    refine GlobalTheory.CplDiv.dvd_of_norm_le_at_classical o' Ω M hO.normal U₀ hO.ne x hx R j hj _ s ha0
      fun p _ y ev hy hev => ?_
    obtain ⟨-, hpow, hup, -⟩ := hpt p y ev hy hev
    rw [hva p y ev hy hev, hpow]
    exact hup α s hα hs
  obtain ⟨hpos₁, hpow₁, -, mu, smu, hmu, hsmu, hlow₁⟩ := hpt p₁ y₁ ev₁ hy₁ hev₁
  obtain ⟨t, ht⟩ := hdvd mu smu hmu hsmu
  have ht1 : 1 ≤ ‖((ev₁ t : OO p₁) : PadicAlgCl p₁)‖ := by
    have h := hlow₁
    rw [ht, map_mul, MulMemClass.coe_mul, norm_mul, hva p₁ y₁ ev₁ hy₁ hev₁, hpow₁] at h
    exact (le_mul_iff_one_le_right (pow_pos hpos₁ _)).1 h
  have htu : IsUnit t := by
    have hu : IsUnit (ev₁ t) := by
      by_contra hn
      exact absurd ((not_isUnit_OO_iff _).1 hn) (not_lt.2 ht1)
    exact isUnit_of_map_unit ev₁ t hu
  have hassoc : Associated (j ((M.stalkEquiv x).symm ⟨_, hmem⟩)) smu := ⟨htu.unit, by rw [ht, IsUnit.unit_spec]⟩
  refine ⟨mu, hmu, fun α hα r s hr hs => ?_, _, _, he0, ⟨S.TT M x, c', κ₁, x₀, hiso, rfl⟩, hstalk, fun r hr => ?_⟩
  · obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord hsmu hr
    have : Associated (j ((M.stalkEquiv x).symm ⟨_, hmem⟩)) r := hassoc.trans ⟨u, by rw [hu, mul_comm]⟩
    exact this.symm.dvd.trans (hdvd α s hα hs)
  · obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord hsmu hr
    exact hassoc.trans ⟨u, by rw [hu, mul_comm]⟩

end GlobalTheory.QUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalPsiCoordinateAssociatedFourierPowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_minimal_psiCoordinate_associated_fourierPower : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ α₀ : D.toPre.X, ∃ mu : D.toPre.X, CongMod S.N mu α₀ ∧ (∀ α, CongMod S.N α α₀ → ∀ r s, PsiCoord D.toPre mu r → PsiCoord D.toPre α s → r ∣ s) ∧ ∃ (e : Ω) (a : M.Z.presheaf.stalk x), e ≠ 0 ∧ (∃ (T₀ : AddSubgroup S.Gam) (c' : T₀ →+ ZMod S.N) (κ : S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) (x₀ : S.Gam), S.IsoFree T₀ ∧ e = S.FF T₀ c' κ / S.th x₀) ∧ M.stalkHom x a = e ^ S.N ∧ ∀ r, PsiCoord D.toPre mu r → Associated (j a) r := by
  first | exact @GlobalTheory.QUnit.main | exact GlobalTheory.QUnit.main | (intros; apply GlobalTheory.QUnit.main <;> assumption)
end
