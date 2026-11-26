module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfContragredientConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfContragredientConjugate
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.ContraPair.SphTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem conjFin_locGL_mem (w : HeightOneSpectrum (𝓞 E))
    (hw : conjSrc (IsCMField.complexConj E).toRingEquiv w = w) (k : GL (Fin a) (w.adicCompletion E))
    (hk : k ∈ GlobalTheory.LFun.KGL w (n := a)) : ∃ k' ∈ GlobalTheory.LFun.KGL w (n := a),
      Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E a w k) = locGL E a w k' := by
  have key : ∀ u (h : conjSrc (IsCMField.complexConj E).toRingEquiv w = u) (k : GL (Fin a) (u.adicCompletion E)),
      k ∈ GlobalTheory.LFun.KGL u (n := a) → ∃ k' ∈ GlobalTheory.LFun.KGL w (n := a),
        Matrix.GeneralLinearGroup.map (conjFin (IsCMField.complexConj E).toRingEquiv) (locGL E a u k) = locGL E a w k' := by
    intro u h k hk
    subst h
    refine ⟨_, ?_, GlobalTheory.ConjPairLoc.conjFin_locGL _ w k⟩
    obtain ⟨k0, rfl⟩ := hk
    let r : Formalism.UG.Ov E (conjSrc (IsCMField.complexConj E).toRingEquiv w) →+* Formalism.UG.Ov E w :=
      (conjLoc (IsCMField.complexConj E).toRingEquiv w).restrict _ _ fun x hx => by
        change _ ∈ w.adicCompletionIntegers E
        change x ∈ (conjSrc (IsCMField.complexConj E).toRingEquiv w).adicCompletionIntegers E at hx
        rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
        rw [(conjLoc_spec _ w).2.2]
        exact hx
    refine ⟨Matrix.GeneralLinearGroup.map r k0, ?_⟩
    ext i j
    rfl
  exact key w hw k hk

end GlobalTheory.ContraPair.SphTwist


open GlobalTheory.ContraPair.SphTwist in
theorem GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy π ψ → ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ψ⁻¹).locRep w) (GlobalTheory.LFun.KGL w (n := a)) := by
  intro E _ _ _ a _ π ψ hP w hns hS
  obtain ⟨B0, hB0⟩ := hS
  obtain ⟨B, -, hB2, hfin, -, -⟩ := hP
  have hsat : GlobalTheory.LFun.HasSatGL w (π.locRep w) B0 := (CG.hasSat_mk π w B0).1 hB0
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsat.1
  obtain ⟨y, hy⟩ : ∃ y, B y x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (hB2 x h)
  have hw : conjSrc (IsCMField.complexConj E).toRingEquiv w = w := by
    by_contra h
    exact hns ⟨_, h, GlobalTheory.DefU.LocRet.under_conjSrc w⟩
  have hL : ∀ k ∈ GlobalTheory.LFun.KGL w (n := a), B.flip x ((π.twist ψ⁻¹).locRep w k y) = B.flip x y := by
    intro k hk
    obtain ⟨k', hk', e⟩ := GlobalTheory.ContraPair.SphTwist.conjFin_locGL_mem w hw k hk
    have hx' : π.op (.fin (locGL E a w k')) x = x := GlobalTheory.LGrp.mem_fixed.1 hx k' hk'
    have h1 := hfin (locGL E a w k) y x
    change B ((π.twist ψ⁻¹).op (.fin (locGL E a w k)) y) x = B y x
    conv_lhs => rw [← hx']
    rw [← e]
    exact h1
  obtain ⟨v, hv, hve⟩ := GlobalTheory.SmGL.IwahoriOnto.exists_fixed_map_eq ((π.twist ψ⁻¹).isSmooth_locRep w)
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2 (B.flip x) y hL
  refine (Submodule.ne_bot_iff _).2 ⟨v, hv, fun h => hy ?_⟩
  have : B.flip x v = B y x := hve
  rw [← this, h, map_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfContragredientConjugateStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSpherical_twist_of_contragredient_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ψ : HChar E), GlobalTheory.ContraPair.DualIsConjBy π ψ → ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ψ⁻¹).locRep w) (GlobalTheory.LFun.KGL w (n := a)) := by
  first | exact @GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy | exact GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy | (intros; apply GlobalTheory.ContraPair.isSpherical_twist_of_dualIsConjBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtOfSphericalAndTwistSpherical
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateMemTwistedJacquetKernelRamified
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateMemTwistedJacquetKernelRamified
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CartanCoinv

open GlobalTheory.PRep

section Gen
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)

theorem sub_mem_coinv {k : G} (hk : k ∈ K) (v : V) : ρ k v - v ∈ twKer ρ K 1 :=
  Submodule.subset_span ⟨⟨k, hk⟩, v, by simp⟩

theorem apply_mem_coinv {k : G} (hk : k ∈ K) {v : V} (hv : v ∈ twKer ρ K 1) : ρ k v ∈ twKer ρ K 1 := by
  have := (twKer ρ K 1).add_mem (sub_mem_coinv ρ K hk v) hv
  simpa using this

theorem mem_coinv_of_eigen {k : G} (hk : k ∈ K) {v : V} {c : ℂ} (hc : c ≠ 1) (hv : ρ k v = c • v) :
    v ∈ twKer ρ K 1 := by
  have h := (twKer ρ K 1).smul_mem (c - 1)⁻¹ (sub_mem_coinv ρ K hk v)
  have e : (c - 1)⁻¹ • (ρ k v - v) = v := by
    have : ρ k v - v = (c - 1) • v := by rw [hv, sub_smul, one_smul]
    rw [this, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hc), one_smul]
  rwa [e] at h

end Gen

def diagUnit {R : Type} [CommRing R] {a : ℕ} (f : Fin a → Rˣ) : GL (Fin a) R where
  val := Matrix.diagonal fun i => (f i : R)
  inv := Matrix.diagonal fun i => ((f i)⁻¹ : Rˣ)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp

theorem exists_diag {L : Type} [Field L] (O : Subring L) {a : ℕ} (ha : 1 ≤ a) (u : Lˣ) (h1 : (u : L) ∈ O)
    (h2 : ((u⁻¹ : Lˣ) : L) ∈ O) : ∃ d ∈ Formalism.UG.GLint (Fin a) O, Matrix.GeneralLinearGroup.det d = u ∧
      ∃ f : Fin a → L, (d : Matrix (Fin a) (Fin a) L) = Matrix.diagonal f := by
  let u' : Oˣ := ⟨⟨u, h1⟩, ⟨(u⁻¹ : Lˣ), h2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  let f : Fin a → Oˣ := Function.update 1 ⟨0, ha⟩ u'
  have hm : ((Formalism.UG.bc O.subtype (diagUnit f) : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      Matrix.diagonal fun i => ((f i : O) : L) := by
    change (Matrix.diagonal fun i => (f i : O)).map O.subtype = _
    rw [Matrix.diagonal_map (map_zero _)]
    rfl
  refine ⟨Formalism.UG.bc O.subtype (diagUnit f), ⟨_, rfl⟩, ?_, _, hm⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, hm, Matrix.det_diagonal,
    Finset.prod_eq_single (⟨0, ha⟩ : Fin a)]
  · simp [f, u']
  · intro b _ hb
    simp [f, Function.update_of_ne hb]
  · simp

theorem translate_mem_twKer : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (u : (w.adicCompletion E)ˣ), 1 ≤ a → Valued.v (u : w.adicCompletion E) = 1 → χ u ≠ 1 → ∀ y : V, (∀ k ∈ GlobalTheory.LFun.KGL w (n := a), ρ k y = (((χ (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y) → ∀ g, ρ g y ∈ GlobalTheory.PRep.twKer ρ (GlobalTheory.LFun.KGL w (n := a)) 1 := by
  intro E _ _ w a V _ _ ρ χ u ha hu hχ y hy g
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  obtain ⟨ex, -, k₁, hk₁, k₂, hk₂, e⟩ :=
    Formalism.UG.Final.CartanDecomp E w a ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ g
  set D : GL (Fin a) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hDdef
  have hD : (D : Matrix (Fin a) (Fin a) (w.adicCompletion E)) = Formalism.UG.diagPow E w ϖ ex := by
    rw [hDdef, Units.val_mul, Units.val_mul, e]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hg : g = k₁ * D * k₂ := by rw [hDdef]; group
  clear_value D
  have h1 : (u : w.adicCompletion E) ∈ Formalism.UG.Ov E w := by
    change Valued.v (u : w.adicCompletion E) ≤ 1
    exact hu.le
  have h2 : ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ∈ Formalism.UG.Ov E w := by
    change Valued.v ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  obtain ⟨d, hd, hdet, f, hf⟩ := exists_diag (Formalism.UG.Ov E w) ha u h1 h2
  have hcomm : d * D = D * d := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD, hf, Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hDy : ρ D y ∈ twKer ρ (GlobalTheory.LFun.KGL w (n := a)) 1 := by
    refine mem_coinv_of_eigen ρ _ hd (c := (((χ u)⁻¹ : ℂˣ) : ℂ)) ?_ ?_
    · intro h
      exact hχ (inv_eq_one.1 (Units.ext h))
    · rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hy d hd, hdet, map_smul]
  rw [hg, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hy k₂ hk₂, map_smul, map_smul]
  exact Submodule.smul_mem _ _ (apply_mem_coinv ρ _ hk₁ hDy)

end GlobalTheory.CartanCoinv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateMemTwistedJacquetKernelRamifiedStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_mem_twistedJacquetKernel_ramified : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (u : (w.adicCompletion E)ˣ), 1 ≤ a → Valued.v (u : w.adicCompletion E) = 1 → χ u ≠ 1 → ∀ y : V, (∀ k ∈ GlobalTheory.LFun.KGL w (n := a), ρ k y = (((χ (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y) → ∀ g, ρ g y ∈ GlobalTheory.PRep.twKer ρ (GlobalTheory.LFun.KGL w (n := a)) 1 := by
  first | exact @GlobalTheory.CartanCoinv.translate_mem_twKer | exact GlobalTheory.CartanCoinv.translate_mem_twKer | (intros; apply GlobalTheory.CartanCoinv.translate_mem_twKer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtOfSphericalAndTwistSpherical
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.SphTwistUnr

open GlobalTheory.PRep

theorem map_mem_twKer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
    (S : V →ₗ[ℂ] V) (hS : ∀ h, S ∘ₗ ρ h = ρ h ∘ₗ S) {v : V} (hv : v ∈ twKer ρ K 1) : S v ∈ twKer ρ K 1 := by
  have h : (twKer ρ K 1).map S ≤ twKer ρ K 1 := by
    rw [twKer, Submodule.map_span_le]
    rintro _ ⟨n, u, rfl⟩
    refine Submodule.subset_span ⟨n, S u, ?_⟩
    have := LinearMap.congr_fun (hS n) u
    simp only [LinearMap.comp_apply] at this
    simp [this]
  exact h ⟨v, hv, rfl⟩

theorem unrAt_of_isSpherical_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ξ).locRep w) (GlobalTheory.LFun.KGL w (n := a)) → ξ.UnrAt w := by
  intro E _ _ _ a ha π ξ w hB hsph
  obtain ⟨B, hB⟩ := hB
  have hS : GlobalTheory.LFun.HasSatGL w (π.locRep w) B := (CG.hasSat_mk π w B).1 hB
  have hK : IsCompact ((GlobalTheory.LFun.KGL w (n := a) : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have hsm : IsSmooth (π.locRep w) := π.isSmooth_locRep w
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hS.1
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).1 hsph
  have hT : ∀ g v, (π.twist ξ).locRep w g (π.toTwist ξ v) =
      ((ξ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • π.toTwist ξ (π.locRep w g v) := by
    intro g v
    rw [CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]
    rfl
  obtain ⟨y, rfl⟩ := (π.toTwist ξ).surjective z
  have hy0 : y ≠ 0 := fun h => hz0 (by rw [h]; exact (π.toTwist ξ).toLinearMap.map_zero)
  have hy : ∀ k ∈ GlobalTheory.LFun.KGL w (n := a), π.locRep w k y =
      (((ξ.loc w (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y := by
    intro k hk
    have h1 := GlobalTheory.LGrp.mem_fixed.1 hz k hk
    rw [hT] at h1
    apply (π.toTwist ξ).injective
    rw [map_smul, ← h1, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  by_contra hne
  obtain ⟨u, hu, hξu⟩ : ∃ u, Formalism.L2.Host.IsUnitAt w u ∧ ξ.loc w u ≠ 1 := by
    by_contra h
    push_neg at h
    exact hne h
  have hall := GlobalTheory.T.translate_mem_twistedJacquetKernel_ramified E w a π.V (π.locRep w) (ξ.loc w) u ha hu hξu y hy
  let Wl : Submodule ℂ π.V := ⨅ g, (twKer (π.locRep w) (GlobalTheory.LFun.KGL w (n := a)) 1).comap (π.locRep w g)
  have memWl : ∀ v, v ∈ Wl ↔ ∀ g, π.locRep w g v ∈ twKer (π.locRep w) (GlobalTheory.LFun.KGL w (n := a)) 1 := fun v => by
    simp [Wl, Submodule.mem_iInf]
  have stab : GlobalTheory.CuspRep.IsStable (Wl.map π.V.subtype) := by
    rintro o _ ⟨v, hv, rfl⟩
    obtain ⟨g, S, hS, ho⟩ := GlobalTheory.T.exists_localTranslation_comp_commuting_operator E a π w o
    have hv' := (memWl v).1 hv
    refine ⟨π.op o v, (memWl _).2 fun h => ?_, rfl⟩
    rw [ho, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul]
    have e := LinearMap.congr_fun (hS (h * g)) v
    simp only [LinearMap.comp_apply] at e
    rw [← e]
    exact map_mem_twKer S hS (hv' (h * g))
  rcases π.irred _ (Submodule.map_subtype_le _ _) stab with h | h
  · have h1 : (y : GlobalTheory.CuspRep.Sm E a) ∈ Wl.map π.V.subtype := ⟨y, (memWl y).2 hall, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    exact hy0 (Subtype.ext h1)
  · have h1 : (x : GlobalTheory.CuspRep.Sm E a) ∈ Wl.map π.V.subtype := by rw [h]; exact x.2
    obtain ⟨x', hx', e⟩ := h1
    obtain rfl : x' = x := Subtype.ext e
    have h2 := (memWl x').1 hx' 1
    rw [map_one, Module.End.one_apply] at h2
    exact hx0 (Submodule.disjoint_def.1 (GlobalTheory.LocGL.isCompl_fixed_twKer hsm hK).disjoint x' hx h2)

end GlobalTheory.SphTwistUnr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharUnrAtOfSphericalAndTwistSphericalStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unrAt_of_spherical_and_twist_spherical : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (ξ : HChar E) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk π).HasSat w B) → GlobalTheory.LGrp.IsSpherical ((π.twist ξ).locRep w) (GlobalTheory.LFun.KGL w (n := a)) → ξ.UnrAt w := by
  first | exact @GlobalTheory.SphTwistUnr.unrAt_of_isSpherical_twist | exact GlobalTheory.SphTwistUnr.unrAt_of_isSpherical_twist | (intros; apply GlobalTheory.SphTwistUnr.unrAt_of_isSpherical_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section
namespace GlobalTheory.GoodCsdTwist

open GlobalTheory.ContraPair

theorem unrAt_mul {K : Type} [Field K] [NumberField K] {χ χ' : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) (h' : χ'.UnrAt v) : (χ * χ').UnrAt v := fun x hx => by
  change χ.loc v x * χ'.loc v x = 1
  rw [h x hx, h' x hx, mul_one]

theorem unrAt_inv {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) : (χ⁻¹).UnrAt v := fun x hx => by
  change (χ.loc v x)⁻¹ = 1
  rw [h x hx, inv_one]

theorem unrAt_pow {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)}
    (h : χ.UnrAt v) : ∀ k : ℕ, (χ ^ k).UnrAt v
  | 0 => fun _ _ => rfl
  | k + 1 => by rw [pow_succ]; exact unrAt_mul (unrAt_pow h k) h

theorem isAlgPos_mul {F : Type} [Field F] [NumberField F] {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ}
    (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') : IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

theorem regAlg_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

theorem neg_one_zpow_natAbs (z : ℤ) : ((-1 : ℂˣ) ^ z.natAbs) = (-1 : ℂˣ) ^ (-z) := by
  rcases Int.even_or_odd z with h | h
  · rw [h.neg.neg_one_zpow, (Int.natAbs_even.2 h).neg_one_pow]
  · rw [h.neg.neg_one_zpow, (Int.natAbs_odd.2 h).neg_one_pow]

theorem exists_goodCsd_twist : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .good l π χ → ∀ w₀ : HeightOneSpectrum (𝓞 E),
    GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m ∧ κ.UnrAt w₀ ∧
    InScope .csd l (π.twist κ) (quadChar E ^ a) := by
  intro _ E _ _ _ l a ha π χ ⟨hreg, hpol, hgood⟩ w₀ hw₀
  obtain ⟨n, hn⟩ := GlobalTheory.RegAlgCharAlg.isAlgPos_of_polarizedPair E a ha π χ hreg hpol
  obtain ⟨φ₀⟩ : Nonempty (maximalRealSubfield E →+* ℂ) := inferInstance
  have hb : IsAlgPos χ (fun _ => n φ₀) := by
    rw [show (fun _ => n φ₀) = n from funext fun φ => UpperTheory.heckeChar_parallel_weight _ χ n hn φ₀ φ]
    exact hn
  have hinv : IsAlgPos χ⁻¹ (fun _ => -n φ₀) := fun k hk => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, hb k hk, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  have ho : (quadChar E ^ (a + (n φ₀).natAbs)).OrderDvd 2 := by
    unfold HChar.OrderDvd
    rw [← pow_mul, mul_comm, pow_mul]
    have : (quadChar E) ^ 2 = 1 := by
      refine Subtype.ext (MonoidHom.ext fun x => ?_)
      change (Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E x)) ^ 2 = 1
      rw [← map_pow, Int.units_sq, map_one]
    rw [this, one_pow]
  have hpos := isAlgPos_mul hinv (isAlgPos_zero_of_orderDvd two_pos ho)
  rw [add_zero] at hpos
  have hsign : ∀ v, (χ⁻¹ * quadChar E ^ (a + (n φ₀).natAbs)).locInf v (-1) = (-1) ^ (-n φ₀) := fun v => by
    change (χ.locInf v (-1))⁻¹ * ((quadChar E ^ (a + (n φ₀).natAbs)).locInf v (-1)) = _
    rw [locInf_pow, quadChar_locInf]
    rw [hpol.sign v, pow_add, inv_mul_cancel_left, neg_one_zpow_natAbs]
  have halg := UpperTheory.heckeChar_algebraic_of_sign _ _ (-n φ₀) hpos hsign
  have hunr : ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w →
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal ∧
      (χ⁻¹ * quadChar E ^ (a + (n φ₀).natAbs)).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := fun w hw => by
    obtain ⟨-, hu, hsat⟩ := hgood.2.2 w hw
    have h1 := GlobalTheory.T.heckeChar_unrAt_of_spherical_and_twist_spherical E a ha π _ w hsat (GlobalTheory.T.isSpherical_twist_of_contragredient_conjugate E a ha π _ hpol.dual w hw hsat)
    replace h1 := unrAt_inv h1
    rw [inv_inv] at h1
    exact ⟨hu, unrAt_mul (unrAt_inv (GlobalTheory.T.heckeChar_unrAt_under_of_compNorm_unramified E χ w hw hu h1)) (unrAt_pow (GlobalTheory.T.quadraticHeckeChar_unramified_of_isUnramifiedAt E w hu) _)⟩
  obtain ⟨κ, m, hκ, hres, hκ0, hκu⟩ := GlobalTheory.T.exists_algebraic_hecke_char_split E _ (-n φ₀) halg hunr w₀ hw₀
  refine ⟨κ, m, hκ, hκ0, regAlg_twist hreg hκ, ⟨fun v => ?_, ?_⟩, ⟨hgood.1, hgood.2.1, fun w hw => ?_⟩, rfl⟩
  · rw [locInf_pow, quadChar_locInf]
  · rw [map_pow, compNorm_quadChar, one_pow, dualIsConjBy_one]
    exact UpperTheory.V.Af.Cq.csdTwist E a π _ κ hpol.dual
      (by rw [hres, map_mul, map_inv, map_pow, compNorm_quadChar, one_pow, mul_one])
  · obtain ⟨h1, h2, B, hB⟩ := hgood.2.2 w hw
    refine ⟨h1, h2, B.map (· * κ.val w), ?_⟩
    rw [CG.hasSat_mk] at hB ⊢
    exact GlobalTheory.SphGal.hasSatGL_twist E a π κ w B (hκu w hw) hB

end GlobalTheory.GoodCsdTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramifiedStatement
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_conjSelfDual_twist_split_unramified : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .good l π χ → ∀ w₀ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₀ → ∃ (κ : HChar E) (m : (E →+* ℂ) → ℤ), κ.IsAlg m ∧ κ.UnrAt w₀ ∧ InScope .csd l (π.twist κ) (quadChar E ^ a) := by
  first | exact @GlobalTheory.GoodCsdTwist.exists_goodCsd_twist | exact GlobalTheory.GoodCsdTwist.exists_goodCsd_twist | (intros; apply GlobalTheory.GoodCsdTwist.exists_goodCsd_twist <;> assumption)
end
