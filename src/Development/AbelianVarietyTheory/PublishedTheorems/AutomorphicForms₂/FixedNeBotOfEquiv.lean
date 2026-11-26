module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FixedNeBotOfEquiv
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.SplitRead

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

section Transport

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem fixed_ne_bot_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) {K : Subgroup G}
    (hπ : fixed π K ≠ ⊥) : fixed σ K ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hπ
  refine (Submodule.ne_bot_iff _).2 ⟨φ v, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, fun h1 => h0 ?_⟩
  · exact (φ.toIntertwiningMap.isIntertwining _ _ u v).symm.trans
      (congrArg φ (GlobalTheory.Parabolic.mem_fixed.1 hv u hu))
  · exact φ.toLinearEquiv.injective (h1.trans (map_zero _).symm)

end Transport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def toIrrRep {n : ℕ} (π : Irr (w.adicCompletion E) n) : IrrRep (GL (Fin n) (w.adicCompletion E)) :=
  ⟨π.V, π.π, π.smooth, π.irr⟩

theorem IsRec.recLaws {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) :
    RecLaws fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  have hc : ∀ (χ : (w.adicCompletion E)ˣ →* ℂˣ) (c : Irr (w.adicCompletion E) 1),
      Nonempty (c.π.Equiv (detRep (Fin 1) χ)) → ∃ hχ : IsSmoothChar χ, cls (toIrrRep c) = .ofChar χ hχ := by
    rintro χ c ⟨φ⟩
    have h1 : IsSmoothChar (detChar (Fin 1) χ) := (isSmooth_ofChar_iff _).1
      ((IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).isSmooth c.smooth)
    have h2 : Continuous (Matrix.GeneralLinearGroup.scalar (R := w.adicCompletion E) (Fin 1)) :=
      Units.continuous_map (continuous_matrix fun i j => by
        rw [Subsingleton.elim i j]; simpa using continuous_id')
    have h3 : (detChar (Fin 1) χ).comp (Matrix.GeneralLinearGroup.scalar (Fin 1)) = χ := by
      refine MonoidHom.ext fun z => congrArg χ ?_
      ext; simp [Matrix.GeneralLinearGroup.scalar]
    exact ⟨h3 ▸ h1.comp _ h2, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ⟨φ⟩)⟩
  refine ⟨fun n π => H.dim _, fun n π π' => H.eq_iff _ _, fun r t σ τ π hπ => H.prod r t _ _ _ hπ, ?_, ?_, ?_, ?_⟩
  · intro t χ c τ h1 h2
    obtain ⟨hχ, e⟩ := hc χ c h1
    rw [e, (H.eq_iff (toIrrRep τ) (IrrRep.det (Fin t) χ hχ)).2 h2, H.det, sumList, List.foldr_map, speh]
    simp [List.foldr_map, ← List.map_eq_flatMap]
  · intro n χ c π π' h1 h2
    obtain ⟨hχ, e⟩ := hc χ c h1
    rw [e, ← H.twist]
    exact congrArg rc ((IrrGL.of_eq_of.2 h2).trans (IrrGL.tw_of π.π π.smooth π.irr χ hχ).symm)
  · intro n π
    rw [← H.sph]
    exact ⟨fixed_ne_bot_of_equiv (equivRep (toIrrRep π)).symm, fixed_ne_bot_of_equiv (equivRep (toIrrRep π))⟩
  · intro n π α hα
    have φ := equivRep (toIrrRep π)
    rw [H.sat (cls (toIrrRep π)) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩, WD.frobEig_diag]

end GlobalTheory.LocLanglands
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.Test

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ}

theorem unr_lpOfChar_iff (ha : IsLocalArtin h a) {χ : (w.adicCompletion E)ˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    (WD.lpOfChar h (χ.comp a) (ha.smooth hχ)).unr ↔ IsUnram χ := by
  rw [WD.lpOfChar, WD.unr_mk]
  constructor
  · rintro ⟨-, H⟩ x hx
    obtain ⟨σ, rfl⟩ := ha.surj x
    have h0 : deg σ = 0 := by
      have := ha.ord_eq σ
      rw [ord_eq_zero_iff.2 hx] at this
      omega
    have h2 := congrFun (LinearMap.congr_fun (H ⟨_, deg_eq_zero_iff.mp h0⟩) fun _ => 1) 0
    have h3 : χ (a (ineIncl h ⟨_, deg_eq_zero_iff.mp h0⟩)) = 1 := by simpa using h2
    exact h3
  · intro H
    refine ⟨rfl, fun σ => LinearMap.ext fun v => funext fun i => ?_⟩
    have : χ (a (ineIncl h σ)) = 1 := H _ (ord_eq_zero_iff.1 (by rw [ha.ord_eq]; simp))
    simp [this]

theorem lpOfChar_unrChar (ha : IsLocalArtin h a) (c : ℂˣ) (hc) :
    WD.lpOfChar h ((SmGL.unrChar (w.adicCompletion E) c).comp a) hc = WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹) := by
  simp only [WD.lpOfChar, WDRep.diag, ha.unrChar_comp]

theorem lpChar_lpSp_one (x : WD h) : x.lpChar (WD.lpSp (h := h) 1) = x := by
  have h1 : WD.lpSp (h := h) 1 = WD.lpOfChar h (WeilDeligne.unrChar h (qPow w 0)) (isSmooth_unrChar h _) := by
    refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
    · funext i
      simp [WDRep.spEig]
    · funext i
      simp [shiftEnd_apply]
  rw [h1, lpChar_lpOfChar]
  exact WD.lpTw_zero x

end GlobalTheory.LocLanglands.Test
end
end
