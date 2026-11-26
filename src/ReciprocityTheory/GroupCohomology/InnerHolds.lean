module

public import ReciprocityTheory.GroupCohomology.CardLenStatement
public import ReciprocityTheory.GroupCohomology.PrismOpZeroEval

@[expose] public section

section -- merged from ReciprocityTheory.GroupCohomology.InnerHolds
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx

universe u

theorem inner_holds : InnerStatement.{u} := by
  intro R _ G _ _ _ M P s hφ hu n
  obtain ⟨e, he, he1, -⟩ := homogIso_holds R G M
  have hcomp : ∀ (n : ℕ) (F : M.coch.X n) (x : Fin (n + 1) → G),
      (e n (P.hom.f n F)).1 x = (e n F).1 fun i => x i * s := by
    intro n F x
    rw [he1, he1]
    show M.rho (x 0) (P.u (F.1 fun i => P.φ ((x i.castSucc)⁻¹ * x i.succ))) =
      M.rho (x 0 * s) (F.1 fun i => (x i.castSucc * s)⁻¹ * (x i.succ * s))
    rw [hu, map_mul]
    first
    | rw [LinearMap.mul_apply]
    | rw [Module.End.mul_apply]
    congr 1
    congr 1
    exact congrArg F.1 (funext fun i => by rw [hφ]; group)
  have key := (prism_holds R G M G G M.coch M.coch e e he he).2 (fun x => x * s) id P.hom
    (Cx.Hom.id M.coch) (continuous_id.mul continuous_const) continuous_id
    (fun g x => by simp only [smul_eq_mul, mul_assoc]) (fun g x => rfl) hcomp
    (fun n F x => rfl) n
  rw [key, Cx.Hom.id_H]

end ReciprocityTheory.Coh
end

section -- merged from ReciprocityTheory.GroupCohomology.IsLowExists
namespace ReciprocityTheory.Coh

universe u

theorem exists_isLow {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (M : TRep R G) : ∃ e₀ e₁ e₂, IsLow M e₀ e₁ e₂ := by
  obtain ⟨-, ⟨e₀, h₀⟩, ⟨e₁, h₁⟩, e₂, h₂⟩ := low_holds R G M
  exact ⟨e₀, e₁, e₂, h₀, h₁, h₂⟩

end ReciprocityTheory.Coh
end

section -- merged from ReciprocityTheory.GroupCohomology.LowNat
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx

universe u

theorem lowNat_holds : LowNatStatement.{u} := by
  intro R _ G _ _ _ G' _ _ _ M M' P e₀ e₁ e₂ e₀' e₁' e₂' hL hL'
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    apply Subtype.ext
    have hw : M'.coch.d 0 (P.hom.Z 0 ⟨c, hc⟩).1 = 0 := (P.hom.Z 0 ⟨c, hc⟩).2
    have hc' : M.coch.d 0 c = 0 := hc
    change (e₀' (M'.coch.cls 0 (P.hom.Z 0 ⟨c, hc⟩).1 hw) : M'.V) =
      P.u (e₀ (M.coch.cls 0 c hc'))
    have h1 := hL'.1 (P.hom.Z 0 ⟨c, hc⟩).1 hw
    have h2 := hL.1 c hc'
    rw [h1, h2]
    show P.u (c.1 fun i => P.φ (![] i)) = P.u (c.1 ![])
    rw [show (fun i => P.φ (![] i)) = (![] : Fin 0 → G) from funext fun i => i.elim0]
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨hz, he⟩ := hL.2.1 c hc
    have hw : M'.coch.d 1 (P.hom.Z 1 ⟨c, hc⟩).1 = 0 := (P.hom.Z 1 ⟨c, hc⟩).2
    obtain ⟨hz', he'⟩ := hL'.2.1 (P.hom.Z 1 ⟨c, hc⟩).1 hw
    change e₁' (M'.coch.cls 1 (P.hom.Z 1 ⟨c, hc⟩).1 hw) =
      P.h1 (e₁ (M.coch.cls 1 c hc))
    rw [he', he]
    unfold Pair.h1 pairH1DecompositionMap
    rw [Submodule.mapQ_apply]
    congr 1
    apply Subtype.ext
    funext g
    show P.u (c.1 fun i => P.φ (![g] i)) = P.u (c.1 ![P.φ g])
    rw [show (fun i => P.φ (![g] i)) = ![P.φ g] from by funext i; fin_cases i; rfl]
  · intro x
    obtain ⟨⟨c, hc⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨hz, he⟩ := hL.2.2 c hc
    have hw : M'.coch.d 2 (P.hom.Z 2 ⟨c, hc⟩).1 = 0 := (P.hom.Z 2 ⟨c, hc⟩).2
    obtain ⟨hz', he'⟩ := hL'.2.2 (P.hom.Z 2 ⟨c, hc⟩).1 hw
    change e₂' (M'.coch.cls 2 (P.hom.Z 2 ⟨c, hc⟩).1 hw) =
      P.h2 (e₂ (M.coch.cls 2 c hc))
    rw [he', he]
    unfold Pair.h2 compatiblePairH2
    rw [Submodule.mapQ_apply]
    congr 1
    apply Subtype.ext
    funext g
    show P.u (c.1 fun i => P.φ (![g.1, g.2] i)) = P.u (c.1 ![P.φ g.1, P.φ g.2])
    rw [show (fun i => P.φ (![g.1, g.2] i)) = ![P.φ g.1, P.φ g.2] from by
      funext i; fin_cases i <;> rfl]

end ReciprocityTheory.Coh
end
