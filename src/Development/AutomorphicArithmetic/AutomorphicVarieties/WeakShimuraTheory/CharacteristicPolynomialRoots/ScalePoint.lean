module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LevFin

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.ScalePoint
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem scale_point {A B K : Type} [CommRing A] [CommRing B] [Field K] {n : ℕ} (i : B →+* A)
    (hi : Function.Injective i) (y : A →+* K) (p : B[X]) (M : Matrix (Fin n) (Fin n) A) (hp : p.map i = M.charpoly)
    (b : B) : (p.scaleRoots b).map (y.comp i) = (M.map y).charpoly.scaleRoots (y (i b)) := by
  have h1 : i p.leadingCoeff = 1 := by
    rw [← leadingCoeff_map_of_injective hi, hp, (Matrix.charpoly_monic M).leadingCoeff]
  rw [map_scaleRoots _ _ _ (by simp [h1]), ← Polynomial.map_map, hp, Matrix.charpoly_map]
  rfl

theorem UpperTheory.V.Ws.Pu.ptCp :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (φ : B.B →ₐ[c'.O] X.B) (y : X.A →ₐ[c'.O] PadicAlgCl l) (ρ : G T.L Ω →* GL (Fin 4) (PadicAlgCl l)), K.IsPhi X 0 B φ → (Link.pt φ y).IsRep ρ →
      ∀ g, (W.mat ρ g).charpoly = ((X.P.map (y : X.A →+* PadicAlgCl l)).r (resLe T.F_le g)).charpoly.scaleRoots (K.kapQ g : PadicAlgCl l) := by
  intro Ω _ _ _ l _ c D T c' h K X B φ y ρ hφ hρ g
  have hxe : (Link.pt φ y : B.B →+* PadicAlgCl l) =
      ((y : X.A →+* PadicAlgCl l).comp (algebraMap X.B X.A)).comp (φ : B.B →+* X.B) :=
    RingHom.ext fun b => Link.pt_apply K φ y b
  have hs : (y : X.A →+* PadicAlgCl l) (algebraMap X.B X.A (algebraMap c'.O X.B (K.κ g * K.β g ^ 0))) =
      (K.kapQ g : PadicAlgCl l) := by
    rw [← IsScalarTower.algebraMap_apply, pow_zero, mul_one]
    exact y.commutes _
  rw [UpperTheory.V.Ws.Pu.repChi K.V B _ ρ hρ g, hxe, ← Polynomial.map_map]
  refine (congrArg (Polynomial.map _) (hφ.1 g)).trans ?_
  rw [scale_point _ X.inj _ _ _ (X.cp_map _), hs]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.RepKill
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem trace_eq_of_charpoly {K : Type} [Field K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (h : A.charpoly = B.charpoly) : A.trace = B.trace := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Matrix.trace]
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, h]

private theorem kill_of_charpoly {Γ K : Type} [Group Γ] [Field K] [CharZero K] {n : ℕ}
    (ρ : Γ →* GL (Fin n) K) (hss : IsSSRep ρ) (g : Γ)
    (h : ∀ k, ((ρ (g * k) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly =
      ((ρ k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly) : ρ g = 1 := by
  have hx := GlobalTheory.isSSRep_trace_nondegenerate Γ K n ρ hss ((ρ g : Matrix (Fin n) (Fin n) K) - 1)
    (Submodule.sub_mem _ (Submodule.subset_span ⟨g, rfl⟩) (Submodule.subset_span ⟨1, by simp⟩))
    (fun k => by
      rw [sub_mul, one_mul, Matrix.trace_sub, ← Units.val_mul, ← map_mul,
        trace_eq_of_charpoly (h k), sub_self])
  exact Units.ext (by simpa using sub_eq_zero.mp hx)

theorem UpperTheory.V.Ws.Pu.repKill :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)), x.IsRep ρ → IsSSRep ρ → ∀ g, V.pr g = 1 → ρ g = 1 := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hx hss g hg
  refine kill_of_charpoly ρ hss g fun k => ?_
  have h1 := UpperTheory.V.Ws.Pu.repChi V B x ρ hx (g * k)
  have h2 := UpperTheory.V.Ws.Pu.repChi V B x ρ hx k
  rw [map_mul V.pr, hg, one_mul] at h1
  exact h1.trans h2.symm
end
