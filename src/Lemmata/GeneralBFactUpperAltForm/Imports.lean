module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_upper_alt_form

theorem goal1 :
    ∀ {K : Type} [inst : Field K] {n k : Type} [Fintype n] [DecidableEq n] [inst_3 : Fintype k]
      [DecidableEq k] (f : K →+* ℂ) (A : Matrix n k K),
      Function.Injective A.mulVec → Function.Injective (A.map ⇑f).mulVec := by
  intro K _ n k _ _ _ _ f A hA
  have hker : LinearMap.ker (Matrix.toLin' A) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (fun x y hxy => hA (by simpa only [Matrix.toLin'_apply] using hxy))
  obtain ⟨g, hg⟩ := (Matrix.toLin' A).exists_leftInverse_of_injective hker
  have hBA : LinearMap.toMatrix' g * A = 1 := by
    have h := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h
  have h1 : (LinearMap.toMatrix' g).map f * A.map f = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ f.map_zero f.map_one]
  intro v w hvw
  have h2 := congrArg (fun u => Matrix.mulVec ((LinearMap.toMatrix' g).map f) u) hvw
  simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using h2

end Bl.general_b_fact_upper_alt_form
