module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusPin

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.TorusMatchPf
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem hermC_mulVec (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) (y v : Fin r → ℂ) :
    hermC τ G (x.mulVec y) v = ∑ a, y a * hermC τ G (col x a) v := by
  simp only [hermC, Matrix.mulVec, dotProduct, col, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
  ring

variable (X : Data E r) (x : Frame X.Ψ r)

end Frame

section Torus

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r} {x : Frame X.Ψ r}

end Torus

section Relab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ)

theorem relab_rt (hσ : GoodEmb c σ) (τ' : E →+* ℂ) :
    relab c σ τ' (H.rt : E) = H.rt0 ↔ τ' (H.rt : E) = H.rt0 := by
  have h0 : H.rt0 ≠ 0 := by
    intro h
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    have hd : (H.d : ℂ) = 0 := by linear_combination this
    exact H.d_prime.ne_zero (by exact_mod_cast hd)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hsq : (τ' (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE, map_neg, map_natCast]
  have hval : relab c σ τ' (H.rt : E) = σ ⟨τ' (H.rt : E), c.conj τ' _⟩ := rfl
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hx | hx
  · refine ⟨fun _ => hx, fun _ => ?_⟩
    rw [hval, ← hσ0]
    exact congrArg σ (Subtype.ext hx)
  · have h1 : σ ⟨τ' (H.rt : E), c.conj τ' _⟩ = -σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ := by
      rw [← map_neg]
      exact congrArg σ (Subtype.ext hx)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exfalso
      rw [← hval, h, hσ0] at h1
      exact h0 (by linear_combination h1 / 2)
    · exfalso
      exact h0 (by linear_combination (h.symm.trans hx) / 2)

theorem conjEmb_conjEmb (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ :=
  RingHom.ext fun a => Complex.conj_conj _

theorem conjugate_eq (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ = conjEmb τ := rfl

end Relab

section Letters

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

theorem conj_mem_iff {X : Data E r} (ρ : E →+* ℂ) : conjEmb ρ ∈ X.Ψ ↔ ρ ∉ X.Ψ := by
  have := X.cmType (conjEmb ρ)
  rw [conjugate_eq, conjEmb_conjEmb] at this
  exact this

include hU in
theorem dim_of (ρ : E →+* ℂ) :
    A.T.dim ρ = if ρ ∈ (U.X k).Ψ then (U.X k).p0 else r - (U.X k).p0 := by
  split_ifs with h
  · exact A.dim_pos ⟨ρ, h⟩
  · have hc : conjEmb ρ ∈ (U.X k).Ψ := (conj_mem_iff ρ).mpr h
    have := A.dim_neg ⟨conjEmb ρ, hc⟩
    rwa [conjugate_eq, conjEmb_conjEmb] at this





end Letters

section Map

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

def yf (τ : (U.X k).Ψ) (b : Fin r) : ℂ :=
  (sgn (U.X k).p0 b : ℂ) * hermC τ.1 (U.X k).Gm (A.e τ b) (col (mat x.1 τ) b)

include hU in
theorem index_lt_signature_of_mem {ρ : E →+* ℂ} (h : ρ ∈ (U.X k).Ψ) (a : Fin (A.T.dim ρ)) : (a : ℕ) < (U.X k).p0 := by
  have h1 := dim_of hU A ρ
  rw [if_pos h] at h1
  have := a.2
  omega

include hU in
theorem index_lt_complementSignature_of_not_mem {ρ : E →+* ℂ} (h : ρ ∉ (U.X k).Ψ) (a : Fin (A.T.dim ρ)) : (a : ℕ) < r - (U.X k).p0 := by
  have h1 := dim_of hU A ρ
  rw [if_neg h] at h1
  have := a.2
  omega


include hU in
def wt (i : ReciprocityTheory.ChartRestriction.G.I2.Idx A.T.dim) : ℂ :=
  if h : i.1 ∈ (U.X k).Ψ then
    (Real.sqrt ((U.X k).c ⟨i.1, h⟩) : ℂ) *
      conj (yf A ⟨i.1, h⟩ ⟨i.2, lt_of_lt_of_le (index_lt_signature_of_mem hU A h i.2) (U.X k).p0_le⟩)
  else
    (Real.sqrt ((U.X k).c ⟨conjEmb i.1, (conj_mem_iff _).mpr h⟩) : ℂ) *
      yf A ⟨conjEmb i.1, (conj_mem_iff _).mpr h⟩
        ⟨(U.X k).p0 + i.2, by have := index_lt_complementSignature_of_not_mem hU A h i.2; have := (U.X k).p0_le; omega⟩


end Map

section Pin1

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

end Pin1

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Complex
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi MonObj
open scoped ComplexConjugate CategoryTheory.Obj

section Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x)

theorem ex_periodic (a : (W.F.Di (W.ik k)).La) (z : Fin W.g → ℂ) :
    W.F.ex (W.ik k) W.Pm (z + W.Pm a) = W.F.ex (W.ik k) W.Pm z := by
  rw [W.F.ex_add _ _ W.per, (W.F.ex_ker _ _ W.per _).mpr ⟨a, rfl⟩, _root_.mul_one]

theorem primeSpectrum_eq (p q : PrimeSpectrum ℂ) : p = q := by
  first
  | exact Subsingleton.elim p q
  | exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime _).trans (Ideal.eq_bot_of_prime _).symm)

theorem exists_chart_pt {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) : ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  let p0 : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hmem : y p0 ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨j, fun q _ => ?_⟩
  have : q = p0 := primeSpectrum_eq q p0
  rw [this]
  exact hj

theorem exists_gx_pt (z : Fin W.g → ℂ) : ∃ pt : Sp ℂ ⟶ Gx (U.un k x).x,
    pt ≫ gxFst (U.un k x).x = (W.F.ex (W.ik k) W.Pm z).left ∧ pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) := by
  let b : Over.mk (U.un k x).x ⟶ Xo.univ.t.G :=
    Over.homMk (W.F.ex (W.ik k) W.Pm z).left ((Over.w (W.F.ex (W.ik k) W.Pm z)).trans W.pt.symm)
  refine ⟨(CartesianMonoidalCategory.lift (𝟙 (Over.mk (U.un k x).x)) b).left, ?_, ?_⟩
  · exact (Over.comp_left _ _ _ _ _).symm.trans
      (congrArg (fun q => Over.Hom.left q) (CartesianMonoidalCategory.lift_snd _ _))
  · exact (Over.comp_left _ _ _ _ _).symm.trans
      (congrArg (fun q => Over.Hom.left q) (CartesianMonoidalCategory.lift_fst _ _))

theorem theta_add (Wu : UnitAt W) (a : (W.F.Di (W.ik k)).La) (z : Fin W.g → ℂ) :
    Wu.θ (z + W.Pm a) = Wu.χl (W.Pm a) * cexp (Real.pi * hermForm Wu.Hm z (W.Pm a) +
      Real.pi / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a)) * Wu.θ z := by
  obtain ⟨j, hj⟩ := exists_chart_pt Xo.univ.t.PP.L Xo.univ.t.PP.isLB (W.F.ex (W.ik k) W.Pm z).left
  obtain ⟨pt, h1, h2⟩ := exists_gx_pt W z
  have hj' : ⊤ ≤ (W.F.ex (W.ik k) W.Pm (z + W.Pm a)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
    rw [ex_periodic]
    exact hj
  have e1 := Wu.c7 j z pt h1 h2 hj
  have e2 := Wu.c7 j (z + W.Pm a) pt (by rw [ex_periodic]; exact h1) h2 hj'
  have e3 := (Wu.c6 a j z).2 hj
  have hne := Wu.c3 j (z + W.Pm a) hj'
  have key : Wu.θ (z + W.Pm a) * Wu.fr j (z + W.Pm a) =
      (Wu.χl (W.Pm a) * cexp (Real.pi * hermForm Wu.Hm z (W.Pm a) +
        Real.pi / 2 * hermForm Wu.Hm (W.Pm a) (W.Pm a)) * Wu.θ z) * Wu.fr j (z + W.Pm a) := by
    rw [← e2, e1, e3]
    ring
  exact mul_right_cancel₀ hne key

end Theta

section Sec

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
  {U : Unf Xo c σ r} (hU : IsUnf U) (hσ : GoodEmb c σ) {k : U.Comp} {x : (U.X k).dom}
  (W : UnfAt U k x) (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1)

end Sec

end ReciprocityTheory.ChartRestriction.G.PullbackSections
