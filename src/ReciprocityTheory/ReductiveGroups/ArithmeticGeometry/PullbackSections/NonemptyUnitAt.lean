module

public import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.ScaledBoundInequality

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

structure UnfAt (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) where
  g : ℕ
  e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)
  F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)
  ik : U.Comp → Fin F.n
  φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ
  isom : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) =
    Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))
  Pm : (F.Di (ik k)).La →+ (Fin g → ℂ)
  pm_eq : ∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2
  per : IsPeriod (F.Di (ik k)) (fun j => relab c σ (e j).1) Pm
  pt : (U.un k x).x = F.u (ik k) Pm
  der : ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
    ((U.un k x).u τ i)
  unit : ((∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1) →
          ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ)
            (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)),
            Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
            (∀ a b, (hermForm Hm (Pm a) (Pm b)).im = (F.Di (ik k)).EF a b) ∧
            (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
            (∀ j z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) ∧
            (∀ j j' z, ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
              fr j z = valAt' (F.ex (ik k) Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
                (Xo.univ.t.PP.L.g j j').val * fr j' z) ∧
            (∀ j, ⊤ ≤ (F.ex (ik k) Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
                (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
            (∀ a j z, ‖χl (Pm a)‖ = 1 ∧ (⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              fr j z = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) +
                Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * fr j (z + Pm a))) ∧
            (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
              pt ≫ gxFst (U.un k x).x = (F.ex (ik k) Pm z).left →
              pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
              ⊤ ≤ (F.ex (ik k) Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
              valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z) ∧
            MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume ∧
            (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
              (MeasureTheory.volume Fd).toReal = 1)

theorem nonempty_unfAt {U : Unf Xo c σ r} (h : IsUnf U) (k : U.Comp) (x : (U.X k).dom) :
    Nonempty (UnfAt U k x) := by
  obtain ⟨_, _, _, _, _, g, e, F, ik, φ, hiso, hpt⟩ := h
  obtain ⟨Pm, h1, h2, h3, h4, h5⟩ := hpt k x
  exact ⟨⟨g, e, F, ik, φ, hiso, Pm, h1, h2, h3, h4, h5⟩⟩

structure UnitAt {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) where
  Hm : Matrix (Fin W.g) (Fin W.g) ℂ
  χl : (Fin W.g → ℂ) → ℂ
  fr : Xo.univ.t.PP.L.ι → (Fin W.g → ℂ) → ℂ
  θ : (Fin W.g → ℂ) → ℂ
  Fd : Set (Fin W.g → ℂ)
  herm : Hm.IsHermitian
  pos : ∀ z : Fin W.g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re
  c1 : (∀ a b, (hermForm Hm (W.Pm a) (W.Pm b)).im = (W.F.Di (W.ik k)).EF a b)
  c2 : (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j})
  c3 : (∀ j z, ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0)
  c4 : (∀ j j' z, ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (W.F.ex (W.ik k) W.Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j')
      (Xo.univ.t.PP.L.g j j').val * fr j' z)
  c5 : (∀ j, ⊤ ≤ (W.F.ex (W.ik k) W.Pm 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' (U.un k x).x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j))
      (Xo.univ.t.PP.rig.s (fun _ => j)).val)
  c6 : (∀ a j z, ‖χl (W.Pm a)‖ = 1 ∧ (⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl (W.Pm a) * Complex.exp (Real.pi * hermForm Hm z (W.Pm a) +
      Real.pi / 2 * hermForm Hm (W.Pm a) (W.Pm a)) * fr j (z + W.Pm a)))
  c7 : (∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
      pt ≫ gxFst (U.un k x).x = (W.F.ex (W.ik k) W.Pm z).left →
      pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (U.un k x).x).U (fun _ => j)) ((U.un k x).s.f (fun _ => j)) = θ z * fr j z)
  c8 : MeasureTheory.IsAddFundamentalDomain W.Pm.range Fd MeasureTheory.volume
  c9 : (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) /
      (MeasureTheory.volume Fd).toReal = 1

theorem nonempty_unitAt {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x)
    (hu : ∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1) : Nonempty (UnitAt W) := by
  obtain ⟨Hm, χl, fr, θ, Fd, h0, h0', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := W.unit hu
  exact ⟨⟨Hm, χl, fr, θ, Fd, h0, h0', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLam
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.TB

theorem latOfLam : LatOfLamSt := by
  intro D B P j X S ka wL wF large₂ C A hg hs hlam hspan hH2
  let Nf : NormFam B.KO (B.Cusp j ka) :=
    { N := B.supN j ka
      nonneg := B.supN_nonneg j ka
      eq_zero := fun σ v h => (B.supN_eq_zero j ka σ v).mp h
      smul := B.supN_smul j ka
      add := B.supN_add j ka }
  have hPL : ProdLower Nf (B.Mlat j ka)
      ((Fintype.card (B.KO →+* ℂ) : ℝ) * (WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size)) := by
    intro f hf hne
    have h1 := hlam f hf hne
    unfold WeightFamilies.meanLogSup at h1
    by_cases hc : (Fintype.card (B.KO →+* ℂ) : ℝ) = 0
    · have hc' : Fintype.card (B.KO →+* ℂ) = 0 := by exact_mod_cast hc
      have hempty : IsEmpty (B.KO →+* ℂ) := Fintype.card_eq_zero_iff.mp hc'
      rw [hc, zero_mul, neg_zero]
      simp
    · have hpos : (0 : ℝ) < Fintype.card (B.KO →+* ℂ) :=
        lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hc)
      have h2 := (le_div_iff₀ hpos).mp h1
      show -((Fintype.card (B.KO →+* ℂ) : ℝ) * _) ≤ ∑ σ : B.KO →+* ℂ, Real.log (B.supN j ka σ f)
      linarith
  have hUD := discriminant_of_product_lower B.KO (B.Cusp j ka) Nf (B.Mlat j ka) _ hPL
  have hFG := formalGroup_of_discriminant B.KO (B.Cusp j ka) Nf (B.Mlat j ka) hUD
  exact Submodule.IsLattice.of_fg B.KO hFG

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanGlue
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

section Abstract

variable {K : Type*} [Field K] {σ : K →+* ℂ} {C : Type*} [AddCommGroup C] [Module K C]
  {W : Type*} [AddCommGroup W] [Module ℂ W]

def IndepToC (j : C →ₛₗ[σ] W) : Prop :=
  ∀ (n : ℕ) (b : Fin n → C), LinearIndependent K b → LinearIndependent ℂ (fun i => j (b i))

theorem map_mem_span_of_mem_span (j : C →ₛₗ[σ] W) (T : Set C) {x : C}
    (hx : x ∈ Submodule.span K T) : j x ∈ Submodule.span ℂ (j '' T) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simp
  | add y w _ _ hy hw => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hw
  | smul a y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy

theorem span_eq_top_of_indepToC (j : C →ₛₗ[σ] W) (hj : IndepToC j) (S : Set C)
    (hS : ∀ f, j f ∈ Submodule.span ℂ (j '' S)) : Submodule.span K S = ⊤ := by
  classical
  rw [eq_top_iff]
  intro f _
  by_contra hf
  obtain ⟨T, hTS, hfT⟩ := Submodule.mem_span_finite_of_mem_span (hS f)
  obtain ⟨T', hT'S, rfl⟩ := Finset.subset_set_image_iff.mp hTS
  obtain ⟨b, hbT, hspan, hli⟩ := exists_linearIndependent K (T' : Set C)
  have hbfin : b.Finite := (T'.finite_toSet).subset hbT

  have hjf : j f ∈ Submodule.span ℂ (j '' b) := by
    have hle : Submodule.span ℂ ((T'.image j : Finset W) : Set W) ≤ Submodule.span ℂ (j '' b) := by
      rw [Submodule.span_le]
      intro y hy
      rw [Finset.coe_image] at hy
      obtain ⟨t, ht, rfl⟩ := hy
      apply map_mem_span_of_mem_span
      rw [hspan]
      exact Submodule.subset_span ht
    exact hle hfT

  have hfb : f ∉ Submodule.span K b := by
    intro h
    apply hf
    rw [hspan] at h
    exact Submodule.span_mono hT'S h
  have hli' : LinearIndependent K (fun y : ↥(insert f b) => (y : C)) :=
    LinearIndepOn.insert (v := id) (s := b) (x := f) hli (by simpa using hfb)
  have hfin : (insert f b).Finite := hbfin.insert f
  haveI := hfin.fintype
  let e := Fintype.equivFin ↥(insert f b)
  have hC := hj _ (fun i => ((e.symm i : ↥(insert f b)) : C)) (hli'.comp _ e.symm.injective)
  have hC' : LinearIndependent ℂ (fun y : ↥(insert f b) => j (y : C)) := by
    have := hC.comp _ e.injective
    simpa [Function.comp_def] using this
  have hnot := hC'.notMem_span_image (s := {y : ↥(insert f b) | (y : C) ∈ b})
    (x := ⟨f, Set.mem_insert f b⟩) (by
      intro hx
      exact hfb (Submodule.subset_span hx))
  apply hnot
  convert hjf using 2
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, Set.mem_insert_of_mem f hz⟩, hz, rfl⟩

end Abstract

theorem spanAt_of_chain {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (ka : WeightFamilies.Wt D j) {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : B.KO →+* ℂ}
    (J : B.Cusp j ka →ₛₗ[σ] W) (hJ : IndepToC J) (Sp : Submodule ℂ W) (A : Set W)
    (hmem : ∀ f, J f ∈ Sp) (hsp : Sp ≤ Submodule.span ℂ A)
    (hA : A ⊆ Submodule.span ℂ (J '' ((X.shortTh ka : Submodule (𝓞 B.KO) (B.Cusp j ka)) : Set (B.Cusp j ka)))) :
    SpanAt X ka := by
  unfold SpanAt
  apply span_eq_top_of_indepToC J hJ
  intro f
  have h1 : Submodule.span ℂ A ≤
      Submodule.span ℂ (J '' ((X.shortTh ka : Submodule (𝓞 B.KO) (B.Cusp j ka)) : Set (B.Cusp j ka))) := by
    rw [Submodule.span_le]
    exact hA
  exact h1 (hsp (hmem f))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
