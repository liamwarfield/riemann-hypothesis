module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe28.FDSec
    {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r) : Type :=
  (c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Frame (X c).Ψ r → ℂ

noncomputable def UpperTheory.Reformulated.B.Qe28.IsHolCusp :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : NumberField E] →
          [inst_2 : NumberField.IsCMField E] →
            {r : ℕ} →
              {Comp : Type} →
                (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r) →
                  ((c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r) →
                    UpperTheory.Reformulated.B.Qe28.FDSec X → Prop :=
    fun {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} {Comp : Type}
        (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r)
        (la : (c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r)
        (P : UpperTheory.Reformulated.B.Qe28.FDSec X) ↦
      ∀ (c : Comp), P c ∈ (X c).SS (la c)

noncomputable def UpperTheory.Reformulated.B.Qe28.holSub :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : NumberField E] →
          [inst_2 : NumberField.IsCMField E] →
            {r : ℕ} →
              {Comp : Type} →
                (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r) →
                  ((c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r) →
                    Submodule ℂ (UpperTheory.Reformulated.B.Qe28.FDSec X) :=
    fun {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ} {Comp : Type}
        (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r)
        (la : (c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r) ↦
      Submodule.span ℂ
        {P : UpperTheory.Reformulated.B.Qe28.FDSec X | UpperTheory.Reformulated.B.Qe28.IsHolCusp X la P}

theorem UpperTheory.Reformulated.B.Qe28.holSub_mul :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {r : ℕ},
      ReciprocityTheory.ChartRestriction.G.FD.SiegelSpaceAlgebra (E := E) →
        ∀ {Comp : Type} {X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r}
          {la la' : (k : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r}
          {P Q : UpperTheory.Reformulated.B.Qe28.FDSec X},
          P ∈ UpperTheory.Reformulated.B.Qe28.holSub X la →
            Q ∈ UpperTheory.Reformulated.B.Qe28.holSub X la' →
              P * Q ∈ UpperTheory.Reformulated.B.Qe28.holSub X (la + la') := by
  intro E _ _ _ r h5 Comp X la la' P Q hP hQ
  have key : ∀ (l : (k : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (R : UpperTheory.Reformulated.B.Qe28.FDSec X),
      R ∈ UpperTheory.Reformulated.B.Qe28.holSub X l → UpperTheory.Reformulated.B.Qe28.IsHolCusp X l R := by
    intro l R hR
    induction hR using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact fun c => (h5 r (X c) (l c) (l c) 0).1.1
    | add x y _ _ hx hy => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.1 _ (hx c) _ (hy c)
    | smul a x _ hx => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.2 a _ (hx c)
  exact Submodule.subset_span fun c =>
    (h5 r (X c) (la c) (la' c) 0).2.1 _ (key la P hP c) _ (key la' Q hQ c).1
