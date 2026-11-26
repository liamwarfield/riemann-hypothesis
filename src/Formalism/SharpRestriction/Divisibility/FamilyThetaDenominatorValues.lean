module

public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.CartierLocalBounds
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.MainNotions.CartierLocalBounds

open Formalism.BasicNotions

def rho (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 1)

def expE (l i : ℕ) : ℕ := 1 + l * ∑ t ∈ Finset.range ((i - 1) / 2), (l ^ 2) ^ t

def rad1 (l i : ℕ) : ℝ := rho l + ((l : ℝ) ^ i)⁻¹ / 2

def rad2 (l : ℕ) : ℝ := rho l + 1 / 2

def dlt (l i : ℕ) : ℝ := ((l : ℝ) ^ i)⁻¹ / 8

def vLe {l : ℕ} [Fact l.Prime] (x : ℂ_[l]) (b : ℝ) : Prop := (l : ℝ) ^ (-b) ≤ ‖x‖

def vGe {l : ℕ} [Fact l.Prime] (x : ℂ_[l]) (b : ℝ) : Prop := ‖x‖ ≤ (l : ℝ) ^ (-b)

section Jets

variable {C : Type} [Field C]

abbrev PVar (n0 : ℕ) := (Fin n0 × Fin n0) ⊕ (Fin n0 × Fin n0)

def mvExp {σ : Type} (h : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun m => ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (h ^ k) / (k.factorial : C)

def dL {ι ι' : Type} [Fintype ι] (μ : (ι ⊕ ι') →₀ ℕ) : ℕ := ∑ c : ι, μ (Sum.inl c)

def dR {ι ι' : Type} [Fintype ι'] (μ : (ι ⊕ ι') →₀ ℕ) : ℕ := ∑ b : ι', μ (Sum.inr b)

end Jets

def WeightGe {l : ℕ} [Fact l.Prime] (i : ℕ) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (h1 : MvPowerSeries (ι ⊕ ι') ℂ_[l]) : Prop :=
  ∀ μ, vGe (MvPowerSeries.coeff μ h1)
    (1 / ((l : ℝ) - 1) - ((dL μ : ℝ) * (rad1 l i - dlt l i) + (dR μ : ℝ) * (rad2 l - dlt l i)))

def hP (l : ℕ) [Fact l.Prime] (i n0 : ℕ) (h1 : MvPowerSeries (PVar n0) ℂ_[l]) :
    MvPowerSeries (PVar n0) ℂ_[l] :=
  -(((l : ℂ_[l]) ^ expE l i)⁻¹) • (∑ b : Fin n0, ∑ c : Fin n0,
      MvPowerSeries.X (Sum.inl (b, c)) ^ (l ^ i) * MvPowerSeries.X (Sum.inr (b, c))) + h1

structure LocD (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d] where

  five_le_l : 5 ≤ l

  d_even : Even d

  r : ℕ
  j : ℕ
  j' : ℕ
  rh : ℕ
  rh_le : rh ≤ j'

  rh_le_big : rh + j' ≤ r
  jj_le : j + j' ≤ r

  big : Fin 2 → ZMod d → Prop

  rk : Fin 2 → ZMod d → ℕ
  rk_big : ∀ g a, big g a → rk g a = r - j'
  rk_small : ∀ g a, ¬ big g a → rk g a = j'

  U : ∀ g a, Submodule 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])
  U_summand : ∀ g a, big g a → ∃ Q : Submodule 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l]), IsCompl (U g a) Q
  U_basis : ∀ g a, big g a → Nonempty (Module.Basis (Fin (r - j' - j)) 𝓞_ℂ_[l] (U g a))

  Chart : Type

  tan : Chart → ∀ g a, Module.Basis (Fin (rk g a)) 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])

  chart_tan : ∀ b : (∀ g a, Module.Basis (Fin (rk g a)) 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])),
    ∃ χ : Chart, tan χ = b

  alC : Chart → ∀ (g : Fin 2) (b : ZMod d), Fin (rk g b) → ℕ → ∀ a : ZMod d, Fin (rk g a) → ℂ_[l]
  alC_type : ∀ χ g b c (s : ℕ) a, a ≠ b + (s : ZMod d) → alC χ g b c s a = 0

  alC_zero : ∀ χ g b c k, alC χ g b c 0 b k = ((tan χ g b c k : 𝓞_ℂ_[l]) : ℂ_[l])

  beP : Chart → ∀ (g : Fin 2) (b : ZMod d), Fin (rk g b) → ℕ → ∀ a : ZMod d, Fin (rk (1 - g) a) → ℂ_[l]
  beP_type : ∀ χ g b c (s : ℕ) a, a ≠ b + (s : ZMod d) → beP χ g b c s a = 0

  beP_zero : ∀ χ g b c a, beP χ g b c 0 a = 0

  chart_mod : ∀ (χ : Chart)
    (x : ∀ g : Fin 2, ℕ → (Σ b : ZMod d, Fin (rk g b)) → (Σ b : ZMod d, Fin (rk g b)) → 𝓞_ℂ_[l]),
    (∀ g (s : ℕ) c b, b.1 ≠ c.1 + (s : ZMod d) → x g s c b = 0) →
    (∀ g, IsUnit (Matrix.of (x g 0)).det) →
    ∃ χ' : Chart,
      (∀ g (c : Σ b : ZMod d, Fin (rk g b)) (n : ℕ) a k, alC χ' g c.1 c.2 n a k =
        ∑ s ∈ Finset.range (n + 1), ∑ b : (Σ b : ZMod d, Fin (rk g b)),
          ((x g s c b : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (n - s)) * alC χ g b.1 b.2 (n - s) a k) ∧
      (∀ g (c : Σ b : ZMod d, Fin (rk g b)) (n : ℕ) a k, beP χ' g c.1 c.2 n a k =
        ∑ s ∈ Finset.range (n + 1), ∑ b : (Σ b : ZMod d, Fin (rk g b)),
          ((x g s c b : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (n - s)) * beP χ g b.1 b.2 (n - s) a k)

  tL : Chart → ∀ (g : Fin 2) (a : ZMod d), (Σ b : ZMod d, Fin (rk g b)) → MvPowerSeries (Fin (rk g a)) ℂ_[l]
  tL_const : ∀ χ g a x, MvPowerSeries.constantCoeff (tL χ g a x) = 0

  tL_log_same : ∀ χ g a (k : Fin (rk g a)) (μ : Fin (rk g a) →₀ ℕ),
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ x : (Σ b : ZMod d, Fin (rk g b)),
      alC χ g x.1 x.2 s a k * MvPowerSeries.coeff μ (tL χ g a x ^ (l ^ s))) =
      if μ = Finsupp.single k 1 then 1 else 0

  tL_log_other : ∀ χ g a a' (k : Fin (rk g a')) (μ : Fin (rk g a) →₀ ℕ), a' ≠ a →
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ x : (Σ b : ZMod d, Fin (rk g b)),
      alC χ g x.1 x.2 s a' k * MvPowerSeries.coeff μ (tL χ g a x ^ (l ^ s))) = 0

  hL : ∀ (g : Fin 2) (a a' : ZMod d), MvPowerSeries (Fin (rk g a) ⊕ Fin (rk (1 - g) a')) ℂ_[l]

  Tt : Fin 2 → Type
  [instTt : ∀ g, AddCommGroup (Tt g)]
  [modTt : ∀ g, Module ℤ_[l] (Tt g)]
  Tt_free : ∀ g, Module.Free ℤ_[l] (Tt g)
  Tt_rank : ∀ g, Module.finrank ℤ_[l] (Tt g) = d * (r - rh)

  alHT : ∀ g, Tt g → ∀ a, (Fin (rk g a) → 𝓞_ℂ_[l]) →ₗ[𝓞_ℂ_[l]] 𝓞_ℂ_[l]

  chiG : Chart → ∀ g, Tt g → MvPowerSeries (Σ b : ZMod d, Fin (rk g b)) 𝓞_ℂ_[l]

  chiG_leaf : ∀ χ g (t : Tt g) a,
    MvPowerSeries.subst (fun x => tL χ g a x)
        (MvPowerSeries.map (algebraMap 𝓞_ℂ_[l] ℂ_[l]) (chiG χ g t)) =
      mvExp (∑ k : Fin (rk g a), ((alHT g t a (Pi.single k 1) : 𝓞_ℂ_[l]) : ℂ_[l]) •
        (MvPowerSeries.X k : MvPowerSeries (Fin (rk g a)) ℂ_[l]))

  ev : Chart → ∀ N : ℕ,
    MvPolynomial (Fin N × Σ g : Fin 2, Σ a : ZMod d, Fin (rk g a)) 𝓞_ℂ_[l] →
    MvPowerSeries (Fin N × Σ g : Fin 2, Σ b : ZMod d, Fin (rk g b)) 𝓞_ℂ_[l] → ℂ_[l]

attribute [instance] LocD.instTt LocD.modTt

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

def nn : ℕ := Λ.r - Λ.j' - Λ.j

def mm : ℕ := Λ.j + Λ.j'

def Alternating : Prop := ∀ a : ZMod d, (Λ.big 0 a ↔ Even a.val) ∧ (Λ.big 1 a ↔ ¬ Even a.val)

def bg (_Λ : LocD l d) (a : ZMod d) : Fin 2 := if Even a.val then 0 else 1

abbrev CoG (g : Fin 2) := Σ b : ZMod d, Fin (Λ.rk g b)

def zeP (χ : Λ.Chart) (g : Fin 2) (a a' : ZMod d) (b : Fin (Λ.rk (1 - g) a')) :
    MvPowerSeries (Fin (Λ.rk g a)) ℂ_[l] :=
  fun μ => -(∑ s ∈ Finset.range (μ.degree + 1), ∑ x : Λ.CoG g, ∑ k : Fin (Λ.rk (1 - g) a'),
    ((Λ.tan χ (1 - g) a' b k : 𝓞_ℂ_[l]) : ℂ_[l]) * Λ.beP χ g x.1 x.2 s a' k *
      MvPowerSeries.coeff μ (Λ.tL χ g a x ^ (l ^ s)))

end LocD

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

abbrev LV (N : ℕ) := Fin N × Σ g : Fin 2, Σ a : ZMod d, Fin (Λ.rk g a)

abbrev CV (N : ℕ) := Fin N × Σ g : Fin 2, Λ.CoG g

def detBlock (N : ℕ) (a : ZMod d) (S : Fin Λ.nn ↪ Fin N)
    (bas : Fin Λ.nn → Fin (Λ.rk (Λ.bg a) a) → 𝓞_ℂ_[l]) : MvPolynomial (Λ.LV N) 𝓞_ℂ_[l] :=
  Matrix.det (Matrix.of fun k c : Fin Λ.nn =>
    ∑ κ : Fin (Λ.rk (Λ.bg a) a), MvPolynomial.C (bas c κ) * MvPolynomial.X (S k, ⟨Λ.bg a, a, κ⟩))

def DetProd (N : ℕ) (W : ZMod d → ℕ) : Set (MvPolynomial (Λ.LV N) 𝓞_ℂ_[l]) :=
  {P | ∃ (B : ℕ) (blk : Fin B → ZMod d) (S : Fin B → (Fin Λ.nn ↪ Fin N)) (ex : Fin B → ℕ)
      (bas : ∀ a, Module.Basis (Fin Λ.nn) 𝓞_ℂ_[l] (Λ.U (Λ.bg a) a)),
    (∀ a, ∑ β ∈ Finset.univ.filter (fun β => blk β = a), ex β = W a) ∧
    (∀ β β', β ≠ β' → blk β = blk β' → Disjoint (Set.range (S β)) (Set.range (S β'))) ∧
    P = ∏ β, (Λ.detBlock N (blk β) (S β)
      (fun c => (bas (blk β) c : Fin (Λ.rk (Λ.bg (blk β)) (blk β)) → 𝓞_ℂ_[l]))) ^ (ex β)}

end LocD

def thl (l k : ℕ) : ℝ :=
  ((l : ℝ) ^ sInf {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i})⁻¹

def addl (C : ℝ) (l k n d : ℕ) (l1 : ℝ) : ℝ :=
  if (l : ℝ) < (k : ℝ) ^ ((1 : ℝ) / 2) then C * d * (n : ℝ) ^ 3 * (k : ℝ) ^ 3 * Real.log k
  else if (l : ℝ) < l1 then C * d * (n : ℝ) ^ 3 * l * Real.log ((n : ℝ) * l) else 0

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

def ContentAt (C : ℝ) : Prop :=
  Λ.Alternating → 0 < Λ.mm →
  ∀ (T Dp l1 : ℝ) (w : ZMod d → ℝ) (W : ZMod d → ℕ) (tha : ZMod d → ℝ),
    1 ≤ T → 1 ≤ Dp → Dp * ((Λ.nn : ℝ) + 1) / Λ.mm ≤ T → (Dp + 4) / T ≤ 1 / 2 →
    (∀ a, 0 < w a) → (∀ a, T * W a = w a * (1 - tha a)) →
    (∀ a, 0 ≤ tha a ∧ tha a ≤ (Dp + 4) / T) →
    ((Λ.nn : ℝ) + 1) ^ ((3 : ℝ) / 2) < l1 → 2 * (Λ.nn : ℝ) + 2 < l1 →
    ∃ N : ℕ, (N : ℝ) ≤ C * Λ.r * d * (1 + ((Finset.univ.sup W : ℕ) : ℝ) / l1 ^ 2) ∧
      ∃ P ∈ Λ.DetProd N W, ∃ (χ : Λ.Chart) (g : MvPowerSeries (Λ.CV N) 𝓞_ℂ_[l]),
        vLe (Λ.ev χ N P g)
          ((lpF l d (fun a => (Λ.nn : ℝ) * w a) +
            C * Real.log ((Λ.nn : ℝ) + 1) * Λ.mm * (∑ a, w a) / l +
            C * ((Λ.nn : ℝ) + 1) * thl l (Λ.nn + 1) * (∑ a, w a) +
            T * addl C l (Λ.nn + 1) Λ.nn d l1) / T)

def CartierFrobeniusFormLocal : Prop :=
  ∀ (χ : Λ.Chart) (g : Fin 2), ∃ (c : ℕ → Λ.CoG g → Λ.CoG g → 𝓞_ℂ_[l])
      (c' : ℕ → Λ.CoG g → ∀ a : ZMod d, Fin (Λ.rk (1 - g) a) → 𝓞_ℂ_[l]),
    ∀ (x : Λ.CoG g) (i : ℕ) (a : ZMod d),
      (∀ k, (l : ℂ_[l]) * Λ.alC χ g x.1 x.2 (i + 1) a k =
        ∑ s ∈ Finset.range (i + 1), ∑ y : Λ.CoG g,
          ((c s x y : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (i - s)) * Λ.alC χ g y.1 y.2 (i - s) a k) ∧
      (∀ k, (l : ℂ_[l]) * Λ.beP χ g x.1 x.2 (i + 1) a k =
        (∑ s ∈ Finset.range (i + 1), ∑ y : Λ.CoG g,
          ((c s x y : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (i - s)) * Λ.beP χ g y.1 y.2 (i - s) a k) +
          ((c' i x a k : 𝓞_ℂ_[l]) : ℂ_[l]))

def GoodC (χ : Λ.Chart) (g : Fin 2) (a : ZMod d) {N : ℕ} (e : Fin N ↪ Fin (Λ.rk g a)) : Prop :=
  ∀ c a'' k, Λ.alC χ g a (e c) 1 a'' k = 0

def RankOneLocalSpread : Prop :=
  ∀ (χ : Λ.Chart) (g : Fin 2) (a : ZMod d), Λ.big g a → Λ.big g (a + 2) →
    ∀ (N : ℕ) (e : Fin N ↪ Fin (Λ.rk g a)), Λ.GoodC χ g a e →
      ∃ (N' : ℕ) (ρ : Fin N' ↪ Fin N) (κ : Fin N' ↪ Fin (Λ.rk g (a + 2))), N ≤ N' + Λ.j' ∧
        ‖(Matrix.of fun s t : Fin N' =>
          (l : ℂ_[l]) * Λ.alC χ g a (e (ρ s)) 2 (a + 2) (κ t)).det‖ = 1

end LocD

def PtCl (D : Formalism.BasicNotions.D7) (Y : ModuliIntegralCharts.Prov D) (w : Y.Dat) (l : ℕ) [Fact l.Prime] : Type :=
  Σ y : (Y.loc w l).Pt (Y.loc w l).YY,
    {e : ((Y.loc w l).fld y).C ≃+* ℂ_[l] // ∀ x, ‖e x‖ = ‖x‖}

structure Loc (D : Formalism.BasicNotions.D7) (X : DivX D) (Y : ModuliIntegralCharts.Prov D) where

  dat : ℕ → Y.Dat
  dat_rk : ∀ j, 1 ≤ j → j < D.R.m → Y.rk (dat j) = D.R.r
  dat_jj : ∀ j, 1 ≤ j → j < D.R.m → Y.jj (dat j) = D.R.k + j - 1

  Pt : D.jet.Sit → Type

  la : ∀ i, Pt i → X.PlP (D.jet.loc i).l

  ty : ∀ i, Pt i → ZMod (D.jet.loc i).d → DV.Emb D (D.jet.loc i).l
  ty_succ : ∀ i y a, ty i y (a + 1) = DV.phiPow D 1 (ty i y a)
  ty_inj : ∀ i y, Function.Injective (ty i y)

  ptE : ∀ i, D.jet.jOf i < D.R.m → Pt i ≃ PtCl D Y (dat (D.jet.jOf i)) (D.jet.loc i).l

  loc : ∀ i, Pt i → LocD (D.jet.loc i).l (D.jet.loc i).d

  loc_r : ∀ i y, (loc i y).r = D.R.r
  loc_j : ∀ i y, (loc i y).j = D.jet.jOf i
  loc_j' : ∀ i y, (loc i y).j' = D.R.m - D.jet.jOf i

  loc_big : ∀ i y a,
    ((loc i y).big 0 a ↔ ty i y a ∈ DV.PsiOf D (X.jC (D.jet.loc i).l (la i y))) ∧
    ((loc i y).big 1 a ↔ ty i y a ∉ DV.PsiOf D (X.jC (D.jet.loc i).l (la i y)))

  loc_alt : ∀ i y, (loc i y).Alternating

  loc_rh : ∀ i (h : D.jet.jOf i < D.R.m) (y : Pt i),
    Module.finrank ℤ ((Y.loc (dat (D.jet.jOf i)) (D.jet.loc i).l).Ylat (ptE i h y).1) =
      2 * D.R.f * (loc i y).rh

variable (D : Formalism.BasicNotions.D7) (X : DivX D) (Y : ModuliIntegralCharts.Prov D) (Lc : Loc D X Y)

def adm1 : Prop := ∀ i y, (Lc.loc i y).CartierFrobeniusFormLocal ∧ (Lc.loc i y).RankOneLocalSpread

def Conclusion5 (C : ℝ) : Prop := ∀ i y, (Lc.loc i y).ContentAt C

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
  (YF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
  (LF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i) (YF x hx i))

end Family

end Formalism.MainNotions.CartierLocalBounds
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.PDVN

variable (D : Formalism.BasicNotions.D7)

def QOk (i : D.ntw.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.QOk D.ntw i Q

def SOk (i : D.ntw.Tw) (lam : D.ntw.abelian₂ i) (s : ℤ) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SOk D.ntw i lam s

def IntAfter (i : D.ntw.Tw) (n : ℕ) (x : FractionRing (D.ntw.O i)) : Prop :=
  ∃ y : D.ntw.O i, algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) y =
    ((D.ntw.l i : ℕ) : FractionRing (D.ntw.O i)) ^ n * x

structure Loc where

  cE : ∀ i, D.ntw.abelian₂ i → ℕ

  kap : ∀ i, D.ntw.abelian₂ i → ℕ

  ffP : Finset ℕ

  a0 : ℕ → ℕ
  a0_mem_one_two : ∀ p ∈ ffP, a0 p = 1 ∨ a0 p = 2

  g_mem : ∀ k, D.host.g k ∈ ffP
  pde_mem : D.host.pde ∈ ffP ∧ D.host.pde' ∈ ffP

variable {D} in
def Loc.wt (X : Loc D) (i : D.ntw.Tw) (lam : D.ntw.abelian₂ i) : ℝ :=
  (X.kap i lam : ℝ) + (D.ntw.s2 i lam : ℝ) * (D.R.f : ℝ)

def ThetaDenominatorValues (X : Loc D) (C : ℝ) : Prop :=
  ∃ n : ∀ i, D.ntw.abelian₂ i → ℕ,
    (∀ i (lam : D.ntw.abelian₂ i) (s : ℤ), D.ntw.NonzeroIndexPlace i → SOk D i lam s → D.ntw.l i ≠ 2 →
      (∀ P ∈ placesOver D.host.E (D.ntw.l i), P.asIdeal.ramificationIdx ℤ = 1) →
      D.ntw.l i ∉ X.ffP → n i lam = 0) ∧
    (∀ i (lam : D.ntw.abelian₂ i) (s : ℤ), D.ntw.NonzeroIndexPlace i → SOk D i lam s → D.ntw.l i ∣ D.host.condN →
      (n i lam : ℝ) ≤ X.wt i lam * (2 + C * Formalism.MainNotions.ExistsIdealDenominator.vdd D (D.ntw.l i))) ∧
    (∀ i (lam : D.ntw.abelian₂ i) (s : ℤ), D.ntw.NonzeroIndexPlace i → SOk D i lam s → D.ntw.l i ∈ X.ffP → (n i lam : ℝ) ≤ C * (X.a0 (D.ntw.l i) : ℝ) * X.wt i lam) ∧
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), QOk D i Q →
      ∀ (lam : D.ntw.abelian₂ i) (s : ℤ), SOk D i lam s → ∀ δ, IntAfter D i (X.cE i lam + n i lam) (D.ntw.th i Q lam δ)



def oW (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (a : 𝓞 E) : (ℂ_[l] ⊗[ℤ] Λ) →ₗ[ℂ_[l]] (ℂ_[l] ⊗[ℤ] Λ) :=
  LinearMap.baseChange ℂ_[l] (DistribSMul.toAddMonoidHom Λ a).toIntLinearMap

structure PtTie {l : ℕ} [Fact l.Prime] (E : Type) [Field E] [NumberField E] {Λ σ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (Y : Formalism.MainNotions.ExistsIdealDenominator.PtGeo l Λ σ) {Bx Ex : Type} (lx : σ → Bx) (le : σ → Ex)
    (slx : Bx → (𝓞 E →+* ℂ_[l])) where

  HA : Type
  [acgHA : AddCommGroup HA]
  [modHA : Module ℂ_[l] HA]
  LA : Type
  [acgLA : AddCommGroup LA]
  [modLA : Module ℂ_[l] LA]
  pr : HA →ₗ[ℂ_[l]] LA
  pr_surj : Function.Surjective pr

  oH : 𝓞 E →+* Module.End ℂ_[l] HA
  oL : 𝓞 E →+* Module.End ℂ_[l] LA
  pr_o : ∀ a h, pr (oH a h) = oL a (pr h)

  bx : Module.Basis Bx ℂ_[l] LA
  bx_eig : ∀ a x, oL a (bx x) = slx x a • bx x

  sle : Ex → (𝓞 E →+* ℂ_[l])
  be : Module.Basis Ex ℂ_[l] (ℂ_[l] ⊗[ℤ] Λ)
  be_eig : ∀ a e, oW l E Λ a (be e) = sle e a • be e

  th : 𝓞 E →+* 𝓞 E
  mu : HA →ₗ[ℂ_[l]] (ℂ_[l] ⊗[ℤ] Λ) →ₗ[ℂ_[l]] Y.H
  mu_bal : ∀ a h w, mu (oH a h) w = mu h (oW l E Λ (th a) w)

  fil : Y.Fil = Submodule.span ℂ_[l] {v | ∃ h w, pr h = 0 ∧ v = mu h w}

  letters : ∀ sA : LA →ₗ[ℂ_[l]] HA, pr ∘ₗ sA = LinearMap.id → ∃ b : Module.Basis σ ℂ_[l] (Y.H ⧸ Y.Fil),
    ∀ u, b u = Y.Fil.mkQ (mu (sA (bx (lx u))) (be (le u)))

  all_pairs : ∀ x e, slx x = (sle e).comp th → ∃ u, lx u = x ∧ le u = e

  EL_eq : Y.EL = {L | ∃ sA : LA →ₗ[ℂ_[l]] HA, pr ∘ₗ sA = LinearMap.id ∧ (∀ a, sA ∘ₗ oL a = oH a ∘ₗ sA) ∧
    ∀ u, L u = mu (sA (bx (lx u))) (be (le u))}

attribute [instance] PtTie.acgHA PtTie.modHA PtTie.acgLA PtTie.modLA









def AO (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Module.End (D.ntw.O i) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.AO D.nexp i j b

def V0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.V0 D.nexp i j b

def M0 (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (D.ntw.O i) (D.nexp.Fm i j b) :=
  Formalism.MainNotions.IntegralHeckeForms.Mall D.nexp i j b

def Mj (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (D.ntw.O i) (D.nexp.Fm i j b) :=
  M0 D i j b ⊓ (V0 D i j b).restrictScalars (D.ntw.O i)

def ConjugationNormInvariance : Prop :=
  (∀ (i : D.ntw.Tw) (b : Bool), ∃ c : MonoidAlgebra (D.ntw.O i) (G0g D.nd),
    MonoidAlgebra.map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).toAddMonoidHom c =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (D.ntw.O i)) • D.nexp.eAlg i b) ∧
  ∀ (i : D.ntw.Tw), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, (M0 D i j b).map (AO D i j b) ≤ Mj D i j b





def wJ (j : ℕ) : ℝ := ∑ ρ : D.what₂.Tau, DV.wSz D j ρ

def wMax : ℝ := (SizeData₂.lifts D).fold max 0 (wJ D)

def onBoundJ (L : SizeData₂ D) (C : ℝ) : ℝ :=
  C * (L.sc.L * Real.log (D.R.k : ℝ) * (D.R.m : ℝ) * wMax D +
    (D.R.f : ℝ) * (D.R.m : ℝ) * L.sc.b * Real.log L.sc.x)



structure ThetaDenominatorData where

  dat : ∀ i j b, Set (D.nexp.Dat i j b)

def OffG (w : D.what₂.places.Pl) : Prop := ∀ i0 : Fin 2, ¬ LiftErrorLocal.Over D i0 w

def GGAt (CH : NChoice D) (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  ∀ B1 B2 : Submodule (D.ntw.O (CH.twI w)) (D.nexp.Fm (CH.twI w) j b),
    B1.FG → B2 ≤ B1 → LiftErrorLocal.spK B2 = LiftErrorLocal.spK B1 → LiftErrorLocal.GStab B1 → LiftErrorLocal.GStab B2 →
    LiftErrorLocal.delq D * LiftErrorLocal.lenQ (D.ntw.l (CH.twI w)) (LiftErrorLocal.psiPart B1) (LiftErrorLocal.psiPart B2) ≤
      LiftErrorLocal.lenQ (D.ntw.l (CH.twI w)) B1 B2 + (LiftErrorLocal.rkK B1 : ℝ) * LiftErrorLocal.vU D (CH.twI w)

def SHAt (CH : NChoice D) (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  (LiftErrorLocal.rkK (D.nexp.Bsup (CH.twI w) j b) : ℝ) / LiftErrorLocal.delq D ≤
                 2 * (Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.Fm0 D.nexp (CH.twI w) j b) : ℝ) ∧
    Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.V0 D.nexp (CH.twI w) j b) = D.what₂.D0 ∧
    (Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.Fm0 D.nexp (CH.twI w) j b) : ℝ) ≤ 2 * D.what₂.D0 ∧
    (D.nexp.Bsup (CH.twI w) j b).map (IntegralHeckeForms.AO D.nexp (CH.twI w) j b) ≤ D.nexp.Bsup (CH.twI w) j b

def SHbAt (CH : NChoice D) (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  LiftErrorLocal.rkK (IntegralHeckeForms.Mall D.nexp (CH.twI w) j b) =
                 Module.finrank (FractionRing (D.ntw.O (CH.twI w))) (IntegralHeckeForms.Fm0 D.nexp (CH.twI w) j b) ∧
    LiftErrorLocal.rkK (LiftErrorLocal.Mj D (CH.twI w) j b) = D.what₂.D0

def ShareAtTypePrimes (CH : NChoice D) : Prop := ∀ (i0 : Fin 2) w, LiftErrorLocal.Over D i0 w → TwistedAt D w → SHAt D CH w

section Run

variable {D} {CH : NChoice D} (X : LiftErrorLocal.Loc D CH)

def UAt (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  IntegralHeckeForms.eThPMt D.nexp (CH.twI w) j b (CH.k' w) (CH.Q w) (X.psiW w b) ≤ LiftErrorLocal.twistV0Submodule D CH w j b ∧
    (D.what₂.Ij (D.what₂.muTw w) j (LiftErrorLocal.plS CH w b) : ℝ) ≤
      (D.what₂.places.ramIdx (LiftErrorLocal.plS CH w b) : ℝ) * X.IsgTw w j b

def LKAt (w : D.what₂.places.Pl) : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool),
  (D.nexp.Bsup (CH.twI w) j b).FG ∧ LiftErrorLocal.GStab (D.nexp.Bsup (CH.twI w) j b) ∧
    X.ThN w j h1 h2 b ≤ D.nexp.Bsup (CH.twI w) j b

def DepAt (L : SizeData₂ D) (T : ThetaDenominatorData D) (er : ℕ → ℕ → ℝ) (w : D.what₂.places.Pl) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool), ∃ c : D.ntw.O (CH.twI w), c ≠ 0 ∧
    (∀ x ∈ LiftErrorLocal.psiPart (LiftErrorLocal.GSpan (X.ThN w j h1 h2 b)),
      ∃ z ∈ IntegralHeckeForms.Th D.nexp (CH.twI w) j b (T.dat (CH.twI w) j b),
        ((Nat.card D.nexp.U : ℕ) : D.ntw.O (CH.twI w)) • x = c • z) ∧
    ((X.W j h1 h2).eLa X.TO (X.run j).nus (X.laK (LiftErrorLocal.plS CH w b)) : ℝ) /
        (eWL X.B.KO (X.laK (LiftErrorLocal.plS CH w b)) : ℝ) -
      LiftErrorLocal.vDv (D.ntw.O (CH.twI w)) (D.ntw.l (CH.twI w)) c ≤ L.F j w + er j (D.what₂.places.resChar w)

def WBAt : Prop := ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (i0 : Fin 2) la, X.laOver i0 la →
  ∀ F ∈ X.WWB j la (X.run j).wL (X.run j).n1 (X.run j).n2, ∃ s : 𝓞 X.B.KO, s ∉ la.asIdeal ∧
    s • F ∈ (X.W j h1 h2).WWc (X.run j).S.sW (X.run j).wL

def DomRun (L : SizeData₂ D) (CP : ℝ) : Prop := ∀ j (_h1 : 1 ≤ j) (_h2 : j ≤ D.R.m), WeightAlgebra.DomAt D L j (X.run j).nW CP

def AdmRun (L : SizeData₂ D) (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  DomRun X L H.C1 → LiftErrorLocal.ArchimedeanSignatureMatching D L X H C2 A2 CR CT ∧ LiftErrorLocal.LemmaBWeightBound D X CRd ∧ WBAt X ∧ LiftErrorLocal.adm11 D L X H C2 A2 CR CT CRd

end Run

structure ONObj (CH : NChoice D) (Xd : DivX D) where
  X : LiftErrorLocal.Loc D CH
  X' : LiftErrorLocal.Loc D CH

  I_eq : X'.I = X.I
  c6 : CartierLocalBounds.Loc D Xd X.P6
  c6' : CartierLocalBounds.Loc D Xd X'.P6
  T : ThetaDenominatorData D

def TwistedPlacesCover : Prop := Formalism.MainNotions.N.LocsCoverTw D

section AdmON

variable {D} (L : SizeData₂ D) {CH : NChoice D} {Xd : DivX D} (O : ONObj D CH Xd)

def admA (CA : ℝ) : Prop := LiftErrorLocal.ConjugationNormInvariance D L O.X CA

def unitBoundAtTwistedPlaces : Prop := ∀ w, TwistedAt D w → UAt O.X w

def OffTypePrimeConditions : Prop := ∀ w, OffG D w → TwistedAt D w → GGAt D CH w ∧ SHAt D CH w ∧ SHbAt D CH w ∧
  (D.what₂.places.resChar w ≠ D.host.pde → LKAt O.X w) ∧ (D.what₂.places.resChar w = D.host.pde → LKAt O.X' w)

def OrbitContentCond (C6 : ℝ) : Prop := CartierLocalBounds.Conclusion5 D Xd O.X.P6 O.c6 C6 ∧ CartierLocalBounds.Conclusion5 D Xd O.X'.P6 O.c6' C6

def DepthFromContent (C6 Cd : ℝ) : Prop := OrbitContentCond O C6 →
  ∃ er : ℕ → ℕ → ℝ, (∀ j l, 0 ≤ er j l) ∧
    (∀ j ∈ SizeData₂.lifts D, ∀ S : Finset ℕ, ∑ l ∈ S, Real.log (l : ℝ) * er j l ≤ onBoundJ D L Cd) ∧
    (∀ w, OffG D w → TwistedAt D w → D.what₂.places.resChar w ≠ D.host.pde → DepAt O.X L O.T er w) ∧
    ∀ w, OffG D w → TwistedAt D w → D.what₂.places.resChar w = D.host.pde → DepAt O.X' L O.T er w

def TypePrimeSizeConds (Cs : ℝ) : Prop :=
  1 ≤ Real.log L.sc.x ∧
    ((O.X.TO : ℝ) + (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2) * (Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ)) ≤
      onBoundJ D L Cs

def AdmON (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd C6 Cd Cs CA : ℝ) : Prop :=
  L.FDef ∧ AdmRun O.X L H C2 A2 CR CT CRd ∧ AdmRun O.X' L H C2 A2 CR CT CRd ∧ admA L O CA ∧ unitBoundAtTwistedPlaces O ∧
    OffTypePrimeConditions O ∧ OrbitContentCond O C6 ∧ DepthFromContent L O C6 Cd ∧ TypePrimeSizeConds L O Cs ∧ TwistedPlacesCover D ∧ ShareAtTypePrimes D CH

end AdmON

abbrev ONObjF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Type 1 :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ONObj (Fm.D x i) (Fm.ex x hx i).nch (Fm.X x i)

section FamON

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (OF : ONObjF Fm)


end FamON

end Formalism.MainNotions.PDVN

end
