module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinCombPullbackTransportIsoWithValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompPullbackIdValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompPullbackIdValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.IsoPullIdComp

theorem exists_comp_val : ∀ {Y X₀ X : Scheme.{0}} {A : LB Y} {L₀ : LB X₀} {M : LB X} {K₀ K : Type} [Fintype K₀] [Fintype K] (φ₀ : K₀ → (Y ⟶ X₀)) (ε₀ : K₀ → ℤ) (φ : K → (Y ⟶ X)) (ε : K → ℤ), A.IsLB → L₀.IsLB → M.IsLB → ∀ (u : LB.Iso A (LB.LinComb L₀ φ₀ ε₀)), u.IsGen → ∀ (v : LB.Iso (LB.LinComb L₀ φ₀ ε₀) ((LB.LinComb M φ ε).pull (𝟙 Y))), v.IsGen → ∃ w : LB.Iso A (LB.LinComb M φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J₀ : (Z ⟶ X₀) → L₀.ι) (a : A.ι), q z ∈ A.U a → Good M z J → Good L₀ z J₀ → gm q z _ (w.s (fun k => J (q ≫ φ k), a)) = gm q z _ (u.s (fun k => J₀ (q ≫ φ₀ k), a)) * GlobalTheory.Mum.Two.isoVal v q z J J₀ := by
  intro Y X₀ X A L₀ M K₀ K _ _ φ₀ ε₀ φ ε hA hL₀ hM u hu v hv
  have eu := GlobalTheory.LinCombComp.gm_iso_linComb φ₀ ε₀ u hu
  have ev : ∀ (y : Y) (j j' : K → M.ι) (j₀ j₀' : K₀ → L₀.ι), y ∈ LB.wchart M φ j → y ∈ LB.wchart L₀ φ₀ j₀ →
      y ∈ LB.wchart M φ j' → y ∈ LB.wchart L₀ φ₀ j₀' →
      gm (𝟙 Y) y ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
          (v.s (fun _ => j, j₀)) =
        (trF φ ε (𝟙 Y) y j j' * (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀')⁻¹) *
          gm (𝟙 Y) y ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j', j₀'))
            (v.s (fun _ => j', j₀')) := by
    intro y j j' j₀ j₀' h h0 h' h0'
    have hp : (𝟙 Y : Y ⟶ Y) y ∈
        (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀) := ⟨mem_pull.2 h, h0⟩
    have hq : (𝟙 Y : Y ⟶ Y) y ∈
        (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j', j₀') := ⟨mem_pull.2 h', h0'⟩
    have e1 := GlobalTheory.LinCombComp.gm_gen hv (𝟙 Y) y hp hq
    rw [GlobalTheory.Mum.Two.gm_div_pull (𝟙 Y) y _ _ hp hq, Category.comp_id] at e1
    exact e1
  have glue : ∀ (j : K → M.ι) (a : A.ι), ∃ s : Γ(Y, LB.wchart M φ j ⊓ A.U a)ˣ,
      ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K₀ → L₀.ι), q z ∈ LB.wchart M φ j → q z ∈ A.U a →
        q z ∈ LB.wchart L₀ φ₀ j₀ →
        gm q z (LB.wchart M φ j ⊓ A.U a) s =
          gm q z ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
              (v.s (fun _ => j, j₀)) *
            gm q z (LB.wchart L₀ φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) := by
    intro j a
    obtain ⟨W, hW⟩ : ∃ W : (K₀ → L₀.ι) → Y.Opens, ∀ j₀, W j₀ = LB.wchart M φ j ⊓ A.U a ⊓ LB.wchart L₀ φ₀ j₀ :=
      ⟨_, fun _ => rfl⟩
    have memW : ∀ y j₀, y ∈ W j₀ ↔ (y ∈ LB.wchart M φ j ∧ y ∈ A.U a) ∧ y ∈ LB.wchart L₀ φ₀ j₀ := fun y j₀ => by
      rw [hW]; exact Iff.rfl
    have l₀ : ∀ j₀, W j₀ ≤ LB.wchart M φ j ⊓ A.U a := fun j₀ y hy => ((memW y j₀).1 hy).1
    have l₁ : ∀ j₀, W j₀ ≤ (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀) :=
      fun j₀ y hy => ⟨mem_pull.2 ((memW y j₀).1 hy).1.1, ((memW y j₀).1 hy).2⟩
    have l₂ : ∀ j₀, W j₀ ≤ LB.wchart L₀ φ₀ j₀ ⊓ A.U a := fun j₀ y hy =>
      ⟨((memW y j₀).1 hy).2, ((memW y j₀).1 hy).1.2⟩
    obtain ⟨uu, hu'⟩ : ∃ uu : ∀ j₀, Γ(Y, W j₀)ˣ, ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K₀ → L₀.ι),
        q z ∈ W j₀ → gm q z (W j₀) (uu j₀) =
          gm q z ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
              (v.s (fun _ => j, j₀)) *
            gm q z (LB.wchart L₀ φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) :=
      ⟨fun j₀ => res (l₁ j₀) (v.s (fun _ => j, j₀)) * res (l₂ j₀) (u.s (j₀, a)), fun Z' q z j₀ h =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res q z (l₁ j₀) h _) (gm_res q z (l₂ j₀) h _))⟩
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart M φ j ⊓ A.U a) W l₀ (fun y hy => by
        choose j₀ hj₀ using fun k => exists_chart hL₀ (φ₀ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j₀, (memW y j₀).2 ⟨hy, Set.mem_iInter.2 hj₀⟩⟩) uu
      (fun j₀ j₀' y hy => by
        obtain ⟨⟨h1, ha⟩, h0⟩ := (memW y j₀).1 hy.1
        obtain ⟨-, h0'⟩ := (memW y j₀').1 hy.2
        refine (hu' Y (𝟙 Y) y j₀ hy.1).trans (Eq.trans ?_ (hu' Y (𝟙 Y) y j₀' hy.2).symm)
        rw [ev y j j j₀ j₀' h1 h0 h1 h0', eu y j₀ j₀' a a h0 ha h0' ha,
          GlobalTheory.LinCombComp.trF_self hM φ ε (𝟙 Y) y j h1, gm_self hA (𝟙 Y) y ha]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Z' q z j₀ h1 ha h0 => ?_⟩
    have hy : q z ∈ W j₀ := (memW _ j₀).2 ⟨⟨h1, ha⟩, h0⟩
    exact (gm_res q z (l₀ j₀) hy s).symm.trans ((congrArg (gm q z (W j₀)) (hs j₀)).trans (hu' Z' q z j₀ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun p p' => unit_ext fun y hy => ?_, fun Z q z J J₀ a ha hJ hJ₀ => ?_⟩
  · obtain ⟨⟨h1, ha⟩, h1', ha'⟩ := hy
    choose j₀ hj₀ using fun k => exists_chart hL₀ (φ₀ k y)
    have h0 : y ∈ LB.wchart L₀ φ₀ j₀ := Set.mem_iInter.2 hj₀
    have key : gm (𝟙 Y) y (LB.wchart M φ p.1 ⊓ A.U p.2) (s p.1 p.2) =
        (trF φ ε (𝟙 Y) y p.1 p'.1 * (gm (𝟙 Y) y (A.U p.2 ⊓ A.U p'.2) (A.g p.2 p'.2))⁻¹) *
          gm (𝟙 Y) y (LB.wchart M φ p'.1 ⊓ A.U p'.2) (s p'.1 p'.2) := by
      rw [hs p.1 p.2 Y (𝟙 Y) y j₀ h1 ha h0, hs p'.1 p'.2 Y (𝟙 Y) y j₀ h1' ha' h0,
        ev y p.1 p'.1 j₀ j₀ h1 h0 h1' h0, eu y j₀ j₀ p.2 p'.2 h0 ha h0 ha',
        GlobalTheory.LinCombComp.trF_self hL₀ φ₀ ε₀ (𝟙 Y) y j₀ h0]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    have hm : y ∈ (LB.div (LB.LinComb M φ ε) A).U p ⊓ (LB.div (LB.LinComb M φ ε) A).U p' :=
      ⟨⟨h1, ha⟩, h1', ha'⟩
    have ed := (GlobalTheory.LinCombComp.gm_div _ _ (𝟙 Y) y p p' hm.1 hm.2).trans
      (congrArg (· * _) (gm_linComb M φ ε (𝟙 Y) y p.1 p'.1 h1 h1'))
    exact (gm_res _ y _ hm _).trans (key.trans ((congrArg₂ (· * ·) ed.symm (gm_res _ y _ hm _).symm).trans
      (map_mul _ _ _).symm))
  · refine (hs _ a Z q z (fun k => J₀ (q ≫ φ₀ k)) (hJ.mem φ q) ha (hJ₀.mem φ₀ q)).trans
      ((mul_comm _ _).trans (congrArg _ ?_))
    have e : ∀ b b', b = b' → gm q z _ (v.s b) = gm q z _ (v.s b') := by rintro _ _ rfl; rfl
    exact e _ _ (Prod.ext (funext fun _ => funext fun k => by simp only [Category.id_comp]) rfl)

end GlobalTheory.IsoPullIdComp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompPullbackIdValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundleIso_comp_pullback_id_values : ∀ {Y X₀ X : Scheme.{0}} {A : LB Y} {L₀ : LB X₀} {M : LB X} {K₀ K : Type} [Fintype K₀] [Fintype K] (φ₀ : K₀ → (Y ⟶ X₀)) (ε₀ : K₀ → ℤ) (φ : K → (Y ⟶ X)) (ε : K → ℤ), A.IsLB → L₀.IsLB → M.IsLB → ∀ (u : LB.Iso A (LB.LinComb L₀ φ₀ ε₀)), u.IsGen → ∀ (v : LB.Iso (LB.LinComb L₀ φ₀ ε₀) ((LB.LinComb M φ ε).pull (𝟙 Y))), v.IsGen → ∃ w : LB.Iso A (LB.LinComb M φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J₀ : (Z ⟶ X₀) → L₀.ι) (a : A.ι), q z ∈ A.U a → Good M z J → Good L₀ z J₀ → gm q z _ (w.s (fun k => J (q ≫ φ k), a)) = gm q z _ (u.s (fun k => J₀ (q ≫ φ₀ k), a)) * GlobalTheory.Mum.Two.isoVal v q z J J₀ := by
  exact @GlobalTheory.IsoPullIdComp.exists_comp_val
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorMumfordBundleIsoOfGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCompPartialSumPair
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

noncomputable section
namespace GlobalTheory.MumFam
variable {R : Type} [CommRing R] [IsDomain R]

section
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G)

theorem padd_eq_mul' (x y : T ⟶ G) : padd G x y = x * y := rfl
theorem pzero_eq_one' : pzero G T = 1 := rfl

theorem psum_pair_01 : psum G ![u, v] {0, 1} = u * v := by
  have hl : (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] := by decide
  rw [psum, hl]
  simp [padd_eq_mul', pzero_eq_one']
theorem psum_pair_0 : psum G ![u, v] {0} = u := by
  have hl : (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] := by decide
  rw [psum, hl]
  simp [padd_eq_mul', pzero_eq_one']
theorem psum_pair_1 : psum G ![u, v] {1} = v := by
  have hl : (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] := by decide
  rw [psum, hl]
  simp [padd_eq_mul', pzero_eq_one']
theorem psum_pair_e : psum G ![u, v] ∅ = 1 := by
  have hl : (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] := by decide
  rw [psum, hl]
  simp [pzero_eq_one']
end

end GlobalTheory.MumFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorMumfordBundleIsoOfGenerator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.LamBridge

section Charts

variable {X X' Y : Scheme.{0}}

def cpTrans {A'' A' A : LB Y} (c₁ : ChartPull A'' A' (𝟙 Y)) (c₂ : ChartPull A' A (𝟙 Y)) : ChartPull A'' A (𝟙 Y) where
  idx i := c₂.idx (c₁.idx i)
  le i _ hy := c₂.le _ (c₁.le i hy)
  g y i j hi hj := (c₁.g y i j hi hj).trans (c₂.g y _ _ (c₁.le i hi) (c₁.le j hj))

def cpDiv {A' A B' B : LB Y} (a : ChartPull A' A (𝟙 Y)) (b : ChartPull B' B (𝟙 Y)) :
    ChartPull (LB.div B' A') (LB.div B A) (𝟙 Y) where
  idx p := (b.idx p.1, a.idx p.2)
  le p _ hy := ⟨b.le _ hy.1, a.le _ hy.2⟩
  g y p q hp hq := (gm_div A' B' (𝟙 Y) y p q ⟨hp, hq⟩).trans (Eq.trans (by rw [a.g y _ _ hp.2 hq.2, b.g y _ _ hp.1 hq.1])
    (gm_div A B (𝟙 Y) y (b.idx p.1, a.idx p.2) (b.idx q.1, a.idx q.2)
      ⟨⟨b.le _ hp.1, a.le _ hp.2⟩, ⟨b.le _ hq.1, a.le _ hq.2⟩⟩).symm)

def cpEquiv (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (E : K' ≃ K) (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (hφ : ∀ k, φ' k = φ (E k)) (hε : ∀ k, ε' k = ε (E k)) :
    ChartPull (LB.LinComb L φ' ε') (LB.LinComb L φ ε) (𝟙 Y) :=
  have le : ∀ j : K' → L.ι, LB.wchart L φ' j ≤ (𝟙 Y) ⁻¹ᵁ LB.wchart L φ (fun k => j (E.symm k)) :=
    fun j y hy => Set.mem_iInter.2 fun k => by
      have h := Set.mem_iInter.1 hy (E.symm k)
      rw [hφ, E.apply_symm_apply] at h
      exact h
  { idx := fun j k => j (E.symm k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L φ' ε' (𝟙 Y) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L φ ε (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Fintype.prod_equiv E _ _ fun k => ?_
      rw [E.symm_apply_apply, hφ, hε] }

def cpFlat (L : LB X) {I K : Type} [Fintype I] [Fintype K] (ψ : K → (X' ⟶ X)) (δ : K → ℤ) (σ : I → (Y ⟶ X'))
    (e : I → ℤ) : ChartPull (LB.LinComb L (fun p : I × K => σ p.1 ≫ ψ p.2) (fun p => e p.1 * δ p.2))
      (LB.LinComb (LB.LinComb L ψ δ) σ e) (𝟙 Y) :=
  have le : ∀ j : I × K → L.ι, LB.wchart L (fun p : I × K => σ p.1 ≫ ψ p.2) j ≤
      (𝟙 Y) ⁻¹ᵁ LB.wchart (LB.LinComb L ψ δ) σ (fun i k => j (i, k)) :=
    fun _ _ hy => Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (i, k)
  { idx := fun j i k => j (i, k)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L _ _ (𝟙 Y) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb (LB.LinComb L ψ δ) σ e (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      refine Eq.trans ?_ (Finset.prod_congr rfl fun i _ => congrArg (· ^ e i)
        (gm_linComb L ψ δ (𝟙 Y ≫ σ i) y (fun k => j (i, k)) (fun k => j' (i, k))
          (Set.mem_iInter.1 (le j hj) i) (Set.mem_iInter.1 (le j' hj') i))).symm
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_mul, mul_comm (δ k), Category.assoc] }

end Charts

def e4 : Fin 4 ≃ ULift.{0} (Finset (Fin 2)) where
  toFun k := ⟨(![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k⟩
  invFun I := if I.down = {0, 1} then 0 else if I.down = {0} then 1 else if I.down = {1} then 2 else 3
  left_inv := by intro k; fin_cases k <;> rfl
  right_inv := by intro I; revert I; decide

theorem finFourEquivSubsetsFinTwo_down_eq (k : Fin 4) : (e4 k).down = (![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k := rfl

theorem mumfordSign_finFourEquivSubsetsFinTwo (k : Fin 4) : Oε k = (-1) ^ (2 - (e4 k).down.card) := by
  fin_cases k <;> decide

end GlobalTheory.Mum.LamBridge

namespace GlobalTheory.Mum.LamBridge

theorem lift_psum {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (u v : T ⟶ B) (I : Finset (Fin 2)) :
    (lift u v).left ≫ (psum B (x2 B) I).left = (psum B ![u, v] I).left := by
  rw [← Over.comp_left, comp_psum]
  congr 2
  funext k
  fin_cases k <;> simp [x2]

theorem mumfordBundleFourPoints_eq_lift_comp_partialSum {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (u v : T ⟶ B) (k : Fin 4) :
    lamPts u v k = (lift u v).left ≫ (psum B (x2 B) (e4 k).down).left := by
  rw [lift_psum]
  fin_cases k
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_01 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_0 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_1 B u v).symm
  · exact congrArg Over.Hom.left (GlobalTheory.MumFam.psum_pair_e B u v).symm

end GlobalTheory.Mum.LamBridge

namespace GlobalTheory.Mum.LamBridge

theorem finFourEquivSubsetsFinTwo_symm_apply (I : ULift.{0} (Finset (Fin 2))) :
    (![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) (e4.symm I) = I.down := by
  rw [← finFourEquivSubsetsFinTwo_down_eq, Equiv.apply_symm_apply]

theorem exists_iso_tens : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (L₀ : LB B₀.left) (M : LB B.left), L₀.IsLB → M.IsLB → ∀ (β₂ : (G2 B₀).left ⟶ (G2 B).left) (wR : LB.Iso (abelian₂ B₀ L₀) ((abelian₂ B M).pull β₂)), wR.IsGen → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (Y : Over S₀) (x : Fin r → (Y ⟶ B₀)) (φ : (Fin r × Fin r) × Fin 4 → (Y.left ⟶ B.left)) (ε : (Fin r × Fin r) × Fin 4 → ℤ), (∀ k, φ k = (lift (x k.1.1) (x k.1.2)).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k.2)).left) → (∀ k, ε k = W k.1.1 k.1.2 * Oε k.2) → ∃ v : LB.Iso (LB.LinComb L₀ (tensφ x) (tensε W)) ((LB.LinComb M φ ε).pull (𝟙 Y.left)), v.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y.left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J₀ : (Z ⟶ B₀.left) → L₀.ι), Good M z J → Good L₀ z J₀ → GlobalTheory.Mum.Two.isoVal v q z J J₀ = ∏ a, ∏ b, lamVal wR (q ≫ (lift (x a) (x b)).left) z J J₀ ^ W a b := by
  intro S₀ S B₀ _ _ B _ _ L₀ M hL₀ hM β₂ wR hw r W Y x φ ε hφ hε
  let σ : Fin r × Fin r → (Y.left ⟶ (G2 B₀).left) := fun ab => (lift (x ab.1) (x ab.2)).left
  let e : Fin r × Fin r → ℤ := fun ab => W ab.1 ab.2
  let v₁ := transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1) wR σ e
  have hv₁ : v₁.IsGen := isGen_transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1) hw σ e
  let cA : ChartPull (LB.LinComb L₀ (tensφ x) (tensε W)) (LB.LinComb (abelian₂ B₀ L₀) σ e) (𝟙 Y.left) :=
    cpTrans (cpEquiv L₀ (Equiv.prodCongr (Equiv.refl _) e4)
      (fun p : (Fin r × Fin r) × ULift.{0} (Finset (Fin 2)) => σ p.1 ≫ (psum B₀ (x2 B₀) p.2.down).left)
      (fun p => e p.1 * (-1) ^ (2 - p.2.down.card)) _ _
      (fun k => mumfordBundleFourPoints_eq_lift_comp_partialSum (x k.1.1) (x k.1.2) k.2)
      (fun k => by
        show W k.1.1 k.1.2 * Oε k.2 = W k.1.1 k.1.2 * (-1) ^ (2 - (e4 k.2).down.card)
        rw [mumfordSign_finFourEquivSubsetsFinTwo]))
      (cpFlat L₀ (fun I : ULift.{0} (Finset (Fin 2)) => (psum B₀ (x2 B₀) I.down).left)
        (fun I => (-1) ^ (2 - I.down.card)) σ e)
  let cB : ChartPull ((LB.LinComb M φ ε).pull (𝟙 Y.left))
      (LB.LinComb (abelian₂ B M) (fun p : (Fin r × Fin r) × PUnit => σ p.1 ≫ β₂) (fun p => e p.1 * 1)) (𝟙 Y.left) :=
    cpTrans (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (LB.LinComb M φ ε) (𝟙 Y.left) (𝟙 Y.left) rfl)
      (cpTrans (cpEquiv M (Equiv.prodCongr (Equiv.prodPUnit _).symm e4)
        (fun q : ((Fin r × Fin r) × PUnit) × ULift.{0} (Finset (Fin 2)) =>
          (σ q.1.1 ≫ β₂) ≫ (psum B (x2 B) q.2.down).left)
        (fun q => (e q.1.1 * 1) * (-1) ^ (2 - q.2.down.card)) φ ε
        (fun k => by rw [hφ k]; exact (Category.assoc _ _ _).symm)
        (fun k => by
          show ε k = (W k.1.1 k.1.2 * 1) * (-1) ^ (2 - (e4 k.2).down.card)
          rw [hε k, mumfordSign_finFourEquivSubsetsFinTwo, _root_.mul_one]))
        (cpFlat M (fun I : ULift.{0} (Finset (Fin 2)) => (psum B (x2 B) I.down).left)
          (fun I => (-1) ^ (2 - I.down.card)) (fun p : (Fin r × Fin r) × PUnit => σ p.1 ≫ β₂) (fun p => e p.1 * 1)))
  let c := cpDiv cA cB
  refine ⟨cGen c v₁, cGen_isGen c hv₁, fun Z q z J J₀ hJ hJ₀ => ?_⟩
  have hm : q z ∈ (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y.left)) (LB.LinComb L₀ (tensφ x) (tensε W))).U
      (fun _ k => J (q ≫ 𝟙 Y.left ≫ φ k), fun k => J₀ (q ≫ tensφ x k)) :=
    ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun k => hJ (q ≫ 𝟙 Y.left ≫ φ k),
      Set.mem_iInter.2 fun k => hJ₀ (q ≫ tensφ x k)⟩
  refine (gm_res q z _ hm _).trans ((gm_transIso (L := abelian₂ B M) (L' := abelian₂ B₀ L₀) (fun _ : PUnit => β₂) (fun _ => 1)
    wR σ e q z (c.idx _) (c.le _ hm)).trans ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => congrArg (· ^ W a b) ?_
  unfold GlobalTheory.PolDeg.lamVal
  have key : ∀ P P', P = P' → gm (q ≫ σ (a, b)) z _ (wR.s P) = gm (q ≫ σ (a, b)) z _ (wR.s P') := by
    rintro _ _ rfl; rfl
  refine key _ _ (Prod.ext (funext fun _ => funext fun I => ?_) (funext fun I => ?_))
  · show J _ = J _
    congr 1
    show q ≫ 𝟙 Y.left ≫ φ ((a, b), e4.symm I) = _
    rw [hφ]
    simp only [finFourEquivSubsetsFinTwo_symm_apply, Category.assoc, Category.id_comp]
  · show J₀ _ = J₀ _
    congr 1
    show q ≫ lamPts (x a) (x b) (e4.symm I) = _
    rw [mumfordBundleFourPoints_eq_lift_comp_partialSum, e4.apply_symm_apply, Category.assoc]

end GlobalTheory.Mum.LamBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorMumfordBundleIsoOfGeneratorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_mumfordBundle_iso_of_generator : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (L₀ : LB B₀.left) (M : LB B.left), L₀.IsLB → M.IsLB → ∀ (β₂ : (G2 B₀).left ⟶ (G2 B).left) (wR : LB.Iso (abelian₂ B₀ L₀) ((abelian₂ B M).pull β₂)), wR.IsGen → ∀ {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (Y : Over S₀) (x : Fin r → (Y ⟶ B₀)) (φ : (Fin r × Fin r) × Fin 4 → (Y.left ⟶ B.left)) (ε : (Fin r × Fin r) × Fin 4 → ℤ), (∀ k, φ k = (lift (x k.1.1) (x k.1.2)).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k.2)).left) → (∀ k, ε k = W k.1.1 k.1.2 * Oε k.2) → ∃ v : LB.Iso (LB.LinComb L₀ (tensφ x) (tensε W)) ((LB.LinComb M φ ε).pull (𝟙 Y.left)), v.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y.left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J₀ : (Z ⟶ B₀.left) → L₀.ι), Good M z J → Good L₀ z J₀ → GlobalTheory.Mum.Two.isoVal v q z J J₀ = ∏ a, ∏ b, lamVal wR (q ≫ (lift (x a) (x b)).left) z J J₀ ^ W a b := by
  first | exact @GlobalTheory.Mum.LamBridge.exists_iso_tens | exact GlobalTheory.Mum.LamBridge.exists_iso_tens | (intros; apply GlobalTheory.Mum.LamBridge.exists_iso_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubePointsFstEqPartialSumsGrpPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubePointsFstEqPartialSumsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.PairPts

private theorem psum_two_01 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {0, 1} = u * v := by
  have hl : (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] := by decide
  rw [psum, hl]
  simp [padd, pzero, Hom.mul_def, Hom.one_def]

private theorem psum_two_e {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] ∅ = 1 := by
  have hl : (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] := by decide
  rw [psum, hl]
  simp [pzero, Hom.one_def]

private theorem psum_two_0 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {0} = u := by
  have hl : (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] := by decide
  rw [psum, hl]
  have := psum_two_e G u v
  rw [psum] at this
  simp only [List.foldr_cons, List.foldr_nil, List.filter] at this ⊢
  show u * pzero G T = u
  simp [pzero, Hom.one_def] at this ⊢

private theorem psum_two_1 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {1} = v := by
  have hl : (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] := by decide
  rw [psum, hl]
  show v * pzero G T = v
  simp [pzero, Hom.one_def]

theorem lamPts_fst_eq_psum : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (f : S₀ ⟶ S) (β : B₀.left ⟶ B.left) (β₂ : (G2 B₀).left ⟶ (G2 B).left), IsGrpPullback B₀ B f β → IsSquare β β₂ → ∀ (Y : Over S₀) (x y : Y ⟶ B₀) (x' y' : Y ⟶ (Over.pullback f).obj B), x'.left ≫ pullback.fst B.hom f = x.left ≫ β → y'.left ≫ pullback.fst B.hom f = y.left ≫ β → ∀ k : Fin 4, lamPts x' y' k ≫ pullback.fst B.hom f = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k)).left := by
  intro S₀ S B₀ _ _ B _ _ f β β₂ hβ hsq Y x y x' y' hx hy k
  have hm : ((lift x y).left ≫ β₂) ≫ (G2 B).hom = (Over.mk (Y.hom ≫ f)).hom := by
    have h1 : (G2 B).hom = (fst B B).left ≫ B.hom := (Over.w (fst B B)).symm
    rw [h1, Category.assoc, ← Category.assoc β₂, hsq.1, Category.assoc, hβ.1.w, ← Category.assoc,
      ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Category.assoc x.left, Over.w x]
    rfl
  let u : Over.mk (Y.hom ≫ f) ⟶ G2 B := Over.homMk ((lift x y).left ≫ β₂) hm
  have key : ∀ g : G2 B ⟶ B, (lift x y).left ≫ β₂ ≫ g.left = (u ≫ g).left := fun g => by
    simp [u]
  have hu1 : (u ≫ fst B B).left = x.left ≫ β := by
    rw [← key, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
  have hu2 : (u ≫ snd B B).left = y.left ≫ β := by
    rw [← key, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
  have h := isGrpPullback_pullback B f
  have m : (x' * y').left ≫ pullback.fst B.hom f = ((u ≫ fst B B) * (u ≫ snd B B)).left :=
    (h.2 Y x' y' _ _ (hu1.trans hx.symm) (hu2.trans hy.symm)).symm
  have o : (1 : Y ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f =
      (1 : Over.mk (Y.hom ≫ f) ⟶ B).left :=
    congrArg (fun z => z.left) (map_one (pushHom h Y))
  have hx2 : x2 B = ![fst B B, snd B B] := rfl
  fin_cases k
  · show (x' * y').left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {0, 1}).left
    rw [hx2, psum_two_01, key, comp_mul, m]
  · show x'.left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {0}).left
    rw [hx2, psum_two_0, key, hu1, hx]
  · show y'.left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {1}).left
    rw [hx2, psum_two_1, key, hu2, hy]
  · show (1 : Y ⟶ (Over.pullback f).obj B).left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ∅).left
    rw [hx2, psum_two_e, key, o]
    congr 1
    simp [Hom.one_def]

end GlobalTheory.PairPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubePointsFstEqPartialSumsGrpPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubePoints_fst_eq_partialSums_grpPullback : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (f : S₀ ⟶ S) (β : B₀.left ⟶ B.left) (β₂ : (G2 B₀).left ⟶ (G2 B).left), IsGrpPullback B₀ B f β → IsSquare β β₂ → ∀ (Y : Over S₀) (x y : Y ⟶ B₀) (x' y' : Y ⟶ (Over.pullback f).obj B), x'.left ≫ pullback.fst B.hom f = x.left ≫ β → y'.left ≫ pullback.fst B.hom f = y.left ≫ β → ∀ k : Fin 4, lamPts x' y' k ≫ pullback.fst B.hom f = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k)).left := by
  first | exact @GlobalTheory.PairPts.lamPts_fst_eq_psum | exact GlobalTheory.PairPts.lamPts_fst_eq_psum | (intros; apply GlobalTheory.PairPts.lamPts_fst_eq_psum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefOfRefinesTensor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.PowData

theorem sharpRef_of_tens : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁) (D₀ D : DegPre V₁) (e₀ : D₀.X ≃+ Q.X), Refines Q ρ D₀ e₀ → ∀ (T : Tens D₀ D W) (e : (Fin 8 → Q.X) ≃+ D.X), (∀ mu a, e₀ (T.xe (e mu) a) = mu a) → GlobalTheory.Poinc.Sep.SharpRef W Q ρ D e := by
  intro W V _ _ Q V₁ _ _ ρ D₀ D e₀ hR T e he
  obtain ⟨β, β₂, wR, hpb, hsq, hwR, hcR, htR⟩ := hR
  obtain ⟨io, hιm, hι⟩ := grpPullback_iso hpb (isGrpPullback_pullback Q.B (spMap ρ))
  have hprI : ∀ a, IsMonHom (T.pr a ≫ io.hom) := fun a => by
    haveI := T.pr_hom a; haveI := hιm; infer_instance
  have hpr' : ∀ a, (T.pr a ≫ io.hom).left ≫ pullback.fst Q.B.hom (spMap ρ) = (T.pr a).left ≫ β := fun a => by
    rw [Over.comp_left, Category.assoc, hι]
  let φQ : (Fin 8 × Fin 8) × Fin 4 → (D.P.A.left ⟶ Q.B.left) := fun k =>
    lamPts (T.pr k.1.1 ≫ io.hom) (T.pr k.1.2 ≫ io.hom) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)
  let εQ : (Fin 8 × Fin 8) × Fin 4 → ℤ := fun k => -(W k.1.1 k.1.2 * negε k.2)
  obtain ⟨v, hv, hvv⟩ := GlobalTheory.T.exists_tensor_mumfordBundle_iso_of_generator D₀.P.A Q.B D₀.P.L Q.M.L D₀.P.isLB Q.M.isLB β₂ wR hwR W D.P.A T.pr φQ εQ
    (fun k => GlobalTheory.T.cubePoints_fst_eq_partialSums_grpPullback D₀.P.A Q.B (spMap ρ) β β₂ hpb hsq D.P.A _ _ _ _ (hpr' _) (hpr' _) k.2)
    (fun k => by obtain ⟨⟨a, b⟩, i⟩ := k; fin_cases i <;> simp [εQ, negε, Oε])
  obtain ⟨w', hw', hwv⟩ := GlobalTheory.T.exists_lineBundleIso_comp_pullback_id_values (A := D.P.L) (tensφ T.pr) (tensε W) φQ εQ D.P.isLB D₀.P.isLB Q.M.isLB T.w T.w_gen v hv
  refine ⟨fun a => T.pr a ≫ io.hom, w', hprI, fun T' y => ?_, hw', fun mu a => ?_, fun κ hκ mu z J J' hJ hJ' => ?_⟩
  · refine ⟨Fan.IsLimit.lift T.lim (fun a => y a ≫ io.inv), fun a => ?_, fun x hx => ?_⟩
    · have h := Fan.IsLimit.fac T.lim (fun a => y a ≫ io.inv) a
      change _ ≫ T.pr a = _ at h
      show _ ≫ T.pr a ≫ io.hom = _
      rw [← Category.assoc, h]
      simp
    · refine Fan.IsLimit.hom_ext T.lim _ _ fun a => ?_
      have h := Fan.IsLimit.fac T.lim (fun a => y a ≫ io.inv) a
      change _ ≫ T.pr a = _ at h
      change x ≫ T.pr a = _ ≫ T.pr a
      rw [h, ← hx a]
      simp
  · show (D.c (e mu) ≫ T.pr a ≫ io.hom).left ≫ pullback.fst Q.B.hom (spMap ρ) = _
    rw [← Category.assoc, Over.comp_left, Category.assoc, hι, T.c_pr, hcR, he]
  · choose J₀ hJ₀ using fun s : (TK V₁).left ⟶ D₀.P.A.left => exists_chart D₀.P.isLB (s z)
    have hJ₀' : Good D₀.P.L z J₀ := hJ₀
    have h1 := T.psi (e mu) z J₀ J' hJ₀' hJ'
    have h2 := hwv _ (D.xK (e mu)) z J J₀ (J' (D.xK (e mu))) (hJ' _) hJ hJ₀'
    have h3 := hvv _ (D.xK (e mu)) z J J₀ hJ hJ₀'
    have h4 : ∀ a b, D.xK (e mu) ≫ (lift (T.pr a) (T.pr b)).left =
        (lift (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) a)) (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) b))).left := by
      intro a b
      show (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ _ = _
      rw [← Over.comp_left, comp_lift, Category.assoc, Category.assoc, T.c_pr, T.c_pr]
    have h5 : ∀ a b, val (D₀.tau (T.xe (e mu) a) (T.xe (e mu) b)) (𝟙 _) z J₀ =
        lamVal wR (lift (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) a)) (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) b))).left z J J₀ *
          val (Q.tau (mu a) (mu b)) κ z J := fun a b => by
      rw [htR κ hκ _ _ z J J₀ hJ hJ₀', he, he]
    rw [h1]
    erw [h2]
    rw [h3]
    simp only [h4, h5, mul_zpow, Finset.prod_mul_distrib, _root_.mul_assoc]

end GlobalTheory.Mum.PowData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefOfRefinesTensorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sharpRef_of_refines_tensor : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁) (D₀ D : DegPre V₁) (e₀ : D₀.X ≃+ Q.X), Refines Q ρ D₀ e₀ → ∀ (T : Tens D₀ D W) (e : (Fin 8 → Q.X) ≃+ D.X), (∀ mu a, e₀ (T.xe (e mu) a) = mu a) → GlobalTheory.Poinc.Sep.SharpRef W Q ρ D e := by
  first | exact @GlobalTheory.Mum.PowData.sharpRef_of_tens | exact GlobalTheory.Mum.PowData.sharpRef_of_tens | (intros; apply GlobalTheory.Mum.PowData.sharpRef_of_tens <;> assumption)
end
