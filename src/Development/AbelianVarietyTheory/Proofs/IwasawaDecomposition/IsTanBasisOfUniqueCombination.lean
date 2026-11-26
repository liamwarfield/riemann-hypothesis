module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcBasisBaseChange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothRayQuotient
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.HeckeFieldSplit
public import Lean

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section


open GlobalTheory.LieMet GlobalTheory.LocM.FrameBC in
theorem GlobalTheory.LineNorm.isTanBasis_of_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), (∀ i, IsTanAtG t x (e i)) → (∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x e cf u) → GlobalTheory.LineNorm.IsTanBasis t x e := by
  intro E _ _ _ H X t R _ x g e he hb
  let v : Fin g → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G := fun i => tanOf (he i)
  have hv : Full v := fun n => (existsUnique_congr fun a => GlobalTheory.LieMet.isComb_iff v a n).1 (hb _ (isTan_tv n))
  refine ⟨he, fun S _ φ w hw => ?_⟩
  have h := full_bc φ hv (tanOf hw)
  exact (existsUnique_congr fun a => GlobalTheory.LieMet.isComb_iff (fun i => resM φ (v i)) a (tanOf hw)).2 h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinates
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.CauchyBinet

theorem lform_plk (S : Type) [CommRing S] (M k : ℕ) (ι ι' : Type) (D : ι' → Fin (M + 1) → S)
    (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι) :
    ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det := by
  have h1 : ∑ q, lform D ρ q * plk u e q =
      ∑ f : Fin k → Fin (M + 1), (∏ l, D (ρ l) (f l)) * (Matrix.of fun l l' => u (e l) (f l')).det :=
    Equiv.sum_comp (plE M k)
      (fun f : Fin k → Fin (M + 1) => (∏ l, D (ρ l) (f l)) * (Matrix.of fun l l' => u (e l) (f l')).det)
  rw [h1]
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib]
  ring

variable {T : Type} {m : T → ℕ} {S : Type} [CommRing S] {M : ℕ} {D c : Let m → Fin (M + 1) → S}

theorem pair_cellVec (w : Pm m) (x : CellVar m → S) (y z : Let m) :
    ∑ r, D y r * cellVec c w x z r = ∑ i, cell x z.1 i z.2 * ∑ r, D y r * c ⟨z.1, w z.1 i⟩ r := by
  simp only [cellVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => ?_
  ring

theorem pair_same (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (τ : T) (a b : Fin (m τ)) :
    ∑ r, D (wLet w ⟨τ, a⟩) r * cellVec c w x ⟨τ, b⟩ r = cell x τ a b := by
  rw [pair_cellVec, Finset.sum_eq_single a]
  · rw [h]
    simp [wLet]
  · intro i _ hi
    rw [h, if_neg, mul_zero]
    intro he
    simp only [wLet, Sigma.mk.injEq, heq_eq_eq, true_and] at he
    exact hi ((w τ).injective he).symm
  · simp

theorem pair_ne (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (y z : Let m) (hne : y.1 ≠ z.1) :
    ∑ r, D (wLet w y) r * cellVec c w x z r = 0 := by
  rw [pair_cellVec]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [h, if_neg, mul_zero]
  intro he
  have h2 := congrArg Sigma.fst he
  exact hne h2

theorem pair_self (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (z : Let m) :
    ∑ r, D (wLet w z) r * cellVec c w x z r = 1 := by
  obtain ⟨τ, a⟩ := z
  rw [pair_same h]
  simp [cell]

theorem pair_zero (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (y z : Let m) (hne : y ≠ z)
    (hle : (y.2 : ℕ) ≤ z.2) : ∑ r, D (wLet w y) r * cellVec c w x z r = 0 := by
  by_cases h1 : y.1 = z.1
  · obtain ⟨τ, a⟩ := y
    obtain ⟨τ', b⟩ := z
    dsimp only at h1 hle
    subst h1
    rw [pair_same h]
    have hab : a ≠ b := fun e => hne (by rw [e])
    have hlt : ¬ b < a := not_lt.2 hle
    simp [cell, hab, hlt]
  · exact pair_ne h w x y z h1

theorem det_eq_one_of_unitri {k : ℕ} (N : Matrix (Fin k) (Fin k) S) (b : Fin k → ℕ) (h1 : ∀ l, N l l = 1)
    (h0 : ∀ l l', l ≠ l' → b l' ≤ b l → N l l' = 0) : N.det = 1 := by
  have hb : N.BlockTriangular b := fun l l' hl =>
    h0 l l' (fun e => by subst e; exact lt_irrefl _ hl) hl.le
  rw [hb.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : N.toSquareBlock b a = 1 := by
    ext ⟨l, hl⟩ ⟨l', hl'⟩
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.one_apply]
    split_ifs with he
    · obtain rfl : l = l' := congrArg Subtype.val he
      exact h1 l
    · exact h0 l l' (fun e => he (Subtype.ext e)) (by rw [hl, hl'])
  rw [this, Matrix.det_one]

theorem lform_plk_down (h : LeftInv D c) (w : Pm m) (x : CellVar m → S) (k : ℕ) (e : Fin k → Let m)
    (he : Down e) : ∑ q, lform D (wLet w ∘ e) q * plk (cellVec c w x) e q = 1 := by
  rw [lform_plk]
  refine det_eq_one_of_unitri _ (fun l => ((e l).2 : ℕ)) (fun l => pair_self h w x (e l)) fun l l' hl hb => ?_
  exact pair_zero h w x (e l') (e l) (fun e' => hl (he.1 e').symm) hb

theorem lform_plk_coord (hD : LeftInv D c) (w : Pm m) (x : CellVar m → S) (τ : T) (i j : Fin (m τ)) (h : j < i) :
    ∑ q, lform D (fun l : Fin (j + 1) =>
        wLet w ⟨τ, if (l : ℕ) = j then i else Fin.castLE (Nat.succ_le_of_lt j.2) l⟩) q *
      plk (cellVec c w x) (std τ (j + 1) (Nat.succ_le_of_lt j.2)) q = x ⟨τ, ⟨(i, j), h⟩⟩ := by
  rw [lform_plk]
  simp only [std, pair_same hD]
  rw [Matrix.det_of_upperTriangular]
  · rw [Fin.prod_univ_castSucc, Finset.prod_eq_one, one_mul]
    · have : Fin.castLE (Nat.succ_le_of_lt j.2) (Fin.last j) = j := Fin.ext rfl
      simp only [Matrix.of_apply, Fin.val_last, if_true, this, cell, dif_pos h]
    · intro l _
      have hl : ((l.castSucc : Fin (j + 1)) : ℕ) ≠ j := ne_of_lt l.2
      simp only [Matrix.of_apply, if_neg hl, cell, lt_irrefl, dif_neg, if_true, not_false_eq_true]
  · intro l l' hl
    have hl2 : (l' : ℕ) < l := hl
    have hl' : (l' : ℕ) ≠ j := by have := l.2; omega
    have hn : ¬ Fin.castLE (Nat.succ_le_of_lt j.2) l < Fin.castLE (Nat.succ_le_of_lt j.2) l' :=
      not_lt.2 (le_of_lt hl2)
    have hne : Fin.castLE (Nat.succ_le_of_lt j.2) l' ≠ Fin.castLE (Nat.succ_le_of_lt j.2) l :=
      ne_of_lt hl2
    simp only [Matrix.of_apply, if_neg hl', cell, dif_neg hn, if_neg hne]

theorem main : (∀ (S : Type) [CommRing S] (M k : ℕ) (ι ι' : Type) (D : ι' → Fin (M + 1) → S) (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι), ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det) ∧ ∀ (T : Type) (m : T → ℕ) (S : Type) [CommRing S] (M : ℕ) (D c : Let m → Fin (M + 1) → S) (w : Pm m) (x : CellVar m → S), LeftInv D c → (∀ (k : ℕ) (e : Fin k → Let m), Down e → ∑ q, lform D (wLet w ∘ e) q * plk (cellVec c w x) e q = 1) ∧ ∀ (τ : T) (i j : Fin (m τ)) (h : j < i), ∑ q, lform D (fun l : Fin (j + 1) => wLet w ⟨τ, if (l : ℕ) = j then i else Fin.castLE (Nat.succ_le_of_lt j.2) l⟩) q * plk (cellVec c w x) (std τ (j + 1) (Nat.succ_le_of_lt j.2)) q = x ⟨τ, ⟨(i, j), h⟩⟩ :=
  ⟨lform_plk, fun _ _ _ _ _ _ _ w x h =>
    ⟨lform_plk_down h w x, lform_plk_coord h w x⟩⟩

end GlobalTheory.FlagEmb.CauchyBinet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates : (∀ (S : Type) [CommRing S] (M k : ℕ) (ι ι' : Type) (D : ι' → Fin (M + 1) → S) (u : ι → Fin (M + 1) → S) (ρ : Fin k → ι') (e : Fin k → ι), ∑ q, lform D ρ q * plk u e q = (Matrix.of fun l l' => ∑ r, D (ρ l') r * u (e l) r).det) ∧ ∀ (T : Type) (m : T → ℕ) (S : Type) [CommRing S] (M : ℕ) (D c : Let m → Fin (M + 1) → S) (w : Pm m) (x : CellVar m → S), LeftInv D c → (∀ (k : ℕ) (e : Fin k → Let m), Down e → ∑ q, lform D (wLet w ∘ e) q * plk (cellVec c w x) e q = 1) ∧ ∀ (τ : T) (i j : Fin (m τ)) (h : j < i), ∑ q, lform D (fun l : Fin (j + 1) => wLet w ⟨τ, if (l : ℕ) = j then i else Fin.castLE (Nat.succ_le_of_lt j.2) l⟩) q * plk (cellVec c w x) (std τ (j + 1) (Nat.succ_le_of_lt j.2)) q = x ⟨τ, ⟨(i, j), h⟩⟩ := by
  first | exact @GlobalTheory.FlagEmb.CauchyBinet.main | exact GlobalTheory.FlagEmb.CauchyBinet.main | (intros; apply GlobalTheory.FlagEmb.CauchyBinet.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open ReciprocityTheory.ChartRestriction.G.PullbackSections (IsEigV)

namespace GlobalTheory.FlagEmb.EigSpread

section Alg

theorem existsUnique_iff {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] (v : ι → M) :
    (∀ w, ∃! a : ι → R, ∑ j, a j • v j = w) ↔ LinearIndependent R v ∧ Submodule.span R (Set.range v) = ⊤ := by
  rw [linearIndependent_iff_injective_fintypeLinearCombination, span_range_eq_top_iff_surjective_fintypeLinearCombination]
  exact (Function.bijective_iff_existsUnique (Fintype.linearCombination R v)).symm

variable {K O ι : Type} [Field K] [CommRing O] [Fintype ι] (χ : ι → O →+* K)

def Splits : Prop :=
  ∀ (S M : Type) [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M] (ρ : O →+* Module.End S M),
    (∀ m, ∃ mm : ι → M, (∀ τ, IsEigV ρ (χ τ) (mm τ)) ∧ ∑ τ, mm τ = m) ∧
    ∀ mm mm' : ι → M, (∀ τ, IsEigV ρ (χ τ) (mm τ)) → (∀ τ, IsEigV ρ (χ τ) (mm' τ)) → ∑ τ, mm τ = ∑ τ, mm' τ → mm = mm'

variable {χ} {R M : Type} [CommRing R] [Algebra K R] [AddCommGroup M] [Module R M] {ρ : O →+* Module.End R M}

omit [Fintype ι] in
theorem eig_single [DecidableEq ι] {τ : ι} {w : M} (hw : IsEigV ρ (χ τ) w) (τ' : ι) :
    IsEigV ρ (χ τ') (Pi.single (M := fun _ => M) τ w τ') := by
  by_cases h : τ' = τ
  · subst h; rwa [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h]; intro a; simp

theorem eig_comb {κ : Type} [Fintype κ] {ψ : O →+* K} {u : κ → M} (hu : ∀ i, IsEigV ρ ψ (u i)) (a : κ → R) :
    IsEigV ρ ψ (∑ i, a i • u i) := fun o => by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hu, smul_comm]

theorem block_basis (hs : Splits χ) {m : ι → ℕ} (u : (Σ τ, Fin (m τ)) → M) (hu : ∀ z, IsEigV ρ (χ z.1) (u z))
    (hb : ∀ w, ∃! a : (Σ τ, Fin (m τ)) → R, ∑ z, a z • u z = w) (τ : ι) (w : M) (hw : IsEigV ρ (χ τ) w) :
    ∃! a : Fin (m τ) → R, ∑ i, a i • u ⟨τ, i⟩ = w := by
  classical
  obtain ⟨a, ha, -⟩ := hb w
  have e := (hs R M ρ).2 (fun τ' => ∑ i, a ⟨τ', i⟩ • u ⟨τ', i⟩) (Pi.single τ w)
    (fun τ' => eig_comb (fun i => hu ⟨τ', i⟩) _) (eig_single hw)
    (by rw [Finset.sum_pi_single', if_pos (Finset.mem_univ _), ← ha, Fintype.sum_sigma])
  have e' := congrFun e τ
  rw [Pi.single_eq_same] at e'
  refine ⟨_, e', fun b hb' => ?_⟩
  have li : LinearIndependent R fun i => u ⟨τ, i⟩ :=
    ((existsUnique_iff u).1 hb).1.comp (Sigma.mk τ) sigma_mk_injective
  exact linearIndependent_iff_injective_fintypeLinearCombination.1 li (hb'.trans e'.symm)

theorem global_basis (hs : Splits χ) {m : ι → ℕ} (u : (Σ τ, Fin (m τ)) → M) (hu : ∀ z, IsEigV ρ (χ z.1) (u z))
    (hb : ∀ τ w, IsEigV ρ (χ τ) w → ∃! a : Fin (m τ) → R, ∑ i, a i • u ⟨τ, i⟩ = w) (w : M) :
    ∃! a : (Σ τ, Fin (m τ)) → R, ∑ z, a z • u z = w := by
  obtain ⟨mm, h1, h2⟩ := (hs R M ρ).1 w
  choose c hc hc' using fun τ => hb τ _ (h1 τ)
  refine ⟨fun z => c z.1 z.2, ?_, fun a ha => ?_⟩
  · show ∑ z : Σ τ, Fin (m τ), c z.1 z.2 • u z = w
    rw [Fintype.sum_sigma, ← h2]
    exact Finset.sum_congr rfl fun τ _ => hc τ
  · have e := (hs R M ρ).2 (fun τ' => ∑ i, a ⟨τ', i⟩ • u ⟨τ', i⟩) mm
      (fun τ' => eig_comb (fun i => hu ⟨τ', i⟩) _) h1 (by rw [h2, ← ha, Fintype.sum_sigma])
    funext z
    exact congrFun (hc' z.1 (fun i => a ⟨z.1, i⟩) (congrFun e z.1)) z.2

variable {S N : Type} [CommRing S] [Algebra K S] [AddCommGroup N] [Module S N] {ρ' : O →+* Module.End S N}
  {φ : R →+* S} (f : M →ₛₗ[φ] N)


end Alg

section Lift

variable {K O ι : Type} [Field K] [CommRing O] [Fintype ι] {χ : ι → O →+* K}
  {R M : Type} [CommRing R] [Algebra K R] [AddCommGroup M] [Module R M] {ρ : O →+* Module.End R M}
  {k N : Type} [Field k] [Algebra K k] [AddCommGroup N] [Module k N] {ρ' : O →+* Module.End k N}
  {φ : R →+* k} (f : M →ₛₗ[φ] N)

end Lift

section Geo

open GlobalTheory.FrameTangent MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {x' : Sp S ⟶ X}

theorem splits {l : Level H} (c : Coeff l) : Splits (embK c) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c)
    (fun τ a => embK_coe c τ a)
  intro S M _ _ _ _ ρ
  refine ⟨fun m => ⟨fun τ => ReciprocityTheory.ChartRestriction.G.PullbackSections.proj ρ (embK c) α τ m, fun τ =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.eig_of_alpha _ _ α hN τ (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_eig_alpha _ _ α hinj f hf hfs τ m), ?_⟩,
    fun mm mm' h h' e => funext fun τ => ?_⟩
  · rw [← LinearMap.sum_apply, ReciprocityTheory.ChartRestriction.G.PullbackSections.sum_proj ρ _ α hinj]
    rfl
  · rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ _ α hinj mm h, e, ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ _ α hinj mm' h']

def lf (m : TanM x t.G) : Tn t R := (tv m).left

theorem lf_inj {m m' : TanM x t.G} (h : lf m = lf m') : m = m' := tv_injective (Over.OverMorphism.ext h)

theorem exists_lf {w : Tn t R} (hw : IsTanAtG t x w) : ∃ m : TanM x t.G, lf m = w :=
  ⟨mkT (FrameTangent.ovT (t := t) hw) (FrameTangent.smT_zero_ovT hw), rfl⟩

theorem comb_lf {n : ℕ} (v : Fin n → TanM x t.G) (a : Fin n → R) (w : TanM x t.G) :
    IsCombAtG t x (fun j => lf (v j)) a (lf w) ↔ ∑ j, a j • v j = w := by
  refine (FrameTangent.isCombAtG_iff t x (fun j => tv (v j)) a (lf w)).trans ⟨fun h => lf_inj ?_, fun h => ?_⟩
  · rw [lf, tv_comb]
    exact h
  · rw [← h, lf, tv_comb]
    rfl


variable {Dw : Datum H} {l : Level H} {c : Coeff l}

end Geo

end GlobalTheory.FlagEmb.EigSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm

namespace GlobalTheory.LineNorm.Neg

theorem valAt_inv {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z}
    {f : Z.functionField} (hf : UnitAt (below y) f) : valAt y f⁻¹ = (valAt y f)⁻¹ := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hf
  rw [← map_units_inv, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, map_units_inv]

end GlobalTheory.LineNorm.Neg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpecMapFieldCancel
open AlgebraicGeometry CategoryTheory

theorem GlobalTheory.spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
    {X : Scheme} (y y' : Spec (CommRingCat.of K) ⟶ X)
    (h : Spec.map (CommRingCat.ofHom gam) ≫ y = Spec.map (CommRingCat.ofHom gam) ≫ y') :
    y = y' := by
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
      Spec.map (CommRingCat.ofHom gam) ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
        (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
    intro q ψ
    simp only [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc]
  rw [e, e] at h
  have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
  simp only [Sigma.mk.inj_iff] at h2
  obtain ⟨rfl, h3⟩ := h2
  have h4 : φ = φ' := by
    have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
    ext x
    apply gam.injective
    have := congrArg (fun f => f.hom x) h5
    simpa using this
  rw [h4]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuum
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.CountableCompletion

open Cardinal IsLocalRing

theorem mk_adicCompletion_le_continuum (R : Type) [CommRing R] [Countable R] (I : Ideal R) :
    #(AdicCompletion I R) ≤ 𝔠 := by
  have hinj : Function.Injective
      (fun x : AdicCompletion I R => (x.1 : ∀ n : ℕ, R ⧸ (I ^ n • ⊤ : Submodule R R))) :=
    fun x y h => Subtype.ext h
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n =>
    (mk_le_of_surjective (Submodule.mkQ_surjective _)).trans mk_le_aleph0).trans ?_
  simp

noncomputable abbrev completionCDVR (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CharZero R] : CDVR :=
  haveI : CharZero (AdicCompletion (maximalIdeal R) R) :=
    charZero_of_injective_algebraMap (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R)
  { V := AdicCompletion (maximalIdeal R) R }

theorem exists_cdvr_mk_le_continuum :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R], Countable R →
      ∃ (T : CDVR) (i : R →+* T.V), Function.Injective i ∧ IsLocalHom i ∧
        Cardinal.mk T.V ≤ Cardinal.continuum := by
  intro R _ _ _ _ hR
  exact ⟨completionCDVR R, algebraMap R (AdicCompletion (maximalIdeal R) R),
    GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R, inferInstance,
    mk_adicCompletion_le_continuum R (maximalIdeal R)⟩

end GlobalTheory.CountableCompletion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.HolFrames

section Hol

open GlobalTheory.Points

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {T : Scheme.{0}}

theorem holTan_of_affine {U : T.Opens} (hU : IsAffineOpen U) (hB : IsOpen B) {z : V → (Sp (DualNumber ℂ) ⟶ T)}
    (hz : ∀ b ∈ B, ⊤ ≤ z b ⁻¹ᵁ U)
    (h₁ : ∀ a : Γ(T, U), DifferentiableOn ℂ (fun b => (valR (A := DualNumber ℂ) (z b) U a).fst) B)
    (h₂ : ∀ a : Γ(T, U), DifferentiableOn ℂ (fun b => (valR (A := DualNumber ℂ) (z b) U a).snd) B) : HolTan B z := by
  intro W f v hv
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨h, hhW, hh⟩ := hU.exists_basicOpen_le (V := W) ⟨_, (le_preimage_iff _ _).1 hv.2⟩
    ((le_preimage_iff _ _).1 (hz v hv.1))
  have key : ∀ b ∈ B, ⊤ ≤ z b ⁻¹ᵁ T.basicOpen h ↔ (valR (A := DualNumber ℂ) (z b) U h).fst ≠ 0 := fun b hb =>
    (le_preimage_basicOpen_iff _ (hz b hb) h).trans (TrivSqZeroExt.isUnit_iff_isUnit_fst.trans isUnit_iff_ne_zero)
  have hv0 := (key v hv.1).1 ((le_preimage_iff _ _).2 hh)
  have := hU.isLocalization_basicOpen h
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h ((T.presheaf.map (homOfLE hhW).op).hom f)
  have d₁ := fun a => (h₁ a).differentiableAt (hB.mem_nhds hv.1)
  have d₂ := fun a => (h₂ a).differentiableAt (hB.mem_nhds hv.1)
  have nz : ∀ b ∈ B, (valR (A := DualNumber ℂ) (z b) U h).fst ≠ 0 →
      (valR (A := DualNumber ℂ) (z b) U (h ^ n)).fst ≠ 0 := fun b hb h0 => by
    rw [valR_pow _ _ (hz b hb), TrivSqZeroExt.fst_pow]
    exact pow_ne_zero n h0
  have di := (d₁ (h ^ n)).inv (nz v hv.1 hv0)
  have hq := ((d₂ a).sub (((d₁ a).mul di).mul (d₂ (h ^ n)))).mul di
  refine hq.congr_of_eventuallyEq ?_
  filter_upwards [hB.mem_nhds hv.1, (d₁ h).continuousAt.eventually_ne hv0] with w hw hw0
  have hw1 := (key w hw).2 hw0
  have ha' : (T.presheaf.map (homOfLE hhW).op).hom f * (T.presheaf.map (homOfLE (T.basicOpen_le h)).op).hom h ^ n =
    (T.presheaf.map (homOfLE (T.basicOpen_le h)).op).hom a := ha
  have e := congrArg (valR (z w) (T.basicOpen h)) ha'
  rw [← map_pow, valR_mul _ _ hw1, valR_res _ _ hw1, valR_res _ _ hw1, valR_res _ _ hw1] at e
  have e₁ := congrArg TrivSqZeroExt.fst e
  have e₂ := congrArg TrivSqZeroExt.snd e
  rw [TrivSqZeroExt.fst_mul] at e₁
  rw [DualNumber.snd_mul] at e₂
  have := nz w hw hw0
  simp only [Pi.inv_apply, Pi.sub_apply, Pi.mul_apply]
  rw [← e₁, ← e₂]
  field_simp
  ring

theorem holTan_dualMap {A : Type} [CommRing A] (hB : IsOpen B) (v : Sp (DualNumber A) ⟶ T) (ψ : ∀ b ∈ B, A →+* ℂ)
    (hψ : ∀ a, ∃ g : V → ℂ, DifferentiableOn ℂ g B ∧ ∀ b hb, ψ b hb a = g b) {w : V → (Sp (DualNumber ℂ) ⟶ T)}
    (hw : ∀ b hb, w b = spMap (dualMap (ψ b hb)) ≫ v) : HolTan B w := by
  classical
  by_cases hne : B.Nonempty
  swap
  · intro U f b hb
    exact (hne ⟨b, hb.1⟩).elim
  obtain ⟨b₀, hb₀⟩ := hne
  let ψ' : V → (A →+* ℂ) := fun b => if hb : b ∈ B then ψ b hb else ψ b₀ hb₀
  have e : ∀ b hb, ψ' b = ψ b hb := fun b hb => dite_eq_left hb
  have hd : ∀ a, DifferentiableOn ℂ (fun b => ψ' b a) B := fun a =>
    have ⟨g, hg, hg'⟩ := hψ a
    hg.congr fun b hb => by rw [e b hb, hg']
  have hv : ∀ b (a : DualNumber A), valR (spMap (dualMap (ψ' b))) ⊤
      ((Scheme.ΓSpecIso (.of (DualNumber A))).inv.hom a) = dualMap (ψ' b) a := fun b a =>
    valR_specMap (CommRingCat.ofHom (dualMap (ψ' b))) a
  have hs : ∀ s : Γ(Sp (DualNumber A), ⊤), ∃ a, (Scheme.ΓSpecIso (.of (DualNumber A))).inv.hom a = s := fun s =>
    ⟨(Scheme.ΓSpecIso (.of (DualNumber A))).hom.hom s, by simp⟩
  have h0 : HolTan B fun b => spMap (dualMap (ψ' b)) :=
    holTan_of_affine (isAffineOpen_top _) hB (fun b _ => le_preimage_top _)
      (fun s => by obtain ⟨a, rfl⟩ := hs s; simp only [hv]; simpa [dualMap] using hd a.fst)
      (fun s => by obtain ⟨a, rfl⟩ := hs s; simp only [hv]; simpa [dualMap] using hd a.snd)
  intro U f
  refine ((h0 (v ⁻¹ᵁ U) ((v.app U).hom f)).mono (s := {b ∈ B | ⊤ ≤ w b ⁻¹ᵁ U}) fun b hb => ⟨hb.1, ?_⟩).congr fun b hb => ?_
  · have := hb.2
    rw [hw b hb.1, ← e b hb.1] at this
    exact this
  · rw [hw b hb.1, ← e b hb.1, valR_comp]

theorem valR_eq_germ {C : Type} [CommRing C] [IsLocalRing C] (p : Sp C ⟶ T) (U : T.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) :
    valMap p U h = T.presheaf.germ U _ ((le_preimage_iff p U).1 h) ≫ Scheme.stalkClosedPointTo (R := .of C) p := by
  rw [Scheme.germ_stalkClosedPointTo]
  rfl

end Hol

section Expo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)


end Expo

section Frames

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.CoordUniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_bc {A B : Type} [CommRing A] [CommRing B] {φ : c.F →+* A} {x : Sp A ⟶ Z.X} (fr : EigFrame Z φ x)
    (ψ : A →+* B) {φ' : c.F →+* B} {x' : Sp B ⟶ Z.X} (hφ : φ' = ψ.comp φ) (hx : x' = spMap ψ ≫ x) :
    ∃ g : EigFrame Z φ' x', ∀ τ i, g.v τ i = spMap (dualMap ψ) ≫ fr.v τ i := by
  subst hφ hx
  obtain ⟨g, hg⟩ := GlobalTheory.ShFam.Spread.exists_bc fr ψ rfl rfl
  exact ⟨g, fun τ i => congrArg (fun v => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left) (hg τ i)⟩

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

end Frames


end GlobalTheory.ShFam.HolFrames
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Tr

theorem exists_iota_comp {K₁ K₂ : Type} [Field K₁] [Field K₂] (c₁ : K₁ →+* ℂ) (c₂ : K₂ →+* ℂ)
    (h : Set.range c₁ ⊆ Set.range c₂) : ∃ ι : K₁ →+* K₂, ∀ x, c₂ (ι x) = c₁ x := by
  have hle : c₁.range ≤ c₂.range := by
    intro y hy
    obtain ⟨x, rfl⟩ := RingHom.mem_range.1 hy
    obtain ⟨z, hz⟩ := h ⟨x, rfl⟩
    exact RingHom.mem_range.2 ⟨z, hz⟩
  let e : K₂ ≃+* c₂.range := RingEquiv.ofBijective c₂.rangeRestrict
    ⟨fun a b hab => c₂.injective (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective c₂⟩
  refine ⟨e.symm.toRingHom.comp ((Subring.inclusion hle).comp c₁.rangeRestrict), fun x => ?_⟩
  have h1 : c₂ (e.symm ⟨c₁ x, hle (RingHom.mem_range_self c₁ x)⟩) = c₁ x := by
    have := congrArg Subtype.val (e.apply_symm_apply ⟨c₁ x, hle (RingHom.mem_range_self c₁ x)⟩)
    exact this
  exact h1

abbrev baseOfColW {B : Base} {f : Fr B.toPre} {T : TwDat B} (_ : ColW B f T) : Base := B

theorem levelFamily_coefficientChange_liftRound (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG)
    (hH : ∀ w, (Λ₂ w).H = (Λ₁ w).H)
    (hl : ∀ w (h₁ : ↥(Λ₁ w).H) (h₂ : ↥(Λ₂ w).H), (h₁ : GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) = h₂ →
      ι (((Λ₁ w).lam h₁ : X.Kˣ) : X.K) = (((Λ₂ w).lam h₂ : Lˣ) : L))
    (φ₁ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG) => d.1.N) Λ₁).EqFun) :
    ∃ φ₂ : (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
      (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
        fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG) => d.1.N) Λ₂).EqFun,
      ∀ d, (φ₂.1 d).1 = MvPolynomial.map ι (φ₁.1 d).1 := by
  refine ⟨⟨fun d => Formalism.L2.Col.hfsJ ι lam (φ₁.1 d), ?_⟩, fun d => rfl⟩
  intro g d
  have hg : g.2.1 ∈ Λ₁.grp := by
    intro w _
    have h' : (g.2.1 w) ∈ (Λ₂ w).H := g.2.2 w (Set.mem_univ _)
    rw [hH w] at h'
    exact h'
  have h1 : φ₁.1 (g • d) = (((Λ₁.chr ⟨g.2.1, hg⟩ : X.Kˣ)) : X.K) •
      Formalism.L2.DIV.rhoVr X.emb lam (Formalism.L2.Col.ufGL X.E n g.1) (φ₁.1 d) := φ₁.2 (g.1, ⟨g.2.1, hg⟩) d
  have he' : e = fun τ => ι.comp (X.emb τ) := funext fun τ => (he τ).symm
  subst he'
  show Formalism.L2.Col.hfsJ ι lam (φ₁.1 (g • d)) = (((Λ₂.chr g.2 : Lˣ)) : L) •
    Formalism.L2.DIV.rhoVr (fun τ => ι.comp (X.emb τ)) lam (Formalism.L2.Col.ufGL X.E n g.1) (Formalism.L2.Col.hfsJ ι lam (φ₁.1 d))
  have h2 := Formalism.L2.Col.hfs_rhoVr ι lam X.emb (Formalism.L2.Col.ufGL X.E n g.1) (φ₁.1 d)
  erw [h2, h1, Formalism.L2.Col.hfsJ_smul]
  congr 1
  rw [Formalism.L2.Col.LevFam.chr_apply, show Λ₂.chr g.2 = _ from Formalism.L2.Col.piChar_apply _ _ g.2, Units.coe_prod, Units.coe_prod, map_prod]
  exact Finset.prod_congr rfl fun w _ => hl w _ _ rfl

theorem liftRound_reidx (X : Formalism.L2.Col.Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam : X.Tau → DomWeight n)
    {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : Formalism.L2.Col.LevFam X.E X.K n SG₁) (Λ₂ : Formalism.L2.Col.LevFam X.E L n SG₂)
    (hΛ : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), Λ₂ ⟨w.1, hw⟩ = (Λ₁ w).coefMap ι)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x) :
    Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₂) = Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) ∧
    ∀ φ₁ : (Formalism.L2.Col.formGSD (Formalism.L2.Col.roundPk X lam fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁).EqFun,
    ∃ φ₂ : (Formalism.L2.Col.formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields))
      (Formalism.L2.Col.roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Formalism.L2.Col.Fields) lam
        fun d : Formalism.L2.Col.DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₂) => d.1.N) Λ₂).EqFun,
      ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ (φ₂.1 d₂).1) (MvPolynomial.map c₁ (φ₁.1 d₁).1) := by
  subst hS
  have hΛ' : Λ₂ = Λ₁.coefMap ι := funext fun w => hΛ w w.2
  subst hΛ'
  refine ⟨rfl, fun φ₁ => ?_⟩
  obtain ⟨φ₂, h⟩ := levelFamily_coefficientChange_liftRound X ι e he lam Λ₁ (Λ₁.coefMap ι) (fun w => rfl) (fun w h₁ h₂ hh => by
    have : h₁ = h₂ := Subtype.ext hh
    subst this
    rfl) φ₁
  refine ⟨φ₂, fun d₁ d₂ hd => ?_⟩
  cases hd
  rw [h, MvPolynomial.map_map]
  have hc' : c₂.comp ι = c₁ := RingHom.ext hc
  rw [hc']

theorem twistRamifiedPrimes_empty_colTuples {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (W : Set B.places.Pl) :
    Formalism.L2.Col.QE w.I.sel ((mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := by
  have e : Formalism.L2.Col.QE w.I.sel (w.I.tup w.I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty w.I
  rw [w.I.trueColumn_tuple_trivial_eq_one] at e
  exact e

theorem rowLevelPrimes_colTuples_eq_vGs {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (W : Set B.places.Pl) :
    Formalism.L2.Col.rowSG (B.primes w.px) w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 = (B.primes w.px).vGs := by
  show Formalism.L2.Col.uSG _ _ = _
  rw [twistRamifiedPrimes_empty_colTuples w W]
  ext x
  simp

theorem glue_inv_coefMap_of_empty {E K L : Type} [Field E] [NumberField E] [Field K] [Field L] (ι : K →+* L) {n : ℕ}
    {SG₁ Q₁ SG₂ Q₂ : Finset (HeightOneSpectrum (𝓞 E))} (hQ₁ : Q₁ = ∅) (hQ₂ : Q₂ = ∅)
    (A₁ : Formalism.L2.Col.LevFam E K n SG₁) (B₁ : Formalism.L2.Col.LevFam E K n Q₁)
    (A₂ : Formalism.L2.Col.LevFam E L n SG₂) (B₂ : Formalism.L2.Col.LevFam E L n Q₂)
    (hA : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), A₂ ⟨w.1, hw⟩ = (A₁ w).coefMap ι) :
    ∀ (w : ↥(Formalism.L2.Col.uSG SG₁ Q₁)) (hw : w.1 ∈ Formalism.L2.Col.uSG SG₂ Q₂),
      (A₂.glue B₂).inv ⟨w.1, hw⟩ = ((A₁.glue B₁).inv w).coefMap ι := by
  intro w hw
  have h1 : w.1 ∈ SG₁ := by
    have := w.2
    simp only [Formalism.L2.Col.uSG, hQ₁, Finset.union_empty] at this
    exact this
  have h2 : w.1 ∈ SG₂ := by
    have := hw
    simp only [Formalism.L2.Col.uSG, hQ₂, Finset.union_empty] at this
    exact this
  show ((A₂.glue B₂) ⟨w.1, hw⟩).inv = (((A₁.glue B₁) w).inv).coefMap ι
  rw [Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h2, Formalism.L2.Col.LevFam.glue_of_mem _ _ _ h1, ← Formalism.L2.Col.Lev.coefMap_inv,
    hA ⟨w.1, h1⟩ h2]

theorem levKV_coefMap_of {E K L : Type} [Field E] [NumberField E] [Field K] [Field L] (ι : K →+* L) {m : ℕ}
    (w : HeightOneSpectrum (𝓞 E)) (χ₁ : Fin m → (𝓞 E ⧸ w.asIdeal)ˣ →* Kˣ) (χ₂ : Fin m → (𝓞 E ⧸ w.asIdeal)ˣ →* Lˣ)
    (h : ∀ s c, ((χ₂ s c : Lˣ) : L) = ι ((χ₁ s c : Kˣ) : K)) (nV r t s : ℕ) :
    (⟨Formalism.L2.Col.HKV (𝓞 E ⧸ w.asIdeal) nV r t, Formalism.L2.Col.lamKV (Formalism.L2.Col.extChi χ₂ s) nV r t⟩ :
        Formalism.L2.Col.Lev (𝓞 E ⧸ w.asIdeal) L nV) =
      Formalism.L2.Col.Lev.coefMap ι ⟨Formalism.L2.Col.HKV (𝓞 E ⧸ w.asIdeal) nV r t, Formalism.L2.Col.lamKV (Formalism.L2.Col.extChi χ₁ s) nV r t⟩ := by
  have hχ : χ₂ = fun s => (Units.map ι.toMonoidHom).comp (χ₁ s) :=
    funext fun s => MonoidHom.ext fun c => Units.ext (h s c)
  subst hχ
  have h' : (fun _ : ℕ => (Formalism.L2.Col.extChi (fun s => (Units.map ι.toMonoidHom).comp (χ₁ s)) s)⁻¹) =
      fun _ : ℕ => (Units.map ι.toMonoidHom).comp (Formalism.L2.Col.extChi χ₁ s)⁻¹ :=
    funext fun _ => (congrArg (·⁻¹) (Formalism.L2.Col.extChi_coefMap ι χ₁ s)).trans (Formalism.L2.Col.coefMap_comp_inv ι _)
  exact congrArg (Formalism.L2.Col.Lev.mk (Formalism.L2.Col.HKV (𝓞 E ⧸ w.asIdeal) nV r t))
    ((congrArg (fun χ => Formalism.L2.Col.lamK χ nV r [t]) h').trans (Formalism.L2.Col.lamK_coefMap ι _ _ _))

theorem lift_refTuple_enl : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (W₁ : Set B₁.places.Pl) (W₂ : Set B₂.places.Pl), Enl B₁ B₂ → HEq (B₂.primes w₂.px).vGs (B₁.primes w₁.px).vGs → (∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K)) → ∀ j₁ j₂ : ℕ, j₁ = j₂ → (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).D = (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).D ∧ ∀ φ₁ : (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).EqFun, ∃ φ₂ : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).EqFun, ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (φ₂.1 d₂).1) (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (φ₁.1 d₁).1) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ W₁ W₂ hE hv hchi j₁ j₂ hj
  subst hj
  obtain ⟨hpre, -, -, hrange⟩ := hE
  obtain ⟨ι, hι⟩ := exists_iota_comp B₁.embLL B₂.embLL hrange
  cases B₁ with | mk P₁ =>
  cases B₂ with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  refine liftRound_reidx (baseOfColW w₁).fields ι (baseOfColW w₂).tauLL ?_ _ ?_ _ _ ?_ (baseOfColW w₁).embLL
    (baseOfColW w₂).embLL hι
  · intro τ
    ext x
    apply (baseOfColW w₂).embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₁) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w₂) τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    rw [RingHom.comp_apply, hι]
    exact h1.trans h2.symm
  · exact (rowLevelPrimes_colTuples_eq_vGs w₂ W₂).trans ((eq_of_heq hv).trans (rowLevelPrimes_colTuples_eq_vGs w₁ W₁).symm)
  · refine glue_inv_coefMap_of_empty ι (twistRamifiedPrimes_empty_colTuples w₁ W₁) (twistRamifiedPrimes_empty_colTuples w₂ W₂) _ _ _ _ ?_
    intro w hw
    refine levKV_coefMap_of ι w.1 (fun s => w₁.I.Ch.chi s w) (fun s => w₂.I.Ch.chi s ⟨w.1, hw⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w₂).embLL.injective
    rw [hι]
    exact hchi s s rfl w ⟨w.1, hw⟩ HEq.rfl c c HEq.rfl

end GlobalTheory.Mem.R3.Tr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargementStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTupleLiftForms_pass_to_coeffEnlargement : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} (w₁ : ColW B₁ f₁ T₁) (w₂ : ColW B₂ f₂ T₂) (W₁ : Set B₁.places.Pl) (W₂ : Set B₂.places.Pl), Enl B₁ B₂ → HEq (B₂.primes w₂.px).vGs (B₁.primes w₁.px).vGs → (∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K)) → ∀ j₁ j₂ : ℕ, j₁ = j₂ → (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).D = (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).D ∧ ∀ φ₁ : (Formalism.L2.Col.mtKGSD (Pr := B₁.primes w₁.px) B₁.wts w₁.I.Ch w₁.I.sel (mu0F (X := B₁.fields) (tuOf w₁.I (usedOf w₁.I T₁ W₁))).1 j₁).EqFun, ∃ φ₂ : (Formalism.L2.Col.mtKGSD (Pr := B₂.primes w₂.px) B₂.wts w₂.I.Ch w₂.I.sel (mu0F (X := B₂.fields) (tuOf w₂.I (usedOf w₂.I T₂ W₂))).1 j₂).EqFun, ∀ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map (B₂.embLL : B₂.fields.K →+* ℂ) (φ₂.1 d₂).1) (MvPolynomial.map (B₁.embLL : B₁.fields.K →+* ℂ) (φ₁.1 d₁).1) := by
  first | exact @GlobalTheory.Mem.R3.Tr.lift_refTuple_enl | exact GlobalTheory.Mem.R3.Tr.lift_refTuple_enl | (intros; apply GlobalTheory.Mem.R3.Tr.lift_refTuple_enl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothBaseAndNormalCoordinateRing
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem smooth_cbase {X : Scheme.{0}} {T : Type} [Finite T] (m : T → ℕ) (U : X.affineOpens) : Smooth (cbase m U) := by
  have h : Smooth (spMap (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) := by
    refine (HasRingHomProperty.Spec_iff (P := @Smooth)).2 ?_
    exact RingHom.smooth_algebraMap.2 (⟨inferInstance, inferInstance⟩ : Algebra.Smooth Γ(X, U.1) (MvPolynomial (CellVar m) Γ(X, U.1)))
  have h' : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  have h'' : Smooth U.2.fromSpec := inferInstance
  exact MorphismProperty.comp_mem @Smooth _ _ h h''

theorem cell_smooth_normal : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Type) [Finite T] (m : T → ℕ) (U : X.affineOpens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → Smooth (cbase m U) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp (CR m U)) := by
  intro X _ T _ m U hX
  have := smooth_cbase m U
  exact ⟨this, forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (cbase m U) hX⟩

end GlobalTheory.FlagEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RosLevel
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv.Transport

abbrev Frame {X Y : Scheme.{0}} (L : LB X) (ψ : Y ⟶ X) : Type :=
  LB.Gen (LB.LinComb L (K := PUnit) (fun _ => ψ) fun _ => 1)

section Defs

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

def Lies {T : Scheme.{0}} (x' : T ⟶ G.left) (b : T ⟶ D.toPre.P.A.left) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T) (y : Z ⟶ (thickObj R I e G).left),
    y ≫ fGl I G e = r ≫ x' → y ≫ pGl U e = r ≫ b

def FrRel {T : Scheme.{0}} (x' : T ⟶ G.left) (b : T ⟶ D.toPre.P.A.left) (g' : Frame U.LG.L x')
    (g : Frame D.toPre.P.L b) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T) (y : Z ⟶ (thickObj R I e G).left), y ≫ fGl I G e = r ≫ x' →
    ∀ (z : Z) (JM) (JL), Good D.toPre.P.L z JM → Good U.LG.L z JL →
      val g r z JM = wVal U e z JM JL y * val g' r z JL

end Defs

end GlobalTheory.RayEv.Transport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfPluckerProportional
noncomputable section

namespace GlobalTheory.FlagEmb

theorem adjugate_mul_eq_plk {K : Type} [Field K] {M k : ℕ} (D : Fin k → Fin (M + 1) → K) (r : Fin k → Fin (M + 1))
    (i : Fin k) (s : Fin (M + 1)) :
    ((Matrix.of fun l l' => D l (r l')).adjugate * Matrix.of D) i s =
      plk D id ((plE M k).symm (Function.update r i s)) := by
  have h1 : ((Matrix.of fun l l' => D l (r l')).adjugate * Matrix.of D) i s =
      ((Matrix.of fun l l' => D l (r l')).adjugate.mulVec fun j => D j s) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [h1, ← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  simp only [plk, Equiv.apply_symm_apply, id]
  congr 1
  ext l l'
  by_cases h : l' = i
  · subst h
    simp [Matrix.updateCol_apply]
  · simp [Matrix.updateCol_apply, Function.update_of_ne h, h]

theorem mem_span_of_plk_eq_smul (K : Type) [Field K] (M k : ℕ) (c c' : Fin k → Fin (M + 1) → K) (a : K)
    (h0 : plk c' id ≠ 0) (h : plk c' id = a • plk c id) (l : Fin k) :
    c' l ∈ Submodule.span K (Set.range c) := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h0
  set r := plE M k q with hr
  set A : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' => c l (r l') with hA
  set A' : Matrix (Fin k) (Fin k) K := Matrix.of fun l l' => c' l (r l') with hA'
  have hdet : A'.det ≠ 0 := hq
  have hadj : A'.adjugate * Matrix.of c' = a • (A.adjugate * Matrix.of c) := by
    ext i s
    rw [hA, hA', adjugate_mul_eq_plk, Matrix.smul_apply, adjugate_mul_eq_plk, h]
    rfl
  have hC : A'.det • (Matrix.of c' : Matrix (Fin k) (Fin (M + 1)) K) = a • (A' * A.adjugate * Matrix.of c) := by
    have := congrArg (fun X => A' * X) hadj
    simp only [← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul] at this
    simpa [Matrix.smul_mul] using this
  have hrow : c' l = ∑ j, ((A'.det)⁻¹ * (a * (A' * A.adjugate) l j)) • c j := by
    funext s
    have h2 := congrFun (congrFun hC l) s
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Matrix.mul_apply (M := A' * A.adjugate)] at h2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [eq_inv_mul_iff_mul_eq₀ hdet |>.2 h2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hrow]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.FlagEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AllStepsHoldOfHasDR
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.LieMet GlobalTheory.LocM.FrameBC

namespace GlobalTheory.LocM.StepOfFrame

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

variable {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W}
  {i₀ : Idx H p}

end GlobalTheory.LocM.StepOfFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeyAtIffExistsKeyAtVia
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.ArcNormal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def KeyAtVia {Y : Model Xo c β} (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    (x : KeyIn R) (φ : x.P.A.left ⟶ Y.t.G.left) : Prop :=
  ∃ (he : eSec x.P.A ≫ φ = z ≫ eSec Y.t.G) (w : LB.Iso x.P.L (Y.t.PP.L.pull φ)) (hg : x.P.g = M.n),
    IsGrpPullback x.P.A Y.t.G z φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ z he Y.t.PP.L Y.t.PP.rig) ∧
    (∀ (j : (Y.t.PP.L.pull φ).ι) (i : x.P.L.ι)
      (h : (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U (j PUnit.unit))),
      (φ.appLE _ _ h).hom (M.θ (j PUnit.unit)) =
        (show Γ(x.P.A.left, (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x.th.f i)) ∧
    ∀ i, (x.v i).left ≫ φ = spMap (dualMap (ev z M.U hz)) ≫ M.v₀ (i.cast hg)

def ArcFib (Y : Model Xo c β) (bF : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left) (u : HolUnif x.P.A x.P.L g) : Prop :=
  ∀ z, ∃ ψ : Sp ℂ ⟶ Y.oF.t.G.left, ψ ≫ Y.m0.toSABMap.φ = (Fu.ex i P z).left ∧
    ψ ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF ∧ (u.ex z).left ≫ φ = ψ ≫ Y.m.φ

end GlobalTheory.ArcNormal
end
end
