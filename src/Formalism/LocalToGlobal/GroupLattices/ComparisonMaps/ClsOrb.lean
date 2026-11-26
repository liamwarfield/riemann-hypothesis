module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ProdMemSpan

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsOrb
section -- merged from Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PtGComp
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

def ptG (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) (i : compL L p)
    (g : ∀ v : Fin nV, GL (Fin R.k) ((I.plc v).adicCompletion F)) : UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) :=
  repP L p i * jP I hdet g

def clsG (I : LocId L p nV W Qq) (hdet : IsUnit sp.gram0.det) (i : compL L p)
    (g : ∀ v : Fin nV, GL (Fin R.k) ((I.plc v).adicCompletion F)) :
    ClassSet ((ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)).subgroupOf
        (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)))
      (L.U.subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))) :=
  Quotient.mk'' (ptG I hdet i g)

end Formalism.L2.G
end
end

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G
open scoped TensorProduct

namespace Formalism.L2.G.Cmp

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

abbrev HA (sp : Spaces R F E) : Subgroup (GA sp) :=
  (ratPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))

abbrev KA (L : ColLevel R F E sp gp C A clsLat) : Subgroup (GA sp) :=
  L.U.subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))

abbrev KA' (L : ColLevel R F E sp gp C A clsLat) (p : ℕ) : Subgroup (GA sp) :=
  (Formalism.L2.Herm.awayFrom₂ L p).subgroupOf (UPts sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F))

def ratA (sp : Spaces R F E) : UJ (sp.cm.sig : E →+* E) sp.gram0 →* GA sp :=
  ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).comp (UJ (sp.cm.sig : E →+* E) sp.gram0).subtype).codRestrict _
    (fun γ => Formalism.UG.P.rational_points_le_holds F E (Fin R.k) sp.cm.sig sp.gram0 (FiniteAdeleRing (𝓞 F) F) ⟨γ, γ.2, rfl⟩)

theorem ratA_mem (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) : ratA sp γ ∈ HA sp :=
  Subgroup.mem_subgroupOf.2 ⟨γ, γ.2, rfl⟩

theorem exists_ratA (x : GA sp) (hx : x ∈ HA sp) : ∃ γ, ratA sp γ = x := by
  obtain ⟨γ, hγ, e⟩ := Subgroup.mem_subgroupOf.1 hx
  exact ⟨⟨γ, hγ⟩, Subtype.ext e⟩

theorem mem_map_conj {G0 : Type} [Group G0] (S : Subgroup G0) (y g : G0) :
    g ∈ S.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * g * y ∈ S := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : y⁻¹ * (MulAut.conj y).toMonoidHom u * y = u := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hu
  · intro h
    exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_gamC_iff (y : GA sp) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) :
    γ ∈ gamC sp.cm.sig sp.gram0 (Formalism.L2.Herm.awayFrom₂ L p) (y : GL (Fin R.k) _) ↔ y⁻¹ * ratA sp γ * y ∈ KA' L p :=
  mem_map_conj (Formalism.L2.Herm.awayFrom₂ L p) (y : GL (Fin R.k) _) (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin R.k) E))

theorem prP_ratA (I : LocId L p nV W Qq) {m : ℕ} (hk : m + 1 = R.k) (γ : UJ (sp.cm.sig : E →+* E) sp.gram0) (v : Fin nV) :
    prP I hk (ratA sp γ) v = (castGL hk Qq).symm ((I.frQ v)⁻¹ * bc (I.iw v) (γ : GL (Fin R.k) E) * I.frQ v) := by
  rw [prP_apply, toF_symm]
  congr 1
  rw [map_mul, map_mul, map_inv]
  rfl

end Formalism.L2.G.Cmp
end
end

section -- merged from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfWeak
section -- merged from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfE
section -- merged from Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RatActGOf
open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G

theorem natAct_rat {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (P : Places p O Kf) {LL : Type} [Field LL] (e : LL →+* Kf) (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v))
    (g : ∀ v, Fin (P.n' v) → GL (Fin (P.m + 1)) LL)
    (hg : ∀ v s, Matrix.GeneralLinearGroup.map e (g v s) = gPosGL P v s (A v)) (Q : XR P LL) :
    MvPolynomial.map e (natActR P LL g Q) = P.natAct A (MvPolynomial.map e Q) := by
  have hinv : ∀ v s a b, e ((((g v s)⁻¹ : GL (Fin (P.m + 1)) LL) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL) a b) =
      P.gPos v s (((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) a b := by
    intro v s a b
    have h1 : Matrix.GeneralLinearGroup.map e ((g v s)⁻¹) = gPosGL P v s ((A v)⁻¹) := by
      rw [map_inv, map_inv, hg]
    have h2 := congrArg (fun M : GL (Fin (P.m + 1)) Kf => (M : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) a b) h1
    exact h2
  have hdet : ∀ v s, e ((g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL).det) =
      (P.gPos v s (A v : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))).det := by
    intro v s
    rw [RingHom.map_det]
    congr 1
    have h2 := congrArg (fun M : GL (Fin (P.m + 1)) Kf => (M : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf)) (hg v s)
    exact h2
  have hsub : ∀ R : XR P LL, MvPolynomial.map e
      (substR P LL (fun v s => (((g v s)⁻¹ : GL (Fin (P.m + 1)) LL) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) LL)) R) =
      P.subst (fun v s => P.gPos v s (((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)) :
        Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))) (MvPolynomial.map e R) := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a => simp [substR, Places.subst]
    | add f q hf hq => simp only [map_add (f := _), hf, hq]
    | mul_X f x hf =>
      simp only [map_mul, hf]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [substR, Places.subst, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.map_C,
        MvPolynomial.map_X, hinv]
  simp only [natActR, Places.natAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, hsub]
  congr 2
  simp only [map_prod, map_zpow₀, hdet]
  rfl

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] (e : LL →+* G.Kf)

def RatLev : Prop :=
  (∀ (i : G.comp) (γ : (G.lev i).Γ) (v : Fin G.P.nV) (s : Fin (G.P.n' v)), ∃ g : GL (Fin (G.P.m + 1)) LL,
    Matrix.GeneralLinearGroup.map e g = gPosGL G.P v s ((G.lev i).act v γ)) ∧
  ∀ (i : G.comp) (γ : (G.lev i).Γ), ∃ a : LL, e a = algebraMap G.O G.Kf ((G.lev i).χ γ : G.O)

theorem ratActG_of (h : RatLev G e) : RatActG G e := by
  intro i γ ξ hξ
  obtain ⟨Q, hQ⟩ := hξ
  choose g hg using fun v s => h.1 i γ v s
  obtain ⟨a, ha⟩ := h.2 i γ
  refine ⟨a • natActR G.P LL g Q, ?_⟩
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
    natAct_rat G.P e (fun v => (G.lev i).act v γ) g hg Q, hQ, ← MvPolynomial.smul_eq_C_mul, ha,
    algebraMap_smul]
  rfl

end Formalism.L2.G.Cmp
end
end

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} (G : GAtP p) {E LL : Type} [Field E] [Field LL] (e : LL →+* G.Kf)
  (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v) (t : ∀ v : Fin G.P.nV, Fin (G.P.n' v) → E →+* LL)

def PosCompat : Prop :=
  ∀ (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (x : E), e (t v s x) = G.P.ι v ((G.P.σ v ^ s.val) (iw v x))

def ActE : Prop :=
  ∀ (i : G.comp) (γ : (G.lev i).Γ), ∃ a : GL (Fin (G.P.m + 1)) E,
    ∀ v, (G.lev i).act v γ = Matrix.GeneralLinearGroup.map (iw v) a

def ChiRat : Prop :=
  ∀ (i : G.comp) (γ : (G.lev i).Γ), ∃ a : LL, e a = algebraMap G.O G.Kf ((G.lev i).χ γ : G.O)

def RatTup : Prop :=
  ∀ L : G.P.Tup, G.P.IsLatTup L → ∃ a : GL (Fin (G.P.m + 1)) E,
    ∀ v, L v = colSpan (G.P.W v) ((a : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) E).map (iw v))

theorem ratLev_of (hp : PosCompat G e iw t) (ha : ActE G iw) (hc : ChiRat G e) : RatLev G e := by
  refine ⟨fun i γ v s => ?_, hc⟩
  obtain ⟨a, ha⟩ := ha i γ
  refine ⟨Matrix.GeneralLinearGroup.map (t v s) a, ?_⟩
  rw [ha v]
  ext j k
  simp [gPosGL, hp v s]

theorem ratBasis_of (hp : PosCompat G e iw t) (hr : RatTup G iw) : RatBasis G e := by
  intro L hL v s
  obtain ⟨a, ha⟩ := hr L hL
  refine ⟨Matrix.GeneralLinearGroup.map (t v s) a, ?_⟩
  rw [ha v, Formalism.MainNotions.G.LatticeSystems.la_extO_G]
  congr 1
  ext j k
  simp [Formalism.MainNotions.G.LatticeSystems.la_tw, hp v s]

end Formalism.L2.G.Cmp
end
end

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.MainNotions.G.LatticeSystems

section Local

variable {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
  [IsFractionRing W Qq] {k : ℕ}

theorem den_one (π : W) (hπ : Irreducible π) (x : Qq) :
    ∃ (n : ℕ) (c : W), algebraMap W Qq π ^ n * x = algebraMap W Qq c := by
  obtain ⟨⟨c, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors W) x
  have hs0 : (s : W) ≠ 0 := nonZeroDivisors.ne_zero s.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hπ
  refine ⟨n, ((u⁻¹ : Wˣ) : W) * c, ?_⟩
  simp only at hs
  rw [hu, map_mul, map_pow] at hs
  have hu' : algebraMap W Qq (u : W) * algebraMap W Qq ((u⁻¹ : Wˣ) : W) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [map_mul]
  linear_combination algebraMap W Qq ((u⁻¹ : Wˣ) : W) * hs - algebraMap W Qq π ^ n * x * hu'

theorem den_mat (π : W) (hπ : Irreducible π) (h : Matrix (Fin k) (Fin k) Qq) :
    ∃ (N : ℕ) (H : Matrix (Fin k) (Fin k) W), algebraMap W Qq π ^ N • h = H.map (algebraMap W Qq) := by
  choose nn cc hnc using fun i j => den_one π hπ (h i j)
  refine ⟨∑ i, ∑ j, nn i j, Matrix.of fun i j => π ^ (∑ i, ∑ j, nn i j - nn i j) * cc i j, ?_⟩
  ext i j
  have hle : nn i j ≤ ∑ i, ∑ j, nn i j :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (nn i j)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, nn i j) (fun i _ => Nat.zero_le _) (Finset.mem_univ i))
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Matrix.of_apply, map_mul, map_pow, ← hnc i j]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem colSpan_mul_le (g : Matrix (Fin k) (Fin k) Qq) (U : Matrix (Fin k) (Fin k) W) :
    colSpan W (g * U.map (algebraMap W Qq)) ≤ colSpan W g := by
  unfold colSpan
  rw [Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have h : (fun i => (g * U.map (algebraMap W Qq)) i c) = ∑ b, U b c • (fun i => g i b) := by
    funext i
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  show (fun i => (g * U.map (algebraMap W Qq)) i c) ∈ Submodule.span W (Set.range fun c : Fin k => fun i => g i c)
  rw [h]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem colSpan_mul_unit (g : Matrix (Fin k) (Fin k) Qq) (U : Matrix (Fin k) (Fin k) W) (hU : IsUnit U.det) :
    colSpan W (g * U.map (algebraMap W Qq)) = colSpan W g := by
  apply le_antisymm (colSpan_mul_le g U)
  have h := colSpan_mul_le (g * U.map (algebraMap W Qq)) U⁻¹
  rwa [Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv U hU, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.mul_one] at h

theorem det_one_add_unit (π : W) (hπ : Irreducible π) (D : Matrix (Fin k) (Fin k) W) : IsUnit (1 + π • D).det := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hπ0 : IsLocalRing.residue W π = 0 :=
    (IsLocalRing.residue_eq_zero_iff π).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit)
  have h1 : (IsLocalRing.residue W).mapMatrix (1 + π • D) = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, hπ0, zero_mul, add_zero, Matrix.one_apply]
    split_ifs <;> simp
  rw [h1, Matrix.det_one]
  exact one_ne_zero

theorem approx_local (π : W) (hπ : Irreducible π) (g : Matrix (Fin k) (Fin k) Qq) (hg : IsUnit g.det) :
    ∃ N : ℕ, ∀ N', N ≤ N' → ∀ (A : Matrix (Fin k) (Fin k) Qq) (C : Matrix (Fin k) (Fin k) W),
      A = g + algebraMap W Qq π ^ N' • C.map (algebraMap W Qq) → colSpan W A = colSpan W g ∧ IsUnit A.det := by
  obtain ⟨N, H, hH⟩ := den_mat π hπ g⁻¹
  refine ⟨N + 1, fun N' hN A C hA => ?_⟩
  have hU : IsUnit (1 + π • (π ^ (N' - (N + 1)) • (H * C))).det := det_one_add_unit π hπ _
  have hAU : A = g * (1 + π • (π ^ (N' - (N + 1)) • (H * C))).map (algebraMap W Qq) := by
    rw [hA, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, map_pow, ← hH,
      Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv g hg, Matrix.one_mul, smul_smul, smul_smul]
    congr 2
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  refine ⟨by rw [hAU]; exact colSpan_mul_unit g _ hU, ?_⟩
  rw [hAU, Matrix.det_mul]
  refine hg.mul ?_
  have h2 : ((1 + π • (π ^ (N' - (N + 1)) • (H * C))).map (algebraMap W Qq)).det =
      algebraMap W Qq (1 + π • (π ^ (N' - (N + 1)) • (H * C))).det := by
    rw [RingHom.map_det]; rfl
  rw [h2]
  exact hU.map _

end Local

variable {p : ℕ} (G : GAtP p) {E : Type} [Field E] (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v)

def WeakApprox : Prop :=
  ∀ (x : ∀ v, G.P.Qq v) (N : ℕ), ∃ a : E, ∀ v, ∃ c : G.P.W v,
    iw v a = x v + (p : G.P.Qq v) ^ N * algebraMap (G.P.W v) (G.P.Qq v) c

theorem ratTup_of_weak (h : WeakApprox G iw) : RatTup G iw := by
  intro L hL
  by_cases hne : Nonempty (Fin G.P.nV)
  swap
  · exact ⟨1, fun v => (hne ⟨v⟩).elim⟩
  choose g hg hLg using hL
  have := fun v => (G.P.setting v).frac_alt
  choose N hN using fun v => approx_local (p : G.P.W v) (G.P.setting v).p_unif (g v) (hg v)
  choose a c hac using fun x y => h (fun v => g v x y) (∑ v, N v)
  have key : ∀ v, colSpan (G.P.W v) ((Matrix.of a).map (iw v)) = colSpan (G.P.W v) (g v) ∧
      IsUnit ((Matrix.of a).map (iw v)).det := fun v =>
    hN v (∑ v, N v) (Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v))
      ((Matrix.of a).map (iw v)) (fun x y => c x y v) (by
        ext x y
        simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_natCast]
        exact hac x y v)
  obtain ⟨v0⟩ := hne
  have hdet : IsUnit (Matrix.of a).det := by
    have h1 := (key v0).2
    have h2 : ((Matrix.of a).map (iw v0)).det = iw v0 (Matrix.of a).det := by
      rw [RingHom.map_det]; rfl
    rw [h2] at h1
    rw [isUnit_iff_ne_zero] at h1 ⊢
    intro h0
    exact h1 (by rw [h0, map_zero])
  exact ⟨Matrix.nonsingInvUnit (Matrix.of a) hdet, fun v => by rw [hLg v]; exact (key v).1.symm⟩

end Formalism.L2.G.Cmp
end
end
