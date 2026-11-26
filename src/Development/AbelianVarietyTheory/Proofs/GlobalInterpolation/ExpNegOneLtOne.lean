module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BranchesAlongOfIrreducible
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedExplicitFormula
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowSubPowLt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpNegOneLtOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.TameVal

open Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem exp_neg_one_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num

theorem locK_eq_of_tame (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) (x y : Lˣ)
    (hxy : v.valuation L ((y : L) - x) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (x : L)) :
    χ.locK v y = χ.locK v x := _root_.GlobalTheory.GalToHecke.locK_eq_of_tame (v := v) χ h x y hxy

theorem exists_approx (S : Finset (HeightOneSpectrum (𝓞 L))) (t : HeightOneSpectrum (𝓞 L) → 𝓞 L)
    (ht : ∀ v, t v ≠ 0) : ∃ y : 𝓞 L, ∀ v ∈ S,
      v.valuation L ((y : L) - (t v : L)) ≤ WithZero.exp (-1 : ℤ) * v.valuation L (t v : L) := by
  have hn : ∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, v.intValuation (t v) = WithZero.exp (-(n : ℤ)) :=
    fun v => ⟨_, v.intValuation_if_neg (ht v)⟩
  choose n hn using hn
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun v => n v + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => t v.1)
  refine ⟨y, fun v hv => ?_⟩
  have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v hv)
  have e1 : v.valuation L ((y : L) - (t v : L)) = v.intValuation (y - t v) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := L)]; simp
  have e2 : v.valuation L (t v : L) = v.intValuation (t v) := HeightOneSpectrum.valuation_of_algebraMap (K := L) v _
  rw [e1, e2, hn, ← WithZero.exp_add]
  convert h1 using 2
  push_cast; ring

theorem locK_mem (χ : HChar L) (G : Subgroup ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (htame : ∀ v, χ.TameAt v) (hunr : ∀ v, v ∉ T → χ.UnrAt v) (hval : ∀ v, v ∉ T → χ.val v ∈ G)
    (hinf : ∀ k, χ.inf k ∈ G) (P : HeightOneSpectrum (𝓞 L)) (x : Lˣ) : χ.locK P x ∈ G := by
  classical
  have hpr : χ.ProductRule := GlobalTheory.Mem.Chr.CharModel.productRule (F := L) ⟨χ.1, χ.2⟩
  have key : ∀ (a : 𝓞 L) (ha : (a : L) ≠ 0), χ.locK P (Units.mk0 (a : L) ha) ∈ G := by
    intro a ha
    have ha' : a ≠ 0 := fun h => ha (by simp [h])
    obtain ⟨y, hy⟩ := exists_approx (insert P T) (fun v => if v = P then a else 1)
      (fun v => by split_ifs; exacts [ha', one_ne_zero])
    have hP := hy P (Finset.mem_insert_self _ _)
    simp only [if_true] at hP
    have hy0 : (y : L) ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg] at hP
      have hpos : 0 < P.valuation L (a : L) := zero_lt_iff.2 (by simpa using ha')
      have := mul_lt_mul_of_pos_right exp_neg_one_lt_one hpos
      rw [one_mul] at this
      exact absurd hP (not_le.2 this)
    have e1 : χ.locK P (Units.mk0 (y : L) hy0) = χ.locK P (Units.mk0 (a : L) ha) :=
      locK_eq_of_tame χ (htame P) _ _ hP
    have e2 : ∏ v ∈ insert P T, χ.locK v (Units.mk0 (y : L) hy0) = χ.locK P (Units.mk0 (y : L) hy0) := by
      refine Finset.prod_eq_single P (fun v hv hne => ?_) (fun h => absurd (Finset.mem_insert_self _ _) h)
      have h1 := hy v hv
      simp only [if_neg hne] at h1
      rw [locK_eq_of_tame χ (htame v) 1 _ (by simpa using h1), map_one]
    have h := hpr (insert P T) (fun v hv => hunr v fun h => hv (Finset.mem_insert_of_mem h)) (Units.mk0 (y : L) hy0)
    rw [e2, e1] at h
    have hF : (∏ᶠ (v : HeightOneSpectrum (𝓞 L)) (_ : v ∉ insert P T),
        χ.val v ^ ordF v (Units.mk0 (y : L) hy0)) ∈ G :=
      finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun v =>
        finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun hv =>
          G.zpow_mem (hval v fun h => hv (Finset.mem_insert_of_mem h)) _
    have h1 : _ ∈ G := h ▸ G.one_mem
    rw [G.mul_mem_cancel_right hF, G.mul_mem_cancel_left (hinf _)] at h1
    exact h1
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 L) (x : L)
  have hb0 : (b : L) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
  have ha0 : (a : L) ≠ 0 := by
    intro h
    apply x.ne_zero
    rw [← hab]
    change (a : L) / _ = 0
    rw [h, zero_div]
  have hx : x = Units.mk0 (a : L) ha0 * (Units.mk0 (b : L) hb0)⁻¹ := by
    apply Units.ext
    rw [← hab, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]; rfl
  rw [hx, map_mul, map_inv]
  exact G.mul_mem (key a ha0) (G.inv_mem (key b hb0))

def unitsIn (M : Subfield ℂ) : Subgroup ℂˣ where
  carrier := {u | (u : ℂ) ∈ M}
  one_mem' := M.one_mem
  mul_mem' := fun ha hb => M.mul_mem ha hb
  inv_mem' := fun {a} ha => by
    change ((a⁻¹ : ℂˣ) : ℂ) ∈ M
    rw [Units.val_inv_eq_inv_val]; exact M.inv_mem ha

theorem sq_div_norm {z : ℂ} (hz : z ≠ 0) : (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 : ℤ) = z / starRingEnd ℂ z := by
  have h1 : z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' z
  have h2 : starRingEnd ℂ z ≠ 0 := (map_ne_zero _).2 hz
  rw [zpow_ofNat, div_pow, ← h1]
  field_simp

end GlobalTheory.TameVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemUnitOff
section -- merged from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.InfiniteGroup
noncomputable section
namespace GlobalTheory.LvT.LevModel
open Formalism.BasicNotions Classical

section Pairs

variable {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ}

lemma mem_std (x : Fin n → Lc.K) : x ∈ Lc.std n ↔ ∀ a, x a ∈ Lc.O := by
  simp only [LocF.std, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨x a, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact y.2

def stdPair (Lc : LocF q F) (a : Fin n) : LocF.PP Lc n :=
  ⟨⟨Lc.std n, fun x => if h : x ∈ Lc.std n then Lc.res ⟨x a, (mem_std x).1 h a⟩ else 0⟩,
   { lat := ⟨1, fun x => by simp⟩
     add := fun x hx y hy => by
       dsimp only at hx hy ⊢
       rw [dif_pos hx, dif_pos hy, dif_pos ((Lc.std n).add_mem hx hy), ← map_add (f := _)]; rfl
     smul := fun c x hx => by
       dsimp only at hx ⊢
       rw [dif_pos hx, dif_pos ((Lc.std n).smul_mem c hx), ← map_mul]; rfl
     off := fun x hx => dif_neg hx
     ne := by
       have h : (fun _ => 1 : Fin n → Lc.K) ∈ Lc.std n := (mem_std _).2 fun _ => Lc.O.one_mem
       refine ⟨fun _ => 1, ?_⟩
       dsimp only
       rw [dif_pos h]
       exact (map_one Lc.res).trans_ne one_ne_zero }⟩

def mvO (g : GL (Fin n) Lc.K) : (Fin n → Lc.K) →ₗ[Lc.O] (Fin n → Lc.K) :=
  (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) Lc.K)).restrictScalars Lc.O

lemma inv_mv (g : GL (Fin n) Lc.K) (x : Fin n → Lc.K) :
    mvO g⁻¹ (Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) x) = x := by
  show Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K)
    (Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) x) = x
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

def actPP (g : GL (Fin n) Lc.K) (p : LocF.PP Lc n) : LocF.PP Lc n :=
  ⟨⟨p.1.L.comap (mvO g⁻¹), fun x => p.1.f (mvO g⁻¹ x)⟩,
   { lat := by
       obtain ⟨h, hh⟩ := p.2.lat
       refine ⟨g * h, fun x => ?_⟩
       rw [← hh x, Units.val_mul, ← Matrix.mulVec_mulVec]
       show mvO g⁻¹ _ ∈ p.1.L ↔ _
       rw [inv_mv]
     add := fun x hx y hy => by
       show p.1.f (mvO g⁻¹ (x + y)) = _
       rw [map_add (f := _)]; exact p.2.add _ hx _ hy
     smul := fun c x hx => by
       show p.1.f (mvO g⁻¹ (c • x)) = _
       rw [map_smul]; exact p.2.smul c _ hx
     off := fun x hx => p.2.off _ hx
     ne := by
       obtain ⟨x, hx⟩ := p.2.ne
       refine ⟨Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) x, ?_⟩
       show p.1.f (mvO g⁻¹ _) ≠ 0
       rwa [inv_mv] }⟩

theorem isAct_actPP (g : GL (Fin n) Lc.K) (p : LocF.PP Lc n) : LocF.PP.IsAct g p (actPP g p) := by
  intro x
  refine ⟨?_, ?_⟩
  · show mvO g⁻¹ _ ∈ p.1.L ↔ _
    rw [inv_mv]
  · show p.1.f (mvO g⁻¹ _) = _
    rw [inv_mv]

private lemma mulVec_mvO_inv (g : GL (Fin n) Lc.K) (y : Fin n → Lc.K) :
    Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) (mvO g⁻¹ y) = y := by
  show Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K)
    (Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) y) = y
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem isAct_unique {g : GL (Fin n) Lc.K} {p p₁ p₂ : LocF.PP Lc n} (h₁ : LocF.PP.IsAct g p p₁)
    (h₂ : LocF.PP.IsAct g p p₂) : p₁ = p₂ := by
  apply Subtype.ext
  apply LocF.Raw.ext
  · ext y
    rw [← mulVec_mvO_inv g y, (h₁ _).1, (h₂ _).1]
  · funext y
    rw [← mulVec_mvO_inv g y, (h₁ _).2, (h₂ _).2]

end Pairs

variable {D : D7} {u : D.what₂.Word}

end GlobalTheory.LvT.LevModel
end
end

noncomputable section

namespace GlobalTheory.LvT.Inh

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)

instance mulActPP {q : ℕ} {F : Type} [Field F] (Lc : LocF q F) (n : ℕ) : MulAction (GL (Fin n) Lc.K) (LocF.PP Lc n) where
  smul := LevModel.actPP
  one_smul p := LevModel.isAct_unique (LevModel.isAct_actPP 1 p) (fun x => by simp)
  mul_smul g h p := LevModel.isAct_unique (LevModel.isAct_actPP (g * h) p) (fun x => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    have h1 := LevModel.isAct_actPP g (LevModel.actPP h p) (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) x)
    have h2 := LevModel.isAct_actPP h p x
    exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)

def valO {K : Type} [Field K] [NumberField K] (Q : HeightOneSpectrum (𝓞 K)) : Subring K :=
  (Q.valuation K).valuationSubring.toSubring

theorem mem_valO {K : Type} [Field K] [NumberField K] (Q : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ valO Q ↔ Q.valuation K x ≤ 1 :=
  Iff.rfl

def unitGL (K : Type) [Field K] [StarRing K] (n : ℕ) : Subgroup (GL (Fin n) K) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) K)ᴴ * (g : Matrix (Fin n) (Fin n) K) = 1}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [Units.val_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (g : Matrix (Fin n) (Fin n) K), hg,
      Matrix.one_mul, hh]
  inv_mem' {g} hg := by
    simp only [Set.mem_setOf_eq] at hg ⊢
    have h1 : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K)ᴴ := by
      rw [← Matrix.one_mul ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ← hg, Matrix.mul_assoc, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [h1, Matrix.conjTranspose_conjTranspose, ← h1, ← Units.val_mul, mul_inv_cancel, Units.val_one]

structure Ar (D : D7) (T : ℕ) [Fact T.Prime] where
  Lc : LocF T (ZMod T)
  [st : StarRing Lc.K]
  j : Lc.K →+* D.what₂.LL
  j_star : ∀ x, D.what₂.embLL (j (star x)) = starRingEnd ℂ (D.what₂.embLL (j x))
  seen : D.what₂.places.Pl → Bool
  int_on : ∀ w, D.what₂.places.resChar w = T → ∀ x, j (if seen w then x else star x) ∈ Ow D w ↔ x ∈ Lc.O
  Γ : ∀ n, Subgroup (GL (Fin n) Lc.K)
  unit : ∀ n, Γ n ≤ unitGL Lc.K n
  int_off : ∀ n, ∀ g ∈ Γ n, ∀ w, D.what₂.places.resChar w ≠ T → ∀ a b, j ((g : Matrix (Fin n) (Fin n) Lc.K) a b) ∈ Ow D w
  free : ∀ n, ∀ g ∈ Γ n, ∀ p : LocF.PP Lc n, g • p = p → g = 1
  fin : ∀ n, Finite (MulAction.orbitRel.Quotient (Γ n) (LocF.PP Lc n))

attribute [instance] Ar.st

end GlobalTheory.LvT.Inh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemDualSetOfMemSpan
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.DualFrame

theorem _root_.GlobalTheory.DualFrame.hform_eq_dot {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y : n → A) : _root_.Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [_root_.Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem _root_.GlobalTheory.DualFrame.hform_mulVec {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J B : Matrix n n A)
    (u y : n → A) : _root_.Formalism.UG.hform σ J (B *ᵥ u) y = (fun i => σ (u i)) ⬝ᵥ ((_root_.Formalism.UG.cT σ B * J) *ᵥ y) := by
  rw [_root_.GlobalTheory.DualFrame.hform_eq_dot, ← mulVec_mulVec, _root_.Formalism.UG.cT,
    dotProduct_mulVec (fun i => σ (u i)) (B.map σ)ᵀ, vecMul_transpose]
  congr 1
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem _root_.GlobalTheory.DualFrame.mem_dualSet_of_mem_span {E n : Type} [Field E] [NumberField E] [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (L : Submodule (𝓞 E) (n → E)) {y : n → E}
    (hy : y ∈ Submodule.span (𝓞 E) (_root_.Formalism.BasicNotions.dualSet σ J L)) : y ∈ _root_.Formalism.BasicNotions.dualSet σ J L := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact hz
  | zero =>
    intro x _
    rw [_root_.GlobalTheory.DualFrame.hform_eq_dot, mulVec_zero, dotProduct_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    intro x hx
    rw [_root_.GlobalTheory.DualFrame.hform_eq_dot, mulVec_add, dotProduct_add,
      ← _root_.GlobalTheory.DualFrame.hform_eq_dot, ← _root_.GlobalTheory.DualFrame.hform_eq_dot]
    exact add_mem (ha x hx) (hb x hx)
  | smul a z _ hz =>
    intro x hx
    have hsm : a • z = algebraMap (𝓞 E) E a • z := (algebraMap_smul E a z).symm
    rw [hsm, _root_.GlobalTheory.DualFrame.hform_eq_dot, mulVec_smul, dotProduct_smul,
      ← _root_.GlobalTheory.DualFrame.hform_eq_dot, smul_eq_mul]
    exact mul_mem ⟨a, rfl⟩ (hz x hx)

private theorem mulVec_mem_latticeCompletion_iff {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) {k : ℕ}
    (L : Submodule (𝓞 E) (Fin k → E)) (P : GL (Fin k) E) (c : 𝓞 F) (hc : c ∉ v.asIdeal)
    (hint : ∀ x ∈ L, ∀ i, algebraMap F E c * (((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i ∈
      (algebraMap (𝓞 E) E).range)
    (hcol : ∀ j, (fun i => algebraMap F E c * (P : Matrix (Fin k) (Fin k) E) i j) ∈ L)
    (y : Fin k → E ⊗[F] v.adicCompletion F) :
    (P : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ y ∈
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L ↔ ∀ i, y i ∈ _root_.Formalism.BasicNotions.intV E v := by
  obtain ⟨u, hu, huc⟩ := _root_.GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one (E := E) v c hc
  have hgen : ∀ x ∈ L, (fun i => _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (x i)) ∈
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L := by
    intro x hx
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat _root_.Formalism.UG.latS
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  have hsmul : ∀ s ∈ _root_.Formalism.BasicNotions.intV E v, ∀ z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L,
      (fun i => s * z i) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L :=
    fun s hs z hz => Submodule.smul_mem _ (⟨s, hs⟩ : _root_.Formalism.BasicNotions.intV E v) hz
  constructor
  · intro h
    have key : ∀ z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L, ∀ i,
        (((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map
          (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ z) i ∈ _root_.Formalism.BasicNotions.intV E v := by
      intro z hz
      unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat _root_.Formalism.UG.latS at hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨x, hx, rfl⟩ := hw
        intro i
        obtain ⟨a, ha⟩ := hint x hx i
        have hmap := RingHom.map_mulVec (_root_.Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F))
          ((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) x i
        simp only [Function.comp_def] at hmap
        rw [← hmap]
        have : _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)
            ((((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i) =
            u * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E a) := by
          rw [ha, map_mul]
          linear_combination (-(_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)
            ((((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i))) * huc
        rw [this]
        refine mul_mem hu ?_
        unfold _root_.Formalism.UG.inclE
        rw [Algebra.TensorProduct.includeLeftRingHom_apply]
        exact _root_.GlobalTheory.OverCompare.tmul_mem_intV a
      | zero =>
        intro i
        rw [mulVec_zero]
        exact zero_mem _
      | add a b _ _ ha hb =>
        intro i
        rw [mulVec_add]
        exact add_mem (ha i) (hb i)
      | smul s z _ hz =>
        intro i
        rw [mulVec_smul]
        exact mul_mem s.2 (hz i)
    intro i
    have hy : y = ((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map
        (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ
        ((P : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ y) := by
      rw [mulVec_mulVec, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _),
        one_mulVec]
    rw [hy]
    exact key _ h i
  · intro hy
    have hsum : (P : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ y =
        ∑ j, fun i => (y j * u) * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)
          (algebraMap F E c * (P : Matrix (Fin k) (Fin k) E) i j) := by
      funext i
      simp only [mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, map_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination (-(y j * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)
        ((P : Matrix (Fin k) (Fin k) E) i j))) * huc
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact hsmul _ (mul_mem (hy j) hu) _ (hgen _ (hcol j))

theorem _root_.GlobalTheory.DualFrame.exists_dual_frames (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E) (hJ : IsUnit J.det)
    (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hsp : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ B C : GL (Fin k) (E ⊗[F] v.adicCompletion F),
      _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (v.adicCompletion F)) (B : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *
        J.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *
        (C : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) = 1 ∧
      (∀ y : Fin k → E ⊗[F] v.adicCompletion F,
        (B : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v Λ ↔
          ∀ i, y i ∈ _root_.Formalism.BasicNotions.intV E v) ∧
      ∀ y : Fin k → E ⊗[F] v.adicCompletion F,
        (C : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈
          _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v (Submodule.span (𝓞 E) (_root_.Formalism.BasicNotions.dualSet (σ : E →+* E) J Λ)) ↔ ∀ i, y i ∈ _root_.Formalism.BasicNotions.intV E v := by
  obtain ⟨B₀, c, hc, hint, hcol⟩ := _root_.GlobalTheory.SemiLocalFrame.exists_frame_denominator F E k Λ hfin hsp v
  set σ' : E →+* E := (σ : E →+* E) with hσ'
  have hσc : σ' (algebraMap F E c) = algebraMap F E c := σ.commutes _
  have hdet : (_root_.Formalism.UG.cT σ' (B₀ : Matrix (Fin k) (Fin k) E) * J).det ≠ 0 := by
    rw [det_mul, _root_.Formalism.UG.cT, det_transpose,
      show ((B₀ : Matrix (Fin k) (Fin k) E).map σ').det = σ' (B₀ : Matrix (Fin k) (Fin k) E).det from
        (RingHom.map_det σ' _).symm]
    exact mul_ne_zero ((map_ne_zero σ').mpr (B₀.isUnit.map Matrix.detMonoidHom).ne_zero) hJ.ne_zero
  set M : GL (Fin k) E := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hM
  have hMcoe : (M : Matrix (Fin k) (Fin k) E) = _root_.Formalism.UG.cT σ' (B₀ : Matrix (Fin k) (Fin k) E) * J := rfl
  have hconj : ∀ e : E, _root_.Formalism.UG.sigR σ (v.adicCompletion F) (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) e) =
      _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (σ' e) := by
    intro e
    simp [_root_.Formalism.UG.sigR, _root_.Formalism.UG.inclE, hσ']
  refine ⟨Matrix.GeneralLinearGroup.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) B₀,
    Matrix.GeneralLinearGroup.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) M⁻¹, ?_, ?_, ?_⟩
  · change _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (v.adicCompletion F))
        ((B₀ : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F))) *
        J.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *
        (((M⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E)).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) = 1
    have hT : _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (v.adicCompletion F))
        ((B₀ : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F))) =
        (_root_.Formalism.UG.cT σ' (B₀ : Matrix (Fin k) (Fin k) E)).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) := by
      simp only [_root_.Formalism.UG.cT, transpose_map, Matrix.map_map]
      congr 2
    rw [hT, ← Matrix.map_mul, ← Matrix.map_mul, ← hMcoe, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · exact mulVec_mem_latticeCompletion_iff v Λ B₀ c hc hint hcol
  · refine mulVec_mem_latticeCompletion_iff v _ M⁻¹ c hc ?_ ?_
    · intro y hy i
      have hyd := _root_.GlobalTheory.DualFrame.mem_dualSet_of_mem_span σ' J Λ hy
      have hx : (fun l => algebraMap F E c * (B₀ : Matrix (Fin k) (Fin k) E) l i) =
          (B₀ : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i (algebraMap F E c) := by
        funext l
        simp [mulVec_single, mul_comm]
      have hval := hyd _ (hcol i)
      rw [hx, _root_.GlobalTheory.DualFrame.hform_mulVec] at hval
      have hfun : (fun l => σ' ((Pi.single i (algebraMap F E c) : Fin k → E) l)) =
          (Pi.single i (algebraMap F E c) : Fin k → E) := by
        funext l
        by_cases hl : l = i
        · subst hl
          simp [hσc]
        · simp [hl]
      rw [hfun, single_dotProduct, ← hMcoe] at hval
      rwa [inv_inv]
    · intro j
      refine Submodule.subset_span ?_
      intro x hx
      set u := ((B₀⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x with hu
      have hxu : x = (B₀ : Matrix (Fin k) (Fin k) E) *ᵥ u := by
        rw [hu, mulVec_mulVec, Units.mul_inv, one_mulVec]
      have hw : (fun i => algebraMap F E c * ((M⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) i j) =
          ((M⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single j (algebraMap F E c) := by
        funext l
        simp [mulVec_single, mul_comm]
      obtain ⟨a, ha⟩ := hint x hx j
      rw [hxu, hw, _root_.GlobalTheory.DualFrame.hform_mulVec, ← hMcoe, mulVec_mulVec, Units.mul_inv, one_mulVec,
        dotProduct_single, ← hσc, ← map_mul, mul_comm, ← ha]
      exact ⟨⟨σ' a, (RingOfIntegers.isIntegral_coe a).map σ'.toIntAlgHom⟩, rfl⟩

end GlobalTheory.DualFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EquivariantMapEqSmul
open MvPolynomial NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance GlobalTheory.BranchFormula

namespace GlobalTheory.Branching

theorem equivariant_map_eq_smul : ∀ (n N : ℕ) (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n), Formalism.MainNotions.PrimeDegreeVariant.Interlace h lam sg → ∀ (φ φ' : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ), (∀ ψ, ψ = φ ∨ ψ = φ' → (∀ f ∈ nablaSq ℂ N lam, ψ f ∈ nablaSq ℂ n sg) ∧ ∀ (g : GL (Fin n) ℂ), ∀ f ∈ nablaSq ℂ N lam, ψ (sqAct ℂ N lam (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N h g) f) = sqAct ℂ n sg g (ψ f)) → (∃ f ∈ nablaSq ℂ N lam, φ' f ≠ 0) → ∃ c : ℂ, ∀ f ∈ nablaSq ℂ N lam, φ f = c • φ' f := by
  intro n N h lam sg hI φ φ' H hne
  let mk : ∀ ψ, (ψ = φ ∨ ψ = φ') → (resRep (MonoidHom.id (GL (Fin n) ℂ)) h lam).IntertwiningMap
      (smallRep (MonoidHom.id (GL (Fin n) ℂ)) sg) := fun ψ hψ =>
    ⟨ψ.restrict (H ψ hψ).1, fun g => LinearMap.ext fun f => Subtype.ext ((H ψ hψ).2 g f.1 f.2)⟩
  have h1 := (comult_id n N h lam sg).1 hI
  have hz : mk φ' (Or.inr rfl) ≠ 0 := by
    obtain ⟨f, hf, hf0⟩ := hne
    intro e
    apply hf0
    have := congrArg (fun F => ((F.toLinearMap ⟨f, hf⟩ : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ)) e
    exact this
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hz).1 h1 (mk φ (Or.inl rfl))
  refine ⟨c, fun f hf => ?_⟩
  have := congrArg (fun F => ((F.toLinearMap ⟨f, hf⟩ : nablaSq ℂ n sg) : MvPolynomial (Fin n × Fin n) ℂ)) hc
  exact this.symm

end GlobalTheory.Branching
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TupleChainSharpColumnValuationOfTwisted
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwSharp

variable {D : D7} {u : D.what₂.Word}

theorem weight_eq (X Y : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j)) :
    (X.fm.lam j τ).w a = (Y.fm.lam j τ).w a := by
  have h := (X.fm.lam_eq j hj τ a).trans (Y.fm.lam_eq j hj τ a).symm
  exact_mod_cast h

theorem weightSup_eq (X Y : Ch D u) (τ : D.what₂.Tau) : TauWeight X τ = TauWeight Y τ := by
  unfold TauWeight
  refine Finset.sup_congr rfl fun i hi => Finset.sup_congr rfl fun a _ => ?_
  rw [weight_eq X Y i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) τ a]

theorem exponent_eq (X Y : Ch D u) : ETpi X = ETpi Y := by
  unfold ETpi Wt; simp only [weightSup_eq X Y]

theorem tupleChainSharpColumnValuation_of_twisted : ∀ (D : D7) (u : D.what₂.Word) (Tw : TwForms D) (μ : D.what₂.Tup),
    Step0Tie Tw u μ → Conclusion5Sharp (tw Tw u μ) → TupleChainSharpColumnValuation Tw u μ := by
  intro D u Tw μ hT h w hw c n hc hn x hx
  have hw' : OverT (tw Tw u μ) w := hw.trans (Tw.A_T u μ).symm
  have hown : ET (own D u) w = EatT D u w := rfl
  have hE : ET (tw Tw u μ) w = EatT D u w := by
    rw [← hown]; unfold ET
    rw [exponent_eq (tw Tw u μ) (own D u)]
    show (if (Tw.fm u μ).seenP w = true then _ else _) = _
    rw [(hT w hw).1]
  obtain ⟨y, hy, e⟩ := h w hw' c n hc (hE ▸ hn) (Tw.e0 u μ x) ((hT w hw).2 x hx)
  refine ⟨y, hy, e.trans ?_⟩
  show _ • (D.chTw u μ).col ((Tw.fm u μ).emb 0 (Tw.e0 u μ x)) = _
  rw [Tw.embed_mul_block_embedding]

end GlobalTheory.LvT.TwSharp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLatticeVectorApproxAllFinitePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLatticeVectorApproxAllFinitePlaces
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverCompare

theorem exists_int_approx_all (F : Type) [Field F] [NumberField F] (T : ℕ) (hT : T ≠ 0)
    (t : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (ht : ∀ v, t v ∈ v.adicCompletionIntegers F) :
    ∃ ρ : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F), ∃ w ∈ v.adicCompletionIntegers F,
      t v = algebraMap F (v.adicCompletion F) (ρ : F) + T • w := by
  let a : FiniteAdeleRing (𝓞 F) F := ⟨t, Filter.Eventually.of_forall ht⟩
  obtain ⟨ρ, w, hw, e⟩ := Formalism.UG.P.csGlob_intAdApprox F (T : 𝓞 F) (by exact_mod_cast hT) a ht
  refine ⟨ρ, fun v => ⟨w v, hw v, ?_⟩⟩
  rw [map_natCast, ← nsmul_eq_mul] at e
  have h : a v = (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) ρ + T • w) v := by rw [← e]
  exact h

theorem exists_lattice_approx_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∀ (T : ℕ), T ≠ 0 → ∀ (y : ∀ v : HeightOneSpectrum (𝓞 F), Fin k → E ⊗[F] v.adicCompletion F), (∀ v, y v ∈ locLat v Λ) → ∃ x ∈ Λ, ∀ v : HeightOneSpectrum (𝓞 F), ∃ z ∈ locLat v Λ, y v = (fun i => inclE (F := F) (v.adicCompletion F) (x i)) + T • z := by
  intro F E _ _ _ _ _ k Λ hΛ T hT y hy
  obtain ⟨m, l, hl, H⟩ := GlobalTheory.T.exists_generators_mem_completedLattice_iff F E k Λ hΛ
  choose t ht hyt using fun v : HeightOneSpectrum (𝓞 F) =>
    (H (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring (y v)).1 (hy v)
  choose ρ hρ using fun j : Fin m =>
    exists_int_approx_all F T hT (fun v => t v j) (fun v => ht v j)
  refine ⟨∑ j, algebraMap (𝓞 F) (𝓞 E) (ρ j) • l j,
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hl j), fun v => ?_⟩
  choose w hw hwt using fun j => hρ j v
  refine ⟨fun i => ∑ j, l j i ⊗ₜ[F] w j,
    (H (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring _).2 ⟨w, hw, rfl⟩, ?_⟩
  rw [hyt v]
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, map_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hwt j, TensorProduct.tmul_add]
  congr 1
  · have h1 : algebraMap (𝓞 F) (𝓞 E) (ρ j) • l j i = (ρ j : F) • l j i := by
      rw [Algebra.smul_def, Algebra.smul_def]; rfl
    rw [h1, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    rfl
  · exact map_nsmul (TensorProduct.mk F E (v.adicCompletion F) (l j i)) T (w j)

end GlobalTheory.OverCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLatticeVectorApproxAllFinitePlacesStatement
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_vector_approx_all_finitePlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∀ (T : ℕ), T ≠ 0 → ∀ (y : ∀ v : HeightOneSpectrum (𝓞 F), Fin k → E ⊗[F] v.adicCompletion F), (∀ v, y v ∈ locLat v Λ) → ∃ x ∈ Λ, ∀ v : HeightOneSpectrum (𝓞 F), ∃ z ∈ locLat v Λ, y v = (fun i => inclE (F := F) (v.adicCompletion F) (x i)) + T • z := by
  first | exact @GlobalTheory.OverCompare.exists_lattice_approx_all | exact GlobalTheory.OverCompare.exists_lattice_approx_all | (intros; apply GlobalTheory.OverCompare.exists_lattice_approx_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RbSNumeric
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rbS_numeric {x E P X b k r m de Del lg : ℝ} (hx : 8 ≤ x) (hE0 : 0 < E) (hE : E ≤ x) (hP : 0 ≤ P)
    (hk0 : 0 ≤ k) (hk : k ≤ 2 * x ^ 5) (hr : r ≤ 2 * k) (hm : 2 ≤ m) (hde : E⁻¹ ≤ de)
    (hD0 : 0 ≤ Del) (hD : Del ≤ 2 * P) (hl0 : 0 ≤ lg) (hl : lg ≤ x) (hb : 0 < b)
    (hX : x ^ 16 ≤ X) (hPb : x ^ 22 * P ≤ b) :
    r * (x * b / X + k * (4 * Del)) * lg * (k * E / (m * de)) ≤ de * m * b := by
  have hx0 : 0 < x := by linarith
  have hxde : x⁻¹ ≤ de := (inv_anti₀ hE0 hE).trans hde
  have hde0 : 0 < de := lt_of_lt_of_le (inv_pos.mpr hx0) hxde
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX
  have h1 : k * E / (m * de) ≤ 2 * x ^ 7 := by
    calc k * E / (m * de) ≤ (2 * x ^ 5) * x / (1 * x⁻¹) := by
          gcongr
          linarith
      _ = 2 * x ^ 7 := by field_simp
  have h2 : x * b / X ≤ b / (8 * x ^ 14) := by
    calc x * b / X ≤ x * b / x ^ 16 := by gcongr
      _ = b / (x * x ^ 14) := by field_simp
      _ ≤ b / (8 * x ^ 14) := by gcongr
  have h3 : k * (4 * Del) ≤ b / (8 * x ^ 14) := by
    rw [le_div_iff₀ (by positivity)]
    have h128 : (128 : ℝ) ≤ x ^ 3 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 3)
    calc k * (4 * Del) * (8 * x ^ 14) ≤ (2 * x ^ 5) * (4 * (2 * P)) * (8 * x ^ 14) := by gcongr
      _ = 128 * (x ^ 19 * P) := by ring
      _ ≤ x ^ 3 * (x ^ 19 * P) := by gcongr
      _ = x ^ 22 * P := by ring
      _ ≤ b := hPb
  have hr' : r ≤ 4 * x ^ 5 := by linarith
  calc r * (x * b / X + k * (4 * Del)) * lg * (k * E / (m * de))
      ≤ (4 * x ^ 5) * (b / (8 * x ^ 14) + b / (8 * x ^ 14)) * x * (2 * x ^ 7) := by
        gcongr
    _ = x⁻¹ * 2 * b := by field_simp; ring
    _ ≤ de * m * b := by gcongr

theorem szRow_rbS : SzRow (fun C D L => ((D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * lA L ≤
    L.de2 * D.R.m * L.sc.b)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD hcD => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨x1, h1⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) 16 0 1 0 le_rfl (by linarith) one_pos
  obtain ⟨x2, h2⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 eps (22 + cD) 0 1 0 le_rfl he0 one_pos
  refine ⟨max 8 (max x1 x2), fun D L heps hx V => ?_⟩
  have hx8 : 8 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hx1 := h1 _ (le_trans ((le_max_left _ _).trans (le_max_right _ _)) hx)
  have hx2 := h2 _ (le_trans ((le_max_right _ _).trans (le_max_right _ _)) hx)
  simp only [zero_mul, add_zero, one_mul] at hx1 hx2
  have hx0 : 0 < L.sc.x := by linarith
  have hone : 1 ≤ L.sc.x := by linarith
  have hP : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hone hcD
  have hn : (0 : ℝ) < D.R.n := by
    have hn : 0 < D.R.n := by
      unfold Ranks.n
      have := D.R.two_le_m
      have := D.R.m_le_f
      omega
    exact_mod_cast hn
  beta_reduce
  unfold lA Scale.b' Scale.a
  rw [L.Sc_eq, V.Del_eq]
  refine rbS_numeric (P := L.sc.x ^ cD) hx8 (Real.rpow_pos_of_pos hx0 _) ?_ (by linarith) (Nat.cast_nonneg _)
    ?_ ?_ ?_ ?_ (by positivity) ?_ (Real.log_nonneg hone) ((Real.log_le_sub_one_of_pos hx0).trans (by linarith))
    (Real.exp_pos _) ?_ ?_
  · calc L.sc.x ^ L.sc.eps ≤ L.sc.x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hone (by linarith)
      _ = L.sc.x := Real.rpow_one _
  · refine V.ranks.2.2.1.2.trans ?_
    have : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ ((5 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hone (by push_cast; linarith)
    rw [Real.rpow_natCast] at this
    linarith
  · have h := D.R.m_add_three_le_k
    have : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
    exact_mod_cast this
  · exact_mod_cast D.R.two_le_m
  · rw [L.typeDensity_eq_card_div, le_div_iff₀ hn, ← Real.rpow_neg hx0.le]
    exact V.host.2.2.1
  · have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    simp only [Delv, Rat.cast_natCast]
    linarith
  · unfold Scale.X'
    rw [heps, ← Real.exp_log (pow_pos hx0 16), Real.log_pow]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  · unfold Scale.b Scale.L
    rw [heps, ← Real.rpow_natCast, ← Real.rpow_add hx0, Real.rpow_def_of_pos hx0]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaClosed
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.ExplicitFormulaClosed

theorem exists_open_eq_closed (f : ℂ → ℂ) (T : ℝ)
    (hfin : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - 0| ≤ T + 1 ∧ f ρ = 0}.Finite) :
    ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧
      {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - 0| ≤ T ∧ f ρ = 0} =
        {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ f ρ = 0} := by
  have h1 : ∀ᶠ T' in 𝓝[>] T, ∀ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - 0| ≤ T + 1 ∧ f ρ = 0},
      T < |ρ.im| → T' < |ρ.im| := by
    rw [Filter.eventually_all_finite hfin]
    intro ρ _
    by_cases h : T < |ρ.im|
    · exact ((eventually_lt_nhds h).filter_mono nhdsWithin_le_nhds).mono fun _ h' _ => h'
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' h
  have h2 : ∀ᶠ T' in 𝓝[>] T, T' < T + 1 :=
    (eventually_lt_nhds (by linarith)).filter_mono nhdsWithin_le_nhds
  have h3 : ∀ᶠ T' in 𝓝[>] T, T < T' := self_mem_nhdsWithin
  obtain ⟨T', a1, a2, a3⟩ := (h1.and (h2.and h3)).exists
  refine ⟨T', a3.le, a2.le, ?_⟩
  ext ρ
  simp only [Set.mem_setOf_eq, sub_zero] at a1 ⊢
  constructor
  · rintro ⟨b0, b1, b2, b3⟩
    exact ⟨b0, b1, by linarith, b3⟩
  · rintro ⟨b0, b1, b2, b3⟩
    refine ⟨b0, b1, ?_, b3⟩
    by_contra h
    have := a1 ρ ⟨b0, b1, by linarith, b3⟩ (not_le.1 h)
    linarith

theorem explicit_formula_closed : ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ‖GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  obtain ⟨C₂, hC₂, h₂⟩ := GlobalTheory.ZeroBand.zeros_band
  refine ⟨C₁ + C₂, fun q _ χ hχ u T hT hu => ?_⟩
  obtain ⟨T', hT1, hT2, hset⟩ := exists_open_eq_closed (DirichletCharacter.LFunction χ) T
    (GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult q χ 0 (T + 1)).1
  have e1 := (h₁ q χ hχ u T hT hu).2
  have e2 := (h₂ q χ hχ u T T' hT hu hT1 hT2).2
  have hz : zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ) =
      ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ DirichletCharacter.LFunction χ ρ = 0},
        ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ) := by
    rw [← hset]; rfl
  have hF := (GlobalTheory.Mem.An.ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  have hsub : {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ DirichletCharacter.LFunction χ ρ = 0} ⊆
      zerosIn χ 0 1 := by
    rintro ρ ⟨b0, b1, b2, b3⟩
    exact ⟨b0, b1, by rw [sub_zero]; exact b2.le, b3⟩
  have hZ : ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧
        DirichletCharacter.LFunction χ ρ = 0},
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ ≤
      zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
    unfold zsumR
    rw [finsum_mem_eq_finite_toFinset_sum _ hF, finsum_mem_eq_finite_toFinset_sum _ (hF.subset hsub)]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun ρ _ => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Set.Finite.toFinset_subset_toFinset.2 hsub)
        fun ρ _ _ => by positivity)
    rw [mul_one_div]; rfl
  have hZ0 : 0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) :=
    finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hB : 0 ≤ Real.log (q * u) := Real.log_nonneg (by nlinarith)
  have key : ∀ P Z Z' : ℂ, ‖P + Z'‖ ≤ ‖P + Z‖ + ‖Z' - Z‖ := by
    intro P Z Z'
    have : P + Z' = (P + Z) + (Z' - Z) := by ring
    rw [this]
    exact norm_add_le _ _
  rw [hz]
  refine (key _ _ _).trans ((add_le_add e1 e2).trans ?_)
  generalize (∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧
        DirichletCharacter.LFunction χ ρ = 0},
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) = Z at hZ ⊢
  generalize zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) = Z' at hZ hZ0 ⊢
  generalize u * Real.log (q * u * T) ^ 2 / T = A
  generalize Real.log (q * u) = B at hB ⊢
  have a1 : C₁ * (A + B + Z) ≤ C₁ * (A + B + Z') := mul_le_mul_of_nonneg_left (by linarith) hC₁.le
  have a2 : C₂ * A ≤ C₂ * (A + B + Z') := mul_le_mul_of_nonneg_left (by linarith) hC₂.le
  nlinarith

end GlobalTheory.ExplicitFormulaClosed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaClosedStatement
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_psi0_add_zsum_le : ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ‖GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)) := by
  first | exact @GlobalTheory.ExplicitFormulaClosed.explicit_formula_closed | exact GlobalTheory.ExplicitFormulaClosed.explicit_formula_closed | (intros; apply GlobalTheory.ExplicitFormulaClosed.explicit_formula_closed <;> assumption)
end
end
