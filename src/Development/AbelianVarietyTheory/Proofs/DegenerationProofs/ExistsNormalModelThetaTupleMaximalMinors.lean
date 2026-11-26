module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlobalGenerators
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOnAdmissibleModel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MaximalMinorsRegularAndUnitIffToric

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOfDividingMaximalMinor
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open Matrix GlobalTheory.ZH.DualLattice

noncomputable section
namespace GlobalTheory.ZH.MinorBundle

section Algebra

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : Subalgebra o Ω) {J : Type} [Fintype J] [DecidableEq J]

theorem dual_dual {G L : Matrix J J Ω} {t : Ω} (ht : t ≠ 0) (hL : L.det ≠ 0)
    (h : Submodule.span S (Set.range (t⁻¹ • G : Matrix J J Ω)) = dotDual S (Submodule.span S (Set.range L))) :
    G.det ≠ 0 ∧ Submodule.span S (Set.range (t • G⁻¹ᵀ : Matrix J J Ω)) = Submodule.span S (Set.range L) := by
  have h1 : L * (L⁻¹ᵀ)ᵀ = 1 := by rw [transpose_transpose, mul_nonsing_inv _ (Ne.isUnit hL)]
  have h2 : L⁻¹ᵀ * Lᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv _ (Ne.isUnit hL), transpose_one]
  rw [dotDual_span_rows S h1] at h
  have hG : G.det ≠ 0 := by
    have h3 : ∀ i, ∃ c : J → Ω, c ᵥ* (t⁻¹ • G) = L⁻¹ᵀ i := fun i => by
      obtain ⟨c, -, hc⟩ := (mem_span_rows S _ (L⁻¹ᵀ i)).1 (h.ge (Submodule.subset_span ⟨i, rfl⟩))
      exact ⟨c, hc⟩
    choose c hc using h3
    have h4 : Matrix.of c * (t⁻¹ • G) = L⁻¹ᵀ := by
      ext i j
      exact congrFun (hc i) j
    intro h0
    have h5 := congrArg det h2
    rw [← h4, det_mul, det_mul, det_smul, h0] at h5
    simp at h5
  refine ⟨hG, ?_⟩
  rw [← dotDual_span_rows S (smul_mul_smul_inv hG ht), h, dotDual_span_rows S h2]

theorem exists_inv {G : Matrix J J Ω} (hG : ∀ i j, G i j ∈ S) (h0 : G.det ≠ 0) (h1 : G.det⁻¹ ∈ S) :
    ∃ C : Matrix J J S, (Matrix.of fun i j => (⟨G i j, hG i j⟩ : S)) * C = 1 ∧ G⁻¹ = C.map S.val := by
  set G₀ : Matrix J J S := Matrix.of fun i j => (⟨G i j, hG i j⟩ : S)
  have e : G = S.val.toRingHom.mapMatrix G₀ := rfl
  have hd : (G₀.det : Ω) = G.det := by rw [e, ← RingHom.map_det]; rfl
  have hu : IsUnit G₀.det := IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (by
    show (G₀.det : Ω) * G.det⁻¹ = 1
    rw [hd, mul_inv_cancel₀ h0]))
  refine ⟨G₀⁻¹, mul_nonsing_inv _ hu, Matrix.inv_eq_right_inv ?_⟩
  have := congrArg S.val.toRingHom.mapMatrix (mul_nonsing_inv _ hu)
  rw [map_mul, map_one] at this
  exact this

theorem det_mem {G : Matrix J J Ω} (hG : ∀ i j, G i j ∈ S) : G.det ∈ S := by
  rw [det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hG _ _)

theorem span_eq_std {A B : Matrix J J Ω} (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) (h : B * A = 1) :
    Submodule.span S (Set.range A) = Submodule.span S (Set.range fun i => Pi.single i (1 : Ω)) := by
  have e : (fun i : J => (Pi.single i (1 : Ω) : J → Ω)) = (1 : Matrix J J Ω) := by
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [e]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact (mem_span_rows S _ _).2 ⟨A i, hA i, vecMul_one _⟩
  · rintro _ ⟨i, rfl⟩
    exact (mem_span_rows S _ _).2 ⟨B i, hB i, by rw [← h]; rfl⟩

end Algebra

section Padic

variable {p : ℕ} [Fact p.Prime] {J : Type} [Fintype J] [DecidableEq J]

def OA (p : ℕ) [Fact p.Prime] : Subalgebra ℤ (PadicAlgCl p) := subalgebraOfSubring (OO p).toSubring

theorem mem_OA (x : PadicAlgCl p) : x ∈ OA p ↔ ‖x‖ ≤ 1 := mem_OO_iff x

omit [DecidableEq J] in
theorem mem_span_OO (B : Matrix J J (PadicAlgCl p)) (v : J → PadicAlgCl p) :
    v ∈ Submodule.span (OO p) (Set.range B) ↔ ∃ c : J → PadicAlgCl p, (∀ i, ‖c i‖ ≤ 1) ∧ c ᵥ* B = v := by
  refine (Submodule.mem_span_range_iff_exists_fun (OO p) (v := (B : J → J → PadicAlgCl p))).trans ?_
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨fun i => c i, fun i => (mem_OO_iff _).1 (c i).2, by rw [vecMul_eq_sum]; rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun i => ⟨c i, (mem_OO_iff _).2 (hc i)⟩, by rw [vecMul_eq_sum]; rfl⟩

omit [DecidableEq J] in
theorem mem_span_OA (B : Matrix J J (PadicAlgCl p)) (v : J → PadicAlgCl p) :
    v ∈ Submodule.span (OA p) (Set.range B) ↔ v ∈ Submodule.span (OO p) (Set.range B) := by
  simp only [mem_span_OO, mem_span_rows, mem_OA]

theorem dual_dual_OO {G L : Matrix J J (PadicAlgCl p)} {t : PadicAlgCl p} (ht : t ≠ 0) (hL : L.det ≠ 0)
    (h : ∀ w, w ∈ Submodule.span (OO p) (Set.range G) ↔
      ∀ v ∈ Submodule.span (OO p) (Set.range L), ‖w ⬝ᵥ v‖ ≤ ‖t‖) :
    G.det ≠ 0 ∧ Submodule.span (OO p) (Set.range (t • G⁻¹ᵀ : Matrix J J (PadicAlgCl p))) =
      Submodule.span (OO p) (Set.range L) := by
  have ht' : 0 < ‖t‖ := norm_pos_iff.2 ht
  obtain ⟨h1, h2⟩ := dual_dual (OA p) (G := G) ht hL (by
    ext w
    have e1 : w ∈ Submodule.span (OA p) (Set.range (t⁻¹ • G : Matrix J J _)) ↔
        t • w ∈ Submodule.span (OO p) (Set.range G) := by
      rw [mem_span_OA, mem_span_OO, mem_span_OO]
      refine exists_congr fun c => and_congr_right fun _ => ?_
      rw [vecMul_smul, inv_smul_eq_iff₀ ht]
    rw [e1, h]
    refine forall_congr' fun v => ?_
    rw [mem_span_OA, mem_OA, smul_dotProduct, smul_eq_mul, norm_mul, mul_le_iff_le_one_right ht',
      dotProduct_comm])
  refine ⟨h1, ?_⟩
  ext v
  rw [← mem_span_OA, h2, mem_span_OA]

end Padic

section Val

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {J : Type} [Fintype J] [DecidableEq J]
  {K : Type} [Field K] {y : Sp K ⟶ M.Z} {ξ : M.Z}

omit [DecidableEq J] in
theorem val_vecMul (h : ∀ w, y w ⤳ ξ) {c : J → Ω} {B : Matrix J J Ω} (hc : ∀ i, c i ∈ M.O ξ)
    (hB : ∀ i j, B i j ∈ M.O ξ) :
    (fun j => M.val y ((c ᵥ* B) j)) = (fun i => M.val y (c i)) ᵥ* B.map (M.val y) := by
  ext j
  have := map_sum (RatModel.valHomOf y ξ h) (fun i => (⟨c i, hc i⟩ : M.O ξ) * ⟨B i j, hB i j⟩) Finset.univ
  simp only [map_mul, RatModel.valHomOf_apply] at this
  simpa [vecMul, dotProduct] using this

theorem val_det (h : ∀ w, y w ⤳ ξ) {B : Matrix J J Ω} (hB : ∀ i j, B i j ∈ M.O ξ) :
    M.val y B.det = (B.map (M.val y)).det := by
  set B₀ : Matrix J J (M.O ξ) := Matrix.of fun i j => ⟨B i j, hB i j⟩
  have e : B = (M.O ξ).val.toRingHom.mapMatrix B₀ := rfl
  have hd : (B₀.det : Ω) = B.det := by rw [e, ← RingHom.map_det]; rfl
  rw [← hd, ← RatModel.valHomOf_apply y ξ h, RingHom.map_det]
  rfl

theorem val_inv (h : Set.range y = {ξ}) {B : Matrix J J Ω} (hB : ∀ i j, B i j ∈ M.O ξ)
    (h0 : (B.map (M.val y)).det ≠ 0) :
    (∀ i j, B⁻¹ i j ∈ M.O ξ) ∧ B⁻¹.map (M.val y) = (B.map (M.val y))⁻¹ := by
  rw [← val_det (RatModel.specializes_of_range_eq h) hB] at h0
  have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.val_ne_zero_iff h ⟨_, det_mem _ hB⟩).1 h0)
  obtain ⟨C, hC, e⟩ := exists_inv (M.O ξ) hB hu.1 hu.2
  refine ⟨fun i j => e ▸ (C i j).2, (Matrix.inv_eq_right_inv ?_).symm⟩
  have := congrArg (RatModel.valHom y ξ h).mapMatrix hC
  rw [map_mul, map_one] at this
  rw [e]
  exact this

end Val

section Spec

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {J : Type} [Fintype J]
  {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {z ξ : M.Z}

theorem span_val_image (h : y (cPt p) = z) (hξ : Set.range (gPt p ≫ y) = {ξ}) {B : Matrix J J Ω}
    (hB : ∀ i j, B i j ∈ M.O ξ) :
    Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) ''
      (Submodule.span (M.O z) (Set.range B) : Submodule (M.O z) (J → Ω))) =
      Submodule.span (OO p) (Set.range (B.map (M.val (gPt p ≫ y)))) := by
  have hs : ξ ⤳ z := by
    obtain ⟨w, rfl⟩ : ξ ∈ Set.range (gPt p ≫ y) := hξ ▸ rfl
    exact RatModel.gPt_specializes h w
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (mem_span_rows _ _ _).1 hv
    exact (mem_span_OO _ _).2 ⟨_, fun i => RatModel.norm_val_le_one h (hc i),
      (val_vecMul (RatModel.specializes_of_range_eq hξ) (fun i => RatModel.O_le_of_specializes hs (hc i)) hB).symm⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨B i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩

end Spec

theorem eq_zero_of_divisible {X : Type} [AddCommGroup X] [Module.Free ℤ X] {m : ℕ} (hm : 2 ≤ m)
    (h : ∀ x : X, ∃ x', m • x' = x) (x : X) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  refine b.ext_elem fun i => ?_
  exfalso
  obtain ⟨x', hx⟩ := h (b i)
  have e := congrArg (fun v => b.repr v i) hx
  simp only [map_nsmul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same, nsmul_eq_mul] at e
  have := Int.eq_one_of_mul_eq_one_right (by positivity) e
  omega

section Main

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens}
  {R' : Subalgebra o Ω} {hR : S.R ≤ R'} {n a : ℕ} {GG : Fin n → S.J → R'}

theorem at_test (hR' : R' ≤ M.ringOn U₀) {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z}
    {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀) (hc : M.Cen U₀ z y) (hat : S.At M y y₀)
    (hgen : ∀ (y' : R' →+* PadicAlgCl p) (τ : S.Test p (y'.comp (Subalgebra.inclusion hR).toRingHom)),
      (∀ b : o, ‖y' (algebraMap o R' b)‖ ≤ 1) → ∀ w : S.J → PadicAlgCl p,
        w ∈ Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ τ.δ ^ a)
    {k : S.J → Fin n}
    (hk : M.Div (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k z)
    {t : PadicAlgCl p} (ht : ‖t‖ = τ.δ ^ a) {L : Matrix S.J S.J (PadicAlgCl p)} (hL : L.det ≠ 0)
    (hE : τ.E = Submodule.span (OO p) (Set.range L)) :
    ((Matrix.of fun i j => (GG (k i) j : Ω)).map (M.val (gPt p ≫ y))).det ≠ 0 ∧
      Submodule.span (OO p) (Set.range (t • ((Matrix.of fun i j => (GG (k i) j : Ω)).map (M.val (gPt p ≫ y)))⁻¹ᵀ :
        Matrix S.J S.J (PadicAlgCl p))) = τ.E := by
  have hξ := RatModel.range_eq_singleton (gPt p ≫ y) (IsLocalRing.closedPoint _)
  set ξ := (gPt p ≫ y) (IsLocalRing.closedPoint _)
  have hξU : ξ ∈ U₀ := hc.2 ⟨_, rfl⟩
  have hle : R' ≤ M.O ξ := hR'.trans (RatModel.ringOn_le_O hξU)
  let y' : R' →+* PadicAlgCl p := (RatModel.valHom _ ξ hξ).comp (Subalgebra.inclusion hle).toRingHom
  obtain rfl : y₀ = y'.comp (Subalgebra.inclusion hR).toRingHom := RingHom.ext fun x => hat x
  have h1 := hgen y' τ fun b => RatModel.norm_val_le_one hc.1 ((M.O z).algebraMap_mem b)
  have h2 : Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) =
      Submodule.span (OO p) (Set.range ((Matrix.of fun i j => (GG (k i) j : Ω)).map (M.val (gPt p ≫ y)))) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨m, rfl⟩
      rw [← span_val_image (B := Matrix.of fun i j => (GG (k i) j : Ω)) hc.1 hξ fun i j => hle (GG (k i) j).2]
      refine Submodule.subset_span ⟨fun j => (GG m j : Ω), ?_, rfl⟩
      have e := span_eq_span_minor (M.O z) (fun m j => (GG m j : Ω)) k hk.1 hk.2 one_ne_zero one_ne_zero
        (by simp) (by simp)
      simp only [div_one, inv_one, one_smul] at e
      exact e.le (Submodule.subset_span ⟨m, rfl⟩)
    · rintro _ ⟨i, rfl⟩
      exact ⟨k i, rfl⟩
  have ht0 : t ≠ 0 := norm_pos_iff.1 (ht ▸ pow_pos τ.δ_pos a)
  rw [h2, hE, ← ht] at h1
  rw [hE]
  exact dual_dual_OO ht0 hL h1

theorem exists_basis [ArithBase o Ω] {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)
    (h : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) :
    ∃ L : Matrix S.J S.J (PadicAlgCl p), L.det ≠ 0 ∧ τ.E = Submodule.span (OO p) (Set.range L) ∧
      (τ.yy.ker = ⊤ → ∀ i j, ‖L i j‖ ≤ 1) := by
  obtain ⟨B, l, α, hB, hdet, -, hl, -, -, hE⟩ := GlobalTheory.ZH.exists_adapted_basis_testLattice o Ω S p y₀ τ h
  refine ⟨Matrix.of fun i j => l i * B i j, ?_, hE, fun hker i j => ?_⟩
  · rw [det_mul_column]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => norm_pos_iff.1 (hl i ▸ Real.exp_pos _)) ?_
    exact norm_pos_iff.1 (hdet ▸ one_pos)
  · have h0 : α i = 0 := by
      refine eq_zero_of_divisible (m := S.r * S.N) (by nlinarith [S.N_ge, S.r_pos]) (fun x => ?_) _
      obtain ⟨g, hg⟩ := τ.yy_onto (QuotientAddGroup.mk x)
      have : g ∈ τ.yy.ker := hker ▸ AddSubgroup.mem_top g
      rw [AddMonoidHom.mem_ker, hg, QuotientAddGroup.eq_zero_iff] at this
      exact this
    have h1 : ‖l i‖ = 1 := by rw [hl, h0]; simp
    rw [Matrix.of_apply, norm_mul, h1, _root_.one_mul]
    exact hB i j

end Main

end GlobalTheory.ZH.MinorBundle

namespace GlobalTheory.ZH
open MinorBundle

theorem exists_isEE_of_hasDiv_minors : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (R' : Subalgebra o Ω) (hR : S.R ≤ R') (n a : ℕ) (GG : Fin n → S.J → R'), S.Over₀ M U₀ → R' ≤ M.ringOn U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → (∀ (p : ℕ) [Fact p.Prime] (y' : R' →+* PadicAlgCl p) (τ : S.Test p (y'.comp (Subalgebra.inclusion hR).toRingHom)), (∀ b : o, ‖y' (algebraMap o R' b)‖ ≤ 1) → ∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ τ.δ ^ a) → M.HasDiv (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) → ∃ EE : M.Lat S.J, S.IsEE M U₀ EE ∧ ∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω, w ∈ Submodule.span (M.O z) (Set.range fun k j => (GG k j : Ω) / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z := by
  intro o Ω _ _ _ _ S M U₀ R' hR n a GG hO hR' hLL hT hS hgen hd
  haveI : NeZero (S.r * S.N) := ⟨by nlinarith [S.N_ge, S.r_pos]⟩
  choose x₀ hx₀ using hO.div
  choose k hk using id hd
  have hpow : ∀ {z : M.Z} {x x' : S.Gam}, M.Div S.th x z → S.th x' ^ a / S.th x ^ a ∈ M.O z := fun h => by
    rw [← div_pow]
    exact pow_mem (h.2 _) a
  obtain ⟨EE, hEE⟩ := exists_lat_dual o Ω M S.J n (fun m j => (GG m j : Ω)) (fun z => S.th (x₀ z) ^ a)
    (fun z => ⟨pow_ne_zero _ (hx₀ z).1, ⟨_, M.isOpen_setOf_div S.th (x₀ z)⟩, hx₀ z,
      fun x hx => ⟨hpow (hx₀ x), hpow hx⟩⟩) hd
  have hmin : ∀ (z : M.Z) (x : S.Gam) (l : S.J → Fin n), M.Div S.th x z →
      M.Div (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) l z →
      Submodule.span (M.O z) (Set.range fun m j => (GG m j : Ω) / S.th x ^ a) =
        Submodule.span (M.O z) (Set.range ((S.th (x₀ z) ^ a)⁻¹ • Matrix.of fun i j => (GG (l i) j : Ω) :
          Matrix S.J S.J Ω)) := fun z x l hx hl =>
    span_eq_span_minor (M.O z) (fun m j => (GG m j : Ω)) l hl.1 hl.2 (pow_ne_zero _ hx.1)
      (pow_ne_zero _ (hx₀ z).1) (hpow (hx₀ z)) (hpow hx)
  have hE : ∀ (z : M.Z) (l : S.J → Fin n),
      M.Div (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) l z →
      EE.E z = Submodule.span (M.O z) (Set.range
        (S.th (x₀ z) ^ a • (Matrix.of fun i j => (GG (l i) j : Ω))⁻¹ᵀ : Matrix S.J S.J Ω)) := by
    intro z l hl
    obtain ⟨U, b, hz, hb, hU⟩ := EE.loc z
    rw [hU z hz]
    refine (dual_dual (M.O z) (pow_ne_zero _ (hx₀ z).1) hb ?_).2.symm
    rw [← hmin z _ l (hx₀ z) hl, ← hU z hz]
    ext w
    rw [hEE]
    exact forall₂_congr fun v _ => by rw [dotProduct_comm]
  have hval : ∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∀ x,
      M.val (gPt p ≫ y) (S.th x ^ a) = M.val (gPt p ≫ y) (S.th x) ^ a := fun z p _ y hc x =>
    map_pow (RatModel.valHom _ _ (RatModel.range_eq_singleton (gPt p ≫ y) (IsLocalRing.closedPoint _)))
      ⟨S.th x, RatModel.ringOn_le_O (hc.2 ⟨_, rfl⟩) (hO.le (S.th_mem x))⟩ a
  have hint : ∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p),
      M.Cen U₀ z y → S.At M y y₀ → ∀ b : o, ‖y₀ (algebraMap o S.R b)‖ ≤ 1 := fun z p _ y y₀ hc hat b => by
    rw [hat]
    exact RatModel.norm_val_le_one hc.1 ((M.O z).algebraMap_mem b)
  have hclosed : ∀ z ∈ U₀, IsClosed ({z} : Set M.Z) →
      (Matrix.det (Matrix.of fun i j => (GG (k z i) j : Ω)))⁻¹ ∈ M.O z := by
    intro z hz hcl
    obtain ⟨p, _, y, hc⟩ := (hLL.1 U₀ le_rfl hO.ne z hcl).1
    obtain ⟨y₀, hat, hy₀, ⟨τ⟩⟩ := hT z p y hc
    obtain ⟨hsup, hH⟩ := hS z p y y₀ τ hc hat
    obtain ⟨L, hL, hEL, hL1⟩ := exists_basis τ hy₀
    have hth : ∀ x, S.th x ∈ M.O z := fun x => RatModel.ringOn_le_O hz (hO.le (S.th_mem x))
    have hthi : ∀ x, S.th x ≠ 0 → (S.th x)⁻¹ ∈ M.O z := fun x hx => RatModel.ringOn_le_O hz (hO.th_unit x hx)
    have hker : τ.yy.ker = ⊤ := by
      rw [← hH, eq_top_iff, ← S.supp]
      exact AddSubgroup.closure_mono fun x hx => ⟨hx, fun x' => by
        rw [div_eq_mul_inv]
        exact mul_mem (hth x') (hthi x hx)⟩
    have hδ : τ.δ = 1 := ((hsup _).1 (hx₀ z)).symm.trans
      ((RatModel.norm_val_eq_one_iff hc.1 (hth _)).2 ((RatModel.isUnit_O_iff _).2 ⟨(hx₀ z).1, hthi _ (hx₀ z).1⟩))
    obtain ⟨h0, hsp⟩ := at_test hR' τ hc hat (hgen p) (hk z) (t := 1) (by simp [hδ]) hL hEL
    have hG : ∀ i j, (Matrix.of fun i j => (GG (k z i) j : Ω)) i j ∈ M.O z :=
      fun i j => RatModel.ringOn_le_O hz (hR' (GG _ _).2)
    set G := Matrix.of fun i j => (GG (k z i) j : Ω)
    have hinv : ∀ i j, (G.map (M.val (gPt p ≫ y)))⁻¹ᵀ i j ∈ OA p := by
      intro i j
      have := hsp.le (Submodule.subset_span ⟨i, rfl⟩)
      rw [hEL, mem_span_OO, one_smul] at this
      obtain ⟨c, hc1, hc2⟩ := this
      rw [← hc2]
      exact sum_mem fun m _ => mul_mem ((mem_OA _).2 (hc1 m)) ((mem_OA _).2 (hL1 hker m j))
    have h1 := (mem_OA _).1 (det_mem _ hinv)
    rw [det_transpose, det_nonsing_inv, Ring.inverse_eq_inv', norm_inv,
      ← val_det (RatModel.gPt_specializes hc.1) hG] at h1
    rw [← val_det (RatModel.gPt_specializes hc.1) hG] at h0
    have h2 := RatModel.norm_val_le_one hc.1 (det_mem _ hG)
    have h3 := (inv_le_one₀ (norm_pos_iff.2 h0)).1 h1
    exact ((RatModel.isUnit_O_iff _).1
      ((RatModel.norm_val_eq_one_iff hc.1 (det_mem _ hG)).1 (le_antisymm h2 h3))).2
  refine ⟨EE, ⟨fun z hz => ?_, fun z p _ y y₀ τ hc hat => ?_⟩, fun z x hx w => ?_⟩
  · haveI := hLL.2
    obtain ⟨z', ⟨hz'U, hz'⟩, hcl⟩ := nonempty_inter_closedPoints (Z := (U₀ : Set M.Z) ∩ closure {z})
      ⟨z, hz, subset_closure rfl⟩ (U₀.isOpen.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
    have hs : z ⤳ z' := specializes_iff_mem_closure.2 hz'
    have hG : ∀ i j, (Matrix.of fun i j => (GG (k z' i) j : Ω)) i j ∈ M.O z :=
      fun i j => RatModel.ringOn_le_O hz (hR' (GG _ _).2)
    obtain ⟨C, -, hC⟩ := exists_inv (M.O z) hG (hk z').1 (RatModel.O_le_of_specializes hs (hclosed z' hz'U hcl))
    rw [hE z _ ((hk z').of_specializes hs)]
    have hA := congrArg transpose (smul_mul_smul_inv (hk z').1 (pow_ne_zero a (hx₀ z).1))
    rw [transpose_mul, transpose_transpose, transpose_one] at hA
    refine span_eq_std (M.O z) (fun i j => ?_) (fun i j => ?_) (mul_eq_one_comm.1 hA)
    · rw [hC]
      exact mul_mem (pow_mem (RatModel.ringOn_le_O hz (hO.le (S.th_mem _))) a) (C j i).2
    · rw [← inv_pow]
      exact mul_mem (pow_mem (RatModel.ringOn_le_O hz (hO.th_unit _ (hx₀ z).1)) a) (hG j i)
  · obtain ⟨L, hL, hEL, -⟩ := exists_basis τ (hint z p y y₀ hc hat)
    obtain ⟨h0, hsp⟩ := at_test hR' τ hc hat (hgen p) (hk z) (t := M.val (gPt p ≫ y) (S.th (x₀ z) ^ a))
      (by rw [hval z p y hc, norm_pow, ((hS z p y y₀ τ hc hat).1 _).1 (hx₀ z)]) hL hEL
    have hξ := RatModel.range_eq_singleton (gPt p ≫ y) (IsLocalRing.closedPoint _)
    set ξ := (gPt p ≫ y) (IsLocalRing.closedPoint _)
    have hξU : ξ ∈ U₀ := hc.2 ⟨_, rfl⟩
    have hG : ∀ i j, (Matrix.of fun i j => (GG (k z i) j : Ω)) i j ∈ M.O ξ :=
      fun i j => RatModel.ringOn_le_O hξU (hR' (GG _ _).2)
    obtain ⟨h1, h2⟩ := val_inv hξ hG h0
    have hθ : S.th (x₀ z) ^ a ∈ M.O ξ := pow_mem (RatModel.ringOn_le_O hξU (hO.le (S.th_mem _))) a
    rw [hE z _ (hk z), span_val_image (B := S.th (x₀ z) ^ a • (Matrix.of fun i j => (GG (k z i) j : Ω))⁻¹ᵀ) hc.1 hξ
      fun i j => mul_mem hθ (h1 j i), ← hsp, ← h2]
    congr 2
    ext i j
    exact RatModel.val_mul (RatModel.specializes_of_range_eq hξ) hθ (h1 j i)
  · rw [hmin z x _ hx (hk z), ← hmin z _ _ (hx₀ z) (hk z)]
    exact hEE z w

end GlobalTheory.ZH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDualBundleGeneratorsAllThetaTests
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPointOfRingHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem exists_point_of_ringHom {o Ω K : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field K] (M : RatModel o Ω)
    {U : M.Z.Opens} (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty) (φ : M.ringOn U →+* K) :
    ∃ x : Sp K ⟶ M.Z, Set.range x ⊆ U ∧ (∀ a : M.ringOn U, φ a = M.val x a) ∧
      x ≫ M.s = spMap (φ.comp (algebraMap o _)) := by
  let ψ : Γ(M.Z, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (φ.comp (M.sectionsEquiv U hne).toRingHom)
  have hx := le_preimage_specMap_fromSpec hU ψ
  have hv : ∀ f, valR (Spec.map ψ ≫ hU.fromSpec) U f = φ (M.sectionsEquiv U hne f) := fun f => by
    rw [valR_eq _ U hx, valMap_specMap_fromSpec]
    rfl
  have hr := (top_le_preimage_iff _ _).1 hx
  refine ⟨Spec.map ψ ≫ hU.fromSpec, hr, fun a => ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := (M.sectionsEquiv U hne).surjective a
    rw [coe_sectionsEquiv, val_valF hr]
    exact (hv f).symm
  · rw [← Spec.map_preimage ((Spec.map ψ ≫ hU.fromSpec) ≫ M.s)]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
    rw [← valR_constFn M.s _ U hx, hv]
    exact congrArg φ (Subtype.ext ((coe_sectionsEquiv U hne _).trans (M.valF_constFn hne b)))

theorem exists_cen_of_ringHom : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (U : M.Z.Opens), IsProper M.s → IsAffineOpen U → (U : Set M.Z).Nonempty → ∀ (p : ℕ) [Fact p.Prime]
    (y' : M.ringOn U →+* PadicAlgCl p), (∀ b : o, ‖y' (algebraMap o _ b)‖ ≤ 1) →
    ∃ (z : M.Z) (y : Sp (OO p) ⟶ M.Z), M.Cen U z y ∧ ∀ a : M.ringOn U, y' a = M.val (gPt p ≫ y) a := by
  intro o Ω _ _ _ M U hs hU hne p _ y' hy'
  obtain ⟨x, hx, hv, hxs⟩ := M.exists_point_of_ringHom hU hne y'
  let σ : o →+* OO p := (y'.comp (algebraMap o _)).codRestrict (OO p).toSubring
    fun b => (mem_OO_iff _).2 (hy' b)
  obtain ⟨y, hy, -⟩ := exists_valuativeExtension (V := OO p) (K := PadicAlgCl p) M.s (spMap σ) x (by
    rw [hxs, ← Spec.map_comp]
    rfl)
  have hy2 : gPt p ≫ y = x := hy
  exact ⟨_, y, ⟨rfl, hy2 ▸ hx⟩, hy2 ▸ hv⟩

end GlobalTheory.ZH.RatModel
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

section Specialise

variable {o Ω K J : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field K] [Fintype J]

theorem map_dotProduct_of_mem {B : Subalgebra o Ω} {f : Ω → K} (φ : B →+* K) (hf : ∀ x : B, φ x = f x)
    {u v : J → Ω} (hu : ∀ j, u j ∈ B) (hv : ∀ j, v j ∈ B) :
    f (u ⬝ᵥ v) = (fun j => f (u j)) ⬝ᵥ fun j => f (v j) := by
  have h : u ⬝ᵥ v = ((∑ j, (⟨u j, hu j⟩ : B) * ⟨v j, hv j⟩ : B) : Ω) := by
    simp [dotProduct]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, ← hf, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hf, hf]

theorem dotProduct_mem_of_mem_span {σ : Type} [SetLike σ K] [SubringClass σ K] (O : σ) {s : Set (J → K)} {w v : J → K}
    (hs : ∀ x ∈ s, w ⬝ᵥ x ∈ O) (hv : v ∈ Submodule.span O s) : w ⬝ᵥ v ∈ O := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp
  | add x y _ _ hx hy => rw [dotProduct_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have : w ⬝ᵥ (c • x) = (c : K) * (w ⬝ᵥ x) := dotProduct_smul (c : K) w x
    rw [this]
    exact mul_mem c.2 hx

omit [Fintype J] in
theorem map_mem_span_of_mem_span {A B : Subalgebra o Ω} (hAB : A ≤ B) {f : Ω → K} (φ : B →+* K)
    (hf : ∀ x : B, φ x = f x) (O : ValuationSubring K) (hO : ∀ x ∈ A, f x ∈ O) {I : Type} {g : I → J → Ω}
    (hg : ∀ k j, g k j ∈ B) {v : J → Ω} (hv : v ∈ Submodule.span A (Set.range g)) :
    (∀ j, v j ∈ B) ∧ (fun j => f (v j)) ∈ Submodule.span O (Set.range fun k j => f (g k j)) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨hg k, Submodule.subset_span ⟨k, rfl⟩⟩
  | zero =>
    refine ⟨fun _ => zero_mem B, ?_⟩
    have h0 : f 0 = 0 := (hf 0).symm.trans (map_zero φ)
    have : (fun j => f ((0 : J → Ω) j)) = 0 := funext fun _ => h0
    rw [this]
    exact zero_mem _
  | add x y _ _ hx hy =>
    refine ⟨fun j => add_mem (hx.1 j) (hy.1 j), ?_⟩
    have : (fun j => f ((x + y) j)) = (fun j => f (x j)) + fun j => f (y j) := funext fun j =>
      (hf (⟨_, hx.1 j⟩ + ⟨_, hy.1 j⟩)).symm.trans (by rw [map_add (f := _), hf, hf]; rfl)
    rw [this]
    exact add_mem hx.2 hy.2
  | smul c x _ hx =>
    refine ⟨fun j => mul_mem (hAB c.2) (hx.1 j), ?_⟩
    have : (fun j => f ((c • x) j)) = (⟨f c, hO c c.2⟩ : O) • fun j => f (x j) := funext fun j =>
      (hf (⟨_, hAB c.2⟩ * ⟨_, hx.1 j⟩)).symm.trans (by rw [map_mul, hf, hf]; rfl)
    rw [this]
    exact Submodule.smul_mem _ _ hx.2

theorem mem_span_map_iff_forall_dotProduct_mem [DecidableEq J] {A B : Subalgebra o Ω} (hAB : A ≤ B) {f : Ω → K}
    (φ : B →+* K) (hf : ∀ x : B, φ x = f x) (O : ValuationSubring K) (hO : ∀ x ∈ A, f x ∈ O) {I : Type}
    {g : I → J → Ω} (hg : ∀ k j, g k j ∈ B) (b : Matrix J J Ω)
    (hb : Submodule.span B (Set.range b) = Submodule.span B (Set.range fun i => Pi.single i (1 : Ω)))
    (H : ∀ w : J → Ω, w ∈ Submodule.span A (Set.range g) ↔ ∀ v ∈ Submodule.span A (Set.range b), w ⬝ᵥ v ∈ A)
    (w : J → K) :
    w ∈ Submodule.span O (Set.range fun k j => f (g k j)) ↔
      ∀ v ∈ Submodule.span O ((fun (v : J → Ω) j => f (v j)) '' (Submodule.span A (Set.range b))), w ⬝ᵥ v ∈ O := by
  have hbB : ∀ i j, b i j ∈ B := fun i j => by
    have h : b i ∈ Submodule.span B (Set.range fun i => (Pi.single i (1 : Ω) : J → Ω)) :=
      hb ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h
    rw [← hc]
    simp [Finset.sum_apply, Pi.single_apply, Subalgebra.smul_def]
  constructor
  · intro hw v hv
    refine dotProduct_mem_of_mem_span O ?_ hv
    rintro _ ⟨x, hx, rfl⟩
    rw [dotProduct_comm]
    refine dotProduct_mem_of_mem_span O ?_ hw
    rintro _ ⟨k, rfl⟩
    rw [dotProduct_comm, ← map_dotProduct_of_mem φ hf (hg k) (map_mem_span_of_mem_span hAB φ hf O hO hbB hx).1]
    exact hO _ ((H _).1 (Submodule.subset_span ⟨k, rfl⟩) x hx)
  · intro hw
    have h1 : ∀ i, ∃ c : J → B, ∑ l, HSMul.hSMul (c l) (b l) = (Pi.single i 1 : J → Ω) := fun i =>
      (Submodule.mem_span_range_iff_exists_fun _).1 (hb ▸ Submodule.subset_span ⟨i, rfl⟩)
    choose c hc using h1
    let d : Matrix J J Ω := Matrix.of fun i l => (c i l : Ω)
    have hd : d * b = 1 := by
      ext i j
      have := congrFun (hc i) j
      simpa [Matrix.mul_apply, d, Finset.sum_apply, Subalgebra.smul_def, Matrix.one_apply, Pi.single_apply,
        eq_comm] using this
    have hd' : b * d = 1 := mul_eq_one_comm.1 hd
    have h2 : ∀ i, (fun j => d j i) ∈ Submodule.span A (Set.range g) := fun i => (H _).2 fun v hv => by
      refine dotProduct_mem_of_mem_span A ?_ hv
      rintro _ ⟨l, rfl⟩
      have : (fun j => d j i) ⬝ᵥ b l = (b * d) l i := dotProduct_comm _ _
      rw [this, hd', Matrix.one_apply]
      split_ifs
      exacts [one_mem A, zero_mem A]
    have h3 : ∀ i, w ⬝ᵥ (fun j => f (b i j)) ∈ O := fun i =>
      hw _ (Submodule.subset_span ⟨b i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩)
    have h4 : ∀ j l, ∑ i, f (d j i) * f (b i l) = if j = l then 1 else 0 := fun j l => by
      have h := map_dotProduct_of_mem φ hf (u := d j) (v := fun i => b i l) (fun i => (c j i).2) (fun i => hbB i l)
      have h' : d j ⬝ᵥ (fun i => b i l) = (d * b) j l := rfl
      rw [h', hd, Matrix.one_apply] at h
      refine h.symm.trans ?_
      split_ifs
      exacts [(hf 1).symm.trans (map_one φ), (hf 0).symm.trans (map_zero φ)]
    have h5 : w = ∑ i, (⟨_, h3 i⟩ : O) • fun j => f (d j i) := by
      funext j
      have : ∀ i, ((⟨_, h3 i⟩ : O) • fun j => f (d j i)) j = ∑ l, w l * (f (d j i) * f (b i l)) := fun i => by
        show (w ⬝ᵥ (fun j => f (b i j))) * f (d j i) = _
        rw [dotProduct, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [Finset.sum_apply, Finset.sum_congr rfl fun i _ => this i, Finset.sum_comm]
      simp only [← Finset.mul_sum, h4]
      simp
    rw [h5]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (map_mem_span_of_mem_span hAB φ hf O hO hg (h2 i)).2

omit [Fintype J] in
theorem mem_span_iff_div_mem_span (O : ValuationSubring K) {I : Type} (G : I → J → K) {u : K} (hu : u ≠ 0)
    (w : J → K) :
    w ∈ Submodule.span O (Set.range G) ↔ u⁻¹ • w ∈ Submodule.span O (Set.range fun k j => G k j / u) := by
  have key : ∀ (G : I → J → K) (s : K) (w : J → K), w ∈ Submodule.span O (Set.range G) →
      s • w ∈ Submodule.span O (Set.range fun k => s • G k) := fun G s w hw => by
    have := Submodule.mem_map_of_mem (f := (LinearMap.lsmul K (J → K) s).restrictScalars O) hw
    rwa [Submodule.map_span, ← Set.range_comp] at this
  have e : (fun k j => G k j / u) = fun k => u⁻¹ • G k := by
    funext k j
    simp [div_eq_inv_mul]
  rw [e]
  refine ⟨key G _ w, fun h => ?_⟩
  simpa [smul_smul, hu] using key _ u _ h

end Specialise

theorem exists_generators_at_all_tests : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (n a : ℕ) (GG₀ : Fin n → S.J → S.R), S.Over₀ M U₀ → IsAffineOpen U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → S.IsEE M U₀ EE → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω, w ∈ Submodule.span (M.O z) (Set.range fun k j => (GG₀ k j : Ω) / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z) → ∃ (R' : Subalgebra o Ω) (hR : S.R ≤ R') (GG : Fin n → S.J → R'), R'.FG ∧ (∀ k j, (GG k j : Ω) = GG₀ k j) ∧ (∀ (p : ℕ) [Fact p.Prime] (y' : R' →+* PadicAlgCl p) (τ : S.Test p (y'.comp (Subalgebra.inclusion hR).toRingHom)), (∀ b : o, ‖y' (algebraMap o R' b)‖ ≤ 1) → ∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ τ.δ ^ a) := by
  intro o Ω _ _ _ _ S M U₀ EE n a GG₀ hO hU hsupp hEE hgen
  refine ⟨M.ringOn U₀, hO.le, fun k j => ⟨GG₀ k j, hO.le (GG₀ k j).2⟩, RatModel.fg_ringOn hU hO.ne,
    fun _ _ => rfl, fun p _ y' τ hy' w => ?_⟩
  obtain ⟨z, y, hz, hv⟩ := RatModel.exists_cen_of_ringHom o Ω M U₀ (projProper _ _ _ hO.proj) hU hO.ne p y' hy'
  have hAt : S.At M y (y'.comp (Subalgebra.inclusion hO.le).toRingHom) := fun r => hv ⟨r, hO.le r.2⟩
  obtain ⟨x₀, hx₀⟩ := hO.div z
  have hδ := ((hsupp z p y _ τ hz hAt).1 x₀).1 hx₀
  obtain ⟨V, b, hzV, -, hb⟩ := EE.loc z
  let ξ : M.Z := (gPt p ≫ y) (IsLocalRing.closedPoint _)
  have hξ : ξ ⤳ z := RatModel.gPt_specializes hz.1 _
  have hξU : ξ ∈ U₀ := hz.2 ⟨_, rfl⟩
  have hle : M.ringOn U₀ ≤ M.O ξ := RatModel.ringOn_le_O hξU
  let φ := RatModel.valHom (gPt p ≫ y) ξ (RatModel.range_eq_singleton _ _)
  have ht : S.th x₀ ∈ M.O ξ := hle (hO.le (S.th_mem x₀))
  have ht' : (S.th x₀)⁻¹ ∈ M.O ξ := hle (hO.th_unit x₀ hx₀.1)
  have hg : ∀ k j, (GG₀ k j : Ω) / S.th x₀ ^ a ∈ M.O ξ := fun k j => by
    rw [div_eq_mul_inv, ← inv_pow]
    exact mul_mem (hle (hO.le (GG₀ k j).2)) (pow_mem ht' a)
  have H := hgen z x₀ hx₀
  have hE := hEE.2 z p y _ τ hz hAt
  rw [hb z hzV] at H hE
  have key := mem_span_map_iff_forall_dotProduct_mem (RatModel.O_le_of_specializes hξ) φ (fun _ => rfl) (OO p)
    (fun x hx => (mem_OO_iff _).2 (RatModel.norm_val_le_one hz.1 hx)) hg b
    ((hb ξ (hξ.mem_open V.isOpen hzV)).symm.trans (hEE.1 ξ hξU)) H
  set u := M.val (gPt p ≫ y) (S.th x₀) with hu
  have hu0 : u ^ a ≠ 0 := pow_ne_zero _ (norm_pos_iff.1 (hδ ▸ τ.δ_pos))
  have e : (fun k j => y' ⟨GG₀ k j, hO.le (GG₀ k j).2⟩ / u ^ a) =
      fun k j => M.val (gPt p ≫ y) ((GG₀ k j : Ω) / S.th x₀ ^ a) := by
    funext k j
    rw [div_eq_iff hu0, hv]
    have h := map_mul φ ⟨_, hg k j⟩ (⟨_, ht⟩ ^ a)
    rw [map_pow] at h
    refine Eq.trans ?_ h
    exact congrArg (M.val (gPt p ≫ y)) (div_mul_cancel₀ _ (pow_ne_zero a hx₀.1)).symm
  rw [mem_span_iff_div_mem_span (OO p) _ hu0, e]
  refine (key _).trans ?_
  rw [← hE]
  refine forall₂_congr fun v _ => ?_
  rw [mem_OO_iff, smul_dotProduct, smul_eq_mul, norm_mul, norm_inv, norm_pow, hδ,
    inv_mul_le_iff₀ (pow_pos τ.δ_pos a), _root_.mul_one]

end GlobalTheory.ZH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalModelThetaTupleMaximalMinors
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.MinorModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

variable (S : ThetaSys o Ω)

end GlobalTheory.ZH.MinorModel

namespace GlobalTheory.ZH

open MinorModel

private theorem exists_open_ringOn_contains_of_fg_of_finite {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    (M : _root_.GlobalTheory.ZH.RatModel o Ω) (A : Subalgebra o Ω) (hA : A.FG) (F : Set Ω)
    (hF : F.Finite) :
    ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ A ≤ M.ringOn U ∧ ∀ x ∈ F, x ∈ M.ringOn U := by
  obtain ⟨s, rfl⟩ := hA
  have hT : ((s : Set Ω) ∪ F).Finite := s.finite_toSet.union hF
  let U : M.Z.Opens := ⟨⋂ x ∈ (s : Set Ω) ∪ F, {z | x ∈ M.O z},
    hT.isOpen_biInter fun x _ => M.isOpen_setOf_mem_O x⟩
  have hU : ∀ x ∈ (s : Set Ω) ∪ F, x ∈ M.ringOn (U : Set M.Z) := fun x hx =>
    _root_.GlobalTheory.ZH.RatModel.mem_ringOn.2 fun z hz =>
      Set.mem_iInter₂.1 hz x hx
  refine ⟨U, ⟨genericPoint M.Z, ?_⟩, ?_, fun x hx => hU x (Or.inr hx)⟩
  · show genericPoint M.Z ∈ ⋂ x ∈ (s : Set Ω) ∪ F, {z | x ∈ M.O z}
    simp [M.O_genericPoint]
  · exact Algebra.adjoin_le fun x hx => hU x (Or.inl hx)

private theorem exists_open_over0_ringOn_of_fg {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    (S : _root_.GlobalTheory.ZH.ThetaSys o Ω) (M : _root_.GlobalTheory.ZH.RatModel o Ω) (R' : Subalgebra o Ω)
    (hfg : R'.FG) (hR : S.R ≤ R') (hn : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) (hp : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.s) (hd : M.HasDiv S.th) :
    ∃ U : M.Z.Opens, S.Over₀ M U ∧ R' ≤ M.ringOn U := by
  obtain ⟨U, hUne, hAU, hFU⟩ := exists_open_ringOn_contains_of_fg_of_finite M R' hfg
    (Set.range (fun x => (S.th x)⁻¹) ∪ Set.range (fun q : Σ T : AddSubgroup S.Gam,
      (T →+ ZMod S.N) × (S.J × (T → ZMod ((S.r * S.N) ^ 2))) => (S.FF q.1 q.2.1 q.2.2)⁻¹))
    ((Set.finite_range _).union (Set.finite_range _))
  exact ⟨U, ⟨hn, hp, hd, hUne, hR.trans hAU, fun x _ => hFU _ (Or.inl ⟨x, rfl⟩),
    fun T c k _ _ => hFU _ (Or.inr ⟨⟨T, c, k⟩, rfl⟩)⟩, hAU⟩

private theorem module_finite_of_subfield_le {Ω : Type} [Field Ω] {K K' : Subfield Ω} (h : K ≤ K')
    [Module.Finite K Ω] : Module.Finite K' Ω := by
  letI : Algebra K K' := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower K K' Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  exact Module.Finite.of_restrictScalars_finite K K' Ω

private theorem isProper_of_isProjOver_degeneration {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    (M : _root_.GlobalTheory.ZH.RatModel o Ω) (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver M.s) : IsProper M.s := by
  obtain ⟨N, i, hi, e⟩ := h
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str o N
  rw [← e]
  infer_instance

theorem _root_.GlobalTheory.ZH.exists_minor_model : ∀ (o Ω : Type) [CommRing o] [Field Ω]
    [Algebra o Ω] [_root_.GlobalTheory.ZH.ArithBase o Ω] (S : _root_.GlobalTheory.ZH.ThetaSys o Ω), S.HasTests →
    Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω →
    ∃ (n a : ℕ) (GG : Fin n → S.J → Ω) (X Z : _root_.GlobalTheory.ZH.RatModel o Ω) (U₀ : Z.Z.Opens)
      (EE : Z.Lat S.J) (f : Z.Z ⟶ X.Z) (Xab : X.Z.Opens), X.IsNm S.th ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver X.s ∧
      Z.IsNm (fun q : S.Gam × (S.J → Fin n) => S.th q.1 * Matrix.det (Matrix.of fun i j => GG (q.2 i) j)) ∧
      S.Over₀ Z U₀ ∧ S.IsEE Z U₀ EE ∧ X.IsHom Z (AlgHom.id o Ω) f ∧
      (Xab : Set X.Z) = {x | S.TT X x = ⊥} ∧ IsIso (f ∣_ Xab) ∧
      (∀ z : Z.Z, ∀ x₀ ∈ S.supI Z z, ∀ w : S.J → Ω,
        w ∈ Submodule.span (Z.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔
          ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ Z.O z) ∧
      ∀ z : Z.Z, ∀ x₀ ∈ S.supI Z z,
        (∀ k : S.J → Fin n, Matrix.det (Matrix.of fun i j => GG (k i) j) / S.th x₀ ^ (a * Fintype.card S.J) ∈ Z.O z) ∧
        (S.TT Z z = ⊥ ↔ ∃ k : S.J → Fin n, Matrix.det (Matrix.of fun i j => GG (k i) j) ≠ 0 ∧
          S.th x₀ ^ (a * Fintype.card S.J) / Matrix.det (Matrix.of fun i j => GG (k i) j) ∈ Z.O z) := by
  intro o Ω _ _ _ _ S hT hfin
  haveI : Algebra.FiniteType ℤ o := _root_.GlobalTheory.ZH.ArithBase.ft (o := o) Ω
  haveI : CharZero Ω := _root_.GlobalTheory.ZH.ArithBase.char o (Ω := Ω)
  haveI : IsDedekindDomain o := _root_.GlobalTheory.ZH.ArithBase.ded (o := o) Ω
  have hwt := _root_.GlobalTheory.ZH.test_weights o Ω S
  obtain ⟨M₁, U₁, hAdm₁, hAff₁, -⟩ := _root_.GlobalTheory.ZH.exists_admissible_affine_model_dividing_tuple o Ω S Unit (fun _ => 1) ⟨(), one_ne_zero⟩
    (by
      rw [show {x | ∃ i j : S.Gam × Unit, x = S.th j.1 * (fun _ => (1:Ω)) j.2 / (S.th i.1 * (fun _ => (1:Ω)) i.2)}
          = {x | ∃ i j, x = S.th j / S.th i} by ext x; simp]
      exact hfin)
  have hO₁ := hAdm₁.1
  have hreg₁ := _root_.GlobalTheory.ZH.classical_points_and_local_regularity o Ω M₁ U₁ hO₁.normal
  have htst₁ := _root_.GlobalTheory.ZH.exists_at_test_of_cen o Ω S M₁ U₁ hT hO₁
  have hsup₁ := _root_.GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S M₁ U₁ hO₁
  have hiso₁ := _root_.GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω S M₁ U₁ hO₁ hreg₁ htst₁ hsup₁
  obtain ⟨EE₁, hEE₁, hspan₁⟩ := _root_.GlobalTheory.ZH.exists_isEE_of_adm o Ω S M₁ U₁ hT hAdm₁
  have hFF₁ := _root_.GlobalTheory.ZH.FF_TT_ne_zero o Ω S M₁ U₁ hO₁ hreg₁ htst₁ hsup₁ hiso₁ hwt
  have hdot₁ := _root_.GlobalTheory.ZH.DualSection.ff_div_th_mul_dotProduct_mem o Ω S M₁ U₁ EE₁ hAdm₁ hreg₁ htst₁ hsup₁ hiso₁ hwt
  have hnorm := _root_.GlobalTheory.thetaSys_norm_FF_le_exp o Ω S hwt
  have hnd₁ := _root_.GlobalTheory.norm_val_FF_eq_of_div o Ω S M₁ U₁ hO₁ hsup₁ hnorm htst₁
  have hdot₁' := hdot₁ hnorm hnd₁ hFF₁ hspan₁
  obtain ⟨n, a, GG₀, hGG₀⟩ := _root_.GlobalTheory.ZH.GlobalGen.exists_global_generators o Ω S M₁ U₁ EE₁ hAdm₁ hreg₁.2 hiso₁ hFF₁ hspan₁ hdot₁'
  obtain ⟨R', hR, GG, hfg, hGGeq, htests⟩ := _root_.GlobalTheory.ZH.exists_generators_at_all_tests o Ω S M₁ U₁ EE₁ n a GG₀ hO₁ hAff₁ hsup₁ hEE₁ hGG₀
  have hinj : Function.Injective (algebraMap o Ω) := (inferInstance : _root_.GlobalTheory.ZH.ArithBase o Ω).4
  obtain ⟨X, hXn, hXp⟩ := _root_.GlobalTheory.ZH.exists_isNm_isProjOver o Ω hinj S.Gam S.th S.th_ne hfin
  have hXnorm : Geo.Tor.IsNormalScheme X.Z := fun x => ⟨hXn.isNormalScheme.1 x, hXn.isNormalScheme.2 x⟩
  obtain ⟨UX, hOX, hRX⟩ := exists_open_over0_ringOn_of_fg S X R' hfg hR hXnorm hXp hXn.1
  have hregX := _root_.GlobalTheory.ZH.classical_points_and_local_regularity o Ω X UX hXnorm
  have htstX := _root_.GlobalTheory.ZH.exists_at_test_of_cen o Ω S X UX hT hOX
  have hsupX := _root_.GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S X UX hOX
  have hisoX := _root_.GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω S X UX hOX hregX htstX hsupX
  have hminX := _root_.GlobalTheory.ZH.minors_regular_and_unit_iff o Ω S X UX R' hR n a GG hOX hRX hregX htstX hsupX hisoX hwt htests
  obtain ⟨ξ, hξ⟩ := hOX.ne
  obtain ⟨x₀, hx₀⟩ := hXn.1 ξ
  obtain ⟨k₀, hk₀, -⟩ := ((hminX ξ x₀ hx₀).2).1 (hisoX.2.2.1 ξ hξ)
  obtain ⟨Z, hZn, hZp⟩ := _root_.GlobalTheory.ZH.exists_isNm_isProjOver o Ω hinj (S.Gam × (S.J → Fin n))
    (fun q => S.th q.1 * Matrix.det (Matrix.of fun i j => (GG (q.2 i) j : Ω)))
    ⟨(x₀, k₀), mul_ne_zero hx₀.1 hk₀⟩
    (by
      haveI := hfin
      refine module_finite_of_subfield_le (K := Subfield.closure (Set.range (algebraMap o Ω) ∪
        {x | ∃ i j, x = S.th j / S.th i})) ?_
      refine Subfield.closure_le.2 (Set.union_subset (fun x hx => Subfield.subset_closure (Or.inl hx)) ?_)
      rintro x ⟨i, j, rfl⟩
      exact Subfield.subset_closure (Or.inr ⟨(i, k₀), (j, k₀), (mul_div_mul_right _ _ hk₀).symm⟩))
  have hZdiv := (_root_.GlobalTheory.ZH.isNm_normal_and_div_prod o Ω Z S.Gam S.th).2.1 (S.J → Fin n)
    (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω)))
  have hZth : Z.HasDiv S.th := fun z => by
    obtain ⟨⟨i, k⟩, h⟩ := hZn.1 z
    exact ⟨i, ((hZdiv i k z).1 h).1⟩
  have hZd : Z.HasDiv (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) := fun z => by
    obtain ⟨⟨i, k⟩, h⟩ := hZn.1 z
    exact ⟨k, ((hZdiv i k z).1 h).2⟩
  have hZnorm : Geo.Tor.IsNormalScheme Z.Z := fun x => ⟨hZn.isNormalScheme.1 x, hZn.isNormalScheme.2 x⟩
  obtain ⟨UZ, hOZ, hRZ⟩ := exists_open_over0_ringOn_of_fg S Z R' hfg hR hZnorm hZp hZth
  have hregZ := _root_.GlobalTheory.ZH.classical_points_and_local_regularity o Ω Z UZ hZnorm
  have htstZ := _root_.GlobalTheory.ZH.exists_at_test_of_cen o Ω S Z UZ hT hOZ
  have hsupZ := _root_.GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω S Z UZ hOZ
  have hisoZ := _root_.GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω S Z UZ hOZ hregZ htstZ hsupZ
  obtain ⟨EE, hEE, hspanZ⟩ := _root_.GlobalTheory.ZH.exists_isEE_of_hasDiv_minors o Ω S Z UZ R' hR n a GG hOZ hRZ hregZ htstZ hsupZ htests hZd
  have hminZ := _root_.GlobalTheory.ZH.minors_regular_and_unit_iff o Ω S Z UZ R' hR n a GG hOZ hRZ hregZ htstZ hsupZ hisoZ hwt htests
  obtain ⟨f, hf⟩ := hXn.exists_isHom (φ := AlgHom.id o Ω)
    (show Z.HasDiv (fun j => (AlgHom.id o Ω) (S.th j)) from hZth)
    (fun z => _root_.GlobalTheory.ZH.RatModel.isIntegrallyClosed_O hZnorm z)
  let Xab : X.Z.Opens := ⟨{x | S.TT X x = ⊥}, by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨y₀, hy₀⟩ := hXn.1 x
    obtain ⟨k, hk, hmem⟩ := ((hminX x y₀ hy₀).2).1 hx
    refine ⟨{y | X.Div S.th y₀ y} ∩ {y | S.th y₀ ^ (a * Fintype.card S.J) /
      Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω)) ∈ X.O y}, ?_,
      (X.isOpen_setOf_div S.th y₀).inter
        (X.isOpen_setOf_mem_O _), hy₀, hmem⟩
    rintro y ⟨hy1, hy2⟩
    exact ((hminX y y₀ hy1).2).2 ⟨k, hk, hy2⟩⟩
  have hiso := _root_.GlobalTheory.ZH.isIso_morphismRestrict_of_isNm_prod o Ω X Z S.Gam (S.J → Fin n) S.th
    (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) f hXn hZn (isProper_of_isProjOver_degeneration Z hZp) hf Xab (by
      intro z hz
      obtain ⟨y₀, hy₀⟩ := hXn.1 z
      obtain ⟨k, hk, hmem⟩ := ((hminX z y₀ hy₀).2).1 hz
      refine ⟨k, hk, fun j => ?_⟩
      have h1 := (hminX z y₀ hy₀).1 j
      have ht : S.th y₀ ^ (a * Fintype.card S.J) ≠ 0 := pow_ne_zero _ hy₀.1
      have h2 := (X.O z).mul_mem h1 hmem
      beta_reduce at h1 hmem h2 ⊢
      rwa [div_mul_div_cancel₀ ht] at h2)
  exact ⟨n, a, fun k j => (GG k j : Ω), X, Z, UZ, EE, f, Xab, hXn, hXp, hZn, hOZ, hEE, hf, rfl, hiso, hspanZ, hminZ⟩

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalModelThetaTupleMaximalMinorsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_model_theta_tuple_maximal_minors : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω), S.HasTests → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = S.th j / S.th i})) Ω → ∃ (n a : ℕ) (GG : Fin n → S.J → Ω) (X Z : RatModel o Ω) (U₀ : Z.Z.Opens) (EE : Z.Lat S.J) (f : Z.Z ⟶ X.Z) (Xab : X.Z.Opens), X.IsNm S.th ∧ IsProjOver X.s ∧ Z.IsNm (fun q : S.Gam × (S.J → Fin n) => S.th q.1 * Matrix.det (Matrix.of fun i j => GG (q.2 i) j)) ∧ S.Over₀ Z U₀ ∧ S.IsEE Z U₀ EE ∧ X.IsHom Z (AlgHom.id o Ω) f ∧ (Xab : Set X.Z) = {x | S.TT X x = ⊥} ∧ IsIso (f ∣_ Xab) ∧ (∀ z : Z.Z, ∀ x₀ ∈ S.supI Z z, ∀ w : S.J → Ω, w ∈ Submodule.span (Z.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ Z.O z) ∧ ∀ z : Z.Z, ∀ x₀ ∈ S.supI Z z, (∀ k : S.J → Fin n, Matrix.det (Matrix.of fun i j => GG (k i) j) / S.th x₀ ^ (a * Fintype.card S.J) ∈ Z.O z) ∧ (S.TT Z z = ⊥ ↔ ∃ k : S.J → Fin n, Matrix.det (Matrix.of fun i j => GG (k i) j) ≠ 0 ∧ S.th x₀ ^ (a * Fintype.card S.J) / Matrix.det (Matrix.of fun i j => GG (k i) j) ∈ Z.O z) := by
  first | exact @GlobalTheory.ZH.exists_minor_model | exact GlobalTheory.ZH.exists_minor_model | (intros; apply GlobalTheory.ZH.exists_minor_model <;> assumption)
end
