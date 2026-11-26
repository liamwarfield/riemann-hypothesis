module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemLatOIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.RowLatChi
open Matrix ValuativeRel
open scoped TensorProduct

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem smul_mem_latRat (hS : IsSelfDualC S ΛS) {a : D.host.E} (ha : a ∈ D.host.AA)
    {x : Matrix (Fin T.rank) (Fin S.rank) D.host.E} (hx : x ∈ homLat ΛS ΛT) :
    a • x ∈ GlobalTheory.LatVac.latRat S T (ΛS : Set _) (ΛT : Set _) := by
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hS
  have e : a • x = ∑ l, GlobalTheory.LatVac.genMap S T a (s' l) (x *ᵥ s l) := by
    ext p q
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, GlobalTheory.LatVac.genMap, Matrix.of_apply, Matrix.mulVec,
      dotProduct]
    have h2 : ∀ l, a * (∑ r, x p r * s l r) * (∑ k, star (s' l k) * HSpace.gram S k q) =
        ∑ r, a * x p r * (s l r * ∑ k, star (s' l k) * HSpace.gram S k q) := fun l => by
      rw [mul_comm a, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [Finset.sum_congr rfl fun l _ => h2 l, Finset.sum_comm]
    simp only [← Finset.mul_sum, hdual]
    simp
  rw [e]
  exact sum_mem fun l _ => AddSubgroup.subset_closure ⟨a, ha, s' l, hs' l, x *ᵥ s l, hx _ (hs l), rfl⟩

theorem fr_neg {A : Type} [CommRing A] {m n : ℕ} (β' : GL (Fin m) A) (β : GL (Fin n) A) (x : Matrix (Fin m) (Fin n) A) :
    Comparison₂.fr β' β (-x) = -Comparison₂.fr β' β x := by rw [Comparison₂.fr, Comparison₂.fr, Matrix.mul_neg, Matrix.neg_mul]

theorem genMap_one_mem_homLat (hS : IsSelfDualC S ΛS) {s : Fin S.rank → D.host.E} (hs : s ∈ ΛS)
    {t : Fin T.rank → D.host.E} (ht : t ∈ ΛT) : GlobalTheory.LatVac.genMap S T 1 s t ∈ homLat ΛS ΛT := by
  intro y hy
  obtain ⟨b, hb⟩ := (hS.2 y).1 hy s hs
  have e : GlobalTheory.LatVac.genMap S T 1 s t *ᵥ y = (b : D.host.E) • t := by
    funext i
    simp only [GlobalTheory.LatVac.genMap, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, hb,
      Finset.sum_mul, Finset.mul_sum, one_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact ΛT.smul_mem b ht

theorem tmul_eq (α : Af D.host.F) (c y : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * y) = (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) * incA D c) * incA D y := by
  change _ = (_ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] c)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y)
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one, one_mul]


set_option maxHeartbeats 1000000 in
theorem int_of_mem_latO (hS : IsSelfDualC S ΛS) {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) (w : Pl D.host.E)
    (hw : ∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) (a : Fin T.rank) (b : Fin S.rank) :
    Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (u.map (toEAf D)) a b)) ≤ 1 := by
  let p : WO S T → Prop := fun u => ∀ a b, Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (u.map (toEAf D)) a b)) ≤ 1
  have hadd : ∀ x y, p x → p y → p (x + y) := fun x y hx hy a b => by
    have e : (x + y).map (toEAf D) = x.map (toEAf D) + y.map (toEAf D) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, map_add]
    rw [e, Comparison₂.fr_add, Matrix.add_apply, RingHom.map_add (f := _)]
    exact Valuation.map_add_le _ (hx a b) (hy a b)
  have hneg : ∀ x, p x → p (-x) := fun x hx a b => by
    rw [Matrix.map_neg _ (toEAf D).map_neg, fr_neg, Matrix.neg_apply, RingHom.map_neg, Valuation.map_neg]
    exact hx a b
  have hzero : p 0 := fun a b => by
    rw [Matrix.map_zero _ (toEAf D).map_zero, show Comparison₂.fr βT βS (0 : Matrix (Fin T.rank) (Fin S.rank) (EAf D)) = 0 by
      rw [Comparison₂.fr, Matrix.mul_zero, Matrix.zero_mul]]
    simp
  refine GlobalTheory.LatVac.latO_induction (p := p) (fun α hα M hM => ?_) hzero hadd hneg hu a b
  induction hM using AddSubgroup.closure_induction with
  | mem M hM =>
    obtain ⟨c, hc, s, hs, t, ht, rfl⟩ := hM
    set Y := GlobalTheory.LatVac.genMap S T 1 s t
    have hY : Y ∈ homLat ΛS ΛT := genMap_one_mem_homLat hS hs ht
    have e1 : (GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T c s t) : WO S T).map (toEAf D) =
        toEAf D ((pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D c) • Y.map (eToEAf D) := by
      ext i j
      simp only [GlobalTheory.LatVac.finTens, Y, GlobalTheory.LatVac.genMap, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
        smul_eq_mul]
      rw [show c * t i * ∑ k, star (s k) * HSpace.gram S k j = c * (1 * t i * ∑ k, star (s k) * HSpace.gram S k j) by ring,
        tmul_eq, RingHom.map_mul]
      rfl
    intro a b
    rw [e1, Comparison₂.fr_smul, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, RingHom.map_mul, Valuation.map_mul,
      RingHom.map_mul, Valuation.map_mul]
    have h1 : Valued.v (cpt (D := D) w (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)))) ≤ 1 := by
      have hi : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D :=
        AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩
      exact ((comp_toAd D).int (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E))).1 hi w
    have h2 : Valued.v (cpt (D := D) w (toEAf D (incA D c))) ≤ 1 := by
      rw [show cpt (D := D) w (toEAf D (incA D c)) = algebraMap D.host.E (Kw w) c from Comparison₂.cpt_tmul w c]
      exact hw c hc
    have h3 : Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (Y.map (eToEAf D)) a b)) ≤ 1 := by
      obtain ⟨s', -, hs'⟩ := Comparison₂.fr_mem_idS hβS hβT (𝔪 := ⊤) (by rw [Submodule.top_smul]; exact hY) a b
      have h4 := (mem_OA_iff _).1 s'.2 w
      rw [hs'] at h4
      exact h4
    exact mul_le_one' (mul_le_one' h1 h2) h3
  | zero => rw [GlobalTheory.LatVac.finTens_zero]; exact hzero
  | add x y _ _ hx hy => rw [GlobalTheory.LatVac.finTens_add]; exact hadd _ _ hx hy
  | neg x _ hx => rw [GlobalTheory.LatVac.finTens_neg]; exact hneg _ hx

theorem mem_hatMx_of_int {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
    (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) {e₁ : AE D} {P₁ : Finset (Pl D.host.E)} (he : IsIdemSum e₁ P₁)
    {u : WO S T} (hu : IsHalf e₁ u)
    (h : ∀ w ∈ P₁, ∀ a b, Valued.v (cpt (D := D) w (Comparison₂.fr βT βS (u.map (toEAf D)) a b)) ≤ 1) :
    u ∈ hatMx (homLat ΛS ΛT) := by
  obtain ⟨e0, -, e2⟩ := Comparison₂.cpt_idemSum he
  have hfr : ∀ a b, Comparison₂.fr βT βS (u.map (toEAf D)) a b = toEAf D e₁ * Comparison₂.fr βT βS (u.map (toEAf D)) a b := by
    intro a b
    have hm : u.map (toEAf D) = toEAf D e₁ • u.map (toEAf D) := Matrix.ext fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, ← RingHom.map_mul, hu i j]
    conv_lhs => rw [hm, Comparison₂.fr_smul]
    rfl
  rw [← Submodule.top_smul (homLat ΛS ΛT), HatFrame.mem_hatMx_homLat_iff D ΛS ΛT βS βT hβS hβT ⊤ u]
  refine ⟨fun a b => by rw [← hu a b, RingHom.map_mul, e0, zero_mul], fun a b => ?_⟩
  refine ⟨⟨Comparison₂.fr βT βS (u.map (toEAf D)) a b, (mem_OA_iff _).2 fun Q => ?_⟩, ?_, rfl⟩
  · by_cases hQ : Q ∈ P₁
    · exact h Q hQ a b
    · rw [hfr, RingHom.map_mul, e2 Q hQ, zero_mul]; exact zero_mem _
  · unfold idS; rw [Ideal.map_top]; exact Submodule.mem_top

theorem smul_mem_latO_of_mem_hatMx (hS : IsSelfDualC S ΛS) {a : D.host.E} (ha : a ∈ D.host.AA) {u : WO S T}
    (hm : u ∈ hatMx (homLat ΛS ΛT)) : incA D a • u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True := by
  induction hm using AddSubgroup.closure_induction with
  | mem v hv =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hv
    have e : incA D a • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j : WO S T) =
        GlobalTheory.LatVac.finTens α (a • x) := by
      ext i j
      simp only [Matrix.smul_apply, Matrix.of_apply, GlobalTheory.LatVac.finTens, Matrix.map_apply, smul_eq_mul]
      change ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [e]
    exact GlobalTheory.LatVac.finTens_mem_latO hα (smul_mem_latRat hS ha hx)
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx


set_option maxHeartbeats 1000000 in
theorem mem_latO_of_mem_hatMx (hS : IsSelfDualC S ΛS) {e₁ : AE D} {P₁ : Finset (Pl D.host.E)} (he : IsIdemSum e₁ P₁)
    (hAA : ∀ w ∈ P₁, ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) {u : WO S T} (hu : IsHalf e₁ u)
    (hm : u ∈ hatMx (homLat ΛS ΛT)) : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hxe : (∑ PP ∈ P₁, es PP) • u = u := Matrix.ext fun i j => hu i j
  rw [← hxe, Finset.sum_smul]
  refine sum_mem fun w hw => ?_
  obtain ⟨a, ha, hv⟩ := hAA w hw
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, Valuation.map_zero] at hv
    exact zero_ne_one hv
  have hc : finPart D (es w * incA D a⁻¹) ∈ intAE D := by
    refine ((comp_toAd D).int (es w * incA D a⁻¹)).2 fun Q => ?_
    show Valued.v (cpt (D := D) Q (toEAf D (es w * incA D a⁻¹))) ≤ 1
    obtain ⟨h1, h2⟩ := cpt_of_isIdemAt (hes w hw)
    rw [RingHom.map_mul, RingHom.map_mul,
      show cpt (D := D) Q (toEAf D (incA D a⁻¹)) = algebraMap D.host.E (Kw Q) a⁻¹ from Comparison₂.cpt_tmul Q a⁻¹]
    rcases eq_or_ne Q w with rfl | hQ
    · rw [h1, one_mul, map_inv₀, map_inv₀, hv, inv_one]
    · rw [h2 Q hQ, zero_mul, Valuation.map_zero]
      exact zero_le
  have e : es w • u = (es w * incA D a⁻¹) • (incA D a • u) := by
    rw [smul_smul, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ ha0, RingHom.map_one, mul_one]
  rw [e]
  exact GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ hc _ (smul_mem_latO_of_mem_hatMx hS ha hm)

theorem intM_iff (w : Pl D.host.E) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (Kw w)) :
    GlobalTheory.StepData.IntM M ↔ ∀ a b, Valued.v (M a b) ≤ 1 := by
  refine forall₂_congr fun a b => ?_
  rw [Valuation.mem_integer_iff, ← map_one (valuation (Kw w))]
  rw [(Comparison₂.vEq w) (M a b) 1, map_one]

end GlobalTheory.RowLatChi


open GlobalTheory.RowLatChi in
theorem GlobalTheory.RowLatChi.mem_latO_iff_intM : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) {e₁ : AE D} {P₁ : Finset (Pl D.host.E)}, IsIdemSum e₁ P₁ → (∀ w ∈ P₁, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (i : Fin D.R.m) (z : WO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0))), IsHalf e₁ z → (z ∈ (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _) (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) ↔ ∀ w ∈ P₁, GlobalTheory.StepData.IntM (B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0)) ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (z.map (cpt (D := D) w ∘ toEAf D)))) := by
  intro D T L sc G μ₀ hL B t e₁ P₁ hI hAA i z hz
  have hi : (i : ℕ) < D.R.m := i.2
  have hSD := GlobalTheory.CosetRow.selfDual_chi hL G i hi
  have hβS := B.isFrame_β hL (i := (i : ℕ) + 1) hi (Nat.zero_le _)
  have hβT := B.isFrame_β hL (i := (i : ℕ)) hi.le (Nat.zero_le _)
  have key : ∀ w, (GlobalTheory.StepData.IntM (B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0)) ⟨i.2.le, Nat.zero_le _⟩
      ⟨i.2, Nat.zero_le _⟩ (z.map (cpt (D := D) w ∘ toEAf D))) ↔
      ∀ a b, Valued.v (cpt (D := D) w (Comparison₂.fr (B.β i 0) (B.β (i + 1) 0) (z.map (toEAf D)) a b)) ≤ 1) := by
    intro w
    rw [intM_iff, ← Matrix.map_map, Comparison₂.coord_map]
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
    exact ⟨fun H a b => by
      simpa using H (b.cast (rank_vertex G t w (X := ((i : ℕ) + 1, 0)) ⟨hi, Nat.zero_le _⟩).symm)
        (a.cast (rank_vertex G t w (X := ((i : ℕ), 0)) ⟨hi.le, Nat.zero_le _⟩).symm), fun H a b => H _ _⟩
  simp only [key]
  constructor
  · intro h w hw a b
    exact int_of_mem_latO hSD.1 hβS hβT w (hAA w hw).1 h a b
  · intro h
    exact mem_latO_of_mem_hatMx hSD.1 hI (fun w hw => (hAA w hw).2) hz (mem_hatMx_of_int hβS hβT hI hz h)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatrStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedGridArrowLattice_iff_integral_frameMatrix : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) {e₁ : AE D} {P₁ : Finset (Pl D.host.E)}, IsIdemSum e₁ P₁ → (∀ w ∈ P₁, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (i : Fin D.R.m) (z : WO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0))), IsHalf e₁ z → (z ∈ (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _) (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) ↔ ∀ w ∈ P₁, GlobalTheory.StepData.IntM (B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0)) ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (z.map (cpt (D := D) w ∘ toEAf D)))) := by
  first | exact @GlobalTheory.RowLatChi.mem_latO_iff_intM | exact GlobalTheory.RowLatChi.mem_latO_iff_intM | (intros; apply GlobalTheory.RowLatChi.mem_latO_iff_intM <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HostIdealUnitAtPlacesPrimeToLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HostIdealUnitAtPlacesPrimeToLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.AAUnit

theorem aa_unit : ∀ (D : D7) (w : Pl D.host.E), ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
  intro D w h2qd hN
  have h2q : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun h => h2qd (by
    rw [Nat.cast_mul]; exact w.asIdeal.mul_mem_right _ h)
  refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
  · rw [GlobalTheory.FunObj.Good.valued_alg]
    exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
  · rw [GlobalTheory.FunObj.Good.valued_alg]
    exact GlobalTheory.FunObj.Good.valuation_nat hN

end GlobalTheory.AAUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HostIdealUnitAtPlacesPrimeToLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_ideal_unit_at_places_prime_to_level : ∀ (D : D7) (w : Pl D.host.E), ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
  first | exact @GlobalTheory.AAUnit.aa_unit | exact GlobalTheory.AAUnit.aa_unit | (intros; apply GlobalTheory.AAUnit.aa_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionOfFunctorialityAdopted
namespace ThetaProjectionIdempotent
section
open GlobalTheory.RowClaim

namespace CompanionTheory.Member.ThetaDownProjection

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
open GlobalTheory.ChainEquiv
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem thDn_act (hP : GlobalTheory.Published.CuspRapidDecay) (hC : GlobalTheory.Hk3.Core R F) (t : T0) (g : G) (x : (A.fam.R t).S.Forms)
    (v : SmT (R.MY 0)) :
    R.thDn t (R.jX t ((A.fam.R t).r g x)) v = actL _ (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.thDn t (R.jX t x) v) := by
  have hS : ∀ t j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j) :=
    fun t j _ => @GlobalTheory.MultFinite.schurMult D R.θ _ _ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) hP (R.νY t j) (R.fdY t j)
  refine (GlobalTheory.FormAction.act_eq_translate R hC.grp.red_R hC.models.jX t g x).elim fun κ hκ => ?_
  have hrel : Rel R t (R.eG g) 0 (thCC t (R.jX t x)) (thCC t (R.jX t ((A.fam.R t).r g x))) :=
    rel_dnFrom hC.lev hC.models.inf hC.models.νY hC.models.νY' hC.chain hS t (R.eG g) (D.R.m - 1)
      (by have := D.R.two_le_m; omega) _ _
      (rel_ioX hC.lev hC.models.inf hC.models.νY hC.models.νY' hC.chain hC.models.νX hC.models.cX hC.models.HX hS t
        (R.eG g) κ hκ.1 _ _ hκ.2)
  exact act_of_rel hC.lev t _ _ _ hrel v

theorem sum_act {K V H M W G : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup H] [Module ℂ H]
    [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W] [Fintype G] {σ : K →+* ℂ} (j : V →ₛₗ[σ] H)
    (Θ : H →ₗ[ℂ] M →ₗ[ℂ] W) (r : G → Module.End K V) (a : G → W →ₗ[ℂ] W) (c : G → K) (x : V) (v : M)
    (h : ∀ g, Θ (j (r g x)) v = a g (Θ (j x) v)) :
    Θ (j ((∑ g, c g • r g) x)) v = (∑ g, σ (c g) • a g) (Θ (j x) v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, RingHom.id_apply, h]

theorem heckeProjector_fixes_heckeEigenVector (hC : GlobalTheory.Hk3.Core R F) (y : R.HE.H) (f : (R.MY 0).Vec) : R.e0 (R.HE.e y f) = R.HE.e y f := by
  have h1 : R.HE.e y ∈ R.EEat R.triv := by
    rw [← hC.models.HE.2.1]
    exact LinearMap.mem_range_self _ y
  have h2 : postOn (R.MY 0) R.e0 (R.HE.e y) - R.HE.e y = 0 := h1.2
  have h3 := congrArg (fun u : MMap (R.MY 0) => u f) (sub_eq_zero.1 h2)
  exact (postOn_apply _ _ _ _).symm.trans h3

theorem idem_ind {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (u : SmT M →ₗ[ℂ] (GA D V → ℂ))
    (h : ∀ f : M.Vec, e (e (u (PiTensorProduct.tprod ℂ f))) = e (u (PiTensorProduct.tprod ℂ f))) (v : SmT M) :
    e (e (u v)) = e (u v) := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f => rw [map_smul, map_smul, map_smul]; exact congrArg (fun z => r • z) (h f)
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]


set_option maxHeartbeats 1000000 in
theorem heckeProjector_idempotent_compositeLift (hC : GlobalTheory.Hk3.Core R F) (t : T0) (y : (R.HX t).H) (v : SmT (R.MY 0)) :
    R.e0 (R.e0 (R.thDn t y v)) = R.e0 (R.thDn t y v) := by
  rw [thDn_eq]
  refine idem_ind (R.MY 0) R.e0 _ (fun f => ?_) v
  have h5 := e_Th hC.chain.Th t y f
  exact (congrArg R.e0 h5).symm.trans ((heckeProjector_fixes_heckeEigenVector hC (R.Th t y) f).trans h5)

set_option maxHeartbeats 1000000 in
theorem proj_thDn (hP : GlobalTheory.Published.CuspRapidDecay) (hC : GlobalTheory.Hk3.Core R F) (t : T0) (x : A.fam.amb.FR t)
    (hx : x ∈ (A.fam.R t).goodF A.fam.X) (v : SmT (R.MY 0)) :
    R.e0 (R.thDn t (R.jX t x) v) = R.thDn t (R.jX t x) v := by
  obtain ⟨y, hy⟩ := hx
  rw [goodAt, level_idempotent_bot, mul_one] at hy
  have h : R.thDn t (R.jX t x) v = R.e0 (R.thDn t (R.jX t y) v) := by
    rw [← hy]
    exact sum_act (R.jX t) (R.thDn t) (fun g => (A.fam.R t).r g) _ (fun g => (idemOf A.X).coeff g) y v
      fun g => thDn_act hP hC t g y v
  rw [h]
  exact heckeProjector_idempotent_compositeLift hC t _ v

end CompanionTheory.Member.ThetaDownProjection

end

end ThetaProjectionIdempotent
section
open GlobalTheory.RowClaim

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumSubOfSubsetAndOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumSubOfSubsetAndOrthogonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.IdemSubDiff

variable {D : D7} [DecidableEq (Pl D.host.E)]

theorem comp_sum {es : Pl D.host.E → AE D} {S : Finset (Pl D.host.E)}
    (h : ∀ PP ∈ S, Formalism.L2.NTheta.IsIdemAt (es PP) PP) :
    infPart D (∑ PP ∈ S, es PP) = 0 ∧
      ∀ w, cpt (D := D) w (toEAf D (∑ PP ∈ S, es PP)) = if w ∈ S then 1 else 0 := by
  refine ⟨?_, fun w => ?_⟩
  · rw [GlobalTheory.FunObj.Comparison₂.hom_sum]
    exact Finset.sum_eq_zero fun Q hQ => (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) (h Q hQ)).1
  · rw [GlobalTheory.FunObj.Comparison₂.hom_sum, GlobalTheory.FunObj.Comparison₂.hom_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single_of_mem w hw fun Q hQ hne => (cpt_of_isIdemAt (h Q hQ)).2 w hne.symm]
      exact (cpt_of_isIdemAt (h w hw)).1
    · exact Finset.sum_eq_zero fun Q hQ => (cpt_of_isIdemAt (h Q hQ)).2 w fun h' => hw (h' ▸ hQ)

theorem isIdemSum_sdiff : ∀ {D : D7} [DecidableEq (Pl D.host.E)] {e e₀ : AE D} {P P₀ : Finset (Pl D.host.E)},
    IsIdemSum e P → IsIdemSum e₀ P₀ → P₀ ⊆ P → IsIdemSum (e - e₀) (P \ P₀) ∧ e₀ * (e - e₀) = 0 := by
  intro D _ e e₀ P P₀ h h0 hsub
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  obtain ⟨i0, c1, c0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum h0
  obtain ⟨j0, d⟩ := comp_sum hes
  rw [← he] at j0 d
  have hes0 : ∀ PP ∈ P₀, Formalism.L2.NTheta.IsIdemAt (es PP) PP := fun PP hPP => hes PP (hsub hPP)
  obtain ⟨k0, k⟩ := comp_sum hes0
  have he0 : e₀ = ∑ PP ∈ P₀, es PP := by
    refine GlobalTheory.FunObj.ae_ext (by rw [i0, k0]) fun w => ?_
    rw [k w]
    split_ifs with hw
    · exact c1 w hw
    · exact c0 w hw
  have hdiff : e - e₀ = ∑ PP ∈ P \ P₀, es PP := by
    rw [he, he0, ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  have hmul : e * (e - e₀) = e - e₀ := by
    refine GlobalTheory.FunObj.ae_ext (by simp only [RingHom.map_mul, RingHom.map_sub, j0, i0, sub_zero, mul_zero]) fun w => ?_
    simp only [RingHom.map_mul, RingHom.map_sub, d w]
    by_cases hw : w ∈ P
    · rw [if_pos hw, one_mul]
    · have hw0 : w ∉ P₀ := fun h' => hw (hsub h')
      rw [if_neg hw, c0 w hw0, zero_mul, sub_zero]
  have horth : e₀ * (e - e₀) = 0 := by
    refine GlobalTheory.FunObj.ae_ext (by simp only [RingHom.map_mul, RingHom.map_sub, j0, i0, sub_zero, mul_zero, RingHom.map_zero]) fun w => ?_
    simp only [RingHom.map_mul, RingHom.map_sub, RingHom.map_zero, d w]
    by_cases hw0 : w ∈ P₀
    · rw [c1 w hw0, if_pos (hsub hw0), sub_self, mul_zero]
    · rw [c0 w hw0, zero_mul]
  refine ⟨⟨⟨es, fun PP hPP => hes PP (Finset.mem_sdiff.1 hPP).1, hdiff⟩, ?_⟩, horth⟩
  have h1 : (e - e₀) * cA D (e - e₀) = ((e - e₀) * cA D (e - e₀)) * (e * cA D e) := by
    conv_lhs => rw [← hmul]
    rw [map_mul]
    ring
  rw [h1, hc, mul_zero]

end GlobalTheory.IdemSubDiff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumSubOfSubsetAndOrthogonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIdemSum_sub_of_subset_and_orthogonal : ∀ {D : D7} [DecidableEq (Pl D.host.E)] {e e₀ : AE D} {P P₀ : Finset (Pl D.host.E)}, IsIdemSum e P → IsIdemSum e₀ P₀ → P₀ ⊆ P → IsIdemSum (e - e₀) (P \ P₀) ∧ e₀ * (e - e₀) = 0 := by
  first | exact @GlobalTheory.IdemSubDiff.isIdemSum_sdiff | exact GlobalTheory.IdemSubDiff.isIdemSum_sdiff | (intros; apply GlobalTheory.IdemSubDiff.isIdemSum_sdiff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSBHalfHalfExtensionLatticeIndicatorFn
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSBHalfHalfExtensionLatticeIndicatorFn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.CosetRow.ExtSB

variable {D : D7} {m n : ℕ}

theorem half_of_idem' {b : AE D} (hb : b * b = b) (t : Mx D m n) : IsHalf b (b • t) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination (t i j) * hb

theorem half_add_nsmul_iff {e : AE D} {t u : Mx D m n} (hu : IsHalf e u) (k : ℕ) :
    IsHalf e (t + k • u) ↔ IsHalf e t := by
  constructor
  · intro h i j
    have h1 := h i j
    have h2 := hu i j
    simp only [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul] at h1
    linear_combination h1 - (k : AE D) * h2
  · intro h i j
    have h1 := h i j
    have h2 := hu i j
    simp only [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
    linear_combination h1 + (k : AE D) * h2

theorem smul_add_nsmul (e : AE D) (t u : Mx D m n) (k : ℕ) : e • (t + k • u) = e • t + k • (e • u) := by
  rw [smul_add, smul_comm]

theorem isSBHalf_extFn : ∀ {D : D7} {m n : ℕ} {Λ : AddSubgroup (Mx D m n)} {e₀ e₁ : AE D} {Φ : Mx D m n → ℂ}, e₀ * e₀ = e₀ → e₁ * e₁ = e₁ → e₀ * e₁ = 0 → (∀ u ∈ Λ, e₀ • u ∈ Λ) → (∀ u ∈ Λ, e₁ • u ∈ Λ) → IsSBHalf e₀ Λ Φ → IsSBHalf (e₀ + e₁) Λ (GlobalTheory.CosetRow.extFn e₀ e₁ Λ Φ) := by
  intro D m n Λ e₀ e₁ Φ h0 h1 h01 hΛ0 hΛ1 hΦ
  obtain ⟨sΦ, k, hk, iΦ, fΦ⟩ := hΦ
  refine ⟨fun t ht => ?_, k, hk, fun u hu hue t => ?_, fun t ht => ?_⟩
  · unfold GlobalTheory.CosetRow.extFn at ht
    by_contra hc
    exact ht (if_neg hc)
  · have hhalf := half_add_nsmul_iff (t := t) hue k
    have hA : Φ (e₀ • (t + k • u)) = Φ (e₀ • t) := by
      rw [smul_add_nsmul]
      exact iΦ _ (hΛ0 u hu) (half_of_idem' h0 u) _
    have hB : halfInd e₁ Λ (e₁ • (t + k • u)) = halfInd e₁ Λ (e₁ • t) := by
      rw [smul_add_nsmul]
      unfold halfInd
      have hm : e₁ • t + k • (e₁ • u) ∈ Λ ↔ e₁ • t ∈ Λ :=
        Λ.add_mem_cancel_right (AddSubgroup.nsmul_mem Λ (hΛ1 u hu) k)
      have hh : IsHalf e₁ (e₁ • t + k • (e₁ • u)) ↔ IsHalf e₁ (e₁ • t) :=
        half_add_nsmul_iff (half_of_idem' h1 u) k
      by_cases hc : e₁ • t ∈ Λ ∧ IsHalf e₁ (e₁ • t)
      · rw [if_pos (And.intro (hm.2 hc.1) (hh.2 hc.2)), if_pos hc]
      · rw [if_neg (fun h => hc ⟨hm.1 h.1, hh.1 h.2⟩), if_neg hc]
    unfold GlobalTheory.CosetRow.extFn
    rw [hA, hB]
    by_cases hc : IsHalf (e₀ + e₁) t
    · rw [if_pos (hhalf.2 hc), if_pos hc]
    · rw [if_neg (mt hhalf.1 hc), if_neg hc]
  · unfold GlobalTheory.CosetRow.extFn at ht
    by_cases hc : IsHalf (e₀ + e₁) t
    · rw [if_pos hc] at ht
      have hΦt : Φ (e₀ • t) ≠ 0 := left_ne_zero_of_mul ht
      have hI : halfInd e₁ Λ (e₁ • t) ≠ 0 := right_ne_zero_of_mul ht
      have hI' : e₁ • t ∈ Λ := by
        unfold halfInd at hI
        by_contra hn
        exact hI (if_neg (fun h => hn h.1))
      have hkt : k • t = k • (e₀ • t) + k • (e₁ • t) := by
        ext i j
        have := hc i j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul] at this ⊢
        linear_combination -(k : AE D) * this
      rw [hkt]
      exact Λ.add_mem (fΦ _ hΦt) (AddSubgroup.nsmul_mem Λ hI' k)
    · exact absurd (if_neg hc) ht

end GlobalTheory.CosetRow.ExtSB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSBHalfHalfExtensionLatticeIndicatorFnStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSBHalf_halfExtensionLatticeIndicatorFn : ∀ {D : D7} {m n : ℕ} {Λ : AddSubgroup (Mx D m n)} {e₀ e₁ : AE D} {Φ : Mx D m n → ℂ}, e₀ * e₀ = e₀ → e₁ * e₁ = e₁ → e₀ * e₁ = 0 → (∀ u ∈ Λ, e₀ • u ∈ Λ) → (∀ u ∈ Λ, e₁ • u ∈ Λ) → IsSBHalf e₀ Λ Φ → IsSBHalf (e₀ + e₁) Λ (GlobalTheory.CosetRow.extFn e₀ e₁ Λ Φ) := by
  first | exact @GlobalTheory.CosetRow.ExtSB.isSBHalf_extFn | exact GlobalTheory.CosetRow.ExtSB.isSBHalf_extFn | (intros; apply GlobalTheory.CosetRow.ExtSB.isSBHalf_extFn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceDownChain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.FlipStart.Col

variable {D : D7}

theorem fund_exch {V : HSp D} {μ : Measure (GA D V)} [μ.IsHaarMeasure] {Fd Fd' : Set (GA D V)}
    (h1 : IsFundamentalDomain (GQ V) Fd μ) (h2 : IsFundamentalDomain (GQ V) Fd' μ) (f : GA D V → ℂ)
    (hf : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) :
    (IntegrableOn f Fd μ ↔ IntegrableOn f Fd' μ) ∧ ∫ g in Fd, f g ∂μ = ∫ g in Fd', f g ∂μ := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  exact ⟨h1.integrableOn_iff h2 fun γ g => hf γ γ.2 g, h1.setIntegral_eq h2 fun γ g => hf γ γ.2 g⟩

theorem step_heq {S S₀ T T₀ : HSp D} (hS : S = S₀) (hT : T = T₀)
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {ω₀ : GA D S₀ × GA D T₀ →* Module.End ℂ (WO S₀ T₀ → ℂ)} (hω : HEq ω ω₀)
    {s : WO S T → ℂ} {s₀ : WO S₀ T₀ → ℂ} (hs : HEq s s₀)
    {μ : Measure (GA D T)} {μ₀ : Measure (GA D T₀)} (hμ : HEq μ μ₀) (hH : μ₀.IsHaarMeasure)
    {Fd : Set (GA D T)} {Fd₀ : Set (GA D T₀)} (h1 : IsFundamentalDomain (GQ T) Fd μ) (h2 : IsFundamentalDomain (GQ T₀) Fd₀ μ₀)
    {F : GA D T → ℂ} {F₀ : GA D T₀ → ℂ} (hF : HEq F F₀)
    (hinv : ∀ h, ∀ γ ∈ GQ T₀, ∀ g, thetaKO ω₀ h (γ * g) s₀ * F₀ (γ * g) = thetaKO ω₀ h g s₀ * F₀ g)
    (hint : ∀ h, IntegrableOn (fun g => thetaKO ω₀ h g s₀ * F₀ g) Fd₀ μ₀) :
    (∀ h, IntegrableOn (fun g => thetaKO ω h g s * F g) Fd μ) ∧
      HEq (fun h => ∫ g in Fd, thetaKO ω h g s * F g ∂μ) (Lift.liftInt μ₀ Fd₀ (thetaKO ω₀) s₀ F₀) := by
  subst hS hT
  obtain rfl := eq_of_heq hω
  obtain rfl := eq_of_heq hs
  obtain rfl := eq_of_heq hμ
  obtain rfl := eq_of_heq hF
  haveI := hH
  exact ⟨fun h => (fund_exch h1 h2 _ (hinv h)).1.2 (hint h),
    heq_of_eq (funext fun h => (fund_exch h1 h2 _ (hinv h)).2)⟩

theorem pt_heq {ψ ψ₀ : AddChar (AF D.host.F) ℂ} {θ θ₀ : InfFam D} (hψ : ψ = ψ₀) (hθ : θ = θ₀) {S S₀ T T₀ : HSp D} (hS : S = S₀)
    (hT : T = T₀)
    {a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {a₀ : D.what₂.Tau → Matrix (Fin S₀.rank) (Fin S₀.rank) ℂ} (ha : HEq a a₀)
    {b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {b₀ : D.what₂.Tau → Matrix (Fin T₀.rank) (Fin T₀.rank) ℂ} (hb : HEq b b₀)
    {c : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {c₀ : D.what₂.Tau → Matrix (Fin S₀.rank) (Fin S₀.rank) ℂ} (hc : HEq c c₀)
    {d : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {d₀ : D.what₂.Tau → Matrix (Fin T₀.rank) (Fin T₀.rank) ℂ} (hd : HEq d d₀)
    {f : WO S T → ℂ} {f₀ : WO S₀ T₀ → ℂ} (hf : HEq f f₀) {P : PolF D T.rank S.rank} {P₀ : PolF D T₀.rank S₀.rank} (hP : HEq P P₀) :
    HEq (pureTensorO ψ θ S T a b c d f P) (pureTensorO ψ₀ θ₀ S₀ T₀ a₀ b₀ c₀ d₀ f₀ P₀) := by
  subst hψ hθ hS hT
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hd
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hP
  rfl

theorem measFD_heq {V V₀ : HSp D} (hV : V = V₀) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : Lev.IsMeasFD V K μ F) (h₀ : Lev.IsMeasFD V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  subst hV
  obtain rfl := eq_of_heq hK
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (fun _ _ e => e.1) h.1 h₀.1)

theorem measDef_heq {V V₀ : HSp D} (hV : V = V₀) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))}
    {K₀ : Subgroup (GL (Fin V₀.rank) (Lev.EAf D))} (hK : HEq K K₀) {μ : Measure (GA D V)} {μ₀ : Measure (GA D V₀)}
    {F : Set (GA D V)} {F₀ : Set (GA D V₀)} (h : IsMeasDef V K μ F) (h₀ : IsMeasDef V₀ K₀ μ₀ F₀) : HEq μ μ₀ := by
  subst hV
  obtain rfl := eq_of_heq hK
  exact heq_of_eq (GlobalTheory.FunObjModel.isMeasLevW_unique (fun _ _ e => e.1) h.1 h₀.1)

theorem cast_fun_heq {A B : Type} (e : A = B) (φ : B → ℂ) : HEq (fun x => φ (cast e x)) φ := by
  subst e; rfl

variable {T : Type} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem stepY {ch : Choice R} (hW : ch.W.Over R) (hch : R.IsChain) (hmod : R.IsModels) {t : T} {M : Vol ch.G} (hM : M.Is t)
    {j : ℕ} (hj : j + 1 < D.R.m) {fj : Sch ch.G (.down t 0 j)} (hfj : HEq fj (R.vY t j))
    {P : PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank} {P₀ : PolF D (Yc D (j + 1)).rank (Yc D j).rank}
    (hP : HEq P P₀) {s : Sch ch.G (.down t 0 j)} (hs : s = ch.W.fock (.mu t 0 j) fj P) {F : Fn ch.G (.grid 0 (j + 1))}
    {F₀ : GA D (Yc D (j + 1)) → ℂ} (hF : HEq F F₀)
    (hinv : ∀ γ ∈ GQ (Yc D (j + 1)), ∀ g, F₀ (γ * g) = F₀ g)
    (hint : ∀ h, IntegrableOn (fun g => thetaKO (R.ωY t j) h g (R.ptY t j P₀) * F₀ g) (R.fdY t (j + 1)) (R.νY t (j + 1))) :
    LiftConv ch.W M (.down t 0 j) s F ∧
      HEq (liftA ch.W M (.down t 0 j) s F)
        (Lift.liftInt (R.νY t (j + 1)) (R.fdY t (j + 1)) (thetaKO (R.ωY t j)) (R.ptY t j P₀) F₀) := by
  subst hs
  have hS : ch.G.V (.grid 0 j) = Yc D j := congrArg LSp.sp (colY_lt R.toLevCh (by omega))
  have hT : ch.G.V (.grid 0 (j + 1)) = Yc D (j + 1) := congrArg LSp.sp (colY_lt R.toLevCh hj)
  have hs : HEq (ch.W.fock (.mu t 0 j) fj P) (R.ptY t j P₀) :=
    pt_heq hW.ψ hW.θ hS hT (hW.cartY j (by omega)) (hW.cartY (j + 1) hj) (hW.onbY j (by omega)) (hW.onbY (j + 1) hj) hfj hP
  have hAt := hM.vtx (.grid 0 (j + 1)) ⟨Nat.zero_le _, by omega⟩
  have hfund := hAt.haar_fund
  have hK : HEq (levJ ch.G t (.grid 0 (j + 1)))
      (lev D.sp.cm (Yc D (j + 1)).gram (R.βY (j + 1)) (R.datYt t (j + 1) R.triv)) := levCol_lt R.toLevCh t hj
  have key : HEq (M.ν (.grid 0 (j + 1))) (R.νY t (j + 1)) ∧ (R.νY t (j + 1)).IsHaarMeasure ∧
      IsFundamentalDomain (GQ (Yc D (j + 1))) (R.fdY t (j + 1)) (R.νY t (j + 1)) := by
    unfold Vol.IsAt at hAt
    rcases Nat.lt_or_ge (j + 1 + 1) D.R.m with h | h
    · have hc := hmod.νY t (j + 1) h
      rw [if_neg (show ¬ (Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [Node.neg]; omega)] at hAt
      exact ⟨measFD_heq hT hK hAt hc, hc.1.1, hc.2⟩
    · have e : j + 1 = D.R.m - 1 := by omega
      have hc := hmod.νY' t
      rw [← e] at hc
      rw [if_pos (show (Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [Node.neg]; omega)] at hAt
      exact ⟨measDef_heq hT hK hAt hc, hc.1.1, hc.2⟩
  have hker := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ (R.ωY t j) (hch.ωY t j hj) _ (hch.ptY t j hj P₀)).1
  exact step_heq hS hT (hW.omY t j hj) hs key.1 key.2.1 hfund.2 key.2.2 hF (fun h γ hγ g => by
      have h1 := hker 1 (one_mem _) γ hγ h g
      rw [one_mul] at h1
      rw [h1, hinv γ hγ g]) hint

theorem stepX {ch : Choice R} (hW : ch.W.Over R) (hch : R.IsChain) (hmod : R.IsModels) {t : T} {M : Vol ch.G} (hM : M.Is t)
    {j : ℕ} (hj : j + 1 = D.R.m) {fj : Sch ch.G (.down t 0 j)} (hfj : HEq fj (R.vX t))
    {P : PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank} {P₀ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank}
    (hP : HEq P P₀) {s : Sch ch.G (.down t 0 j)} (hs : s = ch.W.fock (.mu t 0 j) fj P) {F : Fn ch.G (.grid 0 (j + 1))}
    {F₀ : GA D D.sp.X' → ℂ} (hF : HEq F F₀)
    (hinv : ∀ γ ∈ GQ D.sp.X', ∀ g, F₀ (γ * g) = F₀ g)
    (hint : ∀ h, IntegrableOn (fun g => thetaKO (R.ωX t) h g (R.ptX t P₀) * F₀ g) (R.fdX t) (R.νX t)) :
    LiftConv ch.W M (.down t 0 j) s F ∧
      HEq (liftA ch.W M (.down t 0 j) s F)
        (Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t P₀) F₀) := by
  subst hs
  have e : D.R.m - 1 = j := by omega
  have hS : ch.G.V (.grid 0 j) = Yc D (D.R.m - 1) := by
    rw [e]; exact congrArg LSp.sp (colY_lt R.toLevCh (by omega))
  have hT : ch.G.V (.grid 0 (j + 1)) = D.sp.X' := by
    show (columnBlock R.toLevCh (j + 1)).sp = _
    rw [hj, colY_m]
  have hcS : HEq (ch.W.cart (.grid 0 j)) (cart (R.MY (D.R.m - 1))) := by
    rw [e]; exact hW.cartY j (by omega)
  have hoS : HEq (ch.W.onb (.grid 0 j)) (onb (R.MY (D.R.m - 1))) := by
    rw [e]; exact hW.onbY j (by omega)
  have hcT : HEq (ch.W.cart (.grid 0 (j + 1))) (cart R.MX) := by
    rw [hj]; exact hW.cartX
  have hoT : HEq (ch.W.onb (.grid 0 (j + 1))) (onb R.MX) := by
    rw [hj]; exact hW.onbX
  have hs : HEq (ch.W.fock (.mu t 0 j) fj P) (R.ptX t P₀) := pt_heq hW.ψ hW.θ hS hT hcS hcT hoS hoT hfj hP
  have hAt := hM.vtx (.grid 0 (j + 1)) ⟨Nat.zero_le _, by omega⟩
  have hfund := hAt.haar_fund
  have hK : HEq (levJ ch.G t (.grid 0 (j + 1))) (lev D.sp.cm D.sp.X'.gram R.βX (R.datXt t)) :=
    levCol_top R.toLevCh t (by omega)
  unfold Vol.IsAt at hAt
  rw [if_pos (show (Node.grid 0 (j + 1)).neg D.R.m = 0 by simp only [Node.neg]; omega)] at hAt
  have hc := hmod.νX t
  have hker := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ (R.ωX t) (hch.ωX t) _ (hch.ptX t P₀)).1
  exact step_heq hS hT (hW.omX t j hj) hs (measDef_heq hT hK hAt hc) hc.1.1 hfund.2 hc.2 hF (fun h γ hγ g => by
      have h1 := hker 1 (one_mem _) γ hγ h g
      rw [one_mul] at h1
      rw [h1, hinv γ hγ g]) hint

theorem col_ind {ch : Choice R} (hW : ch.W.Over R) (hch : R.IsChain) (hmod : R.IsModels) {t : T}
    {q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank} (hq : ChainPols ch q)
    {M : Vol ch.G} (hM : M.Is t) : ∀ n, n + 1 ≤ D.R.m → ∀ (g : ∀ j : Fin n, Sch ch.G (.down t 0 j)),
    (∀ j : Fin n, ∃ fj : Sch ch.G (.down t 0 j),
      HEq fj (R.vY t j) ∧ g j = ch.W.fock (.mu t 0 j) fj (q j)) →
    ∀ (F : Fn ch.G (.grid 0 n)) (F₀ : R.CC t n) (v : SmT (R.MY n)), HEq F (F₀.1 v) →
    PathConv ch.W M (downPath t 0 n) (downFam t 0 n g) F ∧
      HEq (liftP ch.W M (downPath t 0 n) (downFam t 0 n g) F) (ch.cv.dnFun t n (F₀.1 v)) := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ _ _ _ hF
    exact ⟨trivial, hF⟩
  | succ n ih =>
    intro hn g hg F F₀ v hF
    obtain ⟨fj, hfj, hgj⟩ := hg (Fin.last n)
    have hgj' : g (Fin.last n) = ch.W.fock (.mu t 0 n) fj (q n) := hgj
    have hio := hch.ioY t n (by omega)
    have hst := stepY hW hch hmod hM (j := n) (by omega) hfj ((hq n).1 (by omega)) hgj' hF
      (fun γ hγ g' => (GlobalTheory.ChainEquiv.multT_value _ _ _ _ F₀.1 F₀.2 v).1 γ hγ g') (fun h => hio.integ F₀ _ v h)
    have e1 : Lift.liftInt (R.νY t (n + 1)) (R.fdY t (n + 1)) (thetaKO (R.ωY t n)) (R.ptY t n (ch.cv.polY n)) (F₀.1 v) =
        (R.ioY t n F₀).1 (R.ItY n (ch.cv.polY n) v) := funext fun g' => hio.eq F₀ _ v g'
    rw [e1] at hst
    have hprev := ih (by omega) (fun j => g j.castSucc) (fun j => hg j.castSucc) _ (R.ioY t n F₀)
      (R.ItY n (ch.cv.polY n) v) hst.2
    refine ⟨(pathConv_comp ch.W M (Path.one (.down t 0 n)) ((), g (Fin.last n)) F (downPath t 0 n)
      (downFam t 0 n fun j => g j.castSucc)).2 ⟨⟨trivial, hst.1⟩, hprev.1⟩, ?_⟩
    refine HEq.trans (heq_of_eq (pathLift_comp ch.W M (Path.one (.down t 0 n)) ((), g (Fin.last n)) F (downPath t 0 n)
      (downFam t 0 n fun j => g j.castSucc))) ?_
    refine hprev.2.trans (heq_of_eq ?_)
    show _ = ch.cv.dnFun t n _
    rw [e1]

theorem formX_inv (hmod : R.IsModels) (d : ChainVec R) (t : T) (y : (R.HX t).H) :
    ∀ γ ∈ GQ D.sp.X', ∀ g, d.formX t y (γ * g) = d.formX t y g := by
  have hmem : (R.HX t).e y ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J
      (levEnv _ R.βX (R.datXt t)).χ := SetLike.le_def.1 (hmod.HX t).2.1.le (LinearMap.mem_range_self _ y)
  have := GlobalTheory.ThetaIntegrand.ext_invariant R.cX hmem
  intro γ hγ g
  unfold ChainVec.formX
  simp only [CoefA.toMap, LinearMap.coe_mk, AddHom.coe_mk, this γ hγ g]

theorem col_ind' {ch : Choice R} (hW : ch.W.Over R) (hch : R.IsChain) (hmod : R.IsModels) {t : T}
    {q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank} (hq : ChainPols ch q)
    {M : Vol ch.G} (hM : M.Is t) {n n' : ℕ} (hn : n = n') (hn1 : n + 1 ≤ D.R.m) (g : ∀ j : Fin n, Sch ch.G (.down t 0 j))
    (hg : ∀ j : Fin n, ∃ fj : Sch ch.G (.down t 0 j),
      HEq fj (R.vY t j) ∧ g j = ch.W.fock (.mu t 0 j) fj (q j))
    (F : Fn ch.G (.grid 0 n)) (F₀ : R.CC t n') (v : SmT (R.MY n')) (hF : HEq F (F₀.1 v)) :
    PathConv ch.W M (downPath t 0 n) (downFam t 0 n g) F ∧
      HEq (liftP ch.W M (downPath t 0 n) (downFam t 0 n g) F) (ch.cv.dnFun t n' (F₀.1 v)) := by
  subst hn
  exact col_ind hW hch hmod hq hM n hn1 g hg F F₀ v hF

theorem col_top {ch : Choice R} (hW : ch.W.Over R) (hch : R.IsChain) (hmod : R.IsModels) {t : T}
    {q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank} (hq : ChainPols ch q)
    {M : Vol ch.G} (hM : M.Is t) (y : (R.HX t).H) : ∀ N, N = D.R.m → ∀ (g : ∀ j : Fin N, Sch ch.G (.down t 0 j)),
    (∀ j : Fin N, ((j : ℕ) + 1 < D.R.m → ∃ fj : Sch ch.G (.down t 0 j),
      HEq fj (R.vY t j) ∧ g j = ch.W.fock (.mu t 0 j) fj (q j)) ∧
      ((j : ℕ) + 1 = D.R.m → ∃ fj : Sch ch.G (.down t 0 j),
        HEq fj (R.vX t) ∧ g j = ch.W.fock (.mu t 0 j) fj (q j))) →
    ∀ F : Fn ch.G (.grid 0 N), HEq F (ch.cv.formX t y) →
    PathConv ch.W M (downPath t 0 N) (downFam t 0 N g) F ∧
      HEq (liftP ch.W M (downPath t 0 N) (downFam t 0 N g) F) (ch.cv.lift t y) := by
  intro N
  cases N with
  | zero =>
    intro h
    have := D.R.two_le_m
    omega
  | succ k =>
    intro hk g hg F hF
    obtain ⟨fj, hfj, hgj⟩ := (hg (Fin.last k)).2 (by simp only [Fin.val_last]; omega)
    have hgj' : g (Fin.last k) = ch.W.fock (.mu t 0 k) fj (q k) := hgj
    have hio := hch.ioX t
    have hst := stepX hW hch hmod hM (j := k) (by omega) hfj ((hq k).2 (by omega)) hgj' hF (formX_inv hmod ch.cv t y)
      (fun h => hio.integ ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y) ch.cv.polX ch.cv.v h)
    have e1 : Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t ch.cv.polX) (ch.cv.formX t y) =
        (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 (R.ItX ch.cv.polX ch.cv.v) :=
      funext fun g' => hio.eq ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y) ch.cv.polX ch.cv.v g'
    rw [e1] at hst
    have ih := col_ind' hW hch hmod hq hM (n := k) (n' := D.R.m - 1) (by omega) (by omega) (fun j => g j.castSucc)
      (fun j => (hg j.castSucc).1 (by have := j.2; simp only [Fin.coe_castSucc]; omega)) _
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)) (R.ItX ch.cv.polX ch.cv.v) hst.2
    refine ⟨(pathConv_comp ch.W M (Path.one (.down t 0 k)) ((), g (Fin.last k)) F (downPath t 0 k)
      (downFam t 0 k fun j => g j.castSucc)).2 ⟨⟨trivial, hst.1⟩, ih.1⟩, ?_⟩
    refine HEq.trans (heq_of_eq (pathLift_comp ch.W M (Path.one (.down t 0 k)) ((), g (Fin.last k)) F
      (downPath t 0 k) (downFam t 0 k fun j => g j.castSucc))) ?_
    refine ih.2.trans (heq_of_eq ?_)
    exact (congrArg (ch.cv.dnFun t (D.R.m - 1)) e1).symm

end GlobalTheory.FlipStart.Col


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarLocalIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.SplitMoveKappa

theorem om_toPair_mul : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R) (p : Pair T) (s x : FinPt ch.G p.small) (s' y : FinPt ch.G p.big) (v : WO (ch.G.pS p) (ch.G.pT p) → ℂ),
    ch.W.om p (ch.G.toPair p ((s * x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((s' * y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) v =
      ch.W.om p (ch.G.toPair p (s : Formalism.L2.Theta.GA D (ch.G.V p.small)) (s' : Formalism.L2.Theta.GA D (ch.G.V p.big)))
        (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) v) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch p s x s' y v
  have e1 : ((s * x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) =
      (s : Formalism.L2.Theta.GA D (ch.G.V p.small)) * ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) := by
    rw [mul_assoc]; rfl
  have e2 : ((s' * y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) =
      (s' : Formalism.L2.Theta.GA D (ch.G.V p.big)) * ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big)) := by
    rw [mul_assoc]; rfl
  have e3 : ∀ (a b : Formalism.L2.Theta.GA D (ch.G.V p.small)) (c d : Formalism.L2.Theta.GA D (ch.G.V p.big)),
      ch.G.toPair p (a * b) (c * d) = ch.G.toPair p a c * ch.G.toPair p b d := by
    intro a b c d
    cases p <;> simp [GlobalTheory.ChiGrid.GridData.toPair, map_mul]
  rw [e1, e2, e3, map_mul]
  rfl

end GlobalTheory.SplitMoveKappa
end
end
