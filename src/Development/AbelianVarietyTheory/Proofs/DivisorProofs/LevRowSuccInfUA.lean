module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointLeSpanGoodBlock

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.LevRowSucc

open GlobalTheory.AdIsom GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

variable {D : D7}

theorem mem_O_iff {w : Pl D.host.E} (a : Kw w) : a ∈ 𝒪[Kw w] ↔ Valued.v a ≤ 1 := by
  have : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (Kw w)) Valued.v).le_one_iff_le_one

theorem inBasis_val {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).val i j = cpt w ((β⁻¹ * x * β).val (Fin.cast h i) (Fin.cast h j)) := by
  simp only [inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rfl

theorem ent_of_KO {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (hx : inBasis h β w x ∈ KO (Kw w) (Fin n')) :
    (∀ i j, Valued.v (cpt w ((β⁻¹ * x * β).val i j)) ≤ 1) ∧ ∀ i j, Valued.v (cpt w ((β⁻¹ * x⁻¹ * β).val i j)) ≤ 1 := by
  subst h
  obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 hx
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have := (mem_O_iff _).1 (h1 i j)
    rwa [inBasis_val] at this
  · have := (mem_O_iff _).1 (h2 i j)
    rwa [← map_inv, inBasis_val] at this

theorem KO_of_St {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) {x : GL (Fin n) (Lev.EAf D)}
    (hx : x ∈ St β) : inBasis h β w x ∈ KO (Kw w) (Fin n') := by
  subst h
  obtain ⟨z, rfl⟩ := hx
  have e1 : β⁻¹ * frGL β z * β = intGL D.host.F D.host.E _ z := by
    show β⁻¹ * (β * intGL D.host.F D.host.E _ z * β⁻¹) * β = _
    group
  have e2 : β⁻¹ * (frGL β z)⁻¹ * β = intGL D.host.F D.host.E _ z⁻¹ := by
    rw [← map_inv]
    show β⁻¹ * (β * intGL D.host.F D.host.E _ z⁻¹ * β⁻¹) * β = _
    group
  refine (mem_KO_iff _).2 ⟨fun i j => (mem_O_iff _).2 ?_, fun i j => (mem_O_iff _).2 ?_⟩
  · rw [inBasis_val, e1]
    exact (mem_OA _).1 (z.val _ _).2 w
  · rw [← map_inv, inBasis_val, e2]
    exact (mem_OA _).1 ((z⁻¹).val _ _).2 w

theorem idem_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (Lev.EAf D)}
    (hβ : IsFrame β Λ) {w : Pl D.host.E} {x : GL (Fin n) (Lev.EAf D)}
    (hx : ∀ i j, Valued.v (cpt w ((β⁻¹ * x * β).val i j)) ≤ 1) {y : Fin n → Lev.EAf D} (hy : y ∈ hat Λ) :
    idem w • (x.val *ᵥ y) ∈ hat Λ := by
  rw [mem_hat, hβ] at hy ⊢
  intro i
  have e : (β⁻¹).val *ᵥ (idem w • (x.val *ᵥ y)) = idem w • ((β⁻¹ * x * β).val *ᵥ ((β⁻¹).val *ᵥ y)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [e, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  rw [← mul_assoc]
  exact mul_mem ((idem_mul_mem_iff w _).2 (hx i j)) (hy j)

theorem hA_unitary {V : HSp D} {x : GL (Fin V.rank) (Lev.EAf D)} (hx : x ∈ UA D.sp.cm V.gram)
    (a b : Fin V.rank → Lev.EAf D) : hA V (x.val *ᵥ a) (x.val *ᵥ b) = hA V a b := by
  have hx' : Formalism.UG.cT (cjA D) x.val * V.gram.map (inc D) * x.val = V.gram.map (inc D) := hx
  have e2 : ∀ u v : Fin V.rank → Lev.EAf D,
      Formalism.UG.hform (cjA D) (V.gram.map (inc D)) u v = (cjA D ∘ u) ⬝ᵥ (V.gram.map (inc D) *ᵥ v) := by
    intro u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : cjA D ∘ (x.val *ᵥ b) = (cjA D ∘ b) ᵥ* Formalism.UG.cT (cjA D) x.val := by
    funext i
    rw [Formalism.UG.cT, vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  rw [hA_eq, hA_eq, e2, e2, e3, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hx']

theorem transfer {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hsd : IsSelfDualC V Λ)
    {x : GL (Fin V.rank) (Lev.EAf D)} (hU : x ∈ UA D.sp.cm V.gram) {w : Pl D.host.E}
    (h : ∀ y ∈ hat Λ, idem w • ((x⁻¹).val *ᵥ y) ∈ hat Λ) {y : Fin V.rank → Lev.EAf D} (hy : y ∈ hat Λ) :
    idem (GlobalTheory.IdemSupport.cP w) • (x.val *ᵥ y) ∈ hat Λ := by
  rw [mem_hat_iff_of_selfDual hsd]
  intro z hz
  have e : z = x.val *ᵥ ((x⁻¹).val *ᵥ z) := by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  rw [hA_smul_right, cjA_idem, GlobalTheory.StdFrames.cP_cP, e, hA_unitary hU, ← hA_smul_left]
  exact (mem_hat_iff_of_selfDual hsd y).1 hy _ (h z hz)

theorem givenLevel_succ {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) (a : ℕ) :
    ∀ b, b ≠ 0 → givenLevel G t w (a + 1, b) = KO (Kw w) (Fin ((locGrid G t w).rank (a + 1, b)))
  | 0, h => absurd rfl h
  | _ + 1, _ => rfl


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem prodLev_inf_UA {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Lev.EAf D)}
    (hβ : IsFrame β Λ) (hsd : IsSelfDualC V Λ) (P : Finset (Pl D.host.E)) {n' : P → ℕ} (hn : ∀ w, n' w = V.rank)
    (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (hK : ∀ w, K w = KO (Kw w.1) (Fin (n' w))) :
    prodLev β P hn K ⊓ UA D.sp.cm V.gram = congLev D.sp.cm V.gram Λ ⊤ := by
  rw [congLev_top]
  have key : ∀ g ∈ prodLev β P hn K ⊓ UA D.sp.cm V.gram, ∀ (Q : Pl D.host.E), ∀ y ∈ hat Λ,
      idem Q • (g.val *ᵥ y) ∈ hat Λ := by
    rintro g hg Q y hy
    obtain ⟨hg, hU⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hA', hB'⟩ := Subgroup.mem_inf.1 hg
    have hA : ∀ w : P, (∀ i j, Valued.v (cpt w.1 ((β⁻¹ * g * β).val i j)) ≤ 1) ∧
        ∀ i j, Valued.v (cpt w.1 ((β⁻¹ * g⁻¹ * β).val i j)) ≤ 1 := fun w => by
      have := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hA' w)
      rw [hK] at this
      exact ent_of_KO _ β g w.1 this
    by_cases hQ : ∃ w ∈ P, Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)
    · obtain ⟨w, hw, hQw⟩ := hQ
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP hQw with rfl | rfl
      · exact idem_smul_mem hβ (hA ⟨Q, hw⟩).1 hy
      · exact transfer hsd hU (fun y hy => idem_smul_mem hβ (hA ⟨w, hw⟩).2 hy) hy
    · push Not at hQ
      have := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hB' Q) hQ)
      exact idem_smul_mem hβ (ent_of_KO _ β g Q this).1 hy
  ext x
  constructor
  · intro hx
    have hS : x ∈ St β := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).2
      ⟨fun y hy => mem_hat_of_idem hsd.1.fg fun Q => key x hx Q y hy,
        fun y hy => mem_hat_of_idem hsd.1.fg fun Q => key x⁻¹ (inv_mem hx) Q y hy⟩
    obtain ⟨h1, h2⟩ := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).1 hS
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, ?_⟩
    intro y
    refine ⟨fun hy => h1 y hy, fun hy => ?_⟩
    have := h2 _ hy
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
    exact this
  · intro hx
    obtain ⟨hU, hst⟩ := Subgroup.mem_inf.1 hx
    have hS : x ∈ St β := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).2
      ⟨fun y hy => (hst y).1 hy, fun y hy => (hst _).2 (by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]; exact hy)⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
      Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => ?_⟩, hU⟩
    · rw [Subgroup.mem_comap, hK]
      exact KO_of_St _ β w.1 hS
    · rw [Subgroup.mem_comap]
      exact KO_of_St _ β w' hS

end GlobalTheory.FunObj.LevRowSucc

namespace GlobalTheory.FunObj.GridChoice

open GlobalTheory.FunObj.LevRowSucc

theorem levRow_succ_inf_UA {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) (t : T) (i : ℕ) (h : i + 1 ≤ D.R.m) :
    S.levRow t (i + 1) h ⊓ UA D.sp.cm (G.V (.grid (i + 1) D.R.m)).gram = G.levMax (.grid (i + 1) D.R.m) := by
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  rw [GridData.levMax]
  exact prodLev_inf_UA (S.B.isFrame (i + 1) D.R.m (by omega) h le_rfl)
    (G.isV (X := .grid (i + 1) D.R.m) ⟨h, le_rfl⟩ fun j e => by cases e).sd (locPl G t) _ _
    fun w => givenLevel_succ G t w.1 i D.R.m hm

end GlobalTheory.FunObj.GridChoice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwich
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.DetInv.HTKer

theorem sat_of_ker_eq_range {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C] [IsFractionRing O C]
    {h : ℕ} (a b : Matrix (Fin h) (Fin h) O)
    (H : LinearMap.ker (toLin' (a.map (algebraMap O C))) = LinearMap.range (toLin' (b.map (algebraMap O C))))
    (y : Fin h → O) : toLin' a y = 0 ↔ ∃ c : O, c ≠ 0 ∧ ∃ m, c • y = toLin' b m := by
  have inj : Function.Injective (algebraMap O C) := IsFractionRing.injective O C
  have key : ∀ (X : Matrix (Fin h) (Fin h) O) (z : Fin h → O),
      toLin' (X.map (algebraMap O C)) (fun i => algebraMap O C (z i)) = fun i => algebraMap O C (toLin' X z i) := by
    intro X z
    funext i
    simp [toLin'_apply, mulVec, dotProduct]
  constructor
  · intro hy
    have h1 : (fun i => algebraMap O C (y i)) ∈ LinearMap.ker (toLin' (a.map (algebraMap O C))) := by
      rw [LinearMap.mem_ker, key, hy]; funext i; simp
    rw [H] at h1
    obtain ⟨z, hz⟩ := h1
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) z
    choose m hm using hc
    refine ⟨c, nonZeroDivisors.ne_zero c.2, m, ?_⟩
    funext i
    apply inj
    have h2 : (fun i => algebraMap O C (m i)) = algebraMap O C c • z := by
      funext j; rw [hm j]; simp [Algebra.smul_def]
    have h3 := congrFun (key b m) i
    rw [h2, map_smul, hz] at h3
    rw [← h3]; simp
  · rintro ⟨c, hc, m, hm⟩
    have h1 : (fun i => algebraMap O C (toLin' b m i)) ∈ LinearMap.ker (toLin' (a.map (algebraMap O C))) := by
      rw [H]; exact ⟨_, key b m⟩
    rw [LinearMap.mem_ker, key, ← hm, map_smul] at h1
    funext i
    have h2 := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, map_eq_zero_iff _ inj, mul_eq_zero] at h2
    exact h2.resolve_left hc

theorem finrank_ker_of_sat {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.IsTorsionFree O M] (a b : M →ₗ[O] M)
    (H : ∀ y, a y = 0 ↔ ∃ c : O, c ≠ 0 ∧ ∃ m, c • y = b m) :
    Module.finrank O (LinearMap.ker a) = Module.finrank O (M ⧸ LinearMap.ker b) := by
  have hle : LinearMap.range b ≤ LinearMap.ker a := by
    rintro _ ⟨m, rfl⟩
    exact (H _).2 ⟨1, one_ne_zero, m, one_smul _ _⟩
  have h1 := Submodule.rank_quotient_add_rank (R := O) ((LinearMap.range b).comap (LinearMap.ker a).subtype)
  have h2 : Module.rank O (LinearMap.ker a ⧸ (LinearMap.range b).comap (LinearMap.ker a).subtype) = 0 := by
    rw [rank_eq_zero_iff_isTorsion]
    intro x
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨c, hc, m, hm⟩ := (H y).1 hy
    refine ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, ?_⟩
    change c • Submodule.mkQ ((LinearMap.range b).comap (LinearMap.ker a).subtype) ⟨y, hy⟩ = 0
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨m, hm.symm⟩
  rw [h2, zero_add, (Submodule.comapSubtypeEquivOfLe hle).rank_eq, ← (LinearMap.quotKerEquivRange b).rank_eq] at h1
  unfold Module.finrank
  rw [h1]

theorem finrank_dual_ker {O : Type} [CommRing O] [IsDomain O] [ValuationRing O] {h : ℕ}
    (b : (Fin h → O) →ₗ[O] (Fin h → O)) :
    Module.finrank O (Module.Dual O (LinearMap.ker b)) = Module.finrank O (LinearMap.ker b) := by
  have free : ∀ (N : Submodule O (Fin h → O)) [Module.Finite O N], Module.Free O N := by
    intro N _
    have : Module.Flat O N := by
      rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
      exact Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance
    exact Module.free_of_flat_of_isLocalRing
  haveI := free (LinearMap.range b)
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective b.rangeRestrict
    (LinearMap.range_rangeRestrict b)
  have hb : ∀ m, b (s (b.rangeRestrict m)) = b m := fun m =>
    congrArg Subtype.val (LinearMap.congr_fun hs (b.rangeRestrict m))
  haveI : Module.Finite O (LinearMap.ker b) := by
    refine Module.Finite.of_surjective
      (LinearMap.codRestrict (LinearMap.ker b) (LinearMap.id - s ∘ₗ b.rangeRestrict) (fun m => by
        simp [hb])) ?_
    rintro ⟨m, hm⟩
    refine ⟨m, Subtype.ext ?_⟩
    have : b.rangeRestrict m = 0 := Subtype.ext hm
    simp [this]
  haveI := free (LinearMap.ker b)
  rw [Module.finrank_linearMap, Module.finrank_self, mul_one]

section
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]

noncomputable def coordO {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) :
    O ⊗[ℤ_[p]] G.Tate ≃ₗ[O] (Fin h → O) :=
  (LinearEquiv.baseChange ℤ_[p] O _ _ e).trans (TensorProduct.piScalarRight ℤ_[p] O O (Fin h))

theorem coordO_tmul {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (c : O) (t : G.Tate) :
    coordO e (c ⊗ₜ t) = c • IndefiniteRowSideFullHecke.EpsilonPairingZeta.toO e t := by
  funext i
  simp [coordO, IndefiniteRowSideFullHecke.EpsilonPairingZeta.toO, Algebra.smul_def, ← padicToO_unique p O (algebraMap ℤ_[p] O), mul_comm]

variable [IsDomain O] {ε : PreTilt O p} {hε : IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε}

omit [Algebra ℤ_[p] O] in
theorem pairingO_add {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (y z : Fin h → O)
    (χ : G.dual.Tate) : IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e (y + z) χ =
      IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e y χ + IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e z χ := by
  simp [IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO, add_mul, Finset.sum_add_distrib]

omit [Algebra ℤ_[p] O] in
theorem pairingO_smul {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (c : O) (y : Fin h → O)
    (χ : G.dual.Tate) : IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e (c • y) χ = c * IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e y χ := by
  simp [IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO, Finset.mul_sum, mul_assoc]


omit [Algebra ℤ_[p] O] in
theorem pairingO_inj {G : PDivGroup p O} (hG : Function.Surjective (G.pairing O).flip) {h : ℕ}
    (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (y z : Fin h → O)
    (H : ∀ χ, IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e y χ = IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e z χ) : y = z := by
  funext i
  obtain ⟨χ, hχ⟩ := hG ((IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsEquiv hε).toLinearMap ∘ₗ LinearMap.proj i ∘ₗ e.toLinearMap)
  have h1 : ∀ t, IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing hε G t χ = e t i := by
    intro t
    have := LinearMap.congr_fun hχ t
    simp only [LinearMap.flip_apply] at this
    rw [IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing, this]
    simp
  have h2 : ∀ w : Fin h → O, IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e w χ = w i := by
    intro w
    simp only [IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO, h1, LinearEquiv.apply_symm_apply]
    rw [Finset.sum_eq_single i] <;> simp +contextual [Pi.single_apply, eq_comm]
  rw [← h2 y, ← h2 z, H]

variable {u₁ u₂ : Oˣ} {G : PDivGroup p O} {h : ℕ} {D : Datum ε h ℤ_[p]} {e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])}
  {fil : G.dual.omega ≃ₗ[O] D.Fil} {lie : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] G.Lie}

theorem al_coordO (R : IndefiniteRowSideFullHecke.EpsilonPairingZeta.Realizes hε u₁ u₂ G G.padicAction D e fil lie) (x : O ⊗[ℤ_[p]] G.Tate) :
    D.al (coordO e x) = (u₁ : O) • (fil (G.hodgeTateLinear x) : Fin h → O) := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [(coordO e).map_zero, D.al.map_zero, G.hodgeTateLinear.map_zero, fil.map_zero]
    simp
  | tmul c t =>
    rw [coordO_tmul, map_smul, R.al_eq, hodgeTateLinear_tmul, hodgeTate_eq_omegaMap, map_smul,
      Submodule.coe_smul, smul_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, Submodule.coe_add, smul_add]

theorem ht_eq_zero_iff (R : IndefiniteRowSideFullHecke.EpsilonPairingZeta.Realizes hε u₁ u₂ G G.padicAction D e fil lie) (x : O ⊗[ℤ_[p]] G.Tate) :
    G.hodgeTateLinear x = 0 ↔ D.al (coordO e x) = 0 := by
  rw [al_coordO R, ← Units.smul_def, smul_eq_zero_iff_eq, Submodule.coe_eq_zero, fil.map_eq_zero_iff]

theorem finrank_ker_ht (R : IndefiniteRowSideFullHecke.EpsilonPairingZeta.Realizes hε u₁ u₂ G G.padicAction D e fil lie)
    (H : ∀ y, D.al y = 0 ↔ ∃ c : O, c ≠ 0 ∧ ∃ m, c • y = D.bb m) :
    Module.finrank O (LinearMap.ker G.hodgeTateLinear) = Module.finrank O G.Lie := by
  rw [← lie.finrank_eq]
  refine Eq.trans ?_ (finrank_ker_of_sat D.al D.bb H)
  refine LinearEquiv.finrank_eq (LinearEquiv.ofSubmodules (coordO e) _ _ ?_)
  ext y
  obtain ⟨x, rfl⟩ := (coordO e).surjective y
  simp [ht_eq_zero_iff R]

omit [Algebra ℤ_[p] O] in
theorem finrank_lie_add [ValuationRing O] (fil : G.dual.omega ≃ₗ[O] D.Fil)
    (lie : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] G.Lie) :
    Module.finrank O G.Lie + Module.finrank O G.dual.Lie = h := by
  have h1 : Module.finrank O G.dual.Lie = Module.finrank O D.Fil :=
    fil.dualMap.finrank_eq.symm.trans (finrank_dual_ker D.bb)
  rw [h1, ← lie.finrank_eq, Submodule.finrank_quotient_add_finrank]
  simp

end

theorem ker_hodgeTateLinear : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ (G : PDivGroup p O) (ζ : (PDivGroup.mu p O).Tate) (B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]), v.Integers O → Function.Bijective (fun a : ℤ_[p] => a • ζ) → (∀ s χ, pairing G O s χ = B s χ • ζ) → (∀ x : O ⊗[ℤ_[p]] G.Tate, G.hodgeTateLinear x = 0 ↔ ∃ (c : O) (y : G.Lie), c ≠ 0 ∧ ∀ χ, c * (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) = y (dlog (G := G) χ)) ∧ Module.finrank O (LinearMap.ker G.hodgeTateLinear) + Module.finrank O (LinearMap.ker G.dual.hodgeTateLinear) = G.height := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε hS G ζ B hv hζ hB
  obtain ⟨u₁, u₂, hS⟩ := hS
  haveI : IsFractionRing O C := hv.isFractionRing
  haveI : ValuationRing O := by
    refine @ValuationRing.mk O _ _ ⟨fun a b => ?_⟩
    rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inr hc.symm⟩
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inl hc.symm⟩
  have hroot : IsPrimitiveRoot (PreTilt.untilt (root ε)) p := by
    simpa [IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta] using hε 1
  have sat : ∀ {h : ℕ} (D : Datum ε h ℤ_[p]) (y), D.al y = 0 ↔ ∃ c : O, c ≠ 0 ∧ ∃ m, c • y = D.bb m := by
    intro h D y
    refine sat_of_ker_eq_range (C := C) _ _ ?_ y
    have := (ker_bC_eq_range_alC_and_ker_alC_eq_range_bC p C v O hv ε hroot ℤ_[p] h D).2
    simpa only [alC, bC, redC, Matrix.map_map, RingHom.coe_comp] using this
  obtain ⟨D, e, fil, lie, R⟩ := hS G ℤ_[p] G.padicAction
  obtain ⟨D', e', fil', lie', R'⟩ := hS G.dual ℤ_[p] G.dual.padicAction
  refine ⟨fun x => ?_, ?_⟩
  swap
  · rw [finrank_ker_ht R (sat D), finrank_ker_ht R' (sat D')]
    exact finrank_lie_add fil lie
  have hperf : Function.Surjective (G.pairing O).flip :=
    (tate_free_perfect p O C G).2.2.2.2.2.2.2.2

  obtain ⟨w, hw⟩ := hζ.2 (IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsTate hε)
  obtain ⟨w', hw'⟩ := (IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsEquiv hε).surjective ζ
  have hw'' : w' • IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsTate hε = ζ := hw'
  have hww : w' * w = 1 := by
    apply hζ.1
    simp only at hw ⊢
    rw [mul_smul, hw, hw'', one_smul]
  have hBe : ∀ t χ, B t χ = IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing hε G t χ * w := by
    intro t χ
    apply hζ.1
    simp only at hw ⊢
    rw [mul_smul, hw, IndefiniteRowSideFullHecke.EpsilonPairingZeta.epsPairing_smul, hB]
  set W : O := algebraMap ℤ_[p] O w
  set W' : O := algebraMap ℤ_[p] O w'
  have hWW : W' * W = 1 := by rw [← map_mul, hww, map_one]
  have hBO : ∀ (x : O ⊗[ℤ_[p]] G.Tate) χ, (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) =
      W * IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e (coordO e x) χ := by
    intro x χ
    induction x using TensorProduct.induction_on with
    | zero =>
      have := pairingO_smul (hε := hε) e 0 0 χ
      simp only [zero_smul, zero_mul] at this
      simp [this]
    | tmul c t =>
      rw [coordO_tmul, pairingO_smul, IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO_toO, ← padicToO_unique p O (algebraMap ℤ_[p] O)]
      simp only [LinearMap.baseChange_tmul, LinearMap.flip_apply, rid_tmul, hBe, Algebra.smul_def, map_mul, W]
      ring
    | add x y hx hy => simp only [map_add (f := _), hx, hy, pairingO_add, mul_add]
  have hb : ∀ (m : Fin G.height → O) χ, IndefiniteRowSideFullHecke.EpsilonPairingZeta.pairingO hε e (D.bb m) χ =
      u₂ * lie (D.Fil.mkQ m) (dlog (G := G) χ) := by
    intro m χ
    rw [dlog_eq_omegaMap, ← R.b_eq, LinearEquiv.symm_apply_apply]
    rfl
  rw [ht_eq_zero_iff R, sat]
  constructor
  · rintro ⟨c, hc, m, hm⟩
    refine ⟨c, (W * u₂) • lie (D.Fil.mkQ m), hc, fun χ => ?_⟩
    rw [hBO, LinearMap.smul_apply, smul_eq_mul, mul_assoc, ← hb, ← hm, pairingO_smul]
    ring
  · rintro ⟨c, y, hc, hy⟩
    obtain ⟨m, hm⟩ := D.Fil.mkQ_surjective (lie.symm y)
    refine ⟨c * W * u₂, ?_, m, pairingO_inj (hε := hε) hperf e _ _ fun χ => ?_⟩
    · exact mul_ne_zero (mul_ne_zero hc (right_ne_zero_of_mul_eq_one hWW)) u₂.ne_zero
    · rw [hb, hm, LinearEquiv.apply_symm_apply, ← hy, hBO, pairingO_smul]
      ring

end GlobalTheory.DetInv.HTKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintOfEntries
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj

open Filter Topology

variable {D : D7}

theorem mem_GLint_of_entries {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L)
    (h1 : ∀ i j, g.1 i j ∈ O) (h2 : ∀ i j, g⁻¹.1 i j ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) O => A.map O.subtype :=
    Matrix.map_injective Subtype.val_injective
  refine ⟨⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩, hi ?_, hi ?_⟩, Units.ext rfl⟩
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.mul_inv
  · simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact g.inv_mul

theorem inBasis_apply {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).1 i j = cpt w ((β⁻¹ * x * β).1 (finCongr h i) (finCongr h j)) := rfl

theorem inBasis_mem_KO {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (hx : x ∈ St β) (w : Pl D.host.E) :
    inBasis rfl β w x ∈ KO (Kw w) (Fin n) := by
  obtain ⟨y, rfl⟩ := hx
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
  have hm : ∀ z : GL (Fin n) (Lev.EAf D), z ∈ ({Formalism.L2.DIV.intGL _ _ n y, (Formalism.L2.DIV.intGL _ _ n y)⁻¹} : Set _) →
      ∀ a b, cpt w (z.1 a b) ∈ Formalism.UG.Ov D.host.E w := by
    intro z hz a b
    refine (mem_OA_iff _).1 ?_ w
    rcases hz with rfl | rfl
    · exact (y.1 a b).2
    · rw [← map_inv]; exact ((y⁻¹).1 a b).2
  have e1 : β⁻¹ * Formalism.L2.DIV.frGL β y * β = Formalism.L2.DIV.intGL _ _ n y := by
    simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply]
    group
  have e2 : β⁻¹ * (Formalism.L2.DIV.frGL β y)⁻¹ * β = (Formalism.L2.DIV.intGL _ _ n y)⁻¹ := by
    rw [← e1]; group
  refine mem_GLint_of_entries _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [inBasis_apply, e1]; exact hm _ (Or.inl rfl) _ _
  · rw [← map_inv, inBasis_apply, e2]; exact hm _ (Or.inr rfl) _ _

end GlobalTheory.FunObj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointLiftRangeLeGoodBlockEigenspaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfSemilinearMemComplexSpan
namespace GlobalTheory

theorem mem_of_semilinear_mem_complex_span : ∀ {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] [Finite ι] (σ : K →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι K V), LinearIndependent ℂ (fun k => j (b k)) → ∀ (U : Submodule K V) (x : V), j x ∈ Submodule.span ℂ (j '' (U : Set V)) → x ∈ U := by
  intro K V W ι _ _ _ _ _ _ σ j b hli U x hx
  by_contra hxU
  obtain ⟨f, hfx, hfU⟩ := U.exists_dual_map_eq_bot_of_notMem hxU inferInstance
  obtain ⟨L, hL⟩ := (Finsupp.linearCombination ℂ (fun k => j (b k))).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hli)
  let g : W →ₗ[ℂ] ℂ := (Finsupp.linearCombination ℂ (fun k => σ (f (b k)))).comp L
  have hb : ∀ k, g (j (b k)) = σ (f (b k)) := by
    intro k
    have h1 : L (j (b k)) = Finsupp.single k 1 := by
      have := LinearMap.congr_fun hL (Finsupp.single k 1)
      simpa using this
    simp [g, h1]
  have hg : ∀ v, g (j v) = σ (f v) := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hv using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hb k
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy => rw [j.map_smulₛₗ, map_smul, map_smul, hy]; simp
  have hle : Submodule.span ℂ (j '' (U : Set V)) ≤ LinearMap.ker g := by
    rw [Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have : f u = 0 := by
      have : f u ∈ U.map f := ⟨u, hu, rfl⟩
      rw [hfU] at this
      simpa using this
    simp [hg, this]
  have h0 : σ (f x) = 0 := by rw [← hg]; exact hle hx
  exact hfx (by simpa using h0)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointLiftRangeLeGoodBlockEigenspaces
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.Hk3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem range_adjoint_smul_le {E E' : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E'] (c : ℂ) (f : E →ₗ[ℂ] E') :
    LinearMap.range (LinearMap.adjoint (c • f)) ≤ LinearMap.range (LinearMap.adjoint f) := by
  rintro _ ⟨y, rfl⟩
  rw [RealDat3.adjoint_smul']
  exact ⟨starRingEnd ℂ c • y, by simp⟩

theorem inBlock_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → R.PGEquiv F → (R.toCx3 F).zs.InBlock := by
  intro hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hL hOk hC hE hG
  obtain ⟨h1, h2⟩ := GlobalTheory.T.range_adjoint_le_span_jX_image_ZHg R F hL hOk hC hE (schurAll_of_cuspRapidDecay hP R.toRealDat) hG
  have hM := hC.base.models
  refine ⟨fun t x hx => ?_, fun j t x hx => ?_⟩
  · have hB := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.R t).pres
    obtain ⟨hinj, hrange, -⟩ := hM.HX t
    have h := kForm_semi (R.jX t) (R.HX t).e (R.B.R t).pres.extL (fun x => hM.jX t x) hinj (hrange.trans hB.2.symm)
      (Formalism.L2.DIV.CSD.basis _) (Formalism.L2.DIV.CSD.basis _) hB.1
    have hx' : R.jX t x ∈ LinearMap.range (LinearMap.adjoint (R.Th t)) :=
      (GlobalTheory.AdjBlock.mem_range_adjoint_tw (twAt D.what₂.embLL A3.A.v0) (R.Th t) (R.jX t x)).1 hx
    exact GlobalTheory.mem_of_semilinear_mem_complex_span D.what₂.embLL (R.jX t) (Formalism.L2.DIV.CSD.basis _) h.1 _ x (h1 t hx')
  · have hB := Formalism.IndefR.Bridge.ClassPres.extBij_holds (R.B.L j t).pres
    obtain ⟨hinj, hrange, -⟩ := hM.HV j t
    have h := kForm_semi (R.jV j t) (R.HV j t).e (R.B.L j t).pres.extL (fun x => hM.jV j t x) hinj (hrange.trans hB.2.symm)
      (Formalism.L2.DIV.CSD.basis _) (Formalism.L2.DIV.CSD.basis _) hB.1
    have hx1 := range_adjoint_smul_le (R.phs j) (Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j t)) hx
    have hx' : R.jV j t x ∈ LinearMap.range (LinearMap.adjoint (R.thG j t)) :=
      (GlobalTheory.AdjBlock.mem_range_adjoint_tw (twAt D.what₂.embLL A3.A.v0) (R.thG j t) (R.jV j t x)).1 hx1
    exact GlobalTheory.mem_of_semilinear_mem_complex_span D.what₂.embLL (R.jV j t) (Formalism.L2.DIV.CSD.basis _) h.1 _ x (h2 j t hx')

end GlobalTheory.Hk3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointLiftRangeLeGoodBlockEigenspacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointLift_range_le_goodBlock_eigenspaces : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → R.PGEquiv F → (R.toCx3 F).zs.InBlock := by
  first | exact @GlobalTheory.Hk3.inBlock_of_cuspRapidDecay | exact GlobalTheory.Hk3.inBlock_of_cuspRapidDecay | (intros; apply GlobalTheory.Hk3.inBlock_of_cuspRapidDecay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMapToModel
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.RecSpan

open GlobalTheory.HTLat.OmegaRank

theorem exists_eigenbasis {V O : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [CommRing O]
    [Algebra V O] [Module.Flat V O] (G : Over (Sp V)) [GrpObj G] [Smooth G.hom] {Λ : Type} (act : Λ → (G ⟶ G))
    [∀ a, IsMonHom (act a)] (χ : Λ → V) {m : ℕ} (u : Fin m → (epsOver V V ⟶ G)) (ht : ∀ i, IsTan (u i))
    (he : ∀ i a, (u i ≫ act a).left = spMap (epsMul (χ a)) ≫ (u i).left)
    (hb : ∀ w : epsOver V V ⟶ G, IsTan w → (∀ a, (w ≫ act a).left = spMap (epsMul (χ a)) ≫ w.left) →
      ∃! c : Fin m → V, IsComb u c w)
    {G' : Over (Sp O)} [GrpObj G'] {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (spMap (algebraMap V O)) π)
    (act' : Λ → (G' ⟶ G')) (ha : ∀ a, (act' a).left ≫ π = π ≫ (act a).left) :
    ∃ u' : Fin m → (specO O (DualNumber O) ⟶ G'),
      (∀ i, (u' i).left ≫ π = spMap (dualMap (algebraMap V O)) ≫ (u i).left) ∧
      ∀ w : LieG G', (∀ a, w.1 ≫ act' a = ptMap (dualScale (algebraMap V O (χ a))) ≫ w.1) →
        ∃ c : Fin m → O, w.1 = (List.ofFn fun i => ptMap (dualScale (c i)) ≫ u' i).prod := by
  obtain ⟨u', -, -, h3, h4⟩ := PlaceInt.Ext.exists_eigenbasis_pullback (V' := O) G act χ u ht he hb
  obtain ⟨e, he, he'⟩ := grpPullback_iso hπ (isGrpPullback_pullback G _)
  refine ⟨fun i => u' i ≫ e.inv, fun i => ?_, fun w hw => ?_⟩
  · rw [← he', ← Category.assoc, ← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
    exact h4 i
  · have hc : ∀ a, e.hom ≫ (Over.pullback (spMap (algebraMap V O))).map (act a) = act' a ≫ e.hom := fun a => by
      refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
      have A : ((Over.pullback (spMap (algebraMap V O))).map (act a)).left ≫ pullback.fst G.hom _ =
        pullback.fst G.hom _ ≫ (act a).left := pullback.lift_fst _ _ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, A, he', ha, ← Category.assoc, he']
    obtain ⟨c, ⟨y, hy, hy'⟩, -⟩ := h3 (w.1 ≫ e.hom) (by
      have h := congrArg (fun z => (z ≫ e.hom).left) w.2
      simp only [Category.assoc, IsMonHom.one_hom] at h
      exact h) fun a => by
        have h := congrArg (fun z => (z ≫ e.hom).left) (hw a)
        simp only [Category.assoc, ← hc] at h
        exact h
    refine ⟨c, ?_⟩
    have h := congrArg (IsMonHom.monoidHom e.inv _) hy'
    rw [map_list_prod, List.map_ofFn] at h
    refine Eq.trans ?_ (h.trans ?_)
    · exact ((Category.assoc _ _ _).trans (by rw [e.hom_inv_id, Category.comp_id])).symm
    · congr 2
      funext i
      exact (congrArg (· ≫ e.inv) (show y i = ptMap (dualScale (c i)) ≫ u' i from Over.OverMorphism.ext (hy i))).trans
        (Category.assoc _ _ _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [StarRing (𝓞 E)] {P : Point p v O (𝓞 E)}

theorem exists_map_to_model {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
    [IsFractionRing V F] {x₀ : Sp F ⟶ Xo.X} {k : F →+* C} {kO : V →+* O} {ψ : P.A.A.left ⟶ Xo.univ.t.G.left}
    (h : PointOver P x₀ k kO ψ) {G : SAB H (Sp V)} {t : SAB H (Sp F)} (n₁ : SABMap t Xo.univ.t x₀)
    (n₂ : SABMap t G (spMap (algebraMap V F))) :
    ∃ (π : P.G.left ⟶ G.G.left) (φ : P.A.A.left ⟶ t.G.left), IsGrpPullback P.G G.G (spMap kO) π ∧
      (∀ a, (P.oG.act a).left ≫ π = π ≫ (G.act.act a).left) ∧ φ ≫ t.G.hom = P.A.A.hom ≫ spMap k ∧
      φ ≫ n₂.φ = P.gen ≫ π ∧ φ ≫ n₁.φ = ψ := by
  obtain ⟨-, G', t', m₁, m₂, π, φ, h1, h2, h3, h4, rfl, -⟩ := h
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso m₁.cart n₁.cart
  obtain ⟨e, he, he'⟩ := LocModelLie.exists_iso_of_models HomExtExamples.homExtSt_holds V F G'.G G.G G'.semi G.semi t'.G
    m₂.cart (((isGrpPullback_of_iso a).comp n₂.cart).congr (Category.id_comp _) rfl)
  have c₁ : ∀ b, (t'.act.act b).left ≫ a.hom.left = a.hom.left ≫ (t.act.act b).left := fun b =>
    n₁.cart.1.hom_ext (by rw [Category.assoc, Category.assoc, n₁.act, ha', m₁.act, ← Category.assoc, ha'])
      (by rw [Category.assoc, Category.assoc, Over.w, Over.w, Over.w, Over.w])
  have c₂ : ∀ b, (G'.act.act b).left ≫ e.hom.left = e.hom.left ≫ (G.act.act b).left := fun b => by
    haveI := G.semi.separated
    haveI := G'.semi.smooth
    haveI : IsSchemeTheoreticallyDominant (spMap (algebraMap V F)) :=
      schDom_spec_map _ (IsFractionRing.injective V F)
    haveI : IsSchemeTheoreticallyDominant m₂.φ := .of_isPullback m₂.cart.1.flip
    refine ext_of_schDom G.G.hom (by rw [Category.assoc, Category.assoc, Over.w, Over.w, Over.w, Over.w]) m₂.φ ?_
    rw [← Category.assoc, ← m₂.act, Category.assoc, he', ← Category.assoc, c₁, ← Category.assoc m₂.φ, he',
      Category.assoc, Category.assoc, n₂.act]
  refine ⟨π ≫ e.hom.left, φ ≫ a.hom.left, (h1.comp (isGrpPullback_of_iso e)).congr (Category.comp_id _) rfl,
    fun b => ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, h2, Category.assoc, Category.assoc, c₂]
  · rw [Category.assoc, Over.w, h3.1.w]
  · rw [Category.assoc, ← he', ← Category.assoc, h4, Category.assoc]
  · rw [Category.assoc, ha']

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    (dualMap f).comp (dualMap g) = dualMap (f.comp g) := by
  ext s <;> simp [dualMap]

theorem dualMap_alg {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    spMap (dualMap f) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap f := by
  rw [spMap_spMap, spMap_spMap]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem ext_generic {y y' : specO O (DualNumber O) ⟶ P.G}
    (h : spMap (dualMap (algebraMap O C)) ≫ y.left = spMap (dualMap (algebraMap O C)) ≫ y'.left) : y = y' := by
  haveI : IsSchemeTheoreticallyDominant (spMap (dualMap (algebraMap O C))) :=
    (schemeDominant_specMap_iff _).2 fun a b hab => TrivSqZeroExt.ext
      (P.integers.hom_inj (by simpa [dualMap] using congrArg TrivSqZeroExt.fst hab))
      (P.integers.hom_inj (by simpa [dualMap, Algebra.algebraMap_eq_smul_one] using congrArg TrivSqZeroExt.snd hab))
  haveI := P.semi.separated
  exact Over.OverMorphism.ext (ext_of_schDom P.G.hom ((Over.w y).trans (Over.w y').symm) _ h)

theorem span_bLie_eq_wRec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [Algebra c.F C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left) (z : FrPt Xo c C), (letI := io.toAlgebra; PointOver P y₀.1.x k.toRingHom kO ψ) → (letI := io.toAlgebra; FrMap k y₀.1 z) → ∀ (τ : E →+* ℂ) (x : Fin (Dw.mult τ) → LieG P.Gt), (∀ j, LieTie P ψ (x j) (z.u τ j)) → Submodule.span O (Set.range fun j => P.bLie (x j)) = P.wRec (embInt c P.integers τ) := by
  intro E _ _ _ H Dw l Xo c p _ C _ _ _ v O _ _ _ _ _ _ _ _ _ T io y₀ k kO P ψ z hP hz τ x hx
  letI := io.toAlgebra
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨j, rfl⟩
    exact ⟨⟨x j, (hx j).isEig hP (z.eig τ j)⟩, rfl⟩
  rintro _ ⟨⟨w, hw⟩, rfl⟩
  obtain ⟨G, t, n₁, n₂, ⟨ub, u₁, u₂, u₃, u₄⟩, -⟩ := y₀.2.2
  obtain ⟨π, φ, h1, h2, h3, h4, h5⟩ := exists_map_to_model hP n₁ n₂
  letI := kO.toAlgebra
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  have inj : Function.Injective (algebraMap T.V O) := fun a b h => IsFractionRing.injective T.V T.Fr
    (k.toRingHom.injective ((hP.1 a).symm.trans ((congrArg _ h).trans (hP.1 b))))
  haveI : FaithfulSMul T.V O := (faithfulSMul_iff_algebraMap_injective _ _).2 inj
  haveI : Module.Flat T.V O := inferInstance
  haveI := G.semi.smooth
  haveI := G.act.hom
  choose χ hχ using fun a => int_val c T io τ a
  have hχ' : ∀ a, algebraMap T.V O (χ a) = embInt c P.integers τ a := fun a => P.integers.hom_inj (by
    rw [algebraMap_embInt, ← k.commutes]
    exact (hP.1 _).trans (congrArg k (hχ a)))
  obtain ⟨u', v₁, v₂⟩ := exists_eigenbasis G.G G.act.act χ (ub τ) (u₁ τ) (fun i a => u₂ τ i a _ (hχ a))
    (fun w hw he => u₃ τ w hw fun a z hz => by
      obtain rfl : z = χ a := IsFractionRing.injective T.V T.Fr (hz.trans (hχ a).symm)
      exact he a) h1 P.oG.act h2
  have hc : ∀ j, Corr P (x j).1 (u' j) := fun j => by
    obtain ⟨xG, s, s₁, s₂, s₃⟩ := hx j
    obtain ⟨r, r₁, r₂⟩ := u₄ τ j
    have r₃ : r ≫ t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) := IsLocalization.epi (nonZeroDivisors T.V) T.Fr
      have : Mono (spMap (algebraMap T.V T.Fr)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
      refine (cancel_mono (spMap (algebraMap T.V T.Fr))).1 ?_
      have k : (ub τ j).left ≫ G.G.hom = spMap (algebraMap T.V (DualNumber T.V)) := Over.w (ub τ j)
      rw [Category.assoc, ← n₂.cart.1.w, ← Category.assoc, r₂]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) k).trans (dualMap_alg _))
    have e₁ : s.left ≫ φ = spMap (dualMap k.toRingHom) ≫ r := n₁.cart.1.hom_ext
      (by rw [Category.assoc, Category.assoc, r₁, h5, s₂, hz.2.1])
      (by rw [Category.assoc, Category.assoc, r₃, h3, dualMap_alg, ← Category.assoc, Over.w s]; rfl)
    have e₂ : xG.1 = u' j := ext_generic (h1.1.hom_ext ?_ (by
      rw [Category.assoc, Category.assoc, Over.w, Over.w]))
    · exact e₂ ▸ s₁
    have e₃ : k.toRingHom.comp (algebraMap T.V T.Fr) = (algebraMap O C).comp (algebraMap T.V O) :=
      RingHom.ext fun a => (hP.1 a).symm
    rw [← s₃, Category.assoc, ← h4, ← Category.assoc, e₁, Category.assoc, r₂, Category.assoc, v₁, ← Category.assoc,
      ← Category.assoc, spMap_spMap, spMap_spMap, dualMap_comp, dualMap_comp, e₃]
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have mem_pow : ∀ {R : Type} [CommRing R] (a : R) (n : ℕ) (x : R),
      x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule R R) ↔ a ^ n ∣ x := by
    intro R _ a n x
    rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]
  have dual_dvd : ∀ (n : ℕ) (x : DualNumber O),
      (p : DualNumber O) ^ n ∣ x ↔ (p : O) ^ n ∣ x.fst ∧ (p : O) ^ n ∣ x.snd := by
    intro n x
    have e : (p : DualNumber O) ^ n = TrivSqZeroExt.inl ((p : O) ^ n) := by
      rw [← TrivSqZeroExt.inl_pow, TrivSqZeroExt.inl_natCast]
    rw [e]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.fst, by simp⟩, ⟨y.snd, by simp⟩⟩
    · rintro ⟨⟨a, ha⟩, b, hb⟩
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, by ext <;> simp [ha, hb]⟩
  have hadic : IsAdicComplete (Ideal.span {(p : DualNumber O)}) (DualNumber O) := by
    have h : IsAdicComplete (Ideal.span {(p : O)}) O := inferInstance
    refine { haus' := ?_, toIsPrecomplete := ?_ }
    · intro x hx
      simp only [SModEq.zero, mem_pow, dual_dvd] at hx
      refine TrivSqZeroExt.ext (h.toIsHausdorff.haus' x.fst fun n => ?_)
        (h.toIsHausdorff.haus' x.snd fun n => ?_)
      · rw [SModEq.zero, mem_pow]; exact (hx n).1
      · rw [SModEq.zero, mem_pow]; exact (hx n).2
    · constructor
      intro f hf
      simp only [SModEq.sub_mem, mem_pow, dual_dvd] at hf ⊢
      obtain ⟨a, ha⟩ := h.toIsPrecomplete.prec' (fun n => (f n).fst) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).1
      obtain ⟨b, hb⟩ := h.toIsPrecomplete.prec' (fun n => (f n).snd) fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_pow]; exact (hf hmn).2
      simp only [SModEq.sub_mem, mem_pow] at ha hb
      exact ⟨TrivSqZeroExt.inl a + TrivSqZeroExt.inr b, fun n => ⟨by simpa using ha n, by simpa using hb n⟩⟩
  have hl := existsUnique_left (P := P) hp hadic
  have hr := existsUnique_right (P := P) hp hadic
  obtain ⟨y, hy, -⟩ := hr w.1
  have y₁ := hy.comp (TrivSqZeroExt.fstHom O O O)
  rw [w.2] at y₁
  obtain ⟨a, ha⟩ := v₂ ⟨y, (existsUnique_right (P := P) hp₀ inferInstance 1).unique y₁ Corr.one⟩ fun a =>
    (hr _).unique (corr_act hy a) (by
      rw [hχ', show w.1 ≫ P.oGt.act a = _ from congrArg Subtype.val (hw a)]
      exact hy.comp _)
  let S : Submonoid (specO O (DualNumber O) ⟶ P.G) :=
    { carrier := {y | ∃ w : LieG P.Gt, Corr P w.1 y ∧ P.bLie w ∈ Submodule.span O (Set.range fun j => P.bLie (x j))}
      mul_mem' := by
        rintro _ _ ⟨a, a₁, a₂⟩ ⟨b, b₁, b₂⟩
        exact ⟨lieAdd a b, a₁.mul b₁, P.bLie_add a b ▸ Submodule.add_mem _ a₂ b₂⟩
      one_mem' := ⟨lieZero P.Gt, Corr.one, P.bLie_zero ▸ Submodule.zero_mem _⟩ }
  obtain ⟨w', w₁, w₂⟩ : y ∈ S := by
    rw [show y = _ from ha]
    refine S.list_prod_mem fun s hs => ?_
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hs
    exact ⟨AvDefs.lieScale P.Gt (a j) (x j), (hc j).comp _,
      P.bLie_scale (a j) (x j) ▸ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)⟩
  obtain rfl : w = w' := Subtype.ext ((hl y).unique hy w₁)
  exact w₂

end GlobalTheory.CompHt.RecSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExternalProductOnHermitianSumSmulLeft
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RouteSeesaw

variable {D : D7}

def adjM (S B : HSp D) (y : Mx D B.rank S.rank) : Mx D S.rank B.rank :=
  HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D) : Matrix (Fin S.rank) (Fin S.rank) (AE D))
    ((y.map (cA D))ᵀ : Matrix (Fin S.rank) (Fin B.rank) (AE D))) (B.gram.map (incA D) : Matrix (Fin B.rank) (Fin B.rank) (AE D))

theorem adjM_zero (S B : HSp D) : adjM S B 0 = 0 := by
  have e : ((0 : Mx D B.rank S.rank).map (cA D)) = 0 := by ext a b; simp
  simp only [adjM, e, transpose_zero, Matrix.mul_zero, Matrix.zero_mul]

theorem adjM_add (S B : HSp D) (y z : Mx D B.rank S.rank) : adjM S B (y + z) = adjM S B y + adjM S B z := by
  have e : (y + z).map (cA D) = y.map (cA D) + z.map (cA D) := by
    ext a b; simp
  simp only [adjM, e, transpose_add, Matrix.mul_add, Matrix.add_mul]

def topR {A B : HSp D} {n : ℕ} (x : Matrix (Fin (A.rank + B.rank)) (Fin n) (AE D)) : Mx D A.rank n :=
  x.submatrix (Fin.castAdd B.rank) id

def botR {A B : HSp D} {n : ℕ} (x : Matrix (Fin (A.rank + B.rank)) (Fin n) (AE D)) : Mx D B.rank n :=
  x.submatrix (Fin.natAdd A.rank) id

def box2 {S A B : HSp D} (φ : WO S A → ℂ) (φ' : WO S B → ℂ) : WO S (GlobalTheory.Doubling.hsum A B) → ℂ :=
  fun x => φ (topR (A := A) (B := B) x) * φ' (botR (A := A) (B := B) x)

theorem externalProductOnHermitianSum_add_left {S A B : HSp D} (φ₁ φ₂ : WO S A → ℂ) (φ' : WO S B → ℂ) :
    box2 (φ₁ + φ₂) φ' = box2 φ₁ φ' + box2 φ₂ φ' := by
  funext x; simp [box2, add_mul]

theorem externalProductOnHermitianSum_smul_left {S A B : HSp D} (c : ℂ) (φ : WO S A → ℂ) (φ' : WO S B → ℂ) :
    box2 (c • φ) φ' = c • box2 φ φ' := by
  funext x; simp [box2, mul_assoc]

end GlobalTheory.RouteSeesaw

end
end
