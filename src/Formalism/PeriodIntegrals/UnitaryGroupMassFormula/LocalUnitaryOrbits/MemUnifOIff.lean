module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfBas
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NearTIff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CrossMSmulRight

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUnifOIff
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.VolStabSW

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem le_ofAdd_neg_one_of_lt_one_local_unitary_orbits {a : WithZero (Multiplicative ℤ)} (h : a < 1) :
    a ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  by_cases ha : a = 0
  · simp [ha]
  · have h1 : a < ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      simpa using h
    rw [WithZero.lt_ofAdd_iff ha] at h1
    rw [WithZero.le_ofAdd_iff ha]
    omega

theorem mem_unifO_iff {ϖ : Fv F v} (hϖ : IsUnif v ϖ) (x : v.adicCompletionIntegers F) :
    x ∈ unifO v ϖ ↔ Valued.v (x : Fv F v) < 1 := by
  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := hϖ
  have hlt : Valued.v ϖ < 1 := by
    rw [hv]
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) < 1)
  have hne : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact WithZero.zero_ne_coe hv
  constructor
  · rintro ⟨d, hd⟩
    have hd1 : Valued.v (d : Fv F v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 d.2
    rw [hd, map_mul]
    calc Valued.v ϖ * Valued.v (d : Fv F v) ≤ Valued.v ϖ * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  · intro hx
    have hle : Valued.v (x : Fv F v) ≤ Valued.v ϖ := by
      rw [hv]; exact le_ofAdd_neg_one_of_lt_one_local_unitary_orbits hx
    have hmem : (x : Fv F v) / ϖ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
      exact div_le_one_of_le₀ hle zero_le'
    refine ⟨⟨_, hmem⟩, ?_⟩
    simp only
    field_simp

def redO : v.adicCompletionIntegers F →+ 𝓞 F ⧸ v.asIdeal where
  toFun x := red v (x : Fv F v)
  map_zero' := red_zero v
  map_add' x y := red_add v x.2 y.2

theorem resIdx_holds : ResIdx v := by
  intro ϖ hϖ
  have hker : unifO v ϖ = (redO v).ker := by
    ext x
    rw [mem_unifO_iff v hϖ x, AddMonoidHom.mem_ker]
    exact (red_eq_zero_iff v x.2).symm
  have hsurj : Function.Surjective (redO v) := by
    intro t
    obtain ⟨y, hy, hyt⟩ := red_surj v t
    exact ⟨⟨y, hy⟩, hyt⟩
  rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  simp

end PI.OmLocU
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OBas1OfUnitV
noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def OBas1 : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∃ e : Fin n → Fin n → Fv F v ⊗[F] E, Orb.IsOBas v Λ e ∧ gramR (Fv F v) σ J e = 1

def ResAlg : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Ideal.absNorm v.asIdeal ∧
      ((etaV (E := E) v = -1 ∧ ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K)
          (π : OR (E := E) v →+* K),
          (∀ x, σ' (σ' x) = x) ∧ Module.finrank k K = 2 ∧ σ' ≠ AlgEquiv.refl ∧
          IsRes σ v ϖ (σ' : K →+* K) π) ∨
       (etaV (E := E) v = 1 ∧ ∃ π : OR (E := E) v →+* k × k,
          IsRes σ v ϖ (RingEquiv.prodComm (R := k) (S := k)).toRingHom π))

theorem oBas1_of_unitV (hU : Orb.UnitV σ J ψ v Λ) : OBas1 σ J ψ v Λ := by
  intro hstd hL hsd hun
  obtain ⟨e, he, -, he1, hsp⟩ := Orb.orthoGen σ J ψ v Λ hU hstd hL hsd hun n (Fin 0)
    (fun i => i.elim0) (by simp) (fun i => i.elim0) ⟨1, (Orb.oSub v).1, by simp [Matrix.det_isEmpty]⟩
  refine ⟨e, fun x => ⟨fun hx => hsp x ⟨hx, fun i => i.elim0⟩, ?_⟩, he1⟩
  rintro ⟨c, hc, rfl⟩
  exact Submodule.sum_mem _ fun i _ => Orb.oSmul v Λ hL (c i) (hc i) (e i) (he i).1

theorem det_red {K : Type} [CommRing K] (π : OR (E := E) v →+* K) {a : ℕ}
    (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (hT : ∀ i j, T i j ∈ OR (E := E) v)
    {w : Fv F v ⊗[F] E} (hw : w ∈ OEv (E := E) v) (hd : T.det * w = 1) :
    IsUnit (Matrix.det (fun i j => π ⟨T i j, hT i j⟩)) := by
  set Ts : Matrix (Fin a) (Fin a) (OR (E := E) v) := fun i j => ⟨T i j, hT i j⟩
  have hdet : ((Ts.det : OR (E := E) v) : Fv F v ⊗[F] E) = T.det := by
    rw [show ((Ts.det : OR (E := E) v) : Fv F v ⊗[F] E) = (OR (E := E) v).subtype Ts.det from rfl,
      RingHom.map_det]
    rfl
  have hm : Ts.det * ⟨w, hw⟩ = 1 := by
    apply Subtype.ext
    rw [Subring.coe_mul, hdet]
    exact hd
  have hu : IsUnit Ts.det := ⟨⟨Ts.det, ⟨w, hw⟩, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  have := hu.map π
  rw [RingHom.map_det] at this
  exact this

theorem redU_of (hU : Orb.UnitV σ J ψ v Λ) (hR : ResAlg σ J ψ v) (a : ℕ) (Y : TupV (E := E) v n a) :
    RedU σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hstd := hG.1
  have hcm := hstd.1
  have hJ : ∀ i j, σ (J j i) = J i j := hstd.2.1.1
  obtain ⟨e, he, he1⟩ := oBas1_of_unitV σ J ψ v Λ hU hstd hG.2.1 hG.2.2.1 hG.2.2.2.1
  have hT := gY_mem σ J ψ v Λ hG
  obtain ⟨w, hw, -, hd⟩ := hG.2.2.2.2.2.2
  have hconj : ∀ i j, gramR (Fv F v) σ J Y i j = sigR (Fv F v) σ (gramR (Fv F v) σ J Y j i) := fun i j =>
    (Orb.hR_conj σ J v hcm hJ (Y j) (Y i)).symm
  obtain ⟨k, _, _, hk, h⟩ := hR hstd hG.2.2.2.1 ϖ hϖ
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  rcases h with ⟨hη, K, _, _, σ', π, hσ, h2, hne, hπ⟩ | ⟨hη, π, hπ⟩
  · refine Or.inl ⟨hη, K, inferInstance, inferInstance, σ', 1, fun i j => π ⟨_, hT i j⟩, hσ, h2, hne, ?_,
      by simp, ?_, det_red v π _ hT hw hd,
      card_cls σ J v Λ hcm hJ hG.2.2.1 he he1 (σ' : K →+* K) π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro i j
      exact (hπ.2.2 _ _ (hconj i j)).symm
  · refine Or.inr ⟨hη, 1, fun i j => π ⟨_, hT i j⟩, ?_, by simp, ?_, det_red v π _ hT hw hd,
      card_cls σ J v Λ hcm hJ hG.2.2.1 he he1 (RingEquiv.prodComm (R := k) (S := k)).toRingHom π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; ext <;> simp
      · ext <;> simp [h, Ne.symm h]
    · intro i j
      exact (hπ.2.2 _ _ (hconj i j)).symm

end PI.OmLocU.Red
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRSumSmulRight
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem oEv_mul {x y : Fv F v ⊗[F] E} (hx : x ∈ OEv (E := E) v) (hy : y ∈ OEv (E := E) v) :
    x * y ∈ OEv (E := E) v := by
  unfold OEv at *
  rw [SetLike.mem_coe] at *
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨e, -, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨f, -, rfl⟩ := hb
      rw [← map_mul]
      exact Submodule.subset_span ⟨e * f, Set.mem_univ _, by simp⟩
    | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
    | add b c _ _ hb hc =>
      rw [mul_add]
      exact Submodule.add_mem _ hb hc
    | smul r b _ hb =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ r hb
  | zero =>
    rw [zero_mul]
    exact Submodule.zero_mem _
  | add a c _ _ ha hc =>
    rw [add_mul]
    exact Submodule.add_mem _ ha hc
  | smul r a _ ha =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r ha

theorem oEv_sum {ι : Type} (s : Finset ι) (f : ι → Fv F v ⊗[F] E) (h : ∀ i ∈ s, f i ∈ OEv (E := E) v) :
    ∑ i ∈ s, f i ∈ OEv (E := E) v := by
  unfold OEv at *
  exact Submodule.sum_mem _ h

theorem hR_sum_smul_right {a : ℕ} (x : Fin n → Fv F v ⊗[F] E) (c : Fin a → Fv F v ⊗[F] E)
    (y : Fin a → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (∑ k, c k • y k) = ∑ k, c k * hR (Fv F v) σ J x (y k) := by
  have := map_sum (PI.VolStabSW.hLin (Fv F v) σ J x) (fun k => c k • y k) Finset.univ
  simp only [map_smul, smul_eq_mul] at this
  exact this

theorem hR_smul_left' (c : Fv F v ⊗[F] E) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = sigR (Fv F v) σ c * hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_sum_smul_left {a : ℕ} (y : Fin n → Fv F v ⊗[F] E) (c : Fin a → Fv F v ⊗[F] E)
    (x : Fin a → Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (∑ k, c k • x k) y = ∑ k, sigR (Fv F v) σ (c k) * hR (Fv F v) σ J (x k) y := by
  have := map_sum (AddMonoidHom.mk' (fun z => hR (Fv F v) σ J z y) (fun z z' => hR_add_left σ J z z' y))
    (fun k => c k • x k) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at this
  rw [this]
  exact Finset.sum_congr rfl fun k _ => hR_smul_left' σ J v (c k) (x k) y

section Onto

variable (Λ : Set (Fin n → E)) (ψ : AddChar (AF F) ℂ)

def GramInvO (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ → ∀ y ∈ LamT v Λ a,
    (∀ i j, gramR (Fv F v) σ J y i j - gramR (Fv F v) σ J Y i j ∈ PO (E := E) v ϖ) →
    ∃ Ginv : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E), (∀ i j, Ginv i j ∈ OEv (E := E) v) ∧
      gramR (Fv F v) σ J y * Ginv = 1

def TrOnto : Prop :=
  UnramAt (E := E) v → ∀ s ∈ OEv (E := E) v, sigR (Fv F v) σ s = s →
    ∃ x ∈ OEv (E := E) v, x + sigR (Fv F v) σ x = s

theorem hensOnto_of (a : ℕ) (Y : TupV (E := E) v n a) (hGI : GramInvO σ J v Λ ψ a Y) (hTr : TrOnto σ v) :
    HensOnto σ J v Λ ψ a Y := by
  classical
  intro hGood ϖ hϖ y hy hyT S hS
  obtain ⟨Ginv, hGi, hGG⟩ := hGI hGood ϖ hϖ y hy hyT
  obtain ⟨L, -, hLΛ⟩ := hGood.2.1
  have hσ : ∀ x, σ (σ x) = x := PI.VolStabSW.sigma_invol σ hGood.1.1.2.2.2
  have hJ : ∀ i j, σ (J j i) = J i j := hGood.1.2.1.1
  have hdiag : ∀ i, ∃ x ∈ OEv (E := E) v, x + sigR (Fv F v) σ x = (S : Matrix (Fin a) (Fin a) _) i i :=
    fun i => hTr hGood.2.2.2.1 _ (hS i i) (S.2 i i)
  choose x hx hxs using hdiag
  set A : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := fun i j =>
    if i < j then (S : Matrix (Fin a) (Fin a) _) i j else if i = j then x i else 0 with hAdef
  have hA : ∀ i j, A i j ∈ OEv (E := E) v := by
    intro i j
    simp only [hAdef]
    split_ifs
    · exact hS i j
    · exact hx i
    · exact oEv_zero v
  have hAS : ∀ i j, A i j + sigR (Fv F v) σ (A j i) = (S : Matrix (Fin a) (Fin a) _) i j := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [hAdef, h, not_lt.2 h.le, h.ne']
    · simp [hAdef, hxs]
    · simp only [hAdef, h, not_lt.2 h.le, h.ne, h.ne', if_false, if_true, zero_add]
      exact S.2 i j
  set C := Ginv * A with hCdef
  have hC : ∀ i j, C i j ∈ OEv (E := E) v := fun i j => by
    rw [hCdef, Matrix.mul_apply]
    exact oEv_sum v _ _ fun k _ => oEv_mul v (hGi i k) (hA k j)
  have hGm := PI.VolStabSW.gramR_mem (Fv F v) σ hσ J hJ y
  subst hLΛ
  refine ⟨fun j => ∑ k, C k j • y k, fun j => ?_, ?_⟩
  · exact Submodule.sum_mem _ fun k _ => oEv_smul_mem v L (hC k j) (hy k)
  · funext i j
    simp only [crossM]
    rw [hR_sum_smul_right, hR_sum_smul_left]
    have e1 : ∑ k, C k j * hR (Fv F v) σ J (y i) (y k) = A i j := by
      have : (gramR (Fv F v) σ J y * C) i j = A i j := by
        rw [hCdef, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
      rw [← this, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have e2 : ∑ k, sigR (Fv F v) σ (C k i) * hR (Fv F v) σ J (y k) (y j) = sigR (Fv F v) σ (A j i) := by
      have : (gramR (Fv F v) σ J y * C) j i = A j i := by
        rw [hCdef, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← this, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, mul_comm]
      congr 1
      exact (hGm k j).symm
    rw [e1, e2, hAS]

end Onto

end PI.OmLocU
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BasIntSmulMem
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct

section Bas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}

theorem basRatV_add (x y : Fin n → E) :
    ratV (F := F) (Fv F v) (x + y) = ratV (F := F) (Fv F v) x + ratV (F := F) (Fv F v) y := by
  funext i
  simp [ratV, map_add (f := _)]

theorem basRatV_zsmul (c : ℤ) (x : Fin n → E) :
    ratV (F := F) (Fv F v) (c • x) = c • ratV (F := F) (Fv F v) x := by
  funext i
  simp [ratV]

theorem basRatV_zero : ratV (F := F) (Fv F v) (0 : Fin n → E) = 0 := by
  funext i
  simp [ratV]

theorem basRatV_single (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e : Fin n → E) =
      (Pi.single i (inclR (F := F) (Fv F v) e) : Fin n → Fv F v ⊗[F] E) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [ratV]
  · simp [ratV, Pi.single_eq_of_ne h]

theorem basInt_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ y : ℤ, y ≠ 0 ∧ y • x ∈ L := by
  classical
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  obtain ⟨m, f, g, rfl⟩ := Submodule.mem_span_set'.1 hx
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ (y • f i) := hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  convert L.smul_mem (⟨y • f i, hi⟩ : 𝓞 E) (g i).2 using 1
  rw [← smul_assoc]
  rfl

theorem basLat_fg (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsLattice E L) :
    (latLoc (E := E) v (L : Set (Fin n → E))).FG := by
  classical
  obtain ⟨s, hs⟩ : (L.restrictScalars ℤ).FG := hLat.fg.restrictScalars
  refine ⟨s.image (ratV (F := F) (Fv F v)), ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hxL : x ∈ L := by
      have : x ∈ L.restrictScalars ℤ := by
        rw [← hs]
        exact Submodule.subset_span hx
      exact this
    exact Submodule.subset_span ⟨x, hxL, rfl⟩
  · unfold latLoc
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Submodule.span ℤ (s : Set (Fin n → E)) := by
      rw [hs]
      exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero =>
      rw [basRatV_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [basRatV_add]
      exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [basRatV_zsmul]
      exact zsmul_mem hy c

theorem basSpan_top (L : Submodule (𝓞 E) (Fin n → E)) (hLat : Submodule.IsFullLattice E L) :
    Submodule.span (Fv F v) (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) = ⊤ := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let bE := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (Fv F v) bE
  let P := Pi.basis (fun _ : Fin n => B)
  rw [eq_top_iff, ← P.span_eq, Submodule.span_le]
  rintro _ ⟨⟨i, k⟩, rfl⟩
  obtain ⟨N, hN, hNL⟩ := basInt_smul_mem L hLat.span_eq_top (Pi.single i (bE k) : Fin n → E)
  have hN' : (N : Fv F v) ≠ 0 := by
    rw [← map_intCast (algebraMap F (Fv F v))]
    exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hN)
  have hmem : ratV (F := F) (Fv F v) (N • (Pi.single i (bE k) : Fin n → E)) ∈
      latLoc (E := E) v (L : Set (Fin n → E)) := Submodule.subset_span ⟨_, hNL, rfl⟩
  have e : P ⟨i, k⟩ = (N : Fv F v)⁻¹ • ratV (F := F) (Fv F v) (N • (Pi.single i (bE k) : Fin n → E)) := by
    rw [basRatV_zsmul, basRatV_single, ← Int.cast_smul_eq_zsmul (Fv F v), smul_smul, inv_mul_cancel₀ hN', one_smul]
    simp only [P, B, Pi.basis_apply, Algebra.TensorProduct.basis_apply]
    rfl
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end Bas

end PI.OmLocU
end
end
