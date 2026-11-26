module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantGroupCounts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinearIndependentOrth
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscriminantNormShapesTer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibreCountingDataFurther

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FibreCountingData
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

def liftQ {K F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} {𝔭 : Ideal (𝓞 F)} {k : ℕ}
    (M : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) : Matrix (Fin m) (Fin m) (𝓞 K) :=
  Matrix.of fun i j => (Ideal.Quotient.mk_surjective (M i j)).choose

theorem liftQ_map {K F : Type} [Field K] [Field F] [Algebra F K] {m : ℕ} {𝔭 : Ideal (𝓞 F)} {k : ℕ}
    (M : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :
    (liftQ M).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) = M := by
  ext i j
  simp only [Matrix.map_apply, liftQ, Matrix.of_apply]
  exact (Ideal.Quotient.mk_surjective (M i j)).choose_spec

end Formalism.L2.SG.Pf.fibreCountingData

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G5 Formalism.L2.SG.Pf.discriminantNormShapes Formalism.L2.SG.Pf.fibreCountingData

theorem unitary_discriminant_model : UDModel := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ _ hK h hs hd L hL hLi 𝔭 h𝔭 b a hb k hk
  have hli := linearIndependent_of_jordan hb
  have hcard : Fintype.card (Fin (finrank K (⊤ : Submodule K V))) = finrank K V := by
    simp [finrank_top]
  have hbspan := hli.span_eq_top_of_card_eq_finrank' hcard
  obtain ⟨-, hloc, horth, hdiag, hne⟩ := hb
  have hfull : Submodule.span K (L : Set V) = ⊤ := by
    apply top_unique
    rw [← hbspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hmem : b i ∈ locF 𝔭 L := by
      rw [← hloc]
      exact Formalism.HermitianLattices.Ext.L3.localizedQuotients.le_locF 𝔭 _
        (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨s, hs, hsx⟩ := hmem
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      clear hsx
      induction hs using Submonoid.closure_induction with
      | mem y hy =>
        obtain ⟨t, ht, rfl⟩ := hy
        rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K,
          IsScalarTower.algebraMap_apply (𝓞 F) F K]
        exact (map_ne_zero (algebraMap F K)).2
          ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 (fun ht0 => ht (ht0 ▸ 𝔭.zero_mem)))
      | one => simp
      | mul x y _ _ hx hy => simp only [map_mul]; exact mul_ne_zero hx hy
    have hsx' : algebraMap (𝓞 K) K s • b i ∈ Submodule.span K (L : Set V) := by
      rw [algebraMap_smul]; exact Submodule.subset_span hsx
    exact (Submodule.smul_mem_iff _ hs0).1 hsx'
  have hFx : IsFixF K F := Fact.out
  let s := udSetoid K 𝔭 k a
  let J : JD h L 𝔭 b a := ⟨horth, hdiag, hne, hloc, hFx, h𝔭, ⟨hL.fg, hfull⟩⟩
  have := h𝔭.isPrime
  have hv : ∀ i, vF 𝔭 (a i) ≤ vJof 𝔭 a := fun i =>
    Finset.single_le_sum (f := fun i => vF 𝔭 (a i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hk1 : ∀ i, vF 𝔭 (a i) ≤ k := fun i => by have := hv i; omega
  have hk2 : ∀ i j, vF 𝔭 (a i) + vF 𝔭 (a j) ≤ k := fun i j => by
    have := hv i; have := hv j; omega
  have hA : ∀ Y : udPre K 𝔭 k a, ∀ i j,
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i) * liftQ Y.1 i j) / algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j)) ∈ HU.SP K 𝔭 := fun Y =>
    (condP_iff_eqP hne hk1 (liftQ Y.1)).1 (by rw [liftQ_map]; exact Y.2.1)
  have hW : ∀ Y : udPre K 𝔭 k a, ∀ i j,
      algebraMap (𝓞 K) K (gramO a (liftQ Y.1) i j) / (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a i)) * algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (a j))) ∈ HU.SP K 𝔭 := fun Y =>
    (condW_iff hne hk2 (liftQ Y.1)).1 (by rw [liftQ_map]; exact Y.2.2)
  let f0 : udPre K 𝔭 k a → {P : Module.End (𝓞 K) (DiscMod h ⊤ L 𝔭) //
      ∀ x y x' y' : ↥(locF 𝔭 (dualIn h ⊤ L)),
        Submodule.Quotient.mk x' = P (Submodule.Quotient.mk x) →
        Submodule.Quotient.mk y' = P (Submodule.Quotient.mk y) →
        h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)} :=
    fun Y => ⟨J.E (liftQ Y.1) (hA Y), J.E_isom (liftQ Y.1) (hA Y) (hW Y)⟩
  have hresp : ∀ Y Y' : udPre K 𝔭 k a, s.r Y Y' → f0 Y = f0 Y' := by
    rintro Y Y' ⟨Z, hZ⟩
    have hd := (condZ_iff hne hk1 (liftQ Y.1) (liftQ Y'.1)).mp
      ⟨Z, by simpa only [liftQ_map] using hZ⟩
    exact Subtype.ext (J.E_eq_of (liftQ Y.1) (liftQ Y'.1) (hA Y) (hA Y') hd)
  let f : udQ K 𝔭 k a → _ := Quotient.lift (s := s) f0 hresp
  have hinj : Function.Injective f := by
    intro q q'
    induction q using Quotient.inductionOn with | h Y => ?_
    induction q' using Quotient.inductionOn with | h Y' => ?_
    intro he
    have he' : J.E (liftQ Y.1) (hA Y) = J.E (liftQ Y'.1) (hA Y') := congrArg Subtype.val he
    apply Quotient.sound
    obtain ⟨Z, hZ⟩ := (condZ_iff hne hk1 (liftQ Y.1) (liftQ Y'.1)).2
      (J.entry_of_E_eq (liftQ Y.1) (liftQ Y'.1) (hA Y) (hA Y') he')
    rw [liftQ_map, liftQ_map] at hZ
    exact ⟨Z, hZ⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨P, hP⟩
    have hLift := J.exists_E_eq P hP
    rcases hLift with ⟨Y, hY, hWY, hE⟩
    let Yq : udPre K 𝔭 k a :=
      ⟨Y.map (Ideal.Quotient.mk _), (condP_iff_eqP hne hk1 Y).2 hY, (condW_iff hne hk2 Y).2 hWY⟩
    refine ⟨Quotient.mk _ Yq, Subtype.ext ?_⟩
    refine (J.E_eq_of (liftQ Yq.1) Y (hA Yq) hY fun i j => ?_).trans hE
    have e := congrFun (congrFun (liftQ_map (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))) i) j
    rw [map_apply, map_apply, Ideal.Quotient.eq] at e
    exact div_mem_SP_of_mem h𝔭 (hne j) (hk1 j) e
  rw [discAut]
  exact (Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩).symm

end Formalism.L2.SG.Pf.Cnt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiagonalFormCounting
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PhiCountingHolds
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CardPhiSucc
open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.LocalizedFibreSets

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}

theorem starO_ι (a : 𝓞 F) : star (algebraMap (𝓞 F) (𝓞 K) a) = algebraMap (𝓞 F) (𝓞 K) a := by
  apply RingOfIntegers.ext
  change star ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K) = ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K)
  have h1 : ((algebraMap (𝓞 F) (𝓞 K) a : 𝓞 K) : K) = algebraMap F K (a : F) := by
    first
    | rfl
    | exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K a).symm.trans
        (IsScalarTower.algebraMap_apply (𝓞 F) F K a)
  rw [h1]
  exact ((Fact.out : IsFixF K F) _).2 ⟨_, rfl⟩

theorem diagQ_herm (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (diagQ K 𝔭 k a)ᴴ = diagQ K 𝔭 k a := by
  unfold diagQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  rw [Pi.star_apply, star_mk, starO_ι]

theorem phiQ_herm (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) : (phiQ K 𝔭 k a Y)ᴴ = phiQ K 𝔭 k a Y := by
  unfold phiQ
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, diagQ_herm]
  simp only [Matrix.mul_assoc]
  abel

theorem map_diagQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F) :
    (diagQ K 𝔭 (k + 1) a).map (piQ K 𝔭 k) = diagQ K 𝔭 k a := by
  unfold diagQ
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1

theorem map_phiQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : Fin m → 𝓞 F)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))) :
    (phiQ K 𝔭 (k + 1) a Y).map (piQ K 𝔭 k) = phiQ K 𝔭 k a (Y.map (piQ K 𝔭 k)) := by
  have hs : Function.Semiconj (piQ K 𝔭 k) star star := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    unfold piQ
    rw [star_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, star_mk]
  have hd := map_diagQ (K := K) 𝔭 k a
  unfold phiQ
  rw [Matrix.map_add (piQ K 𝔭 k) (map_add (piQ K 𝔭 k)), Matrix.map_add (piQ K 𝔭 k) (map_add (piQ K 𝔭 k)),
    Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map _ hs, hd]

theorem card_phi_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (a : Fin m → 𝓞 F) {k : ℕ} (hk : 1 ≤ k) (T : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)))
    (hT : Tᴴ = T) (hT0 : ∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))) :
    Nat.card {Y // phiQ K 𝔭 (k + 1) a Y = T} =
      Ideal.absNorm 𝔭 ^ (m * m) * Nat.card {Y // phiQ K 𝔭 k a Y = T.map (piQ K 𝔭 k)} := by
  classical
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  haveI := finite_quot (K := K) h𝔭 k
  haveI : Finite (Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))) := inferInstanceAs (Finite (Fin m → Fin m → (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))))
  haveI : Finite (Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k)) :=
    inferInstanceAs (Finite (Fin m → Fin m → (𝓞 K ⧸ extP K 𝔭 ^ k)))

  have hJJ : ∀ x ∈ (RingHom.ker (piQ K 𝔭 k)), ∀ y ∈ (RingHom.ker (piQ K 𝔭 k)), x * y = 0 := by
    intro x hx y hy
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [mk_mem_ker_piQ] at hx hy
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have huv : u * v ∈ extP K 𝔭 ^ (k + k) := by rw [pow_add]; exact Ideal.mul_mem_mul hx hy
    exact Ideal.pow_le_pow_right (by omega) huv
  have hPJ : ∀ x ∈ ((extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))), ∀ y ∈ (RingHom.ker (piQ K 𝔭 k)), x * y = 0 := by
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hx
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [mk_mem_ker_piQ] at hy
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_succ']
    exact Ideal.mul_mem_mul hu hy
  have hJP : ∀ x ∈ (RingHom.ker (piQ K 𝔭 k)), x ∈ ((extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))) := by
    intro x hx
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [mk_mem_ker_piQ] at hx
    exact Ideal.mem_map_of_mem _ (Ideal.pow_le_self (by omega) hx)
  have hJs : ∀ x ∈ (RingHom.ker (piQ K 𝔭 k)), star x ∈ (RingHom.ker (piQ K 𝔭 k)) := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    rw [piQ_star, hx, star_zero]
  obtain ⟨θ, e, he⟩ := exists_unit_quot hK h𝔭 (k + 1)
  have hmem : ∀ (C E : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))), E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)) → C * E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)) := by
    intro C E hE i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ (fun l _ => Ideal.mul_mem_left _ _ (hE l j))

  have hfib : ∀ (A B : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1))), (∀ G ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), A * (B * G) = G) →
      ∀ S ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k)), Nat.card {E : Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)) // A * E.1 + (A * E.1)ᴴ = S} =
        Ideal.absNorm 𝔭 ^ (m * m) := by
    intro A B hAB S hS
    let L : Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)) →+ Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) :=
      (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.trH (Fin m) (RingHom.ker (piQ K 𝔭 k))).comp
        (AddMonoidHom.mk' (fun E => ⟨A * E.1, hmem A E.1 E.2⟩)
          (fun E F => Subtype.ext (by simp [Matrix.mul_add])))
    have hL : ∀ E, L E = A * E.1 + (A * E.1)ᴴ := fun E => rfl
    have hrange : L.range = Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k)) := by
      apply le_antisymm
      · rintro _ ⟨E, rfl⟩
        rw [← Formalism.HermitianLattices.Ext.L3.HermitianSublattices.range_trH hJs he]
        exact ⟨⟨A * E.1, hmem _ _ E.2⟩, rfl⟩
      · intro S' hS'
        rw [← Formalism.HermitianLattices.Ext.L3.HermitianSublattices.range_trH hJs he] at hS'
        obtain ⟨G, rfl⟩ := hS'
        refine ⟨⟨B * G.1, hmem _ _ G.2⟩, ?_⟩
        rw [hL]
        show A * (B * G.1) + (A * (B * G.1))ᴴ = G.1 + G.1ᴴ
        rw [hAB G.1 G.2]
    have hcardE : Nat.card (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k))) = Nat.card L.ker * Nat.card (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k))) := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup L.ker,
        Nat.card_congr (QuotientAddGroup.quotientKerEquivRange L).toEquiv, hrange, mul_comm]
    have hsq := Formalism.HermitianLattices.Ext.L3.HermitianSublattices.card_hermSub_sq (r := Fin m) hJs he
    have hh := Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.card_hermSub (r := Fin m) hK h𝔭 k
    rw [Fintype.card_fin] at hh
    have hpos : 0 < Nat.card (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k))) := Nat.card_pos
    have hker : Nat.card L.ker = Nat.card (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k))) := by
      rw [← hsq, pow_two] at hcardE
      exact (Nat.eq_of_mul_eq_mul_right hpos hcardE).symm
    have hSr : S ∈ L.range := by rw [hrange]; exact hS
    obtain ⟨E0, hE0⟩ := hSr
    rw [← hh, ← hker]
    exact Nat.card_congr
      { toFun := fun E => ⟨E.1 - E0, by
          rw [AddMonoidHom.mem_ker, map_sub, hE0, hL, E.2, sub_self]⟩
        invFun := fun K0 => ⟨K0.1 + E0, by
          rw [← hL, map_add (f := _), AddMonoidHom.mem_ker.mp K0.2, hE0, zero_add]⟩
        left_inv := fun E => Subtype.ext (sub_add_cancel _ _)
        right_inv := fun K0 => Subtype.ext (add_sub_cancel_right _ _) }

  let f : {Y // phiQ K 𝔭 (k + 1) a Y = T} → {Y // phiQ K 𝔭 k a Y = T.map (piQ K 𝔭 k)} :=
    fun Y => ⟨Y.1.map (piQ K 𝔭 k), by rw [← map_phiQ, Y.2]⟩
  have hfiber : ∀ y, Nat.card {x // f x = y} = Ideal.absNorm 𝔭 ^ (m * m) := by
    rintro ⟨Y', hY'⟩
    obtain ⟨Y0, hY0⟩ : ∃ Y0 : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)), Y0.map (piQ K 𝔭 k) = Y' :=
      ⟨fun i j => (piQ_surjective (K := K) 𝔭 k (Y' i j)).choose,
        by ext i j; exact (piQ_surjective (K := K) 𝔭 k (Y' i j)).choose_spec⟩
    obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)), A = 1 + Y0ᴴ * diagQ K 𝔭 (k + 1) a := ⟨_, rfl⟩
    obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)), B = 1 + Y0 * diagQ K 𝔭 (k + 1) a := ⟨_, rfl⟩
    have hS : T - phiQ K 𝔭 (k + 1) a Y0 ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.hermSub (Fin m) (RingHom.ker (piQ K 𝔭 k)) := by
      refine ⟨?_, ?_⟩
      · rw [Matrix.conjTranspose_sub, hT, phiQ_herm]
      · intro i j
        rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
        have h1 := congrFun (congrFun (map_phiQ 𝔭 k a Y0) i) j
        rw [Matrix.map_apply] at h1
        rw [h1, hY0, hY', Matrix.map_apply, sub_self]
    have hPhi0 : ∀ i j, phiQ K 𝔭 (k + 1) a Y0 i j ∈ ((extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)))) := by
      intro i j
      have e1 : phiQ K 𝔭 (k + 1) a Y0 i j = T i j - (T - phiQ K 𝔭 (k + 1) a Y0) i j := by
        rw [Matrix.sub_apply]; ring
      rw [e1]
      exact Ideal.sub_mem _ (hT0 i j) (hJP _ (hS.2 i j))
    have hAB : A * B = 1 + phiQ K 𝔭 (k + 1) a Y0 * diagQ K 𝔭 (k + 1) a := by
      rw [hA, hB]; unfold phiQ; noncomm_ring
    have hABG : ∀ G ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), A * (B * G) = G := by
      intro G hG
      have h0 : phiQ K 𝔭 (k + 1) a Y0 * diagQ K 𝔭 (k + 1) a * G = 0 := by
        ext i j
        rw [Matrix.mul_apply, Matrix.zero_apply]
        refine Finset.sum_eq_zero (fun l _ => hPJ _ ?_ _ (hG l j))
        rw [Matrix.mul_apply]
        exact Ideal.sum_mem _ (fun l' _ => Ideal.mul_mem_right _ _ (hPhi0 i l'))
      rw [← Matrix.mul_assoc, hAB, Matrix.add_mul, Matrix.one_mul, h0, add_zero]
    have hEE : ∀ E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), Eᴴ * diagQ K 𝔭 (k + 1) a * E = 0 := by
      intro E hE
      ext i j
      rw [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun l _ => hJJ _ ?_ _ (hE l j))
      rw [Matrix.mul_apply]
      refine Ideal.sum_mem _ (fun l' _ => Ideal.mul_mem_right _ _ ?_)
      rw [Matrix.conjTranspose_apply]
      exact hJs _ (hE l' i)
    have hDh : (diagQ K 𝔭 (k + 1) a)ᴴ = diagQ K 𝔭 (k + 1) a := diagQ_herm 𝔭 (k + 1) a
    have hexp : ∀ E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), phiQ K 𝔭 (k + 1) a (Y0 + E) =
        phiQ K 𝔭 (k + 1) a Y0 + (A * E + (A * E)ᴴ) := by
      intro E hE
      have h1 : (A * E)ᴴ = Eᴴ * (1 + diagQ K 𝔭 (k + 1) a * Y0) := by
        rw [Matrix.conjTranspose_mul, hA, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
          Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hDh]
      rw [h1, hA]
      unfold phiQ
      rw [Matrix.conjTranspose_add]
      calc _ = Y0 + Y0ᴴ + Y0ᴴ * diagQ K 𝔭 (k + 1) a * Y0 +
            ((1 + Y0ᴴ * diagQ K 𝔭 (k + 1) a) * E + Eᴴ * (1 + diagQ K 𝔭 (k + 1) a * Y0)) + Eᴴ * diagQ K 𝔭 (k + 1) a * E := by noncomm_ring
        _ = _ := by rw [hEE E hE, add_zero]
    have hker0 : ∀ E ∈ Formalism.HermitianLattices.Ext.L3.HermitianSublattices.entSub (Fin m) (Fin m) (RingHom.ker (piQ K 𝔭 k)), E.map (piQ K 𝔭 k) = 0 := by
      intro E hE
      ext i j
      exact hE i j
    rw [← hfib A B hABG _ hS]
    exact Nat.card_congr
      { toFun := fun x => ⟨⟨x.1.1 - Y0, by
            intro i j
            have hx := congrArg Subtype.val x.2
            have hx' := congrFun (congrFun hx i) j
            rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
            have hy := congrFun (congrFun hY0 i) j
            simp only [f, Matrix.map_apply] at hx' hy
            rw [hx', hy, sub_self]⟩, by
            have h2 := hexp (x.1.1 - Y0) (by
              intro i j
              have hx := congrArg Subtype.val x.2
              have hx' := congrFun (congrFun hx i) j
              rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
              have hy := congrFun (congrFun hY0 i) j
              simp only [f, Matrix.map_apply] at hx' hy
              rw [hx', hy, sub_self])
            rw [add_sub_cancel, x.1.2] at h2
            show A * (x.1.1 - Y0) + (A * (x.1.1 - Y0))ᴴ = T - phiQ K 𝔭 (k + 1) a Y0
            exact eq_sub_of_add_eq' h2.symm⟩
        invFun := fun E => ⟨⟨Y0 + E.1.1, by rw [hexp E.1.1 E.1.2, E.2, add_sub_cancel]⟩,
          Subtype.ext (by
            show (Y0 + E.1.1).map (piQ K 𝔭 k) = Y'
            rw [Matrix.map_add _ (map_add _), hY0, hker0 E.1.1 E.1.2, add_zero])⟩
        left_inv := fun x => Subtype.ext (Subtype.ext (add_sub_cancel _ _))
        right_inv := fun E => Subtype.ext (Subtype.ext (add_sub_cancel_left _ _)) }
  haveI : Fintype {Y // phiQ K 𝔭 k a Y = T.map (piQ K 𝔭 k)} := Fintype.ofFinite _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma,
    Finset.sum_congr rfl (fun y _ => hfiber y), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, smul_eq_mul, mul_comm]

def PhiModP : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [Fact (IsFixF K F)], Formalism.HermitianLatticesTheory.IsCMUnram K →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ (m : ℕ) (a : Fin m → 𝓞 F), (∀ i, a i ≠ 0) →
      (Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ 1) // phiQ K 𝔭 1 a Y = 0} : ℝ) =
        (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2) * alphaStd K 𝔭 (m - cJof 𝔭 a)

theorem phiCount_of (h1 : PhiModP) : PhiCount := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro T _ hT0
    have hb : (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ 1)) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker, pow_one]
    have hT' : T = 0 := by
      ext i j
      have := hT0 i j
      rw [hb, Ideal.mem_bot] at this
      exact this
    subst hT'
    rw [mul_one]
    exact h1 K F hK 𝔭 h𝔭 m a ha
  | succ k hk ih =>
    intro T hT hT0
    have hs : Function.Semiconj (piQ K 𝔭 k) star star := by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      unfold piQ
      rw [star_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, star_mk]
    rw [card_phi_succ hK h𝔭 a hk T hT hT0]
    push_cast
    rw [ih (T.map (piQ K 𝔭 k)) ?_ ?_]
    · ring
    · rw [← Matrix.conjTranspose_map _ hs, hT]
    · intro i j
      obtain ⟨x, hx, hxT⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp (hT0 i j)
      rw [Matrix.map_apply, ← hxT]
      unfold piQ
      rw [Ideal.Quotient.factor_mk]
      exact Ideal.mem_map_of_mem _ hx

end Formalism.L2.SG.Pf.LocalizedFibreSets
end
end

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.LocalizedFibreSets

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)]

theorem vF_ne_zero_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {x : 𝓞 F} (hx : x ≠ 0) :
    vF 𝔭 x ≠ 0 ↔ x ∈ 𝔭 := by
  constructor
  · intro h
    by_contra hx'
    apply h
    apply Nat.eq_zero_of_le_zero
    show sSup {e : ℕ | x ∈ 𝔭 ^ e} ≤ 0
    apply csSup_le'
    intro e he
    by_contra hne
    exact hx' (Ideal.pow_le_self (by omega) he)
  · intro hx'
    have hbdd : BddAbove {e : ℕ | x ∈ 𝔭 ^ e} := by
      have h0 : x ∉ ⨅ n : ℕ, 𝔭 ^ n := by
        rw [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭.ne_top]
        simpa using hx
      simp only [Submodule.mem_iInf, not_forall] at h0
      obtain ⟨n, hn⟩ := h0
      refine ⟨n, fun e he => ?_⟩
      by_contra hlt
      push_neg at hlt
      exact hn (Ideal.pow_le_pow_right hlt.le he)
    have h1 : 1 ≤ sSup {e : ℕ | x ∈ 𝔭 ^ e} :=
      le_csSup hbdd (show x ∈ 𝔭 ^ 1 by rwa [pow_one])
    show sSup {e : ℕ | x ∈ 𝔭 ^ e} ≠ 0
    omega

theorem card_U_diag (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : ι → 𝓞 F) (hb : ∀ i, b i ∉ 𝔭) :
    (Nat.card {γ : Matrix ι ι (𝓞 K ⧸ extP K 𝔭 ^ 1) //
      γᴴ * diagonal (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (b i))) * γ =
        diagonal (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (b i)))} : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ (Fintype.card ι ^ 2) * alphaStd K 𝔭 (Fintype.card ι) := by
  classical
  set n := Fintype.card ι with hn
  let e : ι ≃ Fin n := Fintype.equivFin ι
  set d : ι → 𝓞 K ⧸ extP K 𝔭 ^ 1 := fun i =>
    Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (b i)) with hd
  let u : Fin n → 𝓞 K := fun i => algebraMap (𝓞 F) (𝓞 K) (b (e.symm i))
  have hD : (diagonal u).map (Ideal.Quotient.mk (extP K 𝔭 ^ 1)) =
      Matrix.reindex e e (diagonal d) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [u, d, Matrix.reindex_apply]
    · have hij' : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
      simp [u, d, Matrix.reindex_apply, Matrix.diagonal_apply_ne _ hij,
        Matrix.diagonal_apply_ne _ hij']
  have hcard : Nat.card {γ : Matrix ι ι (𝓞 K ⧸ extP K 𝔭 ^ 1) // γᴴ * diagonal d * γ = diagonal d} =
      Nat.card {X : Matrix (Fin n) (Fin n) (𝓞 K ⧸ extP K 𝔭 ^ 1) //
        Xᴴ * Matrix.reindex e e (diagonal d) * X = Matrix.reindex e e (diagonal d)} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Matrix.reindex e e) fun γ => ?_)
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    refine ⟨fun h => by rw [h], fun h => (Matrix.reindex e e).injective ?_⟩
    simpa only [Matrix.reindex_apply] using h
  have hu : ∀ i, Formalism.HermitianLattices.Ext.L3.conjO K (u i) = u i := fun i => by
    apply IsFractionRing.injective (𝓞 K) K
    rw [Formalism.HermitianLattices.Ext.L3.BallB.algebraMap_conjO, (Fact.out : IsFixF K F)]
    refine ⟨((b (e.symm i) : 𝓞 F) : F), ?_⟩
    show algebraMap F K (algebraMap (𝓞 F) F (b (e.symm i))) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K]
  have hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤ := fun i => by
    have hF : Ideal.span {b (e.symm i)} ⊔ 𝔭 = ⊤ := by
      refine h𝔭.1.2 _ (lt_of_le_of_ne le_sup_right fun h => hb (e.symm i) ?_)
      rw [h]
      exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    have h2 := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hF
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_top] at h2
    exact h2
  rw [hcard, ← hD]
  exact Formalism.HermitianLattices.Ext.L3.IsotropicCounts.isoCount_one hK h𝔭 u hu hunit

private theorem fromBlocks_cayley_eq_zero_iff {A : Type*} [CommRing A] [StarRing A] {u z : Type*} [Fintype u] [Fintype z]
    [DecidableEq u] [DecidableEq z] (Du : Matrix u u A) (hDu : Duᴴ = Du) (P : Matrix u u A)
    (Q : Matrix u z A) (R : Matrix z u A) (S : Matrix z z A) :
    Matrix.fromBlocks P Q R S + (Matrix.fromBlocks P Q R S)ᴴ +
        (Matrix.fromBlocks P Q R S)ᴴ * Matrix.fromBlocks Du 0 0 0 * Matrix.fromBlocks P Q R S = 0 ↔
      P + Pᴴ + Pᴴ * Du * P = 0 ∧ R = -(Q + Pᴴ * Du * Q)ᴴ ∧ S + Sᴴ + Qᴴ * Du * Q = 0 := by
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_add, Matrix.fromBlocks_add, ← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  constructor
  · rintro ⟨h1, h2, -, h4⟩
    refine ⟨h1, ?_, h4⟩
    have hR : Rᴴ = -(Q + Pᴴ * Du * Q) := by
      rw [eq_neg_iff_add_eq_zero, ← h2]; abel
    rw [← Matrix.conjTranspose_conjTranspose R, hR, Matrix.conjTranspose_neg]
  · rintro ⟨h1, rfl, h4⟩
    refine ⟨h1, ?_, ?_, h4⟩
    · rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose]; abel
    · rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDu,
        Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc]
      abel

private theorem card_fromBlocks_cayley_eq_mul {A : Type*} [CommRing A] [StarRing A] [Finite A] {u z : Type*} [Fintype u]
    [Fintype z] [DecidableEq u] [DecidableEq z] (Du : Matrix u u A) (hDu : Duᴴ = Du) {θ e : A}
    (he : (θ - star θ) * e = 1) :
    Nat.card {Y : Matrix (u ⊕ z) (u ⊕ z) A // Y + Yᴴ + Yᴴ * Matrix.fromBlocks Du 0 0 0 * Y = 0} =
      Nat.card {P : Matrix u u A // P + Pᴴ + Pᴴ * Du * P = 0} * Nat.card (Matrix u z A) *
        Nat.card {S : Matrix z z A // S + Sᴴ = 0} := by
  have hse : star e = -e := Formalism.HermitianLattices.Ext.L3.HermitianSublattices.star_inv_eq_neg he
  have hte : θ * e + star θ * -e = 1 := by rw [← he]; ring

  have hS0 : ∀ Q : Matrix u z A, (θ * e) • (-(Qᴴ * Du * Q)) + ((θ * e) • (-(Qᴴ * Du * Q)))ᴴ =
      -(Qᴴ * Du * Q) := by
    intro Q
    have hM : (-(Qᴴ * Du * Q))ᴴ = -(Qᴴ * Du * Q) := by
      rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hDu, Matrix.mul_assoc]
    rw [Matrix.conjTranspose_smul, hM, star_mul', hse, ← add_smul, hte, one_smul]
  have key : ∀ (Q : Matrix u z A) (S : Matrix z z A),
      (S - (θ * e) • (-(Qᴴ * Du * Q))) + (S - (θ * e) • (-(Qᴴ * Du * Q)))ᴴ =
        S + Sᴴ + Qᴴ * Du * Q := by
    intro Q S
    rw [Matrix.conjTranspose_sub]
    rw [show S - (θ * e) • (-(Qᴴ * Du * Q)) + (Sᴴ - ((θ * e) • (-(Qᴴ * Du * Q)))ᴴ) =
      S + Sᴴ - ((θ * e) • (-(Qᴴ * Du * Q)) + ((θ * e) • (-(Qᴴ * Du * Q)))ᴴ) by abel, hS0 Q,
      sub_neg_eq_add]
  let eqv : {Y : Matrix (u ⊕ z) (u ⊕ z) A // Y + Yᴴ + Yᴴ * Matrix.fromBlocks Du 0 0 0 * Y = 0} ≃
      ({P : Matrix u u A // P + Pᴴ + Pᴴ * Du * P = 0} × Matrix u z A) ×
        {S : Matrix z z A // S + Sᴴ = 0} :=
    { toFun := fun Y =>
        have h := (fromBlocks_cayley_eq_zero_iff Du hDu _ _ _ _).mp (by rw [Matrix.fromBlocks_toBlocks]; exact Y.2)
        ((⟨Y.1.toBlocks₁₁, h.1⟩, Y.1.toBlocks₁₂),
          ⟨Y.1.toBlocks₂₂ - (θ * e) • (-(Y.1.toBlocks₁₂ᴴ * Du * Y.1.toBlocks₁₂)),
            by rw [key]; exact h.2.2⟩)
      invFun := fun x =>
        ⟨Matrix.fromBlocks x.1.1.1 x.1.2 (-(x.1.2 + x.1.1.1ᴴ * Du * x.1.2)ᴴ)
            (x.2.1 + (θ * e) • (-(x.1.2ᴴ * Du * x.1.2))),
          (fromBlocks_cayley_eq_zero_iff Du hDu _ _ _ _).mpr ⟨x.1.1.2, rfl, by
            have h := key x.1.2 (x.2.1 + (θ * e) • (-(x.1.2ᴴ * Du * x.1.2)))
            rw [add_sub_cancel_right] at h
            rw [← h]; exact x.2.2⟩⟩
      left_inv := fun Y => by
        have h := (fromBlocks_cayley_eq_zero_iff Du hDu _ _ _ _).mp (by rw [Matrix.fromBlocks_toBlocks]; exact Y.2)
        apply Subtype.ext
        simp only [sub_add_cancel]
        rw [← h.2.1, Matrix.fromBlocks_toBlocks]
      right_inv := fun x => by
        ext
        · simp
        · simp
        · simp }
  rw [Nat.card_congr eqv, Nat.card_prod, Nat.card_prod]

private theorem card_skewHermitian_eq_card_hermitian {A : Type*} [CommRing A] [StarRing A] {z : Type*} {θ e : A}
    (he : (θ - star θ) * e = 1) :
    Nat.card {S : Matrix z z A // S + Sᴴ = 0} = Nat.card {M : Matrix z z A // Mᴴ = M} := by
  have hse : star e = -e := Formalism.HermitianLattices.Ext.L3.HermitianSublattices.star_inv_eq_neg he
  have hst : star (θ - star θ) = -(θ - star θ) := by rw [star_sub, star_star]; ring
  have he' : e * (θ - star θ) = 1 := by rw [mul_comm]; exact he
  exact Nat.card_congr
    { toFun := fun S => ⟨(θ - star θ) • S.1, by
        have hS : S.1ᴴ = -S.1 := eq_neg_of_add_eq_zero_right S.2
        rw [Matrix.conjTranspose_smul, hst, hS, neg_smul, smul_neg, neg_neg]⟩
      invFun := fun M => ⟨e • M.1, by
        rw [Matrix.conjTranspose_smul, hse, M.2, neg_smul, add_neg_cancel]⟩
      left_inv := fun S => Subtype.ext (by simp only [smul_smul, he', one_smul])
      right_inv := fun M => Subtype.ext (by simp only [smul_smul, he, one_smul]) }

private theorem exists_UJ_umat_eq_of_inUJ {A : Type*} [CommRing A] [StarRing A] {u : Type*} [Fintype u] [DecidableEq u]
    (Du Dv : Matrix u u A) (hDu : Duᴴ = Du) (huv : Du * Dv = 1) (hvu : Dv * Du = 1) :
    Nat.card {P : Matrix u u A // P + Pᴴ + Pᴴ * Du * P = 0} =
      Nat.card {γ : Matrix u u A // γᴴ * Du * γ = Du} := by
  have iden : ∀ P : Matrix u u A, (1 + P * Du)ᴴ * Du * (1 + P * Du) =
      Du + Du * (P + Pᴴ + Pᴴ * Du * P) * Du := by
    intro P
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, hDu]
    noncomm_ring
  have cancel : ∀ X : Matrix u u A, Dv * (Du * X * Du) * Dv = X := by
    intro X
    rw [← Matrix.mul_assoc Dv (Du * X) Du, ← Matrix.mul_assoc Dv Du X, hvu, Matrix.one_mul,
      Matrix.mul_assoc X Du Dv, huv, Matrix.mul_one]
  exact Nat.card_congr
    { toFun := fun P => ⟨1 + P.1 * Du, by rw [iden, P.2, Matrix.mul_zero, Matrix.zero_mul, add_zero]⟩
      invFun := fun γ => ⟨(γ.1 - 1) * Dv, by
        have h1 : 1 + (γ.1 - 1) * Dv * Du = γ.1 := by
          rw [Matrix.mul_assoc, hvu, Matrix.mul_one]; abel
        have h2 := iden ((γ.1 - 1) * Dv)
        rw [h1, γ.2] at h2
        have h3 : Du * ((γ.1 - 1) * Dv + ((γ.1 - 1) * Dv)ᴴ + ((γ.1 - 1) * Dv)ᴴ * Du * ((γ.1 - 1) * Dv)) * Du = 0 := by
          have := congrArg (fun X => X - Du) h2
          simp only [sub_self, add_sub_cancel_left] at this
          exact this.symm
        have h4 := cancel ((γ.1 - 1) * Dv + ((γ.1 - 1) * Dv)ᴴ + ((γ.1 - 1) * Dv)ᴴ * Du * ((γ.1 - 1) * Dv))
        rw [h3, Matrix.mul_zero, Matrix.zero_mul] at h4
        exact h4.symm⟩
      left_inv := fun P => Subtype.ext (by
        simp only [add_sub_cancel_left, Matrix.mul_assoc, huv, Matrix.mul_one])
      right_inv := fun γ => Subtype.ext (by
        simp only
        rw [Matrix.mul_assoc, hvu, Matrix.mul_one]; abel) }

theorem phi_mod_p_holds : PhiModP := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha
  classical
  haveI := finite_quot (K := K) h𝔭 1
  haveI : Subsingleton (𝓞 K ⧸ extP K 𝔭 ^ 0) :=
    Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
  obtain ⟨θ, e, he⟩ := exists_unit_quot hK h𝔭 1

  have hzero : ∀ i, a i ∈ 𝔭 →
      Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (a i)) = 0 := by
    intro i hi
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact Ideal.mem_map_of_mem _ hi
  have hinv : ∀ i : {i : Fin m // a i ∉ 𝔭}, ∃ v : (𝓞 K ⧸ extP K 𝔭 ^ 1),
      Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (a i.1)) * v = 1 := by
    intro i
    obtain ⟨y, j, hj, hy⟩ := h𝔭.exists_inv i.2
    refine ⟨Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) y), ?_⟩
    have h1 := congrArg (fun x => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) x)) hy
    simp only [map_add (f := _), map_mul, map_one] at h1
    have h2 : Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) j) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
      exact Ideal.mem_map_of_mem _ hj
    rw [h2, add_zero] at h1
    exact (mul_comm _ _).trans h1
  choose dv hdv using hinv
  obtain ⟨Du, hDu_def⟩ : ∃ Du : Matrix {i : Fin m // a i ∉ 𝔭} {i : Fin m // a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1),
      Du = Matrix.diagonal (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (a i.1))) :=
    ⟨_, rfl⟩
  have hDuh : Duᴴ = Du := by
    rw [hDu_def, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    rw [Pi.star_apply, star_mk, starO_ι]
  have huv : Du * Matrix.diagonal dv = 1 := by
    rw [hDu_def, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hdv i
  have hvu : Matrix.diagonal dv * Du = 1 := by
    rw [hDu_def, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hdv i

  let e' : Fin m ≃ {i : Fin m // a i ∉ 𝔭} ⊕ {i : Fin m // ¬ a i ∉ 𝔭} := (Equiv.sumCompl (fun i => a i ∉ 𝔭)).symm
  have hHD : Matrix.fromBlocks Du 0 0 0 = Matrix.reindex e' e' (diagQ K 𝔭 1 a) := by
    rw [hDu_def]
    ext (i | i) (j | j)
    · simp [e', diagQ, Matrix.diagonal_apply, Subtype.ext_iff]
    · have hij : i.1 ≠ j.1 := fun h => j.2 (h ▸ i.2)
      simp [e', diagQ, Matrix.diagonal_apply, hij]
    · have hij : i.1 ≠ j.1 := fun h => i.2 (h ▸ j.2)
      simp [e', diagQ, Matrix.diagonal_apply, hij]
    · have hi : a i.1 ∈ 𝔭 := not_not.mp i.2
      simp [e', diagQ, Matrix.diagonal_apply, hzero _ hi]
      first
      | exact fun _ => (hzero _ hi).symm
      | (intro _; rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) (𝓞 K ⧸ extP K 𝔭 ^ 1)]; exact (hzero _ hi).symm)
  have h6 : Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ 1) // phiQ K 𝔭 1 a Y = 0} =
      Nat.card {Y : Matrix ({i : Fin m // a i ∉ 𝔭} ⊕ {i : Fin m // ¬ a i ∉ 𝔭}) ({i : Fin m // a i ∉ 𝔭} ⊕ {i : Fin m // ¬ a i ∉ 𝔭}) (𝓞 K ⧸ extP K 𝔭 ^ 1) //
        Y + Yᴴ + Yᴴ * Matrix.fromBlocks Du 0 0 0 * Y = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Matrix.reindex e' e') fun Y => ?_)
    have hre : Matrix.reindex e' e' Y + (Matrix.reindex e' e' Y)ᴴ +
        (Matrix.reindex e' e' Y)ᴴ * Matrix.reindex e' e' (diagQ K 𝔭 1 a) * Matrix.reindex e' e' Y =
        Matrix.reindex e' e' (phiQ K 𝔭 1 a Y) := by
      unfold phiQ
      simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
      rfl
    rw [hHD, hre]
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      apply (Matrix.reindex e' e').injective
      rw [h]
      simp

  have hU := card_U_diag hK h𝔭 (ι := {i : Fin m // a i ∉ 𝔭}) (fun i => a i.1) (fun i => i.2)
  rw [← hDu_def] at hU
  have hR1 : Nat.card (𝓞 K ⧸ extP K 𝔭 ^ 1) = Ideal.absNorm 𝔭 ^ 2 := by
    have h := Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.card_ker_piQ hK (Fact.out) h𝔭 0
    have htop : RingHom.ker (piQ K 𝔭 0) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [RingHom.mem_ker]
      exact Subsingleton.elim _ _
    rw [htop] at h
    rw [← h]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun x => Submodule.mem_top))).symm
  have hMat : Nat.card (Matrix {i : Fin m // a i ∉ 𝔭} {i : Fin m // ¬ a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1)) =
      ((Ideal.absNorm 𝔭 ^ 2) ^ Fintype.card {i : Fin m // ¬ a i ∉ 𝔭}) ^ Fintype.card {i : Fin m // a i ∉ 𝔭} := by
    rw [show Nat.card (Matrix {i : Fin m // a i ∉ 𝔭} {i : Fin m // ¬ a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1)) = Nat.card ({i : Fin m // a i ∉ 𝔭} → {i : Fin m // ¬ a i ∉ 𝔭} → (𝓞 K ⧸ extP K 𝔭 ^ 1)) from rfl,
      Nat.card_fun, Nat.card_fun, hR1, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hherm : Nat.card {M : Matrix {i : Fin m // ¬ a i ∉ 𝔭} {i : Fin m // ¬ a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1) // Mᴴ = M} =
      Ideal.absNorm 𝔭 ^ (Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} * Fintype.card {i : Fin m // ¬ a i ∉ 𝔭}) := by
    rw [← Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.card_hermSub (r := {i : Fin m // ¬ a i ∉ 𝔭}) hK h𝔭 0]
    exact Nat.card_congr
      { toFun := fun M => ⟨M.1, Formalism.HermitianLattices.Ext.L3.HermitianSublattices.mem_hermSub.mpr ⟨M.2, fun _ _ => by
            rw [RingHom.mem_ker]; exact Subsingleton.elim _ _⟩⟩
        invFun := fun S => ⟨S.1, (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.mem_hermSub.mp S.2).1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hc : cJof 𝔭 a = Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} := by
    unfold cJof
    rw [Fintype.card_subtype]
    exact congrArg Finset.card (Finset.filter_congr (fun i _ => by
      rw [not_not]; exact vF_ne_zero_iff h𝔭 (ha i)))
  have hm : Fintype.card {i : Fin m // a i ∉ 𝔭} + Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} = m := by
    rw [← Fintype.card_sum, Fintype.card_congr e'.symm, Fintype.card_fin]
  rw [h6, card_fromBlocks_cayley_eq_mul Du hDuh he, exists_UJ_umat_eq_of_inUJ Du (Matrix.diagonal dv) hDuh huv hvu, card_skewHermitian_eq_card_hermitian he, hherm, hMat]
  push_cast
  rw [hU, hc, show m - Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} = Fintype.card {i : Fin m // a i ∉ 𝔭} by omega,
    show m ^ 2 = (Fintype.card {i : Fin m // a i ∉ 𝔭} + Fintype.card {i : Fin m // ¬ a i ∉ 𝔭}) ^ 2 by rw [hm]]
  ring

theorem phi_counting_holds : PhiCount := phiCount_of phi_mod_p_holds

end Formalism.L2.SG.Pf.LocalizedFibreSets
end
end

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.G5

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

theorem alphaDisc_of (hP : PhiCount) (hKc : KerCount) (hD : DiscOnto) : AlphaDisc := by
  unfold AlphaDisc
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hd L hL hLi 𝔭 h𝔭 b a hJ
  have : Fact (IsFixF K F) := ⟨hF⟩
  have hk1 : 2 * vd h L 𝔭 + 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1 := by omega
  have hk2 : 2 * vJof 𝔭 a + 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1 := by omega
  have hk0 : 1 ≤ 2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1 := by omega
  have ha : ∀ i, a i ≠ 0 := hJ.2.2.2.2
  have hm : finrank K (⊤ : Submodule K V) = finrank K V := finrank_top K V
  have hlin : LinearIndependent K b :=
    Formalism.L2.SG.Pf.GluingBases.linearIndependent_orth h b hJ.2.2.1 (fun i => by
      rw [hJ.2.2.2.1 i]
      exact (map_ne_zero (algebraMap F K)).2 (by exact_mod_cast ha i))
  have hspan : Submodule.span K (Set.range b) = ⊤ := by
    apply Submodule.eq_of_le_of_finrank_eq le_top
    rw [finrank_span_eq_card hlin, Fintype.card_fin]
  have hfull : Submodule.IsFullLattice K L := by
    refine { toIsLattice := hL, span_eq_top := ?_ }
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Formalism.L2.SG.Pf.GluingBases.locF_subset_span h𝔭.isPrime L
    rw [← hJ.2.1]
    exact Formalism.HermitianLattices.Ext.L3.LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩)
  have hphi := hP K F hK 𝔭 h𝔭 _ a ha _ hk0 0 (by simp) (fun i j => by simp)
  have hfib : ∀ T : Matrix (Fin (finrank K (⊤ : Submodule K V))) (Fin (finrank K (⊤ : Submodule K V)))
      (𝓞 K ⧸ extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)), Tᴴ = T →
      (∀ i j, T i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)))) →
      Nat.card {Y : Matrix (Fin (finrank K (⊤ : Submodule K V))) (Fin (finrank K (⊤ : Submodule K V)))
        (𝓞 K ⧸ extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)) //
          phiQ K 𝔭 (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) a Y = T} =
      Nat.card {Y : Matrix (Fin (finrank K (⊤ : Submodule K V))) (Fin (finrank K (⊤ : Submodule K V)))
        (𝓞 K ⧸ extP K 𝔭 ^ (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)) //
          phiQ K 𝔭 (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) a Y = 0} := by
    intro T hT hTm
    have h1 := hP K F hK 𝔭 h𝔭 _ a ha _ hk0 T hT hTm
    exact_mod_cast h1.trans hphi.symm
  have hker := hKc K F hK 𝔭 h𝔭 _ a ha _ hk2 _ hfib
  have hdisc := hD K F V hK h hs hd L hL hLi 𝔭 h𝔭 b a hJ _ hk2
  have hpos : (0 : ℝ) < Ideal.absNorm 𝔭 := by exact_mod_cast Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.absNorm_pos h𝔭
  have e1 : (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K (⊤ : Submodule K V) ^ 2 * (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1)) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) * finrank K V ^ 2) := by
    have h1 := congrArg (fun m : ℕ => (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2 * (2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1))) hm
    rw [h1]
    ring
  have e2 : finrank K (⊤ : Submodule K V) - cJof 𝔭 a = finrank K V - cJof 𝔭 a :=
    congrArg (fun x => x - cJof 𝔭 a) hm
  rw [Formalism.HermitianLattices.Ext.L3.firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hfull hLi h𝔭 hk1, hdisc, hker, Nat.cast_mul, hphi, e1, e2]
  have hne : (Ideal.absNorm 𝔭 : ℝ) ^ ((2 * vd h L 𝔭 + 2 * vJof 𝔭 a + 1) * finrank K V ^ 2) ≠ 0 :=
    pow_ne_zero _ hpos.ne'
  field_simp

theorem alphaDisc_of_discOnto (hD : DiscOnto) : AlphaDisc :=
  alphaDisc_of Formalism.L2.SG.Pf.LocalizedFibreSets.phi_counting_holds
    (by
      unfold KerCount
      intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha k hk N hN
      exact Formalism.L2.SG.Pf.discriminantGroupCounts.kerCount_main hK h𝔭 ha hk N hN) hD

end Formalism.L2.SG.Pf.G5
end
end

namespace Formalism.L2.SG.Pf.Cnt

theorem alpha_discriminant_holds : AlphaDisc :=
  Formalism.L2.SG.Pf.G5.alphaDisc_of_discOnto
    (Formalism.L2.SG.Pf.discriminantNormShapes.discOnto_of_uDModel Formalism.L2.SG.Pf.Cnt.unitary_discriminant_model)

end Formalism.L2.SG.Pf.Cnt
