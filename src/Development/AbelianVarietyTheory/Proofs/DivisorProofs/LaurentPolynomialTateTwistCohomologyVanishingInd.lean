module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyFiniteKilling
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNervePullbackBijectiveDegreeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllTraceOfMiddleX

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyVanishesPositive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProIsometryOfLocalIsometries
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStrictlyHenselianTateTwistAcyclic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStrictlyHenselianTateTwistAcyclic
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem finite_sh_acyclic_twists : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 0 < s → Subsingleton (Ht q (sp T) s i) := by
  intro q _ A _ hA _ T _ _ hfin s i hs
  obtain ⟨hH, hsep⟩ := hA
  obtain ⟨ι, hι, F, hF, hAF, e, hHF, hF'⟩ :=
    GlobalTheory.finite_algebra_strictly_henselian_pi A T
  exact acycF_of_pi_sh (ZMod q) (tw q i) ι F T ⟨e.toRingEquiv⟩
    (fun j => ⟨hHF j, (hF' j).1⟩) s hs

end GlobalTheory.EtC.GmStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStrictlyHenselianTateTwistAcyclicStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_strictlyHenselian_tateTwist_acyclic : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 0 < s → Subsingleton (Ht q (sp T) s i) := by
  first | (exact @GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists) | (exact GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists) | (intros; apply GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists  <;> assumption)
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem cech_level_acyc : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 0 < s → Subsingleton (Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) s i) := by
  intro q _ A _ hA hq A' _ _ hfin k s i hs
  obtain ⟨e0, -, -, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  haveI : Subsingleton (Ht q (sp (PiTensorProduct A (fun _ : Fin (k + 1) => A'))) s i) :=
    GlobalTheory.T.finite_strictlyHenselian_tateTwist_acyclic q A hA hq _ inferInstance s i hs
  let f : sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) ⟶ disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌)) :=
    disc.map e0.hom
  let g : disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌)) ⟶ sp (PiTensorProduct A (fun _ : Fin (k + 1) => A')) :=
    disc.map e0.inv
  have hgf : g ≫ f = 𝟙 _ := by
    exact (disc.mapIso e0).inv_hom_id
  have hinj : Function.Injective (pull (ZMod q) f (tw q i) s) := by
    intro x y hxy
    have := congrArg (pull (ZMod q) g (tw q i) s) hxy
    rwa [← pull_comp, ← pull_comp, hgf, pull_id, pull_id] at this
  exact hinj.subsingleton

end GlobalTheory.EtC.GmStep
end

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_cohomology_vanishes_positive : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 0 < s → Subsingleton (Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) s i) := by
  first | (exact @GlobalTheory.EtC.GmStep.cech_level_acyc) | (exact GlobalTheory.EtC.GmStep.cech_level_acyc) | (intros; apply GlobalTheory.EtC.GmStep.cech_level_acyc  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExact
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section

namespace GlobalTheory.EtC.RowVanish

open GlobalTheory.EtC.ClsBasic GlobalTheory.EtC.HCElements

variable {R : Type} [CommRing R] {F : Shv R}

theorem const_d (P : PSh) : ((chains R).obj (disc.obj P)).d (-(((0 : ℕ) + 1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) = 0 := by
  rw [chains_d (R := R) (disc.obj P) 0, Fin.sum_univ_two]
  have h0 : (disc.obj P).δ (0 : Fin 2) = 𝟙 _ := rfl
  have h1 : (disc.obj P).δ (1 : Fin 2) = 𝟙 _ := rfl
  simp [h0, h1]

def dcoc (P : PSh) (m : ℤ) (t : (free R).obj P ⟶ (res R F).X m) (ht : t ≫ (res R F).d m (m + 1) = 0) :
    Cocycle ((chains R).obj (disc.obj P)) (res R F) m :=
  Cocycle.mk (Cochain.single (p := -((0 : ℕ) : ℤ)) (q := m) ((chainsXIso R (disc.obj P) 0).hom ≫ t) m) (m + 1) rfl (by
    rw [Cochain.δ_single _ m (m + 1) rfl (-(((0 : ℕ) + 1 : ℕ) : ℤ)) (m + 1) (by simp) rfl, const_d]
    simp [ht])

def dcl (P : PSh) (m : ℤ) (t : (free R).obj P ⟶ (res R F).X m) (ht : t ≫ (res R F).d m (m + 1) = 0) :
    H R (disc.obj P) F m :=
  CohomologyClass.mk (dcoc P m t ht)

theorem dcl_add (P : PSh) (m : ℤ) (t t' : (free R).obj P ⟶ (res R F).X m) (ht ht') (h) :
    dcl P m t ht + dcl P m t' ht' = dcl P m (t + t') h := by
  rw [dcl, dcl, dcl, ← CohomologyClass.mk_add]
  congr 1
  refine Cocycle.ext ?_
  change Cochain.single _ m + Cochain.single _ m = Cochain.single _ m
  rw [← single_add', Preadditive.comp_add]

def closedSub (P : PSh) (m : ℤ) : AddSubgroup ((free R).obj P ⟶ (res R F).X m) :=
  (Preadditive.rightComp ((free R).obj P) ((res R F).d m (m + 1))).ker

def dclHom (P : PSh) (m : ℤ) : closedSub (F := F) P m →+ H R (disc.obj P) F m :=
  AddMonoidHom.mk' (fun t => dcl P m t.1 t.2) (fun t t' => (dcl_add P m t.1 t'.1 t.2 t'.2 (t + t').2).symm)

theorem dcl_sum_zsmul (P : PSh) (m : ℤ) {ι : Type} (S : Finset ι) (c : ι → ℤ) (t : ι → ((free R).obj P ⟶ (res R F).X m))
    (ht : ∀ i, t i ≫ (res R F).d m (m + 1) = 0) (h) :
    ∑ i ∈ S, c i • dcl P m (t i) (ht i) = dcl P m (∑ i ∈ S, c i • t i) h := by
  have hs : (∑ i ∈ S, c i • (⟨t i, ht i⟩ : closedSub (F := F) P m)) = ⟨∑ i ∈ S, c i • t i, h⟩ := by
    apply Subtype.ext
    simp
  have e : dclHom (F := F) P m (∑ i ∈ S, c i • (⟨t i, ht i⟩ : closedSub (F := F) P m)) =
      ∑ i ∈ S, c i • dcl P m (t i) (ht i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    rfl
  rw [← e, hs]
  rfl

end GlobalTheory.EtC.RowVanish

namespace GlobalTheory.EtC.RowVanish

open GlobalTheory.EtC.ClsBasic GlobalTheory.EtC.HCElements

variable {R : Type} [CommRing R] {F : Shv R}

theorem pull_dcl {P P' : PSh} (f : P ⟶ P') (m : ℤ) (t : (free R).obj P' ⟶ (res R F).X m) (ht) (h) :
    pull R (disc.map f) F m (dcl P' m t ht) = dcl P m ((free R).map f ≫ t) h := by
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map (disc.map f))) (dcoc P' m t ht) (zero_add m)) = _
  congr 1
  refine Cocycle.ext ?_
  change (Cochain.ofHom ((chains R).map (disc.map f))).comp (Cochain.single _ m) (zero_add m) = Cochain.single _ m
  rw [ofHom_comp_single, ← Category.assoc, chainsXIso_nat (disc.map f) 0, Category.assoc]
  rfl

theorem dcl_bd (P : PSh) (m : ℤ) (y : (free R).obj P ⟶ (res R F).X (m - 1)) (h) :
    dcl P m (y ≫ (res R F).d (m - 1) m) h = 0 := by
  rw [dcl, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)]
  refine ⟨Cochain.single (p := -((0 : ℕ) : ℤ)) (q := m - 1) ((chainsXIso R (disc.obj P) 0).hom ≫ y) (m - 1), ?_⟩
  change _ = Cochain.single _ m
  rw [Cochain.δ_single _ (m - 1) m (by omega) (-(((0 : ℕ) + 1 : ℕ) : ℤ)) m (by simp) (by omega), const_d]
  simp

theorem dcl_eq_zero (P : PSh) (m : ℤ) (t : (free R).obj P ⟶ (res R F).X m) (ht) (h0 : dcl P m t ht = 0) :
    ∃ u : (free R).obj P ⟶ (res R F).X (m - 1), t = u ≫ (res R F).d (m - 1) m := by
  rw [dcl, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (m - 1) (by omega)] at h0
  obtain ⟨β, hβ⟩ := h0
  have e := Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) m (by simp)
  rw [δ_v (m - 1) m (by omega) β _ m _ (m - 1) (-((0 : ℕ) : ℤ) + 1) (by omega) rfl] at e
  have hz : ((chains R).obj (disc.obj P)).d (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) = 0 :=
    (chains_X_isZero R _ _ (by simp)).eq_of_tgt _ _
  rw [hz, zero_comp, smul_zero, add_zero] at e
  change _ = (Cochain.single _ m).v _ _ _ at e
  rw [Cochain.single_v] at e
  refine ⟨(chainsXIso R (disc.obj P) 0).inv ≫ β.v (-((0 : ℕ) : ℤ)) (m - 1) (by omega), ?_⟩
  rw [Category.assoc, e, Iso.inv_hom_id_assoc]

theorem rowD_dcl (E : Spc) (s : ℤ) (p : ℕ) (t : (free R).obj (E.obj (op ⦋p⦌)) ⟶ (res R F).X s) (ht) (h) :
    rowD R E F s p (dcl _ s t ht) =
      dcl _ s ((∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ t) h := by
  have hi : ∀ i : Fin (p + 2), ((free R).map (E.δ i) ≫ t) ≫ (res R F).d s (s + 1) = 0 := fun i => by
    rw [Category.assoc, ht, comp_zero]
  calc rowD R E F s p (dcl _ s t ht)
      = ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) • dcl _ s ((free R).map (E.δ i) ≫ t) (hi i) := by
        simp only [rowD, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pull_dcl]
    _ = dcl _ s (∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) • ((free R).map (E.δ i) ≫ t))
          (by simp [Preadditive.sum_comp, hi]) := dcl_sum_zsmul _ s _ _ _ hi _
    _ = _ := by
        congr 1
        simp [Preadditive.sum_comp]

theorem dcl_surj (P : PSh) (m : ℤ) (w : H R (disc.obj P) F m) :
    ∃ (s : (free R).obj P ⟶ (res R F).X m) (hs : s ≫ (res R F).d m (m + 1) = 0), w = dcl P m s hs := by
  obtain ⟨α, rfl, hα⟩ := GlobalTheory.EtC.discRep R P (res R F) m w
  have e := Cochain.congr_v (Cocycle.δ_eq_zero α (m + 1)) (-((0 : ℕ) : ℤ)) (m + 1) (by simp)
  rw [δ_v m (m + 1) rfl _ _ _ _ m (-((0 : ℕ) : ℤ) + 1) (by simp) rfl,
    (chains_X_isZero R _ (-((0 : ℕ) : ℤ) + 1) (by simp)).eq_of_tgt (((chains R).obj (disc.obj P)).d _ _) 0] at e
  simp only [zero_comp, smul_zero, add_zero, Cochain.zero_v] at e
  refine ⟨(chainsXIso R (disc.obj P) 0).inv ≫ α.1.v (-((0 : ℕ) : ℤ)) m (by simp), by rw [Category.assoc, e, comp_zero], ?_⟩
  congr 1
  refine Cocycle.ext (Cochain.ext _ _ fun p' q' hpq => ?_)
  change α.1.v p' q' hpq = (Cochain.single _ m).v p' q' hpq
  rcases lt_trichotomy p' (-((0 : ℕ) : ℤ)) with hp | hp | hp
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, p' = -(j : ℤ) := ⟨(-p').toNat, by omega⟩
    rw [hα j (by omega) q' hpq, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
  · subst hp
    obtain rfl : q' = m := by omega
    rw [Cochain.single_v, Iso.hom_inv_id_assoc]
  · exact (chains_X_isZero R _ p' (by omega)).eq_of_src _ _

end GlobalTheory.EtC.RowVanish

namespace GlobalTheory.EtC.RowVanish

open GlobalTheory.EtC.ClsBasic GlobalTheory.EtC.HCElements

variable {R : Type} [CommRing R] {F : Shv R}

theorem dcl_congr (P : PSh) (m : ℤ) {t t' : (free R).obj P ⟶ (res R F).X m} (e : t = t') (ht) (ht') :
    dcl P m t ht = dcl P m t' ht' := by
  subst e; rfl

theorem dcl_sub (P : PSh) (m : ℤ) (t t' : (free R).obj P ⟶ (res R F).X m) (ht ht') (h) :
    dcl P m (t - t') h = dcl P m t ht - dcl P m t' ht' := by
  refine eq_sub_of_add_eq ?_
  rw [dcl_add P m _ _ h ht' (by rw [sub_add_cancel]; exact ht)]
  exact dcl_congr P m (sub_add_cancel t t') _ _

theorem clear_step {K L : Cx R} {n : ℤ} (z : Cocycle K L n) (k : ℕ)
    (hv : ∀ p q (hpq : p + n = q), -(k : ℤ) < p → z.1.v p q hpq = 0) (γ : Cochain K L (n - 1))
    (h1 : ∀ p q (hpq : p + n = q), -(k : ℤ) < p → (δ (n - 1) n γ).v p q hpq = 0)
    (h2 : ∀ q (hpq : -(k : ℤ) + n = q), (δ (n - 1) n γ).v (-(k : ℤ)) q hpq = z.1.v (-(k : ℤ)) q hpq) :
    ∃ z' : Cocycle K L n, CohomologyClass.mk z' = CohomologyClass.mk z ∧
      ∀ p q (hpq : p + n = q), -((k + 1 : ℕ) : ℤ) < p → z'.1.v p q hpq = 0 := by
  let c : Cocycle K L n := Cocycle.mk (δ (n - 1) n γ) (n + 1) (by omega) (δ_δ _ _ _ _)
  refine ⟨z - c, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    exact ⟨γ, rfl⟩
  · intro p q hpq hp
    rw [Cocycle.coe_sub, Cochain.sub_v]
    change z.1.v p q hpq - (δ (n - 1) n γ).v p q hpq = 0
    rcases lt_or_eq_of_le (show -(k : ℤ) ≤ p by omega) with h | h
    · rw [hv p q hpq h, h1 p q hpq h, sub_zero]
    · subst h
      rw [h2, sub_self]

end GlobalTheory.EtC.RowVanish


open GlobalTheory.EtC.RowVanish GlobalTheory.EtC.ClsBasic GlobalTheory.EtC.HCElements in
theorem GlobalTheory.EtC.vanish_of_rowExact : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (P : PSh) (g : disc.obj P ⟶ E),
    IsIso (g.app (op ⦋0⦌)) →
    ∀ (n : ℕ) (x : H R E F n), pull R g F n x = 0 →
    (∀ p : ℕ, p + 1 ≤ n → RowExact R E F ((n : ℤ) - ((p + 1 : ℕ) : ℤ)) p) → x = 0 := by
  intro R _ F E P g hg n x hx hrow
  obtain ⟨-, hneg, -, -, -, hpos⟩ := GlobalTheory.EtC.res_basic R F
  have key : ∀ k : ℕ, k ≤ n + 1 → ∃ z : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk z = x ∧
      ∀ p q (hpq : p + (n : ℤ) = q), -(k : ℤ) < p → z.1.v p q hpq = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨z, rfl⟩ := x.mk_surjective
      exact ⟨z, rfl, fun p q hpq hp => (hpos E p (by omega)).eq_of_src _ _⟩
    | succ k ih =>
      intro hk
      obtain ⟨z, hz, hv⟩ := ih (by omega)
      rcases k with _ | p
      · subst hz
        have hx' : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map g)) z (zero_add _)) = 0 := hx
        rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ ((n : ℤ) - 1) (by omega)] at hx'
        obtain ⟨β, hβ⟩ := hx'
        have e := Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) n (by simp)
        rw [δ_v ((n : ℤ) - 1) n (by omega) β _ n _ ((n : ℤ) - 1) (-((0 : ℕ) : ℤ) + 1) (by omega) rfl,
          (chains_X_isZero R _ (-((0 : ℕ) : ℤ) + 1) (by simp)).eq_of_tgt (((chains R).obj (disc.obj P)).d _ _) 0,
          zero_comp, smul_zero, add_zero] at e
        change _ = ((Cochain.ofHom ((chains R).map g)).comp z.1 (zero_add _)).v _ _ _ at e
        rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at e
        haveI : IsIso (((chains R).map g).f (-((0 : ℕ) : ℤ))) := by
          have h := chainsXIso_nat (R := R) g 0
          rw [← Iso.eq_comp_inv] at h
          rw [h]
          infer_instance
        let γ : Cochain ((chains R).obj E) (res R F) ((n : ℤ) - 1) :=
          Cochain.single (p := -((0 : ℕ) : ℤ)) (q := (n : ℤ) - 1)
            (inv (((chains R).map g).f (-((0 : ℕ) : ℤ))) ≫ β.v (-((0 : ℕ) : ℤ)) ((n : ℤ) - 1) (by omega)) ((n : ℤ) - 1)
        refine clear_step z 0 hv γ (fun p q hpq hp => (hpos E p (by omega)).eq_of_src _ _) (fun q hpq => ?_)
        obtain rfl : q = (n : ℤ) := by omega
        rw [δ_v ((n : ℤ) - 1) n (by omega) γ _ n hpq ((n : ℤ) - 1) (-((0 : ℕ) : ℤ) + 1) (by omega) rfl,
          (hpos E (-((0 : ℕ) : ℤ) + 1) (by simp)).eq_of_tgt (((chains R).obj E).d _ _) 0, zero_comp, smul_zero, add_zero,
          Cochain.single_v, Category.assoc, e, IsIso.inv_hom_id_assoc]
      · subst hz
        obtain ⟨S, hS⟩ : ∃ S : ℤ, S = (n : ℤ) - ((p + 1 : ℕ) : ℤ) := ⟨_, rfl⟩
        have hrowp := hrow p (by omega)
        rw [← hS] at hrowp
        let t : (free R).obj (E.obj (op ⦋p + 1⦌)) ⟶ (res R F).X S :=
          (chainsXIso R E (p + 1)).inv ≫ z.1.v (-((p + 1 : ℕ) : ℤ)) S (by omega)
        have ht : t ≫ (res R F).d S (S + 1) = 0 := by
          have e := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-((p + 1 : ℕ) : ℤ)) (S + 1) (by omega)
          rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ S (-((p + 1 : ℕ) : ℤ) + 1) (by omega) rfl,
            hv (-((p + 1 : ℕ) : ℤ) + 1) _ _ (by omega), comp_zero, smul_zero, add_zero, Cochain.zero_v] at e
          simp only [t, Category.assoc, e, comp_zero]

        let D1 : (free R).obj (E.obj (op ⦋p + 1 + 1⦌)) ⟶ (free R).obj (E.obj (op ⦋p + 1⦌)) :=
          ∑ i : Fin (p + 1 + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)
        have hb : D1 ≫ t = ((-(((n : ℤ) + 1).negOnePow : ℤ)) • ((chainsXIso R E (p + 1 + 1)).inv ≫
            z.1.v (-((p + 1 + 1 : ℕ) : ℤ)) (S - 1) (by omega))) ≫ (res R F).d (S - 1) S := by
          have e := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-((p + 1 + 1 : ℕ) : ℤ)) S (by omega)
          rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ (S - 1) (-((p + 1 : ℕ) : ℤ)) (by omega) (by omega),
            chains_d E (p + 1), Cochain.zero_v, Units.smul_def] at e
          have e2 := eq_neg_of_add_eq_zero_right e
          apply (cancel_epi (chainsXIso R E (p + 1 + 1)).hom).1
          have e3 := congrArg (fun f => (((n : ℤ) + 1).negOnePow : ℤ) • f) e2
          simp only [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul] at e3
          simp only [D1, t, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc, Iso.hom_inv_id_assoc,
            smul_neg, neg_smul, Preadditive.neg_comp, Preadditive.comp_neg] at e3 ⊢
          rw [← e3]
        have hD1 : (D1 ≫ t) ≫ (res R F).d S (S + 1) = 0 := by rw [Category.assoc, ht, comp_zero]
        have hc0 : rowD R E F S (p + 1) (dcl _ S t ht) = 0 := by
          rw [rowD_dcl E S (p + 1) t ht hD1]
          rw [dcl_congr _ S hb hD1 (by rw [← hb]; exact hD1)]
          exact dcl_bd _ S _ _
        obtain ⟨w, hw⟩ := hrowp _ hc0
        obtain ⟨s, hs, hsw⟩ := dcl_surj (E.obj (op ⦋p⦌)) S w
        subst w
        let D0 : (free R).obj (E.obj (op ⦋p + 1⦌)) ⟶ (free R).obj (E.obj (op ⦋p⦌)) :=
          ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)
        have hD0 : (D0 ≫ s) ≫ (res R F).d S (S + 1) = 0 := by rw [Category.assoc, hs, comp_zero]
        rw [rowD_dcl E S p s hs hD0] at hw
        have hdiff : dcl _ S (t - D0 ≫ s) (by rw [Preadditive.sub_comp, ht, hD0, sub_zero]) = 0 := by
          rw [dcl_sub _ S t (D0 ≫ s) ht hD0, ← hw, sub_self]
        obtain ⟨u, hu⟩ := dcl_eq_zero _ S _ _ hdiff
        let ε : ℤˣ := (n : ℤ).negOnePow
        let γ : Cochain ((chains R).obj E) (res R F) ((n : ℤ) - 1) :=
          Cochain.single (p := -((p + 1 : ℕ) : ℤ)) (q := S - 1) ((chainsXIso R E (p + 1)).hom ≫ u) ((n : ℤ) - 1) +
            ε • Cochain.single (p := -((p : ℕ) : ℤ)) (q := S) ((chainsXIso R E p).hom ≫ s) ((n : ℤ) - 1)
        have htz : z.1.v (-((p + 1 : ℕ) : ℤ)) S (by omega) =
            (chainsXIso R E (p + 1)).hom ≫ (u ≫ (res R F).d (S - 1) S + D0 ≫ s) := by
          rw [← hu, sub_add_cancel]
          simp only [t, Iso.hom_inv_id_assoc]
        refine clear_step z (p + 1) hv γ (fun p' q hpq hp' => ?_) (fun q hpq => ?_)
        · rcases eq_or_ne p' (-((p : ℕ) : ℤ)) with h | h
          · subst h
            obtain rfl : q = S + 1 := by omega
            rw [δ_v ((n : ℤ) - 1) n (by omega) γ _ _ hpq S (-((p : ℕ) : ℤ) + 1) (by omega) rfl]
            simp (disch := omega) only [γ, Cochain.add_v, Cochain.units_smul_v, Cochain.single_v_eq_zero,
              Cochain.single_v, smul_zero, add_zero, zero_add, comp_zero]
            rw [Units.smul_def, Preadditive.zsmul_comp, Category.assoc, hs, comp_zero, smul_zero]
          · rw [δ_v ((n : ℤ) - 1) n (by omega) γ _ _ hpq (q - 1) (p' + 1) (by omega) rfl]
            simp (disch := omega) only [γ, Cochain.add_v, Cochain.units_smul_v, Cochain.single_v_eq_zero,
              smul_zero, add_zero, zero_add, comp_zero, zero_comp]
        · have hq : S = q := by omega
          subst hq
          rw [δ_v ((n : ℤ) - 1) n (by omega) γ _ _ hpq (S - 1) (-((p : ℕ) : ℤ)) (by omega) (by omega), chains_d E p]
          simp (disch := omega) only [γ, Cochain.add_v, Cochain.units_smul_v, Cochain.single_v_eq_zero,
            Cochain.single_v, smul_zero, add_zero, zero_add]
          rw [htz, Units.smul_def, Units.smul_def, Preadditive.comp_zsmul, smul_smul, ← Units.val_mul,
            Int.units_mul_self, Units.val_one, one_smul]
          simp only [D0, Category.assoc, Iso.inv_hom_id_assoc, Preadditive.comp_add]
  obtain ⟨z, hz, hv⟩ := key (n + 1) le_rfl
  have h0 : z = 0 := Cocycle.ext (Cochain.ext _ _ fun p q hpq => by
    by_cases hp : -((n + 1 : ℕ) : ℤ) < p
    · exact hv p q hpq hp
    · exact (hneg q (by omega)).eq_of_tgt _ _)
  rw [← hz, h0]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExactStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_eq_zero_of_simplicialRowExact : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (P : PSh) (g : disc.obj P ⟶ E), IsIso (g.app (op ⦋0⦌)) →
  ∀ (n : ℕ) (x : H R E F n), pull R g F n x = 0 →
  (∀ p : ℕ, p + 1 ≤ n → RowExact R E F ((n : ℤ) - ((p + 1 : ℕ) : ℤ)) p) → x = 0 := by
  first | (exact @GlobalTheory.EtC.vanish_of_rowExact) | (exact GlobalTheory.EtC.vanish_of_rowExact) | (intros; apply GlobalTheory.EtC.vanish_of_rowExact  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialSpectralRowExactZeroOfAcyclic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialSpectralRowExactZeroOfAcyclic
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section

namespace GlobalTheory.EtC.GmStep.DegRow

variable {R : Type} [CommRing R] (F : Shv R)

theorem cobd_disc (P : PSh) (s : (free R).obj ((disc.obj P).obj (op ⦋0⦌)) ⟶ F) :
    cobd (E := disc.obj P) s = 0 := by
  simp [cobd, Fin.sum_univ_two, SimplicialObject.δ]

theorem exists_rep (E : Spc) (x : H R E F 0) : ∃ s : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, IsCls s x := by
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨z, rfl⟩ := x.mk_surjective
  let b := (z.1 : Cochain ((chains R).obj E) (res R F) 0).v 0 0 (add_zero 0)
  have hb : b ≫ (res R F).d 0 1 = 0 := by
    have e := Cochain.congr_v (Cocycle.δ_eq_zero z 1) 0 1 (zero_add 1)
    rw [δ_v 0 1 (zero_add 1) _ 0 1 (zero_add 1) 0 1 (by omega) (zero_add 1),
      (hpos E 1 one_pos).eq_of_tgt (((chains R).obj E).d 0 1) 0, zero_comp, smul_zero, add_zero] at e
    exact e
  haveI : Mono (ShortComplex.mk _ _ w).f := hmono
  let t' : ((chains R).obj E).X 0 ⟶ F := hex.lift b hb
  have ht' : t' ≫ resι R F = b := hex.lift_f b hb
  refine ⟨(chainsXIso R E 0).inv ≫ t', z, rfl, ?_⟩
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = 0 := by omega
    change b = (Cochain.single (p := -((0 : ℕ) : ℤ)) (q := 0) ((chainsXIso R E 0).hom ≫ ((chainsXIso R E 0).inv ≫ t') ≫ resι R F) ((0 : ℕ) : ℤ)).v (-((0 : ℕ) : ℤ)) 0 (by simp)
    rw [Cochain.single_v, ← ht']
    simp
  · rcases lt_or_gt_of_ne hp with hp | hp
    · exact (hneg q (by omega)).eq_of_tgt _ _
    · exact (hpos E p hp).eq_of_src _ _

def clsFun (P : PSh) (s : (free R).obj P ⟶ F) : H R (disc.obj P) F 0 :=
  Classical.choose ((isCls_basic R F (disc.obj P) 0).1 s (cobd_disc F P s))

theorem clsFun_spec (P : PSh) (s : (free R).obj P ⟶ F) : IsCls (E := disc.obj P) (n := 0) s (clsFun F P s) :=
  Classical.choose_spec ((isCls_basic R F (disc.obj P) 0).1 s (cobd_disc F P s))

theorem clsFun_eq (P : PSh) (s : (free R).obj P ⟶ F) (x : H R (disc.obj P) F 0)
    (h : IsCls (E := disc.obj P) (n := 0) s x) : clsFun F P s = x :=
  (isCls_basic R F (disc.obj P) 0).2.2.1 s _ _ (clsFun_spec F P s) h

def cls0 (P : PSh) : ((free R).obj P ⟶ F) →+ H R (disc.obj P) F 0 :=
  AddMonoidHom.mk' (clsFun F P) fun s s' =>
    clsFun_eq F P (s + s') _ ((isCls_basic R F (disc.obj P) 0).2.1 s s' _ _ (clsFun_spec F P s) (clsFun_spec F P s'))

theorem degreeZeroClassConstantSpaceAddHom_represents (P : PSh) (s : (free R).obj P ⟶ F) : IsCls (E := disc.obj P) (n := 0) s (cls0 F P s) :=
  clsFun_spec F P s

theorem degreeZeroClassConstantSpaceAddHom_eq_of_represents (P : PSh) (s : (free R).obj P ⟶ F) (x : H R (disc.obj P) F 0)
    (h : IsCls (E := disc.obj P) (n := 0) s x) : cls0 F P s = x :=
  clsFun_eq F P s x h

theorem etaleSpaceCohomologyPullback_degreeZeroClass {P P' : PSh} (f : P ⟶ P') (s : (free R).obj P' ⟶ F) :
    pull R (disc.map f) F 0 (cls0 F P' s) = cls0 F P ((free R).map f ≫ s) :=
  (degreeZeroClassConstantSpaceAddHom_eq_of_represents F P _ _ ((isCls_basic R F (disc.obj P') 0).2.2.2.2 (disc.obj P) (disc.map f) s _ (degreeZeroClassConstantSpaceAddHom_represents F P' s))).symm

theorem degreeZeroClassConstantSpaceAddHom_eq_zero_imp (P : PSh) (s : (free R).obj P ⟶ F) (h : cls0 F P s = 0) : s = 0 :=
  (leray_inj R F (disc.obj P) 0 (fun k m hm hkm _ => by omega)).1 s (h ▸ degreeZeroClassConstantSpaceAddHom_represents F P s)

theorem simplicialSpectralRowDifferential_degreeZeroClass (E : Spc) (p : ℕ) (s : (free R).obj (E.obj (op ⦋p⦌)) ⟶ F) :
    rowD R E F 0 p (cls0 F _ s) = cls0 F _ (cobd s) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rowD, cobd, map_sum, map_zsmul]
    change (AddMonoidHom.eval (cls0 F _ s)) (∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E.δ j)) F 0) = _
    rw [map_sum]
    change (∑ j : Fin (p + 2), (((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E.δ j)) F 0) (cls0 F _ s)) = _
    simp only [AddMonoidHom.smul_apply, etaleSpaceCohomologyPullback_degreeZeroClass]

end GlobalTheory.EtC.GmStep.DegRow


open GlobalTheory.EtC.GmStep.DegRow in
theorem GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
    (∀ (p : ℕ) (s : ℤ), 0 < s → Subsingleton (H R (disc.obj (E.obj (op ⦋p⦌))) F s)) →
    (∀ m : ℤ, 0 < m → Subsingleton (H R E F m)) → ∀ p : ℕ, RowExact R E F 0 p := by
  intro R _ F E hlev htot p y hy
  obtain ⟨s, hs⟩ : ∃ s : (free R).obj (E.obj (op ⦋p + 1⦌)) ⟶ F, IsCls (E := disc.obj (E.obj (op ⦋p + 1⦌))) (n := 0) s y :=
    exists_rep F (disc.obj (E.obj (op ⦋p + 1⦌))) y
  obtain rfl : cls0 F (E.obj (op ⦋p + 1⦌)) s = y := degreeZeroClassConstantSpaceAddHom_eq_of_represents F _ s y hs
  rw [simplicialSpectralRowDifferential_degreeZeroClass] at hy
  have hc : cobd s = 0 := degreeZeroClassConstantSpaceAddHom_eq_zero_imp F _ _ hy
  obtain ⟨x, hx⟩ := (isCls_basic R F E (p + 1)).1 s hc
  have hx0 : x = 0 := @Subsingleton.elim _ (htot _ (by positivity)) x 0
  rw [hx0] at hx
  obtain ⟨t, ht⟩ := (leray_inj R F E p (fun k m hm _ y => @Subsingleton.elim _ (hlev k m (by exact_mod_cast hm)) y 0)).2 s hx
  exact ⟨cls0 F _ t, by rw [simplicialSpectralRowDifferential_degreeZeroClass, ht]⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialSpectralRowExactZeroOfAcyclicStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
  (∀ (p : ℕ) (s : ℤ), 0 < s → Subsingleton (H R (disc.obj (E.obj (op ⦋p⦌))) F s)) →
  (∀ m : ℤ, 0 < m → Subsingleton (H R E F m)) → ∀ p : ℕ, RowExact R E F 0 p := by
  first | (exact @GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic) | (exact GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic) | (intros; apply GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelCohomologySubsingleton
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelCohomologySubsingleton
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

theorem finite_piTensorProduct_const (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Module.Finite A A']
    (ι : Type) [Fintype ι] : Module.Finite A (PiTensorProduct A fun _ : ι => A') := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := A')
  refine ⟨⟨Finset.univ.image (fun r : ι → S => PiTensorProduct.tprod A (fun i => (r i : A'))), ?_⟩⟩
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  have hm : ∀ i, m i ∈ Submodule.span A (S : Set A') := fun i => hS ▸ Submodule.mem_top
  choose c hc using fun i => (Submodule.mem_span_finset).1 (hm i)
  have hm' : m = fun i => ∑ s ∈ S, c i s • s := funext fun i => ((hc i).2).symm
  rw [hm', MultilinearMap.map_sum_finset]
  refine Submodule.sum_mem _ fun r hr => ?_
  rw [MultilinearMap.map_smul_univ]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [Finset.coe_image]
  refine ⟨fun i => ⟨r i, Fintype.mem_piFinset.1 hr i⟩, by simp, rfl⟩

theorem level_vanish : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 2 ≤ s → s < n →
  Subsingleton (Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) s i) := by
  intro q _ n hyp A _ _ hSH hq A' _ _ hfin k s i hs hsn
  obtain ⟨_, e, -, -⟩ := GlobalTheory.T.laurentCechNerve_level_spec_tensorPower A A' k
  have hT := GlobalTheory.T.tateTwistCohomology_laurent_vanishing_finite_algebra q n hyp A hSH hq (PiTensorProduct A fun _ : Fin (k + 1) => A')
    (finite_piTensorProduct_const A A' (Fin (k + 1))) s i hs hsn
  haveI : Subsingleton (Ht q (disc.obj (yoneda.obj (Spec (CommRingCat.of
    (LaurentPolynomial (PiTensorProduct A fun _ : Fin (k + 1) => A')))))) s i) := hT
  let f := disc.mapIso e
  have inj : Function.Injective (pull (ZMod q) f.hom (tw q i) s) := fun x y h => by
    have h' := congrArg (pull (ZMod q) f.inv (tw q i) s) h
    rwa [← pull_comp, ← pull_comp, Iso.inv_hom_id, pull_id, pull_id] at h'
  exact inj.subsingleton

end GlobalTheory.EtC.GmStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCechNerveLevelCohomologySubsingletonStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentCechNerve_level_cohomology_subsingleton : ∀ (q : ℕ) [NeZero q] (n : ℤ), (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
  ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
  ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 2 ≤ s → s < n →
  Subsingleton (Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) s i) := by
  first | (exact @GlobalTheory.EtC.GmStep.level_vanish) | (exact GlobalTheory.EtC.GmStep.level_vanish) | (intros; apply GlobalTheory.EtC.GmStep.level_vanish  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechNerveDiagonalIsoZeroOverBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechNerveDiagonalIsoZeroOverBase
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep

noncomputable def cechDiagApp {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) :
    yoneda.obj Y ⟶ widePullback (yoneda.obj X) (fun _ : Fin (k + 1) => yoneda.obj Y) (fun _ => yoneda.map f) :=
  WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (by intro; exact Category.id_comp _)

theorem cechDiagApp_π {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) (j : Fin (k + 1)) :
    cechDiagApp f k ≫ WidePullback.π _ j = 𝟙 _ := WidePullback.lift_π _ _ _ _ _

theorem cechDiagApp_base {Y X : Scheme.{0}} (f : Y ⟶ X) (k : ℕ) :
    cechDiagApp f k ≫ WidePullback.base _ = yoneda.map f := WidePullback.lift_base _ _ _ _

noncomputable def cechDiag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := cechDiagApp f n.unop.len
  naturality n m g := by
    change 𝟙 (yoneda.obj Y) ≫ cechDiagApp f m.unop.len = cechDiagApp f n.unop.len ≫ _
    rw [Category.id_comp]
    apply WidePullback.hom_ext
    · intro j
      rw [cechDiagApp_π]
      erw [Category.assoc, WidePullback.lift_π]
      exact (cechDiagApp_π f _ _).symm
    · rw [cechDiagApp_base]
      refine Eq.trans ?_ (Category.assoc (cechDiagApp f _) ((cech f).map g) _).symm
      erw [WidePullback.lift_base]
      exact (cechDiagApp_base f _).symm

theorem cechDiag_spec {Y X : Scheme.{0}} (f : Y ⟶ X) :
    ∃ Δ : sch.obj Y ⟶ cech f, IsIso (Δ.app (op ⦋0⦌)) ∧ Δ ≫ cechAug f = sch.map f := by
  refine ⟨cechDiag f, ?_, ?_⟩
  · refine ⟨⟨(WidePullback.π (fun _ : Fin (0 + 1) => yoneda.map f) 0 : _ ⟶ yoneda.obj Y), ?_, ?_⟩⟩
    · exact cechDiagApp_π f 0 0
    · change WidePullback.π (fun _ : Fin (0 + 1) => yoneda.map f) 0 ≫ cechDiagApp f 0 = 𝟙 _
      apply WidePullback.hom_ext
      · intro j
        rw [Fin.fin_one_eq_zero j, Category.assoc, cechDiagApp_π, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, cechDiagApp_base, Category.id_comp, WidePullback.π_arrow]
  · ext n : 1
    exact cechDiagApp_base f _

end GlobalTheory.EtC.GmStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechNerveDiagonalIsoZeroOverBaseStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechNerve_diagonal_iso_zero_over_base : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X), ∃ Δ : sch.obj Y ⟶ cech f, IsIso (Δ.app (op ⦋0⦌)) ∧ Δ ≫ cechAug f = sch.map f := by
  first | (exact @GlobalTheory.EtC.GmStep.cechDiag_spec) | (exact GlobalTheory.EtC.GmStep.cechDiag_spec) | (intros; apply GlobalTheory.EtC.GmStep.cechDiag_spec  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialTateTwistCohomologyVanishingInd
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC

namespace GlobalTheory.EtC.GmStep

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem cechC_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] {R : Type} [CommRing R] (F : Shv R) (s : ℤ)
    (k : ℕ) (j : Fin (k + 2)) (y : H R (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) F s) :
    pull R (disc.map ((cechC A A').app (op ⦋k + 1⦌))) F s (pull R (disc.map ((cech (baseHom A A')).δ j)) F s y) =
      pull R (disc.map ((cech (laurentHom A A')).δ j)) F s (pull R (disc.map ((cechC A A').app (op ⦋k⦌))) F s y) := by
  simp only [SimplicialObject.δ]
  rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, (cechC A A').naturality]

theorem aug_face (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (k : ℕ) (j : Fin (k + 2)) :
    disc.map ((cech (laurentHom A A')).δ j) ≫ augK A A' k = augK A A' (k + 1) := by
  have h := (cechAug (laurentHom A A')).naturality (SimplexCategory.δ j).op
  exact (disc.map_comp _ _).symm.trans (congrArg disc.map (h.trans (Category.comp_id _)))

theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  have := hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using this

theorem rowExact_base (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A))
    (A' : Type) [CommRing A'] [Algebra A A'] [Module.Finite A A'] (hker : RingHom.ker (algebraMap A A') ≤ nilradical A)
    (j : ℤ) (p : ℕ) : RowExact (ZMod q) (cech (baseHom A A')) (tw q j) 0 p := by
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI, hS⟩ := spec_integral_surj (algebraMap A A') hint hker
  have hB := @GlobalTheory.EtC.b4 q _ _ (baseHom A A') hI hS (isUnit_gamma q A hq) j
  refine GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic (ZMod q) (tw q j) _ (fun k s hs => GlobalTheory.T.cech_cohomology_vanishes_positive q A hA hq A' inferInstance k s j hs) (fun m hm => ?_) p
  haveI : Subsingleton (H (ZMod q) (sch.obj (Spec (CommRingCat.of A))) (tw q j) m) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) A hA (tw q j) m hm
  exact ⟨fun a b => by
    obtain ⟨a', rfl⟩ := (hB m).2 a
    obtain ⟨b', rfl⟩ := (hB m).2 b
    rw [Subsingleton.elim a' b']⟩

theorem gm_vanishing_step : ∀ (q : ℕ) [NeZero q] (n : ℤ), 2 ≤ n → (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) →
    ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) →
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
    Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  intro q _ n hn IH A _ _ hA hq i
  suffices h : ∀ x : Ht q (sp (LaurentPolynomial A)) n i, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨A', _, _, hfin, hker, hx⟩ := GlobalTheory.T.laurent_cohomology_finite_killing q A hA hq n i hn x
  haveI := hfin
  have hint : (algebraMap A A').IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨hI', hS'⟩ := spec_integral_surj _ (laurentMap_isIntegral _ hint) (laurentMap_ker _ hker)
  have hqL : IsUnit (q : LaurentPolynomial A) := by simpa using hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)
  have hB := @GlobalTheory.EtC.b4 q _ _ (laurentHom A A') hI' hS' (isUnit_gamma q _ hqL) i
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = N := ⟨n.toNat, by omega⟩
  apply (hB N).1
  rw [map_zero]
  obtain ⟨Δ, hΔ0, hΔ⟩ := GlobalTheory.T.exists_cechNerve_diagonal_iso_zero_over_base (laurentHom A A')
  refine GlobalTheory.T.etaleSpaceCohomology_eq_zero_of_simplicialRowExact (ZMod q) (tw q i) (cech (laurentHom A A')) (yoneda.obj _) Δ hΔ0 N _ ?_ ?_
  · exact (pull_comp (ZMod q) Δ (cechAug (laurentHom A A')) (tw q i) N x).symm.trans
      ((congrArg (fun g => pull (ZMod q) g (tw q i) N x) hΔ).trans hx)
  · intro p hp
    rcases (by omega : (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 0 ∨ (N : ℤ) - ((p + 1 : ℕ) : ℤ) = 1 ∨
        2 ≤ (N : ℤ) - ((p + 1 : ℕ) : ℤ)) with h0 | h1 | h2
    · rw [h0]
      exact rowExact_transfer (fun k => pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q i) 0)
        (fun k => GlobalTheory.T.laurentCechNerve_pullback_bijective_degree_zero q A hA hq A' hfin k i) (fun k j y => cechC_face A A' _ _ k j y) p
        (rowExact_base q A hA hq A' hker i p)
    · rw [h1]
      refine rowExact_transfer (fun k => rowOne A A' q i k) (fun k => GlobalTheory.T.cech_degree_zero_bijective q A hA hq A' hfin k i) (fun k j y => ?_) p
        (rowExact_base q A hA hq A' hker (i - 1) p)
      simp only [rowOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [pull_cast, (GlobalTheory.T.cup_chern_kummer_pullback_naturality q).1, cechC_face,
        ← pull_comp (ZMod q) (disc.map ((cech (laurentHom A A')).δ j)) (augK A A' k), aug_face]
    · intro y _
      haveI := GlobalTheory.T.laurentCechNerve_level_cohomology_subsingleton q N IH A hA hq A' hfin (p + 1) _ i h2 (by omega)
      exact ⟨0, by rw [map_zero]; exact Subsingleton.elim _ _⟩

end GlobalTheory.EtC.GmStep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialTateTwistCohomologyVanishingIndStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentPolynomial_tateTwistCohomology_vanishing_inductive : ∀ (q : ℕ) [NeZero q] (n : ℤ), 2 ≤ n → (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ m i : ℤ, 2 ≤ m → m < n → Subsingleton (Ht q (sp (LaurentPolynomial A)) m i)) → ∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Subsingleton (Ht q (sp (LaurentPolynomial A)) n i) := by
  first | (exact @GlobalTheory.EtC.GmStep.gm_vanishing_step) | (exact GlobalTheory.EtC.GmStep.gm_vanishing_step) | (intros; apply GlobalTheory.EtC.GmStep.gm_vanishing_step  <;> assumption)
end
