module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecTrivSqZeroExtIsPushout
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentConstPart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfSubsingletonPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeBaseChangeOfIdem
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup.IdemSplit

theorem finrank_range_baseChange_of_idem {R S M : Type} [CommRing R] [CommRing S] [Algebra R S]
    [StrongRankCondition R] [StrongRankCondition S] [AddCommGroup M] [Module R M]
    (e : M →ₗ[R] M) (he : e ∘ₗ e = e) [Module.Free R (LinearMap.range e)] :
    Module.finrank S (LinearMap.range (e.baseChange S)) =
      Module.finrank R (LinearMap.range e) := by
  let r : M →ₗ[R] LinearMap.range e := e.rangeRestrict
  let i : LinearMap.range e →ₗ[R] M := (LinearMap.range e).subtype
  have hri : r ∘ₗ i = LinearMap.id := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    change e x.1 = x.1
    rw [← hy]
    exact LinearMap.congr_fun he y
  have hir : e = i ∘ₗ r := LinearMap.ext fun _ => rfl
  have hS : r.baseChange S ∘ₗ i.baseChange S = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id]
  have hsurj : Function.Surjective (r.baseChange S) := fun x =>
    ⟨i.baseChange S x, LinearMap.congr_fun hS x⟩
  have hinj : Function.Injective (i.baseChange S) := fun x y hxy => by
    have := congrArg (r.baseChange S) hxy
    rwa [← LinearMap.comp_apply, hS, ← LinearMap.comp_apply, hS] at this
  have h2 : e.baseChange S = i.baseChange S ∘ₗ r.baseChange S := by
    rw [← LinearMap.baseChange_comp, ← hir]
  rw [h2, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hsurj),
    LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]

def quotEquivRange {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (f : A →ₐ[R] A)
    (I : Ideal A) (h : RingHom.ker f = I) : (A ⧸ I) ≃ₗ[R] LinearMap.range f.toLinearMap :=
  (Submodule.Quotient.restrictScalarsEquiv R I).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (by ext x; simp [← h]) ≪≫ₗ
    LinearMap.quotKerEquivRange f.toLinearMap

end GlobalTheory.PDivGroup.IdemSplit

namespace GlobalTheory.PDivGroup.IdemSplit

open GlobalTheory.PDivGroup.KerGrp

theorem exists_of_family {p : ℕ} {k : Type} [CommRing k] (G : PDivGroup p k)
    (v : G ⟶ G) (h₀ : ℕ) (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, HopfAlgebra k (B n)]
    [∀ n, Module.Projective k (B n)]
    (π : ∀ n, G.A n →ₐc[k] B n) (hπ : ∀ n, Function.Surjective (π n))
    (hk : ∀ n, RingHom.ker (π n) = kerIdeal (v.app n))
    (h : ∀ (n : ℕ) (q : PrimeSpectrum k), Module.rankAtStalk (B n) q = p ^ (n * h₀)) :
    ∃ (K : PDivGroup p k) (i : K ⟶ G), ∀ n : ℕ, Function.Surjective (i.app n) ∧
      RingHom.ker (i.app n) = kerIdeal (v.app n) := by
  haveI : ∀ n, IsCocomm k (B n) := fun n => isCocomm_of_surjective (π n) (hπ n)
  have hle : ∀ n, RingHom.ker (π (n + 1)) ≤ RingHom.ker ((π n).comp (G.res n)) := fun n a ha => by
    have : G.res n a ∈ RingHom.ker (π n) := by
      rw [hk, ← map_res_kerIdeal]
      rw [hk] at ha
      exact Ideal.mem_map_of_mem (G.res n : G.A (n + 1) →ₐ[k] G.A n) ha
    exact this
  let r := fun n => liftSurj (π (n + 1)) (hπ (n + 1)) ((π n).comp (G.res n)) (hle n)
  have hr : ∀ n a, r n (π (n + 1) a) = π n (G.res n a) := fun n a => liftSurj_apply ..
  let K : PDivGroup p k :=
    { height := h₀
      A := B
      finite := fun n => Module.Finite.of_surjective (π n : G.A n →ₗ[k] B n) (hπ n)
      rank_eq := h
      res := r
      res_surjective := fun n b => by
        obtain ⟨c, rfl⟩ := hπ n b
        obtain ⟨a, rfl⟩ := G.res_surjective n c
        exact ⟨_, hr n a⟩
      ker_res := fun n => by
        rw [← map_torsionIdeal (hπ (n + 1)), ← G.ker_res]
        refine le_antisymm (fun b hb => ?_) (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
        · obtain ⟨a, rfl⟩ := hπ _ b
          have h1 : G.res n a ∈ RingHom.ker (π n) := (hr n a).symm.trans hb
          rw [hk, ← map_res_kerIdeal] at h1
          obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective
            (G.res n : G.A (n + 1) →ₐ[k] G.A n) (G.res_surjective n)).1 h1
          rw [← hk] at hc
          have hc' : π (n + 1) c = 0 := hc
          have e' : G.res n c = G.res n a := e
          have h2 : a - c ∈ RingHom.ker (G.res n) := by
            rw [RingHom.mem_ker, map_sub, e', sub_self]
          have h3 : π (n + 1) a = π (n + 1) (a - c) := by rw [map_sub, hc', sub_zero]
          rw [h3]
          exact Ideal.mem_map_of_mem (π (n + 1) : G.A (n + 1) →ₐ[k] B (n + 1)) h2
        · have ha' : G.res n a = 0 := ha
          change r n (π (n + 1) a) = 0
          rw [hr, ha', map_zero] }
  exact ⟨K, ⟨π, fun n => BialgHom.ext fun a => hr n a⟩, fun n => ⟨hπ n, hk n⟩⟩

end GlobalTheory.PDivGroup.IdemSplit

namespace GlobalTheory.PDivGroup.IdemSplit

theorem baseChangeMap_zero {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (O' : Type) [CommRing O']
    [Algebra O O'] (G H : PDivGroup p O) : baseChangeMap O' (0 : G ⟶ H) = 0 := by
  have h := baseChangeMap_add O' (0 : G ⟶ H) 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

theorem bcMap_toLinearMap {O : Type} [CommRing O] (O' : Type) [CommRing O'] [Algebra O O']
    {A : Type} [CommRing A] [Bialgebra O A] (f : A →ₐc[O] A) :
    ((bcMap O' f : O' ⊗[O] A →ₐ[O'] O' ⊗[O] A)).toLinearMap =
      ((f : A →ₐ[O] A).toLinearMap).baseChange O' := by
  refine LinearMap.ext fun x => ?_
  induction x with
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul r a => exact bcMap_tmul f r a

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O]

theorem idempotent_split_of_isLocalRing (G : PDivGroup p O) (u : G ⟶ G) (hu : u ≫ u = u) :
    ∃ (H : PDivGroup p O) (i : H ⟶ G) (q : G ⟶ H), i ≫ q = 𝟙 H ∧ q ≫ i = u := by
  set v : G ⟶ G := 𝟙 G - u with hv
  have huv : u + v = 𝟙 G := add_sub_cancel u (𝟙 G)
  have h1 : u ≫ v = 0 := by rw [hv, Preadditive.comp_sub, hu, Category.comp_id, sub_self]
  have h2 : v ≫ u = 0 := by rw [hv, Preadditive.sub_comp, hu, Category.id_comp, sub_self]
  have hker : ∀ n, RingHom.ker (u.app n) = kerIdeal (v.app n) :=
    ker_app_eq_kerIdeal_of_idempotents p O G u v huv h1 h2

  let k := IsLocalRing.ResidueField O
  let uk := baseChangeMap k u
  let vk := baseChangeMap k v
  have hF : ∀ {X Y Z : PDivGroup p O} (f : X ⟶ Y) (g : Y ⟶ Z),
      baseChangeMap k (f ≫ g) = baseChangeMap k f ≫ baseChangeMap k g := fun f g =>
    (baseChangeFunctor p O k).map_comp f g
  have hI : baseChangeMap k (𝟙 G) = 𝟙 (G.baseChange k) := (baseChangeFunctor p O k).map_id G
  have hvuk : vk + uk = 𝟙 _ := by rw [← baseChangeMap_add, add_comm, huv, hI]
  have huvk : uk + vk = 𝟙 _ := by rw [add_comm]; exact hvuk
  have h1k : uk ≫ vk = 0 := by rw [← hF, h1, baseChangeMap_zero]
  have h2k : vk ≫ uk = 0 := by rw [← hF, h2, baseChangeMap_zero]
  obtain ⟨h₀, hrk⟩ := kerIdeal_finrank_eq_pow_of_idempotent p k (G.baseChange k) vk uk
    hvuk h2k h1k
  have hkerk : ∀ n, RingHom.ker (uk.app n) = kerIdeal (vk.app n) :=
    ker_app_eq_kerIdeal_of_idempotents p k (G.baseChange k) uk vk huvk h1k h2k

  let e : ∀ n, G.A n →ₗ[O] G.A n := fun n => ((u.app n : G.A n →ₐ[O] G.A n)).toLinearMap
  have he : ∀ n, e n ∘ₗ e n = e n := fun n => LinearMap.ext fun a =>
    DFunLike.congr_fun (congrArg (fun w : G ⟶ G => w.app n) hu) a
  have hproj : ∀ n, Module.Projective O (LinearMap.range (e n)) := fun n =>
    Module.Projective.of_split (LinearMap.range (e n)).subtype (e n).rangeRestrict
      (LinearMap.ext fun x => Subtype.ext (by
        obtain ⟨y, hy⟩ := x.2
        change e n x.1 = x.1
        rw [← hy]
        exact LinearMap.congr_fun (he n) y))
  have hfin : ∀ n, Module.Finite O (LinearMap.range (e n)) := fun n =>
    Module.Finite.of_surjective (e n).rangeRestrict (LinearMap.surjective_rangeRestrict _)
  have hfree : ∀ n, Module.Free O (LinearMap.range (e n)) := fun n =>
    Module.free_of_flat_of_isLocalRing
  let B := fun n => G.A n ⧸ kerIdeal (v.app n)
  have hHopf : ∀ n, (kerIdeal (v.app n)).IsHopfIdeal O := fun n =>
    GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom O _ _ (v.app n)
  let eqv : ∀ n, B n ≃ₗ[O] LinearMap.range (e n) := fun n =>
    quotEquivRange (u.app n : G.A n →ₐ[O] G.A n) _ (hker n)
  have hBproj : ∀ n, Module.Projective O (B n) := fun n =>
    Module.Projective.of_equiv (eqv n).symm
  have hrank : ∀ n, Module.finrank O (B n) = p ^ (n * h₀) := fun n => by
    rw [(eqv n).finrank_eq, ← finrank_range_baseChange_of_idem (S := k) (e n) (he n),
      ← bcMap_toLinearMap, ← (quotEquivRange _ _ (hkerk n)).finrank_eq]
    exact hrk n
  have hBrank : ∀ (n : ℕ) (q : PrimeSpectrum O), Module.rankAtStalk (B n) q = p ^ (n * h₀) :=
    fun n q => by
      haveI := Module.Free.of_equiv (eqv n).symm
      rw [Module.rankAtStalk_eq_finrank_of_free, hrank]
      rfl
  obtain ⟨K, i, hi⟩ := exists_of_family G v h₀ B
    (fun _ => Bialgebra.Quotient.mkBialgHom _) (fun _ => Ideal.Quotient.mk_surjective)
    (fun _ => Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem) hBrank
  obtain ⟨hfac, hcan⟩ := factor_closedImmersion p O K G i (fun n => (hi n).1)
  obtain ⟨q, hq⟩ := hfac G u (fun n => by rw [(hi n).2, hker n])
  have hiv : i ≫ v = 0 := by
    refine Hom.ext (funext fun n => BialgHom.ext fun b => ?_)
    have h := (kerIdeal_le_ker_iff (v.app n) (i.app n : G.A n →ₐ[O] K.A n)).1 (hi n).2.ge b
    change i.app n (v.app n b) = (1 : WithConv (G.A n →ₐc[O] K.A n)).ofConv b
    refine Eq.trans h ?_
    simp
  have hiu : i ≫ u = i := by
    have e := Preadditive.comp_add _ _ _ i u v
    rw [huv, hiv, add_zero, Category.comp_id] at e
    exact e.symm
  refine ⟨K, i, q, ?_, hq⟩
  apply hcan K
  rw [Category.assoc, hq, hiu, Category.id_comp]

end GlobalTheory.PDivGroup.IdemSplit

theorem GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
      [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O →
      ∀ (G : PDivGroup p O) (u : G ⟶ G), u ≫ u = u →
        ∃ (H : PDivGroup p O) (i : H ⟶ G) (q : G ⟶ H), i ≫ q = 𝟙 H ∧ q ≫ i = u :=
  fun p _ _ _ _ _ _ O _ _ _ _ _ _ _ G u hu =>
    GlobalTheory.PDivGroup.IdemSplit.idempotent_split_of_isLocalRing p O G u hu
end
end

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.ConnConstSplit

open IsLocalRing

theorem isLocalRing_of_subsingleton_points (O : Type) [CommRing O] [IsLocalRing O]
    [IsAlgClosed (ResidueField O)] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A]
    [Subsingleton (A →ₐ[O] ResidueField O)] (c₀ : A →ₐ[O] ResidueField O) : IsLocalRing A := by
  have key : ∀ M : Ideal A, M.IsMaximal → M = RingHom.ker c₀ := by
    intro M hM
    have hu : (M.under O).IsMaximal := Ideal.IsMaximal.under O M
    have hum : M.under O = maximalIdeal O := IsLocalRing.eq_maximalIdeal hu
    letI : Field (A ⧸ M) := Ideal.Quotient.field M
    let g : O →+* A ⧸ M := (Ideal.Quotient.mk M).comp (algebraMap O A)
    haveI : IsLocalHom g := ⟨fun x hx => by
      by_contra h
      have hxm : x ∈ M.under O := by rw [hum]; exact h
      have h0 : g x = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hxm
      exact hx.ne_zero h0⟩
    let f : ResidueField O →+* A ⧸ M := ResidueField.lift g
    letI : Algebra (ResidueField O) (A ⧸ M) := f.toAlgebra
    have hf : ∀ x : O, f (residue O x) = g x := fun x => rfl
    haveI : Algebra.IsIntegral (ResidueField O) (A ⧸ M) := ⟨fun y => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨P, hPm, hPa⟩ := Algebra.IsIntegral.isIntegral (R := O) a
      refine ⟨P.map (residue O), hPm.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have h1 : (algebraMap (ResidueField O) (A ⧸ M)).comp (residue O) = g := RingHom.ext hf
      rw [h1]
      have h2 := Polynomial.hom_eval₂ P (algebraMap O A) (Ideal.Quotient.mk M) a
      rw [hPa, map_zero] at h2
      exact h2.symm⟩
    have hsurj := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ResidueField O) (K := A ⧸ M)).2
    let e : ResidueField O ≃+* A ⧸ M := RingEquiv.ofBijective f ⟨f.injective, hsurj⟩
    let c : A →ₐ[O] ResidueField O :=
      { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk M)
        commutes' := fun x => by
          change e.symm (Ideal.Quotient.mk M (algebraMap O A x)) = algebraMap O (ResidueField O) x
          rw [RingEquiv.symm_apply_eq]
          exact (hf x).symm }
    have hc : c = c₀ := Subsingleton.elim _ _
    ext a
    rw [← hc, RingHom.mem_ker]
    change a ∈ M ↔ e.symm (Ideal.Quotient.mk M a) = 0
    rw [RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]
  haveI : Nontrivial A := c₀.toRingHom.domain_nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  exact IsLocalRing.of_unique_max_ideal ⟨M, hM, fun M' hM' => (key M' hM').trans (key M hM).symm⟩

theorem comp_add_app {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {B : Type} [CommRing B]
    [Algebra O B] {G H : PDivGroup p O} (f g : G ⟶ H) (n : ℕ) (x : G.A n →ₐ[O] B) :
    x.comp ((f + g).app n : H.A n →ₐ[O] G.A n) = WithConv.ofConv
      (WithConv.toConv (x.comp (f.app n : H.A n →ₐ[O] G.A n)) *
        WithConv.toConv (x.comp (g.app n : H.A n →ₐ[O] G.A n))) :=
  congrArg WithConv.ofConv
    (map_mul ((GlobalTheory.PDiv.ptsPush (H.A n) x).comp GlobalTheory.PDiv.toPts) (f.conv n) (g.conv n))

theorem eq_one_of_mul_self_of_pow {M : Type*} [Monoid M] {y : M} (hy : y * y = y) {m : ℕ}
    (hm : 1 ≤ m) (h : y ^ m = 1) : y = 1 := by
  have hk : ∀ k : ℕ, y ^ (k + 1) = y := by
    intro k
    induction k with
    | zero => exact pow_one y
    | succ k ih => rw [pow_succ, ih, hy]
  rw [← h, ← Nat.sub_add_cancel hm, hk]

end GlobalTheory.ConnConstSplit

namespace GlobalTheory.ConnConstSplit

open IsLocalRing

theorem exists_isSum_conn_const : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, ∃ G₁ G₂ : PDivGroup p O, IsSum G G₁ G₂ ∧ PDivLat.IsConn G₁ ∧ IsConst G₂ := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv G
  haveI := ValuationRing.of_integers v hv
  haveI := hv.isFractionRing
  haveI : IsAlgClosed (ResidueField O) :=
    GlobalTheory.isAlgClosed_residueField_of_valuationRing_of_isAlgClosed O C
  obtain ⟨u, huu, hfix, hrange⟩ := GlobalTheory.ConstPart.exists_idempotent_constPart p C v O hv G
  obtain ⟨G₂, i₂, q₂, h₂1, h₂2⟩ := GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers p C v O hv G u huu
  have h1u : (𝟙 G - u) ≫ (𝟙 G - u) = 𝟙 G - u := by
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.comp_id, huu]
    abel
  obtain ⟨G₁, i₁, q₁, h₁1, h₁2⟩ := GlobalTheory.PDivGroup.IdemSplit.idempotent_split_integers p C v O hv G (𝟙 G - u) h1u
  have hl₁ : ∀ n (b : G₁.A n), i₁.app n (q₁.app n b) = b := fun n b => by
    have h := congrArg (fun f : G₁ ⟶ G₁ => f.app n b) h₁1
    simpa using h
  have hl₂ : ∀ n (b : G₂.A n), i₂.app n (q₂.app n b) = b := fun n b => by
    have h := congrArg (fun f : G₂ ⟶ G₂ => f.app n b) h₂1
    simpa using h
  have hu₂ : ∀ n (a : G.A n), u.app n a = q₂.app n (i₂.app n a) := fun n a => by
    rw [← h₂2]; rfl
  refine ⟨G₁, G₂, ⟨i₁, i₂, q₁, q₂, h₁1, h₂1, ?_, ?_, ?_⟩, ?_, ?_⟩
  · have e1 : i₁ ≫ q₂ = i₁ ≫ ((q₁ ≫ i₁) ≫ (q₂ ≫ i₂)) ≫ q₂ := by
      simp only [Category.assoc]
      rw [h₂1, Category.comp_id, reassoc_of% h₁1]
    rw [e1, h₁2, h₂2, Preadditive.sub_comp, Category.id_comp, huu, sub_self,
      Limits.zero_comp, Limits.comp_zero]
  · have e1 : i₂ ≫ q₁ = i₂ ≫ ((q₂ ≫ i₂) ≫ (q₁ ≫ i₁)) ≫ q₁ := by
      simp only [Category.assoc]
      rw [h₁1, Category.comp_id, reassoc_of% h₂1]
    rw [e1, h₁2, h₂2, Preadditive.comp_sub, Category.comp_id, huu, sub_self,
      Limits.zero_comp, Limits.comp_zero]
  · rw [h₁2, h₂2, sub_add_cancel]
  · intro n
    let c₀ : G₁.A n →ₐ[O] ResidueField O :=
      (Algebra.ofId O (ResidueField O)).comp (Bialgebra.counitAlgHom O (G₁.A n))
    have hall : ∀ c : G₁.A n →ₐ[O] ResidueField O, c = c₀ := by
      intro c
      set x : G.A n →ₐ[O] ResidueField O := c.comp (i₁.app n : G.A n →ₐ[O] G₁.A n) with hxdef
      have hx1 : x.comp (u.app n : G.A n →ₐ[O] G.A n) = x := AlgHom.ext (hfix n x)
      have hx2 : x.comp ((q₁ ≫ i₁).app n : G.A n →ₐ[O] G.A n) = x := AlgHom.ext fun a => by
        change c (i₁.app n (q₁.app n (i₁.app n a))) = c (i₁.app n a)
        rw [hl₁]
      have hsum : q₁ ≫ i₁ + u = 𝟙 G := by rw [h₁2, sub_add_cancel]
      have hid : x.comp ((𝟙 G : G ⟶ G).app n : G.A n →ₐ[O] G.A n) = x := AlgHom.ext fun a => rfl
      have hmul := comp_add_app (q₁ ≫ i₁) u n x
      rw [hsum, hid, hx2, hx1] at hmul
      have hyy : WithConv.toConv x * WithConv.toConv x = WithConv.toConv x := by
        exact (congrArg WithConv.toConv hmul).symm
      have hx : WithConv.toConv x = 1 :=
        eq_one_of_mul_self_of_pow hyy (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
          (G.pts_pow_self n (WithConv.toConv x))
      ext b
      have hb : c b = x (q₁.app n b) := by
        change c b = c (i₁.app n (q₁.app n b)); rw [hl₁]
      rw [hb]
      have hx' : x = WithConv.ofConv (1 : WithConv (G.A n →ₐ[O] ResidueField O)) := by
        rw [← hx]
      rw [hx', AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply]
      rfl
    haveI : Subsingleton (G₁.A n →ₐ[O] ResidueField O) :=
      ⟨fun a b => (hall a).trans (hall b).symm⟩
    exact isLocalRing_of_subsingleton_points O (G₁.A n) c₀
  · intro n
    obtain ⟨N, ⟨e⟩⟩ := hrange n
    have hinj : Function.Injective (q₂.app n : G₂.A n →ₐ[O] G.A n) := fun a b h => by
      rw [← hl₂ n a, ← hl₂ n b]
      exact congrArg (i₂.app n) h
    have hrng : (u.app n : G.A n →ₐ[O] G.A n).range = (q₂.app n : G₂.A n →ₐ[O] G.A n).range := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨i₂.app n a, (hu₂ n a).symm⟩
      · rintro ⟨b, rfl⟩
        refine ⟨q₂.app n b, ?_⟩
        change u.app n (q₂.app n b) = q₂.app n b
        rw [hu₂, hl₂]
    let e' : G₂.A n ≃ₐ[O] (Fin N → O) :=
      (AlgEquiv.ofInjective _ hinj).trans ((Subalgebra.equivOfEq _ _ hrng.symm).trans e)
    have hN : N = p ^ (n * G₂.height) := by
      have h1 := G₂.rank_eq n ⟨maximalIdeal O, inferInstance⟩
      rw [Module.rankAtStalk_eq_of_equiv e'.toLinearEquiv, Module.rankAtStalk_eq_finrank_of_free,
        Module.finrank_fin_fun] at h1
      simpa using h1
    exact ⟨hN ▸ e'⟩

end GlobalTheory.ConnConstSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedOfIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfSandwichDatumBlockSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfSandwichDatumBlockSum
noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.BlockSum

def blk {R : Type} [Zero R] {m n : ℕ} (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  (fromBlocks A 0 0 B).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem blk_mulVec {R : Type} [CommRing R] {m n : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (B : Matrix (Fin n) (Fin n) R) (x : Fin m → R) (y : Fin n → R) :
    blk A B *ᵥ Fin.append x y = Fin.append (A *ᵥ x) (B *ᵥ y) := by
  unfold blk
  rw [submatrix_mulVec_equiv, fromBlocks_mulVec]
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have : Fin.append x y ∘ finSumFinEquiv = Sum.elim x y := by
      ext (a | b) <;> simp
    simp [this]
  · have : Fin.append x y ∘ finSumFinEquiv = Sum.elim x y := by
      ext (a | b) <;> simp
    simp [this]

theorem blk_mul {R : Type} [CommRing R] {m n : ℕ} (A A' : Matrix (Fin m) (Fin m) R)
    (B B' : Matrix (Fin n) (Fin n) R) : blk A B * blk A' B' = blk (A * A') (B * B') := by
  unfold blk
  rw [submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem blk_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) :
    (blk A B).map f = blk (A.map f) (B.map f) := by
  unfold blk
  rw [← submatrix_map, fromBlocks_map]
  simp

theorem blk_smul_one {R : Type} [CommRing R] {m n : ℕ} (c : R) :
    blk (c • (1 : Matrix (Fin m) (Fin m) R)) (c • (1 : Matrix (Fin n) (Fin n) R)) =
      c • (1 : Matrix (Fin (m + n)) (Fin (m + n)) R) := by
  unfold blk
  have : fromBlocks (c • (1 : Matrix (Fin m) (Fin m) R)) 0 0 (c • (1 : Matrix (Fin n) (Fin n) R))
      = c • (1 : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R) := by
    rw [← fromBlocks_one, fromBlocks_smul, smul_zero, smul_zero]
  rw [this, ← submatrix_one_equiv finSumFinEquiv.symm]
  rfl

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def sum {ε : PreTilt O p} {h₁ h₂ : ℕ} (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p]) :
    Datum ε (h₁ + h₂) ℤ_[p] where
  F := blk D₁.F D₂.F
  G := blk D₁.G D₂.G
  Ψ := blk D₁.Ψ D₂.Ψ
  Ψ' := blk D₁.Ψ' D₂.Ψ'
  ρT := Algebra.ofId _ _
  ρM := (RingHom.mapMatrix (ofPadic p O)).comp (algebraMap _ _)
  G_mul_F := by rw [blk_mul, D₁.G_mul_F, D₂.G_mul_F, blk_smul_one]
  F_eq := by rw [blk_map, blk_mul, ← D₁.F_eq, ← D₂.F_eq]
  Ψ_mul := by rw [blk_mul, D₁.Ψ_mul, D₂.Ψ_mul, blk_smul_one]
  F_act := by
    intro a
    have : ((algebraMap ℤ_[p] (Matrix (Fin (h₁ + h₂)) (Fin (h₁ + h₂)) ℤ_[p]) a).map (ofPadic p O))
        = ofPadic p O a • (1 : Matrix (Fin (h₁ + h₂)) (Fin (h₁ + h₂)) (Ainf p O)) := by
      ext1 i j
      by_cases h : i = j <;> simp [Matrix.algebraMap_matrix_apply, h]
    simp only [Algebra.ofId_apply, RingHom.comp_apply, RingHom.mapMatrix_apply, this,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

theorem sum_al {ε : PreTilt O p} {h₁ h₂ : ℕ} (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p])
    (x : Fin h₁ → O) (y : Fin h₂ → O) :
    (sum D₁ D₂).al (Fin.append x y) = Fin.append (D₁.al x) (D₂.al y) := by
  change Matrix.toLin' ((blk D₁.F D₂.F).map _) _ = _
  rw [blk_map, toLin'_apply, blk_mulVec]
  rfl

theorem sum_bb {ε : PreTilt O p} {h₁ h₂ : ℕ} (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p])
    (x : Fin h₁ → O) (y : Fin h₂ → O) :
    (sum D₁ D₂).bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y) := by
  change Matrix.toLin' ((blk D₁.G D₂.G).map _) _ = _
  rw [blk_map, toLin'_apply, blk_mulVec]
  rfl

theorem exists_sum_datum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (h₁ h₂ : ℕ) (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p]), ∃ D : Datum ε (h₁ + h₂) ℤ_[p], (∀ x y, D.al (Fin.append x y) = Fin.append (D₁.al x) (D₂.al y)) ∧ ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε h₁ h₂ D₁ D₂
  exact ⟨sum D₁ D₂, sum_al D₁ D₂, sum_bb D₁ D₂⟩

end GlobalTheory.BlockSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfSandwichDatumBlockSumStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainfSandwichDatum_blockSum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (h₁ h₂ : ℕ) (D₁ : Datum ε h₁ ℤ_[p]) (D₂ : Datum ε h₂ ℤ_[p]), ∃ D : Datum ε (h₁ + h₂) ℤ_[p], (∀ x y, D.al (Fin.append x y) = Fin.append (D₁.al x) (D₂.al y)) ∧ ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y) := by
  first | exact @GlobalTheory.BlockSum.exists_sum_datum | exact GlobalTheory.BlockSum.exists_sum_datum | (intros; apply GlobalTheory.BlockSum.exists_sum_datum <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SumDatum

section Linear

variable {R X X₁ X₂ : Type*} [Semiring R] [AddCommMonoid X] [AddCommMonoid X₁] [AddCommMonoid X₂]
  [Module R X] [Module R X₁] [Module R X₂]

def splitEquiv (a₁ : X₁ →ₗ[R] X) (a₂ : X₂ →ₗ[R] X) (b₁ : X →ₗ[R] X₁) (b₂ : X →ₗ[R] X₂)
    (h₁ : ∀ x, b₁ (a₁ x) = x) (h₂ : ∀ x, b₂ (a₂ x) = x) (h₁₂ : ∀ x, b₂ (a₁ x) = 0)
    (h₂₁ : ∀ x, b₁ (a₂ x) = 0) (h : ∀ x, a₁ (b₁ x) + a₂ (b₂ x) = x) : X ≃ₗ[R] X₁ × X₂ :=
  LinearEquiv.ofLinear (b₁.prod b₂) (a₁.coprod a₂)
    (LinearMap.ext fun ⟨x, y⟩ => by simp [h₁, h₂, h₁₂, h₂₁])
    (LinearMap.ext fun x => by simp [h])

end Linear

section Fin

variable {R : Type*} [Semiring R]


variable (R) in
def appendEquiv (m n : ℕ) : ((Fin m → R) × (Fin n → R)) ≃ₗ[R] (Fin (m + n) → R) where
  toFun x := Fin.append x.1 x.2
  invFun z := (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j))
  map_add' x y := by
    funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  map_smul' c x := by
    funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp
  left_inv x := by simp
  right_inv z := Fin.append_castAdd_natAdd

theorem appendEquiv_apply {m n : ℕ} (x : (Fin m → R) × (Fin n → R)) :
    appendEquiv R m n x = Fin.append x.1 x.2 := rfl

theorem appendEquiv_symm_apply {m n : ℕ} (z : Fin (m + n) → R) :
    (appendEquiv R m n).symm z = (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j)) :=
  rfl

theorem append_eq_zero_iff {m n : ℕ} (x : Fin m → R) (y : Fin n → R) :
    Fin.append x y = 0 ↔ x = 0 ∧ y = 0 :=
  ((appendEquiv R m n).map_eq_zero_iff (x := (x, y))).trans Prod.mk_eq_zero

theorem comp_append {α β : Type*} {m n : ℕ} (f : α → β) (x : Fin m → α) (y : Fin n → α) :
    (fun i => f (Fin.append x y i)) = Fin.append (fun i => f (x i)) (fun j => f (y j)) := by
  funext i; refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp

theorem single_castAdd {m n : ℕ} (i : Fin m) :
    (Pi.single (Fin.castAdd n i) 1 : Fin (m + n) → R) = Fin.append (Pi.single i 1) 0 := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [Pi.single_apply]
  · have hne : Fin.natAdd m j ≠ Fin.castAdd n i := fun h' => by
      have h'' := congrArg Fin.val h'
      simp only [Fin.val_natAdd, Fin.val_castAdd] at h''
      have := i.isLt
      omega
    simp [Pi.single_apply, hne]

theorem single_natAdd {m n : ℕ} (j : Fin n) :
    (Pi.single (Fin.natAdd m j) 1 : Fin (m + n) → R) = Fin.append 0 (Pi.single j 1) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k
  · have hne : Fin.castAdd n i ≠ Fin.natAdd m j := fun h' => by
      have h'' := congrArg Fin.val h'
      simp only [Fin.val_natAdd, Fin.val_castAdd] at h''
      have := i.isLt
      omega
    simp [Pi.single_apply, hne]
  · simp [Pi.single_apply]

end Fin

end GlobalTheory.SumDatum

namespace GlobalTheory.SumDatum

section Groups

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {G G₁ G₂ : PDivGroup p O}
  (i₁ : G₁ ⟶ G) (i₂ : G₂ ⟶ G) (q₁ : G ⟶ G₁) (q₂ : G ⟶ G₂)


include i₁ i₂ in
theorem exists_tateSplit (h₁ : i₁ ≫ q₁ = 𝟙 _) (h₂ : i₂ ≫ q₂ = 𝟙 _) (h₁₂ : i₁ ≫ q₂ = 0)
    (h₂₁ : i₂ ≫ q₁ = 0) (h : q₁ ≫ i₁ + q₂ ≫ i₂ = 𝟙 _) :
    ∃ T : G.Tate ≃ₗ[ℤ_[p]] G₁.Tate × G₂.Tate,
      (∀ t, T t = (tateMap G G₁ O q₁ t, tateMap G G₂ O q₂ t)) ∧
      ∀ a b, T.symm (a, b) = tateMap G₁ G O i₁ a + tateMap G₂ G O i₂ b :=
  ⟨splitEquiv (tateMap G₁ G O i₁) (tateMap G₂ G O i₂) (tateMap G G₁ O q₁) (tateMap G G₂ O q₂)
    (fun x => by rw [← tateMap_comp, h₁, tateMap_id])
    (fun x => by rw [← tateMap_comp, h₂, tateMap_id])
    (fun x => by rw [← tateMap_comp, h₁₂, map_zero, LinearMap.zero_apply])
    (fun x => by rw [← tateMap_comp, h₂₁, map_zero, LinearMap.zero_apply])
    (fun x => by
      have := LinearMap.congr_fun (congrArg (tateMap G G O) h) x
      rwa [map_add, LinearMap.add_apply, tateMap_comp, tateMap_comp, tateMap_id] at this),
    fun _ => rfl, fun _ _ => rfl⟩


include i₁ i₂ in
theorem exists_lieSplit (h₁ : i₁ ≫ q₁ = 𝟙 _) (h₂ : i₂ ≫ q₂ = 𝟙 _) (h₁₂ : i₁ ≫ q₂ = 0)
    (h₂₁ : i₂ ≫ q₁ = 0) (h : q₁ ≫ i₁ + q₂ ≫ i₂ = 𝟙 _) :
    ∃ L : G.Lie ≃ₗ[O] G₁.Lie × G₂.Lie, ∀ x, L x = (lieMap G G₁ q₁ x, lieMap G G₂ q₂ x) :=
  ⟨splitEquiv (lieMap G₁ G i₁) (lieMap G₂ G i₂) (lieMap G G₁ q₁) (lieMap G G₂ q₂)
    (fun x => by
      have := LinearMap.congr_fun (lieMap_comp i₁ q₁) x
      rw [h₁, lieMap_id] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (lieMap_comp i₂ q₂) x
      rw [h₂, lieMap_id] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (lieMap_comp i₁ q₂) x
      rw [h₁₂, map_zero] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (lieMap_comp i₂ q₁) x
      rw [h₂₁, map_zero] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (congrArg (lieMap G G) h) x
      rw [map_add (f := _), lieMap_comp, lieMap_comp, lieMap_id] at this; exact this),
    fun _ => rfl⟩


include i₁ i₂ in
theorem exists_omegaDualSplit (h₁ : i₁ ≫ q₁ = 𝟙 _) (h₂ : i₂ ≫ q₂ = 𝟙 _) (h₁₂ : i₁ ≫ q₂ = 0)
    (h₂₁ : i₂ ≫ q₁ = 0) (h : q₁ ≫ i₁ + q₂ ≫ i₂ = 𝟙 _) :
    ∃ W : G.dual.omega ≃ₗ[O] G₁.dual.omega × G₂.dual.omega,
      ∀ w, W w = (omegaDualMap G G₁ q₁ w, omegaDualMap G G₂ q₂ w) :=
  ⟨splitEquiv (omegaDualMap G₁ G i₁) (omegaDualMap G₂ G i₂) (omegaDualMap G G₁ q₁)
    (omegaDualMap G G₂ q₂)
    (fun x => by
      have := LinearMap.congr_fun (omegaDualMap_comp i₁ q₁) x
      rw [h₁, omegaDualMap_id] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (omegaDualMap_comp i₂ q₂) x
      rw [h₂, omegaDualMap_id] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (omegaDualMap_comp i₁ q₂) x
      rw [h₁₂, map_zero] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (omegaDualMap_comp i₂ q₁) x
      rw [h₂₁, map_zero] at this; exact this.symm)
    (fun x => by
      have := LinearMap.congr_fun (congrArg (omegaDualMap G G) h) x
      rw [map_add (f := _), omegaDualMap_comp, omegaDualMap_comp, omegaDualMap_id] at this; exact this),
    fun _ => rfl⟩

end Groups

section Datum

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} {h₁ h₂ : ℕ}
  {D : Datum ε (h₁ + h₂) ℤ_[p]} {D₁ : Datum ε h₁ ℤ_[p]} {D₂ : Datum ε h₂ ℤ_[p]}

theorem append_mem_fil_iff (hb : ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y))
    (x : Fin h₁ → O) (y : Fin h₂ → O) : Fin.append x y ∈ D.Fil ↔ x ∈ D₁.Fil ∧ y ∈ D₂.Fil := by
  simp only [Datum.Fil, LinearMap.mem_ker, hb, append_eq_zero_iff]

theorem split_mem_fil (hb : ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y))
    (z : Fin (h₁ + h₂) → O) (hz : z ∈ D.Fil) :
    (fun i => z (Fin.castAdd h₂ i)) ∈ D₁.Fil ∧ (fun j => z (Fin.natAdd h₁ j)) ∈ D₂.Fil :=
  (append_mem_fil_iff hb _ _).1 (by rwa [Fin.append_castAdd_natAdd])

theorem exists_filSplit (hb : ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y)) :
    ∃ F : D.Fil ≃ₗ[O] D₁.Fil × D₂.Fil,
      ∀ u v, (F.symm (u, v) : Fin (h₁ + h₂) → O) = Fin.append u.1 v.1 :=
  ⟨{ toFun := fun z => (⟨_, (split_mem_fil hb z.1 z.2).1⟩, ⟨_, (split_mem_fil hb z.1 z.2).2⟩)
     invFun := fun w => ⟨Fin.append w.1.1 w.2.1, (append_mem_fil_iff hb _ _).2 ⟨w.1.2, w.2.2⟩⟩
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl
     left_inv := fun z => Subtype.ext Fin.append_castAdd_natAdd
     right_inv := fun w => by ext i <;> simp }, fun _ _ => rfl⟩


variable (D₁ D₂) in
def quotProj : (Fin (h₁ + h₂) → O) →ₗ[O] ((Fin h₁ → O) ⧸ D₁.Fil) × ((Fin h₂ → O) ⧸ D₂.Fil) :=
  (D₁.Fil.mkQ.prodMap D₂.Fil.mkQ) ∘ₗ (appendEquiv O h₁ h₂).symm.toLinearMap

theorem exists_quotSplit (hb : ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y)) :
    ∃ Q : ((Fin (h₁ + h₂) → O) ⧸ D.Fil) ≃ₗ[O] ((Fin h₁ → O) ⧸ D₁.Fil) × ((Fin h₂ → O) ⧸ D₂.Fil),
      ∀ z, Q (D.Fil.mkQ z) = (D₁.Fil.mkQ (fun i => z (Fin.castAdd h₂ i)),
        D₂.Fil.mkQ (fun j => z (Fin.natAdd h₁ j))) := by
  have hker : D.Fil = LinearMap.ker (quotProj D₁ D₂) := by
    ext z
    rw [LinearMap.mem_ker]
    conv_lhs => rw [← Fin.append_castAdd_natAdd (f := z)]
    rw [append_mem_fil_iff hb]
    simp [quotProj, appendEquiv_symm_apply, Submodule.Quotient.mk_eq_zero]
  have hs : Function.Surjective (quotProj D₁ D₂) := by
    rintro ⟨u, v⟩
    obtain ⟨a, rfl⟩ := D₁.Fil.mkQ_surjective u
    obtain ⟨b, rfl⟩ := D₂.Fil.mkQ_surjective v
    exact ⟨Fin.append a b, by simp [quotProj, appendEquiv_symm_apply]⟩
  exact ⟨(D.Fil.quotEquivOfEq _ hker).trans ((quotProj D₁ D₂).quotKerEquivOfSurjective hs),
    fun z => rfl⟩

theorem bQuot_symm (hb : ∀ x y, D.bb (Fin.append x y) = Fin.append (D₁.bb x) (D₂.bb y))
    (Q : ((Fin (h₁ + h₂) → O) ⧸ D.Fil) ≃ₗ[O] ((Fin h₁ → O) ⧸ D₁.Fil) × ((Fin h₂ → O) ⧸ D₂.Fil))
    (hQ : ∀ z, Q (D.Fil.mkQ z) = (D₁.Fil.mkQ (fun i => z (Fin.castAdd h₂ i)),
        D₂.Fil.mkQ (fun j => z (Fin.natAdd h₁ j)))) (u) :
    bQuot D (Q.symm u) = Fin.append (bQuot D₁ u.1) (bQuot D₂ u.2) := by
  obtain ⟨q, rfl⟩ := Q.surjective u
  obtain ⟨z, rfl⟩ := D.Fil.mkQ_surjective q
  rw [LinearEquiv.symm_apply_apply, hQ]
  simp only [bQuot, Submodule.mkQ_apply, Submodule.liftQ_apply]
  conv_lhs => rw [← Fin.append_castAdd_natAdd (f := z)]
  exact hb _ _

end Datum

end GlobalTheory.SumDatum

namespace GlobalTheory.SumDatum

section Pairing

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] {ε : PreTilt O p}
  (hε : IsPrimitiveSystem ε) {h₁ h₂ : ℕ} {G G₁ G₂ : PDivGroup p O}

theorem pairingO_append (i₁ : G₁ ⟶ G) (i₂ : G₂ ⟶ G)
    (e : G.Tate ≃ₗ[ℤ_[p]] (Fin (h₁ + h₂) → ℤ_[p])) (e₁ : G₁.Tate ≃ₗ[ℤ_[p]] (Fin h₁ → ℤ_[p]))
    (e₂ : G₂.Tate ≃ₗ[ℤ_[p]] (Fin h₂ → ℤ_[p]))
    (he : ∀ a b, e.symm (Fin.append a b) = tateMap G₁ G O i₁ (e₁.symm a) +
      tateMap G₂ G O i₂ (e₂.symm b))
    (y₁ : Fin h₁ → O) (y₂ : Fin h₂ → O) (χ : G.dual.Tate) :
    pairingO hε e (Fin.append y₁ y₂) χ =
      pairingO hε e₁ y₁ (tateMap _ _ O (dualHom G₁ G i₁) χ) +
        pairingO hε e₂ y₂ (tateMap _ _ O (dualHom G₂ G i₂) χ) := by
  have hp1 : ∀ i : Fin h₁, epsPairing hε G (e.symm (Pi.single (Fin.castAdd h₂ i) 1)) χ =
      epsPairing hε G₁ (e₁.symm (Pi.single i 1)) (tateMap _ _ O (dualHom G₁ G i₁) χ) := by
    intro i
    rw [single_castAdd, he]
    simp [epsPairing, pairing_tateMap]
  have hp2 : ∀ j : Fin h₂, epsPairing hε G (e.symm (Pi.single (Fin.natAdd h₁ j) 1)) χ =
      epsPairing hε G₂ (e₂.symm (Pi.single j 1)) (tateMap _ _ O (dualHom G₂ G i₂) χ) := by
    intro j
    rw [single_natAdd, he]
    simp [epsPairing, pairing_tateMap]
  simp only [pairingO, Fin.sum_univ_add, Fin.append_left, Fin.append_right, hp1, hp2]

end Pairing

end GlobalTheory.SumDatum

namespace GlobalTheory.SumDatum

theorem integrallyClosed_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsIntegrallyClosedIn O C :=
  isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 h)⟩

theorem hasDatum_of_isSum : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G G₁ G₂ : PDivGroup p O,
      IsSum G G₁ G₂ → HasDatum hε G₁ → HasDatum hε G₂ → HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G G₁ G₂ ⟨i₁, i₂, q₁, q₂, h₁, h₂, h₁₂, h₂₁, h⟩
    ⟨D₁, e₁, fil₁, lie₁, hal₁, hb₁⟩ ⟨D₂, e₂, fil₂, lie₂, hal₂, hb₂⟩
  haveI := integrallyClosed_of_integers hv
  obtain ⟨D, hal, hbb⟩ := GlobalTheory.T.exists_ainfSandwichDatum_blockSum p C v O hv ε hε _ _ D₁ D₂
  obtain ⟨T, hT, hTs⟩ := exists_tateSplit i₁ i₂ q₁ q₂ h₁ h₂ h₁₂ h₂₁ h
  obtain ⟨L, hL⟩ := exists_lieSplit i₁ i₂ q₁ q₂ h₁ h₂ h₁₂ h₂₁ h
  obtain ⟨W, hW⟩ := exists_omegaDualSplit i₁ i₂ q₁ q₂ h₁ h₂ h₁₂ h₂₁ h
  obtain ⟨F, hF⟩ := exists_filSplit hbb
  obtain ⟨Q, hQ⟩ := exists_quotSplit hbb
  let e : G.Tate ≃ₗ[ℤ_[p]] (Fin (G₁.height + G₂.height) → ℤ_[p]) :=
    T ≪≫ₗ e₁.prodCongr e₂ ≪≫ₗ appendEquiv ℤ_[p] _ _
  have he : ∀ t, e t = Fin.append (e₁ (tateMap G G₁ O q₁ t)) (e₂ (tateMap G G₂ O q₂ t)) :=
    fun t => by simp [e, hT, appendEquiv_apply]
  have hes : ∀ a b, e.symm (Fin.append a b) = tateMap G₁ G O i₁ (e₁.symm a) +
      tateMap G₂ G O i₂ (e₂.symm b) := fun a b => by
    have : (appendEquiv ℤ_[p] G₁.height G₂.height).symm (Fin.append a b) = (a, b) :=
      (appendEquiv ℤ_[p] G₁.height G₂.height).symm_apply_apply (a, b)
    simp [e, this, hTs]
  have hh : G.height = G₁.height + G₂.height := by
    rw [← G.finrank_tate C, e.finrank_eq, Module.finrank_fin_fun]
  have key : ∃ (D : Datum ε (G₁.height + G₂.height) ℤ_[p])
      (e : G.Tate ≃ₗ[ℤ_[p]] (Fin (G₁.height + G₂.height) → ℤ_[p]))
      (fil : G.dual.omega ≃ₗ[O] D.Fil)
      (lie : ((Fin (G₁.height + G₂.height) → O) ⧸ D.Fil) ≃ₗ[O] G.Lie),
      (∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin (G₁.height + G₂.height) → O)) ∧
        ∀ (x : G.Lie) (χ : G.dual.Tate), pairingO hε e (bQuot D (lie.symm x)) χ = x (dlog G χ) := by
    refine ⟨D, e, W ≪≫ₗ fil₁.prodCongr fil₂ ≪≫ₗ F.symm, Q ≪≫ₗ lie₁.prodCongr lie₂ ≪≫ₗ L.symm,
      fun t => ?_, fun x χ => ?_⟩
    · have ht : toO e t = Fin.append (toO e₁ (tateMap G G₁ O q₁ t))
          (toO e₂ (tateMap G G₂ O q₂ t)) := by
        show (fun i => padicToO p O (e t i)) = _
        rw [he]
        exact comp_append _ _ _
      rw [ht, hal, hal₁, hal₂, hodgeTate_tateMap, hodgeTate_tateMap]
      show _ = ((F.symm ((fil₁.prodCongr fil₂) (W (hodgeTate G t))) : D.Fil) :
        Fin (G₁.height + G₂.height) → O)
      rw [hW, LinearEquiv.prodCongr_apply, hF]
    · have hx : (Q ≪≫ₗ lie₁.prodCongr lie₂ ≪≫ₗ L.symm).symm x =
          Q.symm (lie₁.symm (lieMap G G₁ q₁ x), lie₂.symm (lieMap G G₂ q₂ x)) := by
        simp [hL]
      rw [hx, bQuot_symm hbb Q hQ, pairingO_append hε i₁ i₂ e e₁ e₂ hes, hb₁, hb₂,
        lieMap_apply, lieMap_apply, dlog_tateMap, dlog_tateMap, ← map_add]
      have hw := LinearMap.congr_fun (congrArg (omegaMap G G) h) (dlog G χ)
      rw [map_add (f := _), omegaMap_comp, omegaMap_comp, omegaMap_id] at hw
      exact congrArg x hw
  unfold HasDatum
  rw [hh]
  exact key

end GlobalTheory.SumDatum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTransport
noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def omegaDualCongr {G H : PDivGroup p O} (f : G ≅ H) : G.dual.omega ≃ₗ[O] H.dual.omega :=
  LinearEquiv.ofLinearMap (omegaDualMap G H f.hom) (omegaDualMap H G f.inv)
    (by rw [← omegaDualMap_comp, f.inv_hom_id, omegaDualMap_id])
    (by rw [← omegaDualMap_comp, f.hom_inv_id, omegaDualMap_id])

def lieCongr {G H : PDivGroup p O} (f : G ≅ H) : G.Lie ≃ₗ[O] H.Lie :=
  LinearEquiv.ofLinearMap (lieMap G H f.hom) (lieMap H G f.inv)
    (by rw [← lieMap_comp, f.inv_hom_id, lieMap_id])
    (by rw [← lieMap_comp, f.hom_inv_id, lieMap_id])

theorem datum_transport [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) {h : ℕ}
    {G H : PDivGroup p O} (f : G ≅ H) (D : Datum ε h ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (fil : G.dual.omega ≃ₗ[O] D.Fil) (lie : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] G.Lie)
    (h1 : ∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin h → O))
    (h2 : ∀ (x : G.Lie) (χ : G.dual.Tate), pairingO hε e (bQuot D (lie.symm x)) χ = x (dlog G χ)) :
    ∃ (e' : H.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
      (fil' : H.dual.omega ≃ₗ[O] D.Fil) (lie' : ((Fin h → O) ⧸ D.Fil) ≃ₗ[O] H.Lie),
      (∀ t, D.al (toO e' t) = (fil' (hodgeTate H t) : Fin h → O)) ∧
        ∀ (x : H.Lie) (χ : H.dual.Tate), pairingO hε e' (bQuot D (lie'.symm x)) χ = x (dlog H χ) := by
  refine ⟨(tateCongr O f).symm ≪≫ₗ e, (omegaDualCongr f).symm ≪≫ₗ fil, lie ≪≫ₗ lieCongr f,
    fun s => ?_, fun x χ => ?_⟩
  · have := h1 (tateMap H G O f.inv s)
    change D.al (toO e (tateMap H G O f.inv s)) =
      (fil (omegaDualMap H G f.inv (hodgeTate H s)) : Fin h → O)
    rw [this, ← hodgeTate_tateMap]
  · set χ' := tateMap _ _ O (dualHom G H f.hom) χ
    have hp : ∀ y, pairingO hε ((tateCongr O f).symm ≪≫ₗ e) y χ = pairingO hε e y χ' := by
      intro y
      simp only [pairingO, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      simp only [epsPairing, tateCongr_apply, pairing_tateMap, χ']
    have hl : (lie ≪≫ₗ lieCongr f).symm x = lie.symm (lieMap H G f.inv x) := rfl
    rw [hp, hl, h2, lieMap_apply, dlog_tateMap, ← LinearMap.comp_apply (omegaMap H G f.inv),
      ← omegaMap_comp, f.inv_hom_id, omegaMap_id, LinearMap.id_apply]

theorem hasDatum_of_iso : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G H : PDivGroup p O,
      Nonempty (G ≅ H) → HasDatum hε G → HasDatum hε H := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G H ⟨f⟩ hG
  haveI : IsIntegrallyClosedIn O C :=
    isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun hx => hv.exists_of_le_one
      (hv.isIntegral_iff_v_le_one.1 hx)⟩
  have hh : G.height = H.height := by
    rw [← PDivGroup.finrank_tate G C, ← PDivGroup.finrank_tate H C]
    exact (tateCongr O f).finrank_eq
  obtain ⟨D, e, fil, lie, h1, h2⟩ := hG
  unfold HasDatum
  rw [← hh]
  obtain ⟨e', fil', lie', h1', h2'⟩ := datum_transport hε f D e fil lie h1 h2
  exact ⟨D, e', fil', lie', h1', h2'⟩

end GlobalTheory.PDivLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupDatumOfConnectedDualConnected
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem isConn_of_retract {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Nontrivial O] {G H : PDivGroup p O}
    (f : H ⟶ G) (r : G ⟶ H) (h : f ≫ r = 𝟙 H) (hG : GlobalTheory.PDivLat.IsConn G) : GlobalTheory.PDivLat.IsConn H := by
  intro n
  have hs : Function.Surjective (f.app n) := fun a => ⟨r.app n a, by
    have := congrArg (fun g => Hom.app g n) h
    exact DFunLike.congr_fun this a⟩
  haveI : Nontrivial (H.A n) :=
    (Bialgebra.counitAlgHom O (H.A n) : H.A n →+* O).domain_nontrivial
  haveI := hG n
  exact IsLocalRing.of_surjective' (f.app n : G.A n →+* H.A n) hs

theorem hasDatum_of_conn_dual_conn : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, GlobalTheory.PDivLat.IsConn G → GlobalTheory.PDivLat.IsConn G.dual → HasDatum hε G) → ∀ G : PDivGroup p O, HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε hyp G
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨G₁, G₂, hs, hc₁, hk₂⟩ := GlobalTheory.ConnConstSplit.exists_isSum_conn_const p C v O hv G
  obtain ⟨H₁, H₂, hs', hcH, hkH⟩ := GlobalTheory.ConnConstSplit.exists_isSum_conn_const p C v O hv G₁.dual
  obtain ⟨i₁, -, q₁, -, e₁, -⟩ := id hs'
  have hD : GlobalTheory.PDivLat.IsConn H₁.dual :=
    isConn_of_retract (dualHom _ _ q₁ ≫ G₁.bidual.inv) (G₁.bidual.hom ≫ dualHom _ _ i₁)
      (by rw [Category.assoc, Iso.inv_hom_id_assoc, ← dualHom_comp, e₁, dualHom_id]) hc₁
  have dD := GlobalTheory.SumDatum.hasDatum_of_isSum p C v O hv ε hε _ _ _ hs' (hyp H₁ hcH hD)
    (GlobalTheory.PDivLat.hasDatum_of_isConst p C v O hv ε hε H₂ hkH)
  have d₁ := GlobalTheory.PDivLat.hasDatum_of_iso p C v O hv ε hε _ _ ⟨G₁.bidual.symm⟩
    (GlobalTheory.DualDatum.hasDatum_dual p C v O hv ε hε _ dD)
  exact GlobalTheory.SumDatum.hasDatum_of_isSum p C v O hv ε hε G G₁ G₂ hs d₁ (GlobalTheory.PDivLat.hasDatum_of_isConst p C v O hv ε hε G₂ hk₂)

end GlobalTheory.PDivLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupDatumOfConnectedDualConnectedStatement
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivisibleGroup_datum_of_connected_dual_connected : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ G : PDivGroup p O, GlobalTheory.PDivLat.IsConn G → GlobalTheory.PDivLat.IsConn G.dual → HasDatum hε G) → ∀ G : PDivGroup p O, HasDatum hε G := by
  first | exact @GlobalTheory.PDivLat.hasDatum_of_conn_dual_conn | exact GlobalTheory.PDivLat.hasDatum_of_conn_dual_conn | (intros; apply GlobalTheory.PDivLat.hasDatum_of_conn_dual_conn <;> assumption)
end
