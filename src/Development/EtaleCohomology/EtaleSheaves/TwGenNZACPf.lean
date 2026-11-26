module

public import Development.EtaleCohomology.EtaleSheaves.HensCut
public import Development.EtaleCohomology.EtaleSheaves.TorEtPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.TwGenNZACPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.TwGenNZACPf

section Field
variable {q : ℕ} [NeZero q] {L : Type} [Field L]

theorem prim_isPrimitiveRoot (z : Prim q L) : IsPrimitiveRoot z.1 q := by
  have : NeZero (q : L) := ⟨z.2.1.ne_zero⟩
  have h := z.2.2
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] at h
  exact Polynomial.isRoot_cyclotomic_iff.1 h


open Classical in
def lg (q : ℕ) (z x : L) : ZMod q := if h : ∃ n : ℕ, z ^ n = x then (h.choose : ZMod q) else 0

theorem lg_pow {z : L} (hz : IsPrimitiveRoot z q) (n : ℕ) : lg q z (z ^ n) = n := by
  have h : ∃ m : ℕ, z ^ m = z ^ n := ⟨n, rfl⟩
  unfold lg
  rw [dite_eq_left h, ZMod.natCast_eq_natCast_iff]
  have h2 := h.choose_spec
  have h3 := ((hz.isOfFinOrder (NeZero.ne q)).pow_eq_pow_iff_modEq).1 h2
  rwa [← hz.eq_orderOf] at h3


open Classical in
def fv (q : ℕ) (i : ℤ) (z x : L) : ZMod q :=
  if h : IsUnit (lg q z x) then ((h.unit ^ i : (ZMod q)ˣ) : ZMod q) else 0

theorem fv_rel (i : ℤ) (z : Prim q L) (ζ ξ : Prim q L) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    fv q i z.1 ξ.1 = ((a ^ i : (ZMod q)ˣ) : ZMod q) * fv q i z.1 ζ.1 := by
  have hz := prim_isPrimitiveRoot z
  obtain ⟨m, -, hm⟩ := hz.eq_pow_of_pow_eq_one (prim_isPrimitiveRoot ζ).pow_eq_one
  have hl : lg q z.1 ξ.1 = lg q z.1 ζ.1 * a := by
    rw [h, ← hm, ← pow_mul, lg_pow hz, lg_pow hz]
    push_cast
    rw [ZMod.natCast_zmod_val]
  unfold fv
  by_cases hu : IsUnit (lg q z.1 ζ.1)
  · have hu' : IsUnit (lg q z.1 ξ.1) := hl ▸ hu.mul a.isUnit
    rw [dite_eq_left hu, dite_eq_left hu']
    have : hu'.unit = hu.unit * a := Units.ext (by simp [hl])
    rw [this, mul_zpow, Units.val_mul, mul_comm]
  · have hu' : ¬ IsUnit (lg q z.1 ξ.1) := by
      rw [hl]; exact fun h' => hu ((Units.isUnit_mul_units _ a).1 h')
    rw [dite_eq_right hu, dite_eq_right hu', mul_zero]

theorem fv_self (i : ℤ) (z : Prim q L) : fv q i z.1 z.1 = 1 := by
  have hl : lg q z.1 z.1 = 1 := by
    have := lg_pow (prim_isPrimitiveRoot z) 1
    rw [pow_one] at this
    rw [this, Nat.cast_one]
  unfold fv
  have hu : IsUnit (lg q z.1 z.1) := hl ▸ isUnit_one
  rw [dite_eq_left hu]
  have : hu.unit = 1 := Units.ext (by simp [hl])
  rw [this, one_zpow, Units.val_one]

def lin (i : ℤ) (z : L) : (Prim q L →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (fun ξ : Prim q L => ULift.up (fv q i z ξ.1))

theorem lin_rel (i : ℤ) (z : Prim q L) : twRel q i L ≤ LinearMap.ker (lin i z.1) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, lin, Finsupp.linearCombination_single]
  rw [sub_eq_zero]
  apply ULift.ext
  simp [fv_rel i z ζ ξ a h]

theorem field_nz (i : ℤ) (z : Prim q L) (c : ZMod q)
    (h : c.val • (Submodule.Quotient.mk (Finsupp.single z 1) : (Prim q L →₀ ULift.{1} (ZMod q)) ⧸ twRel q i L) = 0) :
    c = 0 := by
  have h2 := congrArg ((twRel q i L).liftQ (lin i z.1) (lin_rel i z)) h
  rw [map_nsmul, Submodule.liftQ_apply, map_zero, lin, Finsupp.linearCombination_single, fv_self] at h2
  rw [one_smul] at h2
  have h3 := congrArg AddEquiv.ulift h2
  rw [map_nsmul, map_zero] at h3
  change c.val • (1 : ZMod q) = 0 at h3
  rwa [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] at h3

end Field

theorem ring_nz {q : ℕ} [NeZero q] (i : ℤ) {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (c : ZMod q)
    (h : c.val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) = 0) :
    c = 0 := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let _ := Ideal.Quotient.field M
  apply field_nz i (ζ.map (Ideal.Quotient.mk M)) c
  have h2 := congrArg (Submodule.mapQ _ _ (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
    (Prim.map (Ideal.Quotient.mk M))) (twRel_le q i (Ideal.Quotient.mk M))) h
  rw [map_nsmul, map_zero, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] at h2
  exact h2

theorem gamma_nontrivial (V : Scheme.{0}) [Nonempty V] : Nontrivial Γ(V, ⊤) := by
  obtain ⟨y⟩ := ‹Nonempty V›
  exact RingHom.domain_nontrivial (V.presheaf.germ ⊤ y trivial).hom

theorem TwGenNZAC_of : LateralTheory.E.LCBijPf.TwGenNZAC := by
  intro q _ i K _ _ ζ c h
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q i
  let U : Scheme.{0} := Spec (CommRingCat.of K)
  let m : P.obj (op U) := Submodule.Quotient.mk (Finsupp.single (gam ζ) 1)
  have h1 : ((toSheafify Scheme.etaleTopology P).app (op U)).hom (c.val • m) =
      ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0 := by
    rw [map_nsmul, map_zero]
    exact h
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c.val • m) 0 h1
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  obtain ⟨p⟩ : Nonempty U := inferInstance
  obtain ⟨j, y, -⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 p
  have hj := hle _ _ (Presieve.ofArrows.mk j)
  have : Nonempty (𝒰.X j) := ⟨y⟩
  have : Nontrivial (Scheme.Γ.obj (op (𝒰.X j))) := gamma_nontrivial (𝒰.X j)
  apply ring_nz i ((gam ζ).map (Scheme.Γ.map (𝒰.f j).op).hom) c
  change (P.map (𝒰.f j).op).hom (c.val • m) = (P.map (𝒰.f j).op).hom 0 at hj
  rw [map_nsmul, map_zero] at hj
  change c.val • Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map (𝒰.f j).op).hom)
    (Finsupp.single (gam ζ) 1)) = _ at hj
  erw [Finsupp.mapDomain_single] at hj
  exact hj

end LateralTheory.E.TwGenNZACPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ProjFPf
noncomputable section
open LateralTheory.E.t_E1Cut LateralTheory.E.LCSplitPf LateralTheory.E.TorEtPf

namespace LateralTheory.E.ProjFPf

section Tw
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}

theorem twist_apply (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (k : ZMod q) :
    twist hε z k = ∑ c, ε c * z (k + c) := rfl

def tinv (ε : ZMod q → A) (z : ZMod q → A) : ZMod q → A := fun k => ∑ d, ε (-d) * z (k + d)

theorem twist_tinv (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) : twist hε (tinv ε z) = z := by
  funext k
  rw [twist_apply]
  unfold tinv
  have : ∀ c, ε c * ∑ d, ε (-d) * z (k + c + d) = ε c * z k := by
    intro c
    rw [Finset.mul_sum, Finset.sum_eq_single (-c)]
    · rw [neg_neg, ← mul_assoc, (hε.idem c).eq, add_neg_cancel_right]
    · intro d _ hd
      have : c ≠ -d := fun h => hd (by rw [h, neg_neg])
      rw [← mul_assoc, hε.ortho this, zero_mul]
    · simp
  simp_rw [this, ← Finset.sum_mul, hε.complete, one_mul]

theorem tinv_twist (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) : tinv ε (twist hε z) = z := by
  funext k
  unfold tinv
  simp_rw [twist_apply]
  have : ∀ d, ε (-d) * ∑ c, ε c * z (k + d + c) = ε (-d) * z k := by
    intro d
    rw [Finset.mul_sum, Finset.sum_eq_single (-d)]
    · rw [← mul_assoc, (hε.idem (-d)).eq, add_neg_cancel_right]
    · intro c _ hc
      rw [← mul_assoc, hε.ortho (Ne.symm hc), zero_mul]
    · simp
  simp_rw [this, ← Finset.sum_mul]
  rw [show (∑ d : ZMod q, ε (-d)) = ∑ d, ε d from
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl), hε.complete, one_mul]

theorem twist_const_mul (hε : CompleteOrthogonalIdempotents ε) (a : A) (z : ZMod q → A) :
    twist hε (fun k => a * z k) = fun k => a * twist hε z k := by
  funext k
  simp only [twist_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem eq_zero_of_twist (hε : CompleteOrthogonalIdempotents ε) (z : ZMod q → A) (h : twist hε z = 0) : z = 0 := by
  rw [← tinv_twist hε z, h]; funext k; simp [tinv]
end Tw

section Main
variable {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S)

theorem mem_tor {ε : ZMod q → Localization.Away (f * g)} (hε : CompleteOrthogonalIdempotents ε) (p : Amb f g q) :
    p ∈ Tor f g hε ↔ ∀ k, rL f g (p.1 k) = twist hε (fun j => rR f g (p.2 j)) k :=
  funext_iff

theorem rR_alg (a : S) : rR f g (algebraMap S (Localization.Away g) a) = algebraMap S (Localization.Away (f * g)) a := by
  unfold rR; exact IsLocalization.Away.awayToAwayLeft_eq g f a

theorem rL_alg (a : S) : rL f g (algebraMap S (Localization.Away f) a) = algebraMap S (Localization.Away (f * g)) a := by
  unfold rL; exact IsLocalization.Away.awayToAwayRight_eq f g a

theorem unit_g : IsUnit (algebraMap S (Localization.Away (f * g)) g) := by
  refine isUnit_of_mul_isUnit_right (x := algebraMap S (Localization.Away (f * g)) f) ?_
  rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (f * g)

theorem kill (z : Localization.Away g) (hz : rR f g z = 0) :
    ∃ m : ℕ, algebraMap S (Localization.Away g) f ^ m * z = 0 := by
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) z
  dsimp only at hz ⊢
  have hb : algebraMap S (Localization.Away (f * g)) b = 0 := by
    rw [← rR_alg, ← IsLocalization.mk'_spec (Localization.Away g) b s, map_mul, hz, zero_mul]
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f * g)) _ b).mp hb
  refine ⟨n, ?_⟩
  have hu : IsUnit (algebraMap S (Localization.Away g) (s : S) * algebraMap S (Localization.Away g) (g ^ n)) :=
    (IsLocalization.map_units (Localization.Away g) s).mul
      (by rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit g).pow n)
  refine (hu.mul_left_eq_zero).mp ?_
  calc algebraMap S (Localization.Away g) f ^ n * IsLocalization.mk' (Localization.Away g) b s *
        (algebraMap S (Localization.Away g) (s : S) * algebraMap S (Localization.Away g) (g ^ n))
      = algebraMap S (Localization.Away g) f ^ n *
        (IsLocalization.mk' (Localization.Away g) b s * algebraMap S (Localization.Away g) (s : S)) *
        algebraMap S (Localization.Away g) (g ^ n) := by ring
    _ = algebraMap S (Localization.Away g) ((f * g) ^ n * b) := by
        rw [IsLocalization.mk'_spec, mul_pow]; simp only [map_mul, map_pow]; ring
    _ = 0 := by simp only at hn; rw [hn, map_zero]
end Main

theorem projF : ProjF := by
  intro q _ S _ f g _ ε hε
  let _ := (torMap f g hε).toAlgebra
  let _ := (pr1 f g hε).toAlgebra
  have hA : ∀ t : Tor f g hε, algebraMap (Tor f g hε) (ZMod q → Localization.Away f) t = (t : Amb f g q).1 :=
    fun _ => rfl
  have hf : algebraMap S (Tor f g hε) f = torMap f g hε f := rfl
  have hT1 : ((torMap f g hε f : Tor f g hε) : Amb f g q).1 = fun _ => algebraMap S (Localization.Away f) f := rfl
  have hT2 : ((torMap f g hε f : Tor f g hε) : Amb f g q).2 = fun _ => algebraMap S (Localization.Away g) f := rfl
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [hA, hf, hT1, Pi.isUnit_iff]; intro _; exact IsLocalization.Away.algebraMap_isUnit f
  · intro s
    set w : ZMod q → Localization.Away (f * g) := tinv ε (fun k => rL f g (s k)) with hw
    obtain ⟨⟨_, n, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (f * g)) w
    have hb' : ∀ i, ∃ a, algebraMap S (Localization.Away (f * g)) a = (f * g) ^ n • w i :=
      fun i => RingHom.mem_rangeS.mp (hb i)
    choose a ha using hb'
    let y : ZMod q → Localization.Away g := fun k =>
      IsLocalization.mk' (Localization.Away g) (a k) (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
    have hy : ∀ k, rR f g (y k) = algebraMap S _ (f ^ n) * w k := by
      intro k
      have hu : IsUnit (algebraMap S (Localization.Away (f * g)) (g ^ n)) := by
        rw [map_pow]; exact (unit_g f g).pow n
      apply hu.mul_left_injective
      have e1 := IsLocalization.mk'_spec (Localization.Away g) (a k) (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
      simp only at e1 ⊢
      rw [← rR_alg f g (g ^ n), ← map_mul, e1]
      simp only [rR_alg, ha k, Algebra.smul_def, mul_pow, map_mul, map_pow]
      ring
    let x : ZMod q → Localization.Away f := fun k => s k * algebraMap S _ f ^ n
    have hmem : ((x, y) : Amb f g q) ∈ Tor f g hε := by
      rw [mem_tor]; intro k
      have h2 : (fun j => rR f g (((x, y) : Amb f g q).2 j)) = fun j => algebraMap S _ (f ^ n) * w j := funext hy
      rw [h2, twist_const_mul, hw, twist_tinv]
      show rL f g (s k * algebraMap S _ f ^ n) = _
      rw [map_mul, map_pow, rL_alg, map_pow]; ring
    refine ⟨n, ⟨(x, y), hmem⟩, ?_⟩
    show s * (((torMap f g hε f : Tor f g hε) : Amb f g q).1) ^ n = x
    rw [hT1]
    funext k
    simp only [Pi.mul_apply, Pi.pow_apply]
    rfl
  · intro a b hab
    have hc1 : ((a - b : Tor f g hε) : Amb f g q).1 = 0 := by
      rw [← hA (a - b), map_sub, hab, sub_self]
    have hm := (mem_tor f g hε _).mp (a - b).2
    have htw : twist hε (fun j => rR f g (((a - b : Tor f g hε) : Amb f g q).2 j)) = 0 := by
      funext k; rw [← hm k, hc1]; simp
    have hc2 := eq_zero_of_twist hε _ htw
    have hk : ∀ k, ∃ m : ℕ, algebraMap S (Localization.Away g) f ^ m * ((a - b : Tor f g hε) : Amb f g q).2 k = 0 :=
      fun k => kill f g _ (congrFun hc2 k)
    choose m hm' using hk
    refine ⟨Finset.univ.sup m, ?_⟩
    rw [← sub_eq_zero, ← mul_sub]
    apply Subtype.ext
    apply Prod.ext
    · have e : ((algebraMap S (Tor f g hε) f ^ Finset.univ.sup m : Tor f g hε) : Amb f g q).1 *
          ((a - b : Tor f g hε) : Amb f g q).1 = 0 := by rw [hc1, mul_zero]
      exact e
    · funext k
      show (algebraMap S (Localization.Away g) f) ^ (Finset.univ.sup m) * ((a - b : Tor f g hε) : Amb f g q).2 k = 0
      rw [← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ k) : m k ≤ Finset.univ.sup m), pow_add, mul_assoc, hm' k,
        mul_zero]

end LateralTheory.E.ProjFPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.SurjStepPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.ZarIndPf

namespace LateralTheory.E.SurjStepPf

set_option linter.unusedSimpArgs false

variable {X S : Scheme.{0}}

theorem pc {R : Type} [CommRing R] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (F : Shv R) (n : ℤ) (x : H R (sch.obj C) F n) :
    pull R (sch.map (f ≫ g)) F n x = pull R (sch.map f) F n (pull R (sch.map g) F n x) := by
  rw [Functor.map_comp, pull_comp]

@[reassoc] theorem resO_fst (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : resO p h ≫ pullback.fst p U.ι = pullback.fst p V.ι :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc] theorem resO_snd (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO p h ≫ pullback.snd p U.ι = pullback.snd p V.ι ≫ S.homOfLE h :=
  pullback.lift_snd _ _ _

@[reassoc] theorem fO_fst {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    fO f p U ≫ pullback.fst p U.ι = pullback.fst (f ≫ p) U.ι ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc] theorem fO_snd {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    fO f p U ≫ pullback.snd p U.ι = pullback.snd (f ≫ p) U.ι :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem resO_comp (p : X ⟶ S) {U V W : S.Opens} (h1 : U ≤ V) (h2 : V ≤ W) :
    resO p h1 ≫ resO p h2 = resO p (h1.trans h2) := by
  apply pullback.hom_ext <;> simp only [Category.assoc, resO_fst, resO_snd, fO_fst, fO_snd, resO_fst_assoc, resO_snd_assoc, fO_fst_assoc, fO_snd_assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl, Category.comp_id, Category.id_comp]

theorem resO_refl (p : X ⟶ S) (U : S.Opens) : resO p (le_refl U) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp only [Category.assoc, resO_fst, resO_snd, fO_fst, fO_snd, resO_fst_assoc, resO_snd_assoc, fO_fst_assoc, fO_snd_assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl, Category.comp_id, Category.id_comp]

instance (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : IsOpenImmersion (resO p h) := by
  have : IsOpenImmersion (resO p h ≫ pullback.fst p U.ι) := by rw [resO_fst]; infer_instance
  exact IsOpenImmersion.of_comp (resO p h) (pullback.fst p U.ι)

theorem range_fst (p : X ⟶ S) (V : S.Opens) : Set.range (pullback.fst p V.ι) = p ⁻¹' (V : Set S) := by
  rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

theorem range_resO (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    Set.range (resO p h) = pullback.fst p U.ι ⁻¹' (p ⁻¹' (V : Set S)) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, resO_fst, ← range_fst]
    exact ⟨w, rfl⟩
  · intro hz
    rw [Set.mem_preimage, ← range_fst] at hz
    obtain ⟨w, hw⟩ := hz
    refine ⟨w, (pullback.fst p U.ι).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, resO_fst, hw]

theorem cover (p : X ⟶ S) (V W : S.Opens) :
    Set.range (resO p (le_sup_left : V ≤ V ⊔ W)) ∪ Set.range (resO p (le_sup_right : W ≤ V ⊔ W)) = Set.univ := by
  rw [range_resO, range_resO, ← Set.preimage_union, ← Set.preimage_union, Set.eq_univ_iff_forall]
  intro z
  have : pullback.fst p (V ⊔ W).ι z ∈ Set.range (pullback.fst p (V ⊔ W).ι) := ⟨z, rfl⟩
  rw [range_fst] at this
  simpa [Set.mem_union] using this

def phi (p : X ⟶ S) (V W : S.Opens) :
    pullback (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) ⟶ overO p (V ⊓ W) :=
  IsOpenImmersion.lift (resO p (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W))
    (pullback.fst _ _ ≫ resO p le_sup_left) (by
      rintro _ ⟨z, rfl⟩
      rw [range_resO]
      have h1 : (pullback.fst _ _ ≫ resO p (le_sup_left : V ≤ V ⊔ W)) z ∈ Set.range (resO p (le_sup_left : V ≤ V ⊔ W)) :=
        ⟨_, (Scheme.Hom.comp_apply _ _ z).symm⟩
      have h2 : (pullback.fst _ _ ≫ resO p (le_sup_left : V ≤ V ⊔ W)) z ∈ Set.range (resO p (le_sup_right : W ≤ V ⊔ W)) := by
        rw [pullback.condition]; exact ⟨_, (Scheme.Hom.comp_apply _ _ z).symm⟩
      rw [range_resO] at h1 h2
      exact ⟨h1, h2⟩)

@[reassoc] theorem phi_fac (p : X ⟶ S) (V W : S.Opens) :
    phi p V W ≫ resO p (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W) = pullback.fst _ _ ≫ resO p le_sup_left :=
  IsOpenImmersion.lift_fac _ _ _

theorem phi_fst (p : X ⟶ S) (V W : S.Opens) : phi p V W ≫ resO p inf_le_left = pullback.fst _ _ := by
  rw [← cancel_mono (resO p (le_sup_left : V ≤ V ⊔ W)), Category.assoc, resO_comp, phi_fac]

theorem phi_snd (p : X ⟶ S) (V W : S.Opens) : phi p V W ≫ resO p inf_le_right = pullback.snd _ _ := by
  rw [← cancel_mono (resO p (le_sup_right : W ≤ V ⊔ W)), Category.assoc, resO_comp, ← pullback.condition]
  exact phi_fac p V W

def psi (p : X ⟶ S) (V W : S.Opens) :
    overO p (V ⊓ W) ⟶ pullback (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) :=
  pullback.lift (resO p inf_le_left) (resO p inf_le_right) (by rw [resO_comp, resO_comp])

theorem phi_psi (p : X ⟶ S) (V W : S.Opens) : phi p V W ≫ psi p V W = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, psi, pullback.lift_fst, phi_fst, Category.id_comp]
  · rw [Category.assoc, psi, pullback.lift_snd, phi_snd, Category.id_comp]

theorem fO_res {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO (f ≫ p) h ≫ fO f p U = fO f p V ≫ resO p h := by
  apply pullback.hom_ext <;> simp only [Category.assoc, resO_fst, resO_snd, fO_fst, fO_snd, resO_fst_assoc, resO_snd_assoc, fO_fst_assoc, fO_snd_assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl, Category.comp_id, Category.id_comp]

theorem phi_nat {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (V W : S.Opens) :
    pullback.map _ _ _ _ (fO f p V) (fO f p W) (fO f p (V ⊔ W)) (fO_res f p le_sup_left) (fO_res f p le_sup_right) ≫ phi p V W =
      phi (f ≫ p) V W ≫ fO f p (V ⊓ W) := by
  rw [← cancel_mono (resO p (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W)), Category.assoc, Category.assoc, phi_fac,
    ← fO_res, phi_fac_assoc, fO_res, ← Category.assoc, ← Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _

theorem empty_over (p : X ⟶ S) (U : S.Opens) (h : (U : Set S) = ∅) : IsEmpty (overO p U) :=
  ⟨fun z => by
    have : pullback.fst p U.ι z ∈ Set.range (pullback.fst p U.ι) := ⟨z, rfl⟩
    rw [range_fst, h] at this
    exact this⟩

theorem glue (hM : MV) (hH : Hyp) (q : ℕ) {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (i m : ℤ) (V W : S.Opens)
    (hinj : Function.Injective (pull _ (sch.map (fO f p (V ⊓ W))) (tw q i) (m + 1)))
    (hsurj : Function.Surjective (pull _ (sch.map (fO f p (V ⊓ W))) (tw q i) m))
    (y : H (ZMod q) (sch.obj (overO (f ≫ p) (V ⊔ W))) (tw q i) (m + 1))
    (xV : H (ZMod q) (sch.obj (overO p V)) (tw q i) (m + 1)) (xW : H (ZMod q) (sch.obj (overO p W)) (tw q i) (m + 1))
    (hV : pull _ (sch.map (fO f p V)) _ _ xV = pull _ (sch.map (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W))) _ _ y)
    (hW : pull _ (sch.map (fO f p W)) _ _ xW = pull _ (sch.map (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W))) _ _ y) :
    ∃ x, pull _ (sch.map (fO f p (V ⊔ W))) _ _ x = y := by
  obtain ⟨δ, hδ, hnat⟩ := hM hH (ZMod q) (tw q i)
  have hX := hδ (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) (cover p V W)
  have hY := hδ (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W)) (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W)) (cover (f ≫ p) V W)
  have e1 : pull _ (sch.map (fO f p (V ⊓ W))) _ _ (pull _ (sch.map (resO p (inf_le_left : V ⊓ W ≤ V))) _ _ xV) =
      pull _ (sch.map (resO (f ≫ p) (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W))) _ _ y := by
    rw [← pc, ← fO_res, pc, hV, ← pc, resO_comp]
  have e2 : pull _ (sch.map (fO f p (V ⊓ W))) _ _ (pull _ (sch.map (resO p (inf_le_right : V ⊓ W ≤ W))) _ _ xW) =
      pull _ (sch.map (resO (f ≫ p) (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W))) _ _ y := by
    rw [← pc, ← fO_res, pc, hW, ← pc, resO_comp]
  have hI := hinj (e1.trans e2.symm)
  obtain ⟨x0, hx0V, hx0W⟩ := (hX (m + 1)).1 xV xW (by rw [← phi_fst p V W, ← phi_snd p V W, pc, pc, hI])
  have hzV : pull _ (sch.map (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W))) _ _ (pull _ (sch.map (fO f p (V ⊔ W))) _ _ x0 - y) = 0 := by
    rw [map_sub, ← pc, fO_res, pc, hx0V, hV, sub_self]
  have hzW : pull _ (sch.map (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W))) _ _ (pull _ (sch.map (fO f p (V ⊔ W))) _ _ x0 - y) = 0 := by
    rw [map_sub, ← pc, fO_res, pc, hx0W, hW, sub_self]
  obtain ⟨w', hw'⟩ := ((hY m).2.2 _).1 ⟨hzV, hzW⟩
  obtain ⟨u, hu⟩ := hsurj (pull _ (sch.map (psi (f ≫ p) V W)) _ _ w')
  have hn := hnat (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W)) (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W))
    (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) (cover (f ≫ p) V W) (cover p V W)
    (fO f p V) (fO f p W) (fO f p (V ⊔ W)) (fO_res f p le_sup_left) (fO_res f p le_sup_right) m
    (pull _ (sch.map (phi p V W)) _ _ u)
  rw [← pc, phi_nat, pc, hu, ← pc, phi_psi] at hn
  rw [CategoryTheory.Functor.map_id, pull_id] at hn
  rw [hw'] at hn
  refine ⟨x0 - δ _ _ m (pull _ (sch.map (phi p V W)) _ _ u), ?_⟩
  rw [map_sub, ← hn, sub_sub_cancel]

theorem SurjStep_of : SurjStep := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hg hb hinj U hU y
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have hb' : ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i m f p U := by simpa using hb
  let Good : S.Opens → Prop := fun V => ∃ h : V ≤ U, ∃ x : H (ZMod q) (sch.obj (overO p V)) (tw q i) (m + 1),
    pull _ (sch.map (fO f p V)) _ _ x = pull _ (sch.map (resO (f ≫ p) h)) _ _ y
  have mono : ∀ V V' : S.Opens, V' ≤ V → Good V → Good V' := by
    rintro V V' h ⟨hV, x, hx⟩
    refine ⟨h.trans hV, pull _ (sch.map (resO p h)) _ _ x, ?_⟩
    rw [← pc, ← fO_res, pc, hx, ← pc, resO_comp]
  have union : ∀ V W : S.Opens, IsCompact (V : Set S) → IsCompact (W : Set S) → Good V → Good W → Good (V ⊔ W) := by
    rintro V W hVc hWc ⟨hV, xV, hxV⟩ ⟨hW, xW, hxW⟩
    have hIc : IsCompact ((V ⊓ W : S.Opens) : Set S) :=
      QuasiSeparatedSpace.inter_isCompact _ _ V.isOpen hVc W.isOpen hWc
    obtain ⟨x, hx⟩ := glue hM hH q f p i m V W (hinj _ hIc) (hb' _ hIc).2
      (pull _ (sch.map (resO (f ≫ p) (sup_le hV hW))) _ _ y) xV xW
      (by rw [hxV]; first | rfl | rw [← pc, resO_comp]) (by rw [hxW]; first | rfl | rw [← pc, resO_comp])
    exact ⟨sup_le hV hW, x, by rw [hx]⟩
  have P : (U : Set S) = ∅ ∨ ∃ V : S.Opens, IsCompact (V : Set S) ∧ (U : Set S) ⊆ V ∧ Good V := by
    refine hU.induction_on (p := fun T : Set S => T = ∅ ∨ ∃ V : S.Opens, IsCompact (V : Set S) ∧ T ⊆ V ∧ Good V)
      (Or.inl rfl) ?_ ?_ ?_
    · rintro s t hst (h | ⟨V, hVc, htV, hV⟩)
      · exact Or.inl (Set.subset_eq_empty hst h)
      · exact Or.inr ⟨V, hVc, hst.trans htV, hV⟩
    · rintro s t (h | h1) (h' | h2)
      · left; rw [h, h', Set.empty_union]
      · right; rw [h, Set.empty_union]; exact h2
      · right; rw [h', Set.union_empty]; exact h1
      · obtain ⟨V, hVc, hsV, hV⟩ := h1
        obtain ⟨W, hWc, htW, hW⟩ := h2
        exact Or.inr ⟨V ⊔ W, by simpa using hVc.union hWc, Set.union_subset_union hsV htW, union V W hVc hWc hV hW⟩
    · intro s hs
      obtain ⟨V, hVU, hsV, x, hx⟩ := (hg s).2 U hs y
      obtain ⟨V', hV'aff, hsV', hV'V⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens S)) hsV
      exact ⟨V', mem_nhdsWithin_of_mem_nhds (V'.isOpen.mem_nhds hsV'),
        Or.inr ⟨V', hV'aff.isCompact, subset_rfl, mono V V' hV'V ⟨hVU, x, hx⟩⟩⟩
  rcases P with h | ⟨V, -, hUV, hVU, x, hx⟩
  · have := empty_over p U h
    exact (pull_bij_of_iso (sch.map (fO f p U)) (tw q i) _).2 y
  · obtain rfl : V = U := le_antisymm hVU hUV
    exact ⟨x, by rw [hx, resO_refl, CategoryTheory.Functor.map_id, pull_id]⟩

end LateralTheory.E.SurjStepPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.GluePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.ProEqvPf

namespace LateralTheory.E.GluePf

theorem sec_sub {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) [IsEmpty X] : Subsingleton (Sec F X) := by
  have hb : (⊥ : Sieve X) ∈ Scheme.etaleTopology X := Scheme.bot_mem_grothendieckTopology X
  constructor
  intro a b
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property)
  exact (h1 ⊥ hb).isSeparatedFor.ext (fun _ _ hf => hf.elim)

theorem pull_inj_of_initial {R : Type} [CommRing R] {F : Shv R} {X Y : Scheme.{0}} (hX : IsInitial X) (f : Y ⟶ X) (n : ℤ)
    (x : H R (sch.obj X) F n) (hx : pull R (sch.map f) F n x = 0) : x = 0 := by
  have e : hX.to Y ≫ f = 𝟙 X := hX.hom_ext _ _
  have : x = pull R (sch.map (hX.to Y ≫ f)) F n x := by rw [e, CategoryTheory.Functor.map_id, pull_id]
  rw [this, Functor.map_comp, pull_comp, hx, map_zero]

theorem ht_sub (H : Hyp) (q : ℕ) (i n : ℤ) (X : Scheme.{0}) [IsEmpty X] : Subsingleton (Ht q (sch.obj X) n i) := by
  rcases lt_trichotomy n 0 with h | rfl | h
  · exact (H.a9 (ZMod q) (tw q i)).1 _ n h
  · obtain ⟨e, -⟩ := (H.a9 (ZMod q) (tw q i)).2
    have := sec_sub (tw q i) X
    exact ⟨fun a b => (e X).symm.injective (Subsingleton.elim _ _)⟩
  · constructor
    have key : ∀ x : Ht q (sch.obj X) n i, x = 0 := by
      intro x
      obtain ⟨Y, f, -, -, hf⟩ := H.a5 (ZMod q) X (tw q i) n h x
      exact pull_inj_of_initial (isInitialOfIsEmpty) f n x hf
    intro a b; rw [key a, key b]

def cmp {X : Scheme.{0}} (O : X.Opens) (hO : IsClosed (O : Set X)) : X.Opens := ⟨(O : Set X)ᶜ, hO.isOpen_compl⟩

theorem mem_ι {X : Scheme.{0}} (U : X.Opens) (p : U) : U.ι p ∈ U := by
  have : U.ι p ∈ Set.range U.ι := ⟨p, rfl⟩
  rwa [Scheme.Opens.range_ι] at this

theorem vanish_of_range {R : Type} [CommRing R] {F : Shv R} {X U Z : Scheme.{0}} (u : U ⟶ X) [IsOpenImmersion u] (g : Z ⟶ X)
    (hg : Set.range g ⊆ Set.range u) (n : ℤ) (v : H R (sch.obj X) F n) (hv : pull R (sch.map u) F n v = 0) :
    pull R (sch.map g) F n v = 0 := by
  rw [← IsOpenImmersion.lift_fac u g hg, CategoryTheory.Functor.map_comp, pull_comp, hv, map_zero]

theorem empty_pb' {X : Scheme.{0}} (O1 O2 : X.Opens) (hd : ∀ p, p ∈ O1 → p ∉ O2) :
    IsEmpty ((pullback O1.ι O2.ι : Scheme.{0})) := by
  constructor; intro p
  have h := congrArg (fun φ => φ p) (pullback.condition (f := O1.ι) (g := O2.ι))
  simp only [Scheme.Hom.comp_apply] at h
  have a := mem_ι O1 (pullback.fst O1.ι O2.ι p)
  have b := mem_ι O2 (pullback.snd O1.ι O2.ι p)
  rw [← h] at b
  exact hd _ a b

theorem cover' {X : Scheme.{0}} (O1 O2 : X.Opens) (hc : ∀ p, p ∈ O1 ∨ p ∈ O2) :
    Set.range O1.ι ∪ Set.range O2.ι = Set.univ := by
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  ext p; simp only [Set.mem_union, Set.mem_univ, iff_true]; exact hc p

theorem two_inj' (hM : MV) (H : Hyp) (q : ℕ) (i : ℤ) {X : Scheme.{0}} (O1 O2 : X.Opens) (hd : ∀ p, p ∈ O1 → p ∉ O2)
    (hc : ∀ p, p ∈ O1 ∨ p ∈ O2) (n : ℤ)
    (x : Ht q (sch.obj X) n i) (h1 : pull _ (sch.map O1.ι) _ _ x = 0) (h2 : pull _ (sch.map O2.ι) _ _ x = 0) : x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  obtain ⟨δ, hex, -⟩ := hM H (ZMod q) (tw q i)
  obtain ⟨w, rfl⟩ := ((hex O1.ι O2.ι (cover' O1 O2 hc) m).2.2 x).1 ⟨h1, h2⟩
  have := empty_pb' O1 O2 hd
  have := ht_sub H q i m (pullback O1.ι O2.ι)
  rw [Subsingleton.elim w 0, map_zero]

theorem inj_fin (hM : MV) (H : Hyp) (q : ℕ) (i n : ℤ) : ∀ (k : ℕ) {X : Scheme.{0}} (O : Fin k → X.Opens),
    (∀ j, IsClosed (O j : Set X)) → (∀ p : X, ∃ j, p ∈ O j) → ∀ x : Ht q (sch.obj X) n i,
    (∀ j, pull _ (sch.map (O j).ι) _ _ x = 0) → x = 0 := by
  intro k
  induction k with
  | zero =>
    intro X O _ hc x _
    have : IsEmpty X := ⟨fun p => (hc p).elim fun j _ => j.elim0⟩
    have := ht_sub H q i n X
    exact Subsingleton.elim _ _
  | succ k ih =>
    intro X O hO hc x hx
    let A := O (Fin.last k)
    let C := cmp A (hO _)
    refine two_inj' hM H q i A C (fun p h1 h2 => h2 h1) (fun p => by by_cases h : p ∈ A; exacts [Or.inl h, Or.inr h]) n x
      (hx _) ?_
    refine ih (fun j => C.ι ⁻¹ᵁ O j.castSucc) (fun j => (hO _).preimage C.ι.continuous) ?_ _ ?_
    · intro p
      obtain ⟨j, hj⟩ := hc (C.ι p)
      have hpc := mem_ι C p
      cases j using Fin.lastCases with
      | last => exact absurd hj hpc
      | cast j' => exact ⟨j', hj⟩
    · intro j
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp]
      refine vanish_of_range (O j.castSucc).ι _ ?_ n x (hx _)
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact mem_ι _ p

theorem two_glue' (hM : MV) (H : Hyp) (q : ℕ) (i : ℤ) {X : Scheme.{0}} (O1 O2 : X.Opens) (hd : ∀ p, p ∈ O1 → p ∉ O2)
    (hc : ∀ p, p ∈ O1 ∨ p ∈ O2) (n : ℤ) (a : Ht q (sch.obj O1) n i) (b : Ht q (sch.obj O2) n i) :
    ∃ x : Ht q (sch.obj X) n i, pull _ (sch.map O1.ι) _ _ x = a ∧ pull _ (sch.map O2.ι) _ _ x = b := by
  obtain ⟨δ, hex, -⟩ := hM H (ZMod q) (tw q i)
  have := empty_pb' O1 O2 hd
  have := ht_sub H q i n (pullback O1.ι O2.ι)
  exact (hex O1.ι O2.ι (cover' O1 O2 hc) n).1 a b (Subsingleton.elim _ _)

theorem surj_fin (hM : MV) (H : Hyp) (q : ℕ) (i n : ℤ) {X P : Scheme.{0}} (φ : P ⟶ X) (z : Ht q (sch.obj P) n i) :
    ∀ (k : ℕ) (O : Fin k → X.Opens), (∀ j, IsClosed (O j : Set X)) →
    (∀ j, ∃ w : Ht q (sch.obj (O j)) n i, pull _ (sch.map (φ ∣_ O j)) _ _ w = pull _ (sch.map (φ ⁻¹ᵁ O j).ι) _ _ z) →
    ∃ x : Ht q (sch.obj X) n i, ∀ j, pull _ (sch.map (φ ⁻¹ᵁ O j).ι) _ _ (pull _ (sch.map φ) _ _ x) =
      pull _ (sch.map (φ ⁻¹ᵁ O j).ι) _ _ z := by
  intro k
  induction k with
  | zero => intro O _ _; exact ⟨0, fun j => j.elim0⟩
  | succ k ih =>
    intro O hO hW
    obtain ⟨x, hx⟩ := ih (fun j => O j.castSucc) (fun j => hO _) (fun j => hW _)
    let A := O (Fin.last k)
    let C := cmp A (hO _)
    obtain ⟨w, hw⟩ := hW (Fin.last k)
    obtain ⟨x', h1, h2⟩ := two_glue' hM H q i A C (fun p h1 h2 => h2 h1)
      (fun p => by by_cases h : p ∈ A; exacts [Or.inl h, Or.inr h]) n w (pull _ (sch.map C.ι) _ _ x)
    have agreeA : pull _ (sch.map (φ ⁻¹ᵁ A).ι) _ _ (pull _ (sch.map φ) _ _ x') = pull _ (sch.map (φ ⁻¹ᵁ A).ι) _ _ z := by
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp, ← morphismRestrict_ι, CategoryTheory.Functor.map_comp, pull_comp, h1]
      exact hw
    refine ⟨x', fun j => ?_⟩
    cases j using Fin.lastCases with
    | last => exact agreeA
    | cast j' =>
      rw [← sub_eq_zero, ← map_sub]
      let V := φ ⁻¹ᵁ O j'.castSucc
      refine two_inj' hM H q i (V.ι ⁻¹ᵁ (φ ⁻¹ᵁ A)) (V.ι ⁻¹ᵁ (φ ⁻¹ᵁ C)) (fun p h1 h2 => h2 h1)
        (fun p => by by_cases h : p ∈ V.ι ⁻¹ᵁ (φ ⁻¹ᵁ A); exacts [Or.inl h, Or.inr h]) n _ ?_ ?_
      · rw [← pull_comp, ← CategoryTheory.Functor.map_comp]
        refine vanish_of_range (φ ⁻¹ᵁ A).ι _ ?_ n _ (by rw [map_sub, agreeA, sub_self])
        rintro _ ⟨p, rfl⟩
        rw [Scheme.Opens.range_ι]
        simp only [Scheme.Hom.comp_apply]
        exact mem_ι _ p
      · have e : pull _ (sch.map φ) _ _ x' - z = pull _ (sch.map φ) _ _ (x' - x) + (pull _ (sch.map φ) _ _ x - z) := by
          rw [map_sub]; abel
        rw [e, map_add (f := _), map_add (f := _), map_sub (pull _ (sch.map V.ι) _ _), hx j', sub_self, map_zero, add_zero,
          ← pull_comp, ← pull_comp, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
        refine vanish_of_range C.ι _ ?_ n _ (by rw [map_sub, h2, sub_self])
        rintro _ ⟨p, rfl⟩
        rw [Scheme.Opens.range_ι]
        simp only [Scheme.Hom.comp_apply]
        exact mem_ι _ p

theorem hit_opens (q : ℕ) (i n : ℤ) {A : Type} [CommRing A] [IsLocalRing A] {U Y : Scheme.{0}}
    (g : Y ⟶ Spec (CommRingCat.of A)) (z : Ht q (sch.obj (pullback g (cpt A))) n i) (u : U ⟶ Y) [IsOpenImmersion u]
    (O : Y.Opens) (hO : (O : Set Y) = Set.range u) (h : Hit q i n g z u) :
    ∃ w : Ht q (sch.obj O) n i, pull _ (sch.map (pullback.fst g (cpt A) ∣_ O)) _ _ w =
      pull _ (sch.map (pullback.fst g (cpt A) ⁻¹ᵁ O).ι) _ _ z := by
  obtain ⟨w, hw⟩ := h
  have hr : Set.range O.ι ⊆ Set.range u := by rw [Scheme.Opens.range_ι, hO]
  let r := IsOpenImmersion.lift u O.ι hr
  have hr' : r ≫ u = O.ι := IsOpenImmersion.lift_fac _ _ _
  have hr'' : ∀ {Z : Scheme.{0}} (t : Y ⟶ Z), r ≫ u ≫ t = O.ι ≫ t := by
    intro Z t; rw [← Category.assoc, hr']
  let e : ((pullback.fst g (cpt A) ⁻¹ᵁ O : Scheme.{0})) ⟶ pullback (u ≫ g) (cpt A) :=
    pullback.lift ((pullback.fst g (cpt A) ∣_ O) ≫ r) ((pullback.fst g (cpt A) ⁻¹ᵁ O).ι ≫ pullback.snd g (cpt A))
      (by rw [Category.assoc, hr'', morphismRestrict_ι_assoc, pullback.condition, Category.assoc])
  have he : e ≫ fm u g = (pullback.fst g (cpt A) ⁻¹ᵁ O).ι := by
    unfold fm
    apply pullback.hom_ext
    · simp only [e, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hr', morphismRestrict_ι, pullback.map]
    · simp only [e, Category.assoc, pullback.lift_snd, Category.comp_id, pullback.map]
  refine ⟨pull _ (sch.map r) _ _ w, ?_⟩
  have h2 : (pullback.fst g (cpt A) ∣_ O) ≫ r = e ≫ pullback.fst (u ≫ g) (cpt A) := (pullback.lift_fst _ _ _).symm
  rw [← pull_comp, ← CategoryTheory.Functor.map_comp, h2, CategoryTheory.Functor.map_comp, pull_comp, hw, ← pull_comp,
    ← CategoryTheory.Functor.map_comp, he]

theorem fin_cover {Y : Scheme.{0}} [CompactSpace Y] (O : Y → Y.Opens) (hO : ∀ y, y ∈ O y) :
    ∃ (k : ℕ) (f : Fin k → Y), ∀ p, ∃ j, p ∈ O (f j) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (O y : Set Y)) (fun y => (O y).isOpen)
    (fun p _ => Set.mem_iUnion.2 ⟨p, hO p⟩)
  refine ⟨t.card, fun j => (t.equivFin.symm j).1, fun p => ?_⟩
  obtain ⟨y, hy, hp⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ p))
  exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hp⟩

def rg {U Y : Scheme.{0}} (u : U ⟶ Y) (h : IsOpenImmersion u) : Y.Opens := ⟨Set.range u, u.isOpenEmbedding.isOpen_range⟩

theorem rg_closed {U Y : Scheme.{0}} (u : U ⟶ Y) (h : IsOpenImmersion u) (h' : IsClosedImmersion u) :
    IsClosed (rg u h : Set Y) := u.isClosedEmbedding.isClosed_range

theorem glue_of : Glue := by
  intro hM H q i A _ _ hq Y _ _ g n hI hS
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    choose U u hu using hI x hx
    obtain ⟨k, f, hf⟩ := fin_cover (fun y => rg (u y) (hu y).1) (fun y => (hu y).2.2.1)
    refine inj_fin hM H q i n k (fun j => rg (u (f j)) (hu (f j)).1) (fun j => rg_closed (u (f j)) (hu (f j)).1 (hu (f j)).2.1) hf x ?_
    intro j
    have := (hu (f j)).1
    exact vanish_of_range (u (f j)) _ (by rw [Scheme.Opens.range_ι]; exact fun _ h => h) n x (hu (f j)).2.2.2
  · intro z
    choose U u hu using hS z
    obtain ⟨k, f, hf⟩ := fin_cover (fun y => rg (u y) (hu y).1) (fun y => (hu y).2.2.1)
    obtain ⟨x, hx⟩ := surj_fin hM H q i n (pullback.fst g (cpt A)) z k (fun j => rg (u (f j)) (hu (f j)).1)
      (fun j => rg_closed (u (f j)) (hu (f j)).1 (hu (f j)).2.1)
      (fun j => by have := (hu (f j)).1; exact hit_opens q i n g z (u (f j)) _ rfl (hu (f j)).2.2.2)
    refine ⟨x, ?_⟩
    rw [← sub_eq_zero]
    refine inj_fin hM H q i n k (fun j => pullback.fst g (cpt A) ⁻¹ᵁ rg (u (f j)) (hu (f j)).1)
      (fun j => (rg_closed (u (f j)) (hu (f j)).1 (hu (f j)).2.1).preimage (pullback.fst g (cpt A)).continuous) (fun p => hf _) _ ?_
    intro j
    rw [map_sub, hx j, sub_self]

end LateralTheory.E.GluePf
end
end
