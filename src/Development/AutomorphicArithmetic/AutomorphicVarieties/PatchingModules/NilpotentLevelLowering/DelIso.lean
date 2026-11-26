module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwIwQuot

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.DelIso
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Pa.Lev

private theorem di_card (l : ℕ) [hl : Fact l.Prime] (G : Type) [CommGroup G] [Finite G] :
    Nat.card (G ⧸ ellC l G) = l ^ padicValNat l (Nat.card G) := by
  classical
  have hl' := hl.out
  have hQ : IsPGroup l (G ⧸ ellC l G) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨b, c, hc, hbc⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' l hl'.ne_one
      refine ⟨b, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      show (orderOf (x ^ l ^ b)).Coprime l
      rw [orderOf_pow_of_dvd (pow_ne_zero _ hl'.ne_zero) ⟨c, hbc⟩, hbc,
        Nat.mul_div_cancel_left _ (pow_pos hl'.pos _)]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl').2 hc)
  have hC : ¬ l ∣ Nat.card (ellC l G) := by
    intro hd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' l hd
    have h1 : (orderOf (y : G)).Coprime l := y.2
    rw [Subgroup.orderOf_coe, hy] at h1
    exact hl'.one_lt.ne' ((Nat.coprime_self l).1 h1)
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hpos : Nat.card (ellC l G) ≠ 0 := Nat.card_pos.ne'
  rw [hk, Subgroup.card_eq_card_quotient_mul_card_subgroup (ellC l G), hk,
    (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (pow_ne_zero _ hl'.ne_zero) hpos, (show padicValNat l (l ^ k) = k from by
      simpa only [← Nat.padicValNat_def] using Nat.multiplicity_prime_pow (p := l) k),
    (show padicValNat l (Nat.card (ellC l G)) = 0 from by
      simpa only [← Nat.padicValNat_def] using multiplicity_eq_zero_of_not_dvd hC), add_zero]

private theorem di_cyc (l : ℕ) [Fact l.Prime] (G : Type) [CommGroup G] [Finite G] (x : G)
    (hx : Subgroup.zpowers x ⊔ ellC l G = ⊤) (a : ℕ) (ha : a = padicValNat l (Nat.card G)) :
    ∃ e : Multiplicative (ZMod (l ^ a)) ≃* G ⧸ ellC l G, e (Multiplicative.ofAdd 1) = (x : G ⧸ ellC l G) := by
  classical
  have hl' := (Fact.out : l.Prime)
  haveI : NeZero (l ^ a) := ⟨pow_ne_zero _ hl'.ne_zero⟩
  have hcard : Nat.card (G ⧸ ellC l G) = l ^ a := by rw [ha]; exact di_card l G
  let ψ : ZMod (l ^ a) →+ Additive (G ⧸ ellC l G) :=
    ZMod.lift (l ^ a) ⟨zmultiplesHom _ (Additive.ofMul (x : G ⧸ ellC l G)), by
      rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, ← hcard, pow_card_eq_one', ofMul_one]⟩
  let Φ : Multiplicative (ZMod (l ^ a)) →* G ⧸ ellC l G := AddMonoidHom.toMultiplicativeLeft ψ
  have hΦ : ∀ m : ℤ, Φ (Multiplicative.ofAdd (m : ZMod (l ^ a))) = (x : G ⧸ ellC l G) ^ m := by
    intro m
    show Additive.toMul (ψ (m : ZMod (l ^ a))) = _
    rw [ZMod.lift_coe]
    show Additive.toMul (zmultiplesHom _ (Additive.ofMul (x : G ⧸ ellC l G)) m) = _
    rw [zmultiplesHom_apply, toMul_zsmul, toMul_ofMul]
  have hsurj : Function.Surjective Φ := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H g =>
      have hg : g ∈ Subgroup.zpowers x ⊔ ellC l G := hx ▸ Subgroup.mem_top g
      obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup.1 hg
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      refine ⟨Multiplicative.ofAdd (m : ZMod (l ^ a)), ?_⟩
      rw [hΦ, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff v).2 hv, mul_one, QuotientGroup.mk_zpow]
  have hbij : Function.Bijective Φ := by
    refine hsurj.bijective_of_nat_card_le ?_
    rw [hcard]
    show Nat.card (ZMod (l ^ a)) ≤ _
    rw [Nat.card_zmod]
  refine ⟨MulEquiv.ofBijective Φ hbij, ?_⟩
  have h1 := hΦ 1
  rw [Int.cast_one, zpow_one] at h1
  exact h1

private theorem di_pi {q n : ℕ} (G : Fin q → Type) [∀ j, Group (G j)] (H K : ∀ j, Subgroup (G j))
    (Z : Fin q → Type) [∀ j, Group (Z j)] (f : ∀ j, H j →* (Fin n → Z j)) (hs : ∀ j, Function.Surjective (f j))
    (hk : ∀ j (g : H j), f j g = 1 ↔ (g : G j) ∈ K j)
    [((Subgroup.pi Set.univ K).subgroupOf (Subgroup.pi Set.univ H)).Normal] :
    ∃ e : (∀ p : Fin q × Fin n, Z p.1) ≃*
        (Subgroup.pi Set.univ H ⧸ (Subgroup.pi Set.univ K).subgroupOf (Subgroup.pi Set.univ H)),
      ∀ j i (z : Z j) (t : H j), f j t = Pi.mulSingle i z → ∃ g : Subgroup.pi Set.univ H,
        (g : ∀ j, G j) = Pi.mulSingle j (t : G j) ∧ e (Pi.mulSingle (j, i) z) = g := by
  classical
  let Φ : Subgroup.pi Set.univ H →* (∀ p : Fin q × Fin n, Z p.1) :=
    Pi.monoidHom fun p => (Pi.evalMonoidHom _ p.2).comp ((f p.1).comp
      (((Pi.evalMonoidHom G p.1).comp (Subgroup.pi Set.univ H).subtype).codRestrict (H p.1)
        fun g => (Subgroup.mem_pi _).1 g.2 p.1 (Set.mem_univ _)))
  have hΦ : ∀ (g : Subgroup.pi Set.univ H) (p : Fin q × Fin n),
      Φ g p = f p.1 ⟨(g : ∀ j, G j) p.1, (Subgroup.mem_pi _).1 g.2 p.1 (Set.mem_univ _)⟩ p.2 := fun g p => rfl
  have hsurj : Function.Surjective Φ := by
    intro z
    choose t ht using fun j => hs j (fun i => z (j, i))
    refine ⟨⟨fun j => (t j : G j), (Subgroup.mem_pi _).2 fun j _ => (t j).2⟩, funext fun p => ?_⟩
    rw [hΦ]
    exact congrFun (ht p.1) p.2
  have hker : Φ.ker = (Subgroup.pi Set.univ K).subgroupOf (Subgroup.pi Set.univ H) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_pi]
    constructor
    · intro h j _
      refine (hk j ⟨_, (Subgroup.mem_pi _).1 g.2 j (Set.mem_univ _)⟩).1 (funext fun i => ?_)
      have := congrFun h (j, i)
      rw [hΦ] at this
      exact this
    · intro h
      funext p
      rw [hΦ]
      exact congrFun ((hk p.1 ⟨_, (Subgroup.mem_pi _).1 g.2 p.1 (Set.mem_univ _)⟩).2 (h p.1 (Set.mem_univ _))) p.2
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective Φ hsurj).symm.trans (QuotientGroup.quotientMulEquivOfEq hker), ?_⟩
  intro j i z t ht
  have hmemg : Pi.mulSingle j (t : G j) ∈ Subgroup.pi Set.univ H := by
    refine (Subgroup.mem_pi _).2 fun j' _ => ?_
    by_cases h : j' = j
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact t.2
    · rw [Pi.mulSingle_eq_of_ne h]
      exact one_mem _
  have hΦg : Φ ⟨_, hmemg⟩ = Pi.mulSingle (j, i) z := by
    funext p
    obtain ⟨j', i'⟩ := p
    rw [hΦ]
    by_cases h : j' = j
    · subst h
      have key : f j' ⟨Pi.mulSingle j' (t : G j') j', (Subgroup.mem_pi _).1 hmemg j' (Set.mem_univ _)⟩ = f j' t := by
        congr 1
        exact Subtype.ext (Pi.mulSingle_eq_same _ _)
      rw [key, ht]
      by_cases hi : i' = i
      · subst hi
        rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne (fun hp => hi (congrArg Prod.snd hp))]
    · have key : f j' ⟨Pi.mulSingle j (t : G j) j', (Subgroup.mem_pi _).1 hmemg j' (Set.mem_univ _)⟩ = 1 := by
        rw [show (⟨Pi.mulSingle j (t : G j) j', (Subgroup.mem_pi _).1 hmemg j' (Set.mem_univ _)⟩ : H j') = 1 from
          Subtype.ext (Pi.mulSingle_eq_of_ne h _), map_one]
      rw [key, Pi.mulSingle_eq_of_ne (fun hp => h (congrArg Prod.fst hp))]
      rfl
  refine ⟨⟨_, hmemg⟩, rfl, ?_⟩
  have hs1 : (QuotientGroup.quotientKerEquivOfSurjective Φ hsurj).symm (Φ ⟨_, hmemg⟩) =
      ((⟨_, hmemg⟩ : Subgroup.pi Set.univ H) : Subgroup.pi Set.univ H ⧸ Φ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, ← hΦg, hs1, QuotientGroup.quotientMulEquivOfEq_mk]

private theorem di_loc (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n l : ℕ)
    [Fact l.Prime] (δ : kˣ) (hδ : IsGenMod k (ellC l _) δ) :
    ∃ f : iwC k n ⊤ →* (Fin n → Multiplicative (ZMod (l ^ padicValNat l (resCard k - 1)))), Function.Surjective f ∧
      (∀ g : iwC k n ⊤, f g = 1 ↔ (g : GL (Fin n) k) ∈ iwC k n (ellC l _)) ∧
      ∀ i, ∃ t : iwC k n ⊤, (t : GL (Fin n) k) = diagT k (Fin n) (Pi.mulSingle i δ) ∧
        f t = Pi.mulSingle i (Multiplicative.ofAdd 1) := by
  classical
  obtain ⟨d, hdδ, hgen⟩ := hδ
  obtain ⟨f0, hs0, hk0, hv0⟩ := iwQuot k n (ellC l 𝓀[k]ˣ)
  obtain ⟨e, he⟩ := di_cyc l _ _ hgen (padicValNat l (resCard k - 1)) (by rw [Nat.card_units]; rfl)
  refine ⟨(MonoidHom.compLeft e.symm.toMonoidHom (Fin n)).comp f0, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨g, hg⟩ := hs0 (fun i => e (y i))
    refine ⟨g, funext fun i => ?_⟩
    show e.symm (f0 g i) = y i
    rw [hg]
    exact e.symm_apply_apply (y i)
  · intro g
    rw [← hk0 g]
    constructor
    · intro h
      funext i
      exact (MulEquiv.map_eq_one_iff e.symm).1 (congrFun h i)
    · intro h
      funext i
      show e.symm (f0 g i) = 1
      rw [congrFun h i]
      exact map_one e.symm
  · intro i
    let u : Fin n → 𝒪[k]ˣ := Pi.mulSingle i d
    have hmem : ∀ w : Fin n → 𝒪[k]ˣ,
        diagT k (Fin n) (fun i => Units.map (algebraMap 𝒪[k] k : 𝒪[k] →* k) (w i)) ∈ iwC k n ⊤ := by
      intro w
      unfold iwC
      refine Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ ?_)
      unfold torC unitsC
      exact (Subgroup.mem_pi _).2 fun i' _ => Subgroup.mem_map_of_mem _ (Subgroup.mem_comap.2 (Subgroup.mem_top _))
    refine ⟨⟨_, hmem u⟩, ?_, ?_⟩
    · show diagT k (Fin n) _ = _
      congr 1
      funext i'
      by_cases h : i' = i
      · rw [h]
        simp only [u, Pi.mulSingle_eq_same]
        exact hdδ
      · simp only [u, Pi.mulSingle_eq_of_ne h, map_one]
    · funext i'
      refine (congrArg e.symm (hv0 u (hmem u) i')).trans ?_
      by_cases h : i' = i
      · rw [h]
        simp only [u, Pi.mulSingle_eq_same]
        rw [MulEquiv.symm_apply_eq]
        exact he.symm
      · simp only [u, Pi.mulSingle_eq_of_ne h, map_one, QuotientGroup.mk_one]

end UpperTheory.V.Pa.Lev

theorem UpperTheory.V.Pa.Lev.delIso :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (l : ℕ) [Fact l.Prime] (δ : ∀ j, ((w j).adicCompletion L)ˣ) [((UIw1 l n w).subgroupOf (UIw n w)).Normal], (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∃ e : Del l n (fun j => padicValNat l (qj w j - 1)) ≃* (UIw n w ⧸ (UIw1 l n w).subgroupOf (UIw n w)), ∀ j i, ∃ g : UIw n w, (g : GV n w) = atJ n w j (diagT _ (Fin n) (Pi.mulSingle i (δ j))) ∧ e (Pi.mulSingle (j, i) (Multiplicative.ofAdd 1)) = (g : UIw n w ⧸ (UIw1 l n w).subgroupOf (UIw n w)) := by
  intro L _ _ n q w l _ δ _ hδ
  choose f hs hk ht using fun j => di_loc ((w j).adicCompletion L) n l (δ j) (hδ j)
  haveI hN : ((Subgroup.pi Set.univ (fun j => iwC ((w j).adicCompletion L) n (ellC l _))).subgroupOf
      (Subgroup.pi Set.univ (fun j => iwC ((w j).adicCompletion L) n ⊤))).Normal :=
    (inferInstance : ((UIw1 l n w).subgroupOf (UIw n w)).Normal)
  obtain ⟨e, he⟩ := di_pi (fun j => GLw n (w j)) (fun j => iwC ((w j).adicCompletion L) n ⊤)
    (fun j => iwC ((w j).adicCompletion L) n (ellC l _))
    (fun j => Multiplicative (ZMod (l ^ padicValNat l (qj w j - 1)))) f hs hk
  refine ⟨e, fun j i => ?_⟩
  obtain ⟨t, htd, htf⟩ := ht j i
  obtain ⟨g, hg, heg⟩ := he j i _ t htf
  refine ⟨g, ?_, heg⟩
  show (g : ∀ j, GLw n (w j)) = _
  rw [hg, htd]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.MultiPsi
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDdProps
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem rename_alt {R : Type} [CommRing R] {n : ℕ} (u : Perm (Fin n)) (x : MvPolynomial (Fin n) R) :
    rename u (alt x) = Perm.sign u • alt x := by
  unfold alt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun w => ?_
  simp only [Equiv.coe_mulLeft]
  rw [Units.smul_def, map_zsmul, rename_rename, ← Perm.coe_mul, Perm.sign_mul, mul_smul, smul_smul,
    Int.units_mul_self, one_smul, Units.smul_def]

private theorem antisymmetrizer_add {R : Type} [CommRing R] {n : ℕ} (x y : MvPolynomial (Fin n) R) :
    alt (x + y) = alt x + alt y := by
  simp only [alt, map_add (f := _), smul_add, Finset.sum_add_distrib]

private theorem antisymmetrizer_symmetric_mul {R : Type} [CommRing R] {n : ℕ} (z x : MvPolynomial (Fin n) R)
    (hz : z.IsSymmetric) : alt (z * x) = z * alt x := by
  simp only [alt, map_mul, hz _, Finset.mul_sum, mul_smul_comm]

private theorem eq_of_De_mul_eq_De_mul {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    (p q : MvPolynomial (Fin n) R) (h : De R n * p = De R n * q) : p = q :=
  by
    have hd : De R n = (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).det := by
      rw [Matrix.det_vandermonde, De, pairs, Finset.prod_filter, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      refine Finset.prod_congr ?_ fun _ _ => rfl
      ext j
      simp
    apply mul_left_cancel₀ ?_ h
    rw [hd, Matrix.det_vandermonde_ne_zero_iff]
    exact X_injective

theorem UpperTheory.V.AlgebraTools.hkDdProps :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ), (∀ x y : MvPolynomial (Fin n) R, dd (x + y) = dd x + dd y) ∧ (∀ z x : MvPolynomial (Fin n) R, z.IsSymmetric → dd (z * x) = z * dd x) ∧
      (∀ x : MvPolynomial (Fin n) R, (dd x).IsSymmetric) ∧
      ∃ D : MvPolynomial (Fin n) R →ₗ[symmetricSubalgebra (Fin n) R] symmetricSubalgebra (Fin n) R, ∀ x, (D x : MvPolynomial (Fin n) R) = dd x := by
  intro R _ _ n
  have hadd : ∀ x y : MvPolynomial (Fin n) R, dd (x + y) = dd x + dd y := by
    intro x y
    apply eq_of_De_mul_eq_De_mul
    rw [mul_add, UpperTheory.V.AlgebraTools.hkDdSpec, UpperTheory.V.AlgebraTools.hkDdSpec, UpperTheory.V.AlgebraTools.hkDdSpec, antisymmetrizer_add]
  have hmul : ∀ z x : MvPolynomial (Fin n) R, z.IsSymmetric → dd (z * x) = z * dd x := by
    intro z x hz
    apply eq_of_De_mul_eq_De_mul
    rw [UpperTheory.V.AlgebraTools.hkDdSpec, antisymmetrizer_symmetric_mul z x hz, mul_left_comm, UpperTheory.V.AlgebraTools.hkDdSpec]
  have hsym : ∀ x : MvPolynomial (Fin n) R, (dd x).IsSymmetric := by
    intro x w
    apply eq_of_De_mul_eq_De_mul
    have hd : De R n = (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).det := by
      rw [Matrix.det_vandermonde, De, pairs, Finset.prod_filter, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      refine Finset.prod_congr ?_ fun _ _ => rfl
      ext j
      simp
    have hw : rename w (De R n) = Perm.sign w • De R n := by
      rw [hd, AlgHom.map_det]
      have hm : (rename w : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).mapMatrix
          (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)) =
          (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).submatrix w id := by
        ext i j
        simp [Matrix.vandermonde_apply]
      rw [hm, Matrix.det_permute, Units.smul_def, zsmul_eq_mul]
    have e1 := congrArg (rename ⇑w) (UpperTheory.V.AlgebraTools.hkDdSpec R n x)
    rw [map_mul, hw, rename_alt, ← UpperTheory.V.AlgebraTools.hkDdSpec R n x,
      smul_mul_assoc] at e1
    exact (smul_left_cancel_iff _).mp e1
  refine ⟨hadd, hmul, hsym, ?_⟩
  refine ⟨{ toFun := fun x => ⟨dd x, (mem_symmetricSubalgebra _).mpr (hsym x)⟩
            map_add' := fun x y => Subtype.ext (hadd x y)
            map_smul' := fun c x => Subtype.ext ?_ }, fun x => rfl⟩
  simp only [RingHom.id_apply, Subalgebra.smul_def, SetLike.val_smul]
  exact hmul _ _ ((mem_symmetricSubalgebra _).mp c.2)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem one_place {O A N ι : Type} [CommRing O] [IsDomain O] [CommRing A] [AddCommGroup N] [Fintype ι] {n : ℕ}
    (e : MvPolynomial (Fin n) O →+* A) (Φ : A → A → N)
    (h1 : ∀ s (f : ι → A), Φ s (∑ m, f m) = ∑ m, Φ s (f m))
    (h2 : ∀ t (f : ι → A), Φ (∑ m, f m) t = ∑ m, Φ (f m) t)
    (h3 : ∀ s t z, z.IsSymmetric → Φ s (t * e z) = Φ (s * e z) t)
    {a c : ι → MvPolynomial (Fin n) O} (h : Hk.IsDual a c) (x : MvPolynomial (Fin n) O) (s t : A) :
    ∑ k, Φ (e (a k) * s) (e (c k) * t * e x) = ∑ k, Φ (e x * (e (a k) * s)) (e (c k) * t) := by
  have hd := UpperTheory.V.AlgebraTools.hkDualExp O n ι a c h
  have hs := (UpperTheory.V.AlgebraTools.hkDdProps O n).2.2.1
  have e1 : ∀ k, Φ (e (a k) * s) (e (c k) * t * e x)
      = ∑ m, Φ (e (a k * Hk.dd (c k * (x * a m))) * s) (e (c m) * t) := by
    intro k
    have : e (c k) * t * e x = ∑ m, e (c m) * t * e (Hk.dd (c k * (x * a m))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [mul_right_comm, ← map_mul, ← (hd (c k * x)).2, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, mul_right_comm, show a m * (c k * x) = c k * (x * a m) by ring]
    rw [this, h1]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [h3 _ _ _ (hs _), map_mul, mul_right_comm]
  rw [Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h2, ← Finset.sum_mul, ← map_sum, (hd _).1, map_mul, mul_assoc]

private theorem many_places {O A N ι : Type} [CommRing O] [IsDomain O] [CommRing A] [AddCommGroup N] [Fintype ι] {n q : ℕ}
    (e : Fin q → MvPolynomial (Fin n) O →+* A) (Φ : A → A → N)
    (h1 : ∀ s (f : ι → A), Φ s (∑ m, f m) = ∑ m, Φ s (f m))
    (h2 : ∀ t (f : ι → A), Φ (∑ m, f m) t = ∑ m, Φ (f m) t)
    (h3 : ∀ j s t z, z.IsSymmetric → Φ s (t * e j z) = Φ (s * e j z) t)
    {a c : ι → MvPolynomial (Fin n) O} (h : Hk.IsDual a c) (j : Fin q) (x : MvPolynomial (Fin n) O) :
    ∑ i : Fin q → ι, Φ (∏ j, e j (a (i j))) ((∏ j, e j (c (i j))) * e j x)
      = ∑ i : Fin q → ι, Φ (e j x * ∏ j, e j (a (i j))) (∏ j, e j (c (i j))) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := j.pos; omega⟩
  rw [← (Fin.insertNthEquiv (fun _ => ι) j).sum_comp, ← (Fin.insertNthEquiv (fun _ => ι) j).sum_comp,
    Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.prod_univ_succAbove _ j, Fin.insertNthEquiv_apply, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  exact one_place (e j) Φ h1 h2 (h3 j) h x _ _

private theorem esymm_root {O R B : Type} [CommRing O] [CommRing R] [Algebra O R] [CommRing B] {q n : ℕ} (β : R →+* B)
    (P : Fin q → Polynomial B) (j : Fin q) (k : ℕ) (hk : k ≤ n) :
    Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β (emb O R j (MvPolynomial.esymm (Fin n) O k)))
      = algebraMap B (MSplitAlg P n) ((-1) ^ k * (P j).coeff (n - k)) := by
  have h0 := congrArg (fun p => p.coeff (n - k)) (MSplitAlg.prod_root P n j)
  have hc : Multiset.card (Finset.univ.val.map fun i : Fin n => MSplitAlg.root P n j i) = n := by simp
  have h1 := Multiset.prod_X_sub_C_coeff (Finset.univ.val.map fun i : Fin n => MSplitAlg.root P n j i)
    (k := n - k) (by rw [hc]; omega)
  rw [hc, Multiset.map_map, show n - (n - k) = k by omega, Finset.esymm_map_val] at h1
  simp only [Polynomial.coeff_map] at h0
  rw [map_mul, ← h0, Finset.prod_eq_multiset_prod]
  simp only [Function.comp_def] at h1
  rw [h1, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [emb, MvPolynomial.esymm, MSplitAlg.root, map_sum, map_prod]

theorem UpperTheory.V.Pa.Lev.multiPsi :
    ∀ (O R B M V : Type) [CommRing O] [IsDomain O] [CommRing R] [Algebra O R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (tr : V →+ M) (ι : Type) [Fintype ι] (a c : ι → MvPolynomial (Fin n) O), Hk.IsDual a c → (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) → (∀ (t : R) v, tr (t • v) = β t • tr v) → (∀ j k, k ≤ n → ∀ v, tr (act (emb O R j (MvPolynomial.esymm (Fin n) O k)) v) = ((-1) ^ k * (P j).coeff (n - k)) • tr v) → ∀ ψ : V →+ MSplitAlg P n ⊗[B] M, (∀ v, ψ v = ∑ i : Fin q → ι, Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β (∏ j, emb O R j (a (i j)))) ⊗ₜ tr (act (∏ j, emb O R j (c (i j))) v)) → ∀ (t : PU R q n) v, ψ (act t v) = Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t) • ψ v := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β P act tr ι _ a c hd _ _ hβ he ψ hψ
  let π : PU R q n →+* MSplitAlg P n := (Ideal.Quotient.mk (mSplitIdeal P n)).comp (MvPolynomial.map β)
  have hπ : ∀ t, Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t) = π t := fun _ => rfl
  simp only [hπ] at hψ ⊢
  have sc : ∀ (b : B) (y : MSplitAlg P n) (m : M), y ⊗ₜ[B] (b • m) = (y * algebraMap B _ b) ⊗ₜ[B] m := by
    intro b y m
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
  have hC : ∀ (r : R) (y : MSplitAlg P n) w,
      y ⊗ₜ[B] tr (act (MvPolynomial.C r) w) = (y * π (MvPolynomial.C r)) ⊗ₜ[B] tr w := by
    intro r y w
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply, hβ, sc, ← hπ,
      MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
    rfl
  have bal : ∀ j (z : MvPolynomial (Fin n) O), z.IsSymmetric → ∀ (y : MSplitAlg P n) w,
      y ⊗ₜ[B] tr (act (emb O R j z) w) = (y * π (emb O R j z)) ⊗ₜ[B] tr w := by
    intro j z hz
    obtain ⟨p, hp⟩ := MvPolynomial.esymmAlgHom_surjective O (σ := Fin n) (n := n) (by simp) ⟨z, hz⟩
    obtain rfl : z = (MvPolynomial.esymmAlgHom (Fin n) O n p : MvPolynomial (Fin n) O) := by rw [hp]
    clear hp hz
    rw [MvPolynomial.esymmAlgHom_apply]
    induction p using MvPolynomial.induction_on with
    | C r =>
      have : emb O R j (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) O (i + 1))
          (MvPolynomial.C r : MvPolynomial (Fin n) O)) = MvPolynomial.C (algebraMap O R r) := by simp [emb]
      rw [this]
      exact hC _
    | add p p' hp hp' =>
      intro y w
      rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, map_add (f := _), TensorProduct.tmul_add, hp, hp', mul_add,
        TensorProduct.add_tmul]
    | mul_X p i hp =>
      intro y w
      rw [map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply, hp, MvPolynomial.aeval_X, he j _ i.2, sc,
        ← esymm_root (O := O) β P j _ i.2, hπ, mul_assoc]
  intro t
  induction t using MvPolynomial.induction_on with
  | C r =>
    intro v
    rw [hψ, hψ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, hC, TensorProduct.smul_tmul',
      smul_eq_mul, mul_comm]
  | add p p' hp hp' =>
    intro v
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, map_add (f := _), hp, hp', add_smul]
  | mul_X p ji hp =>
    intro v
    obtain ⟨j, i⟩ := ji
    have hX : (MvPolynomial.X (j, i) : PU R q n) = emb O R j (MvPolynomial.X i) := by simp [emb]
    rw [map_mul, map_mul, Module.End.mul_apply, hp, mul_smul, hX, hψ, hψ, Finset.smul_sum (r := π (emb O R j _))]
    congr 1
    have := many_places (emb O R) (fun s t => π s ⊗ₜ[B] tr (act t v))
      (fun s f => by simp only [map_sum, LinearMap.sum_apply, TensorProduct.tmul_sum])
      (fun s f => by simp only [map_sum, TensorProduct.sum_tmul])
      (fun j s t z hz => by
        show π s ⊗ₜ[B] tr (act (t * emb O R j z) v) = π (s * emb O R j z) ⊗ₜ[B] tr (act t v)
        rw [mul_comm t, map_mul, Module.End.mul_apply, bal j z hz, map_mul]) hd j (MvPolynomial.X i)
    simp only [map_mul, Module.End.mul_apply] at this
    rw [this]
    simp only [TensorProduct.smul_tmul', smul_eq_mul]
end
