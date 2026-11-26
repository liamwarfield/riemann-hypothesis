module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpStab
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPushforward

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIwahoriTorusProjection
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem torus_uniq {G : Type} [Group G] (I : Iwa G) {y y' x x' : G} {t t' : I.T} (hy : y ∈ I.Nm 0)
    (hy' : y' ∈ I.Nm 0) (hx : x ∈ I.N) (hx' : x' ∈ I.N) (h : y * t * x = y' * t' * x') : t' = t := by
  have h1 : x = (t : G)⁻¹ * y⁻¹ * (y' * t' * x') := by rw [← h]; group
  have h0 := (I.uniq (x * x'⁻¹) (I.N_le (mul_mem hx (inv_mem hx'))) ((t' : G)⁻¹ * t)
    (I.T_le (mul_mem (inv_mem t'.2) t.2)) ((t : G)⁻¹ * (y'⁻¹ * y) * (t : G)⁻¹⁻¹)
    (I.T_Nm 0 _ (inv_mem t.2) _ (mul_mem (inv_mem hy') hy)) (by rw [h1]; group)).2
  exact Subtype.ext (inv_mul_eq_one.1 h0)

private theorem torus_ex {G : Type} [Group G] (I : Iwa G) {b : G} (hb : b ∈ I.Iw 0) :
    ∃ t : I.T, ∃ y ∈ I.Nm 0, ∃ x ∈ I.N, b = y * t * x := by
  obtain ⟨x, hx, t, ht, y, hy, h⟩ := (UpperTheory.V.Hi.iwMem G I 0 b⁻¹).1.1 (inv_mem hb)
  refine ⟨⟨t⁻¹, inv_mem ht⟩, y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, ?_⟩
  rw [← inv_inv b, h]
  group

private theorem torus_fn {G : Type} [Group G] (I : Iwa G) :
    ∃ tt : G → I.T, ∀ (t : I.T), ∀ y ∈ I.Nm 0, ∀ x ∈ I.N, tt (y * t * x) = t := by
  classical
  refine ⟨fun b => if h : ∃ t : I.T, ∃ y ∈ I.Nm 0, ∃ x ∈ I.N, b = y * t * x then h.choose else 1, ?_⟩
  intro t y hy x hx
  have h : ∃ t' : I.T, ∃ y' ∈ I.Nm 0, ∃ x' ∈ I.N, y * t * x = y' * t' * x' := ⟨t, y, hy, x, hx, rfl⟩
  simp only [dif_pos h]
  obtain ⟨y', hy', x', hx', e⟩ := h.choose_spec
  exact torus_uniq I hy hy' hx hx' e

theorem UpperTheory.exists_iwahori_torus_projection :
    ∀ (G : Type) [Group G] (I : Iwa G), ∃ tt : G → I.T, tt 1 = 1 ∧ ∀ b ∈ I.Iw 0, (∀ s : I.T, tt (s * b) = s * tt b ∧ tt (b * s) = tt b * s) ∧ (∀ x ∈ I.N, tt (b * x) = tt b) ∧ ∀ c, ∀ y ∈ I.Nm c, ∃ s : I.T, (s : G) ∈ I.Tc c ∧ tt (b * y) = tt b * s := by
  intro G _ I
  obtain ⟨tt, htt⟩ := torus_fn I
  refine ⟨tt, by simpa using htt 1 1 (one_mem _) 1 (one_mem _), fun b hb => ?_⟩
  obtain ⟨t, y, hy, x, hx, rfl⟩ := torus_ex I hb
  rw [htt t y hy x hx]
  refine ⟨fun s => ⟨?_, ?_⟩, fun x' hx' => ?_, fun c y' hy' => ?_⟩
  · rw [← htt (s * t) _ (I.T_Nm 0 s s.2 y hy) x hx]
    congr 1
    rw [Subgroup.coe_mul]
    group
  · rw [← htt (t * s) y hy _ (I.T_N _ (inv_mem s.2) x hx)]
    congr 1
    rw [Subgroup.coe_mul]
    group
  · rw [mul_assoc]
    exact htt t y hy _ (mul_mem hx hx')
  · obtain ⟨x2, hx2, s, hs, y2, hy2, h⟩ := I.swap c y'⁻¹ (inv_mem hy') x⁻¹ (inv_mem hx)
    refine ⟨⟨s⁻¹, inv_mem (I.Tc_le c hs)⟩, inv_mem hs, ?_⟩
    rw [← htt (t * ⟨s⁻¹, inv_mem (I.Tc_le c hs)⟩) _
      (mul_mem hy (I.T_Nm 0 t t.2 _ (inv_mem (I.Nm_anti (Nat.zero_le c) hy2)))) _ (inv_mem hx2)]
    congr 1
    have e : x * y' = (x2 * s * y2)⁻¹ := by rw [← h]; group
    rw [mul_assoc, e, Subgroup.coe_mul]
    group
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HarishChandraProjQuantumDetEqProd
open GroundTheory.Automorphic.HarishChandra in
private noncomputable def UpperTheory.V.Af.CuspFin.vermaRep {n : ℕ} (lam : Fin n → ℂ) :
    U n →ₐ[ℂ] Module.End ℂ (U n ⧸ vermaIdeal lam) where
  toFun x := (vermaIdeal lam).mapQ (vermaIdeal lam) (LinearMap.mulLeft ℂ x)
    (fun _ hy => mul_mem_vermaIdeal lam x hy)
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    simp
  map_mul' a b := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    change (Submodule.Quotient.mk (a * b * y) : U n ⧸ vermaIdeal lam) = Submodule.Quotient.mk (a * (b * y))
    rw [mul_assoc]
  map_zero' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    simp
  map_add' a b := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    change (Submodule.Quotient.mk ((a + b) * y) : U n ⧸ vermaIdeal lam) =
      Submodule.Quotient.mk (a * y) + Submodule.Quotient.mk (b * y)
    rw [add_mul, Submodule.Quotient.mk_add]
  commutes' r := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    change (Submodule.Quotient.mk (algebraMap ℂ (U n) r * y) : U n ⧸ vermaIdeal lam) =
      r • Submodule.Quotient.mk y
    rw [← Algebra.smul_def, Submodule.Quotient.mk_smul]

open GroundTheory.Automorphic.HarishChandra in
private theorem UpperTheory.V.Af.CuspFin.vermaRep_one {n : ℕ} (lam : Fin n → ℂ) (x : U n) :
    UpperTheory.V.Af.CuspFin.vermaRep lam x (Submodule.Quotient.mk 1) = Submodule.Quotient.mk x := by
  change Submodule.Quotient.mk (x * 1) = _
  rw [mul_one]

open GroundTheory.Automorphic.HarishChandra in
private theorem UpperTheory.V.Af.CuspFin.one_notMem_vermaIdeal {n : ℕ} (lam : Fin n → ℂ) :
    (1 : U n) ∉ vermaIdeal lam := by
  intro h
  have h0 := vermaCoord_vermaIdeal lam h
  have hnu : ¬ HasUpper (0 : Fin n × Fin n →₀ ℕ) := by
    rintro ⟨b, -, hne⟩
    exact hne rfl
  have hd : diagExp (0 : Fin n × Fin n →₀ ℕ) = 0 := by ext; simp
  rw [← canon_zero, vermaCoord_canon_of_not lam hnu, hd, Finsupp.single_eq_zero] at h0
  simp at h0

open GroundTheory.Automorphic.HarishChandra UpperTheory.V.Af.CuspFin in
theorem UpperTheory.harishChandraProj_quantumDet_eq_prod :
    ∀ (n : ℕ) (u : ℂ), GroundTheory.Automorphic.HarishChandra.hcProjLin (Formalism.REAL.qdet (fun i j : Fin n => GroundTheory.Automorphic.HarishChandra.e (i, j)) u) = ∏ k : Fin n, (MvPolynomial.C (u - (k : ℂ)) + MvPolynomial.X k) := by
  intro n u
  refine MvPolynomial.funext fun lam => ?_
  have hgl : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) := fun a b c d => e_mul_sub_mul (a, b) (c, d)
  have hgl' : Formalism.REAL.GlRel (fun i j : Fin n => vermaRep lam (e (i, j))) := fun a b c d => by
    have h := congrArg (vermaRep lam) (hgl a b c d)
    simp only [map_sub, map_mul, apply_ite (vermaRep lam), map_zero] at h
    exact h
  have hup : ∀ a, IsUpper a → vermaRep lam (e a) (Submodule.Quotient.mk 1) = 0 := fun a ha => by
    rw [vermaRep_one, Submodule.Quotient.mk_eq_zero]
    exact nPlusU_le_vermaIdeal lam (Submodule.subset_span ⟨1, a, ha, one_mul _⟩)
  have hH : ∀ k, vermaRep lam (e (k, k)) (Submodule.Quotient.mk 1) =
      lam k • (Submodule.Quotient.mk 1 : U n ⧸ vermaIdeal lam) := fun k => by
    rw [vermaRep_one, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← Algebra.algebraMap_eq_smul_one]
    simpa using mul_e_sub_mem_vermaIdeal lam 1 k
  have h1 := rep_apply_of_highestWeight (vermaRep lam) lam hup hH
    (z := Formalism.REAL.qdet (fun i j : Fin n => e (i, j)) u)
    (fun k => (Formalism.REAL.qDetCentral _ n _ hgl u k k).symm)
  have h2 := Formalism.REAL.qDetHW _ n _ lam (Submodule.Quotient.mk 1) hgl'
    ⟨hH, fun a b hab => hup (a, b) hab⟩ u
  rw [map_qdet, h2] at h1
  have hv : (Submodule.Quotient.mk 1 : U n ⧸ vermaIdeal lam) ≠ 0 := fun h =>
    one_notMem_vermaIdeal lam ((Submodule.Quotient.mk_eq_zero _).1 h)
  rw [← smul_left_injective ℂ hv h1]
  simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAdicLimitMemAutomorphicSpace
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem spC_lim {A : Type} [CommRing A] (I : Ideal A) [IsPrecomplete I A] (x : ℕ → A)
    (h : ∀ k, x (k + 1) - x k ∈ I ^ k) : ∃ L, ∀ k, L - x k ∈ I ^ k := by
  have h1 : ∀ m n, m ≤ n → x n - x m ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem (Ideal.pow_le_pow_right hmn (h n)) ih
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance (f := x) (fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact neg_mem (h1 m n hmn))
  refine ⟨L, fun k => ?_⟩
  have := hL k
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  rw [← neg_sub]
  exact neg_mem this

private theorem spC_eq {A : Type} [CommRing A] (I : Ideal A) [IsHausdorff I A] {x y : A}
    (h : ∀ k, x - y ∈ I ^ k) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact h k

theorem UpperTheory.exists_adic_limit_mem_automorphicSpace :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (a : ℕ → X.Fn A m), (∀ k, a k ∈ X.Sp τ θ U) → (∀ k, a (k + 1) - a k ∈ X.valIn A m k) → ∃ L ∈ X.Sp τ θ U, ∀ k, L - a k ∈ X.valIn A m k := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ U a ha hc
  have hv : ∀ (k : ℕ) (f : X.Fn A m), f ∈ X.valIn A m k ↔ ∀ g i, f g i ∈ maximalIdeal A ^ k := by
    intro k f
    simp [Frame.valIn, Submodule.mem_pi]
  choose L hL using fun g i => spC_lim (maximalIdeal A) (fun k => a k g i) fun k => (hv _ _).1 (hc k) g i
  have key : ∀ φ ψ : X.Fn A m →ₗ[A] X.Fn A m, (∀ k, ∀ f ∈ X.valIn A m k, φ f ∈ X.valIn A m k) →
      (∀ k, ∀ f ∈ X.valIn A m k, ψ f ∈ X.valIn A m k) → (∀ k, φ (a k) = ψ (a k)) → φ L = ψ L := by
    intro φ ψ h1 h2 h3
    funext g i
    refine spC_eq (maximalIdeal A) fun k => ?_
    have hk : L - a k ∈ X.valIn A m k := (hv _ _).2 fun g i => hL g i k
    have := sub_mem (h1 k _ hk) (h2 k _ hk)
    rw [map_sub, map_sub, h3 k, sub_sub_sub_cancel_right] at this
    exact (hv _ _).1 this g i
  have hrp : ∀ b k, ∀ f ∈ X.valIn A m k, X.rp A m b f ∈ X.valIn A m k := fun b k f hf =>
    (hv _ _).2 fun g i => (hv _ _).1 hf _ i
  refine ⟨L, ⟨⟨fun γ g => ?_, fun x hx => ?_, fun t => ?_, fun k => ?_⟩, fun u hu => ?_⟩,
    fun k => (hv _ _).2 fun g i => hL g i k⟩
  · funext i
    refine spC_eq (maximalIdeal A) fun k => ?_
    have := sub_mem (hL (X.glob γ * g) i k) (hL g i k)
    rwa [(ha k).1.1 γ g, sub_sub_sub_cancel_right] at this
  · exact key _ LinearMap.id (hrp x) (fun _ _ h => h) fun k => (ha k).1.2.1 x hx
  · exact key _ ((((θ t)⁻¹ : Aˣ) : A) • LinearMap.id) (hrp t) (fun _ _ h => Submodule.smul_mem _ _ h)
      fun k => (ha k).1.2.2.1 t
  · obtain ⟨c, h⟩ := (ha k).1.2.2.2 k
    refine ⟨c, fun y hy g i => ?_⟩
    have := add_mem (sub_mem (hL (g * (1, y)) i k) (hL g i k)) (h y hy g i)
    convert this using 1
    ring
  · refine key _ LinearMap.id (fun k f hf => (hv _ _).2 fun g i => ?_) (fun _ _ h => h) fun k => (ha k).2 u hu
    rw [Frame.ra_apply]
    simp only [mulVec, dotProduct]
    exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ((hv _ _).1 hf _ j)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPairCorrespondence
open MulAction UpperTheory.V.Z.Sym

private structure PairSp (H G : Type) [Group G] (U : Subgroup G) : Type where
  fst : H
  snd : G ⧸ U

@[instance_reducible] private def pairAct {H G : Type} [Group H] [Group G] (j : H →* G) (U : Subgroup G) :
    MulAction H (PairSp H G U) where
  smul h p := ⟨h * p.1 * h⁻¹, j h • p.2⟩
  one_smul p := by
    show (⟨(1 : H) * p.1 * (1 : H)⁻¹, j 1 • p.2⟩ : PairSp H G U) = p
    simp
  mul_smul a b p := by
    show (⟨a * b * p.1 * (a * b)⁻¹, j (a * b) • p.2⟩ : PairSp H G U) =
      ⟨a * (b * p.1 * b⁻¹) * a⁻¹, j a • j b • p.2⟩
    simp [mul_assoc, mul_smul]

private theorem out_eq_mul {G : Type} [Group G] (U : Subgroup G) (g : G) :
    ∃ u ∈ U, ((g : G ⧸ U).out : G) = g * u := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U g
  exact ⟨h, h.2, hh⟩

private theorem pair_inv_mul_eq_of_mul_self_eq_one {H G : Type} [Group H] [Group G] (a b o u : G) (key : a⁻¹ * (b * a) = b) :
    (a * o * u)⁻¹ * b * (a * o * u) = u⁻¹ * (o⁻¹ * b * o) * u := by
  calc (a * o * u)⁻¹ * b * (a * o * u) = u⁻¹ * o⁻¹ * (a⁻¹ * (b * a)) * o * u := by group
    _ = u⁻¹ * (o⁻¹ * b * o) * u := by rw [key]; group

theorem UpperTheory.orbitalFiber_pair_correspondence :
    UpperTheory.V.Z.Sym.Glob.Fib.Pair := by
  classical
  intro H G I _ _ j H₀ U c f δ Hi _ φ hcen hfix hc hf hfin hT hidx hrange hδ hcov
  letI : MulAction H (PairSp H G U) := pairAct j U
  letI : MulAction H (G ⧸ U) := MulAction.compHom (G ⧸ U) j
  letI : ∀ i, MulAction (Hi i) (G ⧸ U) := fun i => MulAction.compHom (G ⧸ U) (j.comp (φ i))
  have hnorm : H₀.Normal := ⟨fun n hn g => by
    have hc' := Subgroup.mem_center_iff.1 (hcen hn) g
    rw [hc', mul_inv_cancel_right]
    exact hn⟩
  have hout : ∀ (a : G) (y : G ⧸ U), ∃ u ∈ U, ((a • y : G ⧸ U).out) = a * y.out * u := by
    intro a y
    have hy : (a • y : G ⧸ U) = ((a * y.out : G) : G ⧸ U) := by
      conv_lhs => rw [← QuotientGroup.out_eq' y]
      rfl
    rw [hy]
    exact out_eq_mul U _
  let K' : PairSp H G U → ℂ := fun p => c p.1 * f (p.2.out⁻¹ * j p.1 * p.2.out)
  have hKinv : ∀ (h : H) (p : PairSp H G U), K' (h • p) = K' p := by
    intro h p
    obtain ⟨u, hu, he⟩ := hout (j h) p.2
    show c (h * p.1 * h⁻¹) * f ((j h • p.2).out⁻¹ * j (h * p.1 * h⁻¹) * (j h • p.2).out) =
      c p.1 * f (p.2.out⁻¹ * j p.1 * p.2.out)
    rw [hc, he, map_mul, map_mul, map_inv]
    congr 1
    rw [show (j h * p.2.out * u)⁻¹ * (j h * j p.1 * (j h)⁻¹) * (j h * p.2.out * u) =
        u⁻¹ * (p.2.out⁻¹ * j p.1 * p.2.out) * u by group]
    exact hf u hu _
  have hfib : ∀ x : G ⧸ U, {p : PairSp H G U | p.2 = x ∧ K' p ≠ 0}.Finite := by
    intro x
    refine ((hfin x.out).image (fun γ => (⟨γ, x⟩ : PairSp H G U))).subset ?_
    rintro ⟨γ, y⟩ ⟨hy, hne⟩
    change y = x at hy
    subst hy
    exact ⟨γ, hne, rfl⟩
  obtain ⟨T, hTc⟩ := hT
  have hT'fin : (⋃ s ∈ T, {p : PairSp H G U | p.2 = (s : G ⧸ U) ∧ K' p ≠ 0}).Finite :=
    Set.Finite.biUnion T.finite_toSet (fun s _ => hfib _)
  have hcoverP : ∀ p : PairSp H G U, K' p ≠ 0 → ∃ h : H, ∃ s ∈ hT'fin.toFinset, p = h • s := by
    intro p hp
    obtain ⟨γ0, s, hs, u, hu, he⟩ := hTc p.2.out
    refine ⟨γ0, γ0⁻¹ • p, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset, Set.mem_iUnion₂]
      refine ⟨s, hs, ?_, ?_⟩
      · show j γ0⁻¹ • p.2 = (s : G ⧸ U)
        conv_lhs => rw [← QuotientGroup.out_eq' p.2, he]
        show ((j γ0⁻¹ * (j γ0 * s * u) : G) : G ⧸ U) = s
        rw [QuotientGroup.eq, map_inv]
        simpa [mul_assoc] using U.inv_mem hu
      · rw [hKinv]
        exact hp
    · rw [smul_smul, mul_inv_cancel, one_smul]
  have hfixP : ∀ z ∈ H₀, ∀ p : PairSp H G U, z • p = p := by
    intro z hz p
    obtain ⟨γ, y⟩ := p
    show (⟨z * γ * z⁻¹, j z • y⟩ : PairSp H G U) = ⟨γ, y⟩
    rw [← Subgroup.mem_center_iff.1 (hcen hz) γ, mul_inv_cancel_right, hfix z hz y]
  have hpush := UpperTheory.orbitalFiber_pushforward H (PairSp H G U) (G ⧸ U) H₀ (fun p => p.2) K' hnorm
    (fun _ _ => rfl) hfixP hKinv ⟨hT'fin.toFinset, hcoverP⟩ hfib (fun p _ => hidx p.2)
  have hfibsum : ∀ x : G ⧸ U, (∑ᶠ (p : PairSp H G U) (_ : p.2 = x), K' p) =
      ∑ᶠ γ : H, c γ * f (x.out⁻¹ * j γ * x.out) := by
    intro x
    have hr : ∀ p : PairSp H G U,
        (p.2 = x) = (p ∈ Set.range (fun γ : H => (⟨γ, x⟩ : PairSp H G U))) := by
      intro p
      apply propext
      constructor
      · intro hp
        exact ⟨p.1, by rw [← hp]⟩
      · rintro ⟨γ, rfl⟩
        rfl
    simp only [hr]
    rw [finsum_mem_range (fun a b hab => congrArg PairSp.fst hab)]
  have hcomm : ∀ i (a : Hi i), φ i a * δ i * (φ i a)⁻¹ = δ i := by
    intro i a
    rw [(hrange i (φ i a)).1 ⟨a, rfl⟩, mul_inv_cancel_right]
  have hequi : ∀ i (a : Hi i) (y : G ⧸ U),
      (⟨δ i, a • y⟩ : PairSp H G U) = φ i a • (⟨δ i, y⟩ : PairSp H G U) := by
    intro i a y
    show (⟨δ i, j (φ i a) • y⟩ : PairSp H G U) = ⟨φ i a * δ i * (φ i a)⁻¹, j (φ i a) • y⟩
    rw [hcomm]
  have hkiinv : ∀ i (a : Hi i) (y : G ⧸ U),
      c (δ i) * f ((a • y).out⁻¹ * j (δ i) * (a • y).out) = c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) := by
    intro i a y
    obtain ⟨u, hu, he⟩ := hout (j (φ i a)) y
    show c (δ i) * f ((j (φ i a) • y).out⁻¹ * j (δ i) * (j (φ i a) • y).out) = _
    rw [he, pair_inv_mul_eq_of_mul_self_eq_one (H := H) _ _ _ _ ?_, hf u hu]
    have h1 := (hrange i (φ i a)).1 ⟨a, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← h1, inv_mul_cancel_left]
  have hcovD : ∀ p : PairSp H G U, K' p ≠ 0 → ∃ i, ∃ y : G ⧸ U, ∃ h : H,
      c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) ≠ 0 ∧ p = h • (⟨δ i, y⟩ : PairSp H G U) := by
    rintro ⟨γ, y⟩ hp
    obtain ⟨i, h, hγ⟩ := hcov γ y.out hp
    refine ⟨i, j h⁻¹ • y, h, ?_, ?_⟩
    · have h2 := hKinv h⁻¹ ⟨γ, y⟩
      have h3 : h⁻¹ * γ * h⁻¹⁻¹ = δ i := by rw [hγ]; group
      change c (h⁻¹ * γ * h⁻¹⁻¹) * f ((j h⁻¹ • y).out⁻¹ * j (h⁻¹ * γ * h⁻¹⁻¹) * (j h⁻¹ • y).out) =
        K' ⟨γ, y⟩ at h2
      rw [h3] at h2
      rw [h2]
      exact hp
    · show (⟨γ, y⟩ : PairSp H G U) = ⟨h * δ i * h⁻¹, j h • j h⁻¹ • y⟩
      rw [← hγ, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have huniq : ∀ (i i' : I) (y y' : G ⧸ U) (h : H),
      c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) ≠ 0 → c (δ i') * f (y'.out⁻¹ * j (δ i') * y'.out) ≠ 0 →
      h • (⟨δ i, y⟩ : PairSp H G U) = ⟨δ i', y'⟩ → i = i' ∧ h ∈ (φ i).range := by
    intro i i' y y' h _ _ he
    have h1 : h * δ i * h⁻¹ = δ i' := congrArg PairSp.fst he
    have hii := hδ i i' h h1.symm
    subst hii
    refine ⟨rfl, (hrange i h).2 ?_⟩
    calc h * δ i = h * δ i * h⁻¹ * h := by group
      _ = δ i * h := by rw [h1]
  have hdec := UpperTheory.orbitalFiber_decomposition H (PairSp H G U) I H₀ K' Hi (fun _ => G ⧸ U) φ
    (fun i y => (⟨δ i, y⟩ : PairSp H G U))
    (fun i y => c (δ i) * f (y.out⁻¹ * j (δ i) * y.out)) hnorm hKinv ⟨hT'fin.toFinset, hcoverP⟩
    hequi (fun _ _ _ hab => congrArg PairSp.snd hab) hkiinv (fun _ _ _ => rfl) hcovD huniq
  show gq H₀ (fun y : G ⧸ U => ∑ᶠ γ : H, c γ * f (y.out⁻¹ * j γ * y.out)) = _
  simp only [← hfibsum]
  rw [← hpush, hdec]
  apply finsum_congr
  intro i
  exact (UpperTheory.orbitalFiber_of_bot (Hi i) (G ⧸ U) (Subgroup.comap (φ i) H₀)
    (fun y => f (y.out⁻¹ * j (δ i) * y.out))).1 (c (δ i))
end
