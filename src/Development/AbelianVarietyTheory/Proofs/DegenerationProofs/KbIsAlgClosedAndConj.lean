module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem splits_of_monic_OO {q : (OO p)[X]} (hq : q.Monic) : q.Splits := by
  refine Splits.of_splits_map_of_injective (i := (OO p).subtype) Subtype.val_injective
    (IsAlgClosed.splits _) fun a ha => ?_
  have h : IsIntegral (OO p) a := ⟨q, hq, by
    have := isRoot_of_mem_roots ha
    rwa [IsRoot, Polynomial.eval_map] at this⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact ⟨y, hy⟩

theorem exists_root_residue_OO {q : (OO p)[X]} (hq : q.Monic) {b : kb p}
    (hb : q.eval₂ (residue (OO p)) b = 0) : ∃ a : OO p, q.eval a = 0 ∧ residue (OO p) a = b := by
  have h0 : q.map (residue (OO p)) ≠ 0 := (hq.map _).ne_zero
  have h : b ∈ (q.map (residue (OO p))).roots := by
    rw [mem_roots h0, IsRoot, Polynomial.eval_map, hb]
  rw [(splits_of_monic_OO hq).roots_map_of_ne_zero h0, Multiset.mem_map] at h
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, isRoot_of_mem_roots ha, rfl⟩

theorem isAlgClosed_kb : IsAlgClosed (kb p) := by
  refine IsAlgClosed.of_exists_root _ fun f hf hirr => ?_
  obtain ⟨q, hq, -, hmon⟩ := lifts_and_degree_eq_and_monic
    (mem_lifts_of_surjective (residue_surjective (R := OO p)) f) hf
  have hs : f.Splits := hq ▸ (splits_of_monic_OO hmon).map _
  exact hs.exists_eval_eq_zero (degree_pos_of_irreducible hirr).ne'

theorem charP_kb : CharP (kb p) p :=
  (CharP.charP_iff_prime_eq_zero Fact.out).2 GlobalTheory.ZH.natCast_residueField_OO

theorem exists_pow_eq_one_kb (x : kb p) (hx : x ≠ 0) : ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1 := by
  haveI := charP_kb (p := p)
  letI := ZMod.algebra (kb p) p
  have h : (algebraMap (ZMod p) (kb p)).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (Int.castRingHom (ZMod p)) _ ?_
    rw [RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom _)]
    exact GlobalTheory.ZH.isIntegral_int_residueField_OO
  have h' : IsIntegral (ZMod p) x := h x
  let K := IntermediateField.adjoin (ZMod p) {x}
  haveI : FiniteDimensional (ZMod p) K := IntermediateField.adjoin.finiteDimensional h'
  haveI : Finite K := Module.finite_of_finite (ZMod p)
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h0 => hx (congrArg Subtype.val h0)
  obtain ⟨n, hn, e⟩ := (isOfFinOrder_of_finite (Units.mk0 y hy)).exists_pow_eq_one
  exact ⟨n, hn, by simpa [y] using congrArg (fun u : Kˣ => ((u : K) : kb p)) e⟩

theorem algEquiv_mem_OO (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {x : PadicAlgCl p} (hx : x ∈ OO p) :
    σ x ∈ OO p := by
  rw [GlobalTheory.ZH.mem_OO_iff, ← GlobalTheory.isIntegral_padicInt_iff_norm_le_one] at hx ⊢
  exact hx.map (σ.toAlgHom.restrictScalars ℤ_[p])

noncomputable def restrictOO (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : OO p ≃+* OO p where
  toFun x := ⟨σ x, algEquiv_mem_OO σ x.2⟩
  invFun x := ⟨σ.symm x, algEquiv_mem_OO σ.symm x.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul σ (x : PadicAlgCl p) y)
  map_add' x y := Subtype.ext (map_add σ (x : PadicAlgCl p) y)

theorem exists_int_map_eq_kb (q : ℤ_[p][X]) : ∃ g : ℤ[X], g.map (Int.castRingHom (kb p)) =
    q.map ((residue (OO p)).comp (GlobalTheory.ZH.padicIntToOO p)) := by
  rw [← mem_lifts, lifts_iff_coeff_lifts]
  intro n
  rw [coeff_map]
  have h1 := PadicInt.sub_zmodRepr_mem (q.coeff n)
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 := congrArg ((residue (OO p)).comp (GlobalTheory.ZH.padicIntToOO p)) hc
  rw [map_sub, map_mul, map_natCast, map_natCast, GlobalTheory.ZH.natCast_residueField_OO, zero_mul, sub_eq_zero] at h2
  exact ⟨((q.coeff n).zmodRepr : ℤ), by rw [h2]; simp⟩

theorem exists_residue_restrictOO_eq (a : OO p) (b' : kb p)
    (h : ∀ g : ℤ[X], aeval (residue (OO p) a) g = 0 → aeval b' g = 0) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, residue (OO p) (restrictOO σ a) = b' := by
  have ha : IsIntegral ℤ_[p] (a : PadicAlgCl p) :=
    (GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).2 ((GlobalTheory.ZH.mem_OO_iff _).1 a.2)
  set f := minpoly ℤ_[p] (a : PadicAlgCl p) with hf
  have key : ∀ c : OO p, (((f.map (GlobalTheory.ZH.padicIntToOO p)).eval c : OO p) : PadicAlgCl p) =
      aeval (c : PadicAlgCl p) f := fun c => by
    rw [Polynomial.eval_map]
    exact hom_eval₂ f (GlobalTheory.ZH.padicIntToOO p) (OO p).subtype c
  obtain ⟨g, hg⟩ := exists_int_map_eq_kb f
  have e : ∀ b : kb p, aeval b g = (f.map (GlobalTheory.ZH.padicIntToOO p)).eval₂ (residue (OO p)) b := fun b => by
    rw [eval₂_map, ← Polynomial.eval_map, ← hg, Polynomial.eval_map]
    rfl
  have h1 : aeval (residue (OO p) a) g = 0 := by
    have : (f.map (GlobalTheory.ZH.padicIntToOO p)).eval a = 0 := Subtype.ext ((key a).trans (minpoly.aeval _ _))
    rw [e, eval₂_hom, this, map_zero]
  obtain ⟨a', ha', rfl⟩ := exists_root_residue_OO ((minpoly.monic ha).map (GlobalTheory.ZH.padicIntToOO p))
    ((e b').symm.trans (h g h1))
  have h2 : aeval (a' : PadicAlgCl p) (minpoly ℚ_[p] (a : PadicAlgCl p)) = 0 := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] ha, aeval_map_algebraMap, ← hf, ← key, ha']
    rfl
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _) h2
  exact ⟨σ, congrArg _ (Subtype.ext hσ)⟩

theorem exists_ringEquiv_residue_eq (F : Type) [Field F] [Finite F] (r r' : F →+* kb p) :
    ∃ σ : OO p ≃+* OO p, ∀ (x : F) (a : OO p), residue (OO p) a = r x → residue (OO p) (σ a) = r' x := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_monoid_generator (α := Fˣ)
  obtain ⟨a₀, ha₀⟩ := residue_surjective (r u)
  obtain ⟨σ, hσ⟩ := exists_residue_restrictOO_eq a₀ (r' u) fun g hg => by
    rw [ha₀] at hg
    have h1 := aeval_algHom_apply r.toIntAlgHom (u : F) g
    have h2 := aeval_algHom_apply r'.toIntAlgHom (u : F) g
    have h3 : aeval (u : F) g = 0 := r.injective ((h1.symm.trans hg).trans (map_zero r).symm)
    exact h2.trans (by rw [h3, map_zero])
  refine ⟨restrictOO σ, fun x a ha => ?_⟩
  let τ := ResidueField.mapEquiv (restrictOO σ)
  have hτ : ∀ c : OO p, τ (residue (OO p) c) = residue (OO p) (restrictOO σ c) := fun c => rfl
  rw [← hτ, ha]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨n, hn⟩ := hu (Units.mk0 x hx)
  have hx' : x = (u : F) ^ n := by simpa using (congrArg Units.val hn).symm
  rw [hx', map_pow, map_pow, map_pow, ← ha₀, hτ, hσ]

theorem kb_isAlgClosed_and_conj : ∀ (p : ℕ) [Fact p.Prime], IsAlgClosed (kb p) ∧ (∀ x : kb p, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1) ∧ ∀ (F : Type) [Field F] [Finite F] (r r' : F →+* kb p), ∃ σ : OO p ≃+* OO p, ∀ (x : F) (a : OO p), IsLocalRing.residue (OO p) a = r x → IsLocalRing.residue (OO p) (σ a) = r' x :=
  fun _ _ => ⟨isAlgClosed_kb, exists_pow_eq_one_kb, exists_ringEquiv_residue_eq⟩

end GlobalTheory.ZJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ThetaProj

theorem eStd_swap (g n : ℕ) (a b : Fin g ⊕ Fin g → ZMod n) : eStd g n a b = -eStd g n b a := by
  simp only [eStd]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_eStd_eq (g n : ℕ) (f : (Fin g ⊕ Fin g → ZMod n) →ₗ[ZMod n] ZMod n) :
    ∃ b, ∀ y, eStd g n b y = f y := by
  refine ⟨Sum.elim (fun i => f (Pi.single (.inr i) 1)) (fun i => -f (Pi.single (.inl i) 1)),
    fun y => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← Finset.univ_sum_single y, map_sum, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j, f (Pi.single j (y j)) = y j * f (Pi.single j 1) := fun j => by
    rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [h, h]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

theorem exists_retraction {n d : ℕ} [NeZero n] {Γ : Type} [AddCommGroup Γ] [Module (ZMod n) Γ]
    (T : AddSubgroup Γ) (e : T ≃+ (Fin d → ZMod n)) : ∃ p : Γ →+ T, ∀ t : T, p t = t := by
  let T' : Submodule (ZMod n) Γ := AddSubgroup.toZModSubmodule n T
  let e' : T' →+ (Fin d → ZMod n) :=
    { toFun := fun x => e ⟨x.1, x.2⟩
      map_zero' := map_zero e
      map_add' := fun x y => map_add e ⟨x.1, x.2⟩ ⟨y.1, y.2⟩ }
  obtain ⟨f, hf⟩ := (ZModPerp.baer_of_free (n := n) (Fin d → ZMod n)).extension_property
    T'.subtype T'.subtype_injective (e'.toZModLinearMap n)
  refine ⟨e.symm.toAddMonoidHom.comp f.toAddMonoidHom, fun t => ?_⟩
  have : f t = e t := LinearMap.congr_fun hf ⟨t.1, t.2⟩
  simp [this]

theorem nsmul_eq_zero_of_forall_char {r N : ℕ} [NeZero (r * N)] {Γ : Type} [AddCommGroup Γ]
    [Module (ZMod (r * N)) Γ] (u : Γ) (h : ∀ ψ : Γ →+ ZMod N, ψ u = 0) : r • u = 0 := by
  by_contra hu
  obtain ⟨f, hf⟩ := ZModPerp.exists_dual_ne_zero (n := r * N) hu
  apply hf
  have h1 := h ((ZMod.castHom (dvd_mul_left N r) (ZMod N)).toAddMonoidHom.comp f.toAddMonoidHom)
  have h2 : ZMod.castHom (dvd_mul_left N r) (ZMod N) (f u) = 0 := h1
  rw [← ZMod.natCast_zmod_val (f u), map_natCast, ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨k, hk⟩ := h2
  rw [map_nsmul, ← ZMod.natCast_zmod_val (f u), hk, nsmul_eq_mul, ← Nat.cast_mul, ← _root_.mul_assoc,
    Nat.cast_mul, ZMod.natCast_self, zero_mul]

theorem sum_char_smul {o M U : Type} [CommRing o] [IsDomain o] [AddCommGroup M] [Module o M]
    [AddCommGroup U] [Fintype U] {N : ℕ} [NeZero N] [Fintype (U →+ ZMod N)]
    (χ : AddChar (ZMod N) o) (hχ : ∀ a, χ a = 1 → a = 0) (ρ : U → M)
    (hρ : ∀ u, (∀ ψ : U →+ ZMod N, ψ u = 0) → ρ u = ρ 0) :
    ∑ ψ : U →+ ZMod N, ∑ u, χ (-ψ u) • ρ u = (Fintype.card U : o) • ρ 0 := by
  have h1 : ∀ u, (∑ ψ : U →+ ZMod N, χ (-ψ u)) • ρ u
      = (∑ ψ : U →+ ZMod N, χ (-ψ u)) • ρ 0 := fun u => by
    by_cases hu : ∀ ψ : U →+ ZMod N, ψ u = 0
    · rw [hρ u hu]
    · obtain ⟨ψ, hψ⟩ := not_forall.mp hu
      have : χ.compAddMonoidHom (-(AddMonoidHom.eval u : (U →+ ZMod N) →+ ZMod N)) ≠ 1 := by
        intro h
        have := DFunLike.congr_fun h ψ
        exact hψ (neg_eq_zero.mp (hχ _ this))
      have h0 : ∑ ψ : U →+ ZMod N, χ (-ψ u) = 0 := AddChar.sum_eq_zero_of_ne_one this
      rw [h0, zero_smul, zero_smul]
  have h2 : ∀ ψ : U →+ ZMod N, ψ ≠ 0 → ∑ u, χ (-ψ u) = 0 := fun ψ hψ => by
    have : χ.compAddMonoidHom (-ψ) ≠ 1 := by
      intro h
      apply hψ
      ext u
      have := DFunLike.congr_fun h u
      exact neg_eq_zero.mp (hχ _ this)
    exact AddChar.sum_eq_zero_of_ne_one this
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h1]
  rw [← Finset.sum_smul, Finset.sum_comm,
    Finset.sum_eq_single (0 : U →+ ZMod N) (fun ψ _ => h2 ψ) (by simp)]
  simp

theorem sum_ext_char_smul {o M A T : Type} [CommRing o] [IsDomain o] [AddCommGroup M] [Module o M]
    [AddCommGroup A] [AddCommGroup T] [Finite A] [Finite T] {N : ℕ} [NeZero N]
    (i : A →+ T) (p : T →+ A) (hp : ∀ a, p (i a) = a)
    (χ : AddChar (ZMod N) o) (hχ : ∀ a, χ a = 1 → a = 0) (ρ : T → M)
    (hρ : ∀ a u, (∀ ψ : T →+ ZMod N, ψ u = 0) → ρ (i a + u) = ρ (i a)) (c' : A →+ ZMod N) :
    Nat.card T = Nat.card A * Nat.card p.ker ∧
    ∑ᶠ c ∈ {c : T →+ ZMod N | c.comp i = c'}, ∑ᶠ t, χ (-c t) • ρ t
      = (Nat.card p.ker : o) • ∑ᶠ a, χ (-c' a) • ρ (i a) := by
  let q : T →+ p.ker := (AddMonoidHom.id T - i.comp p).codRestrict p.ker fun t => by
    simp [AddMonoidHom.mem_ker, hp]
  have hq : ∀ t, (q t : T) = t - i (p t) := fun t => rfl
  have hqu : ∀ u : p.ker, q u = u := fun u => Subtype.ext (by
    rw [hq, (AddMonoidHom.mem_ker).mp u.2, map_zero, sub_zero])
  have hqi : ∀ a, q (i a) = 0 := fun a => Subtype.ext (by rw [hq, hp, sub_self]; rfl)
  let e : A × p.ker ≃ T :=
    { toFun := fun x => i x.1 + x.2
      invFun := fun t => (p t, q t)
      left_inv := fun x => by
        simp [hp, hqu, hqi, (AddMonoidHom.mem_ker).mp x.2.2]
      right_inv := fun t => by simp [hq] }
  have he : ∀ a (u : p.ker), e (a, u) = i a + u := fun _ _ => rfl
  refine ⟨by rw [← Nat.card_prod, Nat.card_congr e], ?_⟩
  have := Fintype.ofFinite A
  have := Fintype.ofFinite T
  have := Fintype.ofFinite p.ker
  have : Finite (p.ker →+ ZMod N) := DFunLike.finite _
  have := Fintype.ofFinite (p.ker →+ ZMod N)
  have hinj : Function.Injective fun ψ : p.ker →+ ZMod N => c'.comp p + ψ.comp q := by
    intro ψ ψ' h
    ext u
    have := DFunLike.congr_fun (add_left_cancel h) (u : T)
    simpa [hqu] using this
  have hs : {c : T →+ ZMod N | c.comp i = c'}
      = Set.range fun ψ : p.ker →+ ZMod N => c'.comp p + ψ.comp q := by
    ext c
    constructor
    · rintro rfl
      refine ⟨c.comp p.ker.subtype, ?_⟩
      ext t
      simp [hq]
    · rintro ⟨ψ, rfl⟩
      ext a
      simp [hp, hqi]
  rw [hs, finsum_mem_range hinj]
  simp_rw [finsum_eq_sum_of_fintype, ← e.sum_comp, Fintype.sum_prod_type, he]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have := sum_char_smul χ hχ (fun u : p.ker => ρ (i a + u)) fun u hu => by
    have := hρ a u fun ψ => hu (ψ.comp p.ker.subtype)
    simpa using this
  simp only [ZeroMemClass.coe_zero, add_zero] at this
  rw [smul_comm, Nat.card_eq_fintype_card, ← this, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_smul, ← AddChar.map_add_eq_mul]
  simp [hp, hqu, hqi, (AddMonoidHom.mem_ker).mp u.2, add_comm]

end GlobalTheory.ThetaProj

namespace GlobalTheory

open ThetaProj

theorem thetaSys_FF_mem_finite_perp_proj :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω),
      (∀ T c k, S.FF T c k ∈ S.R) ∧ Set.Finite {x : Ω | ∃ T c k, x = S.FF T c k} ∧
      (∀ H, S.perp (S.perp H) = H) ∧
      ∀ (T T' : AddSubgroup S.Gam) (h : T' ≤ T), S.IsoFree T → S.IsoFree T' →
        ∀ (c' : T' →+ ZMod S.N), S.proj T' c' =
          ∑ᶠ c ∈ {c : T →+ ZMod S.N | c.comp (AddSubgroup.inclusion h) = c'}, S.proj T c := by
  intro o Ω _ _ _ hA S
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have : IsDomain o := hA.inj.isDomain _
  refine ⟨fun T c k => ?_, ?_, fun H => ?_, fun T T' h hT hT' c' => ?_⟩
  · have := Fintype.ofFinite T
    rw [ThetaSys.FF, finsum_eq_sum_of_fintype]
    exact S.R.sum_mem fun t _ => S.R.mul_mem (S.R.algebraMap_mem _)
      (S.R.sum_mem fun j _ => S.R.mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))
  · have : Finite (AddSubgroup S.Gam) := Finite.of_injective _ SetLike.coe_injective
    have : ∀ T : AddSubgroup S.Gam, Finite (T →+ ZMod S.N) := fun T => DFunLike.finite _
    refine (Set.finite_range fun x : Σ T : AddSubgroup S.Gam,
      (T →+ ZMod S.N) × (S.J × (T → ZMod ((S.r * S.N) ^ 2))) => S.FF x.1 x.2.1 x.2.2).subset ?_
    rintro x ⟨T, c, k, rfl⟩
    exact ⟨⟨T, c, k⟩, rfl⟩
  · refine le_antisymm (fun x hx => ?_) fun x hx y hy => ?_
    · by_contra hxH
      let H' : Submodule (ZMod (S.r * S.N)) S.Gam := AddSubgroup.toZModSubmodule _ H
      obtain ⟨f, hf⟩ := ZModPerp.exists_dual_ne_zero (n := S.r * S.N) (q := H'.mkQ x)
        (fun h0 => hxH ((Submodule.Quotient.mk_eq_zero H').mp h0))
      obtain ⟨b, hb⟩ := exists_eStd_eq _ _ (f ∘ₗ H'.mkQ)
      have hb' : b ∈ S.perp H := fun y hy => by
        rw [hb, LinearMap.comp_apply, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero H').mpr hy, map_zero]
      have h1 : eStd S.g _ x b = 0 := hx b hb'
      rw [eStd_swap, neg_eq_zero, hb] at h1
      exact hf h1
    · rw [eStd_swap, hy x hx, neg_zero]
  · obtain ⟨d, ⟨e⟩⟩ := hT.2
    obtain ⟨d', ⟨e'⟩⟩ := hT'.2
    obtain ⟨p, hp⟩ := exists_retraction T' e'
    have hζ : IsPrimitiveRoot S.ζN S.N :=
      S.prim.pow (NeZero.pos _) (by ring)
    let χ : AddChar (ZMod S.N) o := AddChar.zmodChar S.N hζ.pow_eq_one
    have hχ : ∀ a, χ a = 1 → a = 0 := fun a ha =>
      ((AddChar.zmodChar_primitive_of_primitive_root S.N hζ).zmod_char_eq_one_iff S.N a).mp ha
    let _ : Module (ZMod (S.r * S.N)) T := AddCommGroup.zmodModule fun x => Subtype.ext (by
      rw [AddSubgroup.coe_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self,
        zero_smul]
      rfl)
    obtain ⟨h1, h2⟩ := sum_ext_char_smul (AddSubgroup.inclusion h) (p.comp T.subtype)
      (fun a => hp a) χ hχ (fun t : T => S.ρ t) (fun a u hu => by
        have hu' : S.r • (u : S.Gam) = 0 :=
          congrArg Subtype.val (nsmul_eq_zero_of_forall_char (r := S.r) u hu)
        rw [AddSubgroup.coe_add, ← S.ρ_add _ _ (by
          rw [hT.1 (AddSubgroup.inclusion h a).2 u u.2, smul_zero]), S.ρ_one _ hu', _root_.mul_one]) c'
    have hu : IsUnit (Nat.card T : o) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
      exact S.unit.pow _
    have hfin : Finite (T →+ ZMod S.N) := DFunLike.finite _
    have h3 : ∑ᶠ c ∈ {c : T →+ ZMod S.N | c.comp (AddSubgroup.inclusion h) = c'}, S.proj T c
        = Ring.inverse (Nat.card T : o) •
          ∑ᶠ c ∈ {c : T →+ ZMod S.N | c.comp (AddSubgroup.inclusion h) = c'},
            ∑ᶠ t : T, χ (-c t) • S.ρ t := by
      rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
        finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.smul_sum]
      rfl
    rw [h3, h2, smul_smul]
    rw [h1, Nat.cast_mul] at hu ⊢
    rw [Ring.mul_inverse_rev' (Commute.all _ _), mul_right_comm,
      Ring.inverse_mul_cancel _ (isUnit_of_mul_isUnit_right hu), _root_.one_mul]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem isGen_one_of_g_eq_one {X : Scheme.{0}} (L : LB X) (h : ∀ i j, L.g i j = 1) :
    (⟨fun _ => 1⟩ : LB.Gen L).IsGen := fun i j =>
  (map_one _).trans ((congrArg₂ (· * ·) (h i j) (map_one _)).trans (_root_.mul_one _)).symm

theorem div_g_eq_one {X : Scheme.{0}} (M L : LB X) (hM : ∀ i j, M.g i j = 1) (hL : ∀ i j, L.g i j = 1)
    (i j : (LB.div M L).ι) : (LB.div M L).g i j = 1 := by
  simp only [LB.div, hM, hL, map_one, inv_one, _root_.mul_one]
  rfl

theorem isGen_one_linComb_triv {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (⟨fun _ => 1⟩ : LB.Gen (LB.LinComb (Out.Inh.trivLB X) φ ε)).IsGen :=
  isGen_one_of_g_eq_one _ (Out.Inh.linComb_triv_g φ ε)

def splitExtOfAbelian {S : Scheme.{0}} (B : Over S) [GrpObj B] (h : IsAbelianScheme B) : SplitExt S where
  B := B
  isAbelian := h
  X := PUnit
  O := fun _ => ⟨Out.Inh.trivLB _, ⟨fun _ => 1⟩, Out.Inh.trivLB_isLB _, isGen_one_linComb_triv _ _⟩
  addIso := fun _ _ => ⟨⟨fun _ => 1⟩, isGen_one_of_g_eq_one _
    (div_g_eq_one _ _ (div_g_eq_one _ _ (fun _ _ => rfl) fun _ _ => rfl) fun _ _ => rfl)⟩
  zeroTriv := ⟨⟨fun _ => 1⟩, isGen_one_of_g_eq_one _ fun _ _ => rfl⟩
  primitive := fun _ => ⟨⟨fun _ => 1⟩, isGen_one_linComb_triv _ _⟩

theorem isGt_splitExtOfAbelian {S : Scheme.{0}} (B : Over S) [GrpObj B] (h : IsAbelianScheme B) :
    (splitExtOfAbelian B h).IsGt B := by
  have := h.comm
  have := isIso_toUnit_splitTorus_punit S
  have hk : IsPullback (toUnit (splitTorus S PUnit) ≫ η[B]) (toUnit _) (𝟙 B) η[B] :=
    IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  refine CoordToExt.isGt_of_units (splitExtOfAbelian B h) (𝟙 B) (toUnit _ ≫ η[B])
    (inferInstanceAs (IsMonHom (𝟙 B)))
    (inferInstanceAs (IsMonHom (toUnit (splitTorus S PUnit) ≫ η[B])))
    (inferInstanceAs (Flat (𝟙 B.left))) (inferInstanceAs (Surjective (𝟙 B.left)))
    (inferInstanceAs (IsAffineHom (𝟙 B.left))) hk (fun _ _ => 1) ?_ ?_ ?_
  · intro χ Z r z a a' _ _
    exact (map_one _).trans ((congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)).symm
  · intro χ a Z t g z _
    have e : charUnit S PUnit χ = 1 := by
      have e₀ : Multiplicative.ofAdd (α := PUnit) χ = 1 := rfl
      unfold charUnit
      rw [e₀]
      simp only [map_one]
      exact (congrArg _ (map_one _)).trans (map_one _)
    exact (map_one _).trans ((congrArg₂ (· * ·) ((congrArg _ e).trans (map_one _)) (map_one _)).trans
      (_root_.mul_one _)).symm
  · intro χ a y _
    exact (congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)

section

variable {T V Z G H : Scheme.{0}} {f : H ⟶ G} {s : H ⟶ V} {t : G ⟶ Z} {y₀ : V ⟶ Z}

end

section

variable (Z : Scheme.{0}) [IsIntegral Z] (π : Z ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsSeparated π] (hZ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) (A : Over Z) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom)

end

end GlobalTheory.ZJ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AddHomExtSingle
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.Weights

def eLeft (g n : ℕ) (x : Fin g ⊕ Fin g → ZMod n) : (Fin g ⊕ Fin g → ZMod n) →+ ZMod n :=
  AddMonoidHom.mk' (fun a => eStd g n a x) (by
    intro a b
    simp only [eStd, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring)

theorem eLeft_apply (g n : ℕ) (x a : Fin g ⊕ Fin g → ZMod n) : eLeft g n x a = eStd g n a x := rfl

theorem eStd_swap (g n : ℕ) (x a : Fin g ⊕ Fin g → ZMod n) : eStd g n a x = -eStd g n x a := by
  simp only [eStd, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem addHom_ext_single {d n : ℕ} [NeZero n] {A : Type*} [AddCommGroup A] (f f' : (Fin d → ZMod n) →+ A)
    (h : ∀ i, f (Pi.single i 1) = f' (Pi.single i 1)) : f = f' := by
  refine AddMonoidHom.functions_ext _ _ _ fun i z => ?_
  have : (Pi.single i z : Fin d → ZMod n) = z.val • (Pi.single i 1 : Fin d → ZMod n) := by
    rw [← Pi.single_nsmul]
    simp
  rw [this, map_nsmul, map_nsmul, h]

theorem exists_eStd_eq {g d n : ℕ} [NeZero n]
    (φ : (Fin d → ZMod n) →+ (Fin g ⊕ Fin g → ZMod n)) (hφ : Function.Injective φ)
    (a : Fin d → ZMod n) : ∃ x, ∀ i, eStd g n (φ (Pi.single i 1)) x = a i := by
  obtain ⟨F, hF⟩ := (GlobalTheory.ZModPerp.baer_zmod n).extension_property (φ.toZModLinearMap n) hφ
    (Fintype.linearCombination (ZMod n) a)
  refine ⟨Sum.elim (fun i => -F (Pi.single (.inr i) 1)) (fun i => F (Pi.single (.inl i) 1)),
    fun i => ?_⟩
  have h1 : F (φ (Pi.single i 1)) = a i := by
    have := LinearMap.congr_fun hF (Pi.single i 1)
    simpa using this
  rw [← h1, LinearMap.pi_apply_eq_sum_univ F, Fintype.sum_sum_type, eStd, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : ∀ k : Fin g ⊕ Fin g, (fun j => if k = j then (1 : ZMod n) else 0) = Pi.single k 1 := by
    intro k
    funext j
    simp [Pi.single_apply, eq_comm]
  simp only [Sum.elim_inl, Sum.elim_inr, smul_eq_mul, e]
  ring

theorem exists_min {X : Type} [AddCommGroup X] (q : X → ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (N : ℕ) (β : X) :
    ∃ v : X, ∀ v₀ : X, q (β + N • v) ≤ q (β + N • v + N • v₀) := by
  let s : Set X := Set.range fun v : X => β + N • v
  have : Nonempty s := ⟨⟨_, 0, rfl⟩⟩
  obtain ⟨⟨_, v, rfl⟩, hv⟩ := Filter.Tendsto.exists_forall_le (f := fun a : s => q a)
    (hq.comp Subtype.val_injective.tendsto_cofinite)
  refine ⟨v, fun v₀ => ?_⟩
  have := hv ⟨_, v + v₀, rfl⟩
  simpa [add_assoc] using this

end GlobalTheory.ZH.Weights

namespace GlobalTheory.ZH

open Weights

theorem test_weights : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω), (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) := by
  intro o Ω _ _ _ _ S p _ y₀ τ
  have hN : S.N ≠ 0 := by have := S.N_ge; omega
  have hr : S.r ≠ 0 := by have := S.r_pos; omega
  have : NeZero (S.r * S.N) := ⟨mul_ne_zero hr hN⟩
  have : NeZero S.N := ⟨hN⟩
  have hwt : ∀ v : τ.X, τ.wt (S.N • v) = 0 := fun v => by
    ext t
    rw [map_nsmul, AddMonoidHom.nsmul_apply]
    simp
  refine ⟨fun c => ?_, fun T hT hle w hw I hI α => ⟨fun h => ?_, fun h t h₂ ht => ?_⟩⟩
  · obtain ⟨-, d, ⟨E⟩⟩ := τ.isoFree
    obtain ⟨x, hx⟩ := exists_eStd_eq ((S.perp τ.yy.ker).subtype.comp E.symm.toAddMonoidHom)
      (Subtype.val_injective.comp E.symm.injective)
      (fun i => ((c (E.symm (Pi.single i 1))).val : ZMod (S.r * S.N)))
    obtain ⟨β, hβ⟩ := QuotientAddGroup.mk_surjective (τ.yy x)
    obtain ⟨v, hv⟩ := exists_min τ.q τ.pos S.N β
    refine ⟨_, hv, ?_⟩
    rw [map_add (f := _), hwt, add_zero]
    have := addHom_ext_single ((τ.wt β).comp E.symm.toAddMonoidHom) (c.comp E.symm.toAddMonoidHom) fun i => by
      have h1 := τ.wt_eq x β hβ.symm (E.symm (Pi.single i 1))
      have h2 : eStd S.g _ (E.symm (Pi.single i 1) : S.Gam) x = _ := hx i
      rw [h2, map_natCast, ZMod.natCast_zmod_val] at h1
      exact h1
    ext t
    simpa using DFunLike.congr_fun this (E t)
  · obtain ⟨-, d, ⟨E⟩⟩ := hT
    obtain ⟨x, hx⟩ := τ.yy_onto (QuotientAddGroup.mk α)
    have key : ∀ t : T, ∃ a : ZMod (S.r * S.N), eStd S.g _ (t : S.Gam) x = S.N • a := fun t => by
      have h1 := τ.wt_eq x α hx ⟨t, hle t.2⟩
      rw [h t _ t.2, ZMod.castHom_apply, ZMod.cast_eq_val, eq_comm,
        ZMod.natCast_eq_zero_iff] at h1
      obtain ⟨k, hk⟩ := h1
      refine ⟨k, ?_⟩
      rw [← ZMod.natCast_zmod_val (eStd S.g _ (t : S.Gam) x), hk]
      simp
    choose a ha using key
    obtain ⟨b, hb⟩ := exists_eStd_eq (T.subtype.comp E.symm.toAddMonoidHom)
      (Subtype.val_injective.comp E.symm.injective) (fun i => a (E.symm (Pi.single i 1)))
    have h3 := addHom_ext_single ((eLeft S.g _ x).comp (T.subtype.comp E.symm.toAddMonoidHom))
      (S.N • (eLeft S.g _ b).comp (T.subtype.comp E.symm.toAddMonoidHom)) fun i => by
        exact (ha _).trans (congrArg (S.N • ·) (hb i).symm)
    have h4 : x - S.N • b ∈ S.perp T := fun t ht => by
      have h5 : eStd S.g _ t x = S.N • eStd S.g _ t b := by
        simpa [eLeft_apply] using DFunLike.congr_fun h3 (E ⟨t, ht⟩)
      rw [← eLeft_apply, map_sub, map_nsmul, eLeft_apply, eLeft_apply, eStd_swap, h5,
        eStd_swap _ _ t b]
      simp
    set L := AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀) with hL
    have hNL : ∀ v : τ.X, S.N • v ∈ L := fun v => AddSubgroup.subset_closure (Or.inr ⟨v, rfl⟩)
    have h6 : S.perp T ≤ (L.map (QuotientAddGroup.mk' _)).comap τ.yy := by
      rw [← hI, AddSubgroup.closure_le]
      intro i hi
      exact ⟨w i, AddSubgroup.subset_closure (Or.inl ⟨i, hi, rfl⟩), (hw i).symm⟩
    obtain ⟨l, hl, hl'⟩ := h6 h4
    rw [map_sub, map_nsmul, hx, hw, QuotientAddGroup.mk'_apply, ← QuotientAddGroup.mk_nsmul,
      ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq] at hl'
    obtain ⟨u, hu⟩ := hl'
    have h7 : α = l + S.N • w b + S.N • (S.r • u) := by
      rw [← mul_nsmul, show (S.r * S.N) • u = _ from hu]
      abel
    rw [h7]
    exact L.add_mem (L.add_mem hl (hNL _)) (hNL _)
  · induction h using AddSubgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨i, hi, rfl⟩ | ⟨v, rfl⟩
      · have hi' : i ∈ S.perp T := hI ▸ AddSubgroup.subset_closure hi
        rw [τ.wt_eq i _ (hw i), eStd_swap, hi' t ht]
        simp
      · rw [hwt]
        rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), AddMonoidHom.add_apply, hx, hy, add_zero]
    | neg x _ hx => rw [map_neg, AddMonoidHom.neg_apply, hx, neg_zero]

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.FreeNear

section Abstract

variable {o A G B : Type} [CommRing o] [IsDomain o] [Ring A] [Algebra o A] [AddCommGroup G] [Fintype G]
  [AddCommGroup B]

theorem sum_char_comp (ψ : AddChar B o) (hψ : ∀ a, ψ a = 1 → a = 0) (c : G →+ B) :
    ∑ t, ψ (c t) = if c = 0 then (Fintype.card G : o) else 0 := by
  have h := AddChar.sum_eq_ite (ψ.compAddMonoidHom c)
  simp only [AddChar.compAddMonoidHom_apply] at h
  rw [h]
  refine if_congr ⟨fun h0 => ?_, fun h0 => ?_⟩ rfl rfl
  · ext t
    exact hψ _ (by simpa using DFunLike.congr_fun h0 t)
  · ext t
    simp [h0]

theorem avg_mul_avg [DecidableEq (G →+ B)] (ψ : AddChar B o) (hψ : ∀ a, ψ a = 1 → a = 0) (ρ : G → A)
    (hρ : ∀ a b, ρ a * ρ b = ρ (a + b)) (u : o) (hu : u * (Fintype.card G : o) = 1) (c c' : G →+ B) :
    (u • ∑ t, ψ (-(c t)) • ρ t) * (u • ∑ t, ψ (-(c' t)) • ρ t) =
      if c = c' then u • ∑ t, ψ (-(c t)) • ρ t else 0 := by
  have h1 : (∑ t, ψ (-(c t)) • ρ t) * (∑ t, ψ (-(c' t)) • ρ t) =
      (∑ s, ψ ((c' - c) s)) • ∑ t, ψ (-(c' t)) • ρ t := by
    rw [Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft s) _ _ fun t => ?_
    rw [smul_mul_smul_comm, hρ, smul_smul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [AddMonoidHom.sub_apply, Equiv.coe_addLeft, map_add (f := _)]
    abel
  rw [smul_mul_smul_comm, h1, sum_char_comp ψ hψ, smul_smul]
  by_cases h : c = c'
  · subst h
    rw [if_pos (sub_self c), if_pos rfl, _root_.mul_assoc, hu, _root_.mul_one]
  · rw [if_neg (fun h0 => h (sub_eq_zero.1 h0).symm), if_neg h, mul_zero, zero_smul]

theorem sum_avg [Fintype (G →+ B)] (ψ : AddChar B o) (hψ : ∀ a, ψ a = 1 → a = 0) (ρ : G → A)
    (hρ : ∀ t, (∀ c : G →+ B, c t = 0) → ρ t = 1) (u : o) (hu : u * (Fintype.card G : o) = 1) :
    ∑ c : G →+ B, u • ∑ t, ψ (-(c t)) • ρ t = 1 := by
  have h1 : ∀ t, (∑ c : G →+ B, ψ (-(c t))) • ρ t = (∑ c : G →+ B, ψ (-(c t))) • (1 : A) := by
    intro t
    by_cases h : ∀ c : G →+ B, c t = 0
    · rw [hρ t h]
    · have h2 := sum_char_comp ψ hψ (-(AddMonoidHom.eval (M := G) (N := B) t))
      rw [if_neg (fun h0 => h fun c => by simpa using DFunLike.congr_fun h0 c)] at h2
      simp only [AddMonoidHom.neg_apply, AddMonoidHom.eval_apply_apply] at h2
      rw [h2, zero_smul, zero_smul]
  have h3 : ∀ c : G →+ B, ∑ t, ψ (-(c t)) = if c = 0 then (Fintype.card G : o) else 0 := by
    intro c
    simpa using sum_char_comp ψ hψ (-c)
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.sum_smul, h1]
  rw [Finset.sum_comm]
  simp only [h3, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [smul_smul, hu, one_smul]

end Abstract

section System

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

instance neZero_N : NeZero S.N := ⟨by have := S.N_ge; omega⟩

instance neZero_rN : NeZero (S.r * S.N) :=
  ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (NeZero.ne _)⟩

theorem isPrimitiveRoot_ζN : IsPrimitiveRoot S.ζN S.N :=
  S.prim.pow (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _))) (by ring)

theorem finite_char (T : AddSubgroup S.Gam) : Finite (T →+ ZMod S.N) :=
  Finite.of_injective _ DFunLike.coe_injective

theorem proj_orthogonal [IsDomain o] (T : AddSubgroup S.Gam) (hT : S.IsoFree T) [Fintype (T →+ ZMod S.N)]
    [DecidableEq (T →+ ZMod S.N)] :
    (∀ c c', S.proj T c * S.proj T c' = if c = c' then S.proj T c else 0) ∧ ∑ c, S.proj T c = 1 := by
  obtain ⟨hiso, d, ⟨φ⟩⟩ := hT
  haveI := Fintype.ofFinite T
  have hprim := isPrimitiveRoot_ζN S
  let ψ : AddChar (ZMod S.N) o := AddChar.zmodChar S.N hprim.pow_eq_one
  have hψ : ∀ a, ψ a = 1 → a = 0 := fun a ha => by
    rw [AddChar.zmodChar_apply, hprim.pow_eq_one_iff_dvd] at ha
    exact (ZMod.val_eq_zero a).1 (Nat.eq_zero_of_dvd_of_lt ha a.val_lt)
  have hunit : IsUnit (Nat.card T : o) := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  have hu : Ring.inverse (Nat.card T : o) * (Fintype.card T : o) = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Ring.inverse_mul_cancel _ hunit
  have hp : ∀ c, S.proj T c = Ring.inverse (Nat.card T : o) • ∑ t : T, ψ (-(c t)) • S.ρ t := fun c => by
    rw [ThetaSys.proj, finsum_eq_sum_of_fintype]
    rfl
  simp only [hp]
  refine ⟨avg_mul_avg ψ hψ (fun t : T => S.ρ t) (fun a b => S.ρ_add _ _ ?_) _ hu,
    sum_avg ψ hψ (fun t : T => S.ρ t) (fun t ht => S.ρ_one _ ?_) _ hu⟩
  · rw [hiso a.2 b b.2, smul_zero]
  · have h : S.r • t = 0 := by
      apply φ.injective
      rw [map_nsmul, map_zero]
      funext i
      have h1 := ht (((ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom.comp
        (Pi.evalAddMonoidHom (fun _ => ZMod (S.r * S.N)) i)).comp φ.toAddMonoidHom)
      change ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (φ t i) = 0 at h1
      change S.r • φ t i = 0
      obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (φ t i)
      rw [← hn, map_natCast, ZMod.natCast_eq_zero_iff] at h1
      rw [← hn, nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      exact Nat.mul_dvd_mul_left _ h1
    exact congrArg Subtype.val h

end System

section Model

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isOpen_setOf_mem_span {J I : Type} [Fintype I] (b : I → J → Ω) (v : J → Ω) :
    IsOpen {x : M.Z | v ∈ Submodule.span (M.O x) (Set.range b)} := by
  refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
  refine ⟨⋂ i, {w | (a i : Ω) ∈ M.O w}, fun w hw => ?_,
    isOpen_iInter_of_finite fun i => M.isOpen_setOf_mem_O _, Set.mem_iInter.2 fun i => (a i).2⟩
  exact (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ⟨a i, Set.mem_iInter.1 hw i⟩, rfl⟩

theorem exists_opens_span_eq {J I : Type} [Fintype I] (b : I → J → Ω) (V : Set (J → Ω)) (hV : V.Finite)
    (hb : Set.range b ⊆ V) (z : M.Z) (hz : ∀ v ∈ V, v ∈ Submodule.span (M.O z) (Set.range b)) :
    ∃ W : M.Z.Opens, z ∈ W ∧ ∀ x ∈ W, Submodule.span (M.O x) V = Submodule.span (M.O x) (Set.range b) := by
  refine ⟨⟨⋂ v ∈ V, {x : M.Z | v ∈ Submodule.span (M.O x) (Set.range b)},
    hV.isOpen_biInter fun v _ => isOpen_setOf_mem_span M b v⟩, Set.mem_iInter₂.2 hz, fun x hx => ?_⟩
  exact le_antisymm (Submodule.span_le.2 fun v hv => Set.mem_iInter₂.1 hx v hv) (Submodule.span_mono hb)

end Model

end GlobalTheory.ZH.FreeNear

namespace GlobalTheory.ZH


open FreeNear in
theorem exists_basis_lattice_near :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ z : M.Z, ∃ (b : Matrix S.J S.J Ω) (W : M.Z.Opens), z ∈ W ∧ b.det ≠ 0 ∧ ∀ x ∈ W, Submodule.span (M.O x) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)} = Submodule.span (M.O x) (Set.range b)) := by
  intro o Ω _ _ _ hA S M U₀ hAdm h0 hne z
  haveI : IsDomain o := hA.inj.isDomain
  have hT := (h0.1 z).1
  haveI := FreeNear.finite_char S (S.TT M z)
  haveI := Fintype.ofFinite (S.TT M z →+ ZMod S.N)
  obtain ⟨hmul, hsum⟩ := FreeNear.proj_orthogonal S _ hT
  obtain ⟨x₁, hx₁⟩ := hAdm.1.div z
  choose k₁ hk₁ using fun c => hAdm.2 _ c hT (hne z c) z
  obtain ⟨κ, col, hdet, hspan⟩ := exists_basis_adapted_to_idempotents (M.O z) S.J (S.TT M z →+ ZMod S.N)
    (fun c => (algebraMap o (M.O z)).mapMatrix (S.proj _ c))
    (fun c c' => by
      rw [← map_mul, hmul]
      split_ifs <;> simp)
    (by rw [← map_sum, hsum, map_one])
  let f : (S.TT M z →+ ZMod S.N) → Ω := fun c => S.th x₁ / S.FF _ c (k₁ c)
  have hf : ∀ c, f c ≠ 0 := fun c => div_ne_zero hx₁.1 (hk₁ c).1
  let b : Matrix S.J S.J Ω := Matrix.of fun i j => f (κ i) * algebraMap o Ω (S.proj _ (κ i) j (col i))
  have hb : b.det ≠ 0 := by
    have h1 := (hdet.map (algebraMap (M.O z) Ω)).ne_zero
    rw [RingHom.map_det] at h1
    have h2 := Matrix.det_mul_column (fun i => f (κ i))
      (Matrix.of fun i j => algebraMap o Ω (S.proj _ (κ i) j (col i)))
    change b.det = _ at h2
    rw [h2]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hf _) h1
  suffices h : ∃ W : M.Z.Opens, z ∈ W ∧ ∀ x ∈ W, _ = Submodule.span (M.O x) (Set.range b) by
    obtain ⟨W, hz, hW⟩ := h
    exact ⟨b, W, hz, hb, hW⟩
  refine FreeNear.exists_opens_span_eq M b _ ?_ ?_ z ?_
  · refine (Set.finite_range fun q : (S.TT M z →+ ZMod S.N) × (S.J × (S.TT M z → ZMod ((S.r * S.N) ^ 2))) ×
      S.Gam × S.J => fun j => S.th q.2.2.1 / S.FF _ q.1 q.2.1 * algebraMap o Ω (S.proj _ q.1 j q.2.2.2)).subset ?_
    rintro _ ⟨c, k, x₀, i, -, -, rfl⟩
    exact ⟨(c, k, x₀, i), rfl⟩
  · rintro _ ⟨i, rfl⟩
    exact ⟨κ i, k₁ _, x₁, col i, hk₁ _, hx₁, rfl⟩
  · rintro _ ⟨c, k, x₀, i, hk, -, rfl⟩
    have h1 : ∀ w ∈ Submodule.span (M.O z) {v : S.J → M.O z | ∃ i, κ i = c ∧
        v = fun j => (algebraMap o (M.O z)).mapMatrix (S.proj _ c) j (col i)},
        (fun j => f c * (w j : Ω)) ∈ Submodule.span (M.O z) (Set.range b) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem _ h' =>
        obtain ⟨i', rfl, rfl⟩ := h'
        exact Submodule.subset_span ⟨i', rfl⟩
      | zero =>
        convert Submodule.zero_mem (Submodule.span (M.O z) (Set.range b)) using 1
        funext j
        simp
      | add a a' _ _ ha ha' =>
        convert Submodule.add_mem _ ha ha' using 1
        funext j
        simp [mul_add]
      | smul s a _ ha =>
        convert Submodule.smul_mem _ s ha using 1
        funext j
        simp [Subalgebra.smul_def, mul_left_comm]
    have h2 := h1 _ ((hspan c).le (Submodule.subset_span ⟨i, rfl⟩))
    convert Submodule.smul_mem _ (⟨_, mul_mem (hx₁.2 x₀) (hk.2 (k₁ c))⟩ : M.O z) h2 using 1
    funext j
    have := hx₁.1
    have := (hk₁ c).1
    change _ = S.th x₀ / S.th x₁ * (S.FF _ c (k₁ c) / S.FF _ c k) *
      (S.th x₁ / S.FF _ c (k₁ c) * algebraMap o Ω (S.proj _ c j i))
    field_simp

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSupIIffAndHHEqKer
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem ThetaSys.mem_supI_iff_and_HH_eq_ker :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) := by
  intro o Ω _ _ _ _ S M U₀ hO z p _ y y₀ τ hC hA
  have hw : Set.range (gPt p ≫ y) = {(gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))} :=
    RatModel.range_eq_singleton (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))
  have hξ : (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ (U₀ : Set M.Z) := hC.2 ⟨_, rfl⟩
  have hsp := RatModel.specializes_of_range_eq hw
  have hthO : ∀ j, S.th j ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) :=
    fun j => RatModel.ringOn_le_O hξ (hO.le (S.th_mem j))
  have hinvO : ∀ j, S.th j ≠ 0 →
      (S.th j)⁻¹ ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) :=
    fun j hj => RatModel.ringOn_le_O hξ (hO.th_unit j hj)
  have hmul : ∀ i j, S.th i ≠ 0 → M.val (gPt p ≫ y) (S.th j) =
      M.val (gPt p ≫ y) (S.th j / S.th i) * M.val (gPt p ≫ y) (S.th i) := by
    intro i j hi
    have hq : S.th j / S.th i ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))) := by
      rw [div_eq_mul_inv]; exact mul_mem (hthO j) (hinvO i hi)
    rw [← RatModel.val_mul hsp hq (hthO i), div_mul_cancel₀ _ hi]
  have hval : ∀ x, ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = ‖M.val (gPt p ≫ y) (S.th x)‖ := fun x => by rw [hA]
  have hmax : IsGreatest (Set.range fun x => ‖M.val (gPt p ≫ y) (S.th x)‖) τ.δ := by
    simpa only [hval] using τ.δ_max
  have fwd : ∀ x, M.Div S.th x z → ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x hx
    apply le_antisymm (hmax.2 ⟨x, rfl⟩)
    obtain ⟨j, hj⟩ := hmax.1
    rw [← hj]
    dsimp only
    rw [hmul x j hx.1, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.Cen.norm_val_le_one hC (hx.2 j))
  have key : ∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x
    refine ⟨fun h => fwd x h, fun hx => ?_⟩
    obtain ⟨i, hi⟩ := hO.div z
    have h1 : ‖M.val (gPt p ≫ y) (S.th x / S.th i)‖ = 1 := by
      rw [hmul i x hi.1, norm_mul, fwd i hi] at hx
      have h2 : ‖M.val (gPt p ≫ y) (S.th x / S.th i)‖ * τ.δ = 1 * τ.δ := by rw [_root_.one_mul]; exact hx
      exact (mul_left_inj' τ.δ_pos.ne').mp h2
    show M.Div S.th x z
    exact (RatModel.Div.div_iff_isUnit hi x).mpr ((RatModel.norm_val_eq_one_iff hC.1 (hi.2 x)).mp h1)
  refine ⟨key, ?_⟩
  rw [← τ.supp]
  show AddSubgroup.closure (S.supI M z) = _
  congr 1
  ext x
  rw [key x, Set.mem_ofPred_eq, hval]

end GlobalTheory.ZH
end
