module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.UOfSat
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Sd Matrix GlobalTheory.LFun Formalism.UG

private theorem hecke_eq_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (a : G) (h : G → ℂ) (h1 : ∀ g : G, (g : G ⧸ K) ∈ MulAction.orbit K (a : G ⧸ K) → h g = 1)
    (h2 : ∀ g : G, (g : G ⧸ K) ∉ MulAction.orbit K (a : G ⧸ K) → h g = 0) (hf : {c : G ⧸ K | h c.out ≠ 0}.Finite) (x : V) :
    heckeVec ρ K h x = Hi.dc ρ K K a x := by
  classical
  have hfin : (MulAction.orbit K (a : G ⧸ K)).Finite := hf.subset fun c hc => by
    rw [Set.mem_setOf_eq, h1 _ (by rwa [QuotientGroup.out_eq'])]; exact one_ne_zero
  letI := hfin.fintype
  rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← finsum_eq_sum_of_fintype,
    finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out x), heckeVec]
  refine finsum_congr fun c => ?_
  by_cases hc : c ∈ MulAction.orbit K (a : G ⧸ K)
  · rw [h1 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]
  · rw [h2 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

private theorem iwahori_level_zero_eq : K1 w 0 = KGL w (n := 2) := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

private theorem hecke_Tj {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V)
    (j : ℕ) (a : GL (Fin 2) (w.adicCompletion F)) (ha : a.val = diagJ 2 (atFin w (unif w) : w.adicCompletion F) j) (x : V) :
    heckeVec ρ (KGL w (n := 2)) (Tj ℂ 2 (Ov F w) (atFin w (unif w) : w.adicCompletion F) j) x = Hi.dc ρ (KGL w (n := 2)) (KGL w (n := 2)) a x := by
  refine hecke_eq_dc ρ _ a _ (fun g hg => ?_) (fun g hg => ?_)
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm F w 2) (Tj_mem_hecke (unif_spec w) j).2) x
  · obtain ⟨k, hk⟩ := hg
    have h : ((k : GL (Fin 2) (w.adicCompletion F)) * a)⁻¹ * g ∈ KGL w (n := 2) := QuotientGroup.eq.1 hk
    rw [Tj, Set.indicator_of_mem, Pi.one_apply]
    refine ⟨k, k.2, _, h, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left]
  · rw [Tj, Set.indicator_of_notMem]
    rintro ⟨k, hk, k', hk', e⟩
    refine hg ⟨⟨k, hk⟩, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul] at e
    rw [Units.ext e]
    exact (QuotientGroup.mk_mul_of_mem (k * a) hk').symm

theorem UpperTheory.V.Br.uOfSat :
    UpperTheory.V.Br.UOfSat := by
  intro F _ _ w V _ _ ρ x α β ⟨_, hx', _, h⟩
  have hx := GlobalTheory.LGrp.mem_fixed.1 hx'
  constructor
  · have h1 := h (atFin w (unif w) : w.adicCompletion F) (unif_spec w) 1 (by norm_num)
    rw [Uop, iwahori_level_zero_eq, ← hecke_Tj w ρ 1 _ (by ext i j; fin_cases i <;> fin_cases j <;> simp [aff, diagJ]), h1]
    congr 1
    rw [Complex.ofReal_cpow (by positivity)]
    have : qV F w = normV w := by
      simp [normV, qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    simp [satEig, Multiset.esymm, Multiset.powersetCard_one, this]
    norm_num [add_comm]
  · have h2 := h (atFin w (unif w) : w.adicCompletion F) (unif_spec w) 2 (by norm_num)
    set z := GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))
    rw [hecke_Tj w ρ 2 z (by ext i j; fin_cases i <;> fin_cases j <;> simp [z, diagJ])] at h2
    have ho : ∀ q ∈ MulAction.orbit (KGL w (n := 2)) (z : _ ⧸ KGL w (n := 2)), q = z := by
      rintro _ ⟨k, rfl⟩
      change (((k : GL (Fin 2) (w.adicCompletion F)) * z : GL (Fin 2) (w.adicCompletion F)) : _ ⧸ KGL w (n := 2)) = _
      rw [← GlobalTheory.CuspRep.scalar_comm]
      exact QuotientGroup.mk_mul_of_mem _ k.2
    rw [(Hi.dcSum ℂ _ V ρ _ _ z ((Set.finite_singleton _).subset ho)).1 {z}
      (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact MulAction.mem_orbit_self _)
      (fun q hq => ⟨z, ⟨Finset.mem_singleton_self _, (ho q hq).symm⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩) x
      hx, Finset.sum_singleton] at h2
    rw [h2]
    simp [satEig, Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CapTwo
private theorem qdet2 {A : Type} [Ring A] [Algebra ℂ A] (E : Fin 2 → Fin 2 → A) (u : ℂ) :
    Formalism.REAL.qdet E u = (algebraMap ℂ A u + E 0 0) * (algebraMap ℂ A (u - 1) + E 1 1) - E 1 0 * E 0 1 := by
  have h : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [Formalism.REAL.qdet, Formalism.REAL.qminor, h, Finset.sum_pair (by decide)]
  simp [Formalism.REAL.Tm, List.ofFn_succ, sub_eq_add_neg]

private theorem cap2 {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (a b : ℂ) (φ : V)
    (h : ∀ u : ℂ, Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + a) * (u + b)) • φ) :
    E 0 0 φ + E 1 1 φ = (a + b) • φ ∧
      E 0 0 (E 0 0 φ) + E 0 1 (E 1 0 φ) + E 1 0 (E 0 1 φ) + E 1 1 (E 1 1 φ) = (a ^ 2 + b ^ 2 - 1 / 2) • φ := by
  have h0 := h 0
  have h1 := h 1
  rw [qdet2] at h0 h1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply, map_add (f := _),
    map_smul] at h0 h1
  have hs : E 0 0 φ + E 1 1 φ = (a + b) • φ := by
    linear_combination (norm := module) h1 - h0
  have r1 : E 0 0 (E 1 1 φ) - E 1 1 (E 0 0 φ) = 0 := by
    simpa using LinearMap.congr_fun (hE 0 0 1 1) φ
  have r2 : E 0 1 (E 1 0 φ) - E 1 0 (E 0 1 φ) = E 0 0 φ - E 1 1 φ := by
    simpa using LinearMap.congr_fun (hE 0 1 1 0) φ
  have s0 := congrArg (E 0 0) hs
  have s1 := congrArg (E 1 1) hs
  simp only [map_add (f := _), map_smul] at s0 s1
  refine ⟨hs, ?_⟩
  linear_combination (norm := module) s0 + s1 + (a + b) • hs + r1 + r2 - (2 : ℂ) • h0

theorem UpperTheory.V.Br.capTwo :
    UpperTheory.V.Br.CapTwo := by
  intro F _ _ _ π v a b h φ hφ
  refine cap2 _ (UpperTheory.V.TR.glRel_Eop v) a b φ fun u => ?_
  have := h.2 u φ hφ
  rw [UpperTheory.V.TR.cap] at this
  norm_num at this ⊢
  exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharpolySmul
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Formalism.WeaklyAdmissibleFiltrations
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere

open UpperTheory.V UpperTheory.V.Af

end UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharOf
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR UpperTheory.V.Af.Nf Matrix

private theorem corner_sc {R S : Type} [CommRing R] [CommRing S] (s : R →ₙ+* S) (u : Rˣ) :
    cornerGL 2 s (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (Units.map (corner s) u) := by
  ext i j
  change (1 : Matrix (Fin 2) (Fin 2) S) i j - s ((1 : Matrix (Fin 2) (Fin 2) R) i j) + s (Matrix.scalar (Fin 2) u.val i j) =
    Matrix.scalar (Fin 2) (1 - s 1 + s u.val) i j
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem flow_const (φ : Sm ℚ 2) (z : Rinf ℚ) (h : lie ℚ 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0) (g : GA ℚ 2) (t : ℝ) :
    φ.1 (g * infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))) = φ.1 g := by
  have h1 : ∀ g, HasDerivAt (fun t : ℝ => φ.1 (g * infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) 0 0 := by
    intro g
    have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
      (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
        refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
        by_cases e : i = j
        · subst e
          have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
          simpa using this
        · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have e : lieD (toL (Matrix.scalar (Fin 2) z)) φ.1 g = 0 := congrArg (fun ψ : Sm ℚ 2 => ψ.1 g) h
    exact e ▸ h1
  have h2 : ∀ s, HasDerivAt (fun t : ℝ => φ.1 (g * infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) 0 s := by
    intro s
    have h3 := h1 (g * infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (expU (s • z))))
    rw [← sub_self s] at h3
    have h4 := h3.comp_sub_const s s
    refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [mul_assoc, ← map_mul, ← map_mul, ← TR.expU_add, ← add_smul, add_sub_cancel]
  have := is_const_of_deriv_eq_zero (fun s => (h2 s).differentiableAt) (fun s => (h2 s).deriv) t 0
  simpa [TR.expU_zero] using this

private theorem red_uniq {M : ℕ} (hM : 1 ≤ M) {x : Af ℚ} {d e : ℤ} (hd : ∃ y ∈ Af.Ohat ℚ, x - d = M * y)
    (he : ∃ y ∈ Af.Ohat ℚ, x - e = M * y) : (d : ZMod M) = e := by
  obtain ⟨y, hy, hd⟩ := hd
  obtain ⟨z, hz, he⟩ := he
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h0 : algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * M = 1 := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hM', map_one]
  have h1 : algebraMap ℚ (Af ℚ) ((M : ℚ)⁻¹ * ((e : ℚ) - d)) = y - z := by
    rw [map_mul, map_sub, map_intCast, map_intCast]
    linear_combination algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * (hd - he) + (y - z) * h0
  obtain ⟨n, hn⟩ := ratAd.2.2 _ (h1 ▸ sub_mem hy hz)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨n, ?_⟩
  rw [inv_mul_eq_iff_eq_mul₀ hM'] at hn
  exact_mod_cast hn

private theorem red_ex {M : ℕ} (hM : 1 ≤ M) : ∃ ρ : ↥(Af.Ohat ℚ) →* ZMod M,
    (∀ (x : ↥(Af.Ohat ℚ)) (d : ℤ), (∃ y ∈ Af.Ohat ℚ, (x : Af ℚ) - d = M * y) → ρ x = d) ∧
    ∀ x, ρ x = 1 → ∃ y ∈ Af.Ohat ℚ, (x : Af ℚ) - 1 = M * y := by
  choose f hf using fun x : ↥(Af.Ohat ℚ) => ratAd.2.1 M hM x x.2
  refine ⟨⟨⟨fun x => f x, ?_⟩, fun a b => ?_⟩, fun x d h => red_uniq hM (hf x) h, fun x hx => ?_⟩
  · have := red_uniq hM (e := 1) (hf 1) ⟨0, zero_mem _, by simp⟩
    simpa using this
  · obtain ⟨y, hy, h1⟩ := hf a
    obtain ⟨z, hz, h2⟩ := hf b
    have := red_uniq hM (e := f a * f b) (hf (a * b)) ⟨a * z + f b * y,
      add_mem (mul_mem a.2 hz) (mul_mem (intCast_mem _ _) hy), by
        rw [Subring.coe_mul, Int.cast_mul]
        linear_combination (a : Af ℚ) * h2 + (f b : Af ℚ) * h1⟩
    simpa using this
  · obtain ⟨y, hy, h1⟩ := hf x
    have h2 : ((1 : ℤ) : ZMod M) = f x := by rw [Int.cast_one]; exact hx.symm
    obtain ⟨n, hn⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h2
    have h3 := congrArg (Int.cast : ℤ → Af ℚ) hn
    push_cast at h3
    exact ⟨y + n, add_mem hy (intCast_mem _ _), by linear_combination h1 + h3⟩

private theorem ext_char {G : Type} [CommGroup G] {N : ℕ} [NeZero N] (π : G →* (ZMod N)ˣ) (ψ : G →* ℂˣ) (h : π.ker ≤ ψ.ker) :
    ∃ χ : DirichletCharacter ℂ N, ∀ g, χ (π g) = ψ g := by
  have hs := π.rangeRestrict_surjective
  let f : π.range →* ℂˣ := MonoidHom.liftOfSurjective _ hs ⟨ψ, by rwa [MonoidHom.ker_rangeRestrict]⟩
  have hf : ∀ g, f (π.rangeRestrict g) = ψ g := fun g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  obtain ⟨F, hF⟩ := MonoidHom.domRestrict_surjective ℂ π.range f
  refine ⟨MulChar.ofUnitHom F, fun g => ?_⟩
  rw [← hf, ← hF]
  simp

theorem UpperTheory.V.Br.charOf :
    UpperTheory.V.Br.CharOf := by
  intro N hN ω φ hφ hE hK hc
  have : NeZero N := ⟨by omega⟩
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (Subtype.ext (funext h))
  have key : ∀ z : Ideles ℚ, φ.1 (g * GeneralLinearGroup.scalar (Fin 2) z) = φ.1 g → ω.1 z = 1 := fun z h => by
    rw [← GeneralLinearGroup.scalar_commute, hc] at h
    exact Units.ext (mul_right_cancel₀ hg (h.trans (one_mul _).symm))
  obtain ⟨ρ, hρ, hρ1⟩ := red_ex hN
  let j : (↥(Af.Ohat ℚ))ˣ →* (Af ℚ)ˣ := Units.map (Af.Ohat ℚ).subtype.toMonoidHom
  obtain ⟨χ, hχ⟩ := ext_char (Units.map ρ) (ω.1.comp ((finId ℚ).comp j))⁻¹ (fun u hu => by
    have h1 : ρ u = 1 := congrArg Units.val hu
    have h2 : GeneralLinearGroup.scalar (Fin 2) (j u) ∈ K1G N := by
      have hm : ∀ w a b, GeneralLinearGroup.scalar (Fin 2) (j w) a b ∈ Af.Ohat ℚ := fun w a b => by
        by_cases e : a = b
        · simp [e, j]
        · simp [e]
      refine (memK N _).2 ⟨hm u, ?_, ⟨0, zero_mem _, by simp⟩, ?_⟩
      · rw [← map_inv, ← map_inv]
        exact hm _
      · simpa [j] using hρ1 u h1
    have h3 : φ.1 (g * finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (j u))) = φ.1 g :=
      congrFun (congrArg Subtype.val (hK _ h2)) g
    have s3 : finGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) (j u)) = GeneralLinearGroup.scalar (Fin 2) (finId ℚ (j u)) :=
      corner_sc _ _
    rw [s3] at h3
    change (ω.1 (finId ℚ (j u)))⁻¹ = 1
    rw [key _ h3, inv_one])
  refine ⟨χ, fun t ht => ?_, fun u hu d hd => ?_⟩
  · classical
    have h0 : lie ℚ 2 (toL (Matrix.scalar (Fin 2) (Pi.single Rat.infinitePlace 1))) φ = 0 := by
      rw [← hE Rat.infinitePlace, TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add (f := _)]
      congr 2
      ext i j v
      rw [Subsingleton.elim v Rat.infinitePlace]
      fin_cases i <;> fin_cases j <;> simp
    have h1 := flow_const φ _ h0 g (Real.log (t.val Rat.infinitePlace))
    have h2 : expU (Real.log (t.val Rat.infinitePlace) • (Pi.single Rat.infinitePlace 1 : Rinf ℚ)) = t := by
      refine Units.ext (funext fun v => ?_)
      rw [Subsingleton.elim v Rat.infinitePlace]
      simp [Real.exp_log (ht _)]
    have s2 : infGL ℚ 2 (GeneralLinearGroup.scalar (Fin 2) t) = GeneralLinearGroup.scalar (Fin 2) (infId ℚ t) :=
      corner_sc _ _
    rw [h2, s2] at h1
    exact key _ h1
  · let u' : (↥(Af.Ohat ℚ))ˣ := ⟨⟨u, hu.1⟩, ⟨_, hu.2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
    have h1 : χ (ρ ⟨u, hu.1⟩) = ((ω.1 (finId ℚ u))⁻¹ : ℂˣ) := hχ u'
    rw [← hρ ⟨u, hu.1⟩ d hd, h1]
    exact Units.mul_inv _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Sl2Low
namespace UpperTheory.V.Br

section

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W R L : Module.End ℂ V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {k : ℕ}

private theorem wt_low (hL : W * L - L * W = (-2 : ℂ) • L) {x : V} {n : ℤ} (hx : W x = (n : ℂ) • x) :
    W (L x) = ((n - 2 : ℤ) : ℂ) • L x := by
  have h := congrArg (fun f : Module.End ℂ V => f x) hL
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  push_cast
  module

private theorem cas (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W)) {x : V} {n : ℤ}
    (hx : W x = (n : ℂ) • x) :
    R (L x) = ((((k : ℤ) * (k - 2) - n * (n - 2) : ℤ) : ℂ) / 4) • x := by
  have h := congrArg (fun f : Module.End ℂ V => f x) hC
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul,
    Module.End.one_apply] at h
  have e : R (L x) = (1 / 4 : ℂ) • (4 : ℂ) • R (L x) := by
    rw [smul_smul]; norm_num
  rw [e, h]
  push_cast
  module

private theorem bound (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y)) (hH : ∀ x y, H (L x) y = -H x (R y))
    {x : V} (hx0 : x ≠ 0) {n : ℤ} (hx : W x = (n : ℂ) • x) : (k : ℤ) * (k - 2) ≤ n * (n - 2) := by
  by_contra hlt
  push_neg at hlt
  have hltR : (n : ℝ) * (n - 2) < (k : ℝ) * (k - 2) := by exact_mod_cast hlt
  set c : ℝ := ((k : ℝ) * (k - 2) - n * (n - 2)) / 4 with hc
  have hcpos : 0 < c := div_pos (by linarith) (by norm_num)
  have hcC : ((((k : ℤ) * (k - 2) - n * (n - 2) : ℤ) : ℂ) / 4) = (c : ℂ) := by
    rw [hc]; push_cast; ring
  have hwl := wt_low hL hx
  have h1 : H x (L x) = 0 := by
    have e := hW x (L x)
    rw [hx, hwl] at e
    simp [map_smulₛₗ] at e
    rcases e with e | e
    · have h2 : (2 : ℂ) = 0 := by linear_combination e
      norm_num at h2
    · exact e
  have h2 : H (L x) x = 0 := by
    have e := hW (L x) x
    rw [hwl, hx] at e
    simp [map_smulₛₗ] at e
    exact e
  have h3 : H (L x) (L x) = -(c : ℂ) * H x x := by
    have e := hH x (L x)
    rw [cas hC hx, hcC] at e
    simp only [map_smul, smul_eq_mul] at e
    rw [e]; ring
  set s : ℂ := ((Real.sqrt c : ℝ) : ℂ) with hsdef
  have hs : (starRingEnd ℂ) s = s := Complex.conj_ofReal _
  have hss : s * s = (c : ℂ) := by
    rw [hsdef, ← Complex.ofReal_mul, Real.mul_self_sqrt hcpos.le]
  have hy : H (s • x + L x) (s • x + L x) = 0 := by
    simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hs,
      h1, h2, h3, RingHom.id_apply]
    ring_nf
    linear_combination (H x x) * hss
  have hy0 := h0 _ hy
  have hLx : L x = -(s • x) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hy0)
  have e1 : W (L x) = -(s • ((n : ℂ) • x)) := by rw [hLx, map_neg, map_smul, hx]
  rw [hwl, hLx] at e1
  have key : ((2 : ℂ) * s) • x = 0 := by
    have e2 : ((2 : ℂ) * s) • x = (((n - 2 : ℤ) : ℂ) • -(s • x)) - (-(s • ((n : ℂ) • x))) := by
      push_cast; module
    rw [e2, e1, sub_self]
  rcases smul_eq_zero.mp key with h | h
  · have hs0 : s = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact h'
    have hc0 : (c : ℂ) = 0 := by rw [← hss, hs0, mul_zero]
    have : c = 0 := by exact_mod_cast hc0
    linarith
  · exact hx0 h

private theorem descend (hk : 3 ≤ k) (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y)) (hH : ∀ x y, H (L x) y = -H x (R y))
    (j : ℕ) : ∀ x : V, x ≠ 0 → W x = ((j : ℤ) : ℂ) • x → ∃ x, x ≠ 0 ∧ W x = (k : ℂ) • x ∧ L x = 0 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro x hx0 hx
  have hb := bound hL hC h0 hW hH hx0 hx
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hj2 : 2 ≤ j := by
    by_contra h
    push_neg at h
    interval_cases j <;> (push_cast at hb; nlinarith)
  by_cases hL0 : L x = 0
  · refine ⟨x, hx0, ?_, hL0⟩
    have hc := cas hC hx
    rw [hL0, map_zero] at hc
    have hq : ((((k : ℤ) * (k - 2) - ((j : ℤ) : ℤ) * ((j : ℤ) - 2) : ℤ)) : ℂ) / 4 = 0 := by
      rcases smul_eq_zero.mp hc.symm with h | h
      · exact h
      · exact absurd h hx0
    have hq' : (k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) = 0 := by
      have h4 : (((k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) : ℤ) : ℂ) = 0 := by
        linear_combination 4 * hq
      exact_mod_cast h4
    have hf : ((k : ℤ) - j) * ((k : ℤ) + j - 2) = 0 := by linear_combination hq'
    have hjk : j = k := by
      rcases mul_eq_zero.mp hf with h | h
      · omega
      · omega
    rw [hx, hjk]
    simp
  · have hwl := wt_low hL hx
    refine ih (j - 2) (by omega) (L x) hL0 ?_
    rw [hwl, show ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 by omega]

end

theorem sl2Low : UpperTheory.V.Br.Sl2Low := by
  intro V _ _ W R L H k hk hR hL hC hC' h0 hW hRH hLH hex
  obtain ⟨x, hx0, n, hx⟩ := hex
  have hb := bound hL hC h0 hW hLH hx0 hx
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hf : (n - k) * (n + k - 2) = n * (n - 2) - k * (k - 2) := by ring
  rcases le_or_gt (k : ℤ) n with hn | hn
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j := ⟨n.toNat, by omega⟩
    obtain ⟨y, hy0, hy1, hy2⟩ := descend hk hL hC h0 hW hLH j x hx0 hx
    exact ⟨y, hy0, Or.inl ⟨hy1, hy2⟩⟩
  · have hn2 : n + k - 2 ≤ 0 := by nlinarith
    obtain ⟨j, hj⟩ : ∃ j : ℕ, -n = j := ⟨(-n).toNat, by omega⟩
    have hL' : (-W) * R - R * (-W) = (-2 : ℂ) • R := by
      rw [show (-W) * R - R * (-W) = -(W * R - R * W) by noncomm_ring, hR]
      module
    have hC2 : (4 : ℂ) • (L * R) = ((k : ℂ) * (k - 2)) • 1 - ((-W) * (-W) - (2 : ℂ) • (-W)) := by
      rw [hC']
      congr 1
      rw [neg_mul_neg, smul_neg, sub_neg_eq_add]
    have hW' : ∀ a b, H ((-W) a) b = H a ((-W) b) := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg, LinearMap.neg_apply, hW]
    have hx' : (-W) x = ((j : ℤ) : ℂ) • x := by
      rw [LinearMap.neg_apply, hx, ← neg_smul, ← hj]
      push_cast
      rfl
    obtain ⟨y, hy0, hy1, hy2⟩ :=
      descend (W := -W) (R := L) (L := R) (H := H) hk hL' hC2 h0 hW' hRH j x hx0 hx'
    refine ⟨y, hy0, Or.inr ⟨?_, hy2⟩⟩
    rw [neg_smul, ← hy1, LinearMap.neg_apply, neg_neg]

end UpperTheory.V.Br
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ClTwist
noncomputable section

open CongruenceSubgroup UpperHalfPlane ModularForm UpperTheory.V.Af Matrix.GeneralLinearGroup
open scoped MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Br

private theorem tw_coeffs {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) :
    ∃ c : ZMod N → ℂ, (∀ n : ZMod N, ∑ u, c u * ZMod.stdAddChar (u * n) = ψ n) ∧
      ∀ d u : ZMod N, IsUnit d → c u = ψ d * c (d * u) := by
  refine ⟨fun u => (N : ℂ)⁻¹ * ZMod.dft (fun j => ψ j) u, fun n => ?_, fun d u hd => ?_⟩
  · have h := ZMod.invDFT_apply (ZMod.dft (fun j => ψ j)) n
    rw [LinearEquiv.symm_apply_apply] at h
    rw [h, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_eq_mul]; ring
  · obtain ⟨d, rfl⟩ := hd
    have h := ZMod.dft_comp_unitMul (fun j => ψ j) d (d * u)
    simp only [map_mul] at h
    rw [ZMod.dft_const_mul, Units.inv_mul_cancel_left] at h
    simp only [← h]; ring

private def tG (N : ℕ) (u : ℤ) : GL (Fin 2) ℝ := upperRightHom ((u : ℝ) / N)

private theorem tG_val (N : ℕ) (u : ℤ) : (tG N u).1 = !![1, (u : ℝ) / N; 0, 1] := rfl

private theorem tG_det (N : ℕ) (u : ℤ) : (tG N u).det.val = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, tG_val]; simp

private theorem tG_σ (N : ℕ) (u : ℤ) (c : ℂ) : σ (tG N u) c = c := by
  have : 0 < (tG N u).det.val := by rw [tG_det]; exact one_pos
  rw [σ, if_pos this]; rfl

private theorem tG_apply (N : ℕ) (u : ℤ) (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    (f ∣[k] tG N u) z = f (((u : ℝ) / N) +ᵥ z) := by
  have e : tG N u • z = ((u : ℝ) / N) +ᵥ z := by
    ext
    rw [coe_smul_of_det_pos (by rw [tG_det]; exact one_pos)]
    simp [num, denom, tG_val, add_comm]
  rw [slash_apply, tG_σ, tG_det, e]
  simp [denom, tG_val]

private theorem tG_comm {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (N * N)) (u v : ℤ)
    (h : (v : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) ^ 2 * u) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧ ((δ 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) ∧
      ∀ (k : ℤ) (f : ℍ → ℂ), (f ∣[k] tG N u) ∣[k] γ = (f ∣[k] δ) ∣[k] tG N v := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨c, hc⟩ := hγ
  push_cast at hc
  have hd := γ.det_coe
  rw [Matrix.det_fin_two, hc] at hd
  have hd' := congrArg (Int.cast : ℤ → ZMod N) hd
  push_cast at hd'
  rw [ZMod.natCast_self] at hd'
  have h1 : (N : ℤ) ∣ u * γ 1 1 - v * γ 0 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h]
    linear_combination (-(u : ZMod N) * ((γ 1 1 : ℤ) : ZMod N)) * hd'
  obtain ⟨e, he⟩ := h1
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  obtain ⟨δ, d00, d01, d10, d11⟩ : ∃ δ : SL(2, ℤ), δ 0 0 = γ 0 0 + u * c * N ∧ δ 0 1 = γ 0 1 + e - u * v * c ∧
      δ 1 0 = N * N * c ∧ δ 1 1 = γ 1 1 - c * v * N := by
    refine ⟨⟨!![γ 0 0 + u * c * N, γ 0 1 + e - u * v * c; N * N * c, γ 1 1 - c * v * N], ?_⟩, rfl, rfl, rfl, rfl⟩
    rw [Matrix.det_fin_two_of]
    linear_combination hd + N * c * he
  refine ⟨δ, ?_, ?_, fun k f => ?_⟩
  · rw [Gamma0_mem, d10]; simp
  · rw [d11]; simp
  · rw [SL_slash, SL_slash, ← SlashAction.slash_mul, ← SlashAction.slash_mul]
    congr 1
    have he' : (u : ℝ) * (γ 1 1 : ℤ) - v * (γ 0 0 : ℤ) = N * e := by exact_mod_cast he
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tG_val, Matrix.mul_apply, Fin.sum_univ_two, hc, d00, d01, d10, d11] <;> field_simp
    all_goals first | ring1 | linear_combination he'

private theorem tG_cusp (N : ℕ) (u : ℤ) {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : IsCusp (tG N u • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c, rfl⟩ := hc
  refine ⟨(upperRightHom ((u : ℚ) / N) : GL (Fin 2) ℚ) • c, ?_⟩
  rw [← Rat.coe_castHom, OnePoint.map_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tG_val, upperRightHom]

private def tw (N : ℕ) [NeZero N] (k : ℕ) (c : ZMod N → ℂ) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ u : ZMod N, c u • f ∣[(k : ℤ)] tG N (u.val : ℤ)

private theorem tw_char {N : ℕ} [NeZero N] (k : ℕ) (χ ψ : DirichletCharacter ℂ N) {c : ZMod N → ℂ}
    (hc : ∀ d u : ZMod N, IsUnit d → c u = ψ d * c (d * u)) {f : ℍ → ℂ} (hf : HasChar k χ f) :
    HasChar k (DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ ^ 2)) (tw N k c f) := by
  intro γ hγ
  have hu : IsUnit ((γ 1 1 : ℤ) : ZMod (N * N)) := by
    have dγ := congrArg (Int.cast : ℤ → ZMod (N * N)) (γ.det_coe)
    rw [Matrix.det_fin_two] at dγ
    push_cast at dγ
    rw [Gamma0_mem.1 hγ, mul_zero, sub_zero] at dγ
    exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans dγ)
  have hu' : IsUnit ((γ 1 1 : ℤ) : ZMod N) := by
    simpa using hu.map (ZMod.castHom (dvd_mul_right N N) (ZMod N))
  have e : DirichletCharacter.changeLevel (dvd_mul_right N N) (χ * ψ ^ 2) ((γ 1 1 : ℤ) : ZMod (N * N)) =
      χ ((γ 1 1 : ℤ) : ZMod N) * ψ (((γ 1 1 : ℤ) : ZMod N) ^ 2) := by
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ * ψ ^ 2) (dvd_mul_right N N) hu.unit
    rw [IsUnit.unit_spec, ZMod.cast_intCast (dvd_mul_right N N)] at this
    rw [this, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero, map_pow]
  have hb : Function.Bijective fun u : ZMod N => ((γ 1 1 : ℤ) : ZMod N) ^ 2 * u :=
    ((hu'.pow 2).unit.mulLeft).bijective
  rw [e, tw, SlashAction.sum_slash, Finset.smul_sum,
    ← hb.sum_comp fun y => (χ ((γ 1 1 : ℤ) : ZMod N) * ψ (((γ 1 1 : ℤ) : ZMod N) ^ 2)) • c y • f ∣[(k : ℤ)] tG N (y.val : ℤ)]
  refine Finset.sum_congr rfl fun u _ => ?_
  obtain ⟨δ, h0, h1, h⟩ := tG_comm γ hγ (u.val : ℤ) ((((γ 1 1 : ℤ) : ZMod N) ^ 2 * u).val : ℤ) (by simp)
  rw [SL_smul_slash, h, hf δ h0, h1, smul_slash, tG_σ, smul_smul, smul_smul, hc _ u (hu'.pow 2)]
  congr 1; ring

end UpperTheory.V.Br

theorem UpperTheory.V.Br.clTwist :
    UpperTheory.V.Br.ClTwist := by
  intro N k _ χ ψ f hf
  obtain ⟨c, hc1, hc2⟩ := tw_coeffs ψ
  have hch := tw_char k χ ψ hc2 hf
  haveI : NeZero (N * N) := ⟨mul_ne_zero (NeZero.ne N) (NeZero.ne N)⟩
  have h1 : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have h2 : (1 : ℝ) ∈ (Gamma1 (N * N) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hsum : ∀ τ : ℍ, HasSum (fun m => coef f m • Function.Periodic.qParam 1 τ ^ m) (f τ) := fun τ =>
    hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f h1) f.holo'
      (ModularFormClass.bdd_at_infty f) τ
  let g : CuspForm (Gamma1 (N * N)) (k : ℤ) :=
    { toFun := tw N k c f
      slash_action_eq' := fun A hA => by
        obtain ⟨A, hA, rfl⟩ := hA
        have h := hch A (Gamma1_in_Gamma0 _ hA)
        rw [((Gamma1_mem _ A).1 hA).2.1, map_one, one_smul] at h
        exact h
      holo' := by
        change MDiff (tw N k c f)
        unfold tw
        refine Finset.sum_induction _ (fun F : ℍ → ℂ => MDiff F) (fun a b ha hb => ha.add hb) mdifferentiable_const
          fun u _ => ?_
        exact (MDifferentiable.slash f.holo' _ _).const_smul _
      zero_at_cusps' := fun {x} hx => by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hx
        rw [OnePoint.isZeroAt_iff_forall_SL2Z hx]
        intro γ hγ
        rw [tw, SlashAction.sum_slash]
        refine Submodule.sum_mem (zeroAtImInftySubmodule ℂ) fun u _ => ?_
        rw [SL_smul_slash]
        refine Submodule.smul_mem _ _ ?_
        have h3 := tG_cusp N (u.val : ℤ) hx
        rw [← Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (Gamma1 N : Subgroup (GL (Fin 2) ℝ))] at h3
        exact OnePoint.IsZeroAt.smul_iff.1 (f.zero_at_cusps' h3) _ hγ }
  refine ⟨g, hch, fun n => ?_⟩
  refine (ModularFormClass.qExpansion_coeff_unique (f := g)
    (c := fun n => ψ (n : ZMod N) * coef f n) one_pos h2 (fun τ => ?_) n).symm
  have a := hasSum_sum (s := Finset.univ) fun (u : ZMod N) _ => (hsum ((((u.val : ℤ) : ℝ) / N) +ᵥ τ)).mul_left (c u)
  have e : ∑ u : ZMod N, c u * f ((((u.val : ℤ) : ℝ) / N) +ᵥ τ) = tw N k c f τ := by
    rw [tw, Finset.sum_apply]
    simp only [Pi.smul_apply, tG_apply, smul_eq_mul]
  rw [e] at a
  refine cast (congrArg (HasSum · (tw N k c f τ)) (funext fun m => ?_)) a
  rw [← hc1, Finset.sum_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun u _ => ?_
  have e2 : ZMod.stdAddChar (u * (m : ZMod N)) * Function.Periodic.qParam 1 τ ^ m =
      Function.Periodic.qParam 1 (((((u.val : ℤ) : ℝ) / N) +ᵥ τ : ℍ) : ℂ) ^ m := by
    have : u * (m : ZMod N) = ((u.val * m : ℤ) : ZMod N) := by simp
    rw [this, ZMod.stdAddChar_coe, Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul,
      ← Complex.exp_nat_mul, ← Complex.exp_add, coe_vadd]
    congr 1
    push_cast
    ring
  rw [← e2]
  simp only [smul_eq_mul]
  ring
end
end
