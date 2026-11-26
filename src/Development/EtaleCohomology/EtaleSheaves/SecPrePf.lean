module

public import Development.EtaleCohomology.EtaleSheaves.SHTensorPf
public import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
public import Development.EtaleCohomology.EtaleSheaves.MayerVietorisSequence

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.SecPrePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite

namespace LateralTheory.E.SecPrePf
open LateralTheory.E.t_E3Cut

theorem id_mem (hSec : SHSection) (A : CommRingCat.{0}) (hA : SH A) {S : Sieve (Spec A)}
    (hS : S ∈ Scheme.etaleTopology (Spec A)) : S.arrows (𝟙 _) := by
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  have : IsLocalRing A := hA.elim fun h _ => h.toIsLocalRing
  obtain ⟨hcov, -⟩ := (Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀
  obtain ⟨j, y, hy⟩ := hcov (IsLocalRing.closedPoint A : PrimeSpectrum A)
  have : Etale (𝒰.f j) := 𝒰.map_prop j
  have hsurj : Function.Surjective (𝒰.f j) := by
    intro z
    have hopen : IsOpen (Set.range (𝒰.f j)) := (𝒰.f j).isOpenMap.isOpen_range
    have hmem : (IsLocalRing.closedPoint A : PrimeSpectrum A) ∈ Set.range (𝒰.f j) := ⟨y, hy⟩
    exact (IsLocalRing.specializes_closedPoint (z : PrimeSpectrum A)).mem_open hopen hmem
  have : Surjective (𝒰.f j) := ⟨hsurj⟩
  obtain ⟨s, hs⟩ := hSec A hA (𝒰.f j)
  have h1 : S.arrows (𝒰.f j) := hle _ _ (Presieve.ofArrows.mk j)
  have h2 := S.downward_closed h1 s
  rwa [hs] at h2

theorem mem_of_cov (hSec : SHSection) (A : CommRingCat.{0}) (hA : SH A) {V : Scheme.{0}} (h : Spec A ⟶ V)
    (S : Sieve V) (hS : S ∈ Scheme.etaleTopology V) : S.arrows h := by
  have := id_mem hSec A hA (Scheme.etaleTopology.pullback_stable h hS)
  simpa using this

variable {R : Type} [CommRing R]

def sky (U : Scheme.{0}) (N : ModuleCat.{1} (ULift.{1} R)) : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R) where
  obj V := ModuleCat.of _ ((U ⟶ V.unop) → N)
  map g := ModuleCat.ofHom
    { toFun := fun φ h => φ (h ≫ g.unop)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

theorem sky_isSheaf (U : Scheme.{0})
    (hU : ∀ {V : Scheme.{0}} (h : U ⟶ V) (S : Sieve V), S ∈ Scheme.etaleTopology V → S.arrows h)
    (N : ModuleCat.{1} (ULift.{1} R)) : Presheaf.IsSheaf Scheme.etaleTopology (sky U N) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget (ModuleCat.{1} (ULift.{1} R))),
    isSheaf_iff_isSheaf_of_type]
  intro V S hS x hx
  have hc := hx.to_sieveCompatible
  refine ⟨fun h => x h (hU h S hS) (𝟙 U), ?_, ?_⟩
  · intro W f hf
    funext k
    have e := congrFun (hc f k hf) (𝟙 U)
    change x (k ≫ f) _ (𝟙 U) = x f hf k
    rw [e]
    change x f hf (𝟙 U ≫ k) = _
    rw [Category.id_comp]
  · intro t ht
    funext h
    have e := congrFun (ht h (hU h S hS)) (𝟙 U)
    change t (𝟙 U ≫ h) = _ at e
    rw [Category.id_comp] at e
    exact e

@[simps]
def toSky (Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}) {N : ModuleCat.{1} (ULift.{1} R)}
    (g : Q.obj (op U) ⟶ N) : Q ⟶ sky U N where
  app V := ModuleCat.ofHom
    { toFun := fun p h => g.hom ((Q.map h.op).hom p)
      map_add' := fun _ _ => by funext h; simp
      map_smul' := fun _ _ => by funext h; simp }
  naturality V W f := by
    ext p
    funext h
    change g.hom ((Q.map h.op).hom ((Q.map f).hom p)) = g.hom ((Q.map (h ≫ f.unop).op).hom p)
    rw [op_comp, Quiver.Hom.op_unop, Q.map_comp]
    rfl

theorem toSheafify_bij (U : Scheme.{0})
    (hU : ∀ {V : Scheme.{0}} (h : U ⟶ V) (S : Sieve V), S ∈ Scheme.etaleTopology V → S.arrows h)
    (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    Function.Bijective ((toSheafify Scheme.etaleTopology P).app (op U)).hom := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have e := toSheafify_sheafifyLift Scheme.etaleTopology (toSky P U (𝟙 _)) (sky_isSheaf U hU _)
    have e2 := congrFun (congrArg (fun φ => (φ.app (op U)).hom x) e) (𝟙 U)
    simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero] at e2
    have e3 : (P.map (𝟙 U).op).hom x = 0 := e2.symm
    rwa [op_id, P.map_id] at e3
  · intro y
    let η := toSheafify Scheme.etaleTopology P
    let Q := sheafify Scheme.etaleTopology P
    let g : Q.obj (op U) ⟶ ModuleCat.of _ (Q.obj (op U) ⧸ LinearMap.range (η.app (op U)).hom) :=
      ModuleCat.ofHom (Submodule.mkQ _)
    have e := sheafify_hom_ext Scheme.etaleTopology (toSky Q U g) 0 (sky_isSheaf U hU _) (by
      ext V p
      funext h
      have nat : (Q.map h.op).hom ((η.app V).hom p) = (η.app (op U)).hom ((P.map h.op).hom p) :=
        (congrArg (fun φ => φ.hom p) (η.naturality h.op)).symm
      simp only [NatTrans.comp_app, toSky_app, Limits.comp_zero]
      change (Submodule.mkQ _) ((Q.map h.op).hom (η.app V |>.hom p)) = 0
      rw [nat, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨_, rfl⟩)
    have e2 := congrFun (congrArg (fun φ => (φ.app (op U)).hom y) e) (𝟙 U)
    simp only [toSky_app] at e2
    change (Submodule.mkQ _) ((Q.map (𝟙 U).op).hom y) = 0 at e2
    rw [op_id, Q.map_id, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at e2
    obtain ⟨x, hx⟩ := e2
    exact ⟨x, hx⟩

theorem SecPre_of (hSec : SHSection) : LateralTheory.E.SHEqvPf.SecPre := by
  intro _ q i A hA
  exact toSheafify_bij (R := ZMod q) (Spec A) (fun h S hS => mem_of_cov hSec A hA h S hS) (Scheme.Γ ⋙ twF q i)

end LateralTheory.E.SecPrePf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.PushPf
noncomputable section
open CategoryTheory Limits Polynomial

namespace LateralTheory.E.PushPf
open LateralTheory.E.t_E3Cut

section
variable {C D : Type} [CommRing C] [CommRing D] (v : C →+* D) (Q : Ideal D) [Q.IsPrime]

abbrev phi : C →+* D ⧸ Q := (Ideal.Quotient.mk Q).comp v

lemma phi_comp : (phi v Q).range.subtype.comp (phi v Q).rangeRestrict = phi v Q := by ext; rfl

lemma alg_of (x : D) (p : C[X]) (n : ℕ) (hn : v (p.coeff n) ∉ Q) (hp : p.eval₂ v x ∈ Q) :
    IsAlgebraic (phi v Q).range (Ideal.Quotient.mk Q x) := by
  refine ⟨p.map (phi v Q).rangeRestrict, ?_, ?_⟩
  · intro h0
    have := congrArg (fun q => q.coeff n) h0
    simp only [coeff_map, coeff_zero] at this
    apply hn
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h2 := congrArg Subtype.val this
    simpa using h2
  · rw [aeval_def, eval₂_map]
    have : (algebraMap (phi v Q).range (D ⧸ Q)).comp (phi v Q).rangeRestrict = phi v Q := phi_comp v Q
    rw [this, phi, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
    exact hp

lemma of_alg (x : D) (h : IsAlgebraic (phi v Q).range (Ideal.Quotient.mk Q x)) :
    ∃ p : C[X], (∃ n, v (p.coeff n) ∉ Q) ∧ p.eval₂ v x ∈ Q := by
  obtain ⟨q, hq0, hq⟩ := h
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective _ (phi v Q).rangeRestrict_surjective q
  refine ⟨p, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    apply hq0
    ext n
    simp only [coeff_map, coeff_zero]
    simp only [ZeroMemClass.coe_zero]
    change Ideal.Quotient.mk Q (v (p.coeff n)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hall n)
  · rw [aeval_def, eval₂_map] at hq
    have : (algebraMap (phi v Q).range (D ⧸ Q)).comp (phi v Q).rangeRestrict = phi v Q := phi_comp v Q
    rw [this, phi, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem] at hq
    exact hq
end

end LateralTheory.E.PushPf

namespace LateralTheory.E.PushPf
open LateralTheory.E.t_E3Cut TensorProduct

lemma gen {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D)
    (h : IsPushout f g u v) (T : Subring D) (hu : ∀ b, u.hom b ∈ T) (hv : ∀ c, v.hom c ∈ T) (d : D) :
    d ∈ T := by
  algebraize [f.hom, g.hom]
  have ht : IsPushout f g (CommRingCat.ofHom (S := B ⊗[A] C) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := B ⊗[A] C) Algebra.TensorProduct.includeRight.toRingHom) :=
    CommRingCat.isPushout_tensorProduct A B C
  set e := ht.isoIsPushout _ _ h
  have h1 : ∀ b : B, e.hom.hom (b ⊗ₜ[A] (1 : C)) = u.hom b := fun b => by
    have := congr($(ht.inl_isoIsPushout_hom _ _ h).hom b)
    dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have h2 : ∀ c : C, e.hom.hom ((1 : B) ⊗ₜ[A] c) = v.hom c := fun c => by
    have := congr($(ht.inr_isoIsPushout_hom _ _ h).hom c)
    dsimp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at this
    exact this
  have hd : d = e.hom.hom (e.inv.hom d) := by
    have := congrArg (fun φ => φ.hom d) e.inv_hom_id
    simpa using this.symm
  rw [hd]
  induction (e.inv.hom d) using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact T.zero_mem
  | tmul b c =>
    have hbc : b ⊗ₜ[A] c = (b ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] c) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hbc, map_mul, h1, h2]
    exact T.mul_mem (hu b) (hv c)
  | add x y hx hy => rw [map_add (f := _)]; exact T.add_mem hx hy

theorem Push_of : LateralTheory.E.AlgResPropsPf.Push := by
  intro A B C D f g u v h hf Q hQ d
  have hw : ∀ a, u.hom (f.hom a) = v.hom (g.hom a) := fun a => by
    have := congrArg (fun φ => φ.hom a) h.w
    simpa using this
  let S := (phi v.hom Q).range
  let T : Subring D :=
    { carrier := {x | IsAlgebraic S (Ideal.Quotient.mk Q x)}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_mul] at *; exact ha.mul hb
      one_mem' := by simp only [Set.mem_ofPred_eq, map_one]; exact isAlgebraic_one
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at *; exact ha.add hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact isAlgebraic_zero
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, map_neg] at *
        have := (isAlgebraic_algebraMap (R := S) (A := D ⧸ Q) (-1)).mul ha
        simpa using this }
  have hv : ∀ c, v.hom c ∈ T := fun c => by
    refine alg_of v.hom Q (v.hom c) (X - Polynomial.C c) 1 ?_ ?_
    · simp only [coeff_sub, coeff_X_one, coeff_C, one_ne_zero, if_false, sub_zero, map_one]
      exact fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1)
    · simp [Q.zero_mem]
  have hu : ∀ b, u.hom b ∈ T := fun b => by
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hf (Q.comap u.hom) (Ideal.comap_isPrime u.hom Q) b
    refine alg_of v.hom Q (u.hom b) (p.map g.hom) n ?_ ?_
    · rw [coeff_map, ← hw]; exact hn
    · have hc : v.hom.comp g.hom = u.hom.comp f.hom := by ext a; exact (hw a).symm
      rw [eval₂_map, hc, ← Polynomial.hom_eval₂]
      exact hp
  exact of_alg v.hom Q d (gen f g u v h T hu hv d)

end LateralTheory.E.PushPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.DomOpenPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.DomOpenPf

theorem algClosed_of_AIC (T : Type) [CommRing T] [IsDomain T] (hT : AIC T) :
    IsAlgClosed (FractionRing T) := by
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  set K := FractionRing T
  set f := algebraMap T K
  have hf : Function.Injective f := IsFractionRing.injective T K
  obtain ⟨b, hb₁, hb₂⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors T) p
  set q := IsLocalization.integerNormalization (nonZeroDivisors T) p
  have hb0 : (b : T) ≠ 0 := nonZeroDivisors.ne_zero hb₁
  have hdeg : q.natDegree = p.natDegree := by
    rw [← natDegree_map_eq_of_injective hf q, hb₂, ← IsScalarTower.algebraMap_smul K b p,
      natDegree_smul_of_smul_regular]
    exact IsSMulRegular.of_ne_zero (by simpa [f] using (map_ne_zero_iff f hf).mpr hb0)
  have hpos : 0 < p.natDegree := Irreducible.natDegree_pos hirr
  have hq0 : q ≠ 0 := by intro h; rw [h] at hdeg; simp at hdeg; omega
  obtain ⟨a, ha⟩ := hT (integralNormalization q) (monic_integralNormalization hq0)
    (by rw [natDegree_integralNormalization]; omega)
  have hlc : f q.leadingCoeff ≠ 0 := (map_ne_zero_iff f hf).mpr (leadingCoeff_ne_zero.mpr hq0)
  refine ⟨f a / f q.leadingCoeff, ?_⟩
  have key := integralNormalization_eval₂_leadingCoeff_mul (p := q) (by omega) f (f a / f q.leadingCoeff)
  rw [mul_div_cancel₀ _ hlc, eval₂_at_apply, ha, map_zero] at key
  have h2 : q.eval₂ f (f a / f q.leadingCoeff) = 0 := by
    rcases mul_eq_zero.mp key.symm with h | h
    · exact absurd (pow_eq_zero_iff'.mp h).1 hlc
    · exact h
  rw [eval₂_eq_eval_map, hb₂, ← IsScalarTower.algebraMap_smul K b p, eval_smul, smul_eq_mul] at h2
  exact (mul_eq_zero.mp h2).resolve_left ((map_ne_zero_iff f hf).mpr hb0)

theorem algebraMap_ne_zero_of_flat (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [Nontrivial D]
    [Algebra T D] [Module.Flat T D] {s : T} (hs : s ≠ 0) : algebraMap T D s ≠ 0 := by
  intro h
  have hr : IsSMulRegular D s := Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs)
  apply one_ne_zero (α := D)
  apply hr
  simp [Algebra.smul_def, h]

theorem exists_frac (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D]
    [Algebra.Etale T D] (hT : AIC T) (a : D) :
    ∃ s t : T, s ≠ 0 ∧ algebraMap T D s * a = algebraMap T D t := by
  classical
  haveI := algClosed_of_AIC T hT
  let M := nonZeroDivisors T
  let S := Localization (Algebra.algebraMapSubmonoid D M)
  have hle : Algebra.algebraMapSubmonoid D M ≤ nonZeroDivisors D := by
    rintro _ ⟨s, hs, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (algebraMap_ne_zero_of_flat T D (nonZeroDivisors.ne_zero hs))
  have : IsDomain S := IsLocalization.isDomain_localization hle
  have : IsLocalization (M.map (algebraMap T D)) S := inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid D M) S)
  have : Algebra.FormallyEtale (FractionRing T) S :=
    Algebra.FormallyEtale.localization_map M (Rₘ := FractionRing T) (Sₘ := S) (S := D)
  have : Algebra.EssFiniteType (FractionRing T) S := Algebra.EssFiniteType.of_comp T (FractionRing T) S
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed (FractionRing T) S
  have hsub : Subsingleton (PrimeSpectrum S) := by
    constructor
    intro p q
    by_contra hpq
    have h0 : ((fun r => if r = p then (1 : FractionRing T) else 0) * fun r => if r = q then 1 else 0) = 0 := by
      funext r; simp only [Pi.mul_apply, Pi.zero_apply]; split_ifs with h1 h2 <;> simp_all
    have : e.symm (fun r => if r = p then (1 : FractionRing T) else 0) * e.symm (fun r => if r = q then 1 else 0) = 0 := by rw [← map_mul, h0, map_zero]
    rcases mul_eq_zero.mp this with h | h
    · have := congrFun (e.symm.injective (h.trans (map_zero _).symm)) p
      simp at this
    · have := congrFun (e.symm.injective (h.trans (map_zero _).symm)) q
      simp at this
  obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum S) := inferInstance
  set x := algebraMap D S a
  have hx : algebraMap (FractionRing T) S (e x p₀) = x := by
    apply e.injective
    funext p
    rw [AlgEquiv.commutes]
    simp [Subsingleton.elim p p₀]
  generalize e x p₀ = c at hx
  obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.mk'_surjective M c
  change IsLocalization.mk' (FractionRing T) t s = c at hts
  refine ⟨s, t, nonZeroDivisors.ne_zero s.2, ?_⟩
  apply IsLocalization.injective S hle
  rw [map_mul, ← IsScalarTower.algebraMap_apply T D S, ← IsScalarTower.algebraMap_apply T D S,
    show algebraMap D S a = x from rfl, ← hx, ← hts,
    IsScalarTower.algebraMap_apply T (FractionRing T) S (s : T), IsScalarTower.algebraMap_apply T (FractionRing T) S t,
    ← map_mul, mul_comm, IsLocalization.mk'_spec]

theorem isEpi (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D]
    [Algebra.Etale T D] (hT : AIC T) : Algebra.IsEpi T D := by
  rw [Algebra.isEpi_iff_forall_one_tmul_eq]
  intro a
  obtain ⟨s, t, hs, hst⟩ := exists_frac T D hT a
  have hr : IsSMulRegular (TensorProduct T D D) s :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hs)
  rw [← sub_eq_zero]
  apply hr
  change s • (1 ⊗ₜ[T] a - a ⊗ₜ[T] 1) = s • (0 : TensorProduct T D D)
  have hsa : s • a = t • (1 : D) := by rw [Algebra.smul_def, hst, Algebra.smul_def, mul_one]
  have e1 : s • ((1 : D) ⊗ₜ[T] a) = t • ((1 : D) ⊗ₜ[T] (1 : D)) := by
    rw [← TensorProduct.tmul_smul, hsa, TensorProduct.tmul_smul]
  have e2 : s • (a ⊗ₜ[T] (1 : D)) = t • ((1 : D) ⊗ₜ[T] (1 : D)) := by
    rw [TensorProduct.smul_tmul', hsa, ← TensorProduct.smul_tmul']
  rw [smul_zero, smul_sub, e1, e2, sub_self]

theorem DomOpen_of : LateralTheory.E.EtAICPf.DomOpen := by
  intro T D _ _ _ _ _ _ hT
  set f := CommRingCat.ofHom (algebraMap T D)
  have : Algebra.IsEpi T D := isEpi T D hT
  have : Epi f := CommRingCat.epi_iff_epi.mpr inferInstance
  have : Mono (Spec.map f) := inferInstanceAs (Mono (Scheme.Spec.map f.op))
  have : Flat (Spec.map f) := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation (Spec.map f) :=
    (LocallyOfFinitePresentation.SpecMap_iff f).mpr (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  exact IsOpenImmersion.of_flat_of_mono _

end LateralTheory.E.DomOpenPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LocAtPf
noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.LocAtPf

structure DivIdx {A : Type} [CommRing A] (S : Submonoid A) : Type where
  val : S

variable {A : Type} [CommRing A] (S : Submonoid A)

instance : Preorder (DivIdx S) where
  le a b := ∃ c : A, (b.val : A) = (a.val : A) * c
  le_refl a := ⟨1, (mul_one _).symm⟩
  le_trans a b c := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    exact ⟨x * y, by rw [hy, hx, mul_assoc]⟩

instance : IsDirected (DivIdx S) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.val * b.val⟩, ⟨(b.val : A), by simp⟩, ⟨(a.val : A), by simp [mul_comm]⟩⟩⟩

instance : Nonempty (DivIdx S) := ⟨⟨1⟩⟩

lemma one_le (a : DivIdx S) : (⟨1⟩ : DivIdx S) ≤ a := ⟨(a.val : A), by simp⟩

lemma unit_of_le {a b : DivIdx S} (h : a ≤ b) :
    IsUnit (algebraMap A (Localization.Away (b.val : A)) (a.val : A)) := by
  obtain ⟨c, hc⟩ := h
  have hb := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (b.val : A)) (b.val : A)
  have e : algebraMap A (Localization.Away (b.val : A)) (b.val : A) =
      algebraMap A (Localization.Away (b.val : A)) (a.val : A) * algebraMap A (Localization.Away (b.val : A)) c := by
    rw [← map_mul, ← hc]
  rw [e] at hb
  exact isUnit_of_mul_isUnit_left hb

def tr {a b : DivIdx S} (h : a ≤ b) :
    Localization.Away (a.val : A) →+* Localization.Away (b.val : A) :=
  IsLocalization.Away.lift (a.val : A) (unit_of_le S h)

lemma tr_alg {a b : DivIdx S} (h : a ≤ b) (x : A) :
    tr S h (algebraMap A _ x) = algebraMap A _ x :=
  IsLocalization.Away.lift_eq _ _ x

def Dg : DivIdx S ⥤ CommRingCat.{0} where
  obj a := CommRingCat.of (Localization.Away (a.val : A))
  map {a b} f := CommRingCat.ofHom (tr S f.le)
  map_id a := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (a.val : A))
    ext x; simp [tr_alg]
  map_comp {a b c} f g := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (a.val : A))
    ext x; simp [tr_alg]

def tN : (Functor.const (DivIdx S)).obj (CommRingCat.of A) ⟶ Dg S where
  app a := CommRingCat.ofHom (algebraMap A (Localization.Away (a.val : A)))
  naturality a b f := by
    apply CommRingCat.hom_ext; ext x
    exact (tr_alg S f.le x).symm

lemma away_ext (a : DivIdx S) {R : CommRingCat.{0}} {f g : (Dg S).obj a ⟶ R}
    (h : ∀ x : A, f ((tN S).app a x) = g ((tN S).app a x)) : f = g := by
  apply CommRingCat.hom_ext
  exact IsLocalization.ringHom_ext (M := Submonoid.powers (a.val : A))
    (S := Localization.Away (a.val : A)) (RingHom.ext h)

variable (B : Type) [CommRing B] [Algebra A B] [IsLocalization S B]

def sApp (a : DivIdx S) : CommRingCat.of (Localization.Away (a.val : A)) ⟶ CommRingCat.of B :=
  CommRingCat.ofHom (IsLocalization.Away.lift (a.val : A) (IsLocalization.map_units B a.val))

lemma sApp_tN (a : DivIdx S) (x : A) : sApp S B a ((tN S).app a x) = algebraMap A B x :=
  IsLocalization.Away.lift_eq _ (IsLocalization.map_units B a.val) x

def sN : Dg S ⟶ (Functor.const (DivIdx S)).obj (CommRingCat.of B) where
  app a := sApp S B a
  naturality a b f := by
    apply CommRingCat.hom_ext
    refine IsLocalization.ringHom_ext (M := Submonoid.powers (a.val : A))
      (S := Localization.Away (a.val : A)) (RingHom.ext fun x => ?_)
    change IsLocalization.Away.lift (b.val : A) (IsLocalization.map_units B b.val) (tr S f.le (algebraMap A _ x)) =
      IsLocalization.Away.lift (a.val : A) (IsLocalization.map_units B a.val) (algebraMap A _ x)
    rw [tr_alg, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]

lemma cocone_alg (c : Cocone (Dg S)) (a : DivIdx S) :
    (tN S).app a ≫ c.ι.app a = (tN S).app ⟨1⟩ ≫ c.ι.app ⟨1⟩ := by
  rw [← c.w (homOfLE (one_le S a)), ← Category.assoc, ← (tN S).naturality]
  simp

def g0 (c : Cocone (Dg S)) : A →+* c.pt := ((tN S).app ⟨1⟩ ≫ c.ι.app ⟨1⟩).hom

lemma awayDivisibilityCocone_baseHom_submonoid_isUnit (c : Cocone (Dg S)) (s : S) : IsUnit (g0 S c (s : A)) := by
  have e : g0 S c (s : A) = c.ι.app ⟨s⟩ ((tN S).app ⟨s⟩ (s : A)) := by
    rw [← CategoryTheory.comp_apply, cocone_alg]; rfl
  rw [e]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (s : A)) (s : A)).map
    (c.ι.app ⟨s⟩).hom

def isColim : IsColimit (Cocone.mk (CommRingCat.of B) (sN S B)) where
  desc c := CommRingCat.ofHom (IsLocalization.lift (M := S) (S := B) (g := g0 S c) (awayDivisibilityCocone_baseHom_submonoid_isUnit S c))
  fac c a := by
    apply away_ext S a
    intro x
    rw [CategoryTheory.comp_apply]
    change CommRingCat.Hom.hom _ (sApp S B a ((tN S).app a x)) = _
    rw [sApp_tN]
    change IsLocalization.lift _ (algebraMap A B x) = _
    rw [IsLocalization.lift_eq, ← CategoryTheory.comp_apply, cocone_alg]
    rfl
  uniq c m hm := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext S
    ext x
    change m.hom (algebraMap A B x) = IsLocalization.lift _ (algebraMap A B x)
    rw [IsLocalization.lift_eq, ← sApp_tN S B ⟨1⟩ x]
    have := congrArg (fun f => f ((tN S).app ⟨1⟩ x)) (hm ⟨1⟩)
    simp only [CategoryTheory.comp_apply] at this
    exact this

theorem locIE (S : Submonoid A) (B : Type) [CommRing B] [Algebra A B] [IsLocalization S B] :
    IE (CommRingCat.ofHom (algebraMap A B)) := by
  refine ⟨DivIdx S, inferInstance, inferInstance, Dg S, tN S, sN S B, isColim S B, fun a => ⟨?_, ?_⟩⟩
  · show RingHom.Etale (CommRingCat.Hom.hom (CommRingCat.ofHom (algebraMap A (Localization.Away (a.val : A)))))
    rw [CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
    infer_instance
  · apply CommRingCat.hom_ext; ext x
    exact sApp_tN S B a x

theorem LocAt_of : LateralTheory.E.SHExistsPf.LocAt := by
  intro A r _
  exact locIE r.primeCompl (Localization.AtPrime r)

end LateralTheory.E.LocAtPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LocDiagPf
noncomputable section
open CategoryTheory Limits Opposite

namespace LateralTheory.E.LocDiagPf


open Classical in
def g {S : Type} [CommRing S] (p : PrimeSpectrum S) (s : Finset p.asIdeal.primeCompl) : S :=
  ∏ x ∈ s, (x : S)

variable {S : Type} [CommRing S] (p : PrimeSpectrum S)

theorem g_mem (s : Finset p.asIdeal.primeCompl) : g p s ∈ p.asIdeal.primeCompl := by
  classical
  unfold g
  convert Submonoid.prod_mem _ (fun (x : p.asIdeal.primeCompl) _ => x.2)

theorem g_dvd {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) : g p s ∣ g p t := by
  classical
  unfold g
  convert Finset.prod_dvd_prod_of_subset s t (fun x : p.asIdeal.primeCompl => (x : S)) h

theorem g_single (y : p.asIdeal.primeCompl) : g p {y} = (y : S) := by
  classical
  unfold g
  convert Finset.prod_singleton (fun x : p.asIdeal.primeCompl => (x : S)) y

theorem unitAway {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) :
    IsUnit (algebraMap S (Localization.Away (g p t)) (g p s)) :=
  isUnit_of_dvd_unit (map_dvd _ (g_dvd p h)) (IsLocalization.Away.algebraMap_isUnit _)

def tr {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) :
    Localization.Away (g p s) →+* Localization.Away (g p t) :=
  IsLocalization.Away.lift (g p s) (unitAway p h)

theorem tr_comp {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) :
    (tr p h).comp (algebraMap S _) = algebraMap S _ :=
  IsLocalization.Away.lift_comp _ _

theorem tr_apply {s t : Finset p.asIdeal.primeCompl} (h : s ⊆ t) (x : S) :
    tr p h (algebraMap S _ x) = algebraMap S _ x :=
  IsLocalization.Away.lift_eq _ _ _

theorem away_ext {s : Finset p.asIdeal.primeCompl} {P : Type} [CommRing P]
    {u v : Localization.Away (g p s) →+* P}
    (h : u.comp (algebraMap S _) = v.comp (algebraMap S _)) : u = v :=
  IsLocalization.ringHom_ext (Submonoid.powers (g p s)) h

def Dg : Finset p.asIdeal.primeCompl ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (Localization.Away (g p s))
  map {s t} h := CommRingCat.ofHom (tr p (leOfHom h))
  map_id s := by
    ext1
    apply away_ext
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, tr_comp]
    rfl
  map_comp {s t u} a b := by
    ext1
    apply away_ext
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp]
    rw [RingHom.comp_assoc, tr_comp, tr_comp, tr_comp]

theorem unitLoc (s : Finset p.asIdeal.primeCompl) :
    IsUnit (algebraMap S (Localization.AtPrime p.asIdeal) (g p s)) :=
  IsLocalization.map_units _ (⟨g p s, g_mem p s⟩ : p.asIdeal.primeCompl)

def toLoc (s : Finset p.asIdeal.primeCompl) :
    Localization.Away (g p s) →+* Localization.AtPrime p.asIdeal :=
  IsLocalization.Away.lift (g p s) (unitLoc p s)

theorem toLoc_comp (s : Finset p.asIdeal.primeCompl) :
    (toLoc p s).comp (algebraMap S _) = algebraMap S _ :=
  IsLocalization.Away.lift_comp _ _

theorem toLoc_apply (s : Finset p.asIdeal.primeCompl) (x : S) :
    toLoc p s (algebraMap S _ x) = algebraMap S _ x :=
  IsLocalization.Away.lift_eq _ _ _

def Cc : Cocone (Dg p) where
  pt := CommRingCat.of (Localization.AtPrime p.asIdeal)
  ι :=
    { app := fun s => (CommRingCat.ofHom (toLoc p s) : (Dg p).obj s ⟶ CommRingCat.of (Localization.AtPrime p.asIdeal))
      naturality := fun s t h => by
        ext1
        apply away_ext
        simp only [Functor.const_obj_map, CommRingCat.hom_comp, CommRingCat.hom_ofHom, Dg]
        rw [RingHom.comp_assoc, tr_comp, toLoc_comp, RingHom.comp_assoc, toLoc_comp]
        rfl }

def phi (c : Cocone (Dg p)) : S →+* c.pt :=
  (c.ι.app ∅).hom.comp (algebraMap S (Localization.Away (g p ∅)))

theorem cocone_comp (c : Cocone (Dg p)) (s : Finset p.asIdeal.primeCompl) :
    (c.ι.app s).hom.comp (algebraMap S (Localization.Away (g p s))) = phi p c := by
  have hw := c.w (homOfLE (Finset.empty_subset s))
  unfold phi
  rw [← hw]
  ext x
  exact congrArg (c.ι.app s).hom (tr_apply p (Finset.empty_subset s) x).symm

theorem phi_unit (c : Cocone (Dg p)) (y : p.asIdeal.primeCompl) : IsUnit (phi p c y) := by
  rw [← DFunLike.congr_fun (cocone_comp p c {y}) (y : S)]
  have hy : IsUnit (algebraMap S (Localization.Away (g p {y})) y) := by
    rw [show (y : S) = g p {y} from (g_single p y).symm]
    exact IsLocalization.Away.algebraMap_isUnit _
  exact IsUnit.map (c.ι.app {y}).hom hy

def isColim : IsColimit (Cc p) where
  desc c := CommRingCat.ofHom (IsLocalization.lift (M := p.asIdeal.primeCompl)
    (S := Localization.AtPrime p.asIdeal) (phi_unit p c))
  fac c s := by
    ext1
    apply away_ext
    ext x
    change (IsLocalization.lift (M := p.asIdeal.primeCompl) (S := Localization.AtPrime p.asIdeal)
      (phi_unit p c)) (toLoc p s (algebraMap S _ x)) =
      (c.ι.app s).hom (algebraMap S (Localization.Away (g p s)) x)
    rw [toLoc_apply, IsLocalization.lift_eq]
    exact (DFunLike.congr_fun (cocone_comp p c s) x).symm
  uniq c m hm := by
    ext1
    refine IsLocalization.ringHom_ext (S := Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl ?_
    ext x
    have hx := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (hm ∅))
      (algebraMap S (Localization.Away (g p ∅)) x)
    change m.hom (algebraMap S (Localization.AtPrime p.asIdeal) x) =
      (IsLocalization.lift (M := p.asIdeal.primeCompl) (S := Localization.AtPrime p.asIdeal)
      (phi_unit p c)) (algebraMap S _ x)
    rw [IsLocalization.lift_eq]
    refine Eq.trans ?_ hx
    change _ = m.hom (toLoc p ∅ (algebraMap S _ x))
    rw [toLoc_apply]

theorem LocDiag_of : LateralTheory.E.ZarLocalPf.LocDiag := by
  intro S _ p
  refine ⟨Finset p.asIdeal.primeCompl, inferInstance, inferInstance, Dg p, Cc p,
    ⟨isColim p⟩, id, ∅, algebraMap S (Localization.Away (g p ∅)), ?_⟩
  intro k m
  refine ⟨g p k, g_mem p k, RingHom.id _, ?_⟩
  ext x
  exact tr_apply p (leOfHom m) x

end LateralTheory.E.LocDiagPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.AicschOfImm
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.CovPf

theorem aic_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (h : AIC A) : AIC B := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map (e.symm : B →+* A)) (hp.map _) (by
    rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  rw [Polynomial.eval_map] at ha
  have h2 := congrArg (e : A →+* B) ha
  rw [Polynomial.hom_eval₂, map_zero] at h2
  have h3 : ((e : A →+* B).comp (e.symm : B →+* A)) = RingHom.id B := by ext x; simp
  rw [h3] at h2
  exact h2

theorem aicsch_of_imm {W Z : Scheme.{0}} (i : W ⟶ Z) [IsOpenImmersion i] [Nonempty W] (hZ : AICSch Z) :
    AICSch W := by
  have : IsIntegral Z := hZ.1
  refine ⟨isIntegral_of_isOpenImmersion i, fun V hV hne => ?_⟩
  have h1 := hZ.2 (i ''ᵁ V) (hV.image_of_isOpenImmersion i) (by
    obtain ⟨x, hx⟩ := hne; exact ⟨i.base x, x, hx, rfl⟩)
  exact aic_equiv (i.appIso V).commRingCatIsoToRingEquiv h1

theorem unit_of_hom {W Z : Scheme.{0}} (i : W ⟶ Z) (q : ℕ) (hq : IsUnit (q : Γ(Z, ⊤))) :
    IsUnit (q : Γ(W, ⊤)) := by
  have := hq.map (i.appTop).hom
  simpa using this

def R (P : Scheme.{0} → Prop) {Z : Scheme.{0}} (s : Set Z) : Prop :=
  ∀ (W : Scheme.{0}) (i : W ⟶ Z) [IsOpenImmersion i], Set.range i = s → Nonempty W → P W

def StepP (q : ℕ) (P : Scheme.{0} → Prop) : Prop :=
  ∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g],
    Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
    P U → P V → (Nonempty ↥(pullback f g : Scheme.{0}) → P (pullback f g)) → P X

theorem R_empty (P : Scheme.{0} → Prop) {Z : Scheme.{0}} : R P (∅ : Set Z) := by
  intro W i _ hr hW
  obtain ⟨w⟩ := hW
  have : i.base w ∈ Set.range i := ⟨w, rfl⟩
  rw [hr] at this; exact this.elim

theorem R_aff (q : ℕ) (P : Scheme.{0} → Prop) (haff : ∀ Z : Scheme.{0}, IsAffine Z → AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z)
    {Z : Scheme.{0}} (hZ : AICSch Z) (hq : IsUnit (q : Γ(Z, ⊤))) (A : Z.Opens) (hA : IsAffineOpen A) :
    R P (A : Set Z) := by
  intro W i _ hr hW
  have e : Set.range i = Set.range A.ι := by rw [hr]; simp
  have hWa : IsAffine W := (IsAffine.iff_of_isIso (IsOpenImmersion.isoOfRangeEq i A.ι e).hom).mpr hA
  exact haff W hWa (aicsch_of_imm i hZ) (unit_of_hom i q hq)

theorem R_step (q : ℕ) (P : Scheme.{0} → Prop) (hstep : StepP q P) {Z : Scheme.{0}} (hZ : AICSch Z)
    (hq : IsUnit (q : Γ(Z, ⊤))) {s t : Set Z} (hs : IsOpen s) (ht : IsOpen t)
    (Rs : R P s) (Rt : R P t) (Rst : R P (s ∩ t)) : R P (s ∪ t) := by
  intro W i _ hr hW
  rcases s.eq_empty_or_nonempty with hs0 | ⟨x, hx⟩
  · subst hs0; exact Rt W i (by simpa using hr) hW
  rcases t.eq_empty_or_nonempty with ht0 | ⟨y, hy⟩
  · subst ht0; exact Rs W i (by simpa using hr) hW
  have subs : s ⊆ Set.range i := hr ▸ Set.subset_union_left
  have subt : t ⊆ Set.range i := hr ▸ Set.subset_union_right
  let U' : W.Opens := i ⁻¹ᵁ ⟨s, hs⟩
  let V' : W.Opens := i ⁻¹ᵁ ⟨t, ht⟩
  have rU : Set.range (U'.ι ≫ i) = s := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset subs
  have rV : Set.range (V'.ι ≫ i) = t := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset subt
  obtain ⟨w, hw⟩ := subs hx
  obtain ⟨v, hv⟩ := subt hy
  have neU : Nonempty U'.toScheme := ⟨⟨w, show i.base w ∈ s from hw ▸ hx⟩⟩
  have neV : Nonempty V'.toScheme := ⟨⟨v, show i.base v ∈ t from hv ▸ hy⟩⟩
  have hZW : AICSch W := aicsch_of_imm i hZ
  refine hstep U'.ι V'.ι ?_ hZW (aicsch_of_imm U'.ι hZW) (aicsch_of_imm V'.ι hZW) (unit_of_hom i q hq)
    (Rs _ (U'.ι ≫ i) rU neU) (Rt _ (V'.ι ≫ i) rV neV) (fun hne => Rst _ (pullback.fst U'.ι V'.ι ≫ U'.ι ≫ i) ?_ hne)
  · ext w'
    simp only [Scheme.Opens.range_ι, Set.mem_union, Set.mem_univ, iff_true]
    have : i.base w' ∈ s ∪ t := hr ▸ ⟨w', rfl⟩
    exact this
  · rw [← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset (Set.inter_subset_left.trans subs)

section Topo
variable {Z : Scheme.{0}} (Q : Set Z → Prop) (hE : Q ∅) (hB : ∀ A : Z.Opens, IsAffineOpen A → Q A)
  (hS : ∀ {s t : Set Z}, IsOpen s → IsOpen t → Q s → Q t → Q (s ∩ t) → Q (s ∪ t))
include hE hB hS

theorem stage1 (A : Z.Opens) (hA : IsAffineOpen A) {ι : Type} (t : Finset ι) :
    ∀ f : ι → Γ(Z, A), Q (⋃ i ∈ t, (Z.basicOpen (f i) : Set Z)) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro f; simpa using hE
  | insert a t ha ih =>
    intro f
    rw [Finset.set_biUnion_insert]
    have hI : (Z.basicOpen (f a) : Set Z) ∩ ⋃ i ∈ t, (Z.basicOpen (f i) : Set Z)
        = ⋃ i ∈ t, (Z.basicOpen (f a * f i) : Set Z) := by
      simp [Scheme.basicOpen_mul, Set.inter_iUnion₂]
    refine hS (Z.basicOpen (f a)).isOpen (isOpen_biUnion fun i _ => (Z.basicOpen (f i)).isOpen)
      (hB _ (hA.basicOpen _)) (ih f) ?_
    rw [hI]; exact ih _

theorem stage1' (A : Z.Opens) (hA : IsAffineOpen A) (S : Set Z) (hSo : IsOpen S) (hSc : IsCompact S)
    (hSA : S ⊆ A) : Q S := by
  have hch : ∀ x : S, ∃ f : Γ(Z, A), Z.basicOpen f ≤ ⟨S, hSo⟩ ∧ (x : Z) ∈ Z.basicOpen f :=
    fun x => hA.exists_basicOpen_le (V := ⟨S, hSo⟩) ⟨x.1, x.2⟩ (hSA x.2)
  choose f hf1 hf2 using hch
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover (fun x : S => (Z.basicOpen (f x) : Set Z))
    (fun x => (Z.basicOpen _).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hf2 _⟩)
  have : S = ⋃ i ∈ t, (Z.basicOpen (f i) : Set Z) :=
    subset_antisymm ht (Set.iUnion₂_subset fun i _ => hf1 i)
  rw [this]; exact stage1 Q hE hB hS A hA t f

theorem stage2 [QuasiSeparatedSpace Z] (t : Finset Z.affineOpens) :
    Q (⋃ i ∈ t, ((i : Z.Opens) : Set Z)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hE
  | insert a t ha ih =>
    rw [Finset.set_biUnion_insert]
    have hTo : IsOpen (⋃ i ∈ t, ((i : Z.Opens) : Set Z)) := isOpen_biUnion fun i _ => (i : Z.Opens).isOpen
    have hTc : IsCompact (⋃ i ∈ t, ((i : Z.Opens) : Set Z)) := t.isCompact_biUnion fun i _ => i.2.isCompact
    refine hS (a : Z.Opens).isOpen hTo (hB _ a.2) ih ?_
    exact stage1' Q hE hB hS a a.2 _ ((a : Z.Opens).isOpen.inter hTo)
      (QuasiSeparatedSpace.inter_isCompact _ _ (a : Z.Opens).isOpen a.2.isCompact hTo hTc) Set.inter_subset_left

theorem stage3 [CompactSpace Z] [QuasiSeparatedSpace Z] : Q Set.univ := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : Z.affineOpens => ((U : Z.Opens) : Set Z))
    (fun U => (U : Z.Opens).isOpen) (fun x _ => by
      have : x ∈ (⨆ i : Z.affineOpens, (i : Z.Opens)) := by rw [iSup_affineOpens_eq_top]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using this)
  have : (Set.univ : Set Z) = ⋃ i ∈ t, ((i : Z.Opens) : Set Z) := subset_antisymm ht (Set.subset_univ _)
  rw [this]; exact stage2 Q hE hB hS t

end Topo

theorem Cov_of : LateralTheory.E.AICAcycPf.Cov := by
  intro q P hiso haff hstep Z _ _ hZ hq
  have h := stage3 (R P (Z := Z)) (R_empty P) (fun A hA => R_aff q P haff hZ hq A hA)
    (fun hs ht Rs Rt Rst => R_step q P hstep hZ hq hs ht Rs Rt Rst)
  have : IsIntegral Z := hZ.1
  exact h Z (𝟙 Z) (by simp) inferInstance

end LateralTheory.E.CovPf
end
end
