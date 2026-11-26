module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualLatticeSetting
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResidualLatticeSetting

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def maxLam (i : X.Tw) (M : ℕ) (ι : Type) : Ideal (abelian₂ X i M ι) :=
  (IsLocalRing.maximalIdeal (X.O0 i)).map (algebraMap (X.O0 i) (abelian₂ X i M ι)) ⊔
    Ideal.span (Set.range fun q : ι => toLam X i M ι (MvPolynomial.X q))

theorem maxLam_ne_top (i : X.Tw) (M : ℕ) (ι : Type) : maxLam X i M ι ≠ ⊤ := by
  classical
  let ε : abelian₂ X i M ι →ₐ[X.O0 i] X.O0 i := MonoidAlgebra.lift (X.O0 i) (X.O0 i) (Del X i M ι) 1
  let φ : abelian₂ X i M ι →+* IsLocalRing.ResidueField (X.O0 i) :=
    (IsLocalRing.residue (X.O0 i)).comp ε.toRingHom
  have hle : maxLam X i M ι ≤ RingHom.ker φ := by
    unfold maxLam
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simpa [φ, ε, IsLocalRing.residue_eq_zero_iff] using hc
    · rw [Ideal.span_le]
      rintro _ ⟨q, rfl⟩
      simp [φ, ε, toLam]
  exact ne_top_of_le_ne_top (RingHom.ker_ne_top φ) hle

variable {X} (bkP : BKPh X)


end GlobalTheory.IndefiniteRowSideFullHecke.ResidualLatticeSetting

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerIffSelmerMatrixAtPrimes
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.IndefiniteRowSideFullHecke.ResidualLatticeSetting

namespace GlobalTheory.SelMatrixCompare

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem l_mem_maximalIdeal (i : X.Tw) : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
  intro h
  have h2 := h.map (algebraMap (X.O0 i) (X.O i))
  rw [map_natCast] at h2
  exact X.O_l i h2

theorem maxLam_le (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (m : Ideal (abelian₂ X i M ι)) [hm : m.IsMaximal] :
    maxLam X i M ι ≤ m := by
  classical
  have hp : (X.l i).Prime := (X.lPrime i).out
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h0 : (IsLocalRing.maximalIdeal (X.O0 i)).map (algebraMap (X.O0 i) (abelian₂ X i M ι)) ≤ m := by
    rw [Ideal.map_le_iff_le_comap]
    have : (m.comap (algebraMap (X.O0 i) (abelian₂ X i M ι))).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := X.O0 i) m
    exact (IsLocalRing.eq_maximalIdeal this).ge
  refine sup_le h0 ?_
  rw [Ideal.span_le]
  rintro _ ⟨q, rfl⟩
  have hl : ((X.l i : ℕ) : abelian₂ X i M ι) ∈ m := by
    have h := Ideal.mem_map_of_mem (algebraMap (X.O0 i) (abelian₂ X i M ι)) (l_mem_maximalIdeal X i)
    rw [map_natCast] at h
    exact h0 h
  have : Nontrivial (abelian₂ X i M ι ⧸ m) := Ideal.Quotient.nontrivial_iff.2 hm.ne_top
  have : CharP (abelian₂ X i M ι ⧸ m) (X.l i) := by
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    rw [← map_natCast (Ideal.Quotient.mk m)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hl
  have hg : (Multiplicative.ofAdd (Pi.single q 1) : Del X i M ι) ^ (X.l i ^ M) = 1 := by
    apply Multiplicative.toAdd.injective
    funext j
    simp only [toAdd_pow, toAdd_ofAdd, Pi.smul_apply, toAdd_one, Pi.zero_apply]
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  refine hm.isPrime.mem_of_pow_mem (X.l i ^ M) ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
  simp only [toLam, MvPolynomial.aeval_X, map_sub, map_one]
  rw [sub_pow_char_pow, ← map_pow, ← map_pow]
  rw [one_pow, sub_eq_zero]
  convert map_one (Ideal.Quotient.mk m) using 2
  convert map_one (MonoidAlgebra.of (X.O0 i) (Del X i M ι)) using 2

theorem exists_const (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (x : abelian₂ X i M ι) :
    ∃ c : X.O0 i, x - algebraMap (X.O0 i) (abelian₂ X i M ι) c ∈ maxLam X i M ι := by
  obtain ⟨F, rfl⟩ := toLam_surjective X i M ι x
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨a, by rw [MvPolynomial.algHom_C, sub_self]; exact zero_mem _⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a + b, ?_⟩
    have := add_mem ha hb
    rw [map_add (f := _), map_add (f := _)]
    convert this using 1
    ring
  | mul_X p q _ =>
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩))

theorem mem_maxLam_iff (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (x : abelian₂ X i M ι) :
    x ∈ maxLam X i M ι ↔ ¬ IsUnit x := by
  refine ⟨fun hx hu => maxLam_ne_top X i M ι (Ideal.eq_top_of_isUnit_mem _ hx hu), fun hx => ?_⟩
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
  obtain ⟨c, hc⟩ := exists_const X i M ι x
  have h1 : algebraMap (X.O0 i) (abelian₂ X i M ι) c ∈ m := by
    have := sub_mem hxm (maxLam_le X i M ι m hc)
    rwa [sub_sub_cancel] at this
  have h2 : c ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
    hm.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (hu.map _))
  have h3 : algebraMap (X.O0 i) (abelian₂ X i M ι) c ∈ maxLam X i M ι :=
    Ideal.mem_sup_left (Ideal.mem_map_of_mem _ h2)
  have := add_mem hc h3
  rwa [sub_add_cancel] at this

theorem maxLam_isMaximal (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] : (maxLam X i M ι).IsMaximal := by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (maxLam_ne_top X i M ι)
  have : maxLam X i M ι = m := le_antisymm hle fun x hx =>
    (mem_maxLam_iff X i M ι x).2 fun hu => hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
  rwa [this]

variable {X} (bkP : BKPh X)

end GlobalTheory.SelMatrixCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteOfFinite
open IsLocalRing TensorProduct

namespace GlobalTheory.AdicCompleteFinite

theorem isPrecomplete_of_finite {R M : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨x, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r m =>
    obtain ⟨a, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨a • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I R) a (AdicCompletion.of I M m)).symm
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

theorem isPrecomplete_of_pow_le {S : Type} [CommRing S] {I J : Ideal S} (hIJ : I ≤ J) {k : ℕ}
    (hk : J ^ k ≤ I) [h : IsPrecomplete I S] : IsPrecomplete J S := by
  have hk' : J ^ (k + 1) ≤ I := (Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk
  refine ⟨fun f hf => ?_⟩
  have hg : ∀ {m n : ℕ}, m ≤ n →
      f ((k + 1) * m) ≡ f ((k + 1) * n) [SMOD (I ^ m • ⊤ : Submodule S S)] := by
    intro m n hmn
    refine (hf (Nat.mul_le_mul_left (k + 1) hmn)).mono ?_
    refine Submodule.smul_mono_left ?_
    rw [pow_mul]
    exact Ideal.pow_right_mono hk' m
  obtain ⟨L, hL⟩ := IsPrecomplete.prec h (f := fun n => f ((k + 1) * n)) hg
  refine ⟨L, fun n => ?_⟩
  refine (hf (Nat.le_mul_of_pos_left n (Nat.succ_pos k))).trans ?_
  exact (hL n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n))

theorem isAdicComplete_of_finite (R S : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [Module.Finite R S] : IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  haveI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hcomap : (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal S))
  have hle : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S :=
    Ideal.map_le_iff_le_comap.mpr hcomap.ge
  have hrad : maximalIdeal S ≤ ((maximalIdeal R).map (algebraMap R S)).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hP, hprime⟩
    have h1 : maximalIdeal R ≤ P.comap (algebraMap R S) := Ideal.map_le_iff_le_comap.mp hP
    have h2 : P.comap (algebraMap R S) = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ hprime.ne_top) h1).symm
    have h3 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R S)
        (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) P
        (h2 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h3).ge
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI : IsPrecomplete (maximalIdeal R) S := isPrecomplete_of_finite _
  haveI : IsPrecomplete ((maximalIdeal R).map (algebraMap R S)) S :=
    IsPrecomplete.map_algebraMap_iff.mpr this
  haveI : IsPrecomplete (maximalIdeal S) S := isPrecomplete_of_pow_le hle hk
  exact {}

end GlobalTheory.AdicCompleteFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerTheoremOfLocalComponents
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.SelAssemble

section Local
open IsLocalRing

theorem exists_pow_le_map (R S : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : ∃ e, maximalIdeal S ^ e ≤ (maximalIdeal R).map (algebraMap R S) := by
  have := IsNoetherianRing.of_finite R S
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro p ⟨hp, hp'⟩
  have h1 : (p.comap (algebraMap R S)).IsMaximal := by
    have h2 : maximalIdeal R = p.comap (algebraMap R S) :=
      (maximalIdeal.isMaximal R).eq_of_le (Ideal.IsPrime.ne_top inferInstance) (Ideal.map_le_iff_le_comap.1 hp)
    rw [← h2]; infer_instance
  exact (eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) p h1)).ge

theorem map_le_maximalIdeal (R S : Type) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S :=
  Ideal.map_le_iff_le_comap.2 (eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) (maximalIdeal S))).ge

theorem complete_of_finite (R S : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : IsAdicComplete (maximalIdeal S) S := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6 h_7 h_8 h_9; revert R S h_2 h_3 h_4 h_5 h_6 h_7 h_8 h_9; exact @_root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite)
  | exact @_root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite
  | exact _root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite
  | (apply _root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite ..)

theorem tors_of_nsmul (l : ℕ) [Fact l.Prime] (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra ℤ_[l] Λ]
    [Module.Finite ℤ_[l] Λ] (B : Type) [AddCommGroup B] [Module Λ B] (hB : ∀ b : B, ∃ n : ℕ, (l ^ n) • b = 0) :
    Tors Λ B := by
  obtain ⟨e, he⟩ := exists_pow_le_map ℤ_[l] Λ
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast] at he
  intro b
  obtain ⟨n, hn⟩ := hB b
  refine ⟨e * n, fun x hx => ?_⟩
  rw [pow_mul] at hx
  have h := Ideal.pow_right_mono he n hx
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  obtain ⟨y, rfl⟩ := h
  rw [mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hn, smul_zero]

end Local

section Maps

variable {Γ O Λ : Type} [Group Γ] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
  [TopologicalSpace Γ]
  {B B' B'' : Type} [AddCommGroup B] [Module Λ B] [AddCommGroup B'] [Module Λ B'] [AddCommGroup B''] [Module Λ B'']
  [TopologicalSpace B] [DiscreteTopology B] [TopologicalSpace B'] [DiscreteTopology B']
  [TopologicalSpace B''] [DiscreteTopology B'']

theorem h1Map_mk (f : B →ₗ[Λ] B') (z : Z1 (repOn ρ κ B)) (z' : Z1 (repOn ρ κ B'))
    (h : ∀ g c, z'.1 g c = f (z.1 g c)) :
    h1Map ρ κ f (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  change Submodule.Quotient.mk _ = _
  congr 1
  exact Subtype.ext (funext fun g => funext fun c => (h g c).symm)

theorem h1Map_comp (f : B →ₗ[Λ] B') (g : B' →ₗ[Λ] B'') (h : B →ₗ[Λ] B'') (e : ∀ b, h b = g (f b))
    (x : H1 (repOn ρ κ B)) : h1Map ρ κ g (h1Map ρ κ f x) = h1Map ρ κ h x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext (funext fun g => funext fun c => (e _).symm)

theorem h1Map_id (f : B →ₗ[Λ] B) (e : ∀ b, f b = b) (x : H1 (repOn ρ κ B)) : h1Map ρ κ f x = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact h1Map_mk ρ κ f z z fun g c => (e _).symm

theorem h1Map_add (f g h : B →ₗ[Λ] B') (e : ∀ b, h b = f b + g b) (x : H1 (repOn ρ κ B)) :
    h1Map ρ κ h x = h1Map ρ κ f x + h1Map ρ κ g x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_add]
  congr 1
  exact Subtype.ext (funext fun g => funext fun c => e _)

theorem h1Map_smul (a : Λ) (f h : B →ₗ[Λ] B') (e : ∀ b, h b = a • f b) (x : H1 (repOn ρ κ B)) :
    h1Map ρ κ h x = a • h1Map ρ κ f x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk _ = a • Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (funext fun g => funext fun c => e _)

end Maps

def Dsc (B : Type) : Type := B

instance (B : Type) [AddCommGroup B] : AddCommGroup (Dsc B) := inferInstanceAs (AddCommGroup B)
instance (Λ B : Type) [CommRing Λ] [AddCommGroup B] [Module Λ B] : Module Λ (Dsc B) := inferInstanceAs (Module Λ B)
instance (B : Type) : TopologicalSpace (Dsc B) := ⊥
instance (B : Type) : DiscreteTopology (Dsc B) := ⟨rfl⟩

def toDsc (Λ B : Type) [CommRing Λ] [AddCommGroup B] [Module Λ B] : B ≃ₗ[Λ] Dsc B := LinearEquiv.refl Λ B

def dscMap {Λ B B' : Type} [CommRing Λ] [AddCommGroup B] [Module Λ B] [AddCommGroup B'] [Module Λ B']
    (f : B →ₗ[Λ] B') : Dsc B →ₗ[Λ] Dsc B' := f

section Functor
open CategoryTheory

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {bkP : BKPh X}
  {i : X.Tw} {s : X.Sig i} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] {κ : GE N →* Λˣ}
  {Q : Finset (PlE D.host)} (hM : SelMaps bkP i s κ Q)

def selMap {B B' : Type} [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
    [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B'] (f : B →ₗ[Λ] B') :
    ↥(selOn bkP i (Tgl i s) κ B Q) →ₗ[Λ] ↥(selOn bkP i (Tgl i s) κ B' Q) :=
  (h1Map (Tgl i s) κ f).restrict fun x hx => hM B B' f ⟨x, hx, rfl⟩

def selF : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ where
  obj B := ModuleCat.of Λ ↥(selOn bkP i (Tgl i s) κ (Dsc B) Q)
  map f := ModuleCat.ofHom (selMap hM (dscMap f.hom))
  map_id B := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact h1Map_id _ _ _ (fun _ => rfl) _
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact (h1Map_comp (Tgl i s) κ (dscMap f.hom) (dscMap g.hom) (dscMap (f ≫ g).hom) (fun _ => rfl) x.1).symm

instance : (selF hM).Additive where
  map_add {_ _ f g} := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact h1Map_add (Tgl i s) κ (dscMap f.hom) (dscMap g.hom) (dscMap (f + g).hom) (fun _ => rfl) x.1

instance : (selF hM).Linear Λ where
  map_smul f a := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    exact h1Map_smul (Tgl i s) κ a (dscMap f.hom) (dscMap (a • f).hom) (fun _ => rfl) x.1

def selDsc (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B] :
    ↥(selOn bkP i (Tgl i s) κ (Dsc B) Q) ≃ₗ[Λ] ↥(selOn bkP i (Tgl i s) κ B Q) :=
  LinearEquiv.ofLinear (selMap hM (toDsc Λ B).symm.toLinearMap) (selMap hM (toDsc Λ B).toLinearMap)
    (LinearMap.ext fun x => Subtype.ext ((h1Map_comp (Tgl i s) κ (toDsc Λ B).toLinearMap (toDsc Λ B).symm.toLinearMap
      LinearMap.id (fun _ => rfl) x.1).trans (h1Map_id _ _ _ (fun _ => rfl) _)))
    (LinearMap.ext fun x => Subtype.ext ((h1Map_comp (Tgl i s) κ (toDsc Λ B).symm.toLinearMap (toDsc Λ B).toLinearMap
      LinearMap.id (fun _ => rfl) x.1).trans (h1Map_id _ _ _ (fun _ => rfl) _)))

theorem selF_left (h : SelLeft bkP i s κ Q) (B' B B'' : ModuleCat.{0} Λ) (hB : Tors Λ B) (hB'' : Tors Λ B'')
    (f : B' ⟶ B) (g : B ⟶ B'') (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) :
    Function.Injective ((selF hM).map f).hom ∧ Function.Exact ((selF hM).map f).hom ((selF hM).map g).hom := by
  obtain ⟨h1, h2⟩ := h (Dsc B') (Dsc B) (Dsc B'') (show Tors Λ (Dsc B) from hB) (show Tors Λ (Dsc B'') from hB'')
    (dscMap f.hom) (dscMap g.hom) hf hfg
  refine ⟨fun x y hxy => Subtype.ext (h1 (congrArg Subtype.val hxy)), fun y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨x, hx, e⟩ := h2 y.1 y.2 (congrArg Subtype.val hy)
    exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  · rintro ⟨x, rfl⟩
    refine Subtype.ext ?_
    have e1 := h1Map_comp (Tgl i s) κ (dscMap f.hom) (dscMap g.hom) 0 (fun b => (hfg.apply_apply_eq_zero b).symm) x.1
    have e2 := h1Map_smul (Tgl i s) κ (0 : Λ) (0 : Dsc B' →ₗ[Λ] Dsc B'') 0 (fun b => by simp) x.1
    rw [zero_smul] at e2
    exact e1.trans e2

theorem selF_colim (h : SelColim bkP i s κ Q) (B : ModuleCat.{0} Λ) (hB : Tors Λ B) (y : (selF hM).obj B) :
    ∃ B' : Submodule Λ B, B'.FG ∧ y ∈ LinearMap.range ((selF hM).map (ModuleCat.ofHom B'.subtype)).hom := by
  obtain ⟨B', hfg, x, hx, e⟩ := h (Dsc B) (show Tors Λ (Dsc B) from hB) y.1 y.2
  let C : Submodule Λ B := B'
  let u : ↥B' →ₗ[Λ] Dsc ↥C := { toFun := fun b => b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have e2 : h1Map (Tgl i s) κ (dscMap C.subtype) (h1Map (Tgl i s) κ u x) = y.1 :=
    (h1Map_comp (Tgl i s) κ u (dscMap C.subtype) B'.subtype (fun _ => rfl) x).trans e
  exact ⟨C, hfg, selMap hM u ⟨x, hx⟩, Subtype.ext e2⟩

theorem selF_obs (h : SelObs bkP i s κ Q) (K B B'' : ModuleCat.{0} Λ) (hK : IsSimpleModule Λ K) (hB : Tors Λ B)
    (f : K ⟶ B) (g : B ⟶ B'') (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom)
    (hg : Function.Surjective g.hom) :
    Finite ((selF hM).obj K) ∧ Finite ((selF hM).obj B'' ⧸ LinearMap.range ((selF hM).map g).hom) ∧
      Nat.card ((selF hM).obj B'' ⧸ LinearMap.range ((selF hM).map g).hom) ≤ Nat.card ((selF hM).obj K) := by
  have h1 := h (Dsc K) (Dsc B) (Dsc B'') (show IsSimpleModule Λ (Dsc K) from hK) (show Tors Λ (Dsc B) from hB)
    (dscMap f.hom) (dscMap g.hom) hf hfg hg
  have e : ((selOn bkP i (Tgl i s) κ (Dsc B) Q).map (h1Map (Tgl i s) κ (dscMap g.hom))).comap
      (selOn bkP i (Tgl i s) κ (Dsc B'') Q).subtype = LinearMap.range (selMap hM (dscMap g.hom)) := by
    ext y
    constructor
    · rintro ⟨x, hx, e⟩
      exact ⟨⟨x, hx⟩, Subtype.ext e⟩
    · rintro ⟨x, e⟩
      exact ⟨x.1, x.2, congrArg Subtype.val e⟩
  rw [e] at h1
  exact h1


include hM in
theorem exists_matrix (hK : KernelRep) [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ]
    [Finite (IsLocalRing.ResidueField Λ)] (h1 : SelLeft bkP i s κ Q) (h2 : SelColim bkP i s κ Q)
    (h3 : SelObs bkP i s κ Q) :
    ∃ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) Λ), (∀ b c, ¬ IsUnit (Φ b c)) ∧
    ∃ e : ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
      (↥(LinearMap.ker (matAct (M := B) Φ)) ≃ₗ[Λ] ↥(selOn bkP i (Tgl i s) κ B Q)),
    ∀ (B B' : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
      [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']
      (hB : Tors Λ B) (hB' : Tors Λ B')
      (f : B →ₗ[Λ] B') (x : ↥(LinearMap.ker (matAct (M := B) Φ))) (x' : ↥(LinearMap.ker (matAct (M := B') Φ)))
      (z : Z1 (repOn (Tgl i s) κ B)) (z' : Z1 (repOn (Tgl i s) κ B')),
      (∀ c, x'.1 c = f (x.1 c)) → (∀ g c, z'.1 g c = f (z.1 g c)) →
      (e B hB x).1 = Submodule.Quotient.mk z → (e B' hB' x').1 = Submodule.Quotient.mk z' := by
  obtain ⟨a, Φ, hΦ, e, he⟩ := hK Λ (selF hM) (selF_left hM h1) (selF_colim hM h2) (selF_obs hM h3)
  refine ⟨a, Φ, hΦ, fun B _ _ _ _ hB => (e (ModuleCat.of Λ B) hB).trans (selDsc hM B), ?_⟩
  intro B B' _ _ _ _ _ _ _ _ hB hB' f x x' z z' hx hz hxz
  have e1 := he (ModuleCat.of Λ B) (ModuleCat.of Λ B') hB hB' (ModuleCat.ofHom f) x x' hx
  have e2 : h1Map (Tgl i s) κ (toDsc Λ B).symm.toLinearMap (e (ModuleCat.of Λ B) hB x).1 =
    Submodule.Quotient.mk z := hxz
  have e3 : (e (ModuleCat.of Λ B') hB' x').1 = h1Map (Tgl i s) κ (dscMap f) (e (ModuleCat.of Λ B) hB x).1 :=
    congrArg Subtype.val e1
  change h1Map (Tgl i s) κ (toDsc Λ B').symm.toLinearMap (e (ModuleCat.of Λ B') hB' x').1 = _
  rw [e3, ← h1Map_mk (Tgl i s) κ f z z' hz, ← e2,
    h1Map_comp (Tgl i s) κ (toDsc Λ B).symm.toLinearMap f (f ∘ₗ (toDsc Λ B).symm.toLinearMap) (fun _ => rfl)]
  exact h1Map_comp (Tgl i s) κ _ _ _ (fun _ => rfl) _

end Functor

section GroupRing

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)
  (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι]

theorem finite_del : Finite (Del X i M ι) := by
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  infer_instance

theorem isLocalRing_lam : IsLocalRing (abelian₂ X i M ι) := by
  refine IsLocalRing.of_unique_max_ideal ⟨_, SelMatrixCompare.maxLam_isMaximal X i M ι, fun m hm => ?_⟩
  exact ((SelMatrixCompare.maxLam_isMaximal X i M ι).eq_of_le hm.ne_top (SelMatrixCompare.maxLam_le X i M ι m)).symm

theorem finite_lam : Module.Finite (X.O0 i) (abelian₂ X i M ι) := by
  have := finite_del X i M ι
  infer_instance

theorem finite_lam_padic : Module.Finite ℤ_[X.l i] (abelian₂ X i M ι) := by
  have := finite_lam X i M ι
  exact Module.Finite.trans (X.O0 i) _

variable {X M ι} (bkP : BKPh X)

theorem setup_of_auxiliary_characters [IsLocalRing (abelian₂ X i M ι)] (s : X.Sig i) (hG : GalHyp bkP i s) (P : ι → PlE D.host)
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (hA : SlopeTestRemainingChoices X i M ∅ P d)
    (hQ : IsQ P Q) : Setup bkP i s (delInv i M d) Q := by
  have hfin := finite_lam X i M ι
  have h1 : ∀ g, (∀ q, d q g = 1) → delInv i M d g = 1 := fun g hg => by
    have : delAll X i M d g = 1 := by
      apply Multiplicative.toAdd.injective
      funext q
      change Multiplicative.toAdd (d q g) = 0
      rw [hg q]; rfl
    simp [delInv, this]
  refine ⟨hG, ⟨fun x hx => ?_⟩, hfin, ?_, fun g => ⟨M, ?_⟩, fun v hv A hA' σ hσ => h1 σ fun q => ?_, fun v hv hl => ?_,
    fun v hv A hA' σ hσ => h1 σ fun q => ?_⟩
  · by_contra hn
    exact map_le_maximalIdeal (X.O0 i) (abelian₂ X i M ι) (Ideal.mem_map_of_mem _ hn) hx
  · refine Subgroup.isOpen_mono (H₁ := ⨅ q, (d q).ker) (fun g hg => h1 g fun q => Subgroup.mem_iInf.1 hg q) ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun q => (hA.2.2 q).1
  · have : delAll X i M d g ^ (X.l i ^ M) = 1 := by
      apply Multiplicative.toAdd.injective
      funext j
      simp only [toAdd_pow, Pi.smul_apply, toAdd_one, Pi.zero_apply]
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    simp only [delInv, MonoidHom.inv_apply, MonoidHom.comp_apply, inv_pow, ← map_pow, this, map_one, inv_one]
  · exact (hA.2.2 q).2.2.1 v hv A hA' σ hσ
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    exact (hA.1 q v hq).2.2.2.1 (X.twistExcludedPlaces_contains_residueChar i hl)
  · exact (hA.2.2 q).2.2.2.1 v (fun hq => hv ((hQ v).2 ⟨q, hq⟩)) A hA' σ hσ

end GroupRing

theorem thmS_of_selmer_functor : KernelRep → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → SelMaps bkP i s κ Q ∧ SelLeft bkP i s κ Q ∧ SelColim bkP i s κ Q ∧ SelObs bkP i s κ Q) → ThmS bkP := by
  intro hK D N X bkP h i s hG M ι _ P d Q _ hA hQ
  have := isLocalRing_lam X i M ι
  have := finite_lam X i M ι
  have := finite_lam_padic X i M ι
  have hS := setup_of_auxiliary_characters i bkP s hG P d Q hA hQ
  obtain ⟨hM, h1, h2, h3⟩ := h i s _ _ Q hS
  have := IsNoetherianRing.of_finite (X.O0 i) (abelian₂ X i M ι)
  have := complete_of_finite ℤ_[X.l i] (abelian₂ X i M ι)
  have : Finite (IsLocalRing.ResidueField (abelian₂ X i M ι)) := by
    have := hS.2.1
    have := X.twistBaseCoefficientRing_residueField_finite i
    exact Module.finite_of_finite (IsLocalRing.ResidueField (X.O0 i))
  obtain ⟨a, Φ, hΦ, e, he⟩ := exists_matrix hM hK h1 h2 h3
  exact ⟨a, Φ, ⟨fun B _ _ _ _ hB => e B (tors_of_nsmul (X.l i) _ B hB),
    fun B B' _ _ _ _ _ _ _ _ hB hB' => he B B' _ _⟩, hΦ⟩

end GlobalTheory.SelAssemble

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerTheoremOfLocalComponentsStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selmer_theorem_of_local_components : KernelRep → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → SelMaps bkP i s κ Q ∧ SelLeft bkP i s κ Q ∧ SelColim bkP i s κ Q ∧ SelObs bkP i s κ Q) → ThmS bkP := by
  first | exact @GlobalTheory.SelAssemble.thmS_of_selmer_functor | exact GlobalTheory.SelAssemble.thmS_of_selmer_functor | (intros; apply GlobalTheory.SelAssemble.thmS_of_selmer_functor <;> assumption)
end
