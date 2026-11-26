module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.HermASingleLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.UJClassMassOfOpen
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnitaryApproxFin

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.LSBase
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence PI.UnitaryGroupMassFormula.UJClassFin
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable {M : ℕ}

theorem crd_add (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {x y : Fin M → E}
    (hx : x ∈ crdOf b L0) (hy : y ∈ crdOf b L0) : x + y ∈ crdOf b L0 := by
  show ∑ i, (x + y) i • b i ∈ L0
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  exact L0.add_mem hx hy

theorem crd_zero (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) : (0 : Fin M → E) ∈ crdOf b L0 := by
  show ∑ i, (0 : Fin M → E) i • b i ∈ L0
  simp

theorem crd_neg (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {x : Fin M → E}
    (hx : x ∈ crdOf b L0) : -x ∈ crdOf b L0 := by
  show ∑ i, (-x) i • b i ∈ L0
  simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
  exact L0.neg_mem hx

theorem crd_sum (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {ι : Type*} (s : Finset ι)
    (f : ι → Fin M → E) (hf : ∀ i ∈ s, f i ∈ crdOf b L0) : ∑ i ∈ s, f i ∈ crdOf b L0 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact crd_zero b L0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact crd_add b L0 (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem crd_smul (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {e : E} (he : IsIntegral ℤ e)
    {x : Fin M → E} (hx : x ∈ crdOf b L0) : e • x ∈ crdOf b L0 := by
  show ∑ i, (e • x) i • b i ∈ L0
  have : ∑ i, (e • x) i • b i = e • ∑ i, x i • b i := by
    simp [Finset.smul_sum, smul_smul]
  rw [this]
  exact int_smul_mem L0 he hx

theorem vinc_smul (c : E) (x : Fin M → E) : vinc (F := F) (c • x) = inclR (F := F) (Af F) c • vinc (F := F) x := by
  funext i
  simp [vinc, map_mul]

theorem vinc_Fsmul (c : F) (x : Fin M → E) : vinc (F := F) (c • x) = c • vinc (F := F) x := by
  funext i
  simp only [vinc, Pi.smul_apply, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_smul]

theorem vinc_add (x y : Fin M → E) : vinc (F := F) (x + y) = vinc x + vinc y := by
  funext i; simp [vinc]

theorem vinc_sub (x y : Fin M → E) : vinc (F := F) (x - y) = vinc x - vinc y := by
  funext i; simp [vinc]

theorem vinc_mem (L : Set (Fin M → E)) {x : Fin M → E} (hx : x ∈ L) : vinc (F := F) x ∈ latHat F E L :=
  AddSubgroup.subset_closure ⟨1, intAf_one, x, hx, rfl⟩

theorem latHat_Oh_smul (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {o : Af F ⊗[F] E}
    (ho : o ∈ Oh F E) {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E (crdOf b L0)) :
    o • y ∈ latHat F E (crdOf b L0) := by
  induction ho using AddSubgroup.closure_induction with
  | mem o ho =>
    obtain ⟨a, ha, e, he, rfl⟩ := ho
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a', ha', x, hx, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a * a', intAf_mul ha ha', e • x, crd_smul b L0 he hx, ?_⟩
      funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add y y' _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
    | neg y _ h1 => rw [smul_neg]; exact neg_mem h1
  | zero => rw [zero_smul]; exact zero_mem _
  | add o o' _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
  | neg o _ h1 => rw [neg_smul]; exact neg_mem h1

theorem latHat_incl_smul (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) {e : E}
    (he : IsIntegral ℤ e) {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E (crdOf b L0)) :
    inclR (F := F) (Af F) e • y ∈ latHat F E (crdOf b L0) :=
  latHat_Oh_smul b L0 (incl_mem_Oh he) hy

end Base

theorem lsOne : LSOne := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hτ hs hnd hL hsig
  set L := crdOf b L0 with hLdef
  obtain ⟨⟨c1, hc1, hup⟩, ⟨c2, hc2, hlow⟩⟩ := crdBounds F E V M b L0 hL
  obtain ⟨u, hu, hu'⟩ := up_nat L ⟨c1, hc1, hup⟩
  obtain ⟨k, hk, hk'⟩ := low_nat L ⟨c2, hc2, hlow⟩
  have hNpos : 0 < u * k := Nat.mul_pos hu hk

  have hNL : ∀ z : Fin M → E, vinc (F := F) z ∈ latHat F E L → (((u * k : ℕ) : F)) • z ∈ L := by
    intro z hz
    have hi : ∀ i, IsIntegral ℤ (u • z i) := by
      intro i
      apply oh_inter (F := F)
      have := up_Oh L hu' hz i
      simpa [vinc, map_nsmul] using this
    have e : (((u * k : ℕ) : F)) • z = ∑ i, Pi.single i ((k : F) • (u • z i)) := by
      funext j
      simp only [Finset.sum_apply, Pi.single_apply, Pi.smul_apply, Nat.cast_mul]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Nat.cast_smul_eq_nsmul]
      rw [mul_comm, mul_smul]
      rw [Nat.cast_smul_eq_nsmul F, Nat.cast_smul_eq_nsmul F]
    rw [e]
    exact crd_sum b L0 _ _ fun i _ => hk' i _ (hi i)

  have hD : ∀ y ∈ latHat F E L, ∃ l ∈ L, ∃ y' ∈ latHat F E L, y = vinc (F := F) l + (u * k) • y' := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      obtain ⟨e, o, ho, hae⟩ := approx (E := E) (u * k) hNpos (a ⊗ₜ[F] (1 : E))
      have he : IsIntegral ℤ e := by
        apply oh_inter (F := F)
        have : inclR (Af F) e = a ⊗ₜ[F] (1 : E) - (u * k) • o := by rw [hae]; abel
        rw [this]
        exact sub_mem (tmul_mem_Oh ha isIntegral_one) (AddSubgroup.nsmul_mem _ ho _)
      refine ⟨e • x, crd_smul b L0 he hx, o • vinc (F := F) x, latHat_Oh_smul b L0 ho (vinc_mem L hx), ?_⟩
      funext i
      have e1 : a ⊗ₜ[F] x i = (a ⊗ₜ[F] (1 : E)) * inclR (Af F) (x i) := by
        simp [inclR, Algebra.TensorProduct.tmul_mul_tmul]
      rw [e1, hae]
      simp only [vinc, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, add_mul, smul_mul_assoc]
    | zero => exact ⟨0, crd_zero b L0, 0, zero_mem _, by funext i; simp [vinc]⟩
    | add y z _ _ h1 h2 =>
      obtain ⟨l, hl, y', hy', e1⟩ := h1
      obtain ⟨l', hl', z', hz', e2⟩ := h2
      refine ⟨l + l', crd_add b L0 hl hl', y' + z', add_mem hy' hz', ?_⟩
      rw [e1, e2, vinc_add, smul_add]; abel
    | neg y _ h1 =>
      obtain ⟨l, hl, y', hy', e1⟩ := h1
      refine ⟨-l, crd_neg b L0 hl, -y', neg_mem hy', ?_⟩
      rw [e1, smul_neg, neg_add]
      congr 1
      funext i; simp [vinc]
  ext x
  simp only [abelian₂, Set.mem_ofPred_eq, inv_one, finMat_one, Matrix.one_mulVec]
  constructor
  · intro hx
    obtain ⟨l, hl, y', hy', e⟩ := hD _ hx
    set z : Fin M → E := (((u * k : ℕ) : F))⁻¹ • (x - l) with hz
    have hNF : (((u * k : ℕ) : F)) ≠ 0 := by exact_mod_cast hNpos.ne'
    have hvz : vinc (F := F) z = y' := by
      rw [hz, vinc_Fsmul, vinc_sub, e, add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul F, smul_smul,
        inv_mul_cancel₀ hNF, one_smul]
    have h1 := hNL z (by rw [hvz]; exact hy')
    have h2 : (((u * k : ℕ) : F)) • z = x - l := by
      rw [hz, smul_smul, mul_inv_cancel₀ hNF, one_smul]
    rw [h2] at h1
    have := crd_add b L0 h1 hl
    simpa using this
  · intro hx
    exact vinc_mem L hx

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermSk
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def Sw (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (t : HeightOneSpectrum (𝓞 F)) : Submonoid (𝓞 E) :=
  t.asIdeal.primeCompl.map (algebraMap (𝓞 F) (𝓞 E))

def LocSw : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E), (∀ a, σ a = star a) → (∀ e, σ e = e → ∃ c : F, algebraMap F E c = e) →
    ∀ (V : Type) [AddCommGroup V] [Module (𝓞 E) V] (p : Ideal (𝓞 E)), p.IsMaximal →
    ∀ t : HeightOneSpectrum (𝓞 F), t.asIdeal = p.comap (algebraMap (𝓞 F) (𝓞 E)) →
    ∀ X : Submodule (𝓞 E) V, loc (K := E) p X = locS (Sw F E t) X

def CloseLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ e, σ (σ e) = e) → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J → IsUnit J.det → Submodule.IsFullLattice E L0 →
    ∀ g : GL (Fin M) E, g ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ D' : 𝓞 F, D ∣ D' → ∀ γ : GL (Fin M) E, γ ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
      ∀ t : HeightOneSpectrum (𝓞 F),
      (∀ i j, ∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (t.adicCompletion F) (PI.UnitaryApproxDefs.intOE E)
          (t.adicCompletionIntegers F).toSubring,
        PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) ((g : Matrix (Fin M) (Fin M) E) i j) -
            PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) ((γ : Matrix (Fin M) (Fin M) E) i j) =
          PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) (algebraMap F E (D' : F)) * s) →
      locS (Sw F E t) (gmap (linOf b γ) L0) = locS (Sw F E t) (gmap (linOf b g) L0)

def WPlace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (p : Ideal (𝓞 E)), p.IsMaximal → p.comap (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥

def BcU : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (R : Type) [CommRing R] [Algebra F R] (g : GL (Fin M) E),
    g ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
    Units.map ((PI.UnitaryApproxDefs.inclE (F := F) (E := E) R).mapMatrix :
      Matrix (Fin M) (Fin M) E →+* Matrix (Fin M) (Fin M) (E ⊗[F] R)).toMonoidHom g ∈ PI.UnitaryApproxDefs.UPts σ J R

def GramOK : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [StarRing E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ a, σ a = star a) → ∀ (V : Type) [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V),
    h.IsSymm → h.Nondegenerate → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) (gramOf h b) ∧ IsUnit (gramOf h b).det

abbrev Fix {E : Type} [Field E] (s : E →+* E) : Subfield E := RingHom.eqLocusField s (RingHom.id E)

def sigFix {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) :
    E →ₐ[Fix (σ : E →+* E)] E :=
  { (σ : E →+* E) with commutes' := fun r => r.2 }

theorem hermApprox_of (hL : LocSw) (hC : CloseLoc) (hW : WPlace) (hB : BcU) (hG : GramOK) :
    HermApprox := by
  intro F E _ _ _ _ _ _ σ V _ _ _ _ _ h M b L0 hσ hθ hS hN hL0 N hNg P hP
  classical
  have hσσ : ∀ e, σ (σ e) = e := fun e => by rw [hσ, hσ, star_star]
  obtain ⟨hH, hdet⟩ := hG F E σ hσ V h M b hS hN
  set J := gramOf h b with hJ
  let K0 : Subfield E := Fix (σ : E →+* E)
  let σ0 : E →ₐ[K0] E := sigFix σ
  have hσ0 : ∀ e, σ0 e = σ e := fun _ => rfl
  have hσσ0 : ∀ e, σ0 (σ0 e) = e := fun e => hσσ e
  have hθ0 : ∃ θ, σ0 θ ≠ θ := hθ
  have hH0 : PI.UnitaryApproxDefs.IsHerm (σ0 : E →+* E) J := hH
  have hfix : ∀ e, σ0 e = e → ∃ c : K0, algebraMap K0 E c = e := fun e he => ⟨⟨e, he⟩, rfl⟩
  have hσstar : ∀ a, σ0 a = star a := fun a => hσ a

  have wit : ∀ p : P, ∃ u ∈ isom h,
      gmap u (loc (K := E) (p : Ideal (𝓞 E)) L0) = loc (K := E) (p : Ideal (𝓞 E)) N :=
    fun p => hNg.2 p (hP p p.2)
  choose u hu hul using wit
  let g : P → GL (Fin M) E := fun p => matGL b (u p)
  have hg : ∀ p, g p ∈ PI.UnitaryApproxDefs.UJ (σ0 : E →+* E) J := fun p => matGL_mem σ hσ h b (hu p)

  let w : P → HeightOneSpectrum (𝓞 K0) := fun p =>
    ⟨(p : Ideal (𝓞 E)).comap (algebraMap (𝓞 K0) (𝓞 E)),
      by have := (hP _ p.2).isPrime; infer_instance, hW K0 E _ (hP _ p.2)⟩
  let T : Finset (HeightOneSpectrum (𝓞 K0)) := Finset.univ.image w
  let gl : (t : HeightOneSpectrum (𝓞 K0)) → GL (Fin M) (E ⊗[K0] t.adicCompletion K0) := fun t =>
    if hx : ∃ p, w p = t then
      Units.map ((PI.UnitaryApproxDefs.inclE (F := K0) (E := E) (t.adicCompletion K0)).mapMatrix :
        Matrix (Fin M) (Fin M) E →+* Matrix (Fin M) (Fin M) (E ⊗[K0] t.adicCompletion K0)).toMonoidHom
          (g (Classical.choose hx))
    else 1
  have hgl : ∀ t ∈ T, gl t ∈ PI.UnitaryApproxDefs.UPts σ0 J (t.adicCompletion K0) := by
    intro t _
    by_cases hx : ∃ p, w p = t
    · simp only [gl, dif_pos hx]
      exact hB K0 E σ0 M J _ _ (hg _)
    · simp only [gl, dif_neg hx]
      exact one_mem _

  have hCp := fun p : P => hC K0 E σ0 V M J b L0 hσσ0 hH0 hdet hL0 (g p) (hg p)
  choose D hD0 hDcl using hCp
  let Dall : 𝓞 K0 := ∏ p, D p
  have hDall : Dall ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hD0 p
  obtain ⟨γ, hγ, hc⟩ := unitary_approximation_finite K0 E (Fin M) σ0 J hσσ0 hθ0 hH0 hdet
    T gl hgl Dall hDall
  refine ⟨⟨γ, hγ⟩, fun q hq => ?_⟩
  let q' : P := ⟨q, hq⟩
  have hx : ∃ p, w p = w q' := ⟨q', rfl⟩
  set ps := Classical.choose hx with hps
  have hpw : w ps = w q' := Classical.choose_spec hx
  have hT : w q' ∈ T := Finset.mem_image_of_mem w (Finset.mem_univ _)
  have hcong := hc (w q') hT
  have hglq : gl (w q') = Units.map ((PI.UnitaryApproxDefs.inclE (F := K0) (E := E) ((w q').adicCompletion K0)).mapMatrix :
        Matrix (Fin M) (Fin M) E →+* Matrix (Fin M) (Fin M) (E ⊗[K0] (w q').adicCompletion K0)).toMonoidHom
          (g ps) := dif_pos hx
  rw [hglq] at hcong
  have hcl := hDcl ps Dall (Finset.dvd_prod_of_mem _ (Finset.mem_univ _)) γ hγ (w q') hcong
  have eq1 := hL K0 E σ0 hσstar hfix V q (hP q hq) (w q') rfl
  have eq2 := hL K0 E σ0 hσstar hfix V (ps : Ideal (𝓞 E)) (hP _ ps.2) (w q') (by rw [← hpw])
  show loc (K := E) q (gmap (linOf b γ) L0) = loc (K := E) q N
  rw [eq1, eq1, hcl, ← eq2, ← eq2, linOf_matGL, locGmapStep E V (u ps) (ps : Ideal (𝓞 E)) L0]
  exact hul ps

end PI.UnitaryGroupMassFormula.UJClassMass

end
end
