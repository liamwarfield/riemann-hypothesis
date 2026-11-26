module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntiOfKer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerPresentationMatrixOfGaloisCohomology

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCocycleChangeScalarsBack
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
  GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.TameQuot

namespace GlobalTheory.StepTwo.StartInd

theorem unrAt_eq_top {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal)
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R (G F Ω) M)
    (htriv : ∀ σ ∈ Ine (F := F) A, ∀ m, rho σ m = m) (htor : ∀ m : M, ∃ n : ℕ, l ^ n • m = 0)
    (hφ : ∀ φ : G F Ω, IsFrob A (normV v) φ → ∀ m, rho φ m = normV v • m → m = 0) :
    Formalism.GaloisCohomology.unrAt rho A = ⊤ := by
  rw [eq_top_iff]
  intro x _
  induction x using Submodule.Quotient.induction_on with
  | H c =>
  obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hrel⟩ := TameQuotient_holds F Ω l A v hA hl
  obtain ⟨φ, hφ'⟩ := exists_isFrob (F := F) hA
  have hc : ∀ g h : Dec (F := F) A, c.1 (g * h) = c.1 g + rho g (c.1 h) := c.2.2
  have hc1 : c.1 1 = 0 := by
    have := hc 1 1
    simpa using this
  let ι : Ine (F := F) A →* Dec (F := F) A := Subgroup.inclusion (Ine_le_Dec A)
  let f : Ine (F := F) A →* Multiplicative M := MonoidHom.mk' (fun σ => Multiplicative.ofAdd (c.1 (ι σ))) fun a b => by
    rw [map_mul, hc, htriv _ (show ((ι a : Dec (F := F) A) : G F Ω) ∈ Ine (F := F) A from a.2), ofAdd_add]
  have hι : Continuous ι := continuous_subtype_val.subtype_mk _
  have hf : Continuous f := continuous_ofAdd.comp (c.2.1.comp hι)
  have ho : IsOpen (f.ker : Set (Ine (F := F) A)) := (isOpen_discrete {1}).preimage hf
  have hcl : IsClosed (f.ker : Set (Ine (F := F) A)) := isClosed_singleton.preimage hf
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have : CompactSpace (Ine (F := F) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  have hfin : Finite (Ine (F := F) A ⧸ f.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hp : IsPGroup l (Ine (F := F) A ⧸ f.ker) := fun y => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨n, hn⟩ := htor (c.1 (ι y))
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
    exact congrArg Multiplicative.ofAdd hn
  have hJ : ineKer F A l ≤ f.ker.map (Ine (F := F) A).subtype :=
    Subgroup.map_mono fun σ hσ => mem_proKer.1 hσ _ inferInstance ho (IsPGroup.iff_card.1 hp)
  have hker : ∀ σ : Ine (F := F) A, (σ : G F Ω) ∈ f.ker.map (Ine (F := F) A).subtype → f σ = 1 := fun σ h =>
    (Subgroup.mem_map_iff_mem (Ine (F := F) A).subtype_injective).1 h
  let γ' : Ine (F := F) A := ⟨γ, hγ.1⟩
  let φ' : Dec (F := F) A := ⟨φ, hφ'.1⟩
  have hγ0 : f γ' = 1 := by
    have h1 := hJ (hrel φ' (ι γ') hφ' hγ).2.1
    have h2 := hker ((γ' ^ normV v)⁻¹ * ⟨φ * γ * φ⁻¹, conj_mem_Ine hφ'.1 hγ.1⟩) (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at h1 ⊢
      exact h1)
    rw [map_mul, map_inv, map_pow, inv_mul_eq_one] at h2
    have h3 : normV v • c.1 (ι γ') = c.1 (φ' * ι γ' * φ'⁻¹) := congrArg Multiplicative.toAdd h2
    have h4 := hc φ' φ'⁻¹
    rw [mul_inv_cancel, hc1] at h4
    have h5 : c.1 (φ' * ι γ' * φ'⁻¹) = rho φ (c.1 (ι γ')) := by
      rw [mul_assoc, hc, hc, htriv _ (show ((ι γ' : Dec (F := F) A) : G F Ω) ∈ Ine (F := F) A from hγ.1), map_add (f := _),
        add_left_comm, ← h4, add_zero]
    exact congrArg Multiplicative.ofAdd (hφ φ hφ' _ (h5.symm.trans h3.symm))
  have hall : Ine (F := F) A ≤ f.ker.map (Ine (F := F) A).subtype := by
    refine hγ.2.trans (Subgroup.topologicalClosure_minimal _ (sup_le ?_ hJ) ?_)
    · rw [Subgroup.zpowers_le]
      exact ⟨γ', hγ0, rfl⟩
    · exact (isClosed_Ine A).isClosedMap_subtype_val _ hcl
  refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun g => ?_⟩)
  have := hker ⟨g.1.1, g.2⟩ (hall g.2)
  rw [map_zero, sub_zero]
  exact congrArg Multiplicative.toAdd this

section Scalars

variable {Γ Λ Λ' M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing Λ] [CommRing Λ'] [AddCommGroup M] [Module Λ M] [Module Λ' M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul Λ M] [ContinuousConstSMul Λ' M]
  (π : Λ →+* Λ') (hs : ∀ (a : Λ) (m : M), a • m = π a • m) (rho : Representation Λ Γ M) (rho' : Representation Λ' Γ M)
  (h : ∀ g m, rho g m = rho' g m)

def z1Ch : Z1 rho →ₛₗ[π] Z1 rho' where
  toFun z := ⟨z.1, z.2.1, fun g k => by rw [← h]; exact z.2.2 g k⟩
  map_add' _ _ := rfl
  map_smul' a z := Subtype.ext (funext fun g => hs a (z.1 g))

def h1Ch : H1 rho →ₛₗ[π] H1 rho' :=
  Submodule.mapQ _ _ (z1Ch π hs rho rho' h) fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hz
    exact (mem_coboundaries1 _ _).2 ⟨m, fun g => by rw [← h]; exact hm g⟩

def continuousCocycleChangeScalarsBack (z : Z1 rho') : Z1 rho := ⟨z.1, z.2.1, fun g k => by rw [h]; exact z.2.2 g k⟩

theorem h1Ch_back (z : Z1 rho') :
    h1Ch π hs rho rho' h (Submodule.Quotient.mk (continuousCocycleChangeScalarsBack rho rho' h z)) = Submodule.Quotient.mk z := rfl

theorem h1Ch_eq_zero {x : H1 rho} : h1Ch π hs rho rho' h x = 0 ↔ x = 0 := by
  refine ⟨fun hx => ?_, fun hx => by rw [hx, map_zero]⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
  obtain ⟨m, hm⟩ := (mem_coboundaries1 rho' _).1 ((Submodule.Quotient.mk_eq_zero ((B1 rho').comap (Z1 rho').subtype)
    (x := z1Ch π hs rho rho' h z)).1 hx)
  exact (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun g => by rw [h]; exact hm g⟩)

theorem h1Ch_bijective : Function.Bijective (h1Ch π hs rho rho' h) := by
  refine ⟨(injective_iff_map_eq_zero' _).2 fun _ => h1Ch_eq_zero π hs rho rho' h, fun y => ?_⟩
  induction y using Submodule.Quotient.induction_on with
  | H z => exact ⟨_, h1Ch_back π hs rho rho' h z⟩

theorem h1Ch_res {Δ : Type} [Group Δ] [TopologicalSpace Δ] (ψ : Δ →* Γ) (hψ : Continuous ψ) (x : H1 rho) :
    resH1 rho' ψ hψ (h1Ch π hs rho rho' h x) =
      h1Ch π hs (rho.comp ψ) (rho'.comp ψ) (fun g m => h (ψ g) m) (resH1 rho ψ hψ x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

end Scalars

theorem exists_equiv_of_surjective {Λ Λ' V W W' : Type} [CommRing Λ] [CommRing Λ'] [AddCommGroup V] [Module Λ V] [Module Λ' V]
    [AddCommGroup W] [Module Λ W] [AddCommGroup W'] [Module Λ' W'] (π : Λ →+* Λ') (hπ : Function.Surjective π)
    (hs : ∀ (a : Λ) (m : V), a • m = π a • m) (K : Submodule Λ V) (K' : Submodule Λ' V) (hK : ∀ x, x ∈ K' ↔ x ∈ K)
    (S : Submodule Λ W) (S' : Submodule Λ' W') (f : W →ₛₗ[π] W') (hf : Function.Bijective f) (hS : ∀ x, f x ∈ S' ↔ x ∈ S)
    (e : K ≃ₗ[Λ] S) : ∃ e' : K' ≃ₗ[Λ'] S', ∀ x : K', (e' x).1 = f (e ⟨x.1, (hK _).1 x.2⟩).1 := by
  let g : K' →ₗ[Λ'] S' :=
    { toFun := fun x => ⟨f (e ⟨x.1, (hK _).1 x.2⟩).1, (hS _).2 (Subtype.prop _)⟩
      map_add' := fun x y => Subtype.ext (by
        change _ = f _ + f _
        rw [← map_add (f := _), ← Submodule.coe_add, ← map_add (f := _)]; rfl)
      map_smul' := fun a x => Subtype.ext (by
        obtain ⟨a, rfl⟩ := hπ a
        change _ = π a • f _
        rw [← LinearMap.map_smulₛₗ, ← Submodule.coe_smul, ← map_smul]
        exact congrArg (fun t => f (e t).1) (Subtype.ext (hs a x.1).symm)) }
  refine ⟨LinearEquiv.ofBijective g ⟨fun x y hxy => ?_, fun y => ?_⟩, fun _ => rfl⟩
  · exact Subtype.ext (congrArg Subtype.val (e.injective (Subtype.ext (hf.1 (congrArg Subtype.val hxy)))) :)
  · obtain ⟨w, hw⟩ := hf.2 y.1
    obtain ⟨x, hx⟩ := e.surjective ⟨w, (hS _).1 (hw ▸ y.2)⟩
    refine ⟨⟨x.1, (hK _).2 x.2⟩, Subtype.ext ?_⟩
    change f (e x).1 = _
    rw [hx, hw]

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X) (i : X.Tw)

section Sel

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [Algebra (X.O0 i) Λ] [Algebra (X.O0 i) Λ'] (π : Λ →ₐ[X.O0 i] Λ')
  {κ : GE N →* Λˣ} {κ' : GE N →* Λ'ˣ} (hκ : ∀ g, π (κ g : Λˣ) = (κ' g : Λ'ˣ)) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {B : Type} [AddCommGroup B] [Module Λ B] [Module Λ' B] (hs : ∀ (a : Λ) (b : B), a • b = π a • b)

include hκ hs in
theorem repOn_eq (g : GE N) (m : Fin r → B) : repOn ρ κ B g m = repOn ρ κ' B g m := by
  funext a
  simp [repOn, matAct, hs, hκ]

variable [TopologicalSpace B] [DiscreteTopology B]

abbrev ch : H1 (repOn ρ κ B) →ₛₗ[(π : Λ →+* Λ')] H1 (repOn ρ κ' B) :=
  h1Ch (π : Λ →+* Λ') (fun a m => funext fun c => hs a (m c)) _ _ (repOn_eq i π hκ ρ hs)

abbrev chLoc (v : PlE D.host) :
    H1 ((repOn ρ κ B).comp (DecV N v).subtype) →ₛₗ[(π : Λ →+* Λ')] H1 ((repOn ρ κ' B).comp (DecV N v).subtype) :=
  h1Ch (π : Λ →+* Λ') (fun a m => funext fun c => hs a (m c)) _ _ (fun g m => repOn_eq i π hκ ρ hs g m)

theorem chLoc_mem_bkOn (hπ : Function.Surjective π) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i))
    (y : H1 ((repOn ρ κ B).comp (DecV N v).subtype)) :
    chLoc i π hκ ρ hs v y ∈ bkOn bkP i ρ κ' B v ↔ y ∈ bkOn bkP i ρ κ B v := by
  have : RingHomSurjective (π : Λ →+* Λ') := ⟨hπ⟩
  unfold bkOn
  rw [dite_eq_left hv, dite_eq_left hv]
  refine Iff.trans ?_ (Submodule.apply_mem_span_image_iff_mem_span (f := chLoc i π hκ ρ hs v) (h1Ch_bijective _ _ _ _ _).1)
  refine iff_of_eq (congrArg (fun S => chLoc i π hκ ρ hs v y ∈ Submodule.span Λ' S) (Set.ext fun w => ⟨?_, ?_⟩))
  · rintro ⟨z, c, y, b, h1, h2, h3, rfl⟩
    exact ⟨_, ⟨continuousCocycleChangeScalarsBack _ ((repOn ρ κ' B).comp (DecV N v).subtype) (fun g m => repOn_eq i π hκ ρ hs g m) z, c, y, b, h1, h2,
      fun g a => by rw [hs, AlgHom.commutes]; exact h3 g a, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, c, y, b, h1, h2, h3, rfl⟩, rfl⟩
    exact ⟨continuousCocycleChangeScalarsBack _ ((repOn ρ κ B).comp (DecV N v).subtype) (fun g m => (repOn_eq i π hκ ρ hs g m).symm) z, c, y, b, h1, h2,
      fun g a => by rw [← π.commutes, ← hs]; exact h3 g a, rfl⟩

theorem ch_mem_selOn (hπ : Function.Surjective π) (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ B)) :
    ch i π hκ ρ hs x ∈ selOn bkP i ρ κ' B Q ↔ x ∈ selOn bkP i ρ κ B Q := by
  refine (mem_Sel _ _ _ _ _).trans (Iff.trans (forall_congr' fun v => ?_) (mem_Sel _ _ _ _ _).symm)
  refine (iff_of_eq (congrArg (· ∈ _) (h1Ch_res _ _ _ _ _ _ _ _))).trans ?_
  unfold Formalism.GaloisCohomology.bkCond
  split_ifs with h1 h2
  · exact chLoc_mem_bkOn bkP i π hκ ρ hs hπ v h1 _
  · exact iff_of_true trivial trivial
  · exact (iff_of_eq (congrArg (· = 0) (h1Ch_res _ _ _ _ _ _ _ _))).trans (h1Ch_eq_zero _ _ _ _ _)

end Sel

theorem computes_map (s : X.Sig i) (M : ℕ) {ι ι' : Type} (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M))))
    (d' : ι' → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (π : abelian₂ X i M ι →ₐ[X.O0 i] abelian₂ X i M ι')
    (hπ : Function.Surjective π) (hκ : ∀ g, π (delInv i M d g : (abelian₂ X i M ι)ˣ) = (delInv i M d' g : (abelian₂ X i M ι')ˣ))
    (Q Q' : Finset (PlE D.host))
    (hQ : ∀ (B : Type) [AddCommGroup B] [Module (abelian₂ X i M ι') B] [TopologicalSpace B] [DiscreteTopology B],
      (∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0) →
      selOn bkP i (Tgl i s) (delInv i M d') B Q' = selOn bkP i (Tgl i s) (delInv i M d') B Q)
    {a : ℕ} (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)) (h : Computes bkP i s M d Q Φ) :
    Computes bkP i s M d' Q' (Φ.map π) := by
  obtain ⟨e, he⟩ := h
  have key := fun (B : Type) [AddCommGroup B] [Module (abelian₂ X i M ι') B] [TopologicalSpace B] [DiscreteTopology B]
      (hB : ∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0) =>
    letI : Module (abelian₂ X i M ι) B := Module.compHom B (π : abelian₂ X i M ι →+* abelian₂ X i M ι')
    exists_equiv_of_surjective (π : abelian₂ X i M ι →+* abelian₂ X i M ι') hπ (V := Fin a → B) (fun _ _ => rfl)
      (LinearMap.ker (matAct (M := B) Φ)) (LinearMap.ker (matAct (M := B) (Φ.map π))) (fun _ => Iff.rfl)
      (selOn bkP i (Tgl i s) (delInv i M d) B Q) (selOn bkP i (Tgl i s) (delInv i M d') B Q')
      (ch i π hκ (Tgl i s) (B := B) fun _ _ => rfl) (h1Ch_bijective _ _ _ _ _)
      (fun x => by rw [hQ B hB]; exact ch_mem_selOn bkP i π hκ _ _ hπ Q x) (e B hB)
  choose e' he' using key
  refine ⟨e', fun B B' _ _ _ _ _ _ _ _ hB hB' f x x' z z' hx hz h0 => ?_⟩
  letI : Module (abelian₂ X i M ι) B := Module.compHom B (π : abelian₂ X i M ι →+* abelian₂ X i M ι')
  letI : Module (abelian₂ X i M ι) B' := Module.compHom B' (π : abelian₂ X i M ι →+* abelian₂ X i M ι')
  let f₀ : B →ₗ[abelian₂ X i M ι] B' := ⟨f.toAddHom, fun c b => f.map_smul (π c) b⟩
  rw [he'] at h0 ⊢
  have h1 := he B B' hB hB' f₀ ⟨x.1, x.2⟩ ⟨x'.1, x'.2⟩
    (continuousCocycleChangeScalarsBack _ _ (repOn_eq i π hκ (Tgl i s) (B := B) fun _ _ => rfl) z)
    (continuousCocycleChangeScalarsBack _ _ (repOn_eq i π hκ (Tgl i s) (B := B') fun _ _ => rfl) z') hx hz ((h1Ch_bijective _ _ _ _ _).1 h0)
  exact congrArg (ch i π hκ (Tgl i s) (B := B') fun _ _ => rfl) h1

section Frob

variable (s : X.Sig i)

def tbar : GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (X.O0 i)) :=
  (IsLocalRing.residue (X.O0 i)).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (Tgl i s))

theorem tbar_apply (g : GE N) : tbar i s g = (Tmat i s g).map (IsLocalRing.residue (X.O0 i)) := by
  rw [← Tgl_coe]; rfl

theorem tbar_of_conj {g σ : GE N} {u : IsLocalRing.ResidueField (X.O0 i)} (h : tbar i s (g * σ * g⁻¹) = u • 1) :
    tbar i s σ = u • 1 := by
  have e : σ = g⁻¹ * (g * σ * g⁻¹) * g := by group
  rw [e, map_mul, map_mul, h, mul_smul_comm, mul_one, smul_mul_assoc, ← map_mul, inv_mul_cancel, map_one]

theorem tbar_frob (hG : GalHyp bkP i s) {L : Subgroup (GE N)} {z : GE N} (hz : IsTameInertiaElementAtTwistPrime X i z) (hL : Small i s L z)
    {P v : PlE D.host} (hP : ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L) (hv : Over P v)
    (hl : v ∉ placesOver D.host.E (X.l i)) (hq : IsLocalRing.residue (X.O0 i) (normV v : X.O0 i) = 1)
    {φ : GE N} (hφ : IsFrob (N.plOm.1 v) (normV v) φ) :
    ∃ u : IsLocalRing.ResidueField (X.O0 i), u ≠ 1 ∧ tbar i s φ = u • 1 := by
  obtain ⟨d, hd, -, hd1, hez⟩ := TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z hG.1 hz
  let ε : GE N →* IsLocalRing.ResidueField (X.O0 i) :=
    (IsLocalRing.residue (X.O0 i)).toMonoidHom.comp ((Units.coeHom _).comp (eps0 X i))
  have hε : ∀ g, IsLocalRing.residue (X.O0 i) (eps0 X i g : (X.O0 i)ˣ) = ε g := fun _ => rfl
  have hεc : ∀ g σ, ε (g * σ * g⁻¹) = ε σ := fun g σ => by
    rw [map_mul, map_mul, mul_right_comm, ← map_mul, mul_inv_cancel, map_one, one_mul]
  set u := IsLocalRing.residue (X.O0 i) d with hu
  have hu1 : u ≠ 1 := fun h => (hd1.map (IsLocalRing.residue (X.O0 i))).ne_zero (by rw [map_sub, map_one, ← hu, h, sub_self])
  have hu0 : u ≠ 0 := (d.isUnit.map _).ne_zero
  have h0 : ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → tbar i s σ = u • 1 ∧ ε σ = 1 := fun σ hσ => by
    obtain ⟨g, hg⟩ := hP σ hσ
    obtain ⟨h1, h2⟩ := hL.2.2.2.2 _ hg
    have e : g * σ * g⁻¹ = g * σ * g⁻¹ * z⁻¹ * z := by group
    constructor
    · refine tbar_of_conj i s (g := g) ?_
      rw [e, map_mul, tbar_apply, h1, one_mul, tbar_apply, hd]
      ext a b
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp [hu]
    · rw [← hεc g, e, map_mul, ← hε, h2, one_mul, ← hε, hez, Units.val_one, map_one]
  rcases hv with rfl | hv
  · exact ⟨u, hu1, (h0 φ hφ).1⟩
  obtain ⟨σ, g, hσ, rfl⟩ := exists_frob_of_conj X hv hφ
  obtain ⟨h1, h2⟩ := h0 σ hσ
  have h3 : ε (cConj X σ) = 1 := by
    rw [← hεc g, ← hq]
    change IsLocalRing.residue (X.O0 i) (algebraMap ℤ_[X.l i] (X.O0 i) (cycZ D.host.E N.Om (X.l i) _ : ℤ_[X.l i]ˣ)) = _
    rw [cycZ_of_isFrob hl (N.plOm.2 v) hφ, map_natCast]
  obtain ⟨A, hA⟩ := hG.2.2.1
  have h4 := congrArg (IsLocalRing.residue (X.O0 i)).mapMatrix (hA σ (cConj X σ) fun _ => rfl)
  have h5 : (Tmat i s (cConj X σ))⁻¹ = Tmat i s (cConj X σ)⁻¹ := by
    rw [← Tgl_coe, ← Tgl_coe, map_inv, Matrix.coe_units_inv]
  have hsm : ∀ (c : X.O0 i) (Y : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)), (IsLocalRing.residue (X.O0 i)).mapMatrix (c • Y) =
      IsLocalRing.residue (X.O0 i) c • Y.map (IsLocalRing.residue (X.O0 i)) := fun c Y => by
    ext a b
    simp
  rw [Tdual, h5, map_mul, map_mul, hsm, hsm, map_pow, hε, hε, h2, h3, one_pow, one_smul, one_smul, ← tbar_apply, h1,
    mul_smul_comm, mul_one, smul_mul_assoc, ← map_mul, Units.mul_inv, map_one, Matrix.transpose_map, ← tbar_apply] at h4
  have h6 : tbar i s (cConj X σ)⁻¹ = u • 1 := by
    rw [← Matrix.transpose_transpose (tbar i s _), h4, Matrix.transpose_smul, Matrix.transpose_one]
  refine ⟨u⁻¹, inv_ne_one.2 hu1, tbar_of_conj i s (g := g⁻¹) ?_⟩
  have h7 : tbar i s (cConj X σ * (cConj X σ)⁻¹) = 1 := by rw [mul_inv_cancel, map_one]
  rw [map_mul, h6, mul_smul_comm, mul_one] at h7
  have e : g⁻¹ * (g * cConj X σ * g⁻¹) * g⁻¹⁻¹ = cConj X σ := by group
  rw [e, ← h7, smul_smul, inv_mul_cancel₀ hu0, one_smul]

theorem eq_zero_of_scalar {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) {B : Type} [AddCommGroup B]
    [Module Λ B] {φ : GE N} {n q : ℕ} (hκ : κ φ ^ (X.l i ^ n) = 1) {u : IsLocalRing.ResidueField (X.O0 i)} (hu : u ≠ 1)
    (hφ : tbar i s φ = u • 1) (hq : IsLocalRing.residue (X.O0 i) (q : X.O0 i) = 1) (m : Fin D.R.r → B)
    (hm : repOn (Tgl i s) κ B φ m = q • m) : m = 0 := by
  have hpow : ∀ k : ℕ, repOn (Tgl i s) κ B (φ ^ k) m = q ^ k • m := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, map_mul, Module.End.mul_apply, hm, map_nsmul, ih, smul_smul, pow_succ']
  set k := X.l i ^ n with hk
  let Y : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) := Tmat i s (φ ^ k) - ((q : X.O0 i) ^ k) • 1
  have hY : (IsLocalRing.residue (X.O0 i)).mapMatrix Y = (u ^ k - 1) • 1 := by
    have h1 := tbar_apply i s (φ ^ k)
    rw [map_pow, hφ, smul_pow, one_pow] at h1
    rw [map_sub, RingHom.mapMatrix_apply, ← h1, sub_smul]
    congr 1
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul, map_pow,
      hq]
    split_ifs <;> simp
  have hp : Fact (X.l i).Prime := X.lPrime i
  have hch : CharP (IsLocalRing.ResidueField (X.O0 i)) (X.l i) := (CharP.charP_iff_prime_eq_zero hp.out).2 (by
    rw [← map_natCast (IsLocalRing.residue (X.O0 i))]
    exact (IsLocalRing.residue_eq_zero_iff _).2 (SmallSub.l_mem X i))
  have huk : u ^ k - 1 ≠ 0 := by
    have := sub_pow_char_pow (p := X.l i) (n := n) u 1
    rw [one_pow] at this
    rw [← this]
    exact pow_ne_zero _ (sub_ne_zero.2 hu)
  have hYu : IsUnit Y := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hY, Matrix.det_smul,
      Matrix.det_one, mul_one]
    exact pow_ne_zero _ huk
  obtain ⟨Z, hZ⟩ := (hYu.map (algebraMap (X.O0 i) Λ).mapMatrix).exists_left_inv
  have h0 : matAct ((algebraMap (X.O0 i) Λ).mapMatrix Y) m = 0 := by
    funext a
    have h1 := congrFun (hpow k) a
    simp only [repOn, MonoidHom.coe_mk, OneHom.coe_mk, map_pow κ, hκ, Units.val_one, one_smul, Tgl_coe] at h1
    simp only [matAct, LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply, Pi.smul_apply] at h1
    simp [matAct, Y, sub_smul, Finset.sum_sub_distrib, h1, Matrix.one_apply, apply_ite (algebraMap (X.O0 i) Λ),
      ← Nat.cast_smul_eq_nsmul Λ]
  have h1 := congrArg (matAct Z) h0
  rwa [map_zero, ← Module.End.mul_apply, ← matAct_mul, hZ, matAct_one] at h1

end Frob

section Restrict

variable (M : ℕ) {ι ι' : Type} (e : ι' → ι)

def resLam : abelian₂ X i M ι →ₐ[X.O0 i] abelian₂ X i M ι' :=
  MonoidAlgebra.mapDomainAlgHom (X.O0 i) (X.O0 i)
    (MonoidHom.mk' (fun x : Del X i M ι => (Multiplicative.ofAdd fun q => x.toAdd (e q) : Del X i M ι')) fun _ _ => rfl)

theorem resLam_of (x : Del X i M ι) : resLam i M e (MonoidAlgebra.of (X.O0 i) _ x) =
    MonoidAlgebra.of (X.O0 i) (Del X i M ι') (Multiplicative.ofAdd fun q => x.toAdd (e q)) := by
  simp [resLam]

theorem delInv_coe (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (g : GE N) :
    ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) = MonoidAlgebra.of (X.O0 i) _ (delAll X i M d g⁻¹) := by
  rw [delInv, MonoidHom.inv_apply, ← map_inv]; rfl

theorem resLam_delInv (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (g : GE N) :
    resLam i M e (delInv i M d g : (abelian₂ X i M ι)ˣ) = (delInv i M (fun q => d (e q)) g : (abelian₂ X i M ι')ˣ) := by
  rw [delInv_coe, delInv_coe, resLam_of]; rfl

theorem delInv_pow (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (g : GE N) : delInv i M d g ^ (X.l i ^ M) = 1 := by
  apply Units.ext
  have : delAll X i M d g⁻¹ ^ (X.l i ^ M) = 1 := by
    apply Multiplicative.toAdd.injective
    funext q
    rw [toAdd_pow, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rfl
  rw [Units.val_pow_eq_pow_val, delInv_coe, ← map_pow, this, map_one, Units.val_one]

variable {e} (he : Function.Injective e)

theorem resLam_toLam (F : MvPolynomial ι (X.O0 i)) :
    resLam i M e (toLam X i M ι F) = toLam X i M ι' (MvPolynomial.killCompl he F) := by
  have : (resLam i M e).comp (toLam X i M ι) = (toLam X i M ι').comp (MvPolynomial.killCompl he) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, map_sub, map_one, resLam_of]
    by_cases hq : q ∈ Set.range e
    · obtain ⟨q, rfl⟩ := hq
      rw [← MvPolynomial.rename_X e q, MvPolynomial.killCompl_rename_app, toLam, MvPolynomial.aeval_X]
      congr 3
      funext t
      by_cases ht : t = q <;> simp [Pi.single_apply, he.eq_iff, ht]
    · rw [MvPolynomial.killCompl, MvPolynomial.aeval_X, dite_eq_right hq, map_zero, sub_eq_zero, ← map_one (MonoidAlgebra.of _ _)]
      congr 1
      apply Multiplicative.toAdd.injective
      funext t
      have : e t ≠ q := fun h => hq ⟨t, h⟩
      simp [Pi.single_apply, this]
  exact DFunLike.congr_fun this F

include he in
theorem resLam_surjective : Function.Surjective (resLam (X := X) i M e) := by
  intro y
  induction y using MonoidAlgebra.induction_on with
  | of x =>
    refine ⟨MonoidAlgebra.of _ _ (Multiplicative.ofAdd (Function.extend e x.toAdd 0)), ?_⟩
    rw [resLam_of]
    congr 1
    apply Multiplicative.toAdd.injective
    funext t
    exact he.extend_apply _ _ t
  | add _ _ h h' =>
    obtain ⟨a, rfl⟩ := h
    obtain ⟨b, rfl⟩ := h'
    exact ⟨a + b, map_add _ _ _⟩
  | smul c _ h =>
    obtain ⟨a, rfl⟩ := h
    exact ⟨c • a, map_smul _ _ _⟩

end Restrict

theorem unr_first (s : X.Sig i) (hG : GalHyp bkP i s) {L : Subgroup (GE N)} {z : GE N} (hz : IsTameInertiaElementAtTwistPrime X i z) (hL : Small i s L z)
    {P v : PlE D.host} (hP : ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L) (hv : Over P v)
    (h0 : v ∉ X.S0 i) {M : ℕ} (hM : M ≠ 0) (hq : normV v % (2 * X.l i ^ M) = 1) {ι : Type}
    (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (hd : ∀ q, ∀ σ ∈ Ine (F := D.host.E) (N.plOm.1 v), d q σ = 1)
    (B : Type) [AddCommGroup B] [Module (abelian₂ X i M ι) B] [TopologicalSpace B] [DiscreteTopology B]
    (hB : ∀ b : B, ∃ n : ℕ, (X.l i ^ n) • b = 0) :
    Formalism.GaloisCohomology.unrAt (repOn (Tgl i s) (delInv i M d) B) (N.plOm.1 v) = ⊤ := by
  have hp : Fact (X.l i).Prime := X.lPrime i
  have hl : v ∉ placesOver D.host.E (X.l i) := fun h => h0 (X.twistExcludedPlaces_contains_residueChar i h)
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k h => h0 (X.placesOver_subset_exceptional i k h)
  have hq' : IsLocalRing.residue (X.O0 i) (normV v : X.O0 i) = 1 := by
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM
    rw [← Nat.mod_add_div (normV v) (2 * X.l i ^ (M + 1)), hq]
    simp [pow_succ, (IsLocalRing.residue_eq_zero_iff _).2 (SmallSub.l_mem X i), -map_natCast]
  refine unrAt_eq_top (X.l i) (N.plOm.2 v) hl _ (fun σ hσ m => ?_) (fun m => ?_) fun φ hφ m hm => ?_
  · have h1 : X.rhoS i s σ = 1 := hG.1.1 v hl hg _ (N.plOm.2 v) σ hσ
    have h2 : chiS i s σ = 1 := X.twistCharacterFamily_unramified i _ _ v hl hg (fun h => h0 (X.primes_subset_exceptional i h)) _ (N.plOm.2 v) σ hσ
    have h3 : Tmat i s σ = 1 := by simp [Tmat, h1, h2]
    have h4 : delAll X i M d σ = 1 := by
      apply Multiplicative.toAdd.injective
      funext q
      exact congrArg Multiplicative.toAdd (hd q σ hσ)
    have h5 : ((delInv i M d σ : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) = 1 := by rw [delInv_coe, map_inv, h4, inv_one, map_one]
    change (((delInv i M d σ : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) • matAct ((Tgl i s σ : Matrix _ _ (X.O0 i)).map
      (algebraMap (X.O0 i) (abelian₂ X i M ι)))) m = m
    rw [h5, one_smul, Tgl_coe, h3, Matrix.map_one _ (map_zero _) (map_one _), matAct_one, Module.End.one_apply]
  · choose n hn using fun a => hB (m a)
    refine ⟨∑ a, n a, funext fun a => ?_⟩
    obtain ⟨c, hc⟩ := pow_dvd_pow (X.l i) (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a))
    rw [Pi.smul_apply, hc, mul_comm, mul_smul, hn, smul_zero, Pi.zero_apply]
  · obtain ⟨u, hu, hφu⟩ := tbar_frob bkP i s hG hz hL hP hv hl hq' hφ
    exact eq_zero_of_scalar i s _ (delInv_pow i M d φ) hu hφu hq' m hm

theorem selOn_eq {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) (κ : GE N →* Λˣ)
    (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B] {Q Q' : Finset (PlE D.host)}
    (hs : Q' ⊆ Q) (h : ∀ v ∈ Q, v ∉ Q' → Formalism.GaloisCohomology.unrAt (repOn ρ κ B) (N.plOm.1 v) = ⊤) :
    selOn bkP i ρ κ B Q' = selOn bkP i ρ κ B Q := by
  refine congrArg (Formalism.GaloisCohomology.SelAll (repOn ρ κ B) N.plOm) (funext fun v => ?_)
  unfold Formalism.GaloisCohomology.bkCond
  split_ifs with h1 h2 h3 h3
  · rfl
  · rfl
  · exact absurd (h2.imp_right fun k => hs k) h3
  · exact h v (h3.resolve_left fun k => h2 (Or.inl k)) fun k => h2 (Or.inr k)
  · rfl

theorem start_of_galHyp : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ResBound bkP i s → Start bkP i s := by
  intro D N X bkP i s hG hRB M R n d A L z P φ φ' hn hM hz hL ⟨hAux, h1, h2⟩ hφ hco Q hQ a Φ hΦ
  classical
  let e : Fin n ⊕ Fin n → Fin R ⊕ Fin n := Sum.map (Fin.castLE hn) id
  have he : Function.Injective e := (Fin.castLE_injective hn).sumMap Function.injective_id
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hM
    omega
  let Q' := Q.filter fun v => ∃ q, Over (P (e q)) v
  have hQ' : IsQ (fun q => P (e q)) Q' := fun v => by
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun ⟨q, hq⟩ => ⟨(hQ v).2 ⟨_, hq⟩, q, hq⟩⟩
  have hPos : Position i s M (fun q => P (e q)) (fun q => d (P (e q))) φ φ' := by
    refine ⟨⟨fun q v hv => ?_, fun q q' h => he (hAux.2.1 _ _ h), fun q => hAux.2.2 _⟩,
      ⟨z, L, hz, hL, fun b => (h1 _).2, fun b b' σ hσ => ?_⟩, fun b => ⟨fun g hg => hL.2.2.2.2 g ((h2 b).1 hg), hφ b⟩⟩
    · obtain ⟨k1, k2, k3, k4, -, k6⟩ := hAux.1 _ v hv
      exact ⟨k1, k2, k3, k4, Finset.notMem_empty _, k6⟩
    · refine ((h2 b).2 (Fin.castLE hn b') σ hσ).trans ?_
      simp [Fin.ext_iff]
  have hC := computes_map bkP i s M (fun q => d (P q)) (fun q => d (P (e q))) (resLam i M e) (resLam_surjective i M he)
    (resLam_delInv i M e fun q => d (P q)) Q Q' (fun B _ _ _ _ hB =>
      selOn_eq bkP i _ _ B (Finset.filter_subset _ _) fun v hv' hv => by
        obtain ⟨q, hq⟩ := (hQ v).1 hv'
        have hno : ∀ q, ¬ Over (P (e q)) v := fun q h => hv ((hQ' v).2 ⟨q, h⟩)
        rcases q with b | b
        · obtain ⟨-, -, -, k4, -, k6⟩ := hAux.1 _ v hq
          exact unr_first bkP i s hG hz hL (h1 b).2 hq k4 hM0 k6 _
            (fun q => (hAux.2.2 (e q)).2.2.2.1 v (hno q) _ (N.plOm.2 v)) B hB
        · exact absurd hq (hno (.inr b))) Φ hΦ
  refine ((hRB M n _ _ φ φ' Q' hM hPos hQ' a _ hC).2 hco).imp_right fun ⟨b, c, h⟩ => ⟨b, c, fun F hF => ?_⟩
  obtain ⟨m, hm, hu⟩ := h (MvPolynomial.killCompl he F) (by
    rw [← resLam_toLam, hF]
    exact congrFun (congrFun ((resLam i M e).map_adjugate Φ) b) c)
  refine ⟨m.mapDomain e, ?_, fun j hj => Finsupp.mapDomain_of_notMem_range _ _ ?_, ?_⟩
  · rw [Finsupp.degree_mapDomain]
    omega
  · rintro ⟨q | q, hq⟩
    · have := congrArg Fin.val (Sum.inl.inj hq)
      have := q.2
      simp only [Fin.val_castLE] at *
      omega
    · exact Sum.inr_ne_inl hq
  · rwa [MvPolynomial.coeff_killCompl] at hu

theorem start_of_resBound : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstPlace i s → ResBound bkP i s → Start bkP i s :=
  fun D N X bkP i s hG _ hRB => start_of_galHyp D N X bkP i s hG hRB

end GlobalTheory.StepTwo.StartInd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddValLeOfNotMem
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.StepTwo.TwoBound

theorem dec_le_of_frob_mem {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) {σ : G F Ω}
    (hσ : IsFrob A (normV v) σ) {L : Subgroup (G F Ω)} (hL : IsOpen (L : Set (G F Ω))) (hI : Ine (F := F) A ≤ L)
    (hm : σ ∈ L) : Dec (F := F) A ≤ L := by
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω A v hA ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((L.subgroupOf (Dec (F := F) A) : Subgroup (Dec (F := F) A)) : Set (Dec (F := F) A)) :=
    (L.isClosed_of_isOpen hL).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) A) ⊔ (Ine (F := F) A).subgroupOf (Dec (F := F) A))
    (sup_le ((Subgroup.zpowers_le).2 (Subgroup.mem_subgroupOf.2 hm)) (fun x hx => hI hx)) hc
  rw [h] at h2
  intro g hg
  exact h2 (Subgroup.mem_top (⟨g, hg⟩ : Dec (F := F) A))

theorem addVal_le_of_notMem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {l x : O}
    (hx : x ∉ Ideal.span {l} * IsLocalRing.maximalIdeal O) :
    IsDiscreteValuationRing.addVal O x ≤ IsDiscreteValuationRing.addVal O l := by
  by_contra hlt
  push Not at hlt
  obtain ⟨y, rfl⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 hlt.le
  by_cases hy : IsUnit y
  · rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hy, add_zero] at hlt
    exact lt_irrefl _ hlt
  · exact hx (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self l) hy)

noncomputable def bound (w e r k : ℕ) : ℕ := Nat.rec w (fun _ b => 2 * (e + 1) * b + 2 + 2 * r) k

theorem bound_succ (w e r k : ℕ) : bound w e r (k + 1) = 2 * (e + 1) * bound w e r k + 2 + 2 * r := rfl

theorem bound_step (w e r k : ℕ) : bound w e r k + 1 + 2 * r ≤ bound w e r (k + 1) := by
  rw [bound_succ]; nlinarith [Nat.zero_le (e * bound w e r k)]

theorem bound_mono (w e r : ℕ) : Monotone (bound w e r) :=
  monotone_nat_of_le_succ fun k => le_trans (by omega) (bound_step w e r k)

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {bkP : BKPh X}
  {i : X.Tw} {s : X.Sig i} {M R n : ℕ} {d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))}

theorem NF_mono {P : Fin R ⊕ Fin n → PlE D.host} {c c' : ℕ} (hc : c ≤ c') (h : NF bkP i s M d P c) :
    NF bkP i s M d P c' := fun Q hQ a Φ hΦ F hF =>
  (h Q hQ a Φ hΦ F hF).imp fun _ hm => ⟨hm.1.trans_le hc, hm.2⟩

theorem NFit_mono {P : Fin R ⊕ Fin n → PlE D.host} {c c' : ℕ} (hc : c ≤ c') (h : NFit bkP i s M d P c) :
    NFit bkP i s M d P c' := fun Q hQ a Φ hΦ =>
  (h Q hQ a Φ hΦ).imp id fun ⟨b, b', hb⟩ => ⟨b, b', fun F hF => (hb F hF).imp fun _ hm => ⟨hm.1.trans_le hc, hm.2⟩⟩

theorem induct (hl : 0 < nu X i) {t R₀ : ℕ} (f : Fin t → X.Sig i) (hG : ∀ j, Grow bkP i (f j)) (hS : ∀ j, Step bkP i (f j))
    {H : Subgroup (GE N)} {S A : Finset (PlE D.host)} {L : Subgroup (GE N)} {z : GE N} {w e : ℕ}
    (he : IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e)
    (hM : bound w e D.R.r t ≤ X.l i ^ (M - nu X i - 1)) (h3 : nu X i + 2 ≤ M)
    (hd : AdmFam X i M H S d) (hLH : L ≤ H) (hz : IsTameInertiaElementAtTwistPrime X i z) (hL : ∀ j, Small2 i (f j) M L z)
    (P₀ : Fin (R₀ + t) ⊕ Fin R₀ → PlE D.host) (h₀ : PiLocalization₂ i M d A L z P₀) (hF : ∀ j, NFit bkP i (f j) M d P₀ (w + 1)) :
    ∀ k, k ≤ t → ∃ P : Fin (R₀ + t) ⊕ Fin (R₀ + k) → PlE D.host, (∀ a, P (.inl a) = P₀ (.inl a)) ∧ PiLocalization₂ i M d A L z P ∧
      (∀ j, NFit bkP i (f j) M d P (bound w e D.R.r k + 1)) ∧
      ∀ j : Fin t, j.val < k → NF bkP i (f j) M d P (bound w e D.R.r k + 1) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨P₀, fun _ => rfl, h₀, hF, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨P, hP, hSt, hFit, hNF⟩ := ih (by omega)
    have hb : bound w e D.R.r (k + 1) ≤ X.l i ^ (M - nu X i - 1) := (bound_mono w e D.R.r hk).trans hM
    have hs := bound_step w e D.R.r k
    obtain ⟨P', hE, hSt', hN⟩ := hS ⟨k, hk⟩ hl M (R₀ + t) (R₀ + k) H S d A L z P (bound w e D.R.r k) e (by omega) he hb h3
      hd hLH hz (hL _) hSt (hFit _)
    have hg := fun j => hG j hl M (R₀ + t) (R₀ + k) d A L z P P' (bound w e D.R.r k + 1) (by omega) (hs.trans hb) h3 hz
      (hL j) hSt' hE
    refine ⟨P', fun a => (hE (.inl a)).trans (hP a), hSt', fun j => NFit_mono (by omega) ((hg j).2 (hFit j)), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact NF_mono (by omega) ((hg j).1 (hNF j hj))
    · obtain rfl : j = ⟨k, hk⟩ := Fin.ext hj
      exact NF_mono (Nat.le_succ _) hN

theorem thmC_of_parts : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ i, StepAB X i) → (∀ i, ChooseH bkP i) → (∀ i s, GalHyp bkP i s → Start bkP i s ∧ Grow bkP i s ∧ Step bkP i s) → ThmC bkP := by
  intro D N X bkP hAB hCh hP i hl T hT
  obtain ⟨R₀, hR⟩ := hCh i T hT
  have : Finite (X.Sig i) := (X.finSig i).finite
  obtain ⟨t, f, -, hf⟩ := (Set.toFinite T).fin_param
  have hfT : ∀ j, f j ∈ T := fun j => hf ▸ Set.mem_range_self j
  have hp : (X.l i).Prime := (X.lPrime i).out
  have hl0 : (X.l i : X.O0 i) ≠ 0 := fun h0 => by
    have h1 : (X.emb0 i) (X.l i : D.LL0) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap (X.O0 i) (FractionRing (X.O0 i))), h0, map_zero]
    exact hp.ne_zero (Nat.cast_eq_zero.1 ((map_eq_zero _).1 h1))
  obtain ⟨e, he⟩ : ∃ e : ℕ, IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e := by
    obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.1 (mt IsDiscreteValuationRing.addVal_eq_top_iff.1 (pow_ne_zero (nu X i) hl0))
    exact ⟨e, he.symm⟩
  refine ⟨R₀ + t, bound (4 * D.R.r * R₀) e D.R.r t, bound (4 * D.R.r * R₀) e D.R.r t + nu X i + 3,
    fun M hM H S d hd z hz H' ho hn A => ?_⟩
  have hw : 4 * D.R.r * R₀ ≤ bound (4 * D.R.r * R₀) e D.R.r t := bound_mono (4 * D.R.r * R₀) e D.R.r (Nat.zero_le t)
  have hlt : 4 * D.R.r * R₀ + 2 < X.l i ^ M := lt_of_le_of_lt (by omega) (Nat.lt_pow_self (n := M) hp.one_lt)
  have hle : bound (4 * D.R.r * R₀) e D.R.r t ≤ X.l i ^ (M - nu X i - 1) :=
    le_trans (by omega) (Nat.lt_pow_self (n := M - nu X i - 1) hp.one_lt).le
  obtain ⟨L, hLo, hLn, hLH, hLs, hLζ, hLi⟩ := GlobalTheory.ResSel.SmallSub.exists_small D N X bkP i T hT z hz M H hd.1 hd.2.1 hd.2.2.1
  obtain ⟨h, U, hh, hUo, hUn, hUL, hco⟩ := hR z hz L hLo hLn hLs
  have hh' : ∀ a, Fin.append h (fun _ : Fin t => (1 : GE N)) a ∈ L := fun a => by
    refine Fin.addCases (fun a => ?_) (fun a => ?_) a
    · rw [Fin.append_left]; exact hh a
    · rw [Fin.append_right]; exact L.one_mem
  obtain ⟨P, hAux, hSt, hIne, hFr⟩ := hAB i M (by omega) H S d hd z hz (U ⊓ H') (hUo.inter ho) inferInstance A (R₀ + t)
    (Fin.append h fun _ => 1) (fun a => ⟨hLH (hh' a), hLζ _ (hh' a)⟩)
  choose φ g hφ hg using hFr
  have hUL' : U ⊓ H' ≤ L := inf_le_left.trans hUL
  have hφL : ∀ a, φ a ∈ L := fun a => by
    have h1 := L.mul_mem (hUL' (hg a)) (hh' a)
    rw [inv_mul_cancel_right] at h1
    simpa [mul_assoc] using hLn.conj_mem _ h1 (g a)⁻¹
  have hcj : ∀ a, IsCj X (φ a) (GlobalTheory.TwistDet.cConj X (φ a)) := fun a x => rfl
  have hinj : Function.Injective (Sum.map id (Fin.castAdd t) : Fin (R₀ + t) ⊕ Fin R₀ → Fin (R₀ + t) ⊕ Fin (R₀ + t)) :=
    Function.injective_id.sumMap (Fin.castAdd_injective _ _)
  have h₀ : PiLocalization₂ i M d A L z (fun q : Fin (R₀ + t) ⊕ Fin R₀ => P (Sum.map id (Fin.castAdd t) q)) := by
    refine ⟨⟨fun q => hAux.1 _, fun q q' hq => hinj (hAux.2.1 _ _ hq), fun q => hAux.2.2 _⟩,
      fun a => ⟨fun v hv B hB => (hIne _ v hv B hB).trans hUL', fun σ hσ => (hSt.1 a σ hσ).imp fun _ hg => hUL' hg⟩,
      fun a => ⟨dec_le_of_frob_mem (N.plOm.2 _) (hφ (Fin.castAdd t a)) hLo
        ((hIne _ _ (Or.inl rfl) _ (N.plOm.2 _)).trans hUL') (hφL _), fun b σ hσ => ?_⟩⟩
    have := hSt.2 (Fin.castAdd t a) b σ hσ
    simpa [Fin.ext_iff] using this
  have hc := hco (fun a => φ (Fin.castAdd t a)) (fun a => GlobalTheory.TwistDet.cConj X (φ (Fin.castAdd t a)))
    (fun a => ⟨hcj _, g (Fin.castAdd t a), by simpa using (hg (Fin.castAdd t a)).1⟩)
  rw [if_neg hl.ne'] at hc
  obtain ⟨P', hP', hSt', -, hNF⟩ := induct hl f (fun j => (hP i _ (hT _ (hfT j))).2.1) (fun j => (hP i _ (hT _ (hfT j))).2.2)
    he hle (by omega) hd hLH hz (fun j => ⟨hLs _ (hfT j), hLζ, hLi _ (hfT j)⟩) _ h₀
    (fun j => (hP i _ (hT _ (hfT j))).1 M (R₀ + t) R₀ d A L z _ _ _ (Nat.le_add_right _ _) hlt hz (hLs _ (hfT j)) h₀
      (fun a => ⟨hφ _, hcj _⟩) (hc _ (hfT j))) t le_rfl
  refine ⟨P', hSt'.1, ⟨fun a σ hσ => ?_, fun a b σ hσ => ?_⟩, fun s hs Q hQ a Φ hΦ F hF => ?_⟩
  · rw [hP' a] at hσ
    exact (hSt.1 a σ hσ).imp fun _ hg => hg.2
  · simpa [Fin.ext_iff] using (hSt'.2.2 a).2 b σ hσ
  · obtain ⟨j, rfl⟩ : s ∈ Set.range f := hf ▸ hs
    obtain ⟨m, hm, hu⟩ := hNF j j.2 Q hQ a Φ hΦ F hF
    exact ⟨m, Nat.lt_succ_iff.1 hm, addVal_le_of_notMem hu⟩

end GlobalTheory.StepTwo.TwoBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundModTwoUniformizerAtTwoOfChebotarev
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo

namespace GlobalTheory.StepTwo.Dyadic

theorem bound_mod_two_of_hypothesis : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ThmC bkP := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP
  have hS := GlobalTheory.SelFun.oneMatrix_of_galoisCohomology h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP
  have hgw := GlobalTheory.T.residual_selmer_finrank_eq_dual h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP
  have hk4 := GlobalTheory.ScalarFrob.firstHalf h5 h6 h7 h4 D N X bkP
  refine GlobalTheory.StepTwo.TwoBound.thmC_of_parts D N X bkP (GlobalTheory.ChosenPrimes.stepAB h1 D N X) (fun i => GlobalTheory.ChooseForms.chooseH h8 D N X bkP i fun s hs =>
    ⟨GlobalTheory.ResSel.SpanOddPf.spanOdd D N X bkP i s hs, GlobalTheory.ResSel.AltSpan.spanTwo_of_galHyp D N X bkP i s hs, hgw i s hs⟩) fun i s hs => ⟨?_, ?_, ?_⟩
  · exact GlobalTheory.StepTwo.StartInd.start_of_resBound D N X bkP i s hs (GlobalTheory.ScalarFrob.firstPlace h5 h6 h7 D N X bkP i s hs) (GlobalTheory.ResOrder.resBound h4 D N X bkP i s hs (hk4 i s hs)
      (GlobalTheory.ResRecip.reciprocity h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP i s hs (hk4 i s hs)) (hgw i s hs))
  · exact GlobalTheory.Growth.grow h4 D N X bkP hS i s hs
  · exact GlobalTheory.NewPrime.step h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 D N X bkP hS i s hs

end GlobalTheory.StepTwo.Dyadic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundModTwoUniformizerAtTwoOfChebotarevStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundModTwoUniformizerAtTwo_of_chebotarev : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ThmC bkP := by
  first | exact @GlobalTheory.StepTwo.Dyadic.bound_mod_two_of_hypothesis | exact GlobalTheory.StepTwo.Dyadic.bound_mod_two_of_hypothesis | (intros; apply GlobalTheory.StepTwo.Dyadic.bound_mod_two_of_hypothesis <;> assumption)
end
