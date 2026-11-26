module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnipotentIntegralVariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLeviParabolicFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvarianceOfConstantFourierCoefficient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliPolynomialCoefficientsIdeal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsFinsetSeparating
private theorem UpperTheory.Reformulated.B.Qp2.aux {X : Type} (n : ℕ) :
    ∀ (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥V], Module.finrank ℂ V = n →
    ∃ (T : Finset X), ∀ v ∈ V, (∀ x ∈ T, v x = (0 : ℂ)) → v = (0 : X → ℂ) := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ hn
    by_cases hV : ∀ v ∈ V, v = 0
    · exact ⟨∅, fun v hv _ => hV v hv⟩
    · obtain ⟨w, hw⟩ := not_forall.mp hV
      obtain ⟨hwV, hw0⟩ := Classical.not_imp.mp hw
      obtain ⟨x, hx⟩ := Function.ne_iff.mp hw0
      let U : Submodule ℂ (X → ℂ) := V ⊓ LinearMap.ker (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ)
      have hle : U ≤ V := inf_le_left
      have hlt : U < V := by
        refine lt_of_le_of_ne hle ?_
        intro h
        have hwU : w ∈ U := h ▸ hwV
        exact hx (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hwU).2)
      haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hle
      have hr : Module.finrank ℂ U < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨T, hT⟩ := ih _ hr U rfl
      refine ⟨insert x T, fun v hv h => hT v ?_ fun y hy => h y (Finset.mem_insert_of_mem hy)⟩
      exact Submodule.mem_inf.mpr ⟨hv, LinearMap.mem_ker.mpr (h x (Finset.mem_insert_self x T))⟩

theorem UpperTheory.Reformulated.B.Qp2.exists_finset_separating :
    ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥V],
    ∃ (T : Finset X), ∀ v ∈ V, (∀ x ∈ T, v x = (0 : ℂ)) → v = (0 : X → ℂ) := by
  intro X V _
  exact UpperTheory.Reformulated.B.Qp2.aux _ V rfl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteCenterMonicAnnihilator
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteCenterMonicAnnihilator
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin

theorem cofin_monic_on_killed : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ)
    (J : Set (Module.End ℂ (Sm E n))), Cofin J → ∀ z ∈ Zalg E n, ∃ p : Polynomial ℂ, p.Monic ∧
      ∀ φ : Sm E n, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 :=
  fun E _ _ _ n J hJ z hz => GlobalTheory.CompanionTheory.Affgl.minpoly_on_killed E n J hJ z hz

end GlobalTheory.CompanionTheory.CTFin
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteCenterMonicAnnihilatorStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofinite_center_monic_annihilator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (J : Set (Module.End ℂ (Sm E n))), Cofin J → ∀ z ∈ Zalg E n, ∃ p : Polynomial ℂ, p.Monic ∧ ∀ φ : Sm E n, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed | exact GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed | (intros; apply GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnseenStatementBStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_unseen_statement_b : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E (r + s))), Cofin J → ∀ J₂ : Set (Module.End ℂ (Sm E s)), Cofin J₂ → (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) → ∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ z ∈ J₂, z G = 0) → ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)), ∃ (L₂ : Subgroup (GL (Fin s) (Af E))) (ρ₂ : Representation ℂ (Kinf E s) W), IsOpen (L₂ : Set (GL (Fin s) (Af E))) ∧ GlobalTheory.Published.AutFin.IsContRep ρ₂ ∧ ∀ F ∈ goodCT L ρ J, ∀ m₁ : GA E r, ∃ G ∈ genSpace L₂ ρ₂ J₂, ∀ m₂ : GA E s, G.1 m₂ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice2.slice2 | exact GlobalTheory.CompanionTheory.CTFin.Slice2.slice2 | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice2.slice2 <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliUnseenStatementStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_restrict_levi : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (q : Polynomial ℂ) (F : Sm E (r + s)), (∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ m, (Polynomial.aeval (cap (a := r) τ u) q G).1 m = (Polynomial.aeval (capR r s τ u) q F).1 (lev (Ad E) r s (m, 1))) ∧ (∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ m, (Polynomial.aeval (cap (a := s) τ u) q G).1 m = (Polynomial.aeval (capS r s τ u) q F).1 (lev (Ad E) r s (1, m))) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.capelli_restrict | exact GlobalTheory.CompanionTheory.CTFin.capelli_restrict | (intros; apply GlobalTheory.CompanionTheory.CTFin.capelli_restrict <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnseenStatementAStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_unseen_statement_a : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∃ T : Finset (GL (Fin (r + s)) (Af E)), ∀ g : GA E (r + s), ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (t : GL (Fin (r + s)) (Af E)) (k : Kinf E (r + s)) (l : GL (Fin (r + s)) (Af E)), t ∈ T ∧ l ∈ L ∧ g = unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) l := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets | exact GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets | (intros; apply GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparatelyFiniteDimFunctionsFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparatelyFiniteDimFunctionsFinite
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin.ProdTrick

theorem exists_finset_separating {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V] :
    ∃ T : Finset X, ∀ v ∈ V, (∀ x ∈ T, v x = 0) → v = 0 :=
  _root_.UpperTheory.Reformulated.B.Qp2.exists_finset_separating V

theorem exists_finiteDimensional_of_slices :
    ∀ (X Y : Type) (V₁ : Submodule ℂ (X → ℂ)) (V₂ : Submodule ℂ (Y → ℂ)),
      FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ →
      ∃ 𝓥 : Submodule ℂ (X × Y → ℂ), FiniteDimensional ℂ 𝓥 ∧
        ∀ f : X × Y → ℂ, (∀ y, (fun x => f (x, y)) ∈ V₁) → (∀ x, (fun y => f (x, y)) ∈ V₂) →
          f ∈ 𝓥 := by
  intro X Y V₁ V₂ h₁ h₂
  obtain ⟨T, hT⟩ := exists_finset_separating V₁
  let S : Submodule ℂ (X × Y → ℂ) :=
    { carrier := {f | (∀ y, (fun x => f (x, y)) ∈ V₁) ∧ (∀ x, (fun y => f (x, y)) ∈ V₂)}
      add_mem' := fun {a b} ha hb =>
        ⟨fun y => V₁.add_mem (ha.1 y) (hb.1 y), fun x => V₂.add_mem (ha.2 x) (hb.2 x)⟩
      zero_mem' := ⟨fun _ => V₁.zero_mem, fun _ => V₂.zero_mem⟩
      smul_mem' := fun c a ha =>
        ⟨fun y => V₁.smul_mem c (ha.1 y), fun x => V₂.smul_mem c (ha.2 x)⟩ }
  let L : S →ₗ[ℂ] (T → V₂) :=
    { toFun := fun f t => ⟨fun y => (f : X × Y → ℂ) ((t : X), y), f.2.2 t⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply Subtype.ext
    funext ⟨x, y⟩
    have hy := hT _ (f.2.1 y) (fun t ht => by
      have := congrArg Subtype.val (congrFun hf ⟨t, ht⟩)
      exact congrFun this y)
    exact congrFun hy x
  have : FiniteDimensional ℂ S := FiniteDimensional.of_injective L hL
  exact ⟨S, this, fun f h1 h2 => ⟨h1, h2⟩⟩

end GlobalTheory.CompanionTheory.CTFin.ProdTrick
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparatelyFiniteDimFunctionsFiniteStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separately_finite_dim_functions_finite : ∀ (X Y : Type) (V₁ : Submodule ℂ (X → ℂ)) (V₂ : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ → ∃ 𝓥 : Submodule ℂ (X × Y → ℂ), FiniteDimensional ℂ 𝓥 ∧ ∀ f : X × Y → ℂ, (∀ y, (fun x => f (x, y)) ∈ V₁) → (∀ x, (fun y => f (x, y)) ∈ V₂) → f ∈ 𝓥 := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.ProdTrick.exists_finiteDimensional_of_slices | exact GlobalTheory.CompanionTheory.CTFin.ProdTrick.exists_finiteDimensional_of_slices | (intros; apply GlobalTheory.CompanionTheory.CTFin.ProdTrick.exists_finiteDimensional_of_slices <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermKFiniteCoefficient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermKFiniteCoefficient
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.KType

theorem exists_finset_sep {K : Type} (S : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ S] :
    ∃ T : Finset K, ∀ s ∈ S, (∀ t ∈ T, s t = 0) → s = 0 := by
  classical
  let f : Finset K → Submodule ℂ S := fun T =>
    ⨅ t ∈ T, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) t).comp S.subtype)
  obtain ⟨T, -, hT⟩ := (measure fun T => Module.finrank ℂ (f T)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨T, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
  have hmem : ∀ T' : Finset K, ∀ u : S, u ∈ f T' ↔ ∀ t ∈ T', (u : K → ℂ) t = 0 := fun T' u => by
    simp [f, Submodule.mem_iInf]
  have hle : f (insert t T) ≤ f T := fun u hu =>
    (hmem T u).2 fun t' ht' => (hmem _ u).1 hu t' (Finset.mem_insert_of_mem ht')
  have hlt : f (insert t T) < f T := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 : (⟨s, hs⟩ : S) ∈ f T := (hmem T _).2 h0
    rw [← heq] at h1
    exact ht ((hmem _ _).1 h1 t (Finset.mem_insert_self t T))
  exact hT (insert t T) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem integral_mem {K K' : Type} [MeasurableSpace K'] (μ : Measure K') (S : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ S] (F : K' → K → ℂ) (hF : ∀ k', F k' ∈ S)
    (hi : ∀ k, Integrable (fun k' => F k' k) μ) : (fun k => ∫ k', F k' k ∂μ) ∈ S := by
  obtain ⟨T, hT⟩ := exists_finset_sep S
  let R : S →ₗ[ℂ] (T → ℂ) := LinearMap.pi fun t : T => (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) (t : K)).comp S.subtype
  have hker : LinearMap.ker R = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun u hu => Subtype.ext ?_
    refine hT u u.2 fun t ht => ?_
    have := congrFun hu ⟨t, ht⟩
    simpa [R] using this
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hker
  let b := Pi.basisFun ℂ T
  have hexp : ∀ s ∈ S, s = ∑ t : T, s t • ((L (b t) : S) : K → ℂ) := by
    intro s hs
    have h1 : (⟨s, hs⟩ : S) = L (R ⟨s, hs⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨s, hs⟩ = ∑ t : T, s t • b t := by
      conv_lhs => rw [← b.sum_repr (R ⟨s, hs⟩)]
      simp [R, b]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum] at h1
    have h3 := congrArg (fun u : S => (u : K → ℂ)) h1
    simpa [Submodule.coe_sum, map_smul] using h3
  have : (fun k => ∫ k', F k' k ∂μ) = ∑ t : T, (∫ k', F k' t ∂μ) • ((L (b t) : S) : K → ℂ) := by
    funext k
    have hk : ∀ k', F k' k = ∑ t : T, F k' t * ((L (b t) : S) : K → ℂ) k := fun k' => by
      conv_lhs => rw [hexp (F k') (hF k')]
      simp [Finset.sum_apply]
    simp_rw [hk]
    rw [integral_finsetSum (f := fun (t : T) k' => F k' t * ((L (b t) : S) : K → ℂ) k) Finset.univ
      fun t _ => (hi t).mul_const _]
    simp [Finset.sum_apply, integral_mul_const]
  rw [this]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (L (b t)).2

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let T : Module.Dual ℂ (Module.End ℂ W) →ₗ[ℂ] (K → ℂ) :=
    LinearMap.pi fun k => LinearMap.applyₗ (ρ k)
  have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ LinearMap.range T := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨ℓ.comp (LinearMap.applyₗ w), rfl⟩
  exact Submodule.finiteDimensional_of_le this

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem eventually_eq_chart (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a)
    (x₀ : BlockIx a r → Ad E) :
    ∀ᶠ x in 𝓝 x₀, φ.1 (unip x * g) =
      chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val) := by
  have hc : Continuous (fun x : BlockIx a r → Ad E => (JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x) :=
    continuous_const.mul (JointCont.continuous_finPart g)
  have h1 : finRep E a ((JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x₀) φ = φ := by rw [inv_mul_cancel]; simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hlev.mem_nhds h1)] with x hx
  have hx' : finRep E a ((JointCont.finPart g x₀)⁻¹ * JointCont.finPart g x) φ = φ := hx
  rw [chart_val, JointCont.unip_mul_eq, ← mul_inv_cancel_left (JointCont.finPart g x₀) (JointCont.finPart g x),
    map_mul, mul_assoc, ← infGL_comm, ← mul_assoc]
  exact congrArg (fun ψ : Sm E a => ψ.1 (finGL E a (JointCont.finPart g x₀) * infGL E a (JointCont.infPart g x))) hx'

theorem continuous_unip_mul (φ : Sm E a) (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    Continuous fun x : BlockIx a r → Ad E => φ.1 (unip x * g) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hf₀ : ContDiffOn ℝ ∞ (chart φ.1 (finGL E a (JointCont.finPart g x₀))) (invSet E a) := φ.2 _
  have hA : ContinuousAt (fun x : BlockIx a r → Ad E =>
      chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val)) x₀ :=
    ContinuousAt.comp (g := chart φ.1 (finGL E a (JointCont.finPart g x₀)))
      (hf₀.continuousOn.continuousAt (isOpen_invSet.mem_nhds (val_mem_invSet _)))
      (JointCont.continuous_infPart g).continuousAt
  have hE : (fun x : BlockIx a r → Ad E => φ.1 (unip x * g)) =ᶠ[𝓝 x₀]
      fun x => chart φ.1 (finGL E a (JointCont.finPart g x₀)) (toL (JointCont.infPart g x).val) :=
    eventually_eq_chart φ hlev g x₀
  exact hA.congr hE.symm

theorem exists_bound_unip_mul (φ : Sm E a) (hleft : ∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g)
    (hlev : IsOpen {k | finRep E a k φ = φ}) (g : GA E a) :
    ∃ C, ∀ x : BlockIx a r → Ad E, ‖φ.1 (unip x * g)‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hCm : IsCompact (Set.univ.pi fun _ : BlockIx a r => K) := isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hCm.exists_bound_of_continuousOn (continuous_unip_mul (r := r) φ hlev g).continuousOn
  refine ⟨C, fun x => ?_⟩
  choose q hq using fun p => hcov (x p)
  obtain ⟨x', hx'm, rfl⟩ : ∃ x' ∈ Set.univ.pi fun _ : BlockIx a r => K,
      x = (fun p => algebraMap E (Ad E) (q p)) + x' :=
    ⟨fun p => x p - algebraMap E (Ad E) (q p), fun p _ => hq p, by funext p; simp⟩
  rw [unip_add, unip_algebraMap, mul_assoc, hleft]
  exact hC x' hx'm

theorem ct_mem_coeffSpan : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  intro E _ _ _ a r φ hleft hlev W _ _ _ ρ hρ _ _ μ 𝓕 hμ hF g
  haveI := hμ
  haveI := finiteDimensional_coeffSpan ρ
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  refine integral_mem (μ.restrict 𝓕) (GlobalTheory.Published.AutFin.coeffSpan ρ)
    (fun x k => φ.1 (unip x * (g * infGL E a (Unitary.toUnits k)))) (fun x => ?_) (fun k => ?_)
  · have e : ∀ k : Kinf E a, (cptRep E a k φ).1 (unip x * g) = φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) :=
      fun k => by rw [← mul_assoc]; rfl
    have := hρ (unip x * g)
    simp only [e] at this
    exact this
  · obtain ⟨C, hC⟩ := exists_bound_unip_mul (r := r) φ hleft hlev (g * infGL E a (Unitary.toUnits k))
    exact Integrable.of_bound (continuous_unip_mul φ hlev _).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)

end GlobalTheory.CompanionTheory.CTFin.KType

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermKFiniteCoefficientStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_k_finite_coefficient : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, (fun k : Kinf E a => ∫ x in 𝓕, φ.1 (unip x * (g * infGL E a (Unitary.toUnits k))) ∂μ) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.KType.ct_mem_coeffSpan | exact GlobalTheory.CompanionTheory.CTFin.KType.ct_mem_coeffSpan | (intros; apply GlobalTheory.CompanionTheory.CTFin.KType.ct_mem_coeffSpan <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CTFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

def leftN (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) : Submodule ℂ (Sm E (r + s)) where
  carrier := {F | ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g}
  add_mem' := fun {F G} hF hG x g => by
    change F.1 _ + G.1 _ = F.1 _ + G.1 _
    rw [hF, hG]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c F hF x g => by
    change c • F.1 _ = c • F.1 _
    rw [hF]

def vanM (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) : Submodule ℂ (Sm E (r + s)) where
  carrier := {F | ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0}
  add_mem' := fun {F G} hF hG m => by
    change F.1 _ + G.1 _ = 0
    rw [hF, hG, add_zero]
  zero_mem' := fun _ => rfl
  smul_mem' := fun c F hF m => by
    change c • F.1 _ = 0
    rw [hF, smul_zero]

theorem aeval_mem_Zalg {n : ℕ} {x : Module.End ℂ (Sm E n)} (hx : x ∈ Zalg E n) (q : Polynomial ℂ) :
    Polynomial.aeval x q ∈ Zalg E n := by
  rw [← Polynomial.aeval_subalgebra_coe q (Zalg E n) ⟨x, hx⟩]
  exact (Polynomial.aeval (⟨x, hx⟩ : Zalg E n) q).2

theorem cap_mem_Zalg {n : ℕ} (τ : E →+* ℂ) (u : ℂ) : cap (a := n) τ u ∈ Zalg E n :=
  Algebra.subset_adjoin ⟨τ, u, rfl⟩

theorem centre (J : Set (Module.End ℂ (Sm E (r + s)))) (hJ : Cofin J) :
    ∃ (J₁ : Set (Module.End ℂ (Sm E r))) (J₂ : Set (Module.End ℂ (Sm E s))), Cofin J₁ ∧ Cofin J₂ ∧
    (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) →
      ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0) ∧
    (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) →
      ∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ z ∈ J₂, z G = 0) := by
  let W₀ : Set (Sm E (r + s)) := {F | F ∈ leftN E r s ∧ ∀ z ∈ J, z F = 0}
  have key : ∀ τ : E →+* ℂ, (∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (capR r s τ u) q F ∈ vanM E r s) ∧
      ∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (capS r s τ u) q F ∈ vanM E r s := by
    intro τ
    obtain ⟨a, a1, a2, a3⟩ := GlobalTheory.T.quantum_determinant_polynomial_coefficients (Module.End ℂ (Sm E (r + s))) r
      (fun i j : Fin r => Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j)) (((r : ℂ) - 1) / 2)
    obtain ⟨b, b1, b2, b3⟩ := GlobalTheory.T.quantum_determinant_polynomial_coefficients (Module.End ℂ (Sm E (r + s))) s
      (fun i j : Fin s => Eop (a := r + s) τ (Fin.natAdd r i) (Fin.natAdd r j)) (((s : ℂ) - 1) / 2)
    refine GlobalTheory.T.capelli_polynomial_coefficients_ideal (Sm E (r + s)) (fun u => cap (a := r + s) τ u) (capR r s τ) (capS r s τ) (leftN E r s) (vanM E r s) W₀
      (-(s : ℂ) / 2) ((r : ℂ) / 2) r s a b (fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).1)
      (fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).2.1) (fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).2.2)
      (fun u F hF => (GlobalTheory.T.capelli_constant_term_vanishing E r s τ u F).2 hF) (fun u F hF => ((GlobalTheory.T.capelli_constant_term_vanishing E r s τ u F).1 hF).1)
      (fun u F hF => ((GlobalTheory.T.capelli_constant_term_vanishing E r s τ u F).1 hF).2) ?_ a1 a2 a3 b1 b2 b3 (fun F hF => hF.1) ?_
    · intro u F hF m
      have := GlobalTheory.T.capelli_levi_factorization_sum E r s τ u F hF m
      change (cap (a := r + s) τ u F).1 _ - (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u + -(s : ℂ) / 2) F)).1 _ = 0
      rw [this, sub_eq_zero]
      have e : u + -(s : ℂ) / 2 = u - (s : ℂ) / 2 := by ring
      rw [e]
    · intro u
      obtain ⟨p, hp, h⟩ := GlobalTheory.T.cofinite_center_monic_annihilator E (r + s) J hJ _ (cap_mem_Zalg τ u)
      exact ⟨p, hp, fun F hF => h F hF.2⟩
  choose q₁ m₁ h₁ using fun τ => (key τ).1
  choose q₂ m₂ h₂ using fun τ => (key τ).2
  refine ⟨{z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := r) τ u) (q₁ τ u)},
    {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := s) τ u) (q₂ τ u)}, ?_, ?_, ?_, ?_⟩
  · refine GlobalTheory.T.cofinite_of_capelli_monic E r _ ?_ fun τ u => ⟨q₁ τ u, m₁ τ u, τ, u, rfl⟩
    rintro _ ⟨τ, u, rfl⟩
    exact aeval_mem_Zalg (cap_mem_Zalg τ u) _
  · refine GlobalTheory.T.cofinite_of_capelli_monic E s _ ?_ fun τ u => ⟨q₂ τ u, m₂ τ u, τ, u, rfl⟩
    rintro _ ⟨τ, u, rfl⟩
    exact aeval_mem_Zalg (cap_mem_Zalg τ u) _
  · rintro F hF hz G hG _ ⟨τ, u, rfl⟩
    refine Subtype.ext (funext fun m => ?_)
    rw [(GlobalTheory.T.capelli_restrict_levi E r s τ u (q₁ τ u) F).1 G hG m]
    exact h₁ τ u F ⟨hF, hz⟩ (m, 1)
  · rintro F hF hz G hG _ ⟨τ, u, rfl⟩
    refine Subtype.ext (funext fun m => ?_)
    rw [(GlobalTheory.T.capelli_restrict_levi E r s τ u (q₂ τ u) F).2 G hG m]
    exact h₂ τ u F ⟨hF, hz⟩ (1, m)

theorem exists_mem_goodCT (L : Subgroup (GL (Fin (r + s)) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W) (J : Set (Module.End ℂ (Sm E (r + s))))
    (hJ : Cofin J) (φ : Sm E (r + s)) (hφ : φ ∈ genSpace L ρ J)
    [MeasurableSpace (BlockIx (r + s) r → Ad E)] [BorelSpace (BlockIx (r + s) r → Ad E)]
    (μ : Measure (BlockIx (r + s) r → Ad E)) (𝓕 : Set (BlockIx (r + s) r → Ad E)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratN E (r + s) r) 𝓕 μ) :
    ∃ F ∈ goodCT L ρ J, ∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  obtain ⟨hA, hLf, hK, hZ⟩ := hφ
  obtain ⟨F, hF1, hF2⟩ := GlobalTheory.T.constant_term_unipotent_integral_variant E (r + s) r φ hA.left hA.level μ 𝓕 hμ h𝓕
  have hlie : ∀ φ' F' : Sm E (r + s), (∀ (γ : GL (Fin (r + s)) E) (g : GA E (r + s)), φ'.1 (ratGL E (r + s) γ * g) = φ'.1 g) →
      IsOpen {k | finRep E (r + s) k φ' = φ'} → (∀ g, F'.1 g = ∫ x in 𝓕, φ'.1 (unip x * g) ∂μ) →
      ∀ (X : Lie E (r + s)) (g : GA E (r + s)), (lie E (r + s) X F').1 g = ∫ x in 𝓕, (lie E (r + s) X φ').1 (unip x * g) ∂μ := by
    intro φ' F' h1 h2 h3 X g
    obtain ⟨F'', e1, e2⟩ := GlobalTheory.T.constant_term_unipotent_integral_variant E (r + s) r φ' h1 h2 μ 𝓕 hμ h𝓕
    have : F' = F'' := Subtype.ext (funext fun g => (h3 g).trans (e1 g).symm)
    rw [this]
    exact e2 X g
  refine ⟨F, ⟨fun x g => ?_, fun γ g => ?_, fun k hk => ?_, fun g => ?_, fun g => ?_, fun z hz => ?_⟩, hF1⟩
  · rw [hF1, hF1]
    exact GlobalTheory.T.constant_term_translate_formula E (r + s) r φ hA.left hA.level μ 𝓕 hμ h𝓕 x g
  · rw [hF1, hF1]
    exact GlobalTheory.T.constant_term_levi_parabolic_formula E r s φ hA.left hA.level μ 𝓕 hμ h𝓕 γ g
  · refine Subtype.ext (funext fun g => ?_)
    change F.1 (g * finGL E (r + s) k) = F.1 g
    rw [hF1, hF1]
    refine congrArg (fun f : (BlockIx (r + s) r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ) (funext fun x => ?_)
    have := congrFun (congrArg Subtype.val (hLf k hk)) (unip x * g)
    rw [← this]
    change _ = φ.1 (unip x * g * finGL E (r + s) k)
    rw [mul_assoc]
  · have h := GlobalTheory.T.constant_term_k_finite_coefficient E (r + s) r φ hA.left hA.level W ρ hK μ 𝓕 hμ h𝓕 g
    convert h using 1
    funext k
    exact hF1 _
  · obtain ⟨C, N, h⟩ := GlobalTheory.T.constant_term_moderate_growth_alt E (r + s) r φ hA μ 𝓕 hμ h𝓕 g
    exact ⟨C, N, fun y => by rw [hF1]; exact h y⟩
  · refine Subtype.ext (funext fun g => ?_)
    rw [GlobalTheory.T.constant_term_automorphic_criterion E (r + s) r μ 𝓕 hμ h𝓕 hlie φ F hA.left hA.level hF1 z (hJ.1 hz) g, hZ z hz]
    simp

theorem finiteDimensional_goodCT (h₁ : GenFin E r) (h₂ : GenFin E s) (L : Subgroup (GL (Fin (r + s)) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E)))) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Kinf E (r + s)) W) (hρ : GlobalTheory.Published.AutFin.IsContRep ρ)
    (J : Set (Module.End ℂ (Sm E (r + s)))) (hJ : Cofin J) : FiniteDimensional ℂ (goodCT L ρ J) := by
  obtain ⟨J₁, J₂, c₁, c₂, k₁, k₂⟩ := centre J hJ
  obtain ⟨T, hT⟩ := GlobalTheory.T.constant_term_unseen_statement_a E r s L hL
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_dim_coefficients_finite_determining (Kinf E (r + s)) W ρ
  have key : ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)),
      ∃ 𝓥 : Submodule ℂ (GA E r × GA E s → ℂ), FiniteDimensional ℂ 𝓥 ∧ ∀ F ∈ goodCT L ρ J,
        (fun m => F.1 (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ))) ∈ 𝓥 := by
    intro t κ
    obtain ⟨L₁, ρ₁, o₁, q₁, e₁⟩ := GlobalTheory.T.constant_term_cofinite_ideal_transfer E r s L hL W ρ hρ J hJ J₁ c₁ k₁ t κ
    obtain ⟨L₂, ρ₂, o₂, q₂, e₂⟩ := GlobalTheory.T.constant_term_unseen_statement_b E r s L hL W ρ hρ J hJ J₂ c₂ k₂ t κ
    have f₁ := h₁ L₁ o₁ W ρ₁ q₁ J₁ c₁
    have f₂ := h₂ L₂ o₂ W ρ₂ q₂ J₂ c₂
    obtain ⟨𝓥, fd, hV⟩ := GlobalTheory.T.separately_finite_dim_functions_finite (GA E r) (GA E s)
      ((Submodule.span ℂ (genSpace L₁ ρ₁ J₁)).map (Sm E r).subtype)
      ((Submodule.span ℂ (genSpace L₂ ρ₂ J₂)).map (Sm E s).subtype) inferInstance inferInstance
    refine ⟨𝓥, fd, fun F hF => hV _ (fun m₂ => ?_) (fun m₁ => ?_)⟩
    · obtain ⟨G, hG, e⟩ := e₁ F hF m₂
      exact ⟨G, Submodule.subset_span hG, funext e⟩
    · obtain ⟨G, hG, e⟩ := e₂ F hF m₁
      exact ⟨G, Submodule.subset_span hG, funext e⟩
  choose 𝓥 fd hV using key
  let Ψ : goodCT L ρ J →ₗ[ℂ] ∀ p : T × S, 𝓥 p.1.1 p.2.1 :=
    { toFun := fun F p => ⟨_, hV p.1.1 p.2.1 F.1 F.2⟩
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  have hΨ : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun F hF => ?_
    obtain ⟨F, a1, a2, a3, a4, a5, a6⟩ := F
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    obtain ⟨x, m, t, k, l, ht, hl, rfl⟩ := hT g
    have e0 : ∀ κ ∈ S, F.1 (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) = 0 := by
      intro κ hκ
      have := congrFun (congrArg Subtype.val (congrFun hF (⟨t, ht⟩, ⟨κ, hκ⟩))) m
      exact this
    have hc := hS _ (a4 (lev (Ad E) r s m * finGL E (r + s) t)) e0
    have h1 := congrFun hc k
    have h2 := congrFun (congrArg Subtype.val (a3 l hl))
      (unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k))
    change F.1 (_ * finGL E (r + s) l) = _ at h2
    refine h2.trans ?_
    have e1 : unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) =
        unip x * (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k)) := by
      simp only [mul_assoc]
    rw [e1, a1]
    exact h1
  exact FiniteDimensional.of_injective Ψ hΨ

theorem ctFin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) →
    ∀ r, 0 < r → r < a → CTFin E a r := by
  intro E _ _ _ a hG r h0 hr
  obtain ⟨s, rfl⟩ : ∃ s, a = r + s := ⟨a - r, by omega⟩
  intro L hL W _ _ _ ρ hρ J hJ
  have hfd := finiteDimensional_goodCT (hG r hr) (hG s (by omega)) L hL ρ hρ J hJ
  refine ⟨(goodCT L ρ J).map (Sm E (r + s)).subtype, inferInstance, ?_⟩
  intro φ hφ _ _ μ 𝓕 hμ h𝓕
  obtain ⟨F, hF, e⟩ := exists_mem_goodCT L ρ J hJ φ hφ μ 𝓕 hμ h𝓕
  exact ⟨F, hF, funext e⟩

end GlobalTheory.CompanionTheory.CTFin

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmallerStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_finite_of_smaller : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) → ∀ r, 0 < r → r < a → CTFin E a r := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.ctFin | exact GlobalTheory.CompanionTheory.CTFin.ctFin | (intros; apply GlobalTheory.CompanionTheory.CTFin.ctFin <;> assumption)
end
