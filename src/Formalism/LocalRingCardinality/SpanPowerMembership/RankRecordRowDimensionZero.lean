module

public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos
public import Formalism.LocalRingCardinality.SpanPowerMembership.BaseFormAnisotropicOrthogonalSingle

@[expose] public section

section -- merged from Formalism.LocalRingCardinality.SpanPowerMembership.GenericMemberLevelNearLower
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain Formalism.MainNotions.Inhab
open scoped TensorProduct

section SpacesG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

variable (s : ℕ) (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
  (cm : CMData F E) (T : ℕ) (hT : T.Prime) (pz : E) (hpz : star pz * pz = T)
  (hy : ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1)

end SpacesG

section RowsG

variable {R : Ranks} (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)

abbrev rowsG : Rows.Data R where
  LL := LL
  embLL := embLL
  places := P
  O := 𝓞 LL
  OtoLL := algebraMap (𝓞 LL) LL
  Tau := Tau
  card_Tau := hTau
  Tup := Unit
  mu0 := ()
  muStar := ()
  muStar' := ()
  muAt := fun _ => ()
  muAt_conj := fun _ => rfl
  muTw := fun _ => ()
  muTw_conj := fun _ => rfl
  muAt_or := fun _ => Or.inl rfl
  EE := Z0
  Drows := 0
  onb := EuclideanSpace.basisFun (Fin 0) ℂ
  Dall := 0
  delp := 0
  delp_le_one := zero_le_one
  D_eq := by simp
  EE0 := Z0
  D0 := 0
  onb0 := EuclideanSpace.basisFun (Fin 0) ℂ
  FT := Empty
  ft := fun i => i.elim0
  ft0 := fun i => i.elim0
  Dstar := Dst
  Amb := fun _ => Z0
  Mult := fun _ _ => Z0
  multZero := fun _ => LinearIsometryEquiv.refl ℂ Z0
  multTop := fun _ => LinearIsometryEquiv.refl ℂ Z0
  io := fun _ _ => LinearMap.id
  Mtilde := fun _ => zeroOLat _
  eOp := fun _ => 0
  eOp_idem := fun _ => by simp
  eOp_sa := fun _ => LinearMap.IsSymmetric.zero
  restRowsFiniteGroupCard := cg
  restRowsFiniteGroupCard_pos := hcg
  Word := Unit
  Mu := fun _ => Z0
  perCol := fun _ _ _ _ => 0
  Bu := fun _ _ _ => 0
  ze := fun _ _ => 1
  rowsRest_wordColumnUnit_baseTuple := fun _ => rfl
  Mj := fun _ => Z0
  MjLat := fun _ => zeroOLat _
  kaBig := fun _ _ _ => 0
  kaSmall := fun _ _ _ => 0
  Mt := fun _ _ => Z0
  MtLat := fun _ _ => zeroOLat _
  MtL := fun _ _ => PUnit
  jMt := fun _ _ => 0
  jMt_basis := by
    intro μ j b
    have : IsEmpty (Module.Free.ChooseBasisIndex LL PUnit) :=
      ⟨fun i => b.ne_zero i (Subsingleton.elim _ _)⟩
    exact ⟨linearIndependent_empty_type, Subsingleton.elim _ _⟩
  MtLat_sub := fun _ _ x hx => by simp [zeroOLat] at hx
  eMt := fun _ _ => 0
  eMt_idem := fun _ _ => by simp
  eMt_sa := fun _ _ => LinearMap.IsSymmetric.zero
  eMt_LL := fun _ _ _ => ⟨0, by simp⟩
  thetaP := fun _ _ => 0
  isot := fun _ i => i.elim
  lamP := fun _ _ _ => 0
  Ij := fun _ _ _ => 0
  jw := fun _ _ _ => 0
  etaJ := fun _ _ => 0
  etaJ_nonneg := fun _ _ => le_refl _
  shaLen := sha
  shaLen_nonneg := hsha

end RowsG

theorem N_even (R : Ranks) (j : ℕ) : ∃ a : ℕ, R.N j = 2 * a := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.t_odd
  exact ⟨a + j * (b + 1), by unfold Ranks.N; rw [ha, hb]; ring⟩

theorem sInt (R : Ranks) (hc : HCParam R) (i : Fin R.m) :
    (∃ a : ℤ, sExp R (hc.e i) (i.1 + 1) = a) ∧ (∃ a : ℤ, sExp' R (hc.e i) (i.1 + 1) = a) := by
  obtain ⟨z, hz⟩ := hc.e_int i
  obtain ⟨a, ha⟩ := N_even R i.1
  obtain ⟨b, hb⟩ := N_even R (i.1 + 1)
  refine ⟨⟨z - a, ?_⟩, ⟨z - b, ?_⟩⟩
  · unfold sExp; rw [Nat.add_sub_cancel, ha, hz]; push_cast; ring
  · unfold sExp'; rw [hb, hz]; push_cast; ring

section MemberG

variable {R : Ranks} (hc : HCParam R) (Tau : Type) [Fintype Tau]

variable (T : ℕ) [hT : Fact T.Prime]

end MemberG

section Record

variable {s : ℕ}

variable (H : Host (Rt s))

variable (hc : HCParam (Rt s))
  (hgap : ∀ (l : ℕ) (h : l + 1 < (Rt s).k - 1), hc.v ⟨l, by omega⟩ - hc.v ⟨l + 1, h⟩ = 4 * 1)
  (hlet : ∀ (l : ℕ) (h : l < (Rt s).k - 2), hc.u ⟨l + 1, by omega⟩ = hc.v ⟨l, by omega⟩ - 1 / 2)

variable (T : ℕ) [hT : Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ) (hG : 1 < Gam)
  (hw1 : Ts ≤ T) (hw2 : (T : ℝ) ≤ (1 + 1 / 64) * Ts)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (G : LocalGap H)


end Record

end Formalism.BasicNotions.Examples₂
end
end

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

abbrev Tau2 (R : Ranks) : Type := ↥(R.Psi)

theorem card_realPlaces_eq_degree (R : Ranks) : Fintype.card (Tau2 R) = R.f := by
  rw [← Nat.card_eq_fintype_card, R.toFrame.natCard_Psi]
  rfl

section Member2

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R)

abbrev chain2 : ColumnChain R Tau hc where
  cls := fun _ => Empty
  stab := fun _ c => c.elim
  stabGrp := fun _ c => c.elim
  stabFin := fun _ c => c.elim
  DGam := 1
  DGam_pos := one_pos
  dvd_DGam := fun _ _ c => c.elim
  Y := fun _ => Unit
  de := fun _ _ _ => 1
  de_ne := fun _ _ _ => one_ne_zero
  rhoDet := fun _ c => c.elim
  rhoDet' := fun _ c => c.elim
  rho_norm := fun _ _ c => c.elim
  rho'_norm := fun _ _ c => c.elim
  unf := fun _ c => c.elim
  sSharp := fun i τ => if h : i < R.m then (sInt R (hc τ) ⟨i, h⟩).2.choose else 0
  sSharp_eq := fun i h τ => by rw [dite_eq_left h]; exact (sInt R (hc τ) ⟨i, h⟩).2.choose_spec.symm
  sDiv := fun i τ => if h : i < R.m then (sInt R (hc τ) ⟨i, h⟩).1.choose else 0
  sDiv_eq := fun i h τ => by rw [dite_eq_left h]; exact (sInt R (hc τ) ⟨i, h⟩).1.choose_spec.symm

variable (T : ℕ) [hT : Fact T.Prime]

abbrev levelColumnsAt (Dst : ℝ) (hD : 0 < Dst) (Gam : ℝ) (hG : 1 < Gam) : ColumnsAtT R (chain2 hc) :=
  haveI : NeZero T := ⟨hT.out.ne_zero⟩
  { T := T
    T_prime := hT.out
    vT := Fin R.f
    card_vT := Fintype.card_fin _
    Fv := fun _ => ZMod T
    card_Fv := fun _ => ZMod.card T
    psiT := fun _ => ZMod.stdAddChar
    psiT_ne := fun _ => by
      have := ZMod.isPrimitive_stdAddChar T (one_ne_zero (α := ZMod T))
      rwa [AddChar.mulShift_one] at this
    rhoT := fun _ => 1
    Mu0 := ⊥
    Mu0_fd := inferInstance
    Mu0_stable := fun _ _ => by simp
    duStar := 1
    duStar_pos := one_pos
    Dstar := Dst
    Dstar_pos := hD
    GamP := Gam
    one_lt_gammaP := hG }

end Member2

def dstarOfRanks (R : Ranks) (Ts Gam : ℝ) : ℝ :=
  (Ts * Gam ^ ((2 : ℝ) / ((R.f * R.k : ℕ) : ℝ))) ^ (R.f * R.k)

section Record

variable {R : Ranks}

variable (H : Host R)

abbrev hostLevelData (Ts Gam : ℝ) : Rows.Data R :=
  rowsG H.E H.φ₀ (@placesOf H.E _ _ H.cmStar) (Tau2 R) (card_realPlaces_eq_degree R) (dstarOfRanks R Ts Gam) (shaExample H)
    (shaExample_nonneg H) (exampleClassGroupCard H) (exampleClassGroupCard_pos H)

def hostSpacesOfNorm (T : ℕ) [hT : Fact T.Prime] (pz : H.E) (hpz : pz * H.conj pz = (T : H.E)) :
    @Spaces R H.F H.E _ _ _ _ H.cmStar _ :=
  letI := H.cmStar
  spacesOfRanks R star_isIntegral (cmData H) T hT.out pz
    (by rw [star_eq_conj H pz, mul_comm]; exact hpz)
    (exists_adelic_neg_one H (cmData H).sig (fun x => star_eq_conj H x))

variable (hc : Tau2 R → HCParam R) (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hc τ).v ⟨l, by omega⟩ - (hc τ).v ⟨l + 1, h⟩ = 4 * Del)
  (hlet : ∀ (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hc τ).u ⟨l + 1, by omega⟩ = (hc τ).v ⟨l, by omega⟩ - 1 / 2)
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (T : ℕ) [hT : Fact T.Prime] (Ts : ℝ) (hTs : 0 < Ts) (Gam : ℝ) (hG : 1 < Gam)
  (hw1 : Ts ≤ T) (hw2 : (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * Ts)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
  (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (G : LocalGap H)


end Record

end Formalism.BasicNotions.Examples₂
