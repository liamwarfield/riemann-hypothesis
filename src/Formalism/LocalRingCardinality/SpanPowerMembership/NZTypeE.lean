module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocF

@[expose] public section

section -- merged from Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Polynomial Formalism.CyclotomicNorms NumberField IsDedekindDomain

theorem monicOf_injective {K : Type} [Field K] {N : ℕ} : Function.Injective (monicOf (K := K) (N := N)) := by
  intro a b h
  funext i
  have h2 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) h
  simpa [monicOf, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Fin.val_inj,
    (Fin.is_lt i).ne] using h2

variable {R : Ranks} {H : Host R}

theorem neZero_g (k : Fin 2) : NeZero (H.g k) := by
  exact ⟨(H.g_prime k).ne_zero⟩

theorem fact_g (k : Fin 2) : Fact (H.g k).Prime := by
  exact ⟨H.g_prime k⟩

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {what₂ : Rows.Data R} (N : NData R H what₂)

abbrev Ix : Type := Σ k : Fin 2, N.PlG k

def GoodT (f : ∀ k, N.PlG k → (ZMod (H.g k))[X]) : Prop :=
  ∀ k, haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (f k) (N.chiT k) ∧
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (f k) (fun v j => (N.chiT k v j)⁻¹)

variable {K : Type} [Field K]

def e0F (es : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k)))) :
    MonoidAlgebra K (G0g N) :=
  eSum (I := Ix N) (G := fun kv => GL (Fin R.r) (ZMod (H.g kv.1)))
    (L := fun kv => Fin R.r → ZMod (H.g kv.1)) (fun kv a => es kv.1 (monicOf a))
    (fun a => GoodT N fun k v => monicOf (a ⟨k, v⟩))

variable (es : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra K (GL (Fin R.r) (ZMod (H.g k))))
  (hidem : ∀ k f, es k f * es k f = es k f) (hcen : ∀ k f a, es k f * a = a * es k f)
  (horth : ∀ k f f', f ≠ f' → es k f * es k f' = 0)

include hcen in
theorem seriesIdempotent_central (a : MonoidAlgebra K (G0g N)) : e0F N es * a = a * e0F N es := by
  unfold e0F
  apply eSum_central
  intro i x b
  exact hcen i.1 (monicOf x) b

include hidem horth in
theorem seriesIdempotent_idem : e0F N es * e0F N es = e0F N es := by
  unfold e0F
  apply eSum_idem
  · intro i x
    exact hidem i.1 (monicOf x)
  · intro i x y hxy
    exact horth i.1 _ _ (fun h => hxy (monicOf_injective h))


variable {N}

theorem e0_eq {A : NAut N} (X : NTypes A) : X.e0 = e0F N X.eSer := by
  apply MonoidAlgebra.ext
  ext g
  rw [e0F, eSum_coeff]
  simp only [Formalism.BasicNotions.NTypes.e0, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
  rw [finsum_eq_sum_of_fintype]
  rfl

theorem idempotent_mem_center {A : NAut N} (X : NTypes A) :
    X.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) := by
  rw [e0_eq X, Subalgebra.mem_center_iff]
  intro b
  exact (seriesIdempotent_central N X.eSer X.eSer_central b).symm

theorem idempotent_sum {A : NAut N} (X : NTypes A) : X.e0 * X.e0 = X.e0 := by
  rw [e0_eq X]
  exact seriesIdempotent_idem N X.eSer X.eSer_idem X.eSer_orth

end Formalism.BasicNotions.Examples₂.NZ
end
end

section -- merged from Formalism.LocalRingCardinality.SpanPowerMembership.NDLocG
noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime]

section Emb

variable {F : Type} [Field F] [NumberField F]

def Kphi (φ : F →+* PadicAlgCl l) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun i => φ (Module.finBasis ℚ F i))

instance Kphi_fin (φ : F →+* PadicAlgCl l) : FiniteDimensional ℚ_[l] (Kphi φ) :=
  IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem phi_mem (φ : F →+* PadicAlgCl l) (x : F) : φ x ∈ Kphi φ := by
  have hx := (Module.finBasis ℚ F).sum_repr x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hx, map_sum]
  refine sum_mem (fun i _ => ?_)
  rw [map_rat_smul, Rat.smul_def]
  refine mul_mem ?_ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  first
  | exact SubfieldClass.ratCast_mem _ _
  | exact ratCast_mem _ _
  | exact (Kphi φ).toSubfield.ratCast_mem _
  | simp


theorem exists_embAt (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ φ : F →+* PadicAlgCl l, ∀ x : 𝓞 F, x ∈ w.asIdeal ↔ ‖φ (x : F)‖ < 1 := by
  have hA := isPlaceOver_placeOf (AlgebraicClosure F) w
  have hAl : (placeOf (AlgebraicClosure F) w).valuation ((l : ℕ) : AlgebraicClosure F) < 1 := by
    have := (hA ((l : ℕ) : 𝓞 F)).mpr hw
    simpa using this
  haveI : IsAlgClosure ℚ (AlgebraicClosure F) := isAlgClosureQ F (AlgebraicClosure F)
  obtain ⟨j, hj⟩ := exists_emb (l := l) _ hAl
  exact ⟨j.comp (algebraMap F (AlgebraicClosure F)), fun x => by
    rw [← hA x, val_lt_one_iff hj]; rfl⟩

end Emb


section Mu

variable (LL : FinExt l) {N : ℕ} [NeZero N] {ζ : PadicAlgCl l} (hζ : IsPrimitiveRoot ζ N) (hm : ζ ∈ LL.1)


end Mu

end Formalism.BasicNotions.Examples₂.LB
end
end
