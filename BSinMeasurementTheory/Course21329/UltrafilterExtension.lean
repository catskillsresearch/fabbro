import Mathlib.Order.Zorn
import BSinMeasurementTheory.Course21329.Filter

universe u

namespace Course21329

variable {B : Type u} [Lattice B] [BoundedOrder B]

/-- Union of a non-empty chain of proper filters is a proper filter. -/
lemma sUnion_chain_isProperFilter (c : Set (Set B))
    (hc_sub : ∀ F ∈ c, IsProperFilter F)
    (hc_chain : IsChain (· ⊆ ·) c)
    (hc_ne : c.Nonempty) :
    IsProperFilter (⋃₀ c) where
  mem_top := by
    rcases hc_ne with ⟨F, hF⟩
    exact Set.mem_sUnion_of_mem (hc_sub F hF).mem_top hF
  upward := by
    intro x y hx hxy
    rcases Set.mem_sUnion.mp hx with ⟨F, hF, hxF⟩
    exact Set.mem_sUnion_of_mem ((hc_sub F hF).upward hxF hxy) hF
  inf_closed := by
    intro x y hx hy
    rcases Set.mem_sUnion.mp hx with ⟨F, hF, hxF⟩
    rcases Set.mem_sUnion.mp hy with ⟨G, hG, hyG⟩
    rcases hc_chain.total hF hG with hle | hle
    · exact Set.mem_sUnion_of_mem ((hc_sub G hG).inf_closed (hle hxF) hyG) hG
    · exact Set.mem_sUnion_of_mem ((hc_sub F hF).inf_closed hxF (hle hyG)) hF
  not_bot := by
    intro hbot
    rcases Set.mem_sUnion.mp hbot with ⟨F, hF, hbotF⟩
    exact (hc_sub F hF).not_bot hbotF

/-- (a) Ultrafilter Extension Theorem:
Every proper filter `F₀` extends to an ultrafilter `U` using Zorn's Lemma. -/
theorem ultrafilter_extension (F₀ : Set B) (hF₀ : IsProperFilter F₀) :
    ∃ U : Set B, IsUltrafilter U ∧ F₀ ⊆ U := by
  let S := {F : Set B | IsProperFilter F ∧ F₀ ⊆ F}
  have hzorn : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hcS hcchain hcne
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · apply sUnion_chain_isProperFilter c (fun F hF => (hcS hF).1) hcchain hcne
    · rcases hcne with ⟨F, hF⟩
      exact (hcS hF).2.trans (Set.subset_sUnion_of_mem hF)
  rcases zorn_subset_nonempty S hzorn F₀ ⟨hF₀, Set.Subset.refl F₀⟩ with ⟨U, hF₀U, hUmax⟩
  refine ⟨U, { toIsProperFilter := hUmax.1.1, maximal := ?_ }, hF₀U⟩
  intro G hGprop hUG
  have hGS : G ∈ S := ⟨hGprop, hF₀U.trans hUG⟩
  exact Set.Subset.antisymm hUG (hUmax.2 hGS hUG)

end Course21329
