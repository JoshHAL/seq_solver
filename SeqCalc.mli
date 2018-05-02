type prop =
    False
  | Atom of string
  | Not of prop
  | And of prop * prop
  | Or of prop * prop
  | Implies of prop * prop

  type sequent = prop list * prop list

  type rule =
    NoRule
  | Bot_L
  | Neg_L
  | And_L
  | Or_L
  | Impl_L
  | Ax
  | Neg_R
  | And_R
  | Or_R
  | Impl_R

  type proof_tree =
    Unproved
  | Proved
  | Node of rule * sequent * proof_tree * proof_tree

  val map_unproved: (proof_tree -> proof_tree) -> proof_tree -> proof_tree
  val apply_rule_L: proof_tree -> proof_tree
  val apply_Ax: proof_tree -> proof_tree
  val apply_rule_R: proof_tree -> proof_tree
  val graphviz_of_tree: string -> proof_tree -> string
  val print_graphviz: string -> sequent -> unit
  val to_tree: sequent -> proof_tree
  val prove: sequent -> proof_tree

