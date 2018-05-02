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

  let string_of_rule r =
    match r with
      NoRule -> "" 
    | Bot_L -> "bot_L"
    | Neg_L -> "neg_L"
    | And_L -> "and_L"
    | Or_L -> "or_L"
    | Impl_L -> "->_L"
    | Ax -> "Ax"
    | Neg_R -> "neg_R"
    | And_R -> "and_R"
    | Or_R -> "or_R"
    | Impl_R -> "->_R"

  type proof_tree =
    Unproved
  | Proved
  | Node of rule * sequent * proof_tree * proof_tree

  let get_rule_seq (Node (rule, seq,_,_)) = (rule, seq)

  let get_seq (Node (_,seq,_,_)) = seq

  let only_nodes t f = match t with
      Proved -> Proved
    | Unproved -> Unproved
    | _ -> f t

  let hd_singleton ls =
    match ls with
      [] -> []
    | (x::xs) -> [x]
         
  let apply_rule_L_partial node =
    let rec left_rules (rule, (gamma, d)) acc t =
      let
        seq = (gamma @ acc, d)
      in
      match gamma with
        (False :: gamma') -> Node(rule, seq, Node (Bot_L, seq, Proved, Proved), Proved)
      | (Not p :: gamma') -> Node (rule, seq,
                                  Node (Neg_L, (gamma' @ acc, p::d),
                                        Unproved, Proved),
                                  Proved)
      | (And (f, g)::gamma') -> Node
                                 (rule, seq,
                                  Node (And_L, (f::g::(gamma' @ acc), d),
                                        Unproved, Proved),
                                  Proved)
      | (Or (f, g)::gamma') ->
         Node (rule, seq,
               Node (Or_L, (f::(gamma' @ acc), d), Unproved, Proved),
               Node (Or_L, (g::(gamma' @ acc), d), Unproved, Proved))
      | (Implies (f, g)::gamma') ->
         Node
           (rule, seq,
            Node (Impl_L, (gamma' @ acc, f::d),Unproved, Proved),
            Node (Impl_L, (g::(gamma' @ acc), d), Unproved, Proved))
      | (x::xs) -> left_rules (rule,(xs, d)) (x::acc) t
      | [] -> t
    in only_nodes node (left_rules (get_rule_seq node) [])

  let apply_rule_R_partial node =
    let rec right_rules (rule, (gamma, delta)) acc t =
      let
        seq = (gamma, delta @ acc)
      in
      match delta with
        (Not p :: delta') -> Node (rule, seq,
                                  Node (Neg_R, (p::gamma, delta' @ acc),
                                        Unproved, Proved),
                                  Proved)
      | (And (f, g)::delta') -> Node
                                 (rule, seq,
                                  Node (And_R, (gamma, f::(delta' @ acc)),
                                        Unproved, Proved),
                                  Node (And_R, (gamma, g::(delta' @ acc))
                                       ,Unproved,Proved)
                                  )
      | (Or (f, g)::delta') ->
         Node (rule, seq,
               Node (Or_R, (gamma, f::g::(delta' @ acc))
                   , Unproved, Proved),
               Proved)
      | (Implies (f, g)::delta') ->
         Node
           (rule, seq,
            Node (Impl_R, (f::gamma, g::(delta'@acc))
                 ,Unproved, Proved)
            ,Proved)
      | (d::delta') -> right_rules (rule, (gamma, delta')) (d::acc) t
      | [] -> t
    in only_nodes node (right_rules (get_rule_seq node) [] )

     
  let axiom (g, d) =
    let
      isAxiom g d =
        List.fold_left
          (fun acc elem ->
            match (acc,elem) with
              (false, Atom x) -> List.mem elem d
            | _ -> acc
          ) false g
    in isAxiom g d

  let rec map_unproved f t =
      match t with
        Unproved -> Unproved
      | Proved -> Proved
      | Node (rule, seq, Unproved, r) -> f t
      | Node (rule, seq, l, Unproved) -> f t
      | Node (rule, seq, l, r) -> Node (rule, seq, map_unproved f l, map_unproved f r)

  let apply_rule_L = map_unproved apply_rule_L_partial
  let apply_Ax = map_unproved
                   (fun n ->
                     let
                       Node (rule, seq, l, r) = n
                     in
                     if axiom seq
                     then Node (rule, seq, Node (Ax,seq, Proved, Proved), Proved)
                     else n
                   )

  let apply_rule_R = map_unproved apply_rule_R_partial
  let apply_rules node = node |> apply_rule_L |> apply_Ax |> apply_rule_R
  let to_tree seq = Node (NoRule, seq, Unproved, Proved)
  let rec provable t =
    match t with
      Proved -> true
    | Unproved -> false
    | Node (_,_, l, r) -> provable l && provable r

  let rec prove_aux tree =
    let
      next = apply_rules tree
    in
    if next = tree then tree else prove_aux next

  let prove seq =
      seq |> to_tree |> prove_aux



  let rec prop_to_string prop =
    match prop with
      False -> "False"
    | Not p -> "(Not" ^ prop_to_string p ^ ")"
    | Atom x -> x
    | Or (x,y) -> "(" ^ prop_to_string x ^ " or " ^ prop_to_string y ^ ")"
    | And (x, y) ->  "(" ^ prop_to_string x ^ " and " ^ prop_to_string y ^ ")"
    | Implies (x, y) -> "(" ^ prop_to_string x ^ " --> " ^ prop_to_string y ^ ")"

  let seq_to_string seq =
    let
      string_of_prop_list ls = "[" ^
                                 (ls |> List.fold_left (fun acc elem -> prop_to_string elem ^ ";" ^ acc) "")
                                 ^ "]"
    in
    let
      g = fst seq |> string_of_prop_list and
      d = snd seq |> string_of_prop_list
    in g ^ " ==> " ^ d

  let string_of_edge id r id' =
    string_of_int id' ^ "->" ^ string_of_int id ^
      "[label = \"" ^ string_of_rule r ^ "\"];"

  let get_rule n = match n with Node (r,_,_,_) -> r | _ -> NoRule
                                
  let string_of_seq id seq = string_of_int id ^  " [label = \"" ^ seq_to_string seq ^ "\"];"

  let rec graphviz_aux t id =
    let graphviz_sub_aux seq id node =
      let
         current_node = string_of_seq id seq and
         (node_str, last_id) = graphviz_aux node (id + 1) and
         rule = get_rule node
       in
       (current_node ^ "\n" ^ node_str ^ "\n" ^ string_of_edge id rule (id + 1)
       , last_id + 1)
    in
    match t with
      Proved -> ("", id)
    | Unproved -> (string_of_int id ^ " [label = \"Unprovable\"];", id + 1)
    | Node (_, seq, Proved, Proved) ->
       (string_of_int id ^  "[label = \"" ^ seq_to_string seq ^ "\"];", id + 1)
    | Node (_, seq, Proved, r) -> graphviz_sub_aux seq id r
    | Node (_, seq, l, Proved) -> graphviz_sub_aux seq id l
    | Node (_, seq, l, r) ->
       let
         current_node = string_of_seq id seq and
         (l_node, next_id) = graphviz_aux l (id + 1) and
         rule = get_rule l
       in
       let
         (r_node, last_id) = graphviz_aux r next_id
       in
       (current_node ^ "\n" ^ l_node ^ "\n" ^
          string_of_edge id rule (id + 1) ^ "\n" ^
            r_node ^ "\n" ^ string_of_edge id rule next_id
       , last_id + 1)
      
  let graphviz_of_tree name t = "digraph Proof_tree_" ^
                                 name ^ " {\nnode [shape = box];\n" ^
                                   fst (graphviz_aux t 0) ^ "\n}\n"
  let print_graphviz name seq =
    seq
    |> to_tree
    |> prove_aux
    |> (graphviz_of_tree name)
    |> print_string
