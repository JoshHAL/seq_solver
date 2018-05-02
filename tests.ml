open SeqCalc
let test1 = ([Or (Atom "P", Atom "Q")], [And(Atom "P", Atom "Q")])
            |> prove

let test2 =
  ([], [Implies(Implies (Implies(Atom "P", Atom "Q"), Atom "P"), Atom "P")])
  |> prove

let test3 = ([], [Or (Atom "A", Not (Atom "A"))])
            |> prove

let test4 =
  ([], [Implies (Implies (Implies (Atom "A", False), Atom "A"), Atom "A")])
  |> prove

let test5 =
  ([Atom "X"],[And (Atom "X",Or (Atom "X", Atom "Y"))])
  |> prove

let test6 =
  ([], [
     
         Implies (
             And (
                 Implies (Atom "G",
                          Or (Atom "F", Atom "D")),
                 Implies (
                     And (Atom "F", Atom "G"),
                     Atom "D")
               ),
             Implies (
                 Atom "G",
                 Atom "D")
           )
  ])
  |> prove

let do_test name t =
  (
    print_string (name ^ ":\n");
    print_string (graphviz_of_tree name t);
    print_string "\n"
  )
let main () =
  (
    do_test "Test1" test1;
    do_test "Test2" test2;
    do_test "Test3" test3;
    do_test "Test4" test4;
    do_test "Test5" test5;
    do_test "Test6" test6
  )

let _ = main ()
