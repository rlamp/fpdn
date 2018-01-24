Control.Print.printDepth := 100;

(*##############################################################################################################################
###################################################  DATATYPES AND EXCEPTIONS  #################################################
################################################################################################################################*)

    datatype expression =  Constant of int |
            Variable of string |
            Operator of string * expression |
            Pair of expression list |
            List of expression list
    ;

    datatype pattern = ConstantP of int
        | VariableP of string
        | OperatorP of string * pattern
        | PairP of pattern list
        | ListP of pattern list
        | UnorderedListP of pattern list
        | Wildcard
    ;

    exception InvalidVariable of string;
    exception InvalidExpression of expression;

(*##############################################################################################################################
###################################################  CROSS  ####################################################################
################################################################################################################################*)

    fun cross (xs1, xs2) = 
        List.foldl (fn (x,acc) =>  acc @ x) [] (List.map(fn x => List.map(fn y => (x,y)) xs2) xs1)
    ;

(*##############################################################################################################################
###################################################  MATCH  ####################################################################
################################################################################################################################*)

    fun match (expr, patt) =
        case (patt, expr) of
            (Wildcard, _) => SOME []
            | (VariableP s, v) => SOME [(s, v)]
            | (ConstantP n, Constant c) => if n = c then (SOME []) else NONE
            | (PairP [a1,a2], Pair [b1,b2]) =>
                let
                    val match1 = match(b1, a1)
                    val match2 = match(b2, a2)
                in
                    if ((isSome match1) andalso (isSome match2))
                    then 
                        let
                            val m1 = (valOf match1)
                            val m2 = (valOf match2)
                            val filter_m2 = List.filter (fn x => List.foldl (fn (y,acc) => not(x = y) andalso acc) true m1 ) m2

                            val same = List.foldl (fn ((s1, a),acc) => 
                                    (List.foldl (fn ((s2,b),acc2) => ((s1 = s2) andalso not(a = b)) orelse acc2) false filter_m2) orelse acc
                                ) false m1
                        in
                            if same
                            then NONE
                            else SOME (m1 @ filter_m2)
                        end
                    else NONE
                end
            | (ListP ps, List xs) =>
                if List.length(ps) <> List.length(xs)
                then NONE
                else let
                    fun foldlfn (a,b,acc) =
                        let 
                            val m = match(a,b) 
                        in
                            if ((isSome acc) andalso (isSome m))
                            then SOME ((valOf acc) @ (valOf m))
                            else NONE
                        end
                in
                    ListPair.foldl foldlfn (SOME []) (xs, ps)
                end
            | (OperatorP(a, x), Operator(b ,y)) =>
                if a = b 
                then match(y,x)
                else NONE
            | (UnorderedListP ps, List xs) =>
                let
                    fun positions x xs = case xs of nil => [[x]] | h::t => (x::h::t)::(List.map(fn l => h::l) (positions x t));
                    fun permute xs = case xs of nil =>[[]] | h::t => List.concat( List.map (fn l => positions h l) (permute t));
                    fun find_right_permutation perms =
                        case perms of
                            nil => NONE
                            | perm::rest => 
                                let
                                    val res = match (List xs, ListP perm)
                                in
                                    if isSome res
                                    then res
                                    else find_right_permutation rest
                                end

                    val perms = permute ps
                in
                    find_right_permutation perms                                                
                end
            | _ => NONE

(*##############################################################################################################################
###################################################  EVAL  #####################################################################
################################################################################################################################*)

    fun gcd(a,b) =
        if b = 0
        then a
        else gcd(b, a mod b);

    fun lcm(a,b) = 
        (a * b) div (gcd (a,b));

    fun eval vars expr =
        let
            fun getVar_aux xs v =
                (case xs of
                    nil => raise InvalidVariable(v)
                    | (name, value)::rest => 
                        if v = name
                        then value
                        else getVar_aux rest v)

            val getVar = getVar_aux vars
        in
            case expr of
                Constant c => c
                | Variable v => (getVar v)
                | Operator("*", Pair [a,b]) => ((eval vars a) * (eval vars b))
                | Operator("*", List xs) => 
                    List.foldl (fn (a,acc) => (acc * (eval vars a))) 1 xs
                | Operator("+", Pair [a,b]) => ((eval vars a) + (eval vars b))
                | Operator("+", List xs) =>
                    List.foldl (fn (a,acc) => (acc + (eval vars a))) 0 xs
                | Operator("-", Pair [a,b]) => ((eval vars a) - (eval vars b))
                | Operator("/", Pair [a,b]) => 
                    let val eval_b = (eval vars b) in
                        if eval_b = 0
                        then raise InvalidExpression(expr)
                        else ((eval vars a) div eval_b)
                    end
                | Operator("%", Pair [a,b]) =>
                    let val eval_b = (eval vars b) in
                        if eval_b = 0
                        then raise InvalidExpression(expr)
                        else ((eval vars a) mod eval_b)
                    end
                | Operator("lcm", Pair [a,b]) =>
                    let
                        val eval_a = (eval vars a)
                        val eval_b = (eval vars b)
                    in
                        lcm(eval_a, eval_b)
                    end

                | Operator("lcm", List xs) =>
                    let
                        val eval_xs = List.map (fn x => (eval vars x)) xs
                    in
                        List.foldl (fn (x,acc) => lcm(acc, x)) (hd eval_xs) (tl eval_xs)
                    end

                | _ => raise InvalidExpression(expr)
        end
    ;

(*##############################################################################################################################
###################################################  REMOVE EMTPY  #############################################################
################################################################################################################################*)

    fun merge_operator_lists expr =
        case expr of
            (Operator("*", List xs)|Operator("*", Pair xs)) =>
                let
                    val tmp = List.map merge_operator_lists xs
                    val flt_xs = List.foldr (fn(x,acc) => 
                            case x of
                                (Operator("*", List xs2)|Operator("*", Pair xs2)) => xs2 @ acc
                                | x => x::acc
                        ) [] tmp
                in
                    if flt_xs = xs
                    then expr
                    else merge_operator_lists (Operator("*", List flt_xs))
                end
            | (Operator("+", List xs)|Operator("+", Pair xs)) =>
                let
                    val tmp = List.map merge_operator_lists xs
                    val flt_xs = List.foldr (fn(x,acc) => 
                            case x of
                                (Operator("+", List xs2)|Operator("+", Pair xs2)) => xs2 @ acc
                                | x => x::acc
                        ) [] tmp
                in
                    if flt_xs = xs
                    then expr
                    else merge_operator_lists (Operator("+", List flt_xs))
                end
            | _=> expr
    ;


    fun removeEmpty exp = 
        let val expr = merge_operator_lists exp in
        case expr of
            (Constant _|Variable _) => expr
            
            | (Operator(_, List [el, Operator(_, List [])]) |
               Operator(_, List [el, Operator(_, Pair [])]) |
               Operator(_, Pair [el, Operator(_, List [])]) |
               Operator(_, Pair [el, Operator(_, Pair [])]) |
               Operator(_, List [Operator(_, List []), el]) |
               Operator(_, List [Operator(_, Pair []), el]) |
               Operator(_, Pair [Operator(_, List []), el]) |
               Operator(_, Pair [Operator(_, Pair []), el])) => removeEmpty el
            
            | Operator("+", List nil) => Constant 0
            | Operator("*", List nil) => Constant 1

            (*množenja/seštevanja enega elementa*)
            | (Operator("+", List [a])|Operator("*", List [a])) => (removeEmpty a)
            (*množenja, pri katerih je eden izmed členov 0*)
            | (Operator("*", Pair [Constant 0, _])|Operator("*", Pair [_,Constant 0])) => (Constant 0)
            (*množenje z ena*)
            | (Operator("*", Pair [Constant 1,a])|Operator("*", Pair [a,Constant 1])) => (removeEmpty a)
            (*prištevanje ničle*)
            | (Operator("+", Pair [Constant 0, a])|Operator("+", Pair [a,Constant 0])) => (removeEmpty a)
            (*odštevanje ničle*)
            | Operator("-", Pair [a,Constant 0]) => (removeEmpty a)
            (*odštevaje od nič*)
            | Operator("-", Pair [Constant 0,Constant c]) => Constant (c * ~1)
            | Operator("-", Pair [Constant 0,a]) => (removeEmpty (Operator("*", Pair [(Constant ~1), (removeEmpty a)])))


            (*odsetevanje a-a  = 0*)
            | Operator("-", Pair [a,b]) => if a = b then Constant 0 else expr
            
            (*deljenje z 1*)
            | Operator("/", Pair [a, Constant 1]) => (removeEmpty a)
            
            (* deljenje a/a = 1 *)
            | Operator("/", Pair [a, b]) => if a = b then Constant 1 else expr
            
            (*mnozenje list*)
            | (Operator("*", List xs)|Operator("*", Pair xs)) =>
                    let 
                        val tmp = (List.map removeEmpty xs) 
                        (*vse konstante*)
                        val (a,rest) = List.partition (fn x => (case x of Constant _ => true |_=>false)) tmp
                        val b = List.filter (fn x => (case x of
                            (Operator (_, List []) | Operator (_, Pair [])) => false
                            | (List []) => false
                            | (Pair []) => false
                            |_ => true)
                         ) rest

                        val zmnozek = List.foldl (fn(x,acc)=>(case x of Constant n=> (acc*n)|_=>acc)) 1 a
                    in
                        if (List.length(a) = 0) andalso (List.length(b) = 0)
                        then Operator("*", List [])
                        else if List.length(a) = 0
                        then Operator("*", List tmp)
                        else if List.length(b) = 0
                            then (Constant zmnozek)
                            else if zmnozek = 0
                                then Constant 0
                                else if zmnozek = 1
                                    then if List.length(b) = 1 then (hd b) else Operator("*", List b)
                                    else Operator("*", List ((Constant zmnozek)::b))

                    end
            (*sestevanje list*)
            | (Operator("+", List xs)|Operator("+", Pair xs)) => 
                let
                    val tmp = (List.map removeEmpty xs)
                    (*vse konstante*)
                    val (a,rest) = List.partition (fn x => (case x of Constant _ => true |_=>false)) tmp
                    val b = List.filter (fn x => (case x of
                            (Operator (_, List []) | Operator (_, Pair [])) => false
                            | (List []) => false
                            | (Pair []) => false
                            |_ => true)
                         ) rest
                    val sestevek = List.foldl (fn(x,acc)=>(case x of Constant n=> (acc+n)|_=>acc)) 0 a
                in
                    if (List.length(a) = 0) andalso (List.length(b) = 0)
                    then Operator("+", List [])
                    else if List.length(a) = 0
                    then Operator("+", List tmp)
                    else if List.length(b) = 0
                        then Constant sestevek
                        else if sestevek = 0
                        then if List.length(b) = 1 then (hd b) else Operator("+", List b)
                        else  Operator("+", List ((Constant sestevek)::b))
                end
            | _ => expr end
    ;

(*##############################################################################################################################
###################################################  COMBINATIONS  #############################################################
################################################################################################################################*)

    fun combinations xs =
        let
            fun aux acc lists =
                case lists of
                    nil => acc
                    | ([])::rest => (aux acc rest)
                    | a::nil => ((List.map (fn x => x::nil) a) @ acc)
                    | a::rest => 
                        let
                            val rst = (aux acc rest)
                        in
                            case rst of
                                nil => (aux acc [a])
                                | _ => List.foldl (fn (x,acc) => ( acc @ (List.map (fn xx => x::xx) rst))) acc a
                        end
        in
            aux [] xs
        end
    ;

(*##############################################################################################################################
###################################################  FLATTEN  ##################################################################
################################################################################################################################*)

    fun fastpower (x, 0) = 1  
    | fastpower (x, n) = if n mod 2 = 0 then     fastpower (x*x, n div 2)  
                                        else x * fastpower (x*x, n div 2);

    fun flatten exp = 
        let val expr = removeEmpty exp in
        case expr of 
            (Constant _| Variable _) => expr

            | (Operator("*", Pair [a,b])|Operator("*", List [a,b])) => 
                (case (a,b) of

                    (* konstante zmnozis*)
                    (Constant c1, Constant c2) => Constant (c1*c2)
                    |((Variable _, Variable _) |
                      (Constant _, Variable _) |
                      (Variable _, Constant _))  => expr

                    (* konstanta * sestevanje - Distributivnost *)
                    |(((Constant c,Operator("+", List xs))|((Operator("+", List xs),Constant c)))|
                      (Constant c,Operator("+", Pair xs))|(Operator("+", Pair xs),Constant c)) => 
                        let
                            val tmp = List.map flatten xs
                            val crs = cross ([Constant c], tmp)
                            val res = List.map (fn (x1,x2) => Operator("*", List [x1,x2])) crs
                        in
                             flatten (Operator("+", List res))
                        end

                    (* variabla * sestevanje - Distributivnost *)
                    |(((Variable v,Operator("+", List xs))|((Operator("+", List xs),Variable v)))|
                      (Variable v,Operator("+", Pair xs))|(Operator("+", Pair xs),Variable v)) => 
                        let
                            val tmp = List.map flatten xs
                            val crs = cross ([Variable v], tmp)
                            val res = List.map (fn (x1,x2) => Operator("*", List [x1,x2])) crs
                        in
                             flatten (Operator("+", List res))
                        end

                    (* sestevanje * sestevanje *)
                    | ((Operator("+", List xs1),Operator("+", List xs2)) |
                       (Operator("+", List xs1),Operator("+", Pair xs2)) |
                       (Operator("+", Pair xs1),Operator("+", List xs2)) |
                       (Operator("+", Pair xs1),Operator("+", Pair xs2))) =>
                        let
                            val xs11 = List.map flatten xs1
                            val xs22 = List.map flatten xs2
                            val crs = cross(xs11, xs22)
                            val res = List.map (fn (x1,x2) => Operator("*", List [x1,x2])) crs
                        in
                             flatten (Operator("+", List res))
                        end

                        (* sestevanje * mnozenje - removeEmpty  *)
                    (*| ((Operator("+", List xs1),Operator("*", List xs2)) |
                       (Operator("+", List xs1),Operator("*", Pair xs2)) |
                       (Operator("+", Pair xs1),Operator("*", List xs2)) |
                       (Operator("+", Pair xs1),Operator("*", Pair xs2)) |
                       (Operator("*", List xs2),Operator("+", List xs1)) |
                       (Operator("*", List xs2),Operator("+", Pair xs1)) |
                       (Operator("*", Pair xs2),Operator("+", List xs1)) |
                       (Operator("*", Pair xs2),Operator("+", Pair xs1))) =>
                        let
                            val tmp = List.map flatten xs1
                            val tmp2 = List.map flatten xs2
                            val res = List.map (fn x => (Operator("*", List (x::tmp2)))) tmp
                        in
                            flatten (Operator("+", List res))
                        end*)

                    |_=> expr)
            | Operator("*", List xs) =>
                let
                    val tmp = List.map flatten xs
                    val (plus, conVars) = List.partition (fn x => case x of Operator("+", _) => true|_=>false) tmp
                in
                    if plus = nil
                    then if tmp = xs then Operator("*", List xs) else flatten (Operator("*", List tmp))
                    else if conVars = nil
                        then flatten (List.foldl (fn (x,acc) => flatten(Operator("*", List [x,acc]) )) (hd plus) (tl plus))
                        else 
                            let
                                val (Operator("+", List abc)) = (hd plus)
                                val acumxs = List.map (fn x => (Operator("*", List (x::conVars)))) (abc)
                                val acum = Operator("+", List acumxs)
                            in
                                flatten (List.foldl (fn (x,acc) => flatten(Operator("*", List [x,acc]) )) acum (tl plus))
                            end
                end
            | Operator("^", Pair [_, Constant 0]) => Constant 1
            | Operator("^", Pair [a, Constant 1]) => (flatten a)
            | Operator("^", Pair [Constant x, Constant c]) => Constant (fastpower(x,c))
            | Operator("^", Pair [Variable x, Constant c]) => Operator("*", List (List.tabulate(c, (fn a => Variable x) ) ) )
            | Operator("^", Pair [exp, Constant 1]) => 
                let
                    val flt_exp= (flatten exp)
                in
                    body
                end
            


            | Operator(x, List xs) => 
                let
                    val new = List.map flatten xs
                in
                    if new = xs
                    then Operator(x, List xs)
                    else flatten (Operator(x, List new))
                end
            | Operator(x, Pair xs) =>
                let
                    val new = List.map flatten xs
                in
                    if new = xs
                    then Operator(x, Pair xs)
                    else flatten (Operator(x, Pair new))
                end
            | Operator(x, opr) => 
                let
                    val new = flatten opr
                in
                    if new = opr
                    then Operator(x, opr)
                    else flatten (Operator(x, new))
                end
            | List xs => 
                let
                    val new = List.map flatten xs
                in
                    if new = xs
                    then List xs
                    else flatten (List new)
                end
            | Pair xs => 
                let
                    val new = List.map flatten xs
                in
                    if new = xs
                    then Pair xs
                    else flatten (Pair new)
                end
        end
    ;

(*##############################################################################################################################
###################################################  JOIN SIMILAR  #############################################################
################################################################################################################################*)

    fun joinSimilar exp =
        let 
            val expr = (flatten exp)

            fun get_vars xs = let val (vars, _) = List.partition (fn x => case x of Variable _=>true|_=>false) xs in vars end

            fun get_vars_sorted xs =  let val vars_vals = ListMergeSort.sort (String.>) (List.map (fn x => let val Variable v = x in v end) (get_vars xs)) in vars_vals end

            fun get_constans xs =  let
                    val (cons, _) = List.partition (fn x => case x of Constant _=>true|_=>false) xs 
                    val cons_vals = List.foldl op* 1 (List.map (fn x => let val Constant c = x in c end) cons)
                in cons_vals end
        in 
        case expr of
            (Constant _ | Variable _) => expr
            
            | (Operator("+", Pair [a,b]) | Operator("+", List [a,b])) =>
                (case (a,b) of
                (* konstante sestejes *)
                (Constant c1, Constant c2) => Constant (c1 + c2)

                |(Variable v1, Variable v2) =>
                    if v1 = v2
                    then Operator("*", List [Constant 2, Variable v1])
                    else expr

                |((Constant _, Variable _) |
                  (Variable _, Constant _))  => expr

                |((Constant c, Operator(opr,lst)) |
                  (Operator(opr,lst), Constant c))  => let
                      val rs = joinSimilar(Operator(opr,lst))
                  in
                      if (flatten rs) = (flatten (Operator(opr,lst)))
                      then expr
                      else  joinSimilar (Operator("+", List [Constant c, rs]))
                  end

                |((Variable v, Operator(opr,lst)) |
                  (Operator(opr,lst), Variable v))  => let
                      val rs = joinSimilar(Operator(opr,lst))
                  in
                      if (flatten rs) = (flatten (Operator(opr,lst)))
                      then expr
                      else joinSimilar (Operator("+", List [Variable v, rs]))
                  end

                |((Operator("*", List xs),Operator("*", List xs1)) |
                 (Operator("*", Pair xs),Operator("*", Pair xs1)) |
                 (Operator("*", Pair xs),Operator("*", List xs1)) |
                 (Operator("*", List xs),Operator("*", Pair xs1))) =>  
                    let
                        val tmp = List.map joinSimilar xs
                        val tmp1 = List.map joinSimilar xs1

                        val cons_val = get_constans tmp
                        val cons1_val = get_constans tmp1

                        val vars_sorted = get_vars_sorted tmp
                        val vars1_sorted = get_vars_sorted tmp1
                    in
                        if vars_sorted = vars1_sorted
                        then joinSimilar (Operator("*", List ((Constant (cons_val + cons1_val))::(get_vars tmp))))
                        else expr
                    end

                |_=> expr
                )
            
            | Operator("+", List xs) =>
                let
                    val tmp = List.map joinSimilar xs
                    val (consts, rest) = List.partition (fn x => case x of Constant _ => true |_=> false) tmp
                    val (mnozVar, ostalo) = List.partition (fn x => case x of (Variable _|Operator("*",_)) => true |_=> false) rest

                    val consts_sum = List.foldl op+ 0 (List.map (fn x => let val Constant c = x in c end) consts)

                    val catg = List.map (fn x =>
                            case x of
                                Variable v => (1, [v])
                                | (Operator("*", List lxs)|Operator("*", Pair lxs)) => (get_constans lxs, get_vars_sorted lxs)
                                | _=> raise InvalidExpression(expr)
                            ) mnozVar

                    fun uniq xxx = 
                        (case xxx of
                            nil => nil
                            | h::t => h::uniq(List.filter (fn x => x <> h) t))

                    val all_var_combos = List.map (fn x => let val (_,cmb) = x in cmb end) catg
                    val uniq_var_combos = uniq all_var_combos
                    val var_res = List.map ( fn x =>
                            let val cnt = List.foldl (fn ((n,vr), acc) =>
                                    if vr = x
                                    then (acc + n)
                                    else acc
                                ) 0 catg
                                val var_lst = List.map (fn vx => Variable vx) x
                            in
                                if cnt = 1
                                then Operator("*", List (var_lst))
                                else Operator("*", List (((Constant cnt)::var_lst)))
                            end
                        ) uniq_var_combos

                    val res = if consts_sum = 0
                        then var_res @ ostalo
                        else ((Constant consts_sum)::var_res @ ostalo)
                in
                    if (flatten (Operator("+", List res))) = expr
                    then expr
                    else joinSimilar(Operator("+", List res))
                end

            | (Operator(opr, Pair xs) | Operator(opr, List xs)) => 
                let
                    val tmp = List.map joinSimilar xs
                in
                    if (flatten(Operator(opr, List tmp))) = (flatten(Operator(opr, List xs)))
                    then expr
                    else joinSimilar (Operator(opr, List tmp))
                end
            
            | Operator(opr, exp2) => 
                let 
                    val new = joinSimilar exp2
                in
                    if (flatten new) = (flatten exp2)
                    then expr
                    else  joinSimilar (Operator(opr, new))
                end
            | List xs => 
                let val tmp = (List.map joinSimilar xs) in
                    if (flatten(List tmp)) = (flatten(List xs))
                    then expr
                    else  joinSimilar(List tmp) end
            | Pair xs => 
                let val tmp = (List.map joinSimilar xs) in
                    if (flatten (Pair tmp)) = (flatten (Pair xs))
                    then expr
                    else  joinSimilar(Pair tmp) end
        end;

(*##############################################################################################################################
###################################################  ODVAJANJE  ################################################################
################################################################################################################################*)

    fun derivative expr var =
        case expr of
            Constant _ => Constant 0
            | Variable v => if v = var then Constant 1 else Constant 0
            | Operator("+", Pair [a,b]) => Operator("+", Pair [(derivative a var), (derivative b var)])
            | Operator("-", Pair [a,b]) => Operator("-", Pair [(derivative a var), (derivative b var)])
            | Operator("*", Pair [a,b]) => Operator("+", Pair [Operator("*", Pair [(derivative a var), b]), 
                                                               Operator("*", Pair [a, (derivative b var)])])
            | Operator("/", Pair [u,v]) => 
                Operator("/", Pair [
                    Operator("-", Pair [
                        Operator("*", Pair [v,(derivative u var)]), 
                        Operator("*", Pair [u,(derivative v var)])
                    ]),
                    Operator("*", Pair [v,v])
                ])
            | _ => raise InvalidExpression(expr)
    ;

(*##############################################################################################################################
###################################################  DELJENJE POLINOMOV  #######################################################
################################################################################################################################*)

    (* stopnja celna je eneka n pri cemer je c*x**n clen *)
    fun stopnja_clena exp = 
        case exp of 
            (Operator("*", List xs)|Operator("*", Pair xs)) => List.foldl (fn (x,acc) => case x of Variable _ => 1 + acc |_=> acc) 0 xs
            | Variable _ => 1
            | _ => 0
    ;

    fun stevnost_clena exp = 
        case exp of 
            (Operator(_, List nil)|Operator(_, Pair nil)) => 0
            | (Operator(_, List xs)|Operator(_, Pair xs)) => 
                let 
                    val consts = List.foldl (fn (x,acc) => case x of Constant c => c::acc |_=>acc) [] xs
                    val cnt = List.foldl op+ 0 consts
                in
                    if consts = nil
                    then 1 
                    else cnt
                end
            | Constant c => c
            | Variable _ => 1
            | _ => raise InvalidExpression(exp)
    ;

    (* stopnja celotnega polinoma je enaka stopnji najvecjega clena*)
    fun stopnja_poly exp =
        case exp of
            (Operator("+", List xs)|Operator("+", Pair xs)) => List.foldl (fn (x,acc) => Int.max(stopnja_clena(x), acc)) 0 xs
            | _ => 0
    ;

    (* primerjaj dva polinoma *)
    fun compare_poly (exp1, exp2) = stopnja_poly(exp1) < stopnja_poly(exp2);

    (* primerjaja dva celna polinoma *)
    fun compare_clen (exp1, exp2) = stopnja_clena(exp1) < stopnja_clena(exp2);

    (* sortiraj clenee polinoma  *)
    fun sort_poly poly = 
        case poly of
            (Operator("+", List xs)|Operator("+", Pair xs)) => Operator("+", List (ListMergeSort.sort compare_clen xs))
            | _=> poly
    ;

    (* katera spremenljivka nastopa v clenu *)
    fun get_clean_var cl =
        case cl of
            (Operator("*", List xs)|Operator("*", Pair xs)) => 
                let
                    val vars = List.foldl (fn (x,acc) => (case x of Variable v => v::acc |_=> acc)) nil xs
                in
                    if vars = nil
                    then raise InvalidExpression(cl)
                    else (hd vars)
                end
            |_=> raise InvalidExpression(cl)

    (*generira nov clen dolocene stopnje in stevnosti *)
    fun generate_clen stevnost stopnja var = 
        if stopnja < 0
        then raise InvalidExpression(Constant ~1)
        else if stopnja = 0
            then  Constant stevnost
            else if stevnost = 1
                then if stopnja = 1
                    then Variable var 
                    else Operator("*", List (List.concat( List.tabulate (stopnja,(fn x => [Variable var])) )))
                else  Operator("*", List (Constant (stevnost)::(List.concat( List.tabulate (stopnja,(fn x => [Variable var])) ))))
    ;


    (* deli dva clena *)
    fun divide_clena cl1 cl2 = 
        let
            val stopnja1 = stopnja_clena cl1
            val stopnja2 = stopnja_clena cl2
            val stevnost1 = stevnost_clena cl1 
            val stevnost2 = stevnost_clena cl2 

            val nova_stopnja = stopnja1 - stopnja2
            val nova_stevnost = stevnost1 div stevnost2
        in
            if stopnja2 > stopnja1
            then raise InvalidExpression(cl2)
            else if nova_stopnja = 0
            then Constant nova_stevnost
            else generate_clen nova_stevnost nova_stopnja (get_clean_var cl1)
        end
    ;

    fun divide_aux polya polyb acc =
            if polya = polyb
            then Constant 1
            else case (polya, polyb) of
                (Constant c1, Constant c2) => Constant(c1 div c2)
                | (_, Constant 0) => raise InvalidExpression(polyb)
                | (Constant 0, _) => Constant 0
                | (a, Constant 1) => a
                | (a, Constant ~1) => Operator("*", Pair [Constant ~1, a])
                | (Variable v, Constant _) => raise InvalidExpression(polyb)
               
                | (Variable v, Variable vv) => if v = vv then Constant 1 else raise InvalidExpression(polya)
                | (Constant _, Variable _) => raise InvalidExpression(polya)
               
                | ((Operator("+", List nil), _)|(Operator("+", Pair nil), _)) => raise InvalidExpression(polya)                
                | ((Operator("+", _), Operator("+", List nil))|
                   (Operator("+", _), Operator("+", Pair nil))) => polya

                | ((Operator("+", _), Constant _) | (Operator("+", _), Variable _) | (Operator("+", _), Operator("*", _))) => 
                    let
                        val Operator("+", List polya_sorted_xs) = sort_poly polya

                        val k = List.map (fn x => divide_clena x polyb) polya_sorted_xs
                    in
                        Operator("+", List k)
                    end

                | ((Operator("*", _), Operator("*", _)) |
                   (Operator("*", _), Variable _) |
                   (Operator("*", _), Constant _) ) => divide_clena polya polyb


                | ((Operator("+", List polya_xs), Operator("+", List polyb_xs))|
                   (Operator("+", Pair polya_xs), Operator("+", List polyb_xs))|
                   (Operator("+", List polya_xs), Operator("+", Pair polyb_xs))|
                   (Operator("+", Pair polya_xs), Operator("+", Pair polyb_xs))) =>
                    let
                        val polya_s = sort_poly polya
                        val polyb_s = sort_poly polyb
                        val Operator("+", List polya_sorted_xs) = polya_s
                        val Operator("+", List polyb_sorted_xs) = polyb_s

                        val k = divide_clena (hd polya_sorted_xs) (hd polyb_sorted_xs)

                        val odstej = Operator("*", List [Constant ~1, k, polyb_s])
                        val reminder =  (joinSimilar (Operator("+", List [polya_s, odstej])))
                    in
                        if reminder = Constant 0 
                            orelse reminder = Operator("+", List nil) orelse reminder = Operator("+", Pair nil)
                            orelse reminder = Operator("*", List nil) orelse reminder = Operator("*", Pair nil)
                        then Operator("+", List (k::acc))
                        else divide_aux reminder polyb_s (k::acc)
                    end

                | (Operator("*", _), _) => divide_aux (Operator("+", List [polya])) polyb acc
                | (_, Operator("*", _)) => divide_aux polya (Operator("+", List [polyb])) acc
                | _ => raise InvalidExpression(polya)
    ;

    fun divide (pa, pb) = 
        sort_poly(joinSimilar(divide_aux (joinSimilar pa) (joinSimilar pb) []))
    ;

(*##############################################################################################################################
###################################################  TEST  #####################################################################
################################################################################################################################*)

    (*val test_cross:'a list * 'b list -> ('a * 'b) list = cross;
    val test_match:expression * pattern -> (string * expression) list option = match;
    val test_eval:(string * int) list -> expression -> int = eval;
    val test_derivative:expression -> string -> expression = derivative;
    val test_removeEmpty:expression -> expression = removeEmpty;
    val test_combinations:'a list list -> 'a list list = combinations;
    val test_flatten:expression -> expression = flatten;
    val test_joinSimilar:expression -> expression = joinSimilar;
    val test_divide:expression * expression -> expression = divide;

    print "\n\n#############################################  CROSS TESTS  ##############################################################\n\n";
    cross([],[]) = [];
    cross([],[1,1,1]) = [];
    cross([1,1,1],[]) = [];
    cross([1, 2, 3],[3, 4, 5]) = [(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,3),(3,4),(3,5)];
    cross([1,1,1],[1,1]) = [(1,1),(1,1),(1,1),(1,1),(1,1),(1,1)];
    cross([1,1,1],[2,2]) = [(1,2),(1,2),(1,2),(1,2),(1,2),(1,2)];

    print "\n\n#############################################  MATCH TESTS  ##############################################################\n\n";
    match (Operator("test", List []), Wildcard) = SOME [];
    match (List [], Wildcard) = SOME [];
    match (Pair [Constant 1, Constant 2], Wildcard) = SOME [];
    match (Constant 1, Wildcard) = SOME [];
    match (Variable "x", Wildcard) = SOME [];

    match (Constant 1, ConstantP 2) = NONE;
    match (Constant 2, ConstantP 1) = NONE;
    match (Constant 2, ConstantP 2) = SOME [];

    match (Constant 2, VariableP "A") = SOME [("A", Constant 2)];
    match (Variable "x", VariableP "A") = SOME [("A", Variable "x")];
    match (List [], VariableP "A")  = SOME [("A", List [])];
    match (Pair [Constant 1, Constant 2], VariableP "A")  = SOME [("A", Pair [Constant 1, Constant 2])];
    match (Operator("+", Pair [Constant 1, Constant 2]), VariableP "A")  = SOME [("A", Operator("+", Pair [Constant 1, Constant 2]))];
    match (Operator("+", Pair [Operator("*", List []), Operator("-", Pair [Variable "x", Constant 2])]), VariableP "A")  = SOME [("A", Operator("+", Pair [Operator("*", List []), Operator("-", Pair [Variable "x", Constant 2])]))];

    match(Operator("+", Pair [
        Operator ("*", List [Variable "a", Variable "a"]),
        Operator ("*", List [Variable "b", Variable "b"])
    ]), OperatorP("+", PairP [VariableP "A", VariableP "B"])) = SOME [
        ("A",Operator ("*",List [Variable "a",Variable "a"])),
        ("B",Operator ("*",List [Variable "b",Variable "b"]))];

    match(Operator("+", Pair [
        Operator ("*", List [Variable "a", Variable "a"]),
        Operator ("*", List [Variable "b", Variable "b"])
    ]), OperatorP("+", PairP [VariableP "A", VariableP "B", VariableP "C"])) = NONE;


    match(Operator("+", Pair [
        Operator ("*", List [Variable "a", Variable "a"]),
        Operator ("*", List [Variable "b", Variable "b"])
    ]), OperatorP("+", PairP [
        OperatorP ("*", ListP [VariableP "A", Wildcard]),
        OperatorP ("*", ListP [VariableP "B", Wildcard])
    ])) = SOME [("A", Variable "a"),("B", Variable "b")];

    match(Operator("+", Pair [
        Operator ("*", List [Variable "a", Variable "a"]),
        Operator ("*", List [Variable "b", Variable "b"])
    ]), OperatorP("+", PairP [
        OperatorP ("*", UnorderedListP [VariableP "A", Wildcard]),
        OperatorP ("*", UnorderedListP [VariableP "B", Wildcard])
    ])) = SOME [("A", Variable "a"),("B", Variable "b")];

    match(Operator("+", Pair [
        Operator ("*", List [Variable "a", Constant 1]),
        Operator ("*", List [Constant 2, Variable "b"])
    ]), OperatorP("+", PairP [
        OperatorP ("*", UnorderedListP [VariableP "A", ConstantP 1]),
        OperatorP ("*", UnorderedListP [VariableP "B", ConstantP 2])
    ])) = SOME [("A", Variable "a"),("B", Variable "b")];

    match(Operator("+", Pair [
        Operator ("*", List [Variable "a", Constant 2]),
        Operator ("*", List [Constant 1, Variable "b"])
    ]), OperatorP("+", PairP [
        OperatorP ("*", UnorderedListP [VariableP "A", Wildcard]),
        OperatorP ("*", UnorderedListP [VariableP "B", ConstantP 2])
    ])) = NONE;

    match(Operator("+", Pair [
        Operator ("*", List [Variable "a", Constant 2]),
        Operator ("*", List [Constant 2, Variable "b"])
    ]), OperatorP("+", PairP [
        OperatorP ("*", UnorderedListP [VariableP "A", Wildcard]),
        OperatorP ("*", UnorderedListP [VariableP "B", ConstantP 2])
    ])) = SOME [("A", Variable "a"),("B", Variable "b")];

    match(Operator("+", Pair [
        Operator ("*", List [Variable "a", Constant 2]),
        Operator ("*", List [Constant 2, Variable "b"])
    ]), OperatorP("+", PairP [
        OperatorP ("*", UnorderedListP [VariableP "A", Wildcard]),
        OperatorP ("*", ListP [VariableP "B", ConstantP 2])
    ])) = NONE;

    match(Operator("+", Pair [
        Operator ("*", List [Variable "a", Constant 2]),
        Operator ("*", List [Constant 2, Variable "b"])
    ]), OperatorP("+", ListP [
        Wildcard,
        Wildcard
    ])) = NONE;

    match(Operator("+", List [
        Operator ("*", List [Variable "a", Constant 2]),
        Operator ("*", List [Constant 2, Variable "b"])
    ]), OperatorP("+", ListP [
        Wildcard,
        Wildcard
    ])) = SOME [];

    match(Operator("+", List [
        Operator ("*", List [Variable "a", Constant 2]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", List [Constant 2, Variable "b"])
    ]), OperatorP("+", ListP [
        Wildcard,
        Wildcard,
        Wildcard,
        Wildcard,
        Wildcard
    ])) = SOME [];

    match(Operator("+", List [
        Operator ("*", List [Variable "a", Constant 2]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", List [Constant 2, Variable "b"])
    ]), OperatorP("+", ListP [
        Wildcard,
        Wildcard,
        Wildcard,
        Wildcard
    ])) = NONE;


    match(Operator("+", List [
        Operator ("*", List [Variable "a", Constant 2]),
        Operator ("*", Pair [Variable "a", Constant 2]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", Pair [Constant 2, Variable "b"]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", Pair [Constant 2, Variable "b"])
    ]), OperatorP ("+", ListP [
        Wildcard,
        Wildcard,
        Wildcard,
        Wildcard,
        OperatorP ("*", PairP [ConstantP 2, VariableP "C"]),
        OperatorP ("*", PairP [ConstantP 2, VariableP "B"])
    ])) = NONE;

    match(Operator("+", List [
        Operator ("*", List [Variable "a", Constant 2]),
        Operator ("*", Pair [Variable "a", Constant 2]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", Pair [Constant 2, Variable "b"]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", Pair [Constant 2, Variable "b"])
    ]), OperatorP ("+", ListP [
        Wildcard,
        Wildcard,
        OperatorP ("*", ListP [ConstantP 2, VariableP "C"]),
        Wildcard,
        Wildcard,
        OperatorP ("*", PairP [ConstantP 2, VariableP "B"])
    ])) = SOME [("C", Variable "b"), ("B", Variable "b")];

        match(Operator("+", List [
        Operator ("*", List [Variable "a", Constant 2]),
        Operator ("*", Pair [Variable "a", Constant 2]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", Pair [Constant 2, Variable "b"]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", Pair [Constant 2, Variable "b"])
    ]), OperatorP ("+", ListP [
        OperatorP ("*", ListP [ConstantP 2, VariableP "C"]),
        Wildcard,
        Wildcard,
        Wildcard,
        Wildcard,
        OperatorP ("*", PairP [ConstantP 2, VariableP "B"])
    ])) = NONE;

    match(Operator("+", List [
        Operator ("*", List [Variable "a", Constant 2]),
        Operator ("*", Pair [Variable "a", Constant 2]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", Pair [Constant 2, Variable "b"]),
        Operator ("*", List [Constant 2, Variable "b"]),
        Operator ("*", Pair [Constant 2, Variable "b"])
    ]), OperatorP ("+", UnorderedListP [
        OperatorP ("*", ListP [ConstantP 2, VariableP "C"]),
        Wildcard,
        Wildcard,
        Wildcard,
        Wildcard,
        OperatorP ("*", PairP [ConstantP 2, VariableP "B"])
    ])) = SOME [("C", Variable "b"), ("B", Variable "b")];

    match(Operator("+", List [
        Constant 13, 
        Variable "a", 
        Constant 3, 
        Operator ("*", Pair [Constant 1, Constant 2])]), 
    OperatorP("+", UnorderedListP [
        Wildcard, 
        ConstantP 13, 
        OperatorP ("*", PairP [ConstantP 1, VariableP "x"]), 
        Wildcard])) = SOME [("x",Constant 2)];

    print "\n\n#############################################  EVAL TESTS  ###############################################################\n\n";
    eval [("x", 3)] 
    (Operator("+", List [
        Operator ("*", Pair [Constant 3, Variable "x"]),
        Constant 7,
        Operator ("*", List [
            Constant 4,
            Variable "x",
            Variable "x"
        ])
    ])) = 52;

    print "\n\n#############################################  REMOVE EMPTY TESTS  #######################################################\n\n";
    removeEmpty(Operator ("+", List [Operator ("*", List [])])) = Constant 1;
    removeEmpty(Operator ("*", List [Operator ("+", List [])])) = Constant 0;

    removeEmpty(Operator ("+", List [Constant 0])) = Constant 0;
    removeEmpty(Operator ("+", List [Constant 1])) = Constant 1;
    removeEmpty(Operator ("+", List [Constant 11])) = Constant 11;
    removeEmpty(Operator ("*", List [Constant 1])) = Constant 1;
    removeEmpty(Operator ("*", List [Constant 0])) = Constant 0;
    removeEmpty(Operator ("*", List [Constant 22])) = Constant 22;
    removeEmpty(Operator ("*", List [Variable "x"])) = Variable "x";
    removeEmpty(Operator ("+", List [Constant 0, Constant 0])) = Constant 0;
    removeEmpty(Operator ("+", List [Constant 0, Constant 1])) = Constant 1;
    removeEmpty(Operator ("*", List [Constant 0, Constant 1])) = Constant 0;
    removeEmpty(Operator ("*", List [Constant 1, Constant 1])) = Constant 1;
    removeEmpty(Operator ("+", List [Constant 0, Variable "y"])) = Variable "y";
    removeEmpty(Operator ("*", List [Constant 0, Variable "y"])) = Constant 0;
    removeEmpty(Operator ("+", List [Constant 1, Variable "y"])) = Operator ("+", List [Constant 1, Variable "y"]);
    removeEmpty (Operator ("*", List [Constant 0, Variable "x", Variable "x"])) = Constant 0;
    removeEmpty (Operator ("*", List [Operator ("-", Pair [Constant 1, Constant 0]), Variable "x", Constant 1, Constant 1])) = Variable "x";

    removeEmpty (Operator ("+", List [
        Operator ("+", Pair [Constant 0, Constant 0]),
        Operator ("*", List [Constant 0, Variable "x", Variable "x"]),
        Operator ("*", List [Operator ("-", Pair [Constant 1, Constant 0]), Variable "x", Constant 1, Constant 1])]
        )) = Variable "x";

    removeEmpty (Operator ("+", List [
        Operator ("+", Pair [Operator("*", List [Constant 0]), Operator("*", List [Constant 0])]),
        Operator ("*", List [Operator("*", List [Constant 0]), Variable "x", Variable "x"]),
        Operator ("*", List [Operator ("-", Pair [Constant 1, Constant 0]), Variable "x", Constant 1, Constant 1])]
        )) = Variable "x";

    removeEmpty (Operator ("+", List [
        Operator ("+", Pair [Operator("*", List [Constant 1]), Operator("*", List [Constant 0])]),
        Operator ("*", List [Operator("*", List [Constant 0]), Variable "x", Variable "x"]),
        Operator ("*", List [Operator ("-", Pair [Constant 1, Constant 0]), Variable "x", Constant 1, Constant 1])]
        )) = Operator("+", List [Constant 1, Variable "x"]);

    removeEmpty (Operator("+", List [
        Constant 2,
        Operator("+", List [Operator("+", List [Operator("*", Pair[Constant 0,  Operator("+", List [])])])]),
        Operator("+", List [])
    ])) = Constant 2;

    print "\n\n#############################################  COMBINATIONS TESTS  #######################################################\n\n";
    combinations [[1, 3], [4], [2, 5, 1]] = [[1,4,2],[1,4,5],[1,4,1],[3,4,2],[3,4,5],[3,4,1]];
    combinations [[1, 3]] = [[1],[3]];
    combinations [[1, 3], []] = [[1],[3]];
    combinations [[1, 3], [] , [4,5,6]] = [[1,4],[1,5],[1,6],[3,4],[3,5],[3,6]];
    combinations [[], [1, 3], [] , [4,5,6], []] = [[1,4],[1,5],[1,6],[3,4],[3,5],[3,6]];
    combinations [[], [1, 3], [7,8] , [4,5,6], []] = [[1,7,4],[1,7,5],[1,7,6],[1,8,4],[1,8,5],[1,8,6],[3,7,4],[3,7,5],[3,7,6],[3,8,4],[3,8,5],[3,8,6]];

    print "\n\n#############################################  FLATTEN TESTS  ############################################################\n\n";
    flatten (Operator("+", List [Constant 1, Constant 2])) = Constant 3;
    flatten (Operator("+", List [Constant 2, Constant 2])) = Constant 4;
    flatten (Operator("*", List [Constant 1, Constant 2])) = Constant 2;
    flatten (Operator("*", List [Constant 3, Constant 2])) = Constant 6;
    flatten (Operator("+", Pair [Constant 1, Constant 2])) = Constant 3;
    flatten (Operator("+", Pair [Constant 2, Constant 2])) = Constant 4;
    flatten (Operator("*", Pair [Constant 1, Constant 2])) = Constant 2;
    flatten (Operator("*", Pair [Constant 3, Constant 2])) = Constant 6;
    flatten (Constant 1) = Constant 1;
    flatten (Constant 2) = Constant 2;
    flatten (Variable "x") = Variable "x";
    flatten (Variable "y") = Variable "y";
    flatten (List [Constant 1, Constant 2, Constant 2]) = List [Constant 1, Constant 2, Constant 2];
    flatten (Pair [Constant 1, Constant 2]) = Pair [Constant 1, Constant 2];

    flatten (Operator("+", List [
        Constant 2, 
        Operator("+", List [Constant 2, Variable "x"])
    ])) =
    Operator("+", List [Constant 4, Variable "x"]);

    flatten (Operator("+", List [
        Operator("+", List [Constant 2, Variable "x"]),
        Constant 2 
    ])) =
    Operator("+", List [Constant 4, Variable "x"]);

    flatten (Operator("*", List [
        Operator("+", List [Constant 2, Variable "x"]),
        Operator("+", List [Constant 2, Variable "x"])
    ])) =
    Operator("+", List [
        Constant 4,
        Operator ("*", List [
            Constant 2,
            Variable "x"
            ]),
        Operator ("*", List [
            Constant 2,
            Variable "x"
            ]),
        Operator ("*", List [
            Variable "x",
            Variable "x"
            ]) 
    ]);

    flatten (Operator("*", List [
        Constant 2,
        Operator("+", List [Constant 2, Variable "x"]),
        Operator("+", List [Constant 2, Variable "x"])
    ])) =
    Operator("+", List [
        Constant 8,
        Operator ("*", List [
            Constant 4,
            Variable "x"
            ]),
        Operator ("*", List [
            Constant 4,
            Variable "x"
            ]),
        Operator ("*", List [
            Constant 2,
            Variable "x",
            Variable "x"
            ]) 
    ]);

    flatten (Operator("*", List [
        Constant 2,
        Operator("+", List [Operator("+", List [Constant 1, Constant 1]), Variable "x"]),
        Operator("+", List [Operator("+", List [Constant 0, Constant 2]), Variable "x"])
    ])) =
    Operator("+", List [
        Constant 8,
        Operator ("*", List [
            Constant 4,
            Variable "x"
            ]),
        Operator ("*", List [
            Constant 4,
            Variable "x"
            ]),
        Operator ("*", List [
            Constant 2,
            Variable "x",
            Variable "x"
            ]) 
    ]);


    flatten (Operator("*", List [
        Constant 2,
        Operator("+", List [Operator("+", List [Constant 0, Operator("*", Pair [Constant 1, Constant 2])]), Variable "x"]),
        Operator("+", List [Operator("+", List [Constant 0, Constant 2]), Variable "x"])
    ])) =
    Operator("+", List [
        Constant 8,
        Operator ("*", List [
            Constant 4,
            Variable "x"
            ]),
        Operator ("*", List [
            Constant 4,
            Variable "x"
            ]),
        Operator ("*", List [
            Constant 2,
            Variable "x",
            Variable "x"
            ]) 
    ]);


    flatten (Operator ("+", List [
        Constant 1,
        Operator ("+", List [
        Operator ("*", Pair [
            Operator ("+", Pair [Variable "x", Constant 3]),
            Operator ("+", Pair [Constant 3, Variable "x"])]),
        Variable "x",
        Operator ("*", Pair [Constant 3, Variable "x"])])
    ])) = 
    Operator ("+", List [
        Constant 10,
        Operator ("*",List [Constant 3,Variable "x"]),
        Operator ("*",List [Constant 3,Variable "x"]),
        Operator ("*",List [Variable "x",Variable "x"]),
        Variable "x",
        Operator ("*",List [Constant 3,Variable "x"])
    ]);

    flatten (Operator ("*", List [
        Constant 2, Variable "x",
        Operator ("+", Pair [Constant 1, Variable "x"]),
        Operator ("+", Pair [Constant 1, Variable "x"]),
        Operator ("+", Pair [Constant 2, Variable "y"])

    ])) = 
    Operator ("+", List [
        Operator ("*",List [Constant 4,Variable "x"]),
        Operator ("*",List [Constant 4,Variable "x",Variable "x"]),
        Operator ("*",List [Constant 4,Variable "x",Variable "x"]),
        Operator ("*",List [Constant 4,Variable "x",Variable "x",Variable "x"]),
        Operator ("*",List [Constant 2,Variable "y",Variable "x"]),
        Operator ("*",List [Constant 2,Variable "y",Variable "x",Variable "x"]),
        Operator ("*",List [Constant 2,Variable "y",Variable "x",Variable "x"]),
        Operator ("*",List [Constant 2,Variable "y",Variable "x",Variable "x",Variable "x"])
    ]);

    flatten (Operator ("*", List [
        Operator ("+", Pair [Constant 1, Variable "x"]),
        Operator ("+", Pair [Constant 1, Variable "x"])
    ])) = 
    Operator("+", List [
        Constant 1,
        Variable "x",
        Variable "x",
        Operator("*", List [Variable "x", Variable "x"])
    ]);

    flatten (Operator ("*", List [
       Constant 2,
        Operator ("+", Pair [Constant 1, Variable "x"]),
        Operator ("+", Pair [Constant 1, Variable "x"])
    ])) = 
    Operator("+", List [
        Constant 2,
        Operator("*", List [Constant 2, Variable "x"]),
        Operator("*", List [Constant 2, Variable "x"]),
        Operator("*", List [Constant 2,  Variable "x", Variable "x"])
    ]);

    flatten (Operator ("*", List [
       Constant 2,
       Constant 2,
        Operator ("+", Pair [Constant 1, Variable "x"]),
        Operator ("+", Pair [Constant 1, Variable "x"])
    ])) = 
    Operator("+", List [
        Constant 4,
        Operator("*", List [Constant 4, Variable "x"]),
        Operator("*", List [Constant 4, Variable "x"]),
        Operator("*", List [Constant 4,  Variable "x", Variable "x"])
    ]);

    flatten (Operator ("*", List [
       Constant 2,
       Constant 2,
       Variable "x",
        Operator ("+", Pair [Constant 1, Variable "x"]),
        Operator ("+", Pair [Constant 1, Variable "x"])
    ])) = 
    Operator("+", List [
        Operator("*", List [Constant 4, Variable "x"]),
        Operator("*", List [Constant 4, Variable "x", Variable "x"]),
        Operator("*", List [Constant 4, Variable "x", Variable "x"]),
        Operator("*", List [Constant 4,  Variable "x", Variable "x", Variable "x"])
    ]);

    flatten(Operator("*", Pair [
        Operator("*", Pair [Constant 2, Variable "y"]),
        Operator("*", Pair [Constant 2, Variable "x"])
    ])) = 
    Operator ("*",List [Constant 4,Variable "y",Variable "x"]);

    flatten(Operator("*", Pair [
        Operator("*", Pair [Constant 1, Variable "x"]),
        Operator("*", List [Variable "x",Variable "y", Constant 3])
    ])) =
    Operator ("*",List [Constant 3,Variable "x",Variable "x",Variable "y"]);

    print "\n\n#############################################  JOIN SIMILAR TESTS  #######################################################\n\n";
    joinSimilar (Operator("*", List [ 
        Constant 1,
        Constant 2,
        Constant 3
    ])) = Constant 6;

    joinSimilar (Operator("*", List [ 
        Constant 0,
        Constant 1,
        Constant 2,
        Constant 3
    ])) = Constant 0;

    joinSimilar (Operator("*", List [ 
        Variable "x",
        Constant 1,
        Constant 2,
        Variable "x",
        Variable "y",
        Variable "x",
        Constant 3,
        Variable "y"
    ])) = Operator("*",List[Constant 6,Variable "x",Variable "x",Variable "y",Variable "x", Variable "y"]);

    joinSimilar (Operator ("+", List [
        Constant 1,
        Operator ("*", Pair [Constant 3, Constant 1]),
        Operator ("*", Pair [Constant 5, Variable "x"]),
        Variable "x",
        Operator ("*", List [Variable "x", Constant 3]),
        Operator ("*", List [Variable "x", Variable "x"])
    ])) = Operator ("+", List [
        Constant 4,
        Operator ("*",List [Constant 9,Variable "x"]),
        Operator ("*",List [Variable "x",Variable "x"])
    ]);

    joinSimilar(Operator("+", List [
        Variable "x",
        Variable "x",
        Variable "x",
        Variable "x",
        Variable "x"
    ])) = Operator ("*",List [Constant 5,Variable "x"]);

    joinSimilar(Operator("+", List [
        Variable "x",
        Operator ("test",List [Variable "x", Operator("+", Pair [Constant 2, Constant 3])]),
        Variable "x",
        Variable "y",
        Operator ("/",List [Variable "x", Constant 5]),
        Variable "y",
        Variable "x"
    ])) = Operator ("+", List [
        Operator ("*",List [Constant 3,Variable "x"]),
        Operator ("*",List [Constant 2,Variable "y"]),
        Operator ("test",List [Variable "x", Constant 5]),
        Operator ("/",List [Variable "x", Constant 5])
    ]);

    joinSimilar(Operator("+", List [
        Operator("*", List [Constant 22, Variable "y", Variable "y"]),
        Operator("*", List [Constant 10, Variable "x"]),
        Operator("*", List [Constant 2, Variable "x"]),
        Operator("*", List [Constant 3, Variable "x"]),
        Operator("*", List [Constant 3, Variable "x", Variable "x"]),
        Operator("*", List [Constant 2, Variable "x", Variable "x"]),
        Operator("*", List [Constant 100, Variable "y"]),
        Operator("*", List [Constant 22, Variable "y", Variable "y"]),
        Operator ("/",List [Variable "x", Constant 5]),
        Operator("+", List [Constant 22,Constant 33]),
        Constant 1,
        Operator("+", List [Constant 2,Constant 2])
    ])) = Operator ("+", List [
        Constant 60,
        Operator ("*",List [Constant 44,Variable "y",Variable "y"]),
        Operator ("*",List [Constant 15,Variable "x"]),
        Operator ("*",List [Constant 5,Variable "x",Variable "x"]),
        Operator ("*",List [Constant 100,Variable "y"]),
        Operator ("/",List [Variable "x", Constant 5])
    ]);

    joinSimilar (derivative (Operator ("*", Pair [
        Variable "x",
        Operator ("*", Pair [
            Constant 3,
            Variable "x"
        ])
    ])) "x") = Operator ("*",List [Constant 6,Variable "x"]);


    print "\n\n#############################################  DIVIDE TESTS  #############################################################\n\n";
    divide (
    Operator ("+", List [
        Operator ("*",List [Constant 12,Variable "x",Variable "x",Variable "x",Variable "x",Variable "x"]),
        Operator ("*",List [Constant 18,Variable "x",Variable "x",Variable "x"]),
        Operator ("*",List [Constant 3, Operator("*", Pair[Variable "x",Variable "x"])]),
        Operator ("*",Pair [Constant 6,Variable "x"]),
        Operator("+", List [Constant 1, Constant 2])
    ]),
    Operator ("+", List [
        Operator ("*",List [Constant 3]),
        Operator ("*",List [Constant 3,Variable "x",Variable "x"])
    ])
    ) =
    Operator("+", List [
        Operator("*", List [Constant 4, Variable "x", Variable "x", Variable "x"]),
        Operator("*", List [Constant 2, Variable "x"]),
        Constant 1
    ]);


    divide (Constant 4, Constant 2) = Constant 2;
    divide (Constant 4, Constant 4) = Constant 1;
    divide (Constant 4, Constant 1) = Constant 4;
    divide (Variable "x", Constant 1) = Variable "x";
    divide (Variable "x", Variable "x") = Constant 1;

    divide (Operator("+", Pair [
            Operator("*", List [Constant 2, Variable "x", Variable "x"]),
            Operator("*", Pair [Constant 2, Variable "x"])
        ]),
        Operator("+", Pair [
            Operator("*", List [Constant 2, Variable "x", Variable "x"]),
            Operator("*", Pair [Constant 2, Variable "x"])
        ])
    ) = Constant 1;

    divide (Operator("+", List [
            Operator("*", Pair [Constant 2, Variable "x"])
        ]),
        Operator("+", List [
            Operator("*", Pair [Constant 2, Variable "x"])
        ])
    ) = Constant 1;

    divide (Operator("+", Pair [
            Operator("*", List [Constant 2, Variable "x", Variable "x"]),
            Operator("*", Pair [Constant 2, Variable "x"])
        ]),
        Operator("+", Pair [
            Operator("*", List [Variable "x", Variable "x"]),
            Operator("*", List [Variable "x"])
        ])
    ) = Constant 2;

    divide (Operator("+", List [
            Operator("*", List [Constant 2, Variable "x", Variable "x"]),
            Operator("*", Pair [Constant 2, Variable "x"]),
            Constant 4
        ]),
        Operator("+", List [
            Operator("*", List [Variable "x", Variable "x"]),
            Operator("*", List [Variable "x"]),
            Constant 2
        ])
    ) = Constant 2;

    divide (Operator("+", List [
            Operator("*", List [Constant 3, Variable "x", Variable "x", Variable "x", Variable "x", Variable "x"]),
            Operator("*", List [Constant 8, Variable "x", Variable "x", Variable "x", Variable "x"]),
            Operator("*", Pair [Constant 2, Variable "x", Variable "x", Variable "x"]),
            Operator("*", Pair [Constant ~1, Variable "x"])
        ]),
        Operator("+", List [
            Operator("*", List [Constant 3, Variable "x", Variable "x", Variable "x"]),
            Operator("*", List [Constant 2, Variable "x", Variable "x"]),
            Variable "x"
        ])
    ) = 
    Operator("+", List [
            Operator("*", List [Variable "x", Variable "x"]),
            Operator("*", List [Constant 2, Variable "x"]),
            Constant ~1
    ]);

    divide (Operator("+", List [
            Operator("*", List [Constant 88, Variable "x", Variable "x",  Variable "x", Variable "x", Variable "x", Variable "x"]),
            Operator("*", List [Constant ~20, Variable "x",  Variable "x", Variable "x", Variable "x", Variable "x"]),
            Operator("*", List [Constant ~110, Variable "x", Variable "x", Variable "x", Variable "x"]),
            Operator("*", Pair [Constant ~61, Variable "x", Variable "x", Variable "x"]),
            Operator("*", Pair [Constant 15, Variable "x", Variable "x"]),
            Operator("*", Pair [Constant 25, Variable "x"]),
            Constant 15
        ]),
        Operator("+", List [
            Operator("*", List [Constant 4, Variable "x", Variable "x", Variable "x"]),
            Operator("*", List [Constant ~5, Variable "x"]),
            Constant ~3
        ])
    ) = 
    Operator("+", List [
        Operator("*", List [Constant 22, Variable "x", Variable "x", Variable "x"]),
        Operator("*", List [Constant ~5, Variable "x", Variable "x"]),
        Constant ~5
    ]);
    
    divide(Constant 2, Constant 1) = Constant 2;
    divide(Constant 2, Constant 2) = Constant 1;
    divide(Constant 20, Constant ~2) = Constant ~10;


    divide(Operator("+", List [Constant 2, Constant 2]), Operator("+", List [Constant 1])) = Constant 4;
    divide(Operator("+", List [Constant 2, Constant 2]), Operator("+", List [Constant 2])) = Constant 2;
    divide(Operator("+", List [Constant 20, Constant 2]), Operator("+", List [Constant ~2])) = Constant ~11;

    divide (Operator("*", Pair [Constant 4, Variable "x"]),
            Operator("*", Pair [Constant 2, Variable "x"])
    ) = Constant 2;

    divide (Operator("*", Pair [Constant 4, Variable "x"]),
            Operator("*", Pair [Constant 2, Constant 2])
    ) = Variable "x";

    divide (Operator("*", Pair [Constant 4, Variable "x"]),
            Operator("*", List [Constant 2, Constant 2, Variable "x"])
    ) = Constant 1;

    divide (Operator("*", List [Constant 4, Variable "x", Variable "x"]),
            Operator("*", List [Constant 2, Constant 2, Variable "x"])
    ) = Variable "x";

    divide (Operator("*", List [Constant 4, Variable "x", Variable "x"]),
            Operator("*", Pair [ Constant 2, Variable "x"])
    ) = Operator("*", List [ Constant 2, Variable "x"]);

    divide(Variable "x", Variable "x") = Constant 1;
    divide (Operator("+", List [
            Operator("*", Pair [Constant 4, Variable "x"])
        ]),
        Operator("+", List [
            Operator("*", Pair [Constant 2, Variable "x"])
        ])
    ) = Constant 2;

    divide (Operator ("+", List [
        Operator ("*",List [Constant 12,Variable "x",Operator("*", Pair [Variable "x",Variable "x"]),Operator("*", Pair [Variable "x",Variable "x"])]),
        Operator ("*",List [Constant 18,Operator("*", Pair [Variable "x",Variable "x"]),Variable "x"]),
        Operator ("*",List [Constant 3, Operator("*", Pair [Variable "x",Variable "x"])]),
        Operator ("*",Pair [Operator("+", Pair [Constant 3, Constant 3]), Variable "x"]),
        Operator("+", List [Constant 1, Constant 2, Operator("*", List [Constant 1, Constant 0, Constant 22, Constant 1])])
    ]), Operator ("+", List [
        Operator ("*",List [Constant 3]),
        Operator ("*",List [Constant 3,Variable "x",Variable "x"])
    ])) = 
    Operator ("+", List [
        Operator ("*",List [Constant 4,Variable "x",Variable "x",Variable "x"]),
        Operator ("*",List [Constant 2,Variable "x"]),
        Constant 1]);


    divide(Operator("+", List[
            Operator("*", List [Constant 4, Variable "x"]),
            Constant 4
        ]),
        Operator
        ("+",List [Operator ("*",List [Constant 2,Variable "x"]),Constant 2])
    ) = Constant 2;

    divide(Operator("+", List[
            Operator("*", List [Constant 4, Variable "x"]),
            Constant 4
        ]),
        Operator
        ("+",List [Operator ("*",List [Constant 2,Variable "x"]),Constant 2])
    ) = Constant 2;

    divide (
        Operator("+", List [
            Variable "x",
            Constant 2
        ]),
        Operator("+", List [
            Variable "x",
            Constant 2
        ])
    ) = Constant 1;

    divide (
        Operator("+", List [
            Operator("*", List [Constant 2, Variable "x"])
        ]),
        Variable "x"
    ) = Constant 2;

    divide (
        Operator("+", List [
            Operator("*", List [Constant 2, Variable "x"])
        ]),
        Operator("*", List [
            Variable "x"
        ])
    ) = Constant 2;

    divide (
        Operator("+", List [
            Operator("*", List [Constant 2, Variable "x"])
        ]),
        Operator("+", List [
            Variable "x"
        ])
    ) = Constant 2;

    divide (
        Operator("+", List [
            Operator("*", List [Constant 4, Variable "x"])
        ]),
        Operator("+", List [
            Variable "x"
        ])
    ) = Constant 4;

    divide (
        Operator("+", List [
            Operator("*", List [Constant 4, Variable "x"])
        ]),
        Operator("+", List [
            Variable "x"
        ])
    ) = Constant 4;

    divide (
        Operator("+", List [
            Operator("*", List [Constant 4, Variable "x", Variable "x"])
        ]),
        Operator("+", List [
            Variable "x"
        ])
    ) = Operator("*", List [
            Constant 4,
            Variable "x"
        ]);

    divide (
        Operator("+", List [
            Operator("*", List [Constant 6, Variable "x", Variable "x"])
        ]),
        Operator("+", List [Operator("*", List [
            Constant 2,
            Variable "x"
        ])])
    ) = Operator("*", List [
            Constant 3,
            Variable "x"
        ]);*)

(*
eval [("x", 1)] 
    (Operator("lcm", List [
    Operator("+", Pair[Constant 20, Variable "x"]), 
    Constant 6, 
    Operator("lcm", List [Constant 28])
]));*)


(*
match (Operator("+", Pair [
    Operator ("*", Pair [Variable "a", Variable "b"]),
    Operator ("-", Pair [
        Constant 3, 
        Operator ("*", Pair [Variable "a", Variable "b"])
    ])
]), OperatorP("+", PairP [
    VariableP "A", 
    OperatorP ("-", PairP [
        VariableP "B", 
        VariableP "A"])
]))*)