Control.Print.printDepth := 100;

fun gcd (n,m) = if m=0 then n else gcd (m,n mod m);
fun lcm (m, n) = Int.div((m * n),  gcd(m,n));

datatype expression =  Constant of int |
    Variable of string |
    Operator of string * expression |
    Pair of expression list |
    List of expression list
;

fun // (a, b) = 
    let
        val gcd_ = gcd(a,b)
        val aa = Int.div(a, gcd_)
        val bb = Int.div(b, gcd_)
    in
        if bb = 1
        then Constant aa
        else Operator("/", Pair [Constant aa, Constant bb])
    end;

infix //;

fun multiply (Operator("/", Pair [Constant a1, Constant b1]), 
              Operator("/", Pair [Constant a2, Constant b2])) = 
        ((a1 * a2) // (b1 * b2));

fun add (Operator("/", Pair [Constant a1, Constant b1]), 
              Operator("/", Pair [Constant a2, Constant b2])) = 
    ((a1 * b2) + (a2 * b1)) // (b1 * b2)
;

fun add2 (Operator("/", Pair [x, Constant b1]), 
          Operator("/", Pair [y, Constant b2])) = 
    let
        val razsiritev_stevca = fn (a, ax) => if ax = 1
            then a
            else case a of
                Constant c => Constant (ax * c)
                | opr => Operator("*", Pair [Constant ax, opr])

        val skupni_imenovalec = lcm(b1,b2)
        val xx = razsiritev_stevca(x, (skupni_imenovalec div b1))
        val yy = razsiritev_stevca(y, (skupni_imenovalec div b2))

        val stevec = case (xx, yy) of
            (Constant c1, Constant c2) => Constant (c1 + c2)
            | (Operator("*", Pair [Constant c, Variable v]), 
                Operator("*", Pair [Constant c2, Variable v1])) => 
                if v = v1 then Operator("*", Pair [Constant (c + c2), Variable v])
                else Operator("+", Pair [xx, yy])

            (* Merge summations into one list *)
            | ((Operator("+", Pair xs), Operator("+", Pair xs1)) | 
               (Operator("+", List xs), Operator("+", List xs1)) |
               (Operator("+", List xs), Operator("+", Pair xs1)) |
               (Operator("+", Pair xs), Operator("+", List xs1))) => Operator("+", List (xs @ xs1))
            
            | ((Operator("+", Pair xs), opr) |
               (Operator("+", List xs), opr)) => Operator("+", List (xs @ [opr]))
            | ((opr, Operator("+", Pair xs)) |
               (opr, Operator("+", List xs))) => Operator("+", List (opr::xs))

            | (_,_) => Operator("+", Pair [xx, yy])
    in
        Operator("/", Pair [stevec, Constant skupni_imenovalec])
    end

fun add3 xs = 
    case xs of
        nil => raise Empty
        | a::nil => a
        | a::b::rest => add3(add2(a,b)::rest)
;

fun flatten expr =
    case expr of
        (Constant _ | Variable _) => expr

        | Operator("/", Pair [expr1, expr2]) =>
            (case (expr1, expr2) of
                (Operator("/", Pair [a, b]), Operator("/", Pair [c, d])) => 
                    let
                        val a_flat = flatten a 
                        val b_flat = flatten b 
                        val c_flat = flatten c 
                        val d_flat = flatten d 
                        
                        val stevec = flatten(Operator("*", Pair [a_flat, d_flat]))
                        val imenovalec = flatten(Operator("*", Pair [b_flat,c_flat]))
                    in
                        flatten(Operator("/", Pair [stevec, imenovalec]))
                    end

                | (Operator("/", Pair [a, b]), watevr) =>
                    let
                        val a_flat = flatten a 
                        val b_flat = flatten b
                        val watevr_flat = flatten watevr

                        val stevec = a_flat
                        val imenovalec = flatten(Operator("*", Pair [b_flat, watevr_flat]))
                    in
                        flatten(Operator("/", Pair [stevec, imenovalec]))
                    end
                | (watevr, Operator("/", Pair [a, b])) =>
                    let
                        val a_flat = flatten a 
                        val b_flat = flatten b
                        val watevr_flat = flatten watevr

                        val stevec = flatten(Operator("*", Pair [b_flat, watevr_flat]))
                        val imenovalec = a_flat
                    in
                        flatten( Operator("/", Pair [stevec, imenovalec]))
                    end
               
                | _ => expr)

        | Operator("*", Pair [expr1, expr2]) =>
           ( case (expr1, expr2) of
               (Constant c1, Constant c2) => Constant (c1 * c2)

               | (Operator("/", Pair [a, b]), Operator("/", Pair [c, d])) => 
                   let
                       val a_flat = flatten a 
                       val b_flat = flatten b 
                       val c_flat = flatten c 
                       val d_flat = flatten d 
                       
                       val stevec = flatten(Operator("*", Pair [a_flat,c_flat]))
                       val imenovalec = flatten(Operator("*", Pair [b_flat,d_flat]))
                   in
                       flatten(Operator("/", Pair [stevec, imenovalec]))
                   end
               | ((watevr, Operator("/", Pair [a, b])) |
                  (Operator("/", Pair [a, b]), watevr)) =>
                   let
                       val a_flat = flatten a 
                       val b_flat = flatten b
                       val watevr_flat = flatten watevr

                       val stevec = flatten(Operator("*", Pair [a_flat, watevr_flat]))
                       val imenovalec = b_flat
                   in
                       flatten(Operator("/", Pair [stevec, imenovalec]))
                   end

               | _ => expr)

        | _ => expr
;

fun count_constants expr = 
    case expr of
        Constant _ => 1
        | Variable _ => 0
        | (Operator(_, List xs) | Operator(_, Pair xs) |
           List xs | Pair xs) => List.foldl (fn (x, acc) => (acc + count_constants(x))) 0 xs
;

fun sum_constants expr = 
    case expr of
        Constant c => c
        | Variable _ => 0
        | (Operator(_, List xs) | Operator(_, Pair xs) |
           List xs | Pair xs) => List.foldl (fn (x, acc) => (acc + sum_constants(x))) 0 xs
;

fun all_variables expr = 
    case expr of
        Constant _ => nil
        | Variable v => [v]
        | (Operator(_, List xs) | Operator(_, Pair xs) |
           List xs | Pair xs) => 
        let
            val uniq = fn xs =>
                case xs of
                    nil => nil
                    | h::rest => h::(List.filter(fn x => (x <> h)) rest)
        in
            List.foldl (fn (x, acc) => (uniq(all_variables(x) @ acc))) nil xs
        end
;

fun traverse fi fs fa ac expr =
    case expr of
        (Constant c | Operator(_, Constant c)) => fi(c)
        | (Variable v | Operator(_, Variable v)) => fs(v)
        | (Operator(_, Pair xs) | Pair xs |
           Operator(_, List xs) | List xs) => List.foldl (fn (x,acc) => fa((traverse fi fs fa ac x), acc)) ac xs
        | Operator(_, Operator(_, a)) => traverse fi fs fa ac a
;


val count_constants = traverse (fn c => 1) (fn v => 0) (fn (a,b) => a+b) 0;

(*tests*)
val test_multiply: expression * expression -> expression = multiply;
val test_add: expression * expression -> expression = add;
val test_add2: expression * expression -> expression = add2;
val test_add3: expression list -> expression = add3;
val test_flatten: expression -> expression = flatten;
val test_traverse: (int -> 'a) -> (string -> 'a) -> ('a * 'a -> 'a) -> 'a -> expression -> 'a = traverse;
val test_count_constants: expression -> int = count_constants;
val test_sum_constants: expression -> int = sum_constants;
val test_all_variables: expression -> string list = all_variables;


(*(0 // 4) = Constant 0;
(1 // 1) = Constant 1;
(8 // 4) = Constant 2;
(9 // 3) = Constant 3;
(2 // 4) = Operator ("/",Pair [Constant 1,Constant 2]);
(3 // 4) = Operator ("/",Pair [Constant 3,Constant 4]);
(3 // 9) = Operator ("/",Pair [Constant 1,Constant 3]);

multiply ((Operator("/", Pair [Constant 1, Constant 3]),
           Operator("/", Pair [Constant 2, Constant 5]))) = Operator ("/",Pair [Constant 2,Constant 15]);
multiply ((Operator("/", Pair [Constant 1, Constant 3]),
           Operator("/", Pair [Constant 3, Constant 5]))) = Operator ("/",Pair [Constant 1,Constant 5]);
multiply ((Operator("/", Pair [Constant 1, Constant 3]),
           Operator("/", Pair [Constant 3, Constant 1]))) = Constant 1;
multiply ((Operator("/", Pair [Constant 2, Constant 3]),
           Operator("/", Pair [Constant 3, Constant 2]))) = Constant 1;


add ((Operator("/", Pair [Constant 1, Constant 3]),
      Operator("/", Pair [Constant 2, Constant 5]))) = Operator ("/",Pair [Constant 11,Constant 15]);
add ((Operator("/", Pair [Constant 1, Constant 3]),
      Operator("/", Pair [Constant 3, Constant 5]))) = Operator ("/",Pair [Constant 14,Constant 15]);
add ((Operator("/", Pair [Constant 1, Constant 3]),
      Operator("/", Pair [Constant 3, Constant 1]))) = Operator ("/",Pair [Constant 10,Constant 3]);
add ((Operator("/", Pair [Constant 2, Constant 3]),
      Operator("/", Pair [Constant 3, Constant 2]))) = Operator ("/",Pair [Constant 13,Constant 6]);
add ((Operator("/", Pair [Constant 1, Constant 2]),
      Operator("/", Pair [Constant 2, Constant 4]))) = Constant 1; 


add2 ((Operator("/", Pair [Constant 1, Constant 2]),
      Operator("/", Pair [Constant 3, Constant 4]))) = Operator ("/",Pair [Constant 5,Constant 4]);

add2 ((Operator("/", Pair [Constant 2, Constant 2]),
      Operator("/", Pair [Constant 2, Constant 2]))) = Operator ("/",Pair [Constant 4,Constant 2]);

add2 ((Operator("/", Pair [Variable "x", Constant 2]),
      Operator("/", Pair [Constant 3, Constant 4]))) = Operator ("/",Pair [Operator ("+", Pair [Operator ("*", Pair [Constant 2, Variable "x"]), Constant 3]), Constant 4]);

add2 ((Operator("/", Pair [Constant 1, Constant 3]),
      Operator("/", Pair [Variable "x", Constant 4]))) = Operator ("/",Pair [Operator ("+", Pair [Constant 4, Operator ("*", Pair [Constant 3, Variable "x"])]), Constant 12]);

add2 ((Operator("/", Pair [Variable "x", Constant 3]),
      Operator("/", Pair [Variable "x", Constant 2])))
       = Operator("/",Pair [Operator ("*", Pair [Constant 5, Variable "x"]), Constant 6]);

add2 ((Operator("/", Pair [Variable "x", Constant 3]),
      Operator("/", Pair [Variable "y", Constant 2])))
       = Operator("/",Pair [Operator ("+", Pair [Operator ("*", Pair [Constant 2, Variable "x"]), Operator ("*", Pair [Constant 3, Variable "y"])]), Constant 6]);

add3 [Operator("/", Pair [Constant 1, Constant 2]),
      Operator("/", Pair [Constant 2, Constant 3]),
      Operator("/", Pair [Variable "x", Constant 3]),
      Operator("/", Pair [Variable "y", Constant 2])
   ] = Operator("/", Pair [Operator("+", List [Constant 7, Operator("*", Pair [Constant 2,Variable "x"]), Operator("*", Pair [Constant 3,Variable "y"])]), Constant 6])
;

add3 [Operator("/", Pair [Constant 1, Constant 2]),
      Operator("/", Pair [Constant 1, Constant 2]),   
      Operator("/", Pair [Constant 2, Constant 3])] = Operator("/", Pair [Constant 10, Constant 6])
;


flatten(Operator("/", Pair [ Operator("/", Pair [ Constant 3, Variable "x" ]), Operator("/", Pair [ Operator("/", Pair [ Variable "x", Operator("/", Pair [ Constant 2, Constant 3 ]) ]), Constant 4 ]) ])) =
    Operator ("/", Pair [Constant 24, Operator ("*", Pair [Operator ("*",Pair [Constant 3,Variable "x"]),Variable "x"])]);
flatten(Operator("/", Pair [ Variable "x", Operator("/", Pair [ Constant 2, Constant 3 ]) ])) =
    Operator("/",Pair [Operator ("*",Pair [Constant 3,Variable "x"]),Constant 2]);
flatten(Operator("*", Pair [Variable "x", Operator("/", Pair [ Variable "x", Operator("/", Pair [ Constant 2, Constant 3 ]) ]) ])) =
    Operator ("/", Pair [Operator ("*", Pair [Constant 3,Operator ("*",Pair [Variable "x",Variable "x"])]), Constant 2]);

count_constants(Constant 2) = 1;
count_constants(Variable "x") = 0;
count_constants(Operator("/", Pair [ Operator("/", Pair [ Constant 3, Variable "x" ]), Operator("/", Pair [ Operator("/", Pair [ Variable "x", Operator("/", Pair [ Constant 2, Constant 3 ]) ]), Constant 4 ]) ])) = 4;

sum_constants(Constant 2) = 2;
sum_constants(Operator("/", Pair [ Operator("/", Pair [ Constant 3, Variable "x" ]), Operator("/", Pair [ Operator("/", Pair [ Variable "x", Operator("/", Pair [ Constant 2, Constant 3 ]) ]), Constant 4 ]) ])) = 12;

all_variables(Constant 2) = nil;
all_variables(Variable "x") = ["x"];
all_variables(Operator("/", Pair [ Operator("/", Pair [ Constant 3, Variable "x" ]), Operator("/", Pair [ Operator("/", Pair [ Variable "x", Operator("/", Pair [ Constant 2, Constant 3 ]) ]), Constant 4 ]) ])) = ["x"];
all_variables(Operator("/", Pair [ Operator("/", Pair [ Constant 3, Variable "y" ]), Operator("/", Pair [ Operator("/", Pair [ Variable "x", Operator("/", Pair [ Constant 2, Constant 3 ]) ]), Constant 4 ]) ])) = ["x", "y"];*)
