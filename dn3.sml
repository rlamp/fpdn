datatype natural = 
    ZERO
    | NEXT of natural

(* vrne true, če so vrednosti v seznamu urejena naraščajoče. Uporabite case stavek. *)
fun sorted(xs): bool =
	let
		fun aux (xs, acc) =
			if acc = false
			then false
			else case xs of
				nil => acc
				| a::nil => acc
				| a::b::rep => aux(b::rep, (a <= b) andalso acc)
	in
		aux(xs, true)
	end
(*	case xs of
		nil => true
		| _::nil => true
		| a::b::rep => (a <= b) andalso sorted(b::rep)
*)

(* vrne seznam, ki ima na i-tem mestu terko (xs1_i, xs2_i), kjer je xs1_i i-ti element prvega seznama, xs2_i pa i-ti element drugega seznama. Če sta vhodna seznama različnih dolžin je dolžina rezultata enaka dolžini krajšega seznama *)
fun zip(xs1, xs2) =
	let
		fun aux(xs1, xs2, acc) = 
			case (xs1, xs2) of
				(nil, _) => acc
				| (_, nil) => acc
				| (h1::t1, h2::t2) => aux(t1,t2, (acc @ [(h1,h2)]))
	in
		aux(xs1, xs2, nil)
	end

(* vrne obrnjen seznam, uporablja repno rekurzijo! *)
fun reverse(xs) =
	let
		fun aux(xs, acc) =
			case xs of
				nil => acc
				| h::t => aux(t, h::acc)
	in
		aux(xs, nil)
	end

(* vrne objekt tipa natural, ki predstavlja podano število *)
fun toNatural(a: int): natural =
	let
		fun aux(a, acc) = 
			if a = 0
			then acc
			else aux(a-1, NEXT(acc))
	in
		aux(a, ZERO)
	end

(* vrne true, če je podano naravno število sodo. *)
(*
1 true
0 false

2 true
1 false
0 true
*)
fun isEven(a: natural): bool =
	let
		fun aux(a, acc) = 
			case a of
				ZERO => if acc = true
					then true
					else false
				| NEXT(x) => aux(x, not acc)
	in
		aux(a, true)
	end

(* vrne true, če je podano naravno število liho. *)
fun isOdd(a: natural): bool = not (isEven(a));

(* vrne predhodnika naravnega števila a, če je a ZERO, proži izjemo PreviousOfZero *)
exception PreviousOfZero
fun previous(a: natural): natural =
	case a of
		ZERO => raise PreviousOfZero
		| NEXT(x) => x

(* vrne naravno število, ki ustreza razliki števil a in b (a-b), če rezultat ni naravno število, proži izjemo PreviousOfZero *)
fun subtract(a: natural, b: natural): natural =
	case b of
		ZERO => a
		| NEXT(bx) => case a of
			ZERO => raise PreviousOfZero
			| NEXT(ax) => subtract(ax, bx)

(* vrne true, če funkcija f vrne true za katerga od elementov seznama *)
fun any(f, xs) =
	let
		fun aux(xs, acc) =
			if acc = true
			then true
			else case xs of
				nil => false
				| h::t => aux(t, f(h) orelse acc)
	in
		aux(xs, false)
	end

(* vrne true, če funkcija f vrne true za vse elemente podanega seznama *)
fun all(f, xs) =
	let
		fun aux(xs, acc) =
			if acc = false
			then false
			else case xs of
				nil => true
				| h::t => aux(t, f(h) andalso acc)
	in
		aux(xs, true)
	end


;;;; "type tests"  ;;;;
val test_sorted_type: int list -> bool = sorted;
val test_zip_type: 'a list * 'b list -> ('a * 'b) list = zip;
val test_reverse_type: 'a list -> 'a list = reverse;
val test_toNatural_type: int -> natural = toNatural;
val test_isEven_type: natural -> bool = isEven;
val test_isOdd_type: natural -> bool = isOdd;
val test_previous_type: natural -> natural = previous;
val test_subtract_type: natural * natural -> natural = subtract;
val test_any_type: ('a -> bool) * 'a list -> bool = any;
val test_all_type: ('a -> bool) * 'a list -> bool = all;

(*
sorted(nil) = true;
sorted([1]) = true;
sorted([1,1]) = true;
sorted([1,2]) = true;
sorted([2,1]) = false;
sorted([1,2,3]) = true;
sorted([1,2,3,2,1]) = false;

zip([],[]) = [];
zip([1],[]) = [];
zip([],[1]) = [];
zip([1,2,3],[3,2,1]) = [(1,3),(2,2),(3,1)];
zip([1,2,3],[3,2,1,1,2]) = [(1,3),(2,2),(3,1)];
zip([1,2,3,4,5],[3,2,1]) = [(1,3),(2,2),(3,1)];

reverse([]) = [];
reverse([1]) = [1];
reverse([1,2]) = [2,1];
reverse([1,2,3]) = [3,2,1];

val nic = ZERO;
val ena = NEXT(ZERO);
val dva = NEXT(NEXT(ZERO));
val tri = NEXT(NEXT(NEXT(ZERO)));
val stiri = NEXT(NEXT(NEXT(NEXT(ZERO))));
val pet = NEXT(NEXT(NEXT(NEXT(NEXT(ZERO)))));

toNatural(0) = nic;
toNatural(1) = ena;
toNatural(2) = dva;
toNatural(3) = tri;
toNatural(4) = stiri;

isEven(nic) = true;
isEven(ena) = false;
isEven(dva) = true;
isEven(tri) = false;
isEven(stiri) = true;
isEven(pet) = false;

isOdd(nic) = false;
isOdd(ena) = true;
isOdd(dva) = false;
isOdd(tri) = true;
isOdd(stiri) = false;
isOdd(pet) = true;

previous(nic)
handle PreviousOfZero => nic;
previous(ena) = nic;
previous(dva) = ena;
previous(tri) = dva;
previous(stiri) = tri;
previous(pet) = stiri;

subtract(nic,nic) = nic;
subtract(ena,nic) = ena;
subtract(nic,ena)
handle PreviousOfZero => ena;
subtract(ena,ena) = nic;
subtract(dva,ena) = ena;
subtract(tri,ena) = dva;
subtract(tri,dva) = ena;
subtract(pet,dva) = tri;
subtract(dva, tri)
handle PreviousOfZero => dva;

fun f x = (x = 42);

any(f, []) = false;
any(f, [1,2,3]) = false;
any(f, [1,2,42,3]) = true;
any(f, [1,2,3,42]) = true;

all(f, []) = true;
all(f, [1,2,3]) = false;
all(f, [1,2,42,3]) = false;
all(f, [1,2,3,42]) = false;
all(f, [42]) = true;
all(f, [42,42]) = true;
all(f, [42,42,42]) = true;
*)