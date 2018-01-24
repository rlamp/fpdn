(* (podan seznam xs agregira z začetno vrednostjo z in funkcijo f v vrednost f(f(f(z, xs_1),  xs_2)), xs_3)... *)
fun reduce(f, z, xs) = 
	case xs of
		nil => z
		| h::t => reduce(f, f(z,h), t)

(* (vrne seznam, ki vsebuje kvadrate števil iz vhodnega seznama. Uporabite List.map. *)
fun squares xs = 
	List.map(fn x => x*x) xs;

(* (vrne seznam, ki vsebuje vsa soda števila iz vhodnega seznama. Uporabite List.filter. *)
fun only_even xs = 
	List.filter(fn x => (x mod 2) = 0) xs;

(* (je tipa (string * string -> bool) -> string list -> string. Poleg seznama nizov sprejme funkcijo, ki pove, kateri niz izmed dveh je boljši. 
Podana funkcija kot parametra vzame par nizov, vrne pa true, če je boljši prvi niz, sicer pa false. Gre za posplošitev funkcij, kot sta npr. 
largest_string (poišče leksikografsko največji niz) in longest_string (poišče prvi najdaljši niz). Implementirajte omenjeni funkciji z uporabo best_string. *)
fun best_string f xs =
	case xs of
		nil => ""
		| h::t => List.foldl(fn(x,acc) => if f(x,acc) then x else acc) h t
;

fun largest_string xs =
	best_string (fn(a,b) => a>b) xs
;

fun longest_string  xs =
	best_string (fn(a,b) => String.size(a) > String.size(b)) xs
;

(* (sprejme seznam števil (int list) in vrne naraščajoče urejen seznam z algoritmom Quicksort.  *)
fun quicksort xs =
	case xs of 
		nil => nil
		| h::t => let
			val (more, less) = List.partition(fn x => x >= h) t
			val less = quicksort less
			val more = quicksort more
		in
			less @ h::more
		end
;

(* (sprejme dva vektorja tipa (int list) in vrne njun skalarni produkt. Uporabite ListPair.zip, ali pa kar ListPair.map *)
fun dot vc1 vc2 = 
	List.foldl(fn ((a,b), acc) => acc + (a*b)) 0 (ListPair.zip(vc1, vc2))
;

(* (vrne transponirano podano matriko tipa a'' list list. Rešitev vključuje uporabo funkcij map, hd, tl in rekurzije *)
fun transpose mtrx = 
	if (null mtrx) orelse null (hd mtrx)
	then []
	else let
			val vc = List.map(hd) mtrx
			val res = transpose (List.map(tl) mtrx)
		in
			vc::res
		end
;

(* (sprejme dve matriki (int list list) in vrne njun (matrični) produkt. Pomagate si lahko z dot in transpose. *)
fun multiply mtrx1 mtrx2 = 
	List.map(fn x => List.map(fn y => (dot x y)) (transpose mtrx2)) mtrx1
;

(* (v podanem seznamu prešteje koliko zaporednih elementov je enakih in vrne seznam parov (vrednost, število ponovitev), 
ki je tipa (''a * int) list *)
fun group xs = 
	case xs of
		nil => nil
		| h::_ => let
					val zp = ListPair.zip(xs, List.tabulate(List.length(xs), fn x=>x+1));
					val n = List.foldl(fn((a,b),acc) => if a=h andalso acc=(b-1) then acc+1 else acc) 0 zp
					val tail = List.drop(xs, n)
				in
					(h,n)::group(tail)
				end 
;

(* (Elemente iz podanega seznama razvrsti v ekvivalenčne razrede in vrne seznam teh razredov (''a list list). 
Znotraj razredov naj bodo elementi v istem vrstnem redu kot v podanem seznamu. Ekvivalentnost elementov definira podana funkcija, 
ki za dva elementa pove, ali sta ekvivalentna - vrne true oz. false. Primer take funkcije je npr. fun equiv x y = x mod 3 = y mod 3). *)
fun equivalence_classes f xs =
	case xs of
		nil => nil
		| h::t => let
				val (pos, neg) = List.partition(fn x => f h x) t
				val rest = (equivalence_classes f)(neg)
			in
				(h::pos)::rest
			end
;

;;;; "type tests"  ;;;;
val test_reduce_type: ('a * 'b -> 'a) * 'a * 'b list -> 'a = reduce;
val test_squares_type: int list -> int list = squares;
val test_only_even_type: int list -> int list = only_even;
val test_best_string_type: (string * string -> bool) -> string list -> string = best_string;
val test_quicksort_type: int list -> int list = quicksort;
val test_dot_type: int list -> int list -> int = dot;
val test_transpose_type: 'a list list -> 'a list list = transpose;
val test_multiply_type: int list list -> int list list -> int list list = multiply;
val test_group_type: ''a list -> (''a * int) list = group;
val test_equivalence_classes_type: (''a -> ''a -> bool) -> ''a list -> ''a list list = equivalence_classes;


(* tests *)

(*val mtrx = [
	[1,2,3,4,5],
	[1,2,3,4,5],
	[1,2,3,4,5],
	[1,2,3,4,5],
	[1,2,3,4,5]
];
val mtrx1 = [
	[1,1],
	[1,1],
	[1,1],
	[1,1]
];
val mtrx2 = [
	[1,1,1,1],
	[1,1,1,1]
];
val mtrx3 = [
	[1,0,2],
	[~1,3,1]
];
val mtrx4 = [
	[3,1],
	[2,1],
	[1,0]
];

reduce(fn (acc,_) => acc + 1, 0, []) = 0;
reduce(fn (acc,_) => acc + 1, 0, [1,2,3,4]) = 4;
reduce(fn (acc,x) => acc + x, 0, [1,2,3,4,5]) = 15;
reduce(fn (acc,x) => acc + (x mod 2), 0, [1,2,3,4,5]) = 3;

squares([]) = [];
squares([1]) = [1];
squares([0,2]) = [0,4];
squares([1,2,3,4,5]) = [1,4,9,16,25];

only_even([]) = [];
only_even([1]) = [];
only_even([2]) = [2];
only_even([2,2,2,2,2]) = [2,2,2,2,2];
only_even([1,2,3,4,5,6,7,8,9]) = [2,4,6,8];

longest_string([]) = "";
longest_string(["","","","",""]) = "";
longest_string(["abc","a","bcabc","perica","rezeracirep", "pericarezer"]) = "rezeracirep";
longest_string(["a","b","c"]) = "a";

largest_string(["","","","",""]) = "";
largest_string(["abc","a","bcabc","perica","rezeracirep", "sup"]) = "sup";
largest_string(["abc","a","xerxes","perica","rezeracirep", "sup"]) = "xerxes";
largest_string(["a","b","c"]) = "c";

quicksort([]) = [];
quicksort([1]) = [1];
quicksort([1,2]) = [1,2];
quicksort([2,1]) = [1,2];
quicksort([2,3,1]) = [1,2,3];
quicksort([1,2,3,4,5,6,7,8,9]) = [1,2,3,4,5,6,7,8,9];
quicksort([9,8,7,6,5,4,3,2,1]) = [1,2,3,4,5,6,7,8,9];
quicksort([1,2,1,2,1,2]) = [1,1,1,2,2,2];
quicksort([0,0,0,0]) = [0,0,0,0];

dot([1])([1]) = 1;
dot([1,2])([1,2]) = 5;
dot([1,1])([1,1]) = 2;
dot([3,1,2])([2,3,1]) = 11;

transpose [] = [];
transpose [[1],[2],[3]] = [[1,2,3]];
transpose [[1,2],[2,3],[3,4]] = [[1,2,3],[2,3,4]];
transpose mtrx = [[1,1,1,1,1],[2,2,2,2,2],[3,3,3,3,3],[4,4,4,4,4],[5,5,5,5,5]];
transpose mtrx1 = mtrx2;
transpose mtrx2 = mtrx1;
transpose mtrx3 = [[1, ~1],[0,3],[2,1]];
transpose mtrx4 = [[3, 2,1],[1,1,0]];

multiply(mtrx1)(mtrx2) = [[2,2,2,2],[2,2,2,2],[2,2,2,2],[2,2,2,2]];
multiply(mtrx2)(mtrx1) = [[4,4],[4,4]];
multiply(mtrx3)(mtrx4) = [[5,1],[4,2]];

group []  = [];
group [1]  = [(1,1)];
group [1,1]  = [(1,2)];
group [1,1,1,1,1]  = [(1,5)];
group [1,1,2,2,2,3,3,4]  = [(1,2),(2,3),(3,2),(4,1)];
group [1,1,1,1,1,1,2,2,2,2,2,2,2] = [(1,6),(2,7)];
group ["a","a","b","c","c","c","c","c","d","e","f"] = [("a",2),("b",1),("c",5),("d",1),("e",1),("f",1)];

fun equiv x y = x mod 3 = y mod 3;
fun equiv2 x y = x mod 2 = y mod 2;
equivalence_classes equiv [] = [];
equivalence_classes equiv [1] = [[1]];
equivalence_classes equiv [1,2,3,4,5,6,7,8,9,0] = [[1,4,7],[2,5,8],[3,6,9,0]];
equivalence_classes equiv [0,1,2,3,4,5,6,7,8,9] = [[0,3,6,9],[1,4,7],[2,5,8]];
equivalence_classes equiv2 [1,2,3,4,5,6,7,8,9,0] = [[1,3,5,7,9],[2,4,6,8,0]];
equivalence_classes equiv2 [0,1,2,3,4,5,6,7,8,9] = [[0,2,4,6,8],[1,3,5,7,9]];*)