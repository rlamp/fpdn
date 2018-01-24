
fun next (n) =
	n + 1;

fun add (a, b) =
	a + b;


;;;; "type tests"  ;;;;
val test_next_type:int->int = next;
val test_add_type:int*int->int = add;


(*next(0) = 1;
next(1) = 2;
next(3) = 3;

add(0,0) = 0;
add(0,1) = 1;
add(3,7) = 10;*)
