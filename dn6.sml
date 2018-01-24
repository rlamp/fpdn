signature COUNTER = 
sig
  val reset: unit -> unit
  val value: unit -> int
  val add1: unit -> unit
  val add2: unit -> unit
  val add3: unit -> unit
  val add4: unit -> unit
  val add5: unit -> unit
end;

structure Counter :> COUNTER = 
struct
  val count = ref 0

  val reset = fn () => (count := 0)
  val value = fn () => (!count)
  val add1 = fn () => (count := (!count) + 1)
  val add2 = fn () => (count := (!count) + 2)
  val add3 = fn () => (count := (!count) + 3)
  val add4 = fn () => (count := (!count) + 4)
  val add5 = fn () => (count := (!count) + 5)
end;

datatype tree = lf | br of (tree * int * tree)
fun optree operation current neutral t =
    case t of
        lf => neutral
    |   br (left, v, right) => operation(
                                optree operation current neutral left,
                                operation (
                                    optree operation current neutral right,
                                    current v
                                )
                            )  

val sum_tree = optree op+ (fn x => x) 0;
val prod_tree = optree op* (fn x => x) 1;
val count_tree = optree op+ (fn _ => 1) 1;

(* tests *)
Counter.value() = 0;
Counter.reset();
Counter.value() = 0;
Counter.add1();
Counter.value() = 1;
Counter.add2();
Counter.value() = 3;
Counter.add3();
Counter.value() = 6;
Counter.add4();
Counter.value() = 10;
Counter.add5();
Counter.value() = 15;
Counter.reset();
Counter.value() = 0;
Counter.reset();
Counter.value() = 0;
Counter.add5();
Counter.add5();
Counter.value() = 10;
Counter.add2();
Counter.add3();
Counter.value() = 15;
Counter.reset();
Counter.value() = 0;

sum_tree (br(br(lf,1,lf),3,br(lf,2,br(lf,1,lf)))) = 7;
prod_tree (br(br(lf,1,lf),3,br(lf,2,br(lf,1,lf)))) = 6;
count_tree (br(br(lf,1,lf),3,br(lf,2,br(lf,1,lf)))) = 9;
