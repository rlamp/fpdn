(*vrne fakulteto števila n, n >= 0*)
fun factorial(n: int): int =
	if n = 0 orelse n = 1
	then 1
	else n * factorial(n-1)

(*vrne n-to potenco števila x, n >= 0*)
fun power(x: int, n: int): int =
	if n = 0
	then 1
	else x * power(x, n-1)

(*vrne največji skupni delitelj pozitivnih števil a in b*)
fun gcd(a: int, b: int): int =
	if b = 0
	then a
	else gcd(b, a mod b)

(*vrne dolžino seznama*)
fun len(xs: int list):int =
	if null xs
	then 0
	else 1 + len(tl xs)

(*vrne SOME zadnji element seznama, če je seznam prazen vrne NONE*)
fun last(xs: int list):int option =
	if null xs
	then NONE
	else if null (tl xs)
		then SOME (hd xs)
		else last (tl xs)

(*vrne SOME n-ti element seznama; prvi element ima indeks 0; če indeks ni veljaven vrne NONE*)
fun nth(xs: int list, n: int):int option =
	if null xs
	then NONE
	else if n = 0
		then SOME (hd xs)
		else nth(tl xs, n-1)

(*vrne nov seznam, ki je tak kot vhodni, le da je na n-to mesto vstavljen element x; prvo mesto v seznamu ima indeks 0; predpostavite lahko, da je indeks veljaven*)
fun insert(xs: int list, n: int, x:int):int list =
	if n = 0
	then x::xs
	else (hd xs)::insert(tl xs, n-1, x)

(*vrne nov seznam, ki je tak kot vhodni, le da so vse pojavitve elementa x odstranjene*)
fun delete(xs: int list, x:int):int list =
	if null xs
	then nil
	else if (hd xs) = x
		then delete(tl xs, x)
		else (hd xs)::delete(tl xs, x)

(*vrne obrnjen seznam; v pomoč si lahko spišete še funkcijo append, ki doda na konec seznama*)
fun reverse(xs:int list):int list =
	let
		fun append(xs: int list, x: int) =
			if null xs
			then x::nil
			else (hd xs)::append(tl xs, x)
	in
		if null xs
		then nil
		else append(reverse(tl xs), hd xs)
	end

(*vrne true, če je podani seznam palindrom*)
fun palindrome(xs: int list):bool =
	let
		val rev = reverse(xs)
	in
		if xs = rev
		then true
		else false
	end


(*test*)
;;;; "type tests"  ;;;;
val test_factorial_type : int -> int = factorial
val test_power_type : int * int -> int = power
val test_gcd_type : int * int -> int = gcd
val test_len_type : int list -> int = len
val test_last_type : int list -> int option = last
val test_nth_type : int list * int -> int option = nth
val test_insert_type : int list * int * int -> int list = insert
val test_delete_type : int list * int -> int list = delete
val test_reverse_type : int list -> int list = reverse
val test_palindrome_type : int list -> bool = palindrome;

(*factorial (0) = 1;
factorial (1) = 1;
factorial (2) = 2;
factorial (3) = 6;
factorial (4) = 24;
factorial (5) = 120;
factorial (6) = 720;
factorial (7) = 5040;
factorial (8) = 40320;
factorial (9) = 362880;
factorial (10) = 3628800;
factorial (11) = 39916800;
factorial (12) = 479001600;

power(~3,0) = 1;
power(~2,0) = 1;
power(~1,0) = 1;
power(0,0) = 1;
power(1,0) = 1;
power(2,0) = 1;
power(3,0) = 1;
power(~3,1) = ~3;
power(~2,1) = ~2;
power(~1,1) = ~1;
power(0,1) = 0;
power(1,1) = 1;
power(2,1) = 2;
power(3,1) = 3;
power(~3,2) = 9;
power(~2,2) = 4;
power(~1,2) = 1;
power(0,2) = 0;
power(1,2) = 1;
power(2,2) = 4;
power(3,2) = 9;
power(~3,3) = ~27;
power(~2,3) = ~8;
power(~1,3) = ~1;
power(0,3) = 0;
power(1,3) = 1;
power(2,3) = 8;
power(3,3) = 27;

gcd(1,1)=1;
gcd(4,2)=2;
gcd(4,3)=1;
gcd(8,4)=4;
gcd(10,4)=2;
gcd(10,8)=2;
gcd(10,5)=5;
gcd(12,8)=4;
gcd(121,33)=11;

len([])=0;
len([1])=1;
len([2,2])=2;
len([2,2,2])=3;
len([1,2,3,4,5])=5;
len([5,5,5,5,5])=5;

last([])=NONE;
last([1])=SOME 1;
last([1,2])=SOME 2;
last([1,1,1,1,1,1,2])=SOME 2;
last([1,2,3,4])=SOME 4;

nth([],0)=NONE;
nth([],1)=NONE;
nth([1,2,3],~1)=NONE;
nth([1,2,3],~2)=NONE;
nth([1,2,3],0)=SOME 1;
nth([1,2,3],1)=SOME 2;
nth([1,2,3],2)=SOME 3;
nth([0,1,2,3,4,5,6,7,8,9],8)=SOME 8;

insert([0,1,2,3,4],0,41)=[41,0,1,2,3,4];
insert([0,1,2,3,4],1,41)=[0,41,1,2,3,4];
insert([0,1,2,3,4],2,41)=[0,1,41,2,3,4];
insert([0,1,2,3,4],3,41)=[0,1,2,41,3,4];
insert([0,1,2,3,4],4,41)=[0,1,2,3,41,4];
insert([0,1,2,3,4],5,41)=[0,1,2,3,4,41];

delete([0,1,2,3,4,5,6],0)=[1,2,3,4,5,6];
delete([0,1,2,3,4,5,6],3)=[0,1,2,4,5,6];
delete([0,1,2,3,4,5,6],6)=[0,1,2,3,4,5];
delete([],1)=[];
delete([1,1,1,1,1],1)=[];
delete([1,1,1,1,1,2],1)=[2];
delete([1,1,1,1,2,1],1)=[2];
delete([2,2,2,2,2,2],1)=[2,2,2,2,2,2];

reverse([])=[];
reverse([1])=[1];
reverse([1,2])=[2,1];
reverse([1,2,3])=[3,2,1];
reverse([1,2,3,4])=[4,3,2,1];

palindrome([])=true;
palindrome([1])=true;
palindrome([1,1])=true;
palindrome([1,2,3,2,1])=true;
palindrome([1,2,3,3,2,1])=true;
palindrome([0,1])=false;
palindrome([1,0,2])=false;*)