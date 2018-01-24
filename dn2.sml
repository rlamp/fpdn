(*Naravna števila definiramo tako: Obstaja ničla (ZERO). Vsako naravno število
ima svojega naslednika (NEXT). Nič ni naslednik nobenega naravnega števila.
Če sta dve števili enaki, sta enaka tudi njuna naslednika.*)
datatype natural = 
    ZERO
    | NEXT of natural

(*Binarno iskalno drevo definiramo tako: Obstaja prazno iskalno drevo (lf).
Obstaja tudi veja (br), za katero poznamo vrednost elementa v njej ter obe
poddrevesi (bstree * int * bstree). Za poddrevesi velja, da so vsi elementi
znotraj levega poddrevesa (strogo) manjši od elementa v veji, vsi elementi
desnega poddrevesa pa so (strogo) večji.*)
datatype bstree = 
    lf
    | br of bstree * int * bstree


(*vrne celoštevilsko (int) predstavitev naravnega števila*)
fun toInt(a: natural): int =
    case a of
        ZERO => 0
        | NEXT n => 1 + toInt n


(*vrne naravno število, ki ustreza vsoti števil a in b · deluje naj direktno na
naravnih številih, brez pretvorbe v int*)
fun add(a: natural, b: natural): natural = 
    case a of
        ZERO => b
        | NEXT n => add(n, NEXT b)


(*  
    vrne najmanjši element drevesa, če ta obstaja
    CE JE BST JE TO NAJBOLJ LEVI ELEMENT BUT...
*)
fun min(tree: bstree): int option = 
    (*case tree of
        lf => NONE
        | br (l, n, _) => let
                val min_l = min l
            in
                if isSome(min_l)
                then min_l
                else SOME n
            end*)
    case tree of
        lf => NONE
        | br (l, n, r) => let
                val min_l = min l
                val min_r = min r
            in
                if (isSome min_l) andalso (isSome min_r)
                then SOME (Int.min(n, Int.min(valOf(min_l), valOf(min_r))))
                else if (isSome min_l)
                then SOME (Int.min(n, valOf(min_l)))
                else if (isSome min_r)
                then SOME (Int.min(n, valOf(min_r)))
                else SOME n
            end


(*
    vrne največji element drevesa, če ta obstaja
    CE JE BST JE TO NAJBOLJ DESNI ELEMENT BUT...
*)
fun max(tree: bstree): int option =
(*    case tree of
        lf => NONE
        | br (_, n, r) => let
                val max_r = max r
            in
                if isSome(max_r)
                then max_r
                else SOME n
            end*)
    case tree of
        lf => NONE
        | br (l, n, r) => let
                val max_l = max l
                val max_r = max r
            in
                if (isSome max_l) andalso (isSome max_r)
                then SOME (Int.max(n, Int.max(valOf(max_l), valOf(max_r))))
                else if (isSome max_l)
                then SOME (Int.max(n, valOf(max_l)))
                else if (isSome max_r)
                then SOME (Int.max(n, valOf(max_r)))
                else SOME n
            end


(*vrne true, če drevo vsebuje vejo s podano vrednostjo*)
fun contains(tree: bstree, x: int): bool =
    case tree of
        lf => false
        | br (l, n, r) => if n = x
            then true
            else contains(l, x) orelse contains(r, x)


(*vrne število listov (lf) v drevesu*)
fun countLeaves(tree: bstree): int =
    case tree of
        lf => 1
        | br(l, _, r) => (countLeaves l) + (countLeaves r)

(*vrne število vej (br) v drevesu*)
fun countBranches(tree: bstree): int = 
    case tree of
        lf => 0
        | br (l, _, r) => 1 + countBranches(l) + countBranches(r)


(*
    vrne seznam urejenih elementov podanega drevesa, v seznamu naj bo prvi 
    element min(tree), zadnji pa max(tree) · za združevanje seznamov lahko 
    uporabite operator @

    ALI LAHKO DOMNEVAMO DA JE DREVO PRAVO BST DREVO TJ. ELEMENTI GREJO PO VRSTI
*)
fun toList(tree: bstree): int list =
    case tree of
        lf => nil
        | br (l,n,r) => toList(l) @ [n] @ toList(r)


(*vrne true, če je podano drevo veljavno binarno iskalno drevo (glej definicijo
zgoraj)

KAJ TOREJ STROGO VECJE ALI VECJE ALI ENAKO???
*)
fun valid(tree: bstree): bool =
    case tree of
        lf => true
        | br(l, n, r) => let
                val l_max = max(l)
                val r_min = min(r)
            in
                if (isSome l_max) andalso (isSome r_min)
                then ((valOf l_max) < n) andalso (n < (valOf r_min)) 
                    andalso valid(l) andalso valid(r)
                else if (isSome l_max)
                then ((valOf l_max) < n) andalso valid(l)
                else if (isSome r_min)
                then (n < (valOf r_min)) andalso valid(r)
                else true
            end

(*
    vrne ime najstarejše osebe (če obstaja) v seznamu zapisov oblike {name="ime",
    age=starost}

    KAJ CE STA DVA ENAKO STARA????
*)
fun oldest(people: {age:int, name:string} list): string option =
    let
        fun oldest_person(people: {age:int, name:string} list) = 
            if null people
            then NONE
            else let
                    val cur = hd people
                    val old = oldest_person(tl people)
                in
                    if isSome old
                    then if (#age cur) > (#age (valOf old))
                        then SOME cur
                        else old
                    else SOME cur
                end
    in
        if null people
        then NONE
        else SOME (#name (valOf (oldest_person(people))))
    end

    

;;;; "type tests"  ;;;;
val test_toInt_type : natural -> int = toInt
val test_add_type : natural * natural -> natural = add
val test_min_type : bstree -> int option = min
val test_max_type : bstree -> int option = max
val test_contains_type : bstree * int -> bool = contains
val test_countLeaves_type : bstree -> int = countLeaves
val test_countBranches_type : bstree -> int = countBranches
val test_toList_type : bstree -> int list = toList
val test_valid_type : bstree -> bool = valid
val test_oldest_type : {age:int, name:string} list -> string option = oldest


(*val nic = ZERO;
val ena = NEXT(ZERO);
val dva = NEXT(NEXT(ZERO));
val tri = NEXT(NEXT(NEXT(ZERO)));
val stiri = NEXT(NEXT(NEXT(NEXT(ZERO))));
val pet = NEXT(NEXT(NEXT(NEXT(NEXT(ZERO)))));

toInt(nic) = 0;
toInt(ena) = 1;
toInt(dva) = 2;
toInt(tri) = 3;
toInt(stiri) = 4;
toInt(pet) = 5;

add(nic, nic) = nic;
add(ena, nic) = ena;
add(nic, ena) = ena;
add(ena, ena) = dva;
add(ena, dva) = tri;
add(dva, ena) = tri;
add(dva, tri) = pet;

val tree = br (br (br (lf, 2, lf), 7, lf), 9, br (br (lf, 13, lf), 21, 
    br (lf, 25, lf)));
val invalidTree = br (br (br (lf, 2, lf), 7, lf), 9, br (br (lf, ~13, lf),
     21, br (lf, 25, lf)));

min(lf) = NONE;
min(br(lf,1,lf)) = SOME 1;
min(tree) = SOME 2;

max(lf) = NONE;
max(br(lf,1,lf)) = SOME 1;
max(tree) = SOME 25;

contains(lf, 1) = false;
contains(br(lf,2,lf), 1) = false;
contains(br(lf,2,lf), 2) = true;
contains(br(lf,2,br(lf,3,lf)), 3) = true;
contains(br(br(lf,1,lf),2,lf), 1) = true;

contains(br(br(br(lf,~2,lf),~1,br(lf,0,lf)),1,br(br(lf,2,lf),3,lf)), ~1) = true;
contains(br(br(br(lf,~2,lf),~1,br(lf,0,lf)),1,br(br(lf,2,lf),3,lf)), 0) = true;
contains(br(br(br(lf,~2,lf),~1,br(lf,0,lf)),1,br(br(lf,2,lf),3,lf)), 2) = true;
contains(br(br(br(lf,~2,lf),~1,br(lf,0,lf)),1,br(br(lf,2,lf),3,lf)), 3) = true;
contains(br(br(br(lf,~2,lf),~1,br(lf,0,lf)),1,br(br(lf,2,lf),3,lf)), 4) = false;

countLeaves(lf) = 1;
countLeaves(br(lf,1,lf)) = 2;
countLeaves(tree) = 7;

countBranches(lf) = 0;
countBranches(br(lf,1,br(lf,2,lf))) = 2;
countBranches(tree) = 6;

toList(lf) = nil;
toList(br(lf,1,lf)) = [1];
toList(br(lf,1,br(lf,2,lf))) = [1,2];
toList(br(lf,1,br(br(lf,2,lf),3,lf))) = [1,2,3];
toList(br(br(br(lf,~2,lf),~1,br(lf,0,lf)),1,br(br(lf,2,lf),3,lf)))
    = [~2,~1,0,1,2,3];
toList(tree) = [2,7,9,13,21,25];

valid(lf) = true;
valid(br(lf,1,lf)) = true;
valid(br(lf,1,br(lf,2,lf))) = true;
valid(br(lf,1,br(br(lf,2,lf),3,lf))) = true;
valid(tree) = true;
valid(br(br(lf,0,lf),1,br(br(lf,2,lf),4,lf))) = true;

valid(invalidTree) = false;
valid(br(lf,2,br(lf,1,lf))) = false;
valid(br(lf,1,br(br(lf,3,lf),2,lf))) = false;
valid(br(br(lf,0,lf),1,br(br(lf,5,lf),4,lf))) = false;
valid(br(br(lf,1,lf),0,br(br(lf,2,lf),4,lf))) = false;
valid(br(br(br(lf,3,br(lf,5,lf)),4,br(br(lf,1,lf),2,lf)),2,lf)) = false;

val osebe = [{name="Zayed", age=122}, {name="Rashid", age=32},
    {name="Ali", age=12}, {name="Omar", age=32}, {name="Ahmed", age=14},
    {name="Muhammad", age=69}, {name="Hasan", age=54}, 
    {name="Abu Bakr", age=99}];
val osebe1 = [{name="Zayed", age=122}, {name="Rashid", age=32}, 
    {name="Ali", age=12}, {name="Omar", age=32}, {name="Ahmed", age=14}, 
    {name="Muhammad", age=69}, {name="Hasan", age=54}, 
    {name="Abu Bakr", age=199}];
val osebe2 = [{name="Zayed", age=122}, {name="Rashid", age=32}, 
    {name="Ali", age=12}, {name="Omar", age=32}, {name="Ahmed", age=14}, 
    {name="Abdullah", age=200}, {name="Muhammad", age=69}, 
    {name="Hasan", age=54}, {name="Abu Bakr", age=199}];

oldest([]) = NONE;
oldest([{name="Zayed", age=111}, {name="Rashid", age=111}]) = SOME "Rashid";
oldest(osebe) = SOME "Zayed";
oldest(osebe1) = SOME "Abu Bakr";
oldest(osebe2) = SOME "Abdullah";*)