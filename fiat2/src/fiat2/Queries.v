Require Import fiat2.Language.
Require Import fiat2.Elaborate.
Require Import fiat2.Notations.
Require Import fiat2.Interpret.
Require Import fiat2.SamplePrograms.
Require Import fiat2.Optimize.
Require Import coqutil.Map.Interface coqutil.Map.SortedListString coqutil.Map.Properties.
Require Import coqutil.Datatypes.Result.
Require Import Coq.Lists.List.
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellString.
Require Import ExtrHaskellZInteger.
Require Import bedrock2.PrintString.
Import ResultMonadNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.


Section Queries_Section.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.
  Instance tenv : map.map string (type * bool) := SortedListString.map _.
  Instance tenv_ok : map.ok tenv := SortedListString.ok _.
  Instance locals : map.map string {t & interp_type t} := SortedListString.map _.
  Instance locals_ok : map.ok locals := SortedListString.ok _.

  Fixpoint record (l : list (string * type)) : type :=
    match l with
    | nil => TEmpty
    | (s, t) :: xs => TPair s t (record xs)
    end.

  Compute interp_type (record (("a", TString) :: ("b", TInt) :: nil)).

  Fixpoint from_tuple {l : list (string * type)} (tp : interp_type (record l)) : expr (record l) :=
    match l return interp_type (record l) -> expr (record l) with
    | nil => fun _ => EAtom AEmpty
    | (s, t) :: xs => fun tp => let (a, b) := tp in EBinop (OPair s _ _) (reify t a) (from_tuple (snd tp))
    end tp.

  Definition artist := record (("id", TInt) :: ("name", TString) :: nil).

  Definition artist_1 := from_tuple ((1, ("AC/DC", tt)) : interp_type artist).
  Definition artist_2 := from_tuple ((2, ("Accept", tt)) : interp_type artist).
  Definition artist_3 := from_tuple ((3, ("Aerosmith", tt)) : interp_type artist).
  Definition artist_4 := from_tuple ((4, ("Alanis Morisette", tt)) : interp_type artist).

  Definition artists := listify (artist_1 :: artist_2 :: artist_3 :: artist_4 :: nil).

  Compute interp_expr map.empty map.empty artists.

  Definition artists_filter_q :=
    EFlatmap artists "x" (
      EIf (EBinop OLess (EUnop (OFst _ _ _) (ELoc artist "x")) (EAtom (AInt 3)))
        (EBinop (OCons artist) (ELoc artist "x") (EAtom (ANil _)))
        (EAtom (ANil _))
    ).

  Compute artists_filter_q.

  Definition artists_filter_q' :=
    EFlatmap artists "x" (EBinop (OCons _) (EUnop (OFst "id" _ (TPair "name" TString TEmpty)) (EVar _ "x")) (EAtom (ANil TInt))).

  Compute interp_expr map.empty map.empty artists_filter_q.

  Definition test := PEProj (PERecord (("a", PEAtom (PAInt 1)) :: ("b", PEAtom (PAInt 2)) :: nil)) "a".

  Fixpoint pexpr_list (t : type) (l : list (pexpr)) : pexpr :=
    match l with
    | nil => PEAtom (PANil t)
    | x :: xs => PEBinop POCons x (pexpr_list t xs)
    end.

  Fixpoint as_pexpr {t : type} (v : interp_type t) : pexpr :=
    match t return interp_type t -> pexpr with
    | TWord => fun v => PEAtom (PAWord (word.unsigned v))
    | TInt => fun v => PEAtom (PAInt v)
    | TBool => fun v => PEAtom (PABool v)
    | TString => fun v => PEAtom (PAString v)
    | TPair _ _ _  => fun v => PEBinop POPair (as_pexpr (fst v)) (as_pexpr (snd v))
    | TEmpty => fun v => PERecord nil
    | TList t => fun v => pexpr_list t (map as_pexpr v)
    end v.

  Fixpoint zip {A B} (l1 : list A) (l2 : list B) : list (A * B) :=
    match l1, l2 with
    | x :: xs, y :: ys => (x, y) :: zip xs ys
    | _, _ => nil
    end.

  Fixpoint pexperify {l : list (string * type)} (tp : interp_type (record l)) : list pexpr :=
    match l return interp_type (record l) -> list pexpr  with
    | nil => fun _ => nil
    | (s, t) :: xs => fun tp => as_pexpr (fst tp) :: (pexperify (snd tp))
    end tp.

  Definition from_tuple' {l : list (string * type)} (tp : interp_type (record l)) : pexpr :=
    PERecord (zip (map fst l) (pexperify tp)).

  Definition artist_1' := from_tuple' ((1, ("AC/DC", tt)) : interp_type artist).
  Definition artist_2' := from_tuple' ((2, ("Accept", tt)) : interp_type artist).
  Definition artist_3' := from_tuple' ((3, ("Aerosmith", tt)) : interp_type artist).
  Definition artist_4' := from_tuple' ((4, ("Alanis Morisette", tt)) : interp_type artist).

  Definition artists' := pexpr_list artist (artist_1' :: artist_2' :: artist_3' :: artist_4' :: nil).

  Compute artists'.

  Local Open Scope fiat2_scope.

  (* SELECT * FROM artists WHERE id < n *)
  Definition filter_test (n : Z) := <{
    "ans" <- flatmap artists' "x" (if "x"["id"] < <[ PAInt n ]> then ["x"] else nil[artist]);
    "json" <- <[ PEElaborated _ (generate_json _ (ELoc (List artist) "ans")) ]>
    }>.


  (* SELECT SUM(id) FROM artists *)
  Definition fold_test := <{
    "ans" <- fold artists' 0 "x" "y" ("x"["id"] + "y");
    "json" <- <[ PEElaborated _ (generate_json _ (ELoc Int "ans")) ]>
  }>.
  Compute run_program ((("json", (TString, true)) :: ("ans", (TInt, true)) :: nil)) fold_test.

  (* SELECT name FROM artists WHERE id < 3 *)
  Definition select_test := <{
    "ans" <- flatmap (flatmap artists' "x" (if "x"["id"] < 3 then ["x"] else nil[artist])) "y" ["y"["name"]]
  }>.
  Compute run_program ((("ans", (TList TString, true)) :: nil)) select_test.

  Definition select_test_elaborated' : command :=
    Eval cbv in match elaborate_command (map.of_list (("ans", (TList TString, true))::nil)) select_test with
    | Success x => x
    | _ => _
    end.

  Definition select_test_elaborated := Eval cbv in match select_test_elaborated' with
                                                    | CGets _ e => e
                                                    | _ => _
                                                    end.
  Compute select_test_elaborated.
  Compute flatmap_flatmap select_test_elaborated.
  Compute interp_expr map.empty map.empty select_test_elaborated.

  Definition album := record (("album_id", TInt) :: ("title", TString) :: ("artist_id", TInt) :: nil).
  Definition albums := pexpr_list album (map from_tuple'
    ((1, ("For Those About To Rock We Salute You", (1, tt)))
      :: (2, ("Balls to the Wall", (2, tt)))
      :: (3, ("Restless and Wild", (2, tt)))
      :: (4, ("Let There Be Rock", (1, tt)))
      :: (5, ("Big Ones", (3, tt)))
      :: (6, ("Jaggged Little Pill", (4, tt)))
      :: (7, ("Facelift", (5, tt)))
      :: nil
      : list (interp_type album)
           )).

  Definition t := TPair "0" album (TPair "1" artist Unit).

  (* SELECT * FROM albums JOIN artists WHERE album_id = id *)
  Definition join_test := <{
    "ans" <- flatmap (flatmap albums "y" (flatmap artists' "z" [("y", "z")])) "x"
    (if fst("x")["artist_id"] == snd("x")["id"] then ["x"] else nil[t])
  }>.
  Compute run_program ((("ans", (TList (t), true))) :: nil) join_test.

  (* SELECT * FROM albums WHERE album_id = n JOIN artists WHERE album_id = id *)
  Definition filter_albums_with_artist n := <{
    "ans" <- flatmap (flatmap albums "y" (flatmap artists' "z" [("y", "z")])) "x"
    (if (fst("x")["artist_id"] == snd("x")["id"]) && (fst("x")["album_id"] == n) then ["x"] else nil[t]);
    "json" <- <[ PEElaborated _ (generate_json _ (ELoc (List (record (("0", album) :: ("1", artist) :: nil))) "ans")) ]>
  }>.
  Compute run_program (("json", (TString, true)) :: (("ans", (TList t, true))) :: nil) (filter_albums_with_artist 7).

  Compute (elaborate_command (map.of_list (("ans", (TList t, true))::nil)) join_test).
  Definition tmp' : command :=
    Eval cbv in match elaborate_command (map.of_list (("ans", (TList t, true))::nil)) join_test with
    | Success x => x
    | _ => _
    end.

  Definition export_prog (l : list (string * (type * bool))) (p : pcommand) :=
    let output := run_program (*word := Naive.word64*) l p
    in let getJsonStrs := flat_map (fun p =>
        match p return list string with
        | ("json", existT _ String s) => s :: nil
        | _ => nil
        end)
    in match output with
       | Success locals => match getJsonStrs locals with
                           | str :: nil => str
                           | _ => "Error: Program did not output json str"
                           end
       | Failure s => "Error: Program errored"
       end.

  (* Data from https://www.sqltutorial.org/sql-sample-database/ *)
  Definition db_regions_fields := (("region_id", TInt) :: ("region_name", TString) :: nil).
  Definition db_regions := pexpr_list (record db_regions_fields) (map (@from_tuple' db_regions_fields) (
    (1, ("Europe", tt)) ::
    (2, ("Americas", tt)) ::
    (3, ("Asia", tt)) ::
    (4, ("Middle East and Africa", tt)) ::
    nil)).

  (*Data for the table countries *)
  Definition db_countries_fields := ("country_id", TString) :: ("country_name", TString) :: ("region_id", TInt) :: nil.
  Definition db_countries := pexpr_list (record db_countries_fields) (map (@from_tuple' db_countries_fields) (
    ("AR", ("Argentina", (2, tt))) ::
    ("AU", ("Australia", (3, tt))) ::
    ("BE", ("Belgium", (1, tt))) ::
    ("BR", ("Brazil", (2, tt))) ::
    ("CA", ("Canada", (2, tt))) ::
    ("CH", ("Switzerland", (1, tt))) ::
    ("CN", ("China", (3, tt))) ::
    ("DE", ("Germany", (1, tt))) ::
    ("DK", ("Denmark", (1, tt))) ::
    ("EG", ("Egypt", (4, tt))) ::
    ("FR", ("France", (1, tt))) ::
    ("HK", ("HongKong", (3, tt))) ::
    ("IL", ("Israel", (4, tt))) ::
    ("IN", ("India", (3, tt))) ::
    ("IT", ("Italy", (1, tt))) ::
    ("JP", ("Japan", (3, tt))) ::
    ("KW", ("Kuwait", (4, tt))) ::
    ("MX", ("Mexico", (2, tt))) ::
    ("NG", ("Nigeria", (4, tt))) ::
    ("NL", ("Netherlands", (1, tt))) ::
    ("SG", ("Singapore", (3, tt))) ::
    ("UK", ("United Kingdom", (1, tt))) ::
    ("US", ("United States of America", (2, tt))) ::
    ("ZM", ("Zambia", (4, tt))) ::
    ("ZW", ("Zimbabwe", (4, tt))) ::
    nil)).

  (*Data for the table locations *)
  Definition db_locations_fields_list := ("location_id", TInt) :: ("street_address", TString) :: ("postal_code", TString) :: ("city", TString) :: ("state_province", TString) :: ("country_id", TString) :: nil.
  Definition db_locations_fields := record db_locations_fields_list.
  Definition db_locations := pexpr_list (record db_locations_fields_list) (map (@from_tuple' db_locations_fields_list) (
    (1400, ("2014 Jabberwocky Rd", ("26192", ("Southlake", ("Texas", ("US", tt)))))) ::
    (1500, ("2011 Interiors Blvd", ("99236", ("South San Francisco", ("California", ("US", tt)))))) ::
    (1700, ("2004 Charade Rd", ("98199", ("Seattle", ("Washington", ("US", tt)))))) ::
    (1800, ("147 Spadina Ave", ("M5V 2L7", ("Toronto", ("Ontario", ("CA", tt)))))) ::
    (2400, ("8204 Arthur St", ("NULL", ("London", ("NULL", ("UK", tt)))))) ::
    (2500, ("Magdalen Centre, The Oxford Science Park", ("OX9 9ZB", ("Oxford", ("Oxford", ("UK", tt)))))) ::
    (2700, ("Schwanthalerstr. 7031", ("80925", ("Munich", ("Bavaria", ("DE", tt)))))) ::
    nil)).

  (*Data for the table jobs *)
  Definition db_jobs_fields_list := ("job_id", TInt) :: ("job_title", TString) :: ("min_salary", TInt) :: ("max_salary", TInt) :: nil.
  Definition db_jobs_fields := record db_jobs_fields_list.
  Definition db_jobs := pexpr_list (record db_jobs_fields_list) (map (@from_tuple' db_jobs_fields_list) (
    (1, ("Public Accountant", (4200, (9000, tt)))) ::
    (2, ("Accounting Manager", (8200, (16000, tt)))) ::
    (3, ("Administration Assistant", (3000, (6000, tt)))) ::
    (4, ("President", (20000, (40000, tt)))) ::
    (5, ("Administration Vice President", (15000, (30000, tt)))) ::
    (6, ("Accountant", (4200, (9000, tt)))) ::
    (7, ("Finance Manager", (8200, (16000, tt)))) ::
    (8, ("Human Resources Representative", (4000, (9000, tt)))) ::
    (9, ("Programmer", (4000, (10000, tt)))) ::
    (10, ("Marketing Manager", (9000, (15000, tt)))) ::
    (11, ("Marketing Representative", (4000, (9000, tt)))) ::
    (12, ("Public Relations Representative", (4500, (10500, tt)))) ::
    (13, ("Purchasing Clerk", (2500, (5500, tt)))) ::
    (14, ("Purchasing Manager", (8000, (15000, tt)))) ::
    (15, ("Sales Manager", (10000, (20000, tt)))) ::
    (16, ("Sales Representative", (6000, (12000, tt)))) ::
    (17, ("Shipping Clerk", (2500, (5500, tt)))) ::
    (18, ("Stock Clerk", (2000, (5000, tt)))) ::
    (19, ("Stock Manager", (5500, (8500, tt)))) ::
    nil)).

  (*Data for the table departments *)
  Definition db_departments_fields_list := ("department_id", TInt) :: ("department_name", TString) :: ("location_id", TInt) :: nil.
  Definition db_departments_fields := record db_departments_fields_list.
  Definition db_departments := pexpr_list (record db_departments_fields_list) (map (@from_tuple' db_departments_fields_list) (
    (1, ("Administration", (1700, tt))) ::
    (2, ("Marketing", (1800, tt))) ::
    (3, ("Purchasing", (1700, tt))) ::
    (4, ("Human Resources", (2400, tt))) ::
    (5, ("Shipping", (1500, tt))) ::
    (6, ("IT", (1400, tt))) ::
    (7, ("Public Relations", (2700, tt))) ::
    (8, ("Sales", (2500, tt))) ::
    (9, ("Executive", (1700, tt))) ::
    (10, ("Finance", (1700, tt))) ::
    (11, ("Accounting", (1700, tt))) ::
    nil)).

  (*Data for the table employees *)
  Definition db_employees_fields_list := ("employee_id", TInt) :: ("first_name", TString) :: ("last_name", TString) :: ("email", TString) :: ("phone_number", TString) :: ("hire_date", TString) :: ("job_id", TInt) :: ("salary", TInt) :: ("manager_id", TInt) :: ("department_id", TInt) :: nil.
  Definition db_employees_fields := record db_employees_fields_list.
  Definition db_employees := pexpr_list (record db_employees_fields_list) (map (@from_tuple' db_employees_fields_list) (
    (100, ("Steven", ("King", ("steven.king@sqltutorial.org", ("515.123.4567", ("1987-06-17", (4, (24000, (100, (9, tt)))))))))) ::
    (101, ("Neena", ("Kochhar", ("neena.kochhar@sqltutorial.org", ("515.123.4568", ("1989-09-21", (5, (17000, (100, (9, tt)))))))))) ::
    (102, ("Lex", ("De Haan", ("lex.de haan@sqltutorial.org", ("515.123.4569", ("1993-01-13", (5, (17000, (100, (9, tt)))))))))) ::
    (103, ("Alexander", ("Hunold", ("alexander.hunold@sqltutorial.org", ("590.423.4567", ("1990-01-03", (9, (9000, (102, (5, tt)))))))))) ::
    (104, ("Bruce", ("Ernst", ("bruce.ernst@sqltutorial.org", ("590.423.4568", ("1991-05-21", (9, (6000, (103, (6, tt)))))))))) ::
    (105, ("David", ("Austin", ("david.austin@sqltutorial.org", ("590.423.4569", ("1997-06-25", (9, (4800, (103, (6, tt)))))))))) ::
    (106, ("Valli", ("Pataballa", ("valli.pataballa@sqltutorial.org", ("590.423.4560", ("1998-02-05", (9, (4800, (103, (6, tt)))))))))) ::
    (107, ("Diana", ("Lorentz", ("diana.lorentz@sqltutorial.org", ("590.423.5567", ("1999-02-07", (9, (4200, (103, (6, tt)))))))))) ::
    (108, ("Nancy", ("Greenberg", ("nancy.greenberg@sqltutorial.org", ("515.124.4569", ("1994-08-17", (7, (12000, (101, (10, tt)))))))))) ::
    (109, ("Daniel", ("Faviet", ("daniel.faviet@sqltutorial.org", ("515.124.4169", ("1994-08-16", (6, (9000, (108, (10, tt)))))))))) ::
    (110, ("John", ("Chen", ("john.chen@sqltutorial.org", ("515.124.4269", ("1997-09-28", (6, (8200, (108, (10, tt)))))))))) ::
    (111, ("Ismael", ("Sciarra", ("ismael.sciarra@sqltutorial.org", ("515.124.4369", ("1997-09-30", (6, (7700, (108, (10, tt)))))))))) ::
    (112, ("Jose Manuel", ("Urman", ("jose manuel.urman@sqltutorial.org", ("515.124.4469", ("1998-03-07", (6, (7800, (108, (10, tt)))))))))) ::
    (113, ("Luis", ("Popp", ("luis.popp@sqltutorial.org", ("515.124.4567", ("1999-12-07", (6, (6900, (108, (10, tt)))))))))) ::
    (114, ("Den", ("Raphaely", ("den.raphaely@sqltutorial.org", ("515.127.4561", ("1994-12-07", (14, (11000, (100, (3, tt)))))))))) ::
    (115, ("Alexander", ("Khoo", ("alexander.khoo@sqltutorial.org", ("515.127.4562", ("1995-05-18", (13, (3100, (114, (3, tt)))))))))) ::
    (116, ("Shelli", ("Baida", ("shelli.baida@sqltutorial.org", ("515.127.4563", ("1997-12-24", (13, (2900, (114, (3, tt)))))))))) ::
    (117, ("Sigal", ("Tobias", ("sigal.tobias@sqltutorial.org", ("515.127.4564", ("1997-07-24", (13, (2800, (114, (3, tt)))))))))) ::
    (118, ("Guy", ("Himuro", ("guy.himuro@sqltutorial.org", ("515.127.4565", ("1998-11-15", (13, (2600, (114, (3, tt)))))))))) ::
    (119, ("Karen", ("Colmenares", ("karen.colmenares@sqltutorial.org", ("515.127.4566", ("1999-08-10", (13, (2500, (114, (3, tt)))))))))) ::
    (120, ("Matthew", ("Weiss", ("matthew.weiss@sqltutorial.org", ("650.123.1234", ("1996-07-18", (19, (8000, (100, (5, tt)))))))))) ::
    (121, ("Adam", ("Fripp", ("adam.fripp@sqltutorial.org", ("650.123.2234", ("1997-04-10", (19, (8200, (100, (5, tt)))))))))) ::
    (122, ("Payam", ("Kaufling", ("payam.kaufling@sqltutorial.org", ("650.123.3234", ("1995-05-01", (19, (7900, (100, (5, tt)))))))))) ::
    (123, ("Shanta", ("Vollman", ("shanta.vollman@sqltutorial.org", ("650.123.4234", ("1997-10-10", (19, (6500, (100, (5, tt)))))))))) ::
    (126, ("Irene", ("Mikkilineni", ("irene.mikkilineni@sqltutorial.org", ("650.124.1224", ("1998-09-28", (18, (2700, (120, (5, tt)))))))))) ::
    (145, ("John", ("Russell", ("john.russell@sqltutorial.org", ("NULL", ("1996-10-01", (15, (14000, (100, (8, tt)))))))))) ::
    (146, ("Karen", ("Partners", ("karen.partners@sqltutorial.org", ("NULL", ("1997-01-05", (15, (13500, (100, (8, tt)))))))))) ::
    (176, ("Jonathon", ("Taylor", ("jonathon.taylor@sqltutorial.org", ("NULL", ("1998-03-24", (16, (8600, (100, (8, tt)))))))))) ::
    (177, ("Jack", ("Livingston", ("jack.livingston@sqltutorial.org", ("NULL", ("1998-04-23", (16, (8400, (100, (8, tt)))))))))) ::
    (178, ("Kimberely", ("Grant", ("kimberely.grant@sqltutorial.org", ("NULL", ("1999-05-24", (16, (7000, (100, (8, tt)))))))))) ::
    (179, ("Charles", ("Johnson", ("charles.johnson@sqltutorial.org", ("NULL", ("2000-01-04", (16, (6200, (100, (8, tt)))))))))) ::
    (192, ("Sarah", ("Bell", ("sarah.bell@sqltutorial.org", ("650.501.1876", ("1996-02-04", (17, (4000, (123, (5, tt)))))))))) ::
    (193, ("Britney", ("Everett", ("britney.everett@sqltutorial.org", ("650.501.2876", ("1997-03-03", (17, (3900, (123, (5, tt)))))))))) ::
    (200, ("Jennifer", ("Whalen", ("jennifer.whalen@sqltutorial.org", ("515.123.4444", ("1987-09-17", (3, (4400, (101, (1, tt)))))))))) ::
    (201, ("Michael", ("Hartstein", ("michael.hartstein@sqltutorial.org", ("515.123.5555", ("1996-02-17", (10, (13000, (100, (2, tt)))))))))) ::
    (202, ("Pat", ("Fay", ("pat.fay@sqltutorial.org", ("603.123.6666", ("1997-08-17", (11, (6000, (201, (2, tt)))))))))) ::
    (203, ("Susan", ("Mavris", ("susan.mavris@sqltutorial.org", ("515.123.7777", ("1994-06-07", (8, (6500, (101, (4, tt)))))))))) ::
    (204, ("Hermann", ("Baer", ("hermann.baer@sqltutorial.org", ("515.123.8888", ("1994-06-07", (12, (10000, (101, (7, tt)))))))))) ::
    (205, ("Shelley", ("Higgins", ("shelley.higgins@sqltutorial.org", ("515.123.8080", ("1994-06-07", (2, (12000, (101, (11, tt)))))))))) ::
    (206, ("William", ("Gietz", ("william.gietz@sqltutorial.org", ("515.123.8181", ("1994-06-07", (1, (8300, (205, (11, tt)))))))))) ::
    nil)).


  (*Data for the table dependents *)
  Definition db_dependents_fields_list := ("dependent_id", TInt) :: ("first_name", TString) :: ("last_name", TString) :: ("relationship", TString) :: ("employee_id", TInt) :: nil.
  Definition db_dependents_fields := record db_dependents_fields_list.
  Definition db_dependents := pexpr_list (record db_dependents_fields_list) (map (@from_tuple' db_dependents_fields_list) (
    (1, ("Penelope", ("Gietz", ("Child", (206, tt))))) ::
    (2, ("Nick", ("Higgins", ("Child", (205, tt))))) ::
    (3, ("Ed", ("Whalen", ("Child", (200, tt))))) ::
    (4, ("Jennifer", ("King", ("Child", (100, tt))))) ::
    (5, ("Johnny", ("Kochhar", ("Child", (101, tt))))) ::
    (6, ("Bette", ("De Haan", ("Child", (102, tt))))) ::
    (7, ("Grace", ("Faviet", ("Child", (109, tt))))) ::
    (8, ("Matthew", ("Chen", ("Child", (110, tt))))) ::
    (9, ("Joe", ("Sciarra", ("Child", (111, tt))))) ::
    (10, ("Christian", ("Urman", ("Child", (112, tt))))) ::
    (11, ("Zero", ("Popp", ("Child", (113, tt))))) ::
    (12, ("Karl", ("Greenberg", ("Child", (108, tt))))) ::
    (13, ("Uma", ("Mavris", ("Child", (203, tt))))) ::
    (14, ("Vivien", ("Hunold", ("Child", (103, tt))))) ::
    (15, ("Cuba", ("Ernst", ("Child", (104, tt))))) ::
    (16, ("Fred", ("Austin", ("Child", (105, tt))))) ::
    (17, ("Helen", ("Pataballa", ("Child", (106, tt))))) ::
    (18, ("Dan", ("Lorentz", ("Child", (107, tt))))) ::
    (19, ("Bob", ("Hartstein", ("Child", (201, tt))))) ::
    (20, ("Lucille", ("Fay", ("Child", (202, tt))))) ::
    (21, ("Kirsten", ("Baer", ("Child", (204, tt))))) ::
    (22, ("Elvis", ("Khoo", ("Child", (115, tt))))) ::
    (23, ("Sandra", ("Baida", ("Child", (116, tt))))) ::
    (24, ("Cameron", ("Tobias", ("Child", (117, tt))))) ::
    (25, ("Kevin", ("Himuro", ("Child", (118, tt))))) ::
    (26, ("Rip", ("Colmenares", ("Child", (119, tt))))) ::
    (27, ("Julia", ("Raphaely", ("Child", (114, tt))))) ::
    (28, ("Woody", ("Russell", ("Child", (145, tt))))) ::
    (29, ("Alec", ("Partners", ("Child", (146, tt))))) ::
    (30, ("Sandra", ("Taylor", ("Child", (176, tt))))) ::
    nil)).

  Definition field_product (t1 t2 : type) : type := record (("0", t1) :: ("1", t2) :: nil).
  Local Open Scope fiat2_scope.
  (* SELECT * FROM employees JOIN jobs WHERE employees.job_id == job.id and jobs.title = "Programmer" *)

  Definition select_programmers := <{
    let "ans" := flatmap db_employees "empl"
      (flatmap db_jobs "job"
        (if ("empl"["job_id"] == "job"["job_id"]) && ("job"["job_title"] == <[PAString "Programmer"]>)
          then [("empl", "job")] else nil[field_product db_employees_fields db_jobs_fields])
      ) in
    "json" <- <[ PEElaborated _ (generate_json _ (EVar (List (field_product db_employees_fields db_jobs_fields)) "ans")) ]>
  }>.
  Goal True.
    let s := eval vm_compute in (export_prog (("json", (TString, true)) :: nil) select_programmers)%string in
    print_string s.
  Abort.

  Definition programmer_salary := <{
    let "ans" := flatmap db_departments "department"
      (flatmap db_employees "empl"
          (flatmap db_jobs "job"
          (if ("empl"["job_id"] == "job"["job_id"]) && ("job"["job_title"] == <[PAString "Programmer"]>) &&
              ("empl"["department_id"] == "department"["department_id"])
            then [("empl", ("job", "department"))]
            else nil[field_product db_employees_fields (field_product db_jobs_fields db_departments_fields)])
        ))
    in "json" <- <[ PEElaborated _ (generate_json _ (EVar (List (field_product db_employees_fields (field_product db_jobs_fields db_departments_fields))) "ans")) ]>
  }>.
  Goal True.
    let s := eval vm_compute in (export_prog (("json", (TString, true)) :: nil) programmer_salary)%string in
    print_string s.
  Abort.

  Definition tx_prog_type := field_product db_employees_fields (field_product db_jobs_fields (field_product db_departments_fields db_locations_fields)).
  Definition tx_programmers := <{
    let "ans" := flatmap db_employees "empl"
      (flatmap db_jobs "job"
      (if ("empl"["job_id"] == "job"["job_id"]) && ("job"["job_title"] == <[PAString "Programmer"]>) then
        (flatmap db_departments "department"
          (if ("empl"["department_id"] == "department"["department_id"]) then
            (flatmap db_locations "location"
              if ("location"["location_id"] == "department"["location_id"]) && ("location"["state_province"] == <[PAString "Texas"]>)
              then [("empl", ("job", ("department", "location")))]
              else nil[tx_prog_type])
            else nil[tx_prog_type]
        )) else nil[tx_prog_type]))
    in "json" <- <[ PEElaborated _ (generate_json _ (EVar (List tx_prog_type) "ans")) ]>
  }>.
  Goal True.
    let s := eval vm_compute in (export_prog (("json", (TString, true)) :: nil) tx_programmers)%string in
    print_string s.
  Abort.

  Definition tx_programmer_salary := <{
    let "salaries" := flatmap db_employees "empl"
      (flatmap db_jobs "job"
      (if ("empl"["job_id"] == "job"["job_id"]) && ("job"["job_title"] == <[PAString "Programmer"]>) then
        (flatmap db_departments "department"
          (if ("empl"["department_id"] == "department"["department_id"]) then
            (flatmap db_locations "location"
              if ("location"["location_id"] == "department"["location_id"]) && ("location"["state_province"] == <[PAString "Texas"]>)
              then ["empl"["salary"]]
              else nil[TInt])
            else nil[TInt]
        )) else nil[TInt]))
    in "json" <- <[ PEElaborated _ (generate_json _ (EVar (List TInt) "salaries")) ]>
  }>.
  Goal True.
    let s := eval vm_compute in (export_prog (("json", (TString, true)) :: nil) tx_programmer_salary)%string in
    print_string s.
  Abort.

  (* Queries with move filter optimization example *)
  Definition select_steven_job_slow := <{
    let "ans" := flatmap db_employees "empl"
      (flatmap db_jobs "job"
        (if "empl"["first_name"] == <[PAString "Steven"]> then
          (if "empl"["job_id"] == "job"["job_id"] then [("empl", "job")]
            else nil[field_product db_employees_fields db_jobs_fields])
            else nil[field_product db_employees_fields db_jobs_fields]))
    in "json" <- <[ PEElaborated _ (generate_json _ (EVar (List (field_product db_employees_fields db_jobs_fields)) "ans")) ]>
  }>.

  Definition select_steven_job_fast_manual := <{
    let "ans" := flatmap db_employees "empl"
      (if "empl"["first_name"] == <[PAString "Steven"]> then
        (flatmap db_jobs "job"
          (if "empl"["job_id"] == "job"["job_id"] then [("empl", "job")]
            else nil[field_product db_employees_fields db_jobs_fields]))
            else nil[field_product db_employees_fields db_jobs_fields])
    in "json" <- <[ PEElaborated _ (generate_json _ (EVar (List (field_product db_employees_fields db_jobs_fields)) "ans")) ]>
  }>.

  Definition select_steven_job_fast_auto : command :=
    match @elaborate_command tenv (map.of_list (("json", (TString, true)) :: nil)) select_steven_job_slow with
    | Success (CLet v e1 e2) =>
        match enforce_type (List (field_product db_employees_fields db_jobs_fields)) e1 with
        | Success e1' => CLet v (@fold_expr (@move_filter) _ e1') e2
        | Failure _ => CSkip
        end
    | _ => CSkip
    end.

  Goal True.
    let s := eval vm_compute in (export_prog (("json", (TString, true)) :: nil) select_steven_job_slow)%string in
    print_string s.

    let s := eval vm_compute in (export_prog (("json", (TString, true)) :: nil) select_steven_job_fast_manual)%string in
    print_string s.

    Definition export_command_prog (l : list (string * (type * bool))) (c : command) :=
      let output := Success (SortedList.value (interp_command map.empty (map_to_locals l) c))
      in let getJsonStrs := flat_map (fun p =>
          match p return list string with
          | ("json", existT _ String s) => s :: nil
          | _ => nil
          end)
      in match output with
         | Success locals => match getJsonStrs locals with
                             | str :: nil => str
                             | _ => "Error: Program did not output json str"
                             end
         | Failure s => "Error: Program errored"
         end.

    let s := eval vm_compute in (export_command_prog (("json", (TString, true)) :: nil) select_steven_job_fast_auto)%string in
    print_string s.
  Abort.


  Definition tmp := Eval cbv in match tmp' with
                                | CGets _ e => e
                                | _ => _
                                end.
  Compute tmp.
  Compute flatmap_flatmap tmp.
  Compute interp_expr map.empty map.empty tmp.

  Local Close Scope fiat2_scope.

  Declare Scope query_sugar_scope.
  Notation "'join' ( a : x ) ( b : y )" :=
    (PEFlatmap a x%string (PEFlatmap b y%string (PEBinop POPair (PEVar x%string) (PEVar y%string))))
    (at level 0, left associativity) : query_sugar_scope.

  Declare Scope pretty_expr_scope.
  Notation "[ e | x <- l ]" := (EFlatmap l x%string (EBinop (OCons _) e (EAtom (ANil _))))
   (at level 10, only printing, left associativity) : pretty_expr_scope.

  Notation "'nil'" := (EAtom (ANil _))
    (at level 0, only printing) : pretty_expr_scope.

  Notation "[ z ]" := (EBinop (OCons _) z (EAtom (ANil _)))
   (at level 0, only printing) : pretty_expr_scope.

  Notation "[ x , .. , y , z ]" :=
    (EBinop (OCons _) x .. (EBinop (OCons _) y (EBinop (OCons _) z (EAtom (ANil _)))) ..)
   (at level 110, only printing) : pretty_expr_scope.

  Notation "{ x , .. , y , z }" :=
    (EBinop (OPair _ _ _) x .. (EBinop (OPair _ _ _) y (EBinop (OPair _ _ _) z (EAtom AEmpty))) ..)
   (at level 110, only printing) : pretty_expr_scope.

  Declare Custom Entry pretty_record_fields.

  Notation "{{ x }}" := x
    (x custom pretty_record_fields at level 100, only printing) : pretty_expr_scope.

  Notation "x : t , rest" := (TPair x t rest)
    (in custom pretty_record_fields at level 100, x constr at level 0, t constr at level 0, right associativity, only printing) : pretty_expr_scope.

  Notation "x : t" := (TPair x t TEmpty)
    (in custom pretty_record_fields at level 100, x constr at level 0, t constr at level 0, only printing) : pretty_expr_scope.

  Notation "{{}}" := TEmpty : pretty_expr_scope.

  Notation "'<' x '>'" := (EAtom (_ x))
   (at level 10, only printing, format "< x >") : pretty_expr_scope.

  Notation "()" := (EAtom AEmpty)
   (at level 10, only printing) : pretty_expr_scope.

  Notation "$ x" := (EVar _ x%string)
    (at level 10, only printing, format "$ x") : pretty_expr_scope.

  Notation "'if' x 'then' y 'else' z" := (EIf x y z)
    (at level 0, only printing) : pretty_expr_scope.

  Notation "x == y" := (EBinop (OEq _ _) x y)
    (at level 80, only printing) : pretty_expr_scope.

  Notation "x [ k ]" := (EUnop (OFst k _ _) x)
    (at level 10, only printing, left associativity) : pretty_expr_scope.

  Notation "x" := (EUnop (OSnd _ _ _) x)
    (at level 10, only printing, right associativity) : pretty_expr_scope.

  Notation "[ x | x <- l , e ]" :=
    (EFlatmap l x%string (EIf e (EBinop (OCons _) (EVar _ x%string) (EAtom (ANil _))) (EAtom (ANil _))))
    (at level 10, only printing, l at level 9, x at level 0, e at level 10, left associativity) : pretty_expr_scope.

  Local Open Scope pretty_expr_scope.
  Compute tmp.
  Compute partial (flatmap_singleton (flatmap_flatmap (flatmap_flatmap tmp))).
  Local Close Scope pretty_expr_scope.



End Queries_Section.

Require coqutil.Word.Naive.
Require Import coqutil.Word.Bitwidth64.

Definition exported_get_artist (n : Z) := export_prog (word := Naive.word64)
  (("json", (String, true)) :: ("ans", (TList artist, true)) :: nil)
  (filter_test (word := Naive.word64) n).
Definition exported_get_album_and_artist (n : Z) := export_prog (word := Naive.word64)
    (("json", (String, true)) ::
     ("ans", (List (record (("0", album) :: ("1", artist) :: nil)), true)) ::
     nil)
  (filter_albums_with_artist (word := Naive.word64) n).
Compute (exported_get_album_and_artist 5).

Definition exported := (exported_get_artist, exported_get_album_and_artist).

(*
Extraction Language Haskell.
 Extraction "/path/to/haskell/Extracted.hs" exported.
*)
