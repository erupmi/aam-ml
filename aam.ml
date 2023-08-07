open Core
open Printf

type var = string [@@deriving eq, ord, sexp]
type term = Ref of var
          | Lam of var * term
          | App of term * term [@@deriving eq, ord, sexp]

let rec pp_term = function
  | Ref v -> v
  | Lam (v, e) -> "(lam " ^ v ^ "." ^ pp_term e ^ ")"
  | App (e, e') -> pp_term e ^ " " ^ pp_term e'

type addr = int [@@deriving eq, ord, sexp]
type time = int [@@deriving eq, ord, sexp]

(** Concrete time CESK* Machine **)

module CESK = struct

  type storable = Clo of term * env | Cont of kont
  and env = (var * addr) list
  and store = (addr * storable) list
  and kont = Mt
           | Ar of term * env * addr
           | Fn of term * env * addr

  type stat = term * env * store * kont * time

  let pp_env l =
    List.iter l ~f:(fun (var, addr) ->
        printf "%s -> %d\n" var addr)

  let pp_kont =
    begin function
      | Mt -> printf "Empty\n"
      | Ar (term, env, kont) ->
         printf "%s -> %d\n" (pp_term term) kont;
         pp_env env;
      | Fn (term, env, kont) ->
         printf "%s -> %d\n" (pp_term term) kont;
         pp_env env;
    end

  let pp_store : store -> unit =
    List.iter ~f:(fun (addr, storable) ->
        printf "%d -> " addr;
        match storable with
        | Clo (term, env) -> printf "%s\n" (pp_term term); pp_env env
        | Cont kont -> pp_kont kont)

  let pp_stat : stat -> unit = fun (term, env, store, kont, time) ->
    begin
      printf "[%d]\nExecuting:\n%s\n" time (pp_term term);
      printf "\nEnvironment:\n";
      pp_env env;
      printf "\nStorage:\n";
      pp_store store;
      printf "\nContinuation:\n";
      pp_kont kont;
      printf "\n-------------\n";
    end

  let inject : term -> stat =
    fun e -> (e, [], [], Mt, 0)

  let rec slookup list key =
    match list with
    | (k, v)::tl -> if key = k then v else slookup tl key
    | _ -> failwith @@ "cannot find " ^ string_of_int key

  let rec elookup list key =
    match list with
    | (k, v)::tl -> if String.equal key k then v else elookup tl key
    | _ -> failwith @@ "cannot find " ^ key

  let alloc : stat -> addr =
    fun (_, _, s, _, _) -> List.map s ~f:fst |> List.fold ~init:0 ~f:max |> (+) 1

  let tick : stat -> time =
    fun (_, _, _, _, t) -> t + 1

  let step : stat -> stat = function
    | Ref v, env, store, kont, _ as m ->
       begin match elookup env v |> slookup store  with
       | Clo (lam, env') -> (lam, env', store, kont, tick m)
       | _ -> failwith "not exptect Cont"
       end
    | App (f, e), env, store, kont, _ as m ->
       let addr = alloc m in
       let store' = (addr, Cont kont) :: store in
       (f, env, store', Ar(e, env, addr), tick m)
    | Lam (v, e), env, store, Ar (e', env', addr), _ as m ->
       let time = tick m in
       (e', env', store, Fn (Lam (v, e), env, addr), time)
    | Lam (v, e), env, store, Fn (Lam (v', e'), env', kont), _ as m ->
       let addr = alloc m in
       let env'' = (v', addr) :: env' in
       let store' = (addr, Clo (Lam (v, e), env)) :: store in
       let time = tick m in
       begin
         match slookup store kont with
         | Cont kont' -> (e', env'', store', kont', time)
         | _ -> failwith "undefined"
       end
    | _ -> failwith "undefined"

  let isFinal = function
    | Lam (_, _), _, _, Mt, _ -> true
    | _ -> false

  let rec collect : 'a. ('a -> 'a) -> ('a -> 'b) -> 'a -> 'a list =
    fun step isFinal cek ->
    if isFinal cek then [cek]
    else cek :: (collect step isFinal @@ step cek)

  let evaluate : term -> stat list =
    fun pr -> inject pr |> collect step isFinal

end

(** Abstract time CESK* machine **)

module AbsCESK = struct

  module StoreMap =
    Map.Make (
        struct
          type t = addr
          let compare = compare_addr
          let t_of_sexp = addr_of_sexp
          let sexp_of_t = sexp_of_addr
        end
      )

  module EnvMap =
    Map.Make (
        struct
          type t = var
          let compare = compare_var
          let t_of_sexp = var_of_sexp
          let sexp_of_t = sexp_of_var
        end
      )

  type storable = Clo of term * env | Cont of kont [@@deriving ord, sexp]
  and env = addr EnvMap.t [@@deriving ord, sexp]
  and kont = Mt
           | Ar of term * env * addr
           | Fn of term * env * addr [@@deriving ord, sexp]

  module StorableSet =
    Set.Make (
        struct
          type t = storable
          let compare = compare_storable
          let sexp_of_t = sexp_of_storable
          let t_of_sexp = storable_of_sexp
        end
      )

  type store = StorableSet.t StoreMap.t [@@deriving ord, sexp]

  let store_lub : store -> store -> store =
    fun x y ->
    let open StoreMap in
    let unique comp key = mem comp key |> equal_bool false in
    let x' = filter_keys x ~f:(unique y) in
    let y' =
      fold y ~init:x' ~f:(
          fun ~key ~data accu ->
          if unique x key then
            add_exn accu ~key ~data
          else
            accu
        )
    in
    fold x ~init:y' ~f:(
        fun ~key ~data accu ->
        match find y key with
        | Some y_data ->
           let data = StorableSet.union data y_data in
           add_exn accu ~key ~data
        | None -> accu
      )

  type stat = term * env * store * kont * time [@@deriving ord, sexp]

  let pp_env l =
    Map.iteri l ~f:(fun ~key:var ~data:addr ->
        printf "%s -> %d\n" var addr)

  let pp_kont =
    begin function
      | Mt -> printf "Empty\n"
      | Ar (term, env, kont) ->
         printf "%s -> %d\n" (pp_term term) kont;
         pp_env env;
      | Fn (term, env, kont) ->
         printf "%s -> %d\n" (pp_term term) kont;
         pp_env env;
    end

  let pp_store : store -> unit =
    fun s ->
    StoreMap.iteri s ~f:(fun ~key:addr ~data:storable ->
        printf "%d -> " addr;
        Set.iter storable ~f:(
            fun e ->
            printf "\n  ";
            match e with
            | Clo (term, env) -> printf "Clo %s\n" (pp_term term); pp_env env
            | Cont kont -> printf "Conk: "; pp_kont kont))

  let pp_stat : stat -> unit = fun (term, env, store, kont, time) ->
    begin
      printf "[%d]\nExecuting:\n%s\n" time (pp_term term);
      printf "\nEnvironment:\n";
      pp_env env;
      printf "\nStorage:\n";
      pp_store store;
      printf "\nContinuation:\n";
      pp_kont kont;
      printf "\n-------------\n";
    end

  module StatSet =
    Set.Make(
        struct
          type t = stat
          let compare = compare_stat
          let t_of_sexp = stat_of_sexp
          let sexp_of_t = sexp_of_stat
        end
      )

  let inject : term -> stat =
    fun e -> (e, EnvMap.empty, StoreMap.empty, Mt, 0)

  let slookup : store -> addr -> StorableSet.t =
    fun store addr ->
    match StoreMap.find store addr with
    | Some s -> s
    | None -> StorableSet.empty

  let elookup : env -> var -> addr =
    fun list key -> EnvMap.find_exn list key

  let alloc : stat -> addr =
    fun (_, _, s, _, _) ->
    Map.to_alist s |>
      List.map ~f:(fun (addr, _) -> addr) |>
      List.fold ~init:0 ~f:max |> (+) 1

  let tick : stat -> time =
    fun (_, _, _, _, t) -> t + 1

  let s x = StorableSet.singleton x

  let step : stat -> stat list =
    fun curr ->
    pp_stat curr;
    match curr with
    | Ref v, env, store, kont, _ as m ->
       elookup env v |> slookup store |>
         StorableSet.to_list |>
         List.map ~f:(
             function
             | Clo (lam, env') -> (lam, env', store, kont, tick m)
             | _ -> failwith "not exptect Cont"
           )
    | App (f, e), env, store, kont, _ as m ->
       let addr = alloc m in
       let new_sotre = StoreMap.of_alist_exn [(addr, s (Cont kont))] in
       let store' = store_lub new_sotre store in
       let kont' = Ar(e, env, addr) in
       [(f, env, store', kont', tick m)]
    | Lam (v, e), env, store, Ar (e', env', kont), _ as m ->
       let time = tick m in
       [(e', env', store, Fn (Lam (v, e), env, kont), time)]
    | Lam (v, e), env, store, Fn (Lam (v', e'), env', addr), _ as m ->
       let addr' = alloc m in
       let time = tick m in
       slookup store addr |> StorableSet.to_list
       |> List.map ~f:(
              function
              | Cont kont' ->
                 let env'' = EnvMap.add_exn env' ~key:v' ~data:addr' in
                 let new_store = StoreMap.of_alist_exn [(addr', s(Clo (Lam (v, e), env)))] in
                 let store' = store_lub new_store store in
                 (e', env'', store', kont', time)
              | _ -> failwith "undefined Clo")
    | Lam (_, _), _, _, Mt, _ as m -> [m]
    | _ as m-> pp_stat m; failwith "undefined step"

  let rec search : (stat -> stat list) -> StatSet.t -> stat list -> StatSet.t
    = fun f seen list ->
    match list with
    | [] -> seen
    | hd::tl ->
       if StatSet.mem seen hd then
         search f seen tl
       else
         search f (StatSet.add seen hd) (f hd @ tl)

  let explore : (stat -> stat list) -> stat -> StatSet.t =
    fun f start -> search f StatSet.empty [start]

  let aval : term -> StatSet.t =
    fun e -> explore step @@ inject e

end

(** 0-CFA CESK* machine **)

module ZCESK = struct

  type addr = KAddr of term | BAddr of var [@@deriving ord, sexp]

  module StoreMap =
    Map.Make (
        struct
          type t = addr
          let compare = compare_addr
          let t_of_sexp = addr_of_sexp
          let sexp_of_t = sexp_of_addr
        end
      )

  type storable = Clo of term | Cont of kont [@@deriving ord, sexp]
  and kont = Mt
           | Ar of term * addr
           | Fn of term * addr [@@deriving ord, sexp]

  module StorableSet =
    Set.Make (
        struct
          type t = storable
          let compare = compare_storable
          let sexp_of_t = sexp_of_storable
          let t_of_sexp = storable_of_sexp
        end
      )

  type store = StorableSet.t StoreMap.t [@@deriving ord, sexp]

  let store_lub : store -> store -> store =
    fun x y ->
    let open StoreMap in
    let unique comp key = mem comp key |> equal_bool false in
    let x' = filter_keys x ~f:(unique y) in
    let y' =
      fold y ~init:x' ~f:(
          fun ~key ~data accu ->
          if unique x key then
            add_exn accu ~key ~data
          else
            accu
        )
    in
    fold x ~init:y' ~f:(
        fun ~key ~data accu ->
        match find y key with
        | Some y_data ->
           let data = StorableSet.union data y_data in
           add_exn accu ~key ~data
        | None -> accu
      )

  type stat = term * store * kont [@@deriving ord, sexp]

  let pp_addr =
    begin function
      | KAddr term -> printf "K: %s\n" @@ pp_term term;
      | BAddr var -> printf "B: %s\n" var
    end

  let pp_kont =
    begin function
      | Mt -> printf "Empty\n"
      | Ar (term, addr) ->
         printf "Ar %s: <- " (pp_term term); pp_addr addr;
      | Fn (term, addr) ->
         printf "Fn %s: <- " (pp_term term); pp_addr addr;
    end

  let pp_store : store -> unit =
    fun s ->
    StoreMap.iteri s ~f:(fun ~key:addr ~data:storable ->
        pp_addr addr;
        Set.iter storable ~f:(
            fun e ->
            match e with
            | Clo term -> printf "  Clo %s\n" (pp_term term);
            | Cont kont -> printf "  Cont: "; pp_kont kont))

  let pp_stat : stat -> unit = fun (term, store, kont) ->
    begin
      printf "Executing:\n%s\n" (pp_term term);
      printf "\nStorage:\n";
      pp_store store;
      printf "\nContinuation:\n";
      pp_kont kont;
      printf "-------------\n";
    end

  module StatSet =
    Set.Make(
        struct
          type t = stat
          let compare = compare_stat
          let t_of_sexp = stat_of_sexp
          let sexp_of_t = sexp_of_stat
        end
      )

  let inject : term -> stat =
    fun e -> (e, StoreMap.empty, Mt)

  let slookup : store -> addr -> StorableSet.t =
    fun store addr ->
    match StoreMap.find store addr with
    | Some s -> s
    | None -> StorableSet.empty

  let s x = StorableSet.singleton x

  let step : stat -> stat list =
    fun curr ->
    pp_stat curr;
    match curr with
    | Ref v, store, kont ->
       slookup store (BAddr v) |>
         StorableSet.to_list |>
         List.map ~f:(
             function
             | Clo lam -> (lam, store, kont)
             | _ -> failwith "not exptect Cont"
           )
    | App (e, _) as f, store, kont ->
       let addr = KAddr f in
       let new_sotre = StoreMap.of_alist_exn [(addr, s (Cont kont))] in
       let store' = store_lub new_sotre store in
       let kont' = Ar(e, addr) in
       [(f, store', kont')]
    | Lam (v, e), store, Ar (e', kont) ->
       [(e', store, Fn (Lam (v, e), kont))]
    | Lam (v, e), store, Fn (Lam (v', e'), addr) ->
       slookup store addr |> StorableSet.to_list
       |> List.map ~f:(
              function
              | Cont kont' ->
                 let addr' = BAddr v' in
                 let new_store = StoreMap.of_alist_exn [(addr', s(Clo (Lam (v, e))))] in
                 let store' = store_lub new_store store in
                 (e', store', kont')
              | _ -> failwith "undefined Clo")
    | Lam (_, _), _, Mt as m -> [m]
    | _ as m-> pp_stat m; failwith "undefined step"

  let rec search : (stat -> stat list) -> StatSet.t -> stat list -> StatSet.t
    = fun f seen list ->
    match list with
    | [] -> seen
    | hd::tl ->
       if StatSet.mem seen hd then
         search f seen tl
       else
         search f (StatSet.add seen hd) (f hd @ tl)

  let explore : (stat -> stat list) -> stat -> StatSet.t =
    fun f start -> search f StatSet.empty [start]

  let aval : term -> StatSet.t =
    fun e -> explore step @@ inject e

end

let () =
  printf "========== CSEK ===========\n";
  let open CESK in
  let prog = App (Lam("f", Ref "f"), Lam("x", Ref "x")) in
  let y_comb =
    Lam("f", App
               (Lam("x", App (App (Ref "f", Ref "x") , Ref "x")),
                Lam("x", App (App (Ref "f", Ref "x") , Ref "x"))))
  in
  let y = (App (y_comb, y_comb)) in
  (* not supposed to be stoped: evaluate (App (y_comb, y_comb)) |> *)
  evaluate prog |>
    List.iter ~f:(fun s -> pp_stat s);
  printf "\n====== 0 CSEK ========\n";
  let open ZCESK in
  aval y |>
    StatSet.iter ~f:(fun s -> pp_stat s);
