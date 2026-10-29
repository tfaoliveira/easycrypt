(* The native list primitives agree with the definitions of List.ec,
   including on out-of-range arguments. *)
require import AllCore List.

check nth 0 [1; 2] 1 = 2.
check nth 0 [1; 2] (-1) = 0.
check nth 0 [1; 2] 2 = 0.
check drop (-1) [1; 2] = [1; 2].
check drop 1 [1; 2] = [2].
check drop 5 [1; 2] = [].
check take (-1) [1; 2] = [].
check take 1 [1; 2] = [1].
check take 5 [1; 2] = [1; 2].
check drop 0 [1; 2] = [1; 2].
check drop 2 [1; 2] = [].
check take 0 [1; 2] = [].
check take 2 [1; 2] = [1; 2].
check take 1 (drop 5 [1; 2]) = [].
check nth 7 (drop 5 [1; 2]) 0 = 7.
check size (drop 99990 (iota_ 0 100000)) = 10.
check take 3 (drop 99990 (iota_ 0 100000)) = [99990; 99991; 99992].
check size [1; 2; 3] = 3.
check [1; 2] ++ [3] = [1; 2; 3].
check rev [1; 2; 3] = [3; 2; 1].
check catrev [1; 2] [3] = [2; 1; 3].
check iota_ 3 3 = [3; 4; 5].
check iota_ 3 (-2) = [].
check size (iota_ 0 100000) = 100000.
check nth 0 (iota_ 0 100000) 99999 = 99999.
check map (fun x => x + 1) [1; 2] = [2; 3].
check filter (fun x => 1 < x) [1; 2; 3] = [2; 3].
check foldr (fun x acc => x - acc) 0 [1; 2; 3] = 2.
check foldl (fun acc x => acc - x) 0 [1; 2; 3] = -6.
check foldl (fun acc x => 10 * acc + x) 0 [] = 0.
check rcons [1; 2] 3 = [1; 2; 3].
check rcons [] 1 = [1].
check last 0 [] = 0.
check last 0 [1; 2; 3] = 3.
check zip [1; 2; 3] [true; false] = [(1, true); (2, false)].
check zip [1] [true; false] = [(1, true)].
check zip [<:int>] [true] = [].
check has (fun x => 2 < x) [1; 2; 3] = true.
check has (fun x => 3 < x) [1; 2; 3] = false.
check all (fun x => 0 < x) [1; 2; 3] = true.
check all (fun x => 1 < x) [] = true.
check find (fun x => 1 < x) [1; 2; 3] = 1.
check find (fun x => 5 < x) [1; 2; 3] = 3.
check size (foldl (fun acc x => rcons acc x) [] (iota_ 0 2000)) = 2000.

require import BitEncoding.
import BS2Int.

check int2bs 4 6 = [false; true; true; false].
check int2bs 3 (-1) = [true; true; true].
check int2bs 0 5 = [].
check bs2int [false; true; true] = 6.
check bs2int (int2bs 64 123456789) = 123456789.
