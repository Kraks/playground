fun allChange (coins, coinvals, 0) = [coins]
  | allChange (coins, [], amount) = []
  | allChange (coins, c::coinvals, amount) = 
    if amount < 0 then []
    else allChange(c::coins, c::coinvals, amount-c) @
         allChange(coins, coinvals, amount);

allChange([], [10, 2], 13);
allChange([10], [10, 2], 3) @ allChange([], [2], 13);
allChange([10, 10], [10, 2], ~7) @ allChange([10], [2], 3) @ allChange([2], [2], 11) @ allChange([], [], 13);
[] @ allChange([2, 10], [2], 1) @ allChange([10], [], 3) @ allChange([2, 2], [2], 9) @ allChange([2], [], 11) @ [];
allChange([2, 2, 10], [2], ~1) @ allChange([2, 10], [], 1) @ [] @ allChange([2, 2, 2], [2], 7) @ [];
[] @ [] @ allChange([2, 2, 2, 2], [2], 5) @ allChange([2, 2, 2], [], 7);
allChange([2, 2, 2, 2, 2], [2], 3) @ allChange([2, 2, 2, 2], [], 5) @ [];
allChange([2, 2, 2, 2, 2, 2], [2], 1) @ allChange([2, 2, 2, 2, 2], [], 3);
allChange([2, 2, 2, 2, 2, 2, 2], [2], ~1) @ [];

allChange([], [5, 2], 16);
allChange([5], [5, 2], 11) @ allChange([], [2], 16);
allChange([5, 5], [5, 2], 6) @ allChange([5], [2], 11) @ allChange([2], [2], 14) @ allChange([2], [], 16);
allChange([5, 5, 5], [5, 2], 1) @ allChange([5, 5], [2], 6) @ allChange([2, 5], [2], 9) @ allChange([5], [], 11)
		@ allChange([2, 2], [2], 12) @ allChange([2], [], 14) @ [];
allChange([5, 5, 5, 5], [5, 2], ~4) @ allChange([5, 5, 5], [2], 1) @ allChange([2, 5, 5], [2], 4) @ allChange([5, 5], [], 4)
		@ allChange([2, 2, 5], [2], 7) @ allChange([2, 5], [], 9) @ [] @ allChange([2, 2, 2], [2], 10) @ allChange([2, 2], [], 12);
allChange([2, 5, 5, 5], [2], ~1) @ allChange([5, 5, 5], [], 1) @ allChange([2, 2, 5, 5], [2], 2) @ allChange([2, 5, 5], [], 4)
		@ allChange([2, 2, 2, 5], [2], 5) @ allChange([2, 2, 5], [], 7) @ allChange([2, 2, 2, 2], [2], 8) @ allChange([2, 2, 2], [], 10);		