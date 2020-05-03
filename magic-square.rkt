#lang forge

--coordinate of a place in the board
sig Coord {
    value: one Int
}

--represents Coord * Coord board of Int
sig Board {
    places: set Coord -> Coord -> Int, --row->col->N value
    diagonal1: set Int, --TL to BR diagonal
    diagonal2: set Int  --TR to BL diagonal
}

--sets up structure of board
pred structural[b: Board] {

    -- coord x coord size board
    b.places.Int = Coord -> Coord

    all c1: Coord | all c2: Coord | {

        --all values > 0
        sum[b.places[c1][c2]] > 0

        --one int per x,y coord
        one b.places[c1][c2]

        --coord is in range 0 -> (board side length - 1)
        sum[c1.value] >= 0
        sum[c1.value] < #(Coord)

        --no two coordinates have the same value
        c1 != c2 implies (c1.value != c2.value)

        --values in the first diagonal (TL -> BR)
        c1 = c2 implies b.places[c1][c2] in b.diagonal1
        else b.places[c1][c2] not in b.diagonal1

        --values in the second diagonal (TR -> BL)
        --if it is in second diagonal, the sum of two coordinates = (board side length - 1)
        add[sum[c1.value], sum[c2.value]] = max[Coord.value] implies b.places[c1][c2] in b.diagonal2
        else b.places[c1][c2] not in b.diagonal2
    }
  
    all n: Int | {
        --only ints in board can be in diagonals
        n in b.diagonal1 implies one Coord.(b.places.n)
        n in b.diagonal2 implies one Coord.(b.places.n)

        lone b.places.n.Coord -- zero/one col per N
        lone Coord.(b.places.n) -- zero/one row per N
    }  
}

pred magic_square[b: Board] {
    sum[b.diagonal1] = sum[b.diagonal2]
    all c1: Coord {
        sum[b.diagonal1] = sum[(b.places[c1][Coord])]
        sum[b.diagonal1] = sum[(b.places[Coord][c1])]
    }
}

-- Value for each of the vertical, horizontal columns to sum up to.
pred sum_to_value[sum_value: Int, b: Board] {
   sum[b.diagonal1] = sum_value
}

pred successive[b: Board] {
    -- All integers are succesive
    (places[b][Coord][Coord]).succ + sing[min[(places[b][Coord][Coord])]] - sing[max[(places[b][Coord][Coord]).succ]] = places[b][Coord][Coord]
}

pred start_at[value: Int, b: Board]{
    -- Starts at a given value
    min[places[b][Coord][Coord]] = value
}

pred must_contain[values: set Int, b: Board]{
    -- Square must contain the values provided in the set
    all v: values | {
        v in b.places[Coord][Coord]
    }
}

--all values in square are oodd
pred square_all_odd[b: Board] {
    -- Square must contain the values provided in the set
    all val: b.places[Coord][Coord] | {
        remainder[sum[val], 2] = 1
    }
}

--all values in square are even
pred square_all_even[b: Board] {
    -- Square must contain the values provided in the set
    all val: b.places[Coord][Coord] | {
        remainder[sum[val], 2] = 0
    }
}

--b2 is multiplied version of b1
pred multiply_square[b1: Board, b2: Board] {
    all c1: Coord | all c2: Coord | some n: Int {
        sum[b2.places[c1][c2]] = multiply[sum[b1.places[c1][c2]], sum[n]]
    }
}

--b2 is added version of b1
pred add_square[b1: Board, b2: Board] {
    all c1: Coord | all c2: Coord | some n: Int {
        sum[b2.places[c1][c2]] = add[sum[b1.places[c1][c2]], sum[n]]
    }
}

-------------------------Tests-----------------------------
-- Trivial case 1x1
--run {
--    all b: Board {
--        structural[b]
--        magic_square[b]
--        successive[b]
--        start_at[1, b]
--    }
--} for exactly 1 Board, exactly 1 Coord, 2 Int


-- no 2x2 cases exist
--run {
--    all b: Board {
--        structural[b]
--        magic_square[b]
--    }
--} for exactly 1 Board, exactly 2 Coord, 5 Int


-- 3x3 case summing up to 15 (successive numbers)
--run {
--    all b: Board {
--        structural[b]
--        magic_square[b]
--        successive[b]
--        start_at[1, b]
--    }
--} for exactly 1 Board, exactly 3 Coord, 5 Int


-- 3x3 case -- no restrictions
--run {
--    all b: Board | {
--        structural[b]
--        magic_square[b]
--    }
--} for exactly 1 Board, exactly 3 Coord, 5 Int


-- 3x3 case -- all odd
--run {
--    all b: Board {
--        structural[b]
--        magic_square[b]
--        square_all_odd[b]
--    }
--} for exactly 1 Board, exactly 3 Coord, 6 Int


-- 3x3 case -- all even
--run {
--    all b: Board {
--        structural[b]
--        magic_square[b]
--        square_all_even[b]
--    }
--} for exactly 1 Board, exactly 3 Coord, 6 Int


-- foundation goal
-- dictate which values should be in magic square
--run {
--    all b: Board {
--        structural[b]
--        magic_square[b]
--        must_contain[sing[11], b]
--    }
--} for exactly 1 Board, exactly 3 Coord, 6 Int

-- repeated values in board
inst repeatedValue {
  Board = Board0
  Coord = Coord0 + Coord1 + Coord2
  places = Board0->Coord0->Coord0->sing[2] + Board0->Coord0->Coord1->sing[7]  + Board0->Coord0->Coord2->sing[6]  +
      Board0->Coord1->Coord0->sing[0]  + Board0->Coord1->Coord1->sing[5]  + Board0->Coord1->Coord2->sing[1]  +
      Board0->Coord2->Coord0->sing[4]  + Board0->Coord2->Coord1->sing[3]  + Board0->Coord2->Coord2->sing[3]
}

--board with two values at same coordinate
inst invalidBoard {
  Board = Board0
  Coord = Coord0 + Coord1 + Coord2
  places = Board0->Coord0->Coord0->sing[2] + Board0->Coord0->Coord1->sing[0]  + Board0->Coord0->Coord2->sing[6]  +
      Board0->Coord1->Coord1->sing[5]  + Board0->Coord1->Coord1->sing[7]  + Board0->Coord1->Coord2->sing[1]  +
      Board0->Coord2->Coord0->sing[4]  + Board0->Coord2->Coord1->sing[3]  + Board0->Coord2->Coord2->sing[-1]
}

--board with two values at same coordinate
inst twoByTwo {
  Board = Board0
  Coord = Coord0 + Coord1
}

-- repeated values in board
inst goodSquare {
  Int[5]
  Board = Board0
  Coord = Coord0 + Coord1 + Coord2
  places = Board0->Coord0->Coord0->sing[2] + Board0->Coord0->Coord1->sing[7]  + Board0->Coord0->Coord2->sing[6]  +
      Board0->Coord1->Coord0->sing[9]  + Board0->Coord1->Coord1->sing[5]  + Board0->Coord1->Coord2->sing[1]  +
      Board0->Coord2->Coord0->sing[4]  + Board0->Coord2->Coord1->sing[3]  + Board0->Coord2->Coord2->sing[8]
}

inst oneSquare {
  Board = Board0
  Coord = Coord0
}

test expect {
    { structural[Board] magic_square[Board] } for repeatedValue is unsat
    { structural[Board] magic_square[Board] } for invalidBoard is unsat
    { structural[Board] magic_square[Board] } for twoByTwo is unsat
    { structural[Board] magic_square[Board] } for goodSquare is sat
    { structural[Board] magic_square[Board] } for oneSquare is sat
}

-- multiplicity property of magic squares
--multiplicity_property : check {
--    some b1: Board | some b2: Board - b1 {
--        structural[b1] and structural[b2] and multiply_square[b1, b2] and magic_square[b1] implies magic_square[b2]
--    }
--} for exactly 2 Board, exactly 3 Coord, 6 Int


-- additive property of magic squares
--additive_property : check {
--    some b1: Board | some b2: Board - b1 {
--        structural[b1] and structural[b2] and add_square[b1, b2] and magic_square[b1] implies magic_square[b2]
--    }
--} for exactly 2 Board, exactly 3 Coord, 6 Int