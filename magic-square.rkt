#lang forge

--coordinate of a place in the board
sig Coord {
    value: one Int
}

--represents Coord * Coord board of Int
sig Board {
    places: set Coord -> Coord -> Int, --row->col->N value
    diagonal1: set Int,
    diagonal2: set Int
}

pred structural {

    -- coord x coord size board
    Board.places.Int = Coord -> Coord

    all c1: Coord | all c2: Coord {

        --all values > 0
        --sum[Board.places[c1][c2]] > 0

        --one int per x,y coord
        one Board.places[c1][c2]

        --coord is in range 0 -> (board side length - 1)
        sum[c1.value] >= 0
        sum[c1.value] < #(Coord)

        --no two coordinates have the same value
        c1 != c2 implies (c1.value != c2.value)

        --values in the first diagonal (TL -> BR)
        c1 = c2 implies Board.places[c1][c2] in Board.diagonal1
        else Board.places[c1][c2] not in Board.diagonal1

        --values in the second diagonal (TR -> BL)
        --if it is in second diagonal, the sum of two coordinates = (board side length - 1)
        add[sum[c1.value], sum[c2.value]] = max[Coord.value] implies Board.places[c1][c2] in Board.diagonal2
        else Board.places[c1][c2] not in Board.diagonal2
    }

    
    all n: Int | {
        --only ints in board can be in diagonals
        n in Board.diagonal1 implies one Coord.(Board.places.n)
        n in Board.diagonal2 implies one Coord.(Board.places.n)

        lone Board.places.n.Coord -- zero/one col per N
        lone Coord.(Board.places.n) -- zero/one row per N
    }  
}

pred magic_square {
   sum[Board.diagonal1] = sum[Board.diagonal2]
   all c1: Coord {
       sum[Board.diagonal1] = sum[(Board.places[c1][Coord])]
       sum[Board.diagonal1] = sum[(Board.places[Coord][c1])]
   }
}

-- Value for each of the vertical, horizontal columns to sum up to.
pred sum_to_value[sum_value: Int] {
   sum[Board.diagonal1] = sum_value
}

pred successive {
    -- All integers are succesive
    (places[Board][Coord][Coord]).succ + sing[min[(places[Board][Coord][Coord])]] - sing[max[(places[Board][Coord][Coord]).succ]] = places[Board][Coord][Coord]    
}

pred start_at[value: Int]{
    -- Starts at a given value
    min[places[Board][Coord][Coord]] = value
}


---------------------------Tests-----------------------------
-- Trivial case 1x1
run {
    structural
    magic_square
    successive
    start_at[1]
} for exactly 1 Board, exactly 1 Coord, 2 Int


--  no 2x2 cases
--run {
--    structural
--    magic_square
--} for exactly 1 Board, exactly 2 Coord, 4 Int


-- 3x3 case summing up to 15
--run {
--    structural
--    magic_square
--    successive
--    --start_at[1]
--} for exactly 1 Board, exactly 3 Coord, 5 Int

-- 4x4 case solution
run {
    structural
    magic_square
    --successive
    --start_at[-1]
    sum_to_value[-2]
} for exactly 1 Board, exactly 4 Coord, 5 Int



/*
Notes:
--7 int gives us negative numbers and positive numbers
--right now we are not using all of the numbers we are getting
--maybe try to work with negative numbers?
--talk to Tim about how to improve
--Z3??
*/


