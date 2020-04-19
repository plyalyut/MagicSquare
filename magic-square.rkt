#lang forge

--indiviudal spot in board
sig N {
    --numerical value of spot in board
    value: one Int
}

--coordinate of a place in the board
sig Coord {
    num: one Int
}

--represents Coord*Coord board of N
sig Board {
    places: set Coord -> Coord -> N, --row->col->N value
    diagonal1: set N,
    diagonal2: set N
}

pred structural {

    -- all spots are in the board
    N in Board.places[Coord][Coord]

    -- coord x coord size board
    Board.places.N = Coord -> Coord

    all n1: Board.places[Coord][Coord] | all n2: Board.places[Coord][Coord] {
        one Board.places.n1.Coord -- one col per N
        one Coord.(Board.places.n1) -- one row per N
        n1 != n2 implies !(Board.places.n1.Coord = Board.places.n2.Coord and Coord.(Board.places.n1) = Coord.(Board.places.n2))
        -- no two N's have same coordinates
    }

    --coord values range from 0 -> #(coord)-1
    all c1: Coord | all c2: Coord - c1 {
        sum[c1.num] >= 0
        sum[c1.num] < #(Coord)
        c1.num != c2.num
    }

    -- No two N's are the same value.
    all n1: N | all n2: N-n1 {
        n1.value != n2.value
   }

    -- Numbers start at one and are consecutive.
    

    --no box can have value smaller than 0
    all n: N | sum[n.value] > 0

    
    all c1: Coord | all c2: Coord {
        --identifies values in the first diagonal (TL -> BR)
        c1 = c2 implies Board.places[c1][c2] in Board.diagonal1
        else Board.places[c1][c2] not in Board.diagonal1

        --identifies values in the second diagonal (TR -> BL)
        --if it is in second diagonal, the sum of two coordinates = (board side length - 1)
        add[sum[c1.num], sum[c2.num]] = max[Coord.num] implies Board.places[c1][c2] in Board.diagonal2
        else Board.places[c1][c2] not in Board.diagonal2
    }
    
}

pred magic_square {
   all c1: Coord {
       sum[(Board.places[c1][Coord]).value] = sum[(Board.places[Coord][c1]).value]
       --sum[(Board.places[c1][c1]).value] = sum[(Board.places[Coord][c1]).value] -- Diagonal
       --TODO: move digonal stuff up here? Was making program slow.
   }
}

pred sum_to_value {
   all c1: Coord {
       sum[(Board.places[c1][Coord]).value] = 111
   }
   sum[Board.diagonal1.value] = 111
   sum[Board.diagonal2.value] = 111
}                  

run {
    structural
    magic_square
    --sum_to_value
} for exactly 1 Board, exactly 2 Coord, 7 Int
--7 int gives us negative numbers and positive numbers
--right now we are not using all of the numbers we are getting
--maybe try to work with negative numbers?
--7 int = 7 bits (2^7 possible values)
--maybe try working with smaller numbers?
--talk to Tim about how to improve
--z3??

--run {
--    structural
--    magic_square
--    sum_to_value
--} for exactly 1 Board, exactly 3 Coord, exactly 7 Int


