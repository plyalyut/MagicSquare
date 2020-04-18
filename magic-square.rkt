#lang forge

--indiviudal spot in board
sig N {
    --numerical value of spot in board
    value: one Int
}

--coordinate of a place in the board
sig Coord {
    -- TODO: Maybe make the position ant int to keep track of diagnals.
}

--represents Coord*Coord board of N
sig Board {
    places: set Coord -> Coord -> N --row->col->N value
}

pred structural {

    -- all spots are in the board
    N in Board.places[Coord][Coord]

    -- coord x coord size board
    Board.places.N = Coord -> Coord

    all n1: Board.places[Coord][Coord] | all n2: Board.places[Coord][Coord] {
        lone Board.places.n1.Coord -- one col per N
        lone Coord.(Board.places.n1) -- one row per N
        n1 != n2 implies !(Board.places.n1.Coord = Board.places.n2.Coord and Coord.(Board.places.n1) = Coord.(Board.places.n2))
        -- no two N's have same coordinates
    }

    -- No two N's are the same value.
    all n1: N | all n2: N-n1 {
        n1.value != n2.value
    }

    -- Numbers start at one and are consecutive.
    

    --no box can have value smaller than 0
    all n: N | sum[n.value] > 0
    
}

pred magic_square {
   all c1: Coord {
       sum[(Board.places[c1][Coord]).value] = sum[(Board.places[Coord][c1]).value]
       --sum[(Board.places[c1][c1]).value] = sum[(Board.places[Coord][c1]).value] -- Diagonal
   }
}

pred sum_to_value {
     all c1: Coord {
       sum[(Board.places[c1][Coord]).value] = 111
   }
}                  

--run {
--    structural
--    magic_square
--} for exactly 1 Board, exactly 2 Coord, 7 Int, 3 N

run {
    structural
    magic_square
    sum_to_value
} for exactly 1 Board, exactly 3 Coord, exactly 7 Int, exactly 9 N
--TODO: only working for max 2 coord right now. might have to make more Int in the universe for it to work?
--TODO: needs to work on diagonal!

