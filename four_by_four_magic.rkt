#lang forge

--represents Coord * Coord board of Int
sig Board {
  places: set Int -> Int -> Int, --row->col->N value
  filled_places: set Int -> Int -> Int
}

pred structural[b: Board] {
    -- Creates the board
    b.places.Int = (sing[0]+sing[1]+sing[2]+sing[3]) ->
    (sing[0]+sing[1]+sing[2]+sing[3])

    -- every element has a unique number
    b.places[Int][Int] = (sing[1]+sing[2]+sing[3]+sing[4]+
                              sing[5]+sing[6]+sing[7]+sing[8] +
                              sing[9]+sing[10]+sing[11]+sing[12] +
                              sing[13]+sing[14]+sing[15]+sing[16])

    all c1: b.places.Int[Int] | all c2: b.places.Int.Int {
        lone b.places[c1][c2]
        sum[b.places[c1][Int]] = sum[sing[34]]
        sum[b.places[Int][c1]] = sum[sing[34]]
    }

    -- Diagonals
    sum[b.places[sing[0]][sing[0]]+
        b.places[sing[1]][sing[1]]+
        b.places[sing[2]][sing[2]]+
        b.places[sing[3]][sing[3]]] = sum[sing[34]]

    sum[b.places[sing[0]][sing[3]]+
        b.places[sing[1]][sing[2]]+
        b.places[sing[2]][sing[1]]+
        b.places[sing[3]][sing[0]]] = sum[sing[34]]

    b.filled_places in b.places
}

--creates a 4x4 board
--run {
--    all b: Board {
--        structural[b]       
--    }
--} for exactly 1 Board, 6 Int

inst existence {
    -- show that there exists solutions to 4x4
    Int[6]
    Board = Board0
    --places = Board0->sing[1]->sing[1]->sing[2]
}

inst verify_correct_solution {
    -- verify a correct solution
    Int[6]
    Board = Board0
    places = Board0->sing[0]->sing[0]->sing[8]
    + Board0->sing[0]->sing[1]->sing[1]
    + Board0->sing[0]->sing[2]->sing[11]
    + Board0->sing[0]->sing[3]->sing[14]
    + Board0->sing[1]->sing[0]->sing[10]
    + Board0->sing[1]->sing[1]->sing[15]
    + Board0->sing[1]->sing[2]->sing[5]
    + Board0->sing[1]->sing[3]->sing[4]
    + Board0->sing[2]->sing[0]->sing[13]
    + Board0->sing[2]->sing[1]->sing[12]
    + Board0->sing[2]->sing[2]->sing[2]
    + Board0->sing[2]->sing[3]->sing[7]
    + Board0->sing[3]->sing[0]->sing[3]
    + Board0->sing[3]->sing[1]->sing[6]
    + Board0->sing[3]->sing[2]->sing[16]
    + Board0->sing[3]->sing[3]->sing[9]
}

inst one_value_there {
    -- tests that a solution would be found while
    -- only having one value filled in
    Int[6]
    Board = Board0
    filled_places = Board0->sing[1]->sing[1]->sing[2]
}



test expect {
  { structural[Board] } for existence is sat
  { structural[Board] } for verify_correct_solution is sat
  { structural[Board] } for one_value_there is sat
}