#lang forge

sig Board {
  places: set Int -> Int -> Int
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
}

run {
    all b: Board {
        structural[b]       
    }
} for exactly 1 Board, 6 Int 