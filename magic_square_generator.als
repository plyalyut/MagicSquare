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

pred structural[final_coord: set Coord->Coord->Int] {

    -- coord x coord size board
    final_coord.Int = Coord -> Coord
    #(final_coord) = mul[#(Coord), #(Coord)]

    all c1: Coord | all c2: Coord | {

        --all values > 0
        sum[final_coord[c1][c2]] > 0

        --one int per x,y coord
        one  final_coord[c1][c2]

        --coord is in range 0 -> (board side length - 1)
        sum[c1.value] >= 0
        sum[c1.value] < #(Coord)

        --no two coordinates have the same value
        c1 != c2 implies (c1.value != c2.value)

        --values in the first diagonal (TL -> BR)
        c1 = c2 implies  final_coord[c1][c2] in Board.diagonal1
        else  final_coord[c1][c2] not in Board.diagonal1

        --values in the second diagonal (TR -> BL)
        --if it is in second diagonal, the sum of two coordinates = (board side length - 1)
        add[sum[c1.value], sum[c2.value]] = max[Coord.value] implies final_coord[c1][c2] in Board.diagonal2
        else final_coord[c1][c2] not in Board.diagonal2
    }
  
    all n: Int | {
        --only ints in board can be in diagonals
        n in Board.diagonal1 implies one Coord.(final_coord.n)
        n in Board.diagonal2 implies one Coord.( final_coord.n)

        lone final_coord.n.Coord -- zero/one col per N
        lone Coord.(final_coord.n) -- zero/one row per N
    }  
}

-- tests if a coordinate set is a valid magic square 
pred magic_square_coord [final_coord: Coord->Coord->Int] {
    all c1: Coord {
        sum[final_coord[c1][Coord]] = sum[final_coord[Coord][c1]]
        sum[Board.diagonal1] = sum[(final_coord[Coord][c1])]
	 sum[Board.diagonal2] = sum[(final_coord[Coord][c1])]
    }
}


pred generate_square {
    some init: Board | {
       --#(init.places[Coord][Coord]) = 0
       --exactly one set of final coordinates that meet conditions
    	one final_coord: set Coord->Coord->Int | {
              structural[final_coord]
	       magic_square_coord[final_coord]
              init.places in final_coord
              init.places != final_coord
        }
    }
}


-------------------------Tests-----------------------------

run {
    generate_square
} for exactly 1 Board, exactly 3 Coord, 6 Int



