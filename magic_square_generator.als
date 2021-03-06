--coordinate of a place in the board
sig Coord {
    value: one Int
}

--represents Coord * Coord board of Int
sig Board {
    places: set Coord -> Coord -> Int --row->col->N value
}

--keeps track of diagonals in output
sig Final_Diagonals {
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
        c1 = c2 implies  final_coord[c1][c2] in Final_Diagonals.diagonal1
        else  final_coord[c1][c2] not in Final_Diagonals.diagonal1

        --values in the second diagonal (TR -> BL)
        --if it is in second diagonal, the sum of two coordinates = (board side length - 1)
        add[sum[c1.value], sum[c2.value]] = max[Coord.value] implies final_coord[c1][c2] in Final_Diagonals.diagonal2
        else final_coord[c1][c2] not in Final_Diagonals.diagonal2
    }
  
    all n: Int | {
        --only ints in board can be in diagonals
        n in Final_Diagonals.diagonal1 implies one Coord.(final_coord.n)
        n in Final_Diagonals.diagonal2 implies one Coord.(final_coord.n)

        lone final_coord.n.Coord -- zero/one col per N
        lone Coord.(final_coord.n) -- zero/one row per N
    }  
}

-- tests if a coordinate set is a valid magic square 
pred magic_square_coord [final_coord: Coord->Coord->Int] {
    all c1: Coord {
        sum[final_coord[c1][Coord]] = sum[final_coord[Coord][c1]]
        sum[Final_Diagonals.diagonal1] = sum[(final_coord[Coord][c1])]
	 sum[Final_Diagonals.diagonal2] = sum[(final_coord[Coord][c1])]
    }
}

--generates initial and final squares
--starting places represents the number of spaces filled in the initial board
pred generate_square[starting_places: Int] {
    some init: Board | { --initial board --> not all filled
       #(init.places[Coord][Coord]) = starting_places
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

--generates an incomplete init square and the corresponding complete final square
run {
    generate_square[0]
} for exactly 1 Board, exactly 3 Coord, exactly 1 Final_Diagonals, 6 Int

/*
let repeatedValue {
  Board = Board0
  Coord = Coord0 + Coord1 + Coord2
  places = Board0->Coord0->Coord0->sing[2] + Board0->Coord0->Coord1->sing[7]  + Board0->Coord0->Coord2->sing[6]  +
      Board0->Coord1->Coord0->sing[0]  + Board0->Coord1->Coord1->sing[5]  + Board0->Coord1->Coord2->sing[1]  +
      Board0->Coord2->Coord0->sing[4]  + Board0->Coord2->Coord1->sing[3]  + Board0->Coord2->Coord2->sing[3]
}

pred NAME {
    { generated_square } for repeatedValue is unsat
}*/
