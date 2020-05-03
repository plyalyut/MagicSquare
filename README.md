This project focused on modeling Magic Squares https://en.wikipedia.org/wiki/Magic_square of any size in Forge/Alloy and proving various assertions about their existence. We have provided three different specs that show different properties. One spec for the general case, one spec optimized for the 4x4 case, and another spec in Alloy to generate a magic square game.

magic_square.rkt:
In order to keep this general, we employ the use of two signatures: Coord and Board. 
Coord has one field, value, that corresponds to the row or column number.
Board corresponds to the square itself with three fields: places, diagonal1, diagonal2. 
The places field is a relation on Coord->Coord->Int corresponding to the number placed at 
a given coordinate pair.
diagonal1 and diagonal2 correspond to the numbers along the main diagonal and the off-diagonal respectively.
In this spec, we made a few discoveries:
-There does not exist a 2x2 magic square
-Using numbers 1-9, there is only one unique 3x3 magic square
-Adding a constant onto each value in a magic square creates another magic square
-Multiplying each value in a magic square by a constant creates another magic square

four_by_four.rkt:
magic_square.rkt provides a general framework for constructing magic squares of any NxN sized board.
In theory, given enough computation time, you could use that framework to any size. One of our goals
was to find magic squares larger than 3x3. The main magic square framework mentioned before takes
an incredibly large amount of computation time for squares larger than 4x4. This is due to
the amount of calculation necessary for ensuring satisfiability with a variable size. 
The four_by_four spec provides a hyper-optimized model specifically designed for the 
four by four case by ignoring all the fluff for variable size satisfiability.

magic_square_generator.als: 
This spec makes a kind of magic square game. It generates a 3x3 board with some numbers filled in such that there is only
one unique magic square that could be created from this setup. In the result generated, the Init board will not be completely filled in, and the Final board will represent the "solution" magic square that comes from this board. One interesting discovery we made here is that one number filled in (usually on a diagonal) could define a unique magic square. We chose to use alloy* for this part of the problem because we had to use higher order quantification, which forge does not permit.



