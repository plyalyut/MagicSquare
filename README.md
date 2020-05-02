This project focused on modeling Magic Squares [insert wikipedia link] of any size in Forge/Alloy and
proving various assertions about their existence. We have provided three different specs that show
different properties. One spec for the general case, one spec optimized for the 4x4 case, 
and another spec in Alloy to show a property of the 3x3 case.

magic_square.rkt:
In order to keep this general, we employee the use of two signatures: Coord and Board. 
Coord has one field, value, that corresponds to the row or column number.
Board corresponds to the square itself with three fields: places, diagonal1, diagonal2. 
The places field is a relation on Coord->Coord->Int corresponding to the number placed at 
a given coordinate pair.
diagonal1 and diagonal2 correspond to the numbers along the main diagonal and the off-diagonal
respectively.

four_by_four.rkt:
magic_square.rkt provides a general framework for constructing magic squares of any NxN sized board.
In theory, given enough computation time, you could use that framework to any size. One of our goals
was to find magic squares larger than 3x3. The main magic square framework mentioned before takes
an incredibly large amount of computation time for squares larger than 4x4. This is due to
the amount of calculation necessary for ensuring satisfiability with a variable size. 
The four_by_four spec provides a hyper-optimized model specifically designed for the 
four by four case by ignoring all the fluff for variable size satisfiability.

magic_square_generator.als: 
We wanted to show that for the classic 3x3 magic square setup (distinct numbers in the range 1-9),
there exists one unique configuration, disregarding rotations and reflections of the magic square.
By including rotations and reflections, every magic square solution has an additional 7 equaivalent
solutions (3 rotations, 2 reflections along the middle, 2 reflections along the diagonals). We 
chose alloy because it allowed us to disregard these trivial reflection/rotation cases.


