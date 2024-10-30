// GENERAL FUNCTIONS AND LEMMAS
// These functions are used to work with matrices in general, and are not specific to double sorted matrices.

/**
  * This function will count how many values are strictly less than the 
  * given value in the given column. 
  */
function CountInColumn(a: array2<int>, col:int, ylo: int, yhi: int, value: int): int
  requires 0 <= col < a.Length1
  requires 0 <= ylo <= yhi <= a.Length0
  decreases yhi-ylo
  reads a
{
  if(ylo == yhi) then 0
  else if(a[ylo,col] < value) then 1+CountInColumn(a,col,ylo+1,yhi,value)
  else CountInColumn(a,col,ylo+1,yhi,value)
}

/**
  * This function will count how many values are strictly less than the
  * given value in the given row, between the given columns.
  *
  * This does not require the matrix to be sorted in any way.
  */
function CountInRow(a: array2<int>, row:int, xlo: int, xhi: int, value: int): int
  requires 0 <= row < a.Length0
  requires 0 <= xlo <= xhi <= a.Length1
  decreases xhi-xlo
  reads a
{
  if(xlo == xhi) then 0
  else if(a[row,xlo] < value) then 1+CountInRow(a,row,xlo+1,xhi,value)
  else CountInRow(a,row,xlo+1,xhi,value)
}

/**
  * This function will count how many values are strictly less than the
  * given value in the given matrix, between the given columns and rows.
  */
function CountInMatrixByColumns(a: array2<int>, xlo: int, xhi: int, ylo: int, yhi: int, value: int): int
  requires 0 <= xlo <= xhi <= a.Length1
  requires 0 <= ylo <= yhi <= a.Length0
  decreases xhi-xlo
  reads a
{
  if(xlo == xhi) then 0
  else if(ylo == yhi) then 0
  else
    CountInColumn(a,xlo,ylo,yhi,value) + CountInMatrixByColumns(a,xlo+1,xhi,ylo,yhi,value)
}

/**
  * This lemma proves that for any given bounds, regardless of the way in which the matrix is traversed
  * (by row or by column), the count of values less than the given value is the same.
  */
lemma ProveBothCountsAreEqual(a: array2<int>, xlo: int, xhi: int, ylo: int, yhi: int, value: int)
  requires 0 <= xlo <= xhi <= a.Length1
  requires 0 <= ylo <= yhi <= a.Length0
  decreases yhi-ylo, xhi-xlo
  ensures CountInMatrixByColumns(a, xlo, xhi, ylo, yhi, value) == CountInMatrixByRow(a, xlo, xhi, ylo, yhi, value)
{
  if(xlo == xhi || ylo == yhi) {
    assert CountInMatrixByColumns(a, xlo, xhi, ylo, yhi, value) == 0;
    assert CountInMatrixByRow(a, xlo, xhi, ylo, yhi, value) == 0;
  } else if(yhi - ylo == 1) {
    ProveBothCountsAreEqual(a, xlo, xhi-1, ylo, yhi, value);
    assert CountInMatrixByColumns(a, xlo, xhi-1, ylo, yhi, value) ==
           CountInMatrixByRow(a, xlo, xhi-1, ylo, yhi, value);

    CountInMatrixRowLemma(a, xlo, xhi, ylo, value);
    assert CountInMatrixByColumns(a, xlo, xhi, ylo, yhi, value) == CountInMatrixByColumns(a, xlo, xhi, ylo, yhi-1, value) +
                                                          CountInMatrixByColumns(a, xlo, xhi, yhi-1, yhi, value);
  } else {
    ProveBothCountsAreEqual(a, xlo, xhi, ylo+1, yhi, value);
  }
}


/**
 * This lemma proves that the sum of rows is equal to the value of CountInMatrixByRow.
 * Normally, this shouldn't need to exist, but this proves the recursion in reverse.
 * 
 * For ProveBothCountsAreEqual, we need a recursive proof in which the ylo is increased,
 * and for the student implementation, we need a recursive proof in which the yhi is decreased.
 */
lemma ProveSumOfRowsIsMatrixCount(a: array2<int>, xlo: int, xhi: int, ylo: int, yhi: int, value: int)
  requires 0 <= xlo <= xhi <= a.Length1
  requires 0 <= ylo < yhi <= a.Length0
  decreases yhi-ylo
  ensures CountInMatrixByRow(a, xlo, xhi, ylo, yhi-1, value)
          + CountInRow(a, yhi-1, xlo, xhi, value) ==
          CountInMatrixByRow(a, xlo, xhi, ylo, yhi, value) {
}


/**
  * This lemma proves that the CountInMatrix function with a single row 
  * is equivalent to the CountInRow function.
  */
lemma CountInMatrixRowLemma(a: array2<int>, xlo: int, xhi: int, row: int, value: int)
  requires 0 <= xlo <= xhi <= a.Length1
  requires 0 <= row < a.Length0
  decreases xhi-xlo
  ensures CountInMatrixByColumns(a,xlo,xhi,row,row+1,value) == CountInRow(a,row,xlo,xhi,value)
{
  if(xlo == xhi) {
    // If no columns are left, then the count is 0, in both cases.
    assert CountInMatrixByColumns(a,xlo,xhi,row, row + 1,value) == 0;
    assert CountInRow(a,row,xlo,xhi,value) == 0;
  } else {
    // Assert that the count in matrix is equal to the count
    // in the row plus the count in the rest of the matrix.
    assert CountInRow(a,row,xlo,xhi,value) == CountInColumn(a,xlo,row,row+1,value) + CountInRow(a,row,xlo+1,xhi,value);
    CountInMatrixRowLemma(a, xlo+1, xhi, row, value);
  }
}

/**
  * This function will count how many values are strictly less than the
  * given value in the given matrix, between the given columns and rows.
  */
function CountInMatrixByRow(a: array2<int>, xlo: int, xhi: int, ylo: int, yhi: int, value: int): int
  requires 0 <= xlo <= xhi <= a.Length1
  requires 0 <= ylo <= yhi <= a.Length0
  decreases yhi-ylo
  reads a
{
  if(ylo == yhi) then 0
  else if(xlo == xhi) then 0
  else
    CountInRow(a,ylo,xlo,xhi,value) + CountInMatrixByRow(a,xlo,xhi,ylo+1,yhi,value)
}

// SPECIFIC FUNCTIONS AND LEMMAS
// These functions and lemmas are specific to the double sorted matrix problem.
// They will all require the matrix to be sorted in ascending order in both rows and columns.

/**
  * This predicate ensures that the matrix is sorted in ascending order in both rows and columns.
  */
predicate AscAsc(a: array2<int>)
  reads a
{
  (forall i, j, k:: 0 <= i < j < a.Length0 && 0 <= k < a.Length1 ==> a[i,k] <= a[j,k]) &&
  (forall i, j, k:: 0 <= i < a.Length0 && 0 <= j < k < a.Length1 ==> a[i,j] <= a[i,k])
}


/**
  * This lemma proves that given a row between certain columns,
  * if all the values in the row are greater than or equal to the given value,
  * then the count of values less than the given value in the row is 0.
  * (and CountInRow will return 0)
  */
lemma RowEmptyLemma(a: array2<int>, row:int, xlo: int, xhi: int, value: int)
  requires 0 <= row < a.Length0
  requires 0 <= xlo <= xhi <= a.Length1
  requires AscAsc(a) // Technically, not needed, but it is a key part of the student implementation
  requires forall k:: xlo <= k < xhi ==> a[row,k] >= value
  ensures CountInRow(a,row,xlo,xhi,value) == 0
  decreases xhi-xlo
{
}

/**
  * This lemma proves that, given a column and a value, if one of the values in the column,
  * is less than the given value, then the count of values less than the given value in the column
  * is equal to the number of rows in the column.
  */
lemma CountInMatrixSingleColumnLemma(a: array2<int>, x: int, ylo: int, yhi: int, value: int)
  requires 0 <= x < a.Length1
  requires 0 <= ylo < yhi <= a.Length0
  requires AscAsc(a)
  requires a[yhi-1,x] < value
  decreases yhi-ylo
  ensures CountInColumn(a, x, ylo, yhi, value) == yhi-ylo
{
}


method StudentImplementation(a: array2<int>, value: int) returns (z: int)
  requires AscAsc(a)
  requires a.Length0 > 0 && a.Length1 > 0
  ensures z == CountInMatrixByColumns(a,0,a.Length1,0,a.Length0,value)
{
  z := 0;
  var x := 0;
  var y := a.Length0;
  assert z + CountInMatrixByColumns(a, x, a.Length1, 0, y, value) == CountInMatrixByColumns(a, 0, a.Length1, 0, a.Length0, value);
  while(x < a.Length1 && y > 0)
    invariant 0 <= x <= a.Length1
    invariant 0 <= y <= a.Length0
    invariant z + CountInMatrixByColumns(a, x, a.Length1, 0, y, value) == CountInMatrixByColumns(a, 0, a.Length1, 0, a.Length0, value)
  {

    if(a[y - 1,x] < value) {
      assert CountInMatrixByColumns(a, x, a.Length1, 0, y, value) ==
             CountInMatrixByColumns(a, x, x+1, 0, y, value) + CountInMatrixByColumns(a, x+1, a.Length1, 0, y, value);

      // This is the basis of the algorithm when it comes to counting the number of values in a column.
      CountInMatrixSingleColumnLemma(a, x, 0, y, value);
      assert CountInMatrixByColumns(a, x, x+1, 0, y, value) == y;

      z := z + y;
      x := x + 1;
    } else {
      // There should be no values less than the given value in the row.
      RowEmptyLemma(a, y-1, x, a.Length1, value);
      assert CountInMatrixByRow(a, x, a.Length1, y-1, y, value) == 0;

      assert CountInMatrixByRow(a, x, a.Length1, y-1, y, value) == CountInRow(a, y-1, x, a.Length1, value);

      ProveSumOfRowsIsMatrixCount(a, x, a.Length1, 0, y, value);
      assert CountInMatrixByRow(a, x, a.Length1, 0, y, value) == CountInMatrixByRow(a, x, a.Length1, 0, y-1, value)
                                                                 + CountInRow(a, y-1, x, a.Length1, value);

      ProveBothCountsAreEqual(a, x, a.Length1, 0, y, value);
      ProveBothCountsAreEqual(a, x, a.Length1, 0, y-1, value);
      ProveBothCountsAreEqual(a, x, a.Length1, y-1, y, value);
      assert CountInMatrixByColumns(a, x, a.Length1, 0, y, value) == CountInMatrixByColumns(a, x, a.Length1, y-1, y, value) +
                                                            CountInMatrixByColumns(a, x, a.Length1, 0, y-1, value);
      y := y - 1;
    }
  }
}