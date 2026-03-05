int main1(int y){
  int m, jl, w4ma, pxi;
  m=37;
  jl=3;
  w4ma=3;
  pxi=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pxi - w4ma == 4;
  loop invariant w4ma == 4*jl - 9;
  loop invariant 3 <= jl;
  loop invariant jl <= m;
  loop invariant y == \at(y, Pre);
  loop assigns jl, w4ma, pxi;
*/
for (; jl<m; jl++) {
      w4ma += 4;
      pxi += 4;
  }
}