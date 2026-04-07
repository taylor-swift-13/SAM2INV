int main1(int j){
  int y, go4, qj;
  y=j;
  go4=0;
  qj=y;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= go4;
  loop invariant qj == y - go4;
  loop invariant j == \at(j, Pre) + (go4 * (go4 + 1)) / 2;
  loop invariant y == \at(j, Pre);
  loop assigns go4, qj, j;
*/
while (go4<=y-1) {
      go4 += 1;
      qj = y-go4;
      j += go4;
  }
}