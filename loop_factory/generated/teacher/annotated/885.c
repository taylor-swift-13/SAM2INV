int main1(int p,int q){
  int n, j, o;

  n=71;
  j=3;
  o=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o >= 71;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant n == 71;
  loop invariant n == 71 && j == 3;
  loop invariant p == \at(p, Pre) && q == \at(q, Pre) && o >= n;
  loop invariant j == 3;
  loop invariant o % 4 == 3;
  loop invariant o >= n;
  loop invariant (o - n) % 4 == 0;
  loop invariant p == \at(p, Pre) && q == \at(q, Pre);
  loop invariant (j % 6) != 0;
  loop invariant o >= n && n == 71 && j == 3;
  loop invariant j == 3 && n == 71 && o % 4 == 3;
  loop invariant o >= 71 && p == \at(p, Pre) && q == \at(q, Pre);
  loop invariant o >= n && (o - n) % 4 == 0 && j == 3 && n == 71;
  loop invariant o >= 71 && (o - 71) % 4 == 0;
  loop invariant j % 6 != 0;
  loop assigns o;
*/
while (1) {
      o = o+4;
      if ((j%6)==0) {
          o = o+o;
      }
  }

}
