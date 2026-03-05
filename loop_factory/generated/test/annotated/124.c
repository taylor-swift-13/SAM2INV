int main1(int b,int i){
  int xy, st, tudf, a8;
  xy=i;
  st=0;
  tudf=1;
  a8=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (b - \at(b, Pre)) <= 8*st;
  loop invariant 1 <= tudf && tudf <= 8 && (a8 == 1 || a8 == -1);
  loop invariant xy == \at(i, Pre);
  loop invariant i == \at(i, Pre);
  loop invariant 0 <= st && (xy <= 0 || st <= xy) && (a8 == 1 || a8 == -1);
  loop assigns a8, tudf, st, b;
*/
while (st<xy) {
      if (tudf>=8) {
          a8 = -1;
      }
      if (tudf<=1) {
          a8 = 1;
      }
      tudf = tudf + a8;
      st = st + 1;
      b = b + tudf;
  }
}