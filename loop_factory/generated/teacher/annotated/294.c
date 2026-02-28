int main1(int k,int p){
  int r, j, v;

  r=54;
  j=r;
  v=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant r == 54;
  loop invariant j == r;
  loop invariant v >= 54;
  loop invariant v % 2 == 0;
  loop invariant j == 54;
  loop invariant (j % 7) != 0;
  loop invariant j >= 2;
  loop invariant v >= j;
  loop assigns v;
*/
while (j>2) {
      v = v+2;
      if ((j%7)==0) {
          v = v+v;
      }
  }

}
