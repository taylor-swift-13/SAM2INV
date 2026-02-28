int main1(int b,int k){
  int t, j, s;

  t=80;
  j=0;
  s=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 80;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant s >= -4;
  loop invariant s <= j;
  loop invariant j <= t;
  loop invariant j == 0;
  loop invariant s <= 0;
  loop invariant s == -4 || s == 0;
  loop assigns s;
*/
while (j<=t-1) {
      s = s+2;
      if (j+3<=s+t) {
          s = s-s;
      }
      s = s+j;
  }

}
