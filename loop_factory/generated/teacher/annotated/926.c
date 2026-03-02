int main1(int b,int n){
  int d, l, v;

  d=80;
  l=2;
  v=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre) && n == \at(n, Pre);
  loop invariant d == 80 && v >= 3 && (v == 3 || (v % 2 == 0));
  loop invariant v >= 3 && d == 80;
  loop invariant d == 80;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v >= -4;
  loop invariant v >= 3;
  loop invariant (v + 8) % 11 == 0;
  loop invariant v >= 0;
  loop invariant b == \at(b, Pre) && n == \at(n, Pre) && v >= 3;
  loop assigns v;
*/
while (1) {
      v = v+4;
      v = v*2;
  }

}
