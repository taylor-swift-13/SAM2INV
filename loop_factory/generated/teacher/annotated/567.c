int main1(int b,int m){
  int g, x, v, p;

  g=b;
  x=0;
  v=m;
  p=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant p >= 2;
  loop invariant p % 2 == 0;
  loop invariant m == \at(m, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant g == b;
  loop invariant g == \at(b, Pre);
  loop invariant v <= \at(m, Pre) || v <= g + 3;

  loop assigns v, p;
*/
while (1) {
      if (v+6<=g) {
          v = v+6;
      }
      else {
          v = g;
      }
      v = v+3;
      p = p+2;
  }

}
