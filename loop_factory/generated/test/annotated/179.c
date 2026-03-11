int main1(int c,int v){
  int j, orp, a, lp, xe, k;
  j=57;
  orp=2;
  a=0;
  lp=0;
  xe=0;
  k=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2 <= orp;
  loop invariant orp <= j;
  loop invariant 0 <= lp;
  loop invariant lp < 5;
  loop invariant 0 <= xe;
  loop invariant xe < 5;
  loop invariant k >= 4;
  loop invariant j == 57;
  loop invariant c == \at(c, Pre);
  loop invariant v == \at(v, Pre);
  loop invariant a >= -4*(orp - 2);
  loop invariant a <= 4*(orp - 2);
  loop invariant k <= 4 + 4*(orp - 2);
  loop invariant (j - orp) + (orp - 2) == j - 2;
  loop invariant ((orp == 2 && lp == 0) || lp == ((orp - 1) % 5));
  loop assigns a, k, lp, xe, orp;
*/
while (orp<j) {
      lp = orp%5;
      if (!(!(orp>=k))) {
          xe = (orp-k)%5;
          a = a+lp-xe;
      }
      else {
          a += lp;
      }
      k = k + xe;
      orp++;
  }
}