int main1(int m){
  int b, p, r;

  b=20;
  p=b;
  r=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p % 4 == 0;
  loop invariant 0 <= p <= 20;
  loop invariant (r == 6) || (r == 20);
  loop invariant m == \at(m, Pre);
  loop invariant 0 <= p;
  loop invariant p <= b;
  loop invariant (p == b && r == b) || (p <= b - 4 && r == 6);
  loop invariant b == 20;
  loop invariant p <= 20;
  loop invariant (p >= 0) && (p <= 20) && (p % 4 == 0) && ((r == 6) || (r == 20));
  loop assigns p, r;
*/
while (p>=4) {
      r = r-r;
      r = r+6;
      p = p-4;
  }

}
