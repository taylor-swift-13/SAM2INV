int main1(int b,int n){
  int s, p, c;

  s=39;
  p=s+2;
  c=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == 39;
  loop invariant 0 <= p <= 41;
  loop invariant 0 <= c < 9;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p >= 0;
  loop invariant 0 <= p;
  loop invariant p <= 41;
  loop invariant 0 <= c && c <= 8 && (c % 3 == 0 || c % 3 == 2);
  loop invariant p <= s + 2;
  loop invariant 0 <= c;
  loop invariant c <= 8;
  loop invariant c == 3 || c == 5;
  loop assigns c, p;
*/
while (p>=1) {
      c = c*c+c;
      c = c%9;
      p = p/2;
  }

}
