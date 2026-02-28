int main1(int a,int p){
  int v, j, s, h;

  v=(p%17)+7;
  j=0;
  s=0;
  h=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s % 8 == 0;

  loop invariant h >= 0;

  loop invariant p == \at(p, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant v == (\at(p, Pre) % 17) + 7;
  loop invariant (s / 8) < (((v / 2) - 1) / 8) + 1 ==> h == 5 * (s / 8);

  loop invariant h <= (5*s)/8;

  loop invariant h >= s/8;
  loop invariant h <= 5*(s/8);

  loop invariant v == (p % 17) + 7;
  loop invariant (h - s/8) % 4 == 0;
  loop invariant 0 <= s;
  loop invariant 0 <= h;
  loop assigns h, s;
*/
while (s<v) {
      if (s<v/2) {
          h = h+2;
      }
      else {
          h = h-2;
      }
      s = s+1;
      s = s+5;
      h = h+3;
      s = s+2;
  }

}
