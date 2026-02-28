int main1(int b,int m){
  int r, f, d, c;

  r=m+8;
  f=0;
  d=8;
  c=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant r == m + 8;
  loop invariant c >= -3;
  loop invariant (c + 3) % 8 == 0;
  loop invariant (c + 3) % d == 0;
  loop invariant r == \at(m, Pre) + 8;
  loop assigns c;
*/
while (1) {
      c = c+d;
  }

}
