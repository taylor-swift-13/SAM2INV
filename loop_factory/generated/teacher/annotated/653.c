int main1(int b,int m){
  int r, t, l, o;

  r=m-2;
  t=0;
  l=r;
  o=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant r == \at(m, Pre) - 2;
  loop invariant (l - r) >= 0;
  loop invariant (l - r) % 6 == 0;

  loop invariant (l - (\at(m, Pre) - 2)) % 6 == 0;
  loop invariant (l - m + 2) % 6 == 0;
  loop invariant l >= m - 2;

  loop invariant r == m - 2;

  loop invariant 12*(o - 6) == (l + 2)*(l + 2) - m*m;

  loop assigns l, o;
*/
while (1) {
      l = l+4;
      l = l+1;
      o = o+l;
      l = l+1;
  }

}
