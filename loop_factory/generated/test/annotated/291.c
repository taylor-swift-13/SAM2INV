int main1(int n){
  int dh, d, ln, pl, ttir;
  dh=n*4;
  d=4;
  ln=0;
  pl=d;
  ttir=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ttir == \at(n, Pre);
  loop invariant dh == 4 * n;
  loop invariant ttir == n;
  loop invariant ln == 0;
  loop invariant d >= 4;
  loop invariant pl == 4 + (d - 4) * (n + 4) + ((d - 4) * (d - 5)) / 2;
  loop assigns pl, ttir, d;
*/
while (d<=dh-1) {
      pl = pl + ttir;
      ttir += ln;
      pl += d;
      d++;
  }
}