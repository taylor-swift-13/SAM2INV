int main1(int p){
  int uyx6, rsa, cfy, kvt, b2ry, hwqr, au, zr, a2j, j0c;
  uyx6=(p%21)+9;
  rsa=0;
  cfy=rsa;
  kvt=p+2;
  b2ry=p;
  hwqr=25;
  au=p;
  zr=rsa;
  a2j=rsa;
  j0c=uyx6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uyx6 == (\at(p, Pre) % 21) + 9;
  loop invariant 0 <= zr <= rsa;
  loop invariant 0 <= cfy <= rsa;
  loop invariant (rsa == 0) ==> (j0c == uyx6) && (a2j == 0);
  loop invariant \at(p,Pre) <= b2ry <= \at(p,Pre) + rsa;
  loop invariant \at(p,Pre) + 2 <= kvt <= \at(p,Pre) + 2 + rsa;
  loop invariant \at(p,Pre) <= au <= \at(p,Pre) + rsa;
  loop assigns a2j, cfy, kvt, b2ry, j0c, hwqr, au, zr, p, rsa;
*/
while (rsa < uyx6) {
      a2j = rsa % p;
      if ((a2j == 0)) {
          cfy++;
      }
      if ((a2j == 1)) {
          kvt += 1;
      }
      if ((a2j == 2)) {
          b2ry += 1;
      }
      j0c = a2j;
      hwqr = hwqr + a2j;
      if ((rsa % p == 0)) {
          au++;
      }
      else {
          zr += 1;
      }
      p += zr;
      rsa += 1;
      p += p;
  }
}