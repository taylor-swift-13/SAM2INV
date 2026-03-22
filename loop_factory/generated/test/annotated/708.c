int main1(int n,int u){
  int ce, ny, y, dmt, zz9;
  ce=53;
  ny=ce;
  y=0;
  dmt=n;
  zz9=(n%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y >= 0;
  loop invariant ny >= 0;
  loop invariant n == \at(n,Pre) + ce * (((\at(n,Pre) % 35) + 8) - zz9);
  loop invariant ny >= 53;
  loop invariant dmt >= \at(n,Pre);
  loop invariant (n - \at(n, Pre)) == 53 * ( ((\at(n, Pre)) % 35) + 8 - zz9 );
  loop invariant zz9 <= ((\at(n, Pre) % 35) + 8);
  loop invariant (n - \at(n, Pre)) % ce == 0;
  loop assigns ny, dmt, y, n, zz9;
*/
while (1) {
      if (!(zz9>0)) {
          break;
      }
      ny = ny+y*y;
      dmt = dmt+zz9*zz9;
      y = y+zz9*zz9;
      n += ce;
      zz9 -= 1;
  }
}