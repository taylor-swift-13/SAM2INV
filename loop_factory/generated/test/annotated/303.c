int main1(int n){
  int iy, ni, szlo, fv, je;
  iy=n;
  ni=4;
  szlo=3;
  fv=0;
  je=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fv == ((szlo - 1) * szlo * (2 * szlo - 1)) / 6 - 5;
  loop invariant je == n + (szlo - 3) * ni;
  loop invariant 3 <= szlo;
  loop invariant je == \at(n, Pre) + ni*(szlo - 3) &&
                   fv == ((szlo - 1) * szlo * (2 * szlo - 1)) / 6 - 5;
  loop invariant n == \at(n, Pre);
  loop invariant je == \at(n,Pre) + ni * (szlo - 3);
  loop invariant iy == \at(n,Pre);
  loop assigns fv, szlo, je;
*/
while (szlo<=iy) {
      fv = fv+szlo*szlo;
      szlo = szlo + 1;
      je = je + ni;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ni;
  loop invariant iy == \at(n,Pre);
  loop invariant n >= \at(n,Pre);
  loop assigns n, ni, szlo;
*/
while (1) {
      if (!(szlo<je)) {
          break;
      }
      szlo = szlo + 1;
      ni = je-szlo;
      n = n + ni;
  }
}