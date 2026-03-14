int main1(){
  int ll, zv, jcz, lc, j, z0ub;
  ll=1;
  zv=ll;
  jcz=3;
  lc=0;
  j=0;
  z0ub=zv;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z0ub == 1 + lc*(lc+1)/2 + 3*lc;
  loop invariant 0 <= lc;
  loop invariant lc <= ll;
  loop invariant 0 <= z0ub;
  loop invariant z0ub >= ll;
  loop invariant lc == jcz - 3;
  loop invariant j >= 0;
  loop assigns lc, jcz, z0ub, j;
*/
while (lc<=ll-1) {
      lc = lc + 1;
      jcz = jcz + 1;
      z0ub = z0ub + jcz;
      j = j*3+1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j >= 0;
  loop invariant lc >= 1;
  loop invariant jcz - lc == 3;
  loop invariant jcz >= ll;
  loop assigns lc, j, jcz;
*/
while (1) {
      if (jcz%2==0) {
          lc += j;
      }
      else {
          lc = lc+j+1;
      }
      j = j + jcz;
      jcz = jcz + 1;
      if (jcz>=ll) {
          break;
      }
  }
}