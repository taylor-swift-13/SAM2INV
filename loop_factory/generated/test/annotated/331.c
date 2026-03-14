int main1(){
  int ii, d, xiyz, n;
  ii=1*3;
  d=0;
  xiyz=-2;
  n=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d >= 0;
  loop invariant ii == 3;
  loop invariant d == xiyz + 2;
  loop invariant xiyz <= ii;
  loop invariant n % 2 == 0;
  loop invariant n >= 8;
  loop assigns xiyz, d, n;
*/
while (xiyz<ii) {
      xiyz = xiyz + 1;
      d++;
      n = n+(d%6);
      n = n*4+2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d >= 5;
  loop assigns xiyz, ii, d;
*/
while (d>5) {
      xiyz = xiyz+ii*d;
      ii += xiyz;
      d = 5;
  }
}