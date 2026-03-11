int main1(){
  int zmf, k, d4n3, z, e;
  zmf=50;
  k=zmf;
  d4n3=0;
  z=0;
  e=zmf;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d4n3 == z;
  loop invariant 0 <= z <= zmf;
  loop invariant (e % zmf) == 0;
  loop invariant e >= 0;
  loop assigns z, e, d4n3;
*/
while (z<zmf) {
      z += 1;
      e = e + zmf;
      d4n3++;
      e = e*2;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d4n3 == z;
  loop invariant 0 <= z <= zmf;
  loop invariant e >= 0;
  loop invariant k >= 0;
  loop invariant k >= 50;
  loop assigns e, k, d4n3;
*/
while (d4n3<=z-1) {
      e = e+k*d4n3;
      k = k+(e%3);
      d4n3 = z;
  }
}