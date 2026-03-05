int main1(){
  int rc, a, dj, az;
  rc=65;
  a=0;
  dj=2;
  az=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a <= rc;
  loop invariant a >= 0;
  loop invariant dj <= 4*a + 2;
  loop invariant (az == 1) || (az == -1);
  loop invariant (dj - 2*a) >= 2;
  loop invariant rc == 65;
  loop invariant (dj % 2) == 0;
  loop assigns a, dj, az;
*/
while (a<rc) {
      if (dj>=9) {
          az = -1;
      }
      if (dj<=2) {
          az = 1;
      }
      dj = dj + az;
      a++;
      dj = dj + 3;
  }
}