int main1(){
  int mr41, zfy, g166, ux;
  mr41=1;
  zfy=3;
  g166=0;
  ux=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (g166 == 0) ==> (ux == -2);
  loop invariant ux - g166 >= -2;
  loop invariant g166 == ((zfy - 1) * zfy * (2 * zfy - 1)) / 6 - 5;
  loop invariant zfy >= 3;
  loop assigns g166, ux, zfy;
*/
while (1) {
      if (!(zfy<=mr41)) {
          break;
      }
      g166 = g166+zfy*zfy;
      ux += g166;
      zfy = zfy + 1;
  }
}