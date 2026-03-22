int main1(){
  int pmz, ig, ermz, j0y, i, e, ibh, g5, mg6;
  pmz=1-6;
  ig=0;
  ermz=0;
  j0y=0;
  i=ig;
  e=pmz;
  ibh=13;
  g5=ig;
  mg6=ig;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ig;
  loop invariant i == ig/2;
  loop invariant ermz == 3*ig + (ig + 1)/2;
  loop invariant j0y == 2 * ((ig + 1) / 2);
  loop invariant ibh == 13 + 4*ig;
  loop invariant mg6 == (ig/2) * ((ig + 1) / 2);
  loop invariant g5 == i;
  loop invariant e <= (1 - 6);
  loop invariant pmz == (1 - 6);
  loop assigns e, ermz, g5, i, ibh, ig, j0y, mg6;
*/
while (ig < pmz) {
      if (!(!(((ig % 2) == 0)))) {
          j0y += 2;
          ig++;
      }
      else {
          i = i + 1;
          g5 = g5 + 1;
          ig++;
      }
      if (ig+6<=i+pmz) {
          e = e+(-1);
      }
      ermz = ermz+(ig%2);
      ibh++;
      mg6 += g5;
      ibh = ibh + 3;
      ermz = ermz + 3;
  }
}