int main1(int q,int w){
  int md, g7r, fxwi, z;
  md=w+6;
  g7r=md;
  fxwi=0;
  z=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g7r == md + fxwi;
  loop invariant z == 5 - (fxwi * (fxwi - 1)) / 2;
  loop invariant fxwi >= 0;
  loop assigns fxwi, z, g7r;
*/
while (g7r-5>=0) {
      fxwi += 1;
      z = (z+md)+(-(g7r));
      g7r += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z <= 5;
  loop assigns z;
*/
while (1) {
      if (!(z>=6)) {
          break;
      }
      z -= 6;
  }
}