int main1(){
  int mn, mr, g;
  mn=(1%20)+5;
  mr=(1%20)+5;
  g=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */

while (mn>0) {
      if (mr>0) {
          if (g>0) {
              mn--;
              mr -= 1;
              g -= 1;
          }
      }
      mr = mr + 5;
  }
/*@
  assert !(mn>0) &&
         (g == mn);
*/

}