int main1(){
  int mn, mr, g;
  mn=(1%20)+5;
  mr=(1%20)+5;
  g=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == mn;
  loop invariant mr - 4*mn - g >= -24;
  loop invariant 0 <= mn <= 6;
  loop invariant 0 <= g <= 6;
  loop invariant mr >= 5;
  loop assigns mn, mr, g;
*/
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


  int __aux_6=0;
  while (__aux_6 < 2) { __aux_6 = __aux_6 + 1; }
}