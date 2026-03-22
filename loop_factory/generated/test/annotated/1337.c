int main1(){
  int gvo, li, g7ee;
  gvo=0;
  li=(1%28)+10;
  g7ee=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant li == 11 - gvo*(gvo-1)/2;
  loop invariant g7ee == 11*gvo - (gvo*(gvo-1)*(gvo+1))/6;
  loop invariant gvo >= 0;
  loop invariant li >= 0;
  loop assigns li, gvo, g7ee;
*/
while (li>gvo) {
      li -= gvo;
      gvo += 1;
      g7ee = (li)+(g7ee);
  }
}