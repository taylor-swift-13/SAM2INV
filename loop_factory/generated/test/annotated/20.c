int main1(){
  int g, zjd;
  g=1*2;
  zjd=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zjd % 7 == 0;
  loop invariant zjd <= g;
  loop invariant 0 <= zjd;
  loop assigns zjd;
*/
for (; zjd+7<=g; zjd = zjd + 7) {
  }
}