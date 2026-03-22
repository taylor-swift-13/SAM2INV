int main1(){
  int nm, y7, w4;
  nm=1;
  y7=0;
  w4=nm;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y7 >= 0;
  loop invariant y7 % 5 == 0;
  loop invariant nm == 1;
  loop invariant w4 == 1 - (y7/5) + (5 * (y7/5) * ((y7/5) + 1)) / 2;
  loop assigns w4, y7;
*/
while (y7<nm&&w4>0) {
      w4--;
      y7 = (1)+(y7);
      y7 += 4;
      w4 += y7;
  }
}