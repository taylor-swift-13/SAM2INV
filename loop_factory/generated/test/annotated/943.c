int main1(){
  int zmc, xyy, wa;
  zmc=3;
  xyy=(1%20)+10;
  wa=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zmc + xyy + wa == 23;
  loop invariant zmc >= 3;
  loop invariant xyy >= 0;
  loop invariant wa >= 0;
  loop invariant xyy == 11 - ((zmc - 3) / 2);
  loop assigns zmc, xyy, wa;
*/
for (; xyy>0&&wa>0; zmc = zmc + 1) {
      if (!(!(zmc%2==0))) {
          xyy = xyy - 1;
      }
      else {
          wa--;
      }
  }
}