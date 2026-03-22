int main1(){
  int h, vn4, md3, kr;
  h=1*2;
  vn4=0;
  md3=0;
  kr=-5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kr <= -5;
  loop invariant md3 + 5*vn4 <= 0;
  loop invariant 0 <= vn4 <= h;
  loop assigns vn4, md3, kr;
*/
while (vn4 < h) {
      vn4++;
      md3 = md3 + kr;
      kr = kr+(md3%6);
  }
}