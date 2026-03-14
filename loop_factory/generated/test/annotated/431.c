int main1(){
  int skn, f1l, h3, h7, eun, ni;
  skn=24;
  f1l=0;
  h3=1;
  h7=2;
  eun=25;
  ni=f1l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f1l == 0;
  loop invariant 0 <= h3 <= skn + 1;
  loop invariant h3 >= 1;
  loop invariant eun == 25 + (h3 - 1) * f1l;
  loop invariant h7 == (h3 - 1) * (h3 - 1) + 2;
  loop assigns h7, eun, h3;
*/
while (h3<=skn) {
      h7 = h7+2*h3-1;
      eun = eun + f1l;
      h3 += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ni == h3 - eun;
  loop invariant h7 == 2 + (h3 - 1) * (h3 - 1);
  loop invariant eun <= h3;
  loop invariant eun >= 25;
  loop invariant (h7 % 9 != 0);
  loop invariant h3 == 25;
  loop assigns ni, eun;
*/
while (eun<h3) {
      ni = (h3)+(-(eun));
      eun++;
      if ((h7%9)==0) {
          ni = ni + h7;
      }
  }
}