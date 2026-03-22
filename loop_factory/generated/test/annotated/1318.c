int main1(){
  int gf, uce, lh, oc;
  gf=0;
  uce=0;
  lh=(1%28)+10;
  oc=gf;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uce >= 0;
  loop invariant lh == 11 - ((uce * (uce - 1)) / 2);
  loop assigns lh, uce, oc;
*/
while (lh>uce) {
      lh = lh - uce;
      uce += 1;
      oc = oc + gf;
      oc = oc*4+1;
  }
}