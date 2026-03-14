int main1(){
  int hmy, k, pck3, im, hhr9;
  hmy=1+3;
  k=-2;
  pck3=0;
  im=k;
  hhr9=hmy;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant im == -2 + hmy * (pck3 / 2);
  loop invariant pck3 <= hmy;
  loop invariant pck3 % 2 == 0;
  loop invariant hhr9 <= hmy;
  loop invariant (hmy == 4);
  loop invariant pck3 >= 0;
  loop assigns pck3, hhr9, im;
*/
while (pck3<hmy) {
      pck3 += 2;
      if (!(!(pck3<=hhr9))) {
          hhr9 = pck3;
      }
      im += hmy;
  }
}