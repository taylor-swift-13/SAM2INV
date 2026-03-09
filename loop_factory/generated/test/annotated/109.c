int main1(int a){
  int wh, dl8, p6;
  wh=0;
  dl8=(a%20)+10;
  p6=(a%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dl8 + p6 == ((\at(a,Pre) % 20) + 10) + ((\at(a,Pre) % 15) + 8) - wh;
  loop invariant 0 <= wh;
  loop invariant dl8 == ((\at(a,Pre) % 20) + 10) - ((wh + 1) / 2);
  loop invariant p6  == ((\at(a,Pre) % 15) + 8) - (wh / 2);
  loop assigns dl8, p6, wh;
*/
for (; dl8>0&&p6>0; wh++) {
      if (!(!(wh%2==0))) {
          dl8--;
      }
      else {
          p6 -= 1;
      }
  }
}