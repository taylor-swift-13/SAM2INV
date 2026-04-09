int main1(){
  int b2r, o2, gu, pvo, u5;
  b2r=1+12;
  o2=0;
  gu=o2;
  pvo=1;
  u5=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gu == o2 * (o2 + 1) / 2;
  loop invariant ((o2 <= b2r) && ((o2 == 0) ==> (u5 == 0)) && ((o2 > 0) ==> (u5 == 1)));
  loop invariant 0 <= o2;
  loop invariant u5 + pvo == 1;
  loop invariant 2 * gu == o2 * (o2 + 1);
  loop invariant (o2 == 0 && pvo == 1) || (o2 >= 1 && pvo == 0);
  loop invariant (o2 == 0 && u5 == 0) || (o2 >= 1 && u5 == 1);
  loop assigns u5, pvo, o2, gu;
*/
while (o2 < b2r) {
      u5 = u5 + pvo;
      pvo = pvo * gu;
      o2 += 1;
      gu = gu + o2;
  }
}