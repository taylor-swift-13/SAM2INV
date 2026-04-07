int main1(){
  int spo, en, hw, yjl, m, w, s1, h, nd6;
  spo=41;
  en=0;
  hw=spo;
  yjl=6;
  m=-8;
  w=en;
  s1=spo;
  h=en;
  nd6=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == (en + 1) / 3;
  loop invariant h == en / 3;
  loop invariant nd6 == -8 + 3 * (en / 3);
  loop invariant 0 <= en <= spo;
  loop invariant (en == 0) ==> s1 == spo;
  loop invariant (en == 0) ==> yjl == 6;
  loop invariant (en > 0) ==> yjl == 6 + 2 * (en - ((en - 1) / 3) - 1);
  loop invariant hw == spo + en - ((en + 2) / 3);
  loop invariant hw == 41 + en - ((en + 2) / 3);
  loop invariant s1 >= 41;
  loop invariant s1 >= spo * (en + 1);
  loop invariant m <= -8;
  loop assigns en, hw, yjl, m, w, h, nd6, s1;
*/
while (en < spo) {
      if (!(!((en % 3) == 0))) {
      }
      else {
          hw++;
          yjl += 2;
      }
      if ((en % 3) == 1) {
          m = m * 2;
          w += 1;
      }
      else {
      }
      if ((en % 3) == 2) {
          h += 1;
          nd6 = nd6 + 3;
      }
      else {
      }
      s1 = s1 + w;
      en++;
      s1 += s1;
  }
}