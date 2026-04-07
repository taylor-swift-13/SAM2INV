int main1(){
  int bf, fc0, s, t, d, uk, wv9, ad2, wsnl;
  bf=122;
  fc0=0;
  s=1;
  t=12;
  d=4;
  uk=bf;
  wv9=25;
  ad2=1+3;
  wsnl=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uk == bf + ((fc0 + 1) / 2);
  loop invariant t == 12 + (fc0 / 2);
  loop invariant d == 4 + 2 * (fc0 / 2);
  loop invariant 0 <= fc0 <= bf;
  loop invariant uk == 122 + (fc0 + 1) / 2;
  loop invariant wv9 >= 25;
  loop invariant wsnl >= 0;
  loop invariant ad2 >= 4;
  loop invariant ad2 - 2*fc0 >= 4;
  loop invariant uk == bf + s - 1;
  loop assigns s, uk, t, d, fc0, wv9, ad2, wsnl;
*/
while (fc0 < bf) {
      if ((fc0 % 2) == 0) {
          s++;
          uk += 1;
      }
      else {
          t += 1;
          d += 2;
      }
      fc0 = fc0 + 1;
      if (fc0<t+3) {
          wv9 = wv9 + fc0;
      }
      ad2 += 2;
      wsnl = wsnl + s;
      ad2 += wsnl;
      wsnl += wv9;
  }
}