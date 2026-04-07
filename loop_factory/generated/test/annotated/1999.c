int main1(){
  int qz, wvn, jmbw, a44, np3b;
  qz=23;
  wvn=0;
  jmbw=0;
  a44=qz;
  np3b=1+4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= wvn;
  loop invariant wvn <= qz;
  loop invariant a44 == 23 + (wvn * (wvn + 1)) / 2;
  loop invariant (wvn > 0) ==> (np3b == wvn * (a44 - wvn));
  loop invariant jmbw >= 0;
  loop invariant np3b >= 0;
  loop assigns np3b, jmbw, wvn, a44;
*/
while (1) {
      if (!(wvn < qz)) {
          break;
      }
      np3b = (wvn + 1) * a44;
      jmbw = jmbw + np3b;
      wvn += 1;
      a44 = a44 + wvn;
  }
}