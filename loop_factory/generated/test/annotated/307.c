int main1(){
  int qhr, ev, i6, i, en, fam1;
  qhr=61;
  ev=2;
  i6=-1;
  i=0;
  en=3;
  fam1=ev;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == ((i6+1)*(i6-2))/2;
  loop invariant en == 3 + (i6+1)*qhr;
  loop invariant (qhr - i6) >= 0;
  loop invariant en - qhr * i6 == 64;
  loop assigns i, i6, en;
*/
while (i6<qhr) {
      i = i + i6;
      i6 = i6 + 1;
      en = en + qhr;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop assigns i, en, fam1;
*/
while (i<ev) {
      fam1 = ev-i;
      i += 2;
      en = en + qhr;
  }
}