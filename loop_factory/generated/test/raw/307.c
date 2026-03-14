int main1(){
  int qhr, ev, i6, i, en, fam1;

  qhr=61;
  ev=2;
  i6=-1;
  i=0;
  en=3;
  fam1=ev;

  while (i6<qhr) {
      i = i + i6;
      i6 = i6 + 1;
      en = en + qhr;
  }

  while (i<ev) {
      fam1 = ev-i;
      i += 2;
      en = en + qhr;
  }

}
