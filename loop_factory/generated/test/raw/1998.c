int main1(){
  int qz, wvn, jmbw, a44, np3b;

  qz=23;
  wvn=0;
  jmbw=0;
  a44=qz;
  np3b=1+4;

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
