int main1(){
  int pw, vt, m4, c9, rfi, xs;

  pw=1*5;
  vt=1;
  m4=0;
  c9=0;
  rfi=0;
  xs=5;

  while (vt<pw) {
      c9 = vt%5;
      if (!(!(vt>=xs))) {
          rfi = (vt-xs)%5;
          m4 = m4+c9-rfi;
      }
      else {
          m4 += c9;
      }
      vt = vt + 1;
      xs += c9;
  }

}
