int main1(){
  int y4, c, wmn, vcug, qe, f7, f, e6b, h8, wxdq;

  y4=(1%38)+12;
  c=0;
  wmn=0;
  vcug=0;
  qe=0;
  f7=0;
  f=0;
  e6b=0;
  h8=0;
  wxdq=0;

  while (1) {
      if (!(c < y4)) {
          break;
      }
      c = c + 1;
      if ((c % 4) == 0) {
          wmn += 1;
      }
      if (!(!((c % 4) == 1))) {
          vcug += 1;
      }
      if ((c % 4) == 2) {
          qe++;
      }
      if ((c % 4) == 3) {
          f7++;
      }
      f = f + 1;
      h8 = h8 + vcug;
      e6b += f;
      e6b += 4;
      wxdq += 1;
  }

}
