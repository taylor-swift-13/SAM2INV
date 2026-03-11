int main1(){
  int li, ojw, pn, h;

  li=66;
  ojw=li;
  pn=2;
  h=1;

  while (ojw<li) {
      if (!(pn<8)) {
          h = -1;
      }
      if (pn<=2) {
          h = 1;
      }
      ojw = ojw + 1;
      pn += h;
  }

}
