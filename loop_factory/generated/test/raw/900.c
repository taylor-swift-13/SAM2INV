int main1(){
  int fr, nolv, ulaw, xn;

  fr=77;
  nolv=0;
  ulaw=1;
  xn=0;

  while (ulaw<fr) {
      ulaw = 2*ulaw;
      xn += 1;
      xn = (nolv)+(xn);
  }

}
