int main1(){
  int sdn, c, s, ui, lw;

  sdn=1*3;
  c=0;
  s=0;
  ui=3;
  lw=sdn;

  while (c<sdn&&ui>0) {
      s += ui;
      c = c + 1;
      lw = lw + c;
      ui--;
  }

}
