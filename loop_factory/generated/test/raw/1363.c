int main1(int b,int u){
  int yc6, e, r, eaiv;

  yc6=u*2;
  e=yc6;
  r=5;
  eaiv=0;

  while (e>=1) {
      eaiv = eaiv*eaiv+r;
      r = r%3;
      e = e - 1;
  }

}
