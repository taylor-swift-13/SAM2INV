int main1(int x){
  int ko, t6, iq, so;

  ko=0;
  t6=0;
  iq=0;
  so=(x%18)+5;

  while (so>=1) {
      so -= 1;
      t6 = t6+x*x;
      iq = iq+x*x;
      ko = ko+x*x;
      x += so;
  }

}
