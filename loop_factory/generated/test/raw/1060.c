int main1(int a){
  int od9, mi, iso, tkm, f89, l7;

  od9=a-5;
  mi=od9;
  iso=2;
  tkm=0;
  f89=mi;
  l7=a*3;

  while (mi-1>=0) {
      tkm = tkm+iso*mi;
      a += mi;
      f89 = f89+(tkm%7);
      mi++;
  }

  while (mi<od9) {
      l7 += tkm;
      tkm = tkm + l7;
      iso = iso + l7;
      mi = od9;
  }

}
