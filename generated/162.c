int main162(int e,int l,int p){
  int wv, m, b3, pl, ru, zrad, qlk, w2p;

  wv=17;
  m=wv+2;
  b3=0;
  pl=e;
  ru=0;
  zrad=e;
  qlk=4;
  w2p=m;

  while (m>=wv+1) {
      b3 = b3 + 9;
      pl = pl + b3;
      ru += pl;
      w2p = w2p + 3;
      qlk = qlk+(ru%6);
      zrad = zrad+(ru%9);
  }

}
