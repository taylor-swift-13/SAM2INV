int main107(int l){
  int j, e5m, m, njs, v4, n, xg, mak;

  j=l;
  e5m=j;
  m=(l%20)+5;
  njs=4;
  v4=e5m;
  n=j;
  xg=0;
  mak=l;

  while (m>0) {
      xg = xg + 3;
      m -= 1;
      njs = njs + 3;
      v4 += 2;
      mak = mak + m;
      v4 += n;
  }

}
