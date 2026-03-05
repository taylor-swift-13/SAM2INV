int main94(int j,int v){
  int o, nj, at, u, t2cw, o3ra, tbl, w2;

  o=v*4;
  nj=o+4;
  at=0;
  u=(j%28)+10;
  t2cw=v;
  o3ra=nj;
  tbl=(j%18)+5;
  w2=0;

  while (1) {
      if (!(u>at)) {
          break;
      }
      u = u - at;
      at = at + 1;
      t2cw += nj;
      t2cw = t2cw*2+2;
      o3ra = o3ra+(at%7);
      j = j + at;
  }

  while (1) {
      if (!(tbl>0)) {
          break;
      }
      w2 = w2+v*v;
      tbl = tbl+j*j;
      tbl = tbl+j*v;
      tbl -= 1;
      j += tbl;
      j = j*2+1;
  }

}
