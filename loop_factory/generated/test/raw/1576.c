int main1(int g){
  int m8, f6, c, iw, e, ow, sn, p;

  m8=g+3;
  f6=0;
  c=0;
  iw=0;
  e=0;
  ow=3;
  sn=5;
  p=2;

  while (f6<m8) {
      iw += 1;
      e += 1;
      if (iw>=3) {
          iw = iw - 3;
          c = c + 1;
      }
      f6 = f6 + 1;
      if (f6+7<=iw+m8) {
          g++;
      }
      sn += f6;
      g = ow+sn+p;
      ow += 1;
      sn = ow+c;
      g += ow;
  }

}
