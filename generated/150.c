int main150(int m,int q){
  int l9r, kq, e, rpgz, f, d4l;

  l9r=35;
  kq=1;
  e=2;
  rpgz=kq;
  f=q;
  d4l=-4;

  while (1) {
      if (!(kq<l9r)) {
          break;
      }
      rpgz = rpgz*rpgz+e;
      e = e%9;
      m = m*2;
      if (kq*kq<=l9r+3) {
          f = f*d4l;
      }
      kq = kq*2;
  }

}
