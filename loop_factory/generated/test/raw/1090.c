int main1(){
  int eqy, upqf, cl, m, vsw, h;

  eqy=1+21;
  upqf=eqy;
  cl=0;
  m=(1%28)+10;
  vsw=eqy;
  h=eqy;

  while (m>cl) {
      m = m - cl;
      cl = cl + 1;
      vsw = vsw+(m%4);
      vsw = (vsw)+(vsw*vsw);
  }

  while (h>vsw) {
      h -= vsw;
      vsw++;
      m = m+(vsw%9);
      upqf += 2;
  }

}
