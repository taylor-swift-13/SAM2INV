int main1(int n,int l){
  int vw, f, h3, is, jd;

  vw=65;
  f=16;
  h3=5;
  is=1;
  jd=vw;

  while (f<=vw) {
      h3 = h3*f;
      if (f<vw) {
          is = is*f;
      }
      f = f + 1;
      jd += f;
  }

}
