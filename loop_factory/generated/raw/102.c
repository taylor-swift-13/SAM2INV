int main102(int a,int b,int q){
  int v, h, s, m;

  v=(q%25)+9;
  h=v;
  s=h;
  m=a;

  while (h>0) {
      if (h<v/2) {
          s = s+m;
      }
      else {
          s = s*m;
      }
      s = s*s+s;
      s = s%4;
  }

  while (1) {
      if (h>=s) {
          break;
      }
      m = m+2;
      h = h+1;
      m = m+1;
  }

}
