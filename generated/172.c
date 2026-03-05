int main172(int i,int c,int s){
  int x, v, gu, pw, b4a, aqk, u;

  x=101;
  v=x+5;
  gu=v;
  pw=x;
  b4a=8;
  aqk=(s%6)+2;
  u=4;

  while (b4a<x) {
      gu = gu*aqk+2;
      pw = pw*aqk;
      b4a = b4a+(pw%3);
      u = u+(pw%3);
      aqk = aqk+(pw%5);
      c = c + pw;
  }

}
