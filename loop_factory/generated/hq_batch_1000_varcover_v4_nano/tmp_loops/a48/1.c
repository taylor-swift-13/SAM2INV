int main1(int b,int n,int p,int q){
  int l, i, v, x, c, f;

  l=32;
  i=1;
  v=(b%60)+60;
  x=(b%9)+2;
  c=0;
  f=0;

  while (v>x*c+f) {
      if (f==x-1) {
          f = 0;
          c = c+1;
      }
      else {
          f = f+1;
      }
  }

}
