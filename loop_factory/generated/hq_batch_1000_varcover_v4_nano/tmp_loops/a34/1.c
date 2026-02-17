int main1(int k,int m,int n,int q){
  int l, i, v, p, r, d, o, c, h;

  l=(m%27)+13;
  i=l;
  v=(m%60)+60;
  p=(m%9)+2;
  r=0;
  d=0;
  o=m;
  c=n;
  h=m;

  while (v>p*r+d) {
      if (d==p-1) {
          d = 0;
          r = r+1;
      }
      else {
          d = d+1;
      }
      v = v*3;
      p = p/3;
  }

}
