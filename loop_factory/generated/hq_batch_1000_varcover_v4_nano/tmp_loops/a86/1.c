int main1(int a,int b,int p,int q){
  int l, i, v, w, j, f, s, k, r, y;

  l=45;
  i=1;
  v=(b%60)+60;
  w=(b%9)+2;
  j=0;
  f=0;
  s=b;
  k=b;
  r=q;
  y=a;

  while (v>w*j+f) {
      if (f==w-1) {
          f = 0;
          j = j+1;
      }
      else {
          f = f+1;
      }
      v = v*2;
      w = w+v;
  }

}
