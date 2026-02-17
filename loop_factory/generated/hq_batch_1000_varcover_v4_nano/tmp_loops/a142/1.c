int main1(int m,int n,int p,int q){
  int l, i, v, x, r;

  l=n+19;
  i=l;
  v=4;
  x=m;
  r=-4;

  while (i>0) {
      x = x+r;
      r = r+v;
      if ((i%6)==0) {
          r = r+i;
      }
      r = r-5;
      r = x-r;
      i = i-1;
  }

}
