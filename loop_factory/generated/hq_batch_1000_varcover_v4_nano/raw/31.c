int main1(int b,int k,int m){
  int l, i, v, x, u;

  l=52;
  i=l;
  v=l;
  x=l;
  u=4;

  while (i>0) {
      x = x+u;
      u = u+v;
      if (u+2<l) {
          x = x+2;
      }
      i = i-1;
  }

}
