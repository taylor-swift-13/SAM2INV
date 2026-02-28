int main1(int m,int p){
  int l, u, v, j, b, s;

  l=p+14;
  u=l+3;
  v=m;
  j=-6;
  b=-4;
  s=l;

  while (1) {
      if (v>=l) {
          break;
      }
      if (b<=j) {
          j = b;
      }
      v = v+1;
      v = v+j;
  }

}
