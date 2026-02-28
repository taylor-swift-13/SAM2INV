int main1(int a,int m){
  int r, k, v, x;

  r=m+19;
  k=1;
  v=m;
  x=-3;

  while (1) {
      if (k<r/2) {
          v = v+x;
      }
      else {
          v = v+1;
      }
      v = v+5;
      x = x+v;
      x = x+x;
      v = v+2;
      x = x+k;
  }

}
