int main1(int a,int k){
  int r, g, d;

  r=(k%14)+14;
  g=r;
  d=k;

  while (g>0) {
      d = d*d;
      if (g+3<=r+r) {
          d = d*d+d;
      }
      g = g-1;
  }

}
