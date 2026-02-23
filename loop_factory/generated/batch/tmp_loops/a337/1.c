int main1(int k,int p){
  int r, i, u;

  r=(p%19)+5;
  i=0;
  u=k;

  while (i<=r-1) {
      u = u+u;
      if (p<p+5) {
          u = u+2;
      }
      i = i+1;
  }

}
