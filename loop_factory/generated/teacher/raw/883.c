int main1(int k,int n){
  int r, c, x, v;

  r=(k%35)+17;
  c=1;
  x=r;
  v=r;

  while (c+1<=r) {
      x = x*x+x;
      x = x%3;
      c = c+1;
  }

}
