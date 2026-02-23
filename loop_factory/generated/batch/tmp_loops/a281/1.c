int main1(int n,int q){
  int y, b, v, a;

  y=(n%19)+13;
  b=0;
  v=0;
  a=-6;

  while (b<=y-1) {
      v = v*4+1;
      a = a*v+1;
  }

}
