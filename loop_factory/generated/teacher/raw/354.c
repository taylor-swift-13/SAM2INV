int main1(int k,int n){
  int d, b, v;

  d=k;
  b=0;
  v=d;

  while (b+1<=d) {
      v = v%3;
      v = v*v;
      b = b+1;
  }

}
