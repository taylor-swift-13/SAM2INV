int main1(int b,int n){
  int s, p, c;

  s=39;
  p=s+2;
  c=5;

  while (p>=1) {
      c = c*c+c;
      c = c%9;
      p = p/2;
  }

}
