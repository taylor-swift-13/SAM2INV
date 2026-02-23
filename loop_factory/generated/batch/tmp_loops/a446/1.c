int main1(int a,int n){
  int x, i, r, v;

  x=a+23;
  i=1;
  r=-2;
  v=6;

  while (i<=x/3) {
      r = r*4+5;
      v = v*r+5;
      i = i*3;
  }

}
