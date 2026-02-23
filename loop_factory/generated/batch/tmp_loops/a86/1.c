int main1(int b,int n){
  int d, j, v, c;

  d=n-6;
  j=d;
  v=-8;
  c=j;

  while (j>=1) {
      if (v+2<=d) {
          v = v+2;
      }
      else {
          v = d;
      }
      v = v*v+v;
      v = v%6;
  }

}
