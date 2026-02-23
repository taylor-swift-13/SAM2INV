int main1(int b,int m){
  int j, x, v, q;

  j=32;
  x=j+2;
  v=x;
  q=j;

  while (x>1) {
      v = v*4+4;
      q = q*v+4;
      v = v*v+v;
  }

}
