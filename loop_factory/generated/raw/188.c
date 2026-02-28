int main188(int a,int b,int q){
  int h, l, v;

  h=(b%36)+8;
  l=0;
  v=4;

  while (1) {
      v = v*v+v;
      v = v*v;
      l = l+1;
  }

  while (v*2<=h) {
      l = l+3;
      l = l+l;
      if (v+1<=h+h) {
          l = l+v;
      }
      else {
          l = l+l;
      }
  }

  while (h>=2) {
      l = l+2;
      l = l*l;
  }

}
