int main172(int m,int n,int p){
  int h, v, i, a;

  h=n-7;
  v=1;
  i=v;
  a=n;

  while (v*2<=h) {
      a = i;
      i = i+2;
      i = i*2;
  }

  while (h<a) {
      v = v+3;
      if ((h%2)==0) {
          v = v+h;
      }
  }

  while (i<h) {
      v = v+1;
      a = a-1;
  }

}
