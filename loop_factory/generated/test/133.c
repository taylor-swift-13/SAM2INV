int main133(int k,int m,int n){
  int b, w, v, c;

  b=65;
  w=b;
  v=k;
  c=m;

  while (w>0) {
      v = v+c;
      c = c+c;
      w = w/2;
  }

  while (1) {
      b = w-v;
      v = v+1;
      v = v+c;
      b = b*b;
      b = b+v*b;
  }

}
