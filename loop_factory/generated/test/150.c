int main150(int b,int m,int p){
  int y, s, v, l;

  y=b;
  s=0;
  v=0;
  l=s;

  while (s<=y-2) {
      l = y-v;
      v = v+1;
  }

  while (s>1) {
      v = v*4;
      y = y/4;
      v = v*2;
      y = y+v;
  }

  while (y-4>=0) {
      if (v+2<=s) {
          v = v+2;
      }
      else {
          v = s;
      }
  }

}
