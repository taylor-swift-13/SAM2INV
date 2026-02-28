int main148(int k,int m,int n){
  int a, v, h;

  a=k;
  v=a;
  h=k;

  while (v>=1) {
      h = h*2;
      h = h*h;
      v = v-1;
  }

  while (a>0) {
      v = v+3;
      if (h*h<=h+2) {
          v = v*v;
      }
      else {
          v = v%6;
      }
      while (a-1>=0) {
          v = v+2;
          v = v*v;
      }
  }

}
