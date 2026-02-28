int main1(int b,int k,int m,int p){
  int a, r, v, h;

  a=p+13;
  r=1;
  v=k;
  h=-2;

  while (1) {
      if (v+2<=a) {
          v = v+2;
      }
      else {
          v = a;
      }
      v = v+1;
      h = h-1;
      v = v+1;
      h = h+v;
      h = v-h;
  }

}
