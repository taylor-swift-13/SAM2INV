int main1(int a,int b,int m,int q){
  int l, i, v, u;

  l=q;
  i=0;
  v=b;
  u=l;

  while (i<l) {
      if (i<l/2) {
          v = v+u;
      }
      else {
          v = v+1;
      }
      v = v+1;
      u = u+v;
      v = v+6;
      v = u-v;
      if (i<v+1) {
          v = v-b;
      }
  }

}
