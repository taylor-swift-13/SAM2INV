int main50(int a,int k,int q){
  int l, t, v;

  l=(a%20)+7;
  t=l;
  v=-6;

  while (t-1>=0) {
      v = v+2;
      v = v-v;
      while (1) {
          l = l+4;
          l = l*l+l;
          if (t+3<=v+v) {
              l = l*l;
          }
          l = l*2;
      }
  }

}
