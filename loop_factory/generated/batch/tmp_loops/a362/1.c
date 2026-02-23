int main1(int k,int n){
  int m, a, v, t;

  m=70;
  a=0;
  v=a;
  t=-5;

  while (v!=0&&t!=0) {
      if (v>t) {
          v = v-t;
      }
      else {
          t = t-v;
      }
      t = t+t;
      t = t+v;
  }

}
