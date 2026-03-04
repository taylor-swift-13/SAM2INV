int main84(int a,int b,int n){
  int k, u, v;

  k=b;
  u=k;
  v=2;

  while (u-1>=0) {
      if (v==1) {
          v = 2;
      }
      else {
          if (v==2) {
              v = 1;
          }
      }
      v = v+1;
      v = v-v;
      if (v+7<k) {
          v = v+a;
      }
  }

}
