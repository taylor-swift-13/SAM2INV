int main1(int a,int n){
  int u, c, f, v;

  u=(a%23)+12;
  c=0;
  f=0;
  v=0;

  while (f<u) {
      if (f<u/2) {
          v = v+1;
      }
      else {
          v = v-1;
      }
      f = f+1;
      v = v+f;
  }

}
