int main1(int m,int p){
  int h, t, v;

  h=(p%28)+16;
  t=0;
  v=m;

  while (1) {
      v = v+2;
      if (t+5<=p+h) {
          v = v-v;
      }
      else {
          v = v+t;
      }
  }

}
