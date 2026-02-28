int main1(int p,int q){
  int t, g, v;

  t=q;
  g=0;
  v=2;

  while (g+5<=t) {
      v = v+4;
      if ((g%3)==0) {
          v = v-v;
      }
  }

}
