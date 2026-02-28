int main1(int a,int k){
  int o, t, v;

  o=55;
  t=o;
  v=-4;

  while (t>0) {
      v = v-v;
      v = v+v;
      if (t+1<=a+o) {
          v = v+2;
      }
      t = t-1;
  }

}
