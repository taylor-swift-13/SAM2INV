int main1(int k,int q){
  int o, s, v, a;

  o=(q%19)+18;
  s=0;
  v=k;
  a=-1;

  while (v!=0&&a!=0) {
      if (v>a) {
          v = v-a;
      }
      else {
          a = a-v;
      }
  }

}
