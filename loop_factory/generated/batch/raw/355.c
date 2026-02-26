int main1(int a,int q){
  int x, g, v, s;

  x=24;
  g=x;
  v=-2;
  s=5;

  while (v!=0&&s!=0) {
      if (v>s) {
          v = v-s;
      }
      else {
          s = s-v;
      }
      v = v+1;
      s = s+v;
      s = s+1;
  }

}
