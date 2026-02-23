int main1(int m,int n){
  int r, y, v, o;

  r=n;
  y=r;
  v=-8;
  o=r;

  while (v!=0&&o!=0) {
      if (v>o) {
          v = v-o;
      }
      else {
          o = o-v;
      }
      v = v+5;
      o = o+2;
  }

}
